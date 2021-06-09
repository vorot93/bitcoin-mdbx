use anyhow::bail;
use bitcoin::{
    block::Header,
    consensus::{Decodable, Encodable},
    hashes::Hash,
    PubkeyHash, PublicKey, ScriptBuf, ScriptHash, VarInt,
};
use clap::*;
use db_key::Key;
use leveldb::{
    database::Database,
    iterator::Iterable,
    kv::KV,
    options::{Options, ReadOptions},
};
use libmdbx::{Geometry, TableFlags, WriteFlags, WriteMap};
use primitive_types::U128;
use serde::{Deserialize, Serialize};
use std::{
    io::{Read, Seek, SeekFrom},
    path::PathBuf,
    time::{Duration, Instant},
};
use tracing::*;
use tracing_subscriber::{prelude::*, EnvFilter};

#[derive(Parser)]
#[clap(name = "bitcoin-mdbx", about = "Convert bitcoin's database to MDBX")]
struct Opt {
    #[clap(long, env)]
    bitcoin_home_path: PathBuf,
    #[clap(long, env)]
    mdbx_path: Option<PathBuf>,
    #[clap(long, env)]
    skip: Option<usize>,
    #[clap(long, env)]
    debug_after: Option<usize>,
}

/// Used for keying leveldb.
#[derive(Debug, PartialEq)]
pub struct BytesKey {
    key: Vec<u8>,
}

impl Key for BytesKey {
    fn from_u8(key: &[u8]) -> Self {
        Self { key: key.to_vec() }
    }

    fn as_slice<T, F: Fn(&[u8]) -> T>(&self, f: F) -> T {
        f(self.key.as_slice())
    }
}

#[allow(clippy::needless_range_loop)]
fn xor(vch: &mut [u8], key: &[u8]) {
    if !key.is_empty() {
        let mut j = 0;
        for i in 0..vch.len() {
            vch[i] ^= key[j];

            j += 1;

            // This potentially acts on very many bytes of data, so it's
            // important that we calculate `j`, i.e. the `key` index in this
            // way instead of doing a %, which would effectively be a division
            // for each byte Xor'd -- much slower than need be.
            if j == key.len() {
                j = 0;
            }
        }
    }
}

fn decompress_amount(mut x: u64) -> u64 {
    // x = 0  OR  x = 1+10*(9*n + d - 1) + e  OR  x = 1+10*(n - 1) + 9
    if x == 0 {
        return 0;
    }
    x -= 1;
    // x = 10*(9*n + d - 1) + e
    let mut e = (x % 10) as i32;
    x /= 10;
    let mut n = if e < 9 {
        // x = 9*n + d - 1
        let d = ((x % 9) + 1) as i32;
        x /= 9;
        // x = n
        x * 10 + (d as u64)
    } else {
        x + 1
    };
    while e > 0 {
        n *= 10;
        e -= 1;
    }
    n
}

const BLOCK_HAVE_DATA: u64 = 8;
const BLOCK_HAVE_UNDO: u64 = 16;

fn read_var_int(reader: &mut impl Read) -> anyhow::Result<u64> {
    let mut n = 0;
    loop {
        let mut ch_data = [0_u8; 1];
        reader.read_exact(&mut ch_data)?;
        let ch_data = ch_data[0];
        if n > (u64::MAX >> 7) {
            bail!("ReadVarInt(): size too large");
        }
        n = (n << 7) | (ch_data & 0x7F) as u64;
        if (ch_data & 0x80) != 0 {
            if n == u64::MAX {
                bail!("ReadVarInt(): size too large");
            }
            n += 1;
        } else {
            return Ok(n);
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum CompressedScript {
    P2PK(PublicKey),
    P2PKH(PubkeyHash),
    P2SH(ScriptHash),
    Custom(ScriptBuf),
}

impl From<CompressedScript> for ScriptBuf {
    fn from(script: CompressedScript) -> Self {
        match script {
            CompressedScript::P2PK(key) => ScriptBuf::new_p2pk(&key),
            CompressedScript::P2PKH(keyhash) => ScriptBuf::new_p2pkh(&keyhash),
            CompressedScript::P2SH(scripthash) => ScriptBuf::new_p2sh(&scripthash),
            CompressedScript::Custom(s) => s,
        }
    }
}

impl CompressedScript {
    fn from_reader(n_size: usize, reader: &mut impl Read) -> anyhow::Result<Self> {
        Ok(match n_size {
            0 => {
                let mut v = [0_u8; 20];
                reader.read_exact(&mut v)?;

                Self::P2PKH(PubkeyHash::from_slice(&v)?)
            }
            1 => {
                let mut v = [0_u8; 20];
                reader.read_exact(&mut v)?;

                Self::P2SH(ScriptHash::from_slice(&v)?)
            }
            2 | 3 => {
                let mut v = [0_u8; 32];
                reader.read_exact(&mut v)?;

                let mut vch = [0_u8; 33];
                vch[0] = n_size as u8;
                vch[1..].copy_from_slice(&v);

                Self::P2PK(bitcoin::PublicKey::from_slice(&vch)?)
            }
            4 | 5 => {
                let mut v = [0_u8; 32];
                reader.read_exact(&mut v)?;
                let mut vch = [0_u8; 33];
                vch[0] = n_size as u8 - 2;
                vch[1..].copy_from_slice(&v);

                Self::P2PK(bitcoin::PublicKey::from_slice(&vch)?)
            }
            other => {
                bail!("invalid n_size {}", other)
            }
        })
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Coin {
    pub amount: u64,
    pub height: u32,
    pub coin_base: u32,
    pub script: CompressedScript,
}

impl Coin {
    pub fn from_reader<R: Read + std::io::Seek>(
        reader: &mut R,
        dummy_version: bool,
    ) -> anyhow::Result<Self> {
        let code = read_var_int(reader)? as u32;
        let height = code >> 1;
        let coin_base = code & 1;

        if dummy_version && height > 0 {
            read_var_int(reader)?;
        }

        let amount = read_var_int(reader)?;
        let amount = decompress_amount(amount);

        const N_SPECIAL_SCRIPTS: usize = 6;

        let mut n_size = read_var_int(reader)? as usize;

        let script = if n_size < N_SPECIAL_SCRIPTS {
            CompressedScript::from_reader(n_size, reader)?
        } else {
            n_size -= N_SPECIAL_SCRIPTS;
            let mut v = vec![0_u8; n_size];
            reader.read_exact(&mut v)?;
            CompressedScript::Custom(v.into())
        };

        Ok(Self {
            amount,
            height,
            coin_base,
            script,
        })
    }
}

/// Block bodies are actually stored in normalized form.
#[derive(Default, Serialize, Deserialize)]
struct BlockBody {
    pub tx_index: u64,
    pub tx_total: u64,
    pub rev_index: u64,
    pub rev_total: u64,
}

fn main() -> anyhow::Result<()> {
    let opt = Opt::parse();

    let filter = if std::env::var(EnvFilter::DEFAULT_ENV)
        .unwrap_or_default()
        .is_empty()
    {
        EnvFilter::new("bitcoin_mdbx=debug")
    } else {
        EnvFilter::from_default_env()
    };
    let registry = tracing_subscriber::registry()
        // the `TasksLayer` can be used in combination with other `tracing` layers...
        .with(tracing_subscriber::fmt::layer().with_target(false));

    registry.with(filter).init();

    let tmpdir = tempfile::tempdir()?;
    let mdbx_path = opt
        .mdbx_path
        .as_ref()
        .map(|path| {
            let _ = std::fs::remove_dir_all(path);
            path.as_path()
        })
        .unwrap_or_else(|| tmpdir.path());

    let out_db = libmdbx::Database::<WriteMap>::new()
        .set_max_tables(100)
        .set_geometry(Geometry {
            size: Some(0..1024 * 1024 * 1024 * 1024),
            ..Default::default()
        })
        .open(mdbx_path)?;
    let tx = out_db.begin_rw_txn()?;

    let state_table = tx.create_table(Some("State"), TableFlags::default())?;

    let headers_table = tx.create_table(Some("Headers"), TableFlags::default())?;
    let block_hashes_table = tx.create_table(Some("BlockHashes"), TableFlags::default())?;
    let bodies_table = tx.create_table(Some("Bodies"), TableFlags::default())?;
    let txs_table = tx.create_table(Some("BlockTransaction"), TableFlags::default())?;
    let txlookup_table = tx.create_table(Some("TxLookup"), TableFlags::default())?;

    let rev_state_table = tx.create_table(Some("RevState"), TableFlags::default())?;

    let blocks_path = opt.bitcoin_home_path.join("blocks");
    let block_index_path = blocks_path.join("index");
    let chainstate_path = opt.bitcoin_home_path.join("chainstate");

    for path in &[block_index_path, chainstate_path] {
        info!("Opening {}", path.as_os_str().to_string_lossy());

        let db = Database::<BytesKey>::open(path, Options::new())?;

        let mut k = vec![0x0e, 0x00];
        k.extend_from_slice(b"obfuscate_key");

        let obfuscate_key = db
            .get(ReadOptions::new(), BytesKey::from_u8(&k))?
            .map(|mut v| {
                v.remove(0);
                v
            });

        info!(
            "Obfuscate key: {:?}",
            obfuscate_key.as_ref().map(hex::encode)
        );

        let mut prev_print = Instant::now();
        for (i, (k, mut v)) in db
            .iter(ReadOptions::new())
            .enumerate()
            .skip(opt.skip.unwrap_or(0))
        {
            let mut k = k.as_slice(|b| b.to_vec());

            let now = Instant::now();
            if now - prev_print > Duration::from_secs(2) {
                prev_print = now;
                info!("{:?}: Done {}, current entry: {}", path, i, hex::encode(&k));
            }

            if let Some(key) = &obfuscate_key {
                xor(v.as_mut_slice(), key);
            }

            let letter = k.remove(0);

            let mut kcur = std::io::Cursor::new(&k);
            let mut vcur = std::io::Cursor::new(&v);

            let debug = opt
                .debug_after
                .map(|debug_after| i >= debug_after)
                .unwrap_or(false);

            match letter {
                b'b' => {
                    let block_hash = bitcoin::BlockHash::consensus_decode(&mut kcur)?;

                    let _ = read_var_int(&mut vcur)?;

                    let height = read_var_int(&mut vcur)?;
                    let status = read_var_int(&mut vcur)?;
                    let txnum = read_var_int(&mut vcur)?;

                    let f = (status & (BLOCK_HAVE_DATA | BLOCK_HAVE_UNDO) != 0)
                        .then(|| read_var_int(&mut vcur))
                        .transpose()?;
                    let data_pos = (status & BLOCK_HAVE_DATA != 0)
                        .then(|| read_var_int(&mut vcur))
                        .transpose()?;
                    let undo_pos = (status & BLOCK_HAVE_UNDO != 0)
                        .then(|| read_var_int(&mut vcur))
                        .transpose()?;

                    let header = Header::consensus_decode(&mut vcur)?;

                    if debug {
                        debug!(
                                "block {} / height {} / status {} / txnum {} / f {:?} / data_pos {:?} / undo_pos {:?} / header {:?}",
                                block_hash, height, status, txnum, f, data_pos, undo_pos, header
                            );
                    }

                    let mut block_body = BlockBody::default();

                    // Extract block body
                    if let Some(fno) = f {
                        let fpath = blocks_path.join(format!("blk{:0>5}.dat", fno));
                        let revpath = blocks_path.join(format!("rev{:0>5}.dat", fno));

                        if debug {
                            debug!("{fpath:?} | {revpath:?}");
                        }
                        if let Some(data_pos) = data_pos {
                            let mut f = std::fs::File::open(fpath)?;
                            f.seek(SeekFrom::Start(data_pos))?;
                            let h = Header::consensus_decode(&mut f)?;
                            assert_eq!(header, h);
                            let blocktxs = Vec::<bitcoin::Transaction>::consensus_decode(&mut f)?;

                            block_body.tx_index = tx.table_stat(&txs_table)?.entries() as u64;
                            block_body.tx_total = blocktxs.len() as u64;

                            for (blocktx_i, blocktx) in blocktxs.iter().enumerate() {
                                if debug {
                                    trace!("{} => {:?}", blocktx.txid(), blocktx);
                                }

                                let mut v = vec![];
                                blocktx.consensus_encode(&mut v)?;

                                let txidx = (block_body.tx_index + blocktx_i as u64).to_be_bytes();

                                // TODO: Normalize coins further, unite with state table?
                                tx.put(
                                    &txs_table,
                                    txidx,
                                    &v,
                                    WriteFlags::NO_OVERWRITE | WriteFlags::APPEND,
                                )?;
                                tx.put(
                                    &txlookup_table,
                                    blocktx.txid(),
                                    txidx,
                                    WriteFlags::NO_OVERWRITE,
                                )?;
                            }

                            if let Some(undo_pos) = undo_pos {
                                let mut f = std::fs::File::open(revpath)?;
                                f.seek(SeekFrom::Start(undo_pos))?;
                                let revcoins = (0..VarInt::consensus_decode(&mut f)?.0)
                                    .flat_map(|_i| {
                                        let c = (0..VarInt::consensus_decode(&mut f)?.0)
                                            .map(|_j| {
                                                let c = Coin::from_reader(&mut f, true);
                                                if debug {
                                                    trace!(
                                                        "I {} => {:?}",
                                                        bitcoin::OutPoint {
                                                            txid: blocktxs[(_i as usize) + 1]
                                                                .txid(),
                                                            vout: _j as u32
                                                        },
                                                        c
                                                    );
                                                }
                                                c
                                            })
                                            .collect::<anyhow::Result<Vec<_>>>();
                                        Ok::<_, anyhow::Error>(c)
                                    })
                                    .collect::<anyhow::Result<Vec<_>>>()?;
                                block_body.rev_index =
                                    tx.table_stat(&rev_state_table)?.entries() as u64;
                                block_body.rev_total = revcoins.len() as u64;
                                for (i, revcoin) in revcoins.into_iter().enumerate() {
                                    let k = (block_body.rev_index + i as u64).to_be_bytes();

                                    tx.put(
                                        &rev_state_table,
                                        k,
                                        rmp_serde::to_vec(&revcoin)?,
                                        WriteFlags::NO_OVERWRITE | WriteFlags::APPEND,
                                    )?;
                                }
                            }
                        }
                        tx.put(
                            &bodies_table,
                            height.to_be_bytes(),
                            rmp_serde::to_vec(&block_body)?,
                            WriteFlags::NO_OVERWRITE,
                        )?;
                    }

                    let block_hash = k;
                    tx.put(
                        &headers_table,
                        height.to_be_bytes(),
                        v,
                        WriteFlags::NO_OVERWRITE,
                    )?;
                    tx.put(
                        &block_hashes_table,
                        block_hash,
                        height.to_be_bytes(),
                        WriteFlags::NO_OVERWRITE,
                    )?;
                }
                b'C' => {
                    let txid = bitcoin::Txid::consensus_decode(&mut kcur)?;
                    let output_id = U128::from_little_endian(&k[32..]).as_u32();

                    let coin = Coin::from_reader(&mut vcur, false)?;

                    if debug {
                        let fmt_k = format!("tx {} / output {}", txid, output_id,);
                        debug!("{}", hex::encode(&v));
                        let fmt_v = format!("{:?}", coin);
                        debug!("{}, output / K: {:?} / V: {:?}", i, fmt_k, fmt_v);
                    }

                    tx.put(
                        &state_table,
                        k,
                        v,
                        WriteFlags::NO_OVERWRITE | WriteFlags::APPEND,
                    )?;
                }
                other => {
                    warn!("Skipping unknown key: {:02x}{}", other, hex::encode(&k));
                }
            }
        }
    }

    tx.commit()?;

    Ok(())
}
