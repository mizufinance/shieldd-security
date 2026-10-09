//! Diagnostic example for a fresh source stage, not a deployed-key operation.
//! Reuses native setup for Transfer only; copies six other exact complete v2 keys.
use anyhow::{ensure, Context, Result};
use commonware_codec::{Encode, EncodeSize};
use commonware_cryptography::zk::pari;
use commonware_parallel::Sequential;
use sha2::{Digest, Sha256};
use shieldd_sdk_circuits::{catalogue, proof::Family};
use shieldd_sdk_proof_params::pari::{Artifact, Entry, Manifest, Registry};
use std::{fs::{self, File, OpenOptions}, io::{Read, Write}, path::Path};

const MANIFEST_LIMIT: u64 = 64 * 1024;
const VERIFYING_LIMIT: u64 = 8 * 1024 * 1024;
const PROVING_LIMIT: u64 = 512 * 1024 * 1024;

fn checked_copy(source: &Path, destination: Option<&Path>, artifact: &Artifact, limit: u64)
    -> Result<()> {
    ensure!(artifact.bytes > 0 && artifact.bytes <= limit, "invalid source artifact bound");
    let mut input = File::open(source)?;
    ensure!(input.metadata()?.len() == artifact.bytes, "source artifact size mismatch");
    let mut output = destination.map(|path| OpenOptions::new().write(true).create_new(true)
        .open(path)).transpose()?;
    let mut digest = Sha256::new();
    let mut total = 0u64;
    let mut buffer = [0u8; 65536];
    loop {
        let count = input.read(&mut buffer)?;
        if count == 0 { break; }
        total = total.checked_add(count as u64).context("source artifact length overflow")?;
        ensure!(total <= artifact.bytes, "source artifact grew");
        digest.update(&buffer[..count]);
        if let Some(output) = &mut output { output.write_all(&buffer[..count])?; }
    }
    ensure!(total == artifact.bytes && hex::encode(digest.finalize()) == artifact.sha256,
        "source artifact checksum mismatch");
    if let Some(output) = output { output.sync_all()?; }
    Ok(())
}
fn write_new(path: &Path, bytes: &[u8]) -> Result<Artifact> {
    let mut file = OpenOptions::new().write(true).create_new(true).open(path)?;
    file.write_all(bytes)?;
    file.sync_all()?;
    Ok(Artifact { bytes: bytes.len() as u64, sha256: hex::encode(Sha256::digest(bytes)) })
}
fn main() -> Result<()> {
    let arguments = std::env::args_os().skip(1).collect::<Vec<_>>();
    ensure!(arguments.len() == 2, "usage: transfer_distinct_registry COMPLETE_REGISTRY05 FRESH_DESTINATION");
    let source = Path::new(&arguments[0]);
    let destination = Path::new(&arguments[1]);
    ensure!(source.is_dir() && !source.symlink_metadata()?.file_type().is_symlink(),
        "source registry absent or symlinked");
    ensure!(!destination.exists() && destination.symlink_metadata().is_err(), "destination is not fresh");
    let parent = destination.parent().context("fresh destination parent absent")?;
    ensure!(parent.is_dir(), "fresh destination parent is not a directory");
    let source_manifest = source.join("manifest.json");
    ensure!(source_manifest.metadata()?.len() <= MANIFEST_LIMIT, "source manifest exceeds bound");
    let original_manifest = fs::read(&source_manifest)?;
    let mut manifest: Manifest = serde_json::from_slice(&original_manifest)?;
    let original = Registry::load(source)?;
    let original_transfer_vk = original.verifying_key(Family::Transfer)?;
    let expected_paths = std::iter::once("manifest.json".to_owned()).chain(
        Family::ALL.into_iter().flat_map(|family|
            [format!("{}.vk", family.label()), format!("{}.pk", family.label())]))
        .collect::<std::collections::BTreeSet<_>>();
    let actual_paths = fs::read_dir(source)?.map(|entry| {
        let entry = entry?;
        ensure!(entry.file_type()?.is_file() && !entry.file_type()?.is_symlink(),
            "registry source contains non-file");
        Ok(entry.file_name().into_string().map_err(|_| anyhow::anyhow!("non-UTF8 registry file"))?)
    }).collect::<Result<std::collections::BTreeSet<_>>>()?;
    ensure!(actual_paths == expected_paths, "source registry path set is not complete/exact");
    // Full original PK/VK checks precede setup; Registry::load intentionally
    // checks PK bytes only lazily during prove, so do not infer them from load.
    for entry in &manifest.entries {
        checked_copy(&source.join(format!("{}.vk", entry.family.label())), None,
            &entry.verifying_key, VERIFYING_LIMIT)?;
        checked_copy(&source.join(format!("{}.pk", entry.family.label())), None,
            &entry.proving_key, PROVING_LIMIT)?;
    }
    let staging = parent.join(format!(".transfer-only-setup-{}", std::process::id()));
    ensure!(!staging.exists() && staging.symlink_metadata().is_err(), "staging is not fresh");
    fs::create_dir(&staging)?;
    // Retain a failed staging directory for diagnostics; never change source05.
    for entry in &manifest.entries {
        if entry.family != Family::Transfer {
            checked_copy(&source.join(format!("{}.vk", entry.family.label())),
                Some(&staging.join(format!("{}.vk", entry.family.label()))),
                &entry.verifying_key, VERIFYING_LIMIT)?;
            checked_copy(&source.join(format!("{}.pk", entry.family.label())),
                Some(&staging.join(format!("{}.pk", entry.family.label()))),
                &entry.proving_key, PROVING_LIMIT)?;
        }
    }
    let compiled = catalogue::compile(Family::Transfer)?;
    ensure!(compiled.relation.domain_size().is_power_of_two()
        && compiled.relation.domain_size() <= 1 << 21, "generated relation domain invalid");
    ensure!(original_transfer_vk.matches_relation(&compiled.relation), "original relation does not match");
    let (pk, vk) = pari::setup(&compiled.relation,
        &mut rand10::rand_core::UnwrapErr(rand10::rngs::SysRng), &Sequential)?;
    ensure!(pk.verifying_key() == &vk && vk.matches_relation(&compiled.relation), "generated key mismatch");
    ensure!(&vk != original_transfer_vk && vk.digest() != original_transfer_vk.digest(),
        "new Transfer key is not distinct");
    ensure!(vk.encode_size() > 0 && vk.encode_size() as u64 <= VERIFYING_LIMIT
        && pk.encode_size() > 0 && pk.encode_size() as u64 <= PROVING_LIMIT,
        "generated key exceeds size bound");
    let replacement = Entry { family: Family::Transfer,
        relation: hex::encode(compiled.relation.digest()), verifying_key_digest: hex::encode(vk.digest()),
        domain_size: compiled.relation.domain_size(),
        verifying_key: write_new(&staging.join("transfer.vk"), &vk.encode())?,
        proving_key: write_new(&staging.join("transfer.pk"), &pk.encode())? };
    let original_entry = manifest.entries.iter_mut().find(|entry| entry.family == Family::Transfer)
        .context("complete registry lacks Transfer")?;
    ensure!(original_entry.relation == replacement.relation
        && original_entry.domain_size == replacement.domain_size, "Transfer relation changed");
    *original_entry = replacement;
    let encoded = serde_json::to_vec_pretty(&manifest)?;
    ensure!(encoded.len() as u64 <= MANIFEST_LIMIT, "new manifest exceeds bound");
    write_new(&staging.join("manifest.json"), &encoded)?;
    let second = Registry::load(&staging)?;
    ensure!(second.id() != original.id(), "new native registry identity is not distinct");
    for family in Family::ALL {
        if family != Family::Transfer {
            ensure!(second.verifying_key(family)? == original.verifying_key(family)?,
                "other family key changed");
        }
    }
    ensure!(fs::read(&source_manifest)? == original_manifest, "source manifest changed");
    // Recheck all source artifact identities before publication, not only paths.
    let source_entries: Manifest = serde_json::from_slice(&original_manifest)?;
    for entry in &source_entries.entries {
        checked_copy(&source.join(format!("{}.vk", entry.family.label())), None,
            &entry.verifying_key, VERIFYING_LIMIT)?;
        checked_copy(&source.join(format!("{}.pk", entry.family.label())), None,
            &entry.proving_key, PROVING_LIMIT)?;
    }
    File::open(&staging)?.sync_all()?;
    ensure!(!destination.exists(), "destination appeared during setup");
    fs::rename(&staging, destination)?;
    File::open(parent)?.sync_all()?;
    ensure!(Registry::load(destination)?.id() == second.id(), "published native identity changed");
    println!("Fresh distinct native Transfer registry published; genuine first-prove validation remains required.");
    Ok(())
}
