// Formal-owned diagnostic supplement, included inside proof-params pari::tests.
// Uses only an already complete registry. No setup, prover or runtime admission.

#[test]
#[ignore = "requires the complete matching configured native Pari registry"]
fn fv_warm_registry_cache_rejects_exact_shape_and_trailing_decode() -> Result<()> {
    let source = PathBuf::from(std::env::var("SHIELDD_PARI_KEYS")?);
    let original_registry = Registry::load(&source)?;
    let original_bytes = fs::read(source.join("manifest.json"))?;
    let original: Manifest = serde_json::from_slice(&original_bytes)?;
    assert_eq!(original.entries.len(), Family::ALL.len());
    let directory = tempfile::tempdir()?;
    for family in Family::ALL {
        let name = format!("{}.vk", family.label());
        fs::copy(source.join(&name), directory.path().join(name))?;
    }
    let manifest_path = directory.path().join("manifest.json");
    fs::write(&manifest_path, &original_bytes)?;
    assert_eq!(Registry::load(directory.path())?.id(), original_registry.id());

    // Keep the wrong domain within admission bounds, so a bounds error cannot
    // be mistaken for the intended exact compiled-relation failure.
    let mut wrong_domain: Manifest = serde_json::from_slice(&original_bytes)?;
    let entry = wrong_domain.entries.iter_mut()
        .find(|entry| entry.family == Family::Transfer)
        .context("complete registry must include Transfer")?;
    let old_domain = entry.domain_size;
    entry.domain_size = if old_domain > 1 { old_domain / 2 } else { 2 };
    assert_ne!(entry.domain_size, old_domain);
    validate_bounds(entry.domain_size, entry.verifying_key.bytes, entry.proving_key.bytes)?;
    fs::write(&manifest_path, serde_json::to_vec(&wrong_domain)?)?;
    let error = Registry::load(directory.path()).err()
        .context("warm cache must reject a different bounded manifest domain")?;
    assert!(error.to_string().contains("key does not match the compiled Shieldd relation"),
        "wrong failure class for bounded domain mutation: {error:#}");

    // Mutate a native decoded relation label while retaining real key shape.
    // Refresh every manifest identity to reach the compiled-relation gate;
    // this is not a correctly generated alternate-key proof control.
    let key_path = directory.path().join("transfer.vk");
    let original_key = fs::read(&key_path)?;
    let decoded_original: VerifyingKey = decode_key(&original_key)?;
    let mut substituted_bytes = original_key.clone();
    substituted_bytes[0] ^= 1;
    let substituted: VerifyingKey = decode_key(&substituted_bytes)?;
    assert_ne!(substituted.relation_digest(), decoded_original.relation_digest());
    let mut substituted_manifest: Manifest = serde_json::from_slice(&original_bytes)?;
    let entry = substituted_manifest.entries.iter_mut()
        .find(|entry| entry.family == Family::Transfer)
        .context("complete registry must include Transfer")?;
    entry.verifying_key.bytes = substituted_bytes.len() as u64;
    entry.verifying_key.sha256 = hex::encode(Sha256::digest(&substituted_bytes));
    entry.verifying_key_digest = hex::encode(substituted.digest());
    entry.relation = hex::encode(substituted.relation_digest());
    validate_bounds(entry.domain_size, entry.verifying_key.bytes, entry.proving_key.bytes)?;
    fs::write(&key_path, &substituted_bytes)?;
    fs::write(&manifest_path, serde_json::to_vec(&substituted_manifest)?)?;
    let error = Registry::load(directory.path()).err()
        .context("warm cache must recompile-check a different fully decoded VK")?;
    assert!(error.to_string().contains("key does not match the compiled Shieldd relation"),
        "wrong failure class for checksum/identity-consistent relation mutation: {error:#}");

    // Original digest/relation restored; size/checksum updated to the actual
    // bytes with a suffix. Strict decoding must fail before identity checks.
    let mut trailing = original_key.clone();
    trailing.push(0);
    let mut trailing_manifest: Manifest = serde_json::from_slice(&original_bytes)?;
    let entry = trailing_manifest.entries.iter_mut()
        .find(|entry| entry.family == Family::Transfer)
        .context("complete registry must include Transfer")?;
    entry.verifying_key.bytes = trailing.len() as u64;
    entry.verifying_key.sha256 = hex::encode(Sha256::digest(&trailing));
    validate_bounds(entry.domain_size, entry.verifying_key.bytes, entry.proving_key.bytes)?;
    fs::write(&key_path, &trailing)?;
    fs::write(&manifest_path, serde_json::to_vec(&trailing_manifest)?)?;
    let error = Registry::load(directory.path()).err()
        .context("checksum-consistent trailing VK bytes must fail strict decode")?;
    assert!(error.to_string().contains("trailing key bytes"),
        "wrong failure class for trailing native key bytes: {error:#}");

    fs::write(&key_path, &original_key)?;
    fs::write(&manifest_path, &original_bytes)?;
    assert_eq!(Registry::load(directory.path())?.id(), original_registry.id());
    assert_eq!(fs::read(source.join("manifest.json"))?, original_bytes,
        "configured parent registry remains unchanged");
    assert_eq!(fs::read(source.join("transfer.vk"))?, original_key,
        "configured parent Transfer VK remains unchanged");
    Ok(())
}
