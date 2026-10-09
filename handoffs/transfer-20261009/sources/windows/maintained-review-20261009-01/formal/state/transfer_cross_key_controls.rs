//! Diagnostic test overlay for the exact shieldd.lock source.
//! Requires two independently generated, complete matching development registries.
//! Source preparation alone grants no runtime or cryptographic control credit.

use super::*;
use crate::stateless_cache::VerifiedTxArtifact;
use commonware_parallel::Sequential;
use shieldd_sdk_circuits::proof::Family;
use shieldd_sdk_proof_params::pari::Registry;

fn require_rejection<T>(result: Result<T>, expected: &str) {
    let error = match result {
        Ok(_) => panic!("expected rejection: {expected}"),
        Err(error) => error,
    };
    assert!(format!("{error:#}").contains(expected), "wrong rejection cause: {error:#}");
}

#[tokio::test(flavor = "multi_thread")]
async fn genuine_transfer_same_relation_different_key_rejection() -> Result<()> {
    let directory = std::env::var_os("SHIELDD_FV_SECOND_PARI_KEYS")
        .context("independently generated complete second registry is required")?;
    // Use the production loader: a fabricated registry ID or malformed key must
    // not count as a same-relation, distinct-key cryptographic rejection.
    let second = Registry::load(directory)?;
    let first = registry();
    let first_key = first.verifying_key(Family::Transfer)?;
    let second_key = second.verifying_key(Family::Transfer)?;
    assert_eq!(first_key.relation_digest(), second_key.relation_digest());
    assert_ne!(first_key.digest(), second_key.digest(), "fresh setups must differ");
    assert_ne!(first.id(), second.id());

    let fixtures = family_fixtures().await?;
    let bytes = &fixtures.fee_funding_fixture.tx_bytes;
    let tx = Arc::new(Transaction::decode_canonical(bytes)?);
    let extracted = App::build_tx_artifacts_extracted(&[tx]).await?;
    let artifact = extracted[0].clone();
    let items = &artifact.proof_items[&Family::Transfer];
    assert_eq!(items.len(), 2, "genuine body and fee proof occurrences");
    let capabilities = first.verify_items(items, &Sequential)?;
    for item in items {
        first.verify_item(item)?;
        assert_eq!(item.family, Family::Transfer);
        // Family, relation and public statement all agree. Require rejection at
        // actual Pari verification, after the production context guards.
        require_rejection(item.envelope.verify(Family::Transfer, second_key, &item.statement),
            "invalid Pari proof");
        require_rejection(second.verify_item(item), "invalid Pari proof");
    }
    require_rejection(second.verify_items(items, &Sequential), "invalid Pari proof batch");

    let rows = vec![(ProofSlot::BodyAction(0), capabilities[0].clone()),
        (ProofSlot::FeeFunding, capabilities[1].clone())];
    let verified = Arc::new(VerifiedTxArtifact::new(artifact.clone(), rows.clone(), &first)?);
    require_rejection(VerifiedTxArtifact::new(artifact.clone(), rows, &second),
        "proof capability registry mismatch");
    require_rejection(verified.ensure_registry(&second), "verified transaction registry mismatch");
    let cache = StatelessCache::new();
    cache.insert_fully_verified(bytes, verified)?;
    let hash = tx_hash(bytes);
    assert!(matches!(cache.get(first.id(), &hash, bytes), Some(CacheEntry::FullyVerified(_))));
    assert!(cache.get(second.id(), &hash, bytes).is_none());
    // Recheck the positive after all refusals, retaining the exact proof bytes.
    first.verify_items(items, &Sequential)?;
    Ok(())
}
