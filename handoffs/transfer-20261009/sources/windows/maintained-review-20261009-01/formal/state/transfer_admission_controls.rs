// Append only inside the existing owned transfer_effect_controls test module
// in a fresh stage. These are genuine controls, not proof-free/codec fixtures.
#[tokio::test(flavor = "multi_thread")]
async fn genuine_transfer_distinct_same_family_registry_rejects_exact_proof_and_capability() -> Result<()> {
    use shieldd_sdk_circuits::proof::Family;
    use shieldd_sdk_proof_params::pari::Registry;
    use crate::stateless_cache::VerifiedTxArtifact;
    let alternate_path = std::env::var("SHIELDD_TRANSFER_DISTINCT_KEYS")
        .context("complete correctly generated distinct Transfer registry required")?;
    let original = registry();
    let alternate = Arc::new(Registry::load(&alternate_path)?);
    assert_ne!(original.id(), alternate.id());
    assert_eq!(original.verifying_key(Family::Transfer)?.relation_digest(),
        alternate.verifying_key(Family::Transfer)?.relation_digest());
    assert_ne!(original.verifying_key(Family::Transfer)?.digest(),
        alternate.verifying_key(Family::Transfer)?.digest());
    for family in Family::ALL {
        if family != Family::Transfer {
            assert_eq!(original.verifying_key(family)?, alternate.verifying_key(family)?);
        }
    }
    let storage = build_fixture_storage().await?;
    let client = MockClient::new(test_keys::SPEND_KEY.clone()).with_sync_to_storage(&storage).await?;
    let note = client.notes.values().find(|note| note.asset_id() == *BASE_ASSET_ID
        && note.address() == test_keys::ADDRESS_0.deref().clone()).context("actual unspent fixture note")?.clone();
    let intent = shieldd_sdk_mock_client::TransactionIntent {
        actions: vec![transfer_plan(&client, note, Fr::from(1u64),
            test_keys::ADDRESS_1.deref().clone())?.into()],
        transaction_parameters: TransactionParameters { chain_id: TEST_CHAIN_ID.to_owned(), ..Default::default() },
        memo: None, fee_funding: None,
    };
    let plan = client.complete_intent(intent, storage.latest_snapshot()).await?;
    // Each real first-prove validates its PK bytes/hash/decode and embedded VK.
    let original_tx = Arc::new(client.witness_auth_build(&plan, original.clone()).await?);
    let alternate_tx = Arc::new(client.witness_auth_build(&plan, alternate.clone()).await?);
    let original_artifact = App::build_tx_artifacts_extracted(&[original_tx.clone()]).await?.remove(0);
    let alternate_artifact = App::build_tx_artifacts_extracted(&[alternate_tx.clone()]).await?.remove(0);
    let original_item = &original_artifact.proof_items[&Family::Transfer][0];
    let alternate_item = &alternate_artifact.proof_items[&Family::Transfer][0];
    assert_eq!(original_item.statement, alternate_item.statement, "same completed plan/public statement");
    let original_capability = original.verify_item(original_item)?;
    let alternate_capability = alternate.verify_item(alternate_item)?;
    for (item, other) in [(original_item, &alternate), (alternate_item, &original)] {
        expected_rejection(other.verify_item(item), "invalid Pari proof");
        expected_rejection(other.verify_items(std::slice::from_ref(item), &Sequential), "invalid Pari proof batch");
    }
    expected_rejection(VerifiedTxArtifact::new(original_artifact.clone(),
        vec![(ProofSlot::BodyAction(0), original_capability.clone())], &alternate), "proof capability registry mismatch");
    expected_rejection(VerifiedTxArtifact::new(alternate_artifact.clone(),
        vec![(ProofSlot::BodyAction(0), alternate_capability)], &original), "proof capability registry mismatch");
    let verified = Arc::new(VerifiedTxArtifact::new(original_artifact,
        vec![(ProofSlot::BodyAction(0), original_capability)], &original)?);
    let mut app = App::new(storage.latest_snapshot(), alternate.clone(), storage.reader.clone()).await?;
    let context = app.benchmark_block_context().await?;
    app.begin_block(&cnidarium_component::BlockContext { height: context.height, time: context.time }).await?;
    let before = effect_snapshot(&app, &[&original_tx]).await?;
    expected_rejection(app.deliver_tx_with_verified_stateless(verified, None).await,
        "verified transaction registry mismatch");
    assert_eq!(effect_snapshot(&app, &[&original_tx]).await?, before);
    let cache = StatelessCache::new();
    let bytes = original_tx.encode_to_vec();
    let original_verified = App::build_tx_artifacts(original.clone(), &[original_tx]).await?.remove(0);
    cache.insert_fully_verified(&bytes, original_verified)?;
    assert!(cache.get(alternate.id(), &tx_hash(&bytes), &bytes).is_none());
    // Complete alternate proof/signature/current-state pipeline must also pass.
    app.deliver_tx_bytes(&alternate_tx.encode_to_vec(), Some(&cache)).await?;
    assert_exact_transfer_effects(&app, &alternate_tx).await?;
    Ok(())
}

#[tokio::test(flavor = "multi_thread")]
async fn genuine_transfer_cross_transaction_family_queue_order_is_exact() -> Result<()> {
    use shieldd_sdk_circuits::proof::Family;
    use std::collections::{BTreeMap, VecDeque};
    let (_storage, _client, first, second) = setup_test_txs(2).await?;
    let artifacts = App::build_tx_artifacts_extracted(&[Arc::new(first), Arc::new(second)]).await?;
    let merged = App::merge_artifact_proof_items(&artifacts);
    assert_eq!(merged.len(), 1);
    let items = &merged[&Family::Transfer];
    assert_eq!(items.len(), 2);
    assert_ne!(items[0], items[1], "cross-artifact order control must be nonvacuous");
    let capabilities = registry().verify_items(items, &Sequential)?;
    let exact = BTreeMap::from([(Family::Transfer, VecDeque::from(capabilities.clone()))]);
    let verified = App::attach_verified_capabilities(registry(), artifacts.clone(), exact)?;
    assert_eq!(verified.len(), 2);
    for (index, artifact) in verified.iter().enumerate() {
        artifact.proof_for_slot(ProofSlot::BodyAction(0))?.ensure_binds(Family::Transfer, &items[index])?;
    }
    let mut swapped = capabilities; swapped.reverse();
    expected_rejection(App::attach_verified_capabilities(registry(), artifacts,
        BTreeMap::from([(Family::Transfer, VecDeque::from(swapped))])), "verified proof capability mismatch");
    Ok(())
}

#[tokio::test(flavor = "multi_thread")]
async fn genuine_transfer_exact_effect_and_authorization_messages_reject_mutation() -> Result<()> {
    use shieldd_sdk_txhash::EffectingData as _;
    let fixtures = family_fixtures().await?;
    let original = Transaction::decode_canonical(&fixtures.fee_funding_fixture.tx_bytes)?;
    App::build_tx_artifacts(registry(), &[Arc::new(original.clone())]).await?;
    let original_effect = original.effect_hash();
    let original_auth = original.auth_hash();
    let mut changed = original.clone();
    changed.transaction_body.transaction_parameters.expiry_height =
        changed.transaction_body.transaction_parameters.expiry_height.checked_add(1).context("expiry mutation overflow")?;
    assert_ne!(changed.effect_hash(), original_effect);
    assert_ne!(changed.auth_hash(), original_auth);
    expected_rejection(crate::action_handler::transaction::validate_transaction_envelope(&changed),
        "binding signature failed to verify");
    let Action::Transfer(body) = &changed.transaction_body.actions[0] else {
        anyhow::bail!("actual body Transfer required");
    };
    expected_rejection(shieldd_sdk_shielded_pool::component::transfer_check_stateless_and_extract(body,
        &changed.context(), shieldd_sdk_shielded_pool::TransferProofContext::Ordinary),
        "transfer auth signature failed to verify");
    // Move the two genuine bodies between body/fee locations without mutating
    // either proof or signature. Both hash frames and exact context guard matter.
    let mut moved = original.clone();
    let Action::Transfer(ref mut body) = moved.transaction_body.actions[0] else {
        anyhow::bail!("actual body Transfer required");
    };
    let fee = moved.transaction_body.fee_funding.as_mut().context("actual fee Transfer required")?;
    std::mem::swap(body, &mut fee.transfer);
    assert_ne!(moved.effect_hash(), original_effect);
    assert_ne!(moved.auth_hash(), original_auth);
    expected_rejection(crate::action_handler::transaction::validate_transaction_envelope(&moved),
        "binding signature failed to verify");
    let Action::Transfer(body) = &moved.transaction_body.actions[0] else { unreachable!() };
    expected_rejection(shieldd_sdk_shielded_pool::component::transfer_check_stateless_and_extract(body,
        &moved.context(), shieldd_sdk_shielded_pool::TransferProofContext::Ordinary),
        "transfer proof context does not match its transaction location");
    App::build_tx_artifacts(registry(), &[Arc::new(original)]).await?;
    Ok(())
}
