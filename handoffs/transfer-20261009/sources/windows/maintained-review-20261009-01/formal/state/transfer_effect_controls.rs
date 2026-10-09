//! Fresh-stage test overlay, pinned to shieldd.lock; not runtime evidence.
//! Reuses the existing full-relation MockClient witness/auth/proof builders.
//! Faults are cfg(test), transaction-ID-bound, and occur after real effects.

use super::*;
use cnidarium::ArcStateDeltaExt as _;
use commonware_codec::{Encode as _, RangeCfg, Read as _};
use commonware_cryptography::{bls12381::primitives::group::{G1, Scalar}, zk::pari::Claim};
use commonware_math::algebra::{Additive as _, CryptoGroup as _};
use commonware_parallel::Sequential;
use prost::Message as _;
use shieldd_sdk_compact_block::component::RoutingManager as _;
use shieldd_sdk_sct::component::clock::EpochRead as _;
use shieldd_sdk_sct::component::tree::{SctManager as _, SctRead as _};
use shieldd_sdk_shielded_pool::component::{
    NoteManager as _, StateReadExt as _, StateWriteExt as _,
};

const EFFECT_FAULT: &str = "fv.transfer.effect_fault";

fn expected_rejection<T>(result: Result<T>, label: &str) {
    let error = match result { Ok(_) => panic!("expected rejection: {label}"), Err(error) => error };
    assert!(format!("{error:#}").contains(label), "wrong rejection cause: {error:#}");
}

// Decode the actual claim, mutate its typed fields, and preserve the original
// proof tail. Only Shieldd's documented suite/family/relation header is indexed.
// A changed public claim is also used as the expected statement, so the public
// equality guard passes and the actual claim-binding proof check must fail.
fn changed_claim(item: &shieldd_sdk_proof_params::pari::Verification, public: bool)
    -> Result<shieldd_sdk_proof_params::pari::Verification> {
    use shieldd_sdk_circuits::proof::Envelope;
    let original = item.envelope.to_bytes();
    let mut tail = &original[34..];
    let mut claim = Claim::read_cfg(&mut tail, &(RangeCfg::exact(1), RangeCfg::exact(1)))?;
    let original_claim = claim.encode();
    let mut unchanged = original[..34].to_vec();
    unchanged.extend(&original_claim);
    unchanged.extend(tail);
    assert_eq!(unchanged, original, "positive typed-claim encoding correspondence");
    let mut changed = item.clone();
    if public {
        claim.public_inputs[0] += &Scalar::from(1u64);
        changed.statement = claim.public_inputs[0].clone();
    } else {
        claim.commitments[0] += &G1::generator();
    }
    let mut bytes = original[..34].to_vec();
    bytes.extend(claim.encode());
    bytes.extend(tail);
    changed.envelope = Envelope::from_bytes(&bytes).context("changed claim must decode")?;
    assert_ne!(changed.envelope.to_bytes(), original);
    Ok(changed)
}

#[tokio::test(flavor = "multi_thread")]
async fn genuine_transfer_claim_family_key_and_context_admission() -> Result<()> {
    use shieldd_sdk_circuits::proof::{Envelope, Family};
    use shieldd_sdk_shielded_pool::{component::transfer_check_stateless_and_extract,
        TransferProofContext};
    let fixtures = family_fixtures().await?;
    let tx = Arc::new(Transaction::decode_canonical(&fixtures.fee_funding_fixture.tx_bytes)?);
    let extracted = App::build_tx_artifacts_extracted(&[tx.clone()]).await?;
    let items = &extracted[0].proof_items[&Family::Transfer];
    assert_eq!(items.len(), 2, "genuine body and fee proof occurrences");
    registry().verify_items(items, &Sequential)?;
    expected_rejection(registry().verify_items(&[], &Sequential), "empty proof batch");
    let mut mixed = items[1].clone(); mixed.family = Family::Withdrawal;
    expected_rejection(registry().verify_items(&[items[0].clone(), mixed], &Sequential), "mixed proof families");
    for item in items {
        registry().verify_item(item)?;
        expected_rejection(registry().verify(Family::Withdrawal, &item.statement, &item.envelope), "wrong proof family");
        expected_rejection(item.envelope.verify(Family::Transfer, registry().verifying_key(Family::Withdrawal)?,
            &item.statement), "wrong proof relation");
        let mut wrong_statement = item.clone();
        wrong_statement.statement += &Scalar::from(1u64);
        expected_rejection(registry().verify_item(&wrong_statement), "wrong proof statement");
        for public in [true, false] {
            let changed = changed_claim(item, public)?;
            expected_rejection(registry().verify_item(&changed), "invalid Pari proof");
            expected_rejection(registry().verify_items(&[item.clone(), changed], &Sequential), "invalid Pari proof batch");
        }
        let mut relation = item.envelope.to_bytes();
        relation[2] ^= 1;
        let changed = Envelope::from_bytes(&relation).context("changed relation must decode")?;
        expected_rejection(registry().verify(Family::Transfer, &item.statement, &changed), "wrong proof relation");
        let bytes = item.envelope.to_bytes();
        expected_rejection(Envelope::from_bytes(&bytes[..bytes.len() - 1]), "invalid Pari envelope length");
        let mut extended = bytes.clone(); extended.push(0);
        expected_rejection(Envelope::from_bytes(&extended), "invalid Pari envelope length");
        let mut suite = bytes; suite[0] ^= 1;
        expected_rejection(Envelope::from_bytes(&suite), "unsupported cryptographic suite");
    }
    registry().verify_items(items, &Sequential)?;
    let context = tx.context();
    expected_rejection(transfer_check_stateless_and_extract(body_transfer(&tx)?, &context,
        TransferProofContext::FeeFunding), "transfer proof context does not match its transaction location");
    expected_rejection(transfer_check_stateless_and_extract(&tx.transaction_body.fee_funding.as_ref()
        .context("actual fee")?.transfer, &context, TransferProofContext::Ordinary),
        "transfer proof context does not match its transaction location");
    Ok(())
}

#[tokio::test(flavor = "multi_thread")]
async fn genuine_transfer_slot_capabilities_and_exact_cache_reuse() -> Result<()> {
    use crate::stateless_cache::VerifiedTxArtifact;
    use shieldd_sdk_circuits::proof::Family;
    let fixtures = family_fixtures().await?;
    let bytes = &fixtures.fee_funding_fixture.tx_bytes;
    let tx = Arc::new(Transaction::decode_canonical(bytes)?);
    let extracted = App::build_tx_artifacts_extracted(&[tx]).await?;
    let artifact = extracted[0].clone();
    let items = &artifact.proof_items[&Family::Transfer];
    assert_eq!(items.len(), 2);
    assert_ne!(items[0], items[1], "slot-swap control must be nonvacuous");
    let capabilities = registry().verify_items(items, &Sequential)?;
    let rows = vec![(ProofSlot::BodyAction(0), capabilities[0].clone()),
                    (ProofSlot::FeeFunding, capabilities[1].clone())];
    let verified = Arc::new(VerifiedTxArtifact::new(artifact.clone(), rows.clone(), &registry())?);
    let mut reversed = rows.clone(); reversed.reverse();
    VerifiedTxArtifact::new(artifact.clone(), reversed, &registry())?;
    expected_rejection(VerifiedTxArtifact::new(artifact.clone(), vec![rows[0].clone(), rows[0].clone()], &registry()),
        "duplicate verified proof capability");
    expected_rejection(VerifiedTxArtifact::new(artifact.clone(), vec![rows[0].clone()], &registry()),
        "verified proof-slot coverage mismatch");
    expected_rejection(VerifiedTxArtifact::new(artifact.clone(), vec![rows[0].clone(), rows[1].clone(),
        (ProofSlot::BodyAction(1), capabilities[0].clone())], &registry()), "verified proof-slot coverage mismatch");
    expected_rejection(VerifiedTxArtifact::new(artifact, vec![(ProofSlot::BodyAction(0), capabilities[1].clone()),
        (ProofSlot::FeeFunding, capabilities[0].clone())], &registry()), "verified proof capability mismatch");
    let cache = StatelessCache::new();
    cache.insert_fully_verified(bytes, verified.clone())?;
    let hash = tx_hash(bytes);
    assert!(matches!(cache.get(registry().id(), &hash, bytes), Some(CacheEntry::FullyVerified(_))));
    let mut wrong_registry = registry().id(); wrong_registry[0] ^= 1;
    assert!(cache.get(wrong_registry, &hash, bytes).is_none());
    let mut changed_bytes = bytes.to_vec(); changed_bytes.push(0);
    // Deliberately reuse the original lookup hash. Full raw comparison must
    // refuse independently of whether a cryptographic hash collision exists.
    assert!(cache.get(registry().id(), &hash, &changed_bytes).is_none());
    expected_rejection(cache.insert_fully_verified(&changed_bytes, verified),
        "stateless cache artifact transaction does not match raw transaction");
    assert!(matches!(cache.get(registry().id(), &hash, bytes), Some(CacheEntry::FullyVerified(_))));
    Ok(())
}

fn body_transfer(tx: &Transaction) -> Result<&shieldd_sdk_shielded_pool::Transfer> {
    let [Action::Transfer(transfer)] = tx.transaction_body.actions.as_slice() else {
        anyhow::bail!("control requires exactly one actual body Transfer")
    };
    Ok(transfer)
}

#[derive(Debug, PartialEq, Eq)]
struct EffectSnapshot {
    nullifiers: Vec<Nullifier>,
    notes: Vec<(tct::Position, Vec<u8>, CommitmentSource)>,
    volumes: Vec<(tct::Position, Vec<u8>, CommitmentSource)>,
    routes: Vec<([u8; 32], u32, Vec<u32>, Vec<u64>)>,
    position: Option<tct::Position>,
    indexed: Vec<Vec<u8>>,
    deferred: Vec<Vec<u8>>,
    spend_checks: Vec<(Nullifier, bool)>,
    volume_checks: Vec<(u64, Nullifier, bool)>,
    volume_day_markers: Vec<(u64, Option<Vec<u8>>)>,
}

async fn effect_snapshot(app: &App, transactions: &[&Transaction]) -> Result<EffectSnapshot> {
    let mut spend_checks = Vec::new();
    let mut volume_checks = Vec::new();
    let mut volume_day_markers = Vec::new();
    for tx in transactions {
        for nullifier in tx.spent_nullifiers() {
            spend_checks.push((nullifier, app.state.is_nullifier_spent(nullifier).await?));
        }
        let mut transfers = vec![body_transfer(tx)?];
        if let Some(fee) = &tx.transaction_body.fee_funding {
            transfers.push(&fee.transfer);
        }
        for transfer in transfers {
            let volume = &transfer.body.volume_accumulator;
            volume_checks.push((volume.day_start, volume.nullifier,
                app.state.volume_nullifier_exists(volume.day_start, volume.nullifier).await?));
            volume_day_markers.push((volume.day_start, app.state.get_raw(
                &shieldd_sdk_shielded_pool::state_key::volume_nullifiers::day_marker(volume.day_start)
            ).await?));
        }
    }
    let height = app.state.get_block_height().await?;
    Ok(EffectSnapshot {
        nullifiers: app.state.pending_nullifiers().iter().copied().collect(),
        notes: pending_note_records(app),
        volumes: app.state.pending_volume_accumulator_payloads().iter()
            .map(|(position, payload, source)| (*position, payload.encode_to_vec(), source.clone()))
            .collect(),
        routes: app.state.pending_routing_actions().iter().map(|route| (
            route.transaction_id.0, route.action_index,
            route.tags.iter().map(|tag| tag.value).collect(), route.payload_positions.clone(),
        )).collect(),
        position: app.state.get_sct_position().await?,
        indexed: app.state.transactions_by_height(height).await?.transactions.iter()
            .map(|tx| tx.encode_to_vec()).collect(),
        deferred: app.deferred_block_transactions.iter().map(|tx| tx.encode_to_vec()).collect(),
        spend_checks,
        volume_checks,
        volume_day_markers,
    })
}

async fn assert_exact_transfer_effects(app: &App, tx: &Transaction) -> Result<()> {
    let body = body_transfer(tx)?;
    let mut transfers = vec![body];
    if let Some(fee) = &tx.transaction_body.fee_funding {
        transfers.push(&fee.transfer);
    }
    // The intent builder supplies one real spend and pads the second. Persist
    // every serialized slot; no witness-only filtering is permitted here.
    let expected_nullifiers = transfers.iter().flat_map(|transfer| {
        assert_eq!(transfer.body.inputs.len(), 2);
        transfer.body.inputs.iter().map(|input| input.nullifier)
    }).collect::<Vec<_>>();
    assert_eq!(app.state.pending_nullifiers().iter().copied().collect::<Vec<_>>(), expected_nullifiers);
    for nullifier in &expected_nullifiers {
        assert!(app.state.is_nullifier_spent(*nullifier).await?);
    }
    let expected_outputs = transfers.iter().flat_map(|transfer| {
        assert_eq!(transfer.body.outputs.len(), 2);
        transfer.body.outputs.iter().map(|output| output.note_payload.encode_to_vec())
    }).collect::<Vec<_>>();
    let notes = app.state.pending_note_payloads();
    assert_eq!(notes.iter().map(|(_, note, _)| note.encode_to_vec()).collect::<Vec<_>>(), expected_outputs);
    let volumes = app.state.pending_volume_accumulator_payloads();
    assert_eq!(volumes.len(), 1, "ordinary body alone emits volume, including disclosed padding");
    assert_eq!(volumes[0].1, body.body.volume_accumulator);
    assert!(app.state.volume_nullifier_exists(body.body.volume_accumulator.day_start,
        body.body.volume_accumulator.nullifier).await?);
    if let Some(fee) = &tx.transaction_body.fee_funding {
        assert_eq!(fee.transfer.body.volume_accumulator,
            shieldd_sdk_shielded_pool::VolumeAccumulatorPayload::canonical_fee_funding());
        assert!(!app.state.volume_nullifier_exists(0, fee.transfer.body.volume_accumulator.nullifier).await?);
    }
    let routes = app.state.pending_routing_actions();
    assert_eq!(routes.len(), transfers.len());
    for (index, transfer) in transfers.iter().enumerate() {
        assert_eq!(routes[index].transaction_id, tx.id());
        assert_eq!(routes[index].action_index, index as u32);
        assert_eq!(routes[index].tags, transfer.body.routing.tags.to_vec());
        let mut positions = vec![u64::from(notes[2 * index].0), u64::from(notes[2 * index + 1].0)];
        if index == 0 { positions.push(u64::from(volumes[0].0)); }
        positions.sort_unstable();
        assert_eq!(routes[index].payload_positions, positions,
            "routing must reference exact ordered outputs and only ordinary volume");
    }
    Ok(())
}

#[tokio::test(flavor = "multi_thread")]
async fn genuine_transfer_all_slots_volume_and_fee_order() -> Result<()> {
    let fixtures = family_fixtures().await?;
    let ordinary = fixtures.fixtures.iter().find(|fixture|
        fixture.family == DeployedProofFamily::Transfer).context("ordinary fixture")?;
    for fixture in [ordinary, &fixtures.fee_funding_fixture] {
        let tx = Transaction::decode_canonical(&fixture.tx_bytes)?;
        let storage = build_fixture_storage().await?;
        let mut app = App::new(storage.latest_snapshot(), registry(), storage.reader.clone()).await?;
        let context = app.benchmark_block_context().await?;
        app.begin_block(&cnidarium_component::BlockContext { height: context.height, time: context.time }).await?;
        app.deliver_tx_bytes(&fixture.tx_bytes, Some(&StatelessCache::new())).await?;
        assert_exact_transfer_effects(&app, &tx).await?;
        let expected_routes = app.state.pending_routing_actions().iter()
            .map(|route| (route.transaction_id, route.action_index, route.payload_positions.clone()))
            .collect::<Vec<_>>();
        // Check durable all-slot and ordered payload correspondence as well.
        app.end_block(context.height).await;
        app.commit_for_testing(storage.as_ref().clone()).await?;
        let committed = storage.latest_snapshot();
        let compact: shieldd_sdk_compact_block::CompactBlock = committed.compact_block(context.height)
            .await?.context("compact block")?.try_into()?;
        assert_eq!(compact.state_payloads.iter().map(|payload| *payload.commitment()).collect::<Vec<_>>(),
            tx.state_commitments().collect::<Vec<_>>());
        assert_eq!(compact.routing_actions.iter()
            .map(|route| (route.transaction_id, route.action_index, route.payload_positions.clone()))
            .collect::<Vec<_>>(), expected_routes);
        for nullifier in tx.spent_nullifiers() {
            assert!(app.nullifier_reader().contains(&committed, &[nullifier]).await?[0]);
            assert!(compact.nullifiers.contains(&nullifier));
        }
        let body = body_transfer(&tx)?;
        assert!(committed.volume_nullifier_exists(body.body.volume_accumulator.day_start,
            body.body.volume_accumulator.nullifier).await?);
        if let Some(fee) = &tx.transaction_body.fee_funding {
            assert!(!committed.volume_nullifier_exists(0, fee.transfer.body.volume_accumulator.nullifier).await?);
        }
    }
    Ok(())
}

#[tokio::test(flavor = "multi_thread")]
async fn genuine_transfer_daily_replay_rejects_before_spends() -> Result<()> {
    let fixtures = family_fixtures().await?;
    let fixture = fixtures.fixtures.iter().find(|fixture|
        fixture.family == DeployedProofFamily::Transfer).context("ordinary fixture")?;
    let tx = Transaction::decode_canonical(&fixture.tx_bytes)?;
    let storage = build_fixture_storage().await?;
    let mut app = App::new(storage.latest_snapshot(), registry(), storage.reader.clone()).await?;
    let context = app.benchmark_block_context().await?;
    app.begin_block(&cnidarium_component::BlockContext { height: context.height, time: context.time }).await?;
    let volume = &body_transfer(&tx)?.body.volume_accumulator;
    {
        let mut state = app.state.try_begin_transaction().context("unique test state")?;
        state.record_volume_nullifier(volume.day_start, volume.nullifier).await?;
        state.apply();
    }
    for nullifier in tx.spent_nullifiers() { assert!(!app.state.is_nullifier_spent(nullifier).await?); }
    let before = effect_snapshot(&app, &[&tx]).await?;
    let error = app.deliver_tx_bytes(&fixture.tx_bytes, None).await.expect_err("day-scoped replay");
    assert!(format!("{error:#}").contains("daily volume nullifier"), "{error:#}");
    assert_eq!(effect_snapshot(&app, &[&tx]).await?, before);
    Ok(())
}

#[tokio::test(flavor = "multi_thread")]
async fn genuine_transfer_late_failure_preserves_prior_effects_and_indexes() -> Result<()> {
    let (storage, node, bytes) = setup_test_txs(2).await?;
    let first = Transaction::decode_canonical(&bytes[0])?;
    let second = Transaction::decode_canonical(&bytes[1])?;
    for mode in [BlockTxIndexingMode::PerTx, BlockTxIndexingMode::DeferredBatch] {
        for fault in [1u8, 2u8] {
            let mut app = App::new(storage.latest_snapshot(), registry(), node.execution.nullifier_reader()).await?;
            app.set_block_tx_indexing_mode(mode);
            let context = app.benchmark_block_context().await?;
            app.begin_block(&cnidarium_component::BlockContext { height: context.height, time: context.time }).await?;
            let cache = StatelessCache::new();
            app.deliver_tx_bytes(&bytes[0], Some(&cache)).await?;
            for nullifier in second.spent_nullifiers() { assert!(!app.state.is_nullifier_spent(nullifier).await?); }
            let volume = &body_transfer(&second)?.body.volume_accumulator;
            assert!(!app.state.volume_nullifier_exists(volume.day_start, volume.nullifier).await?);
            {
                let mut state = app.state.try_begin_transaction().context("unique test state")?;
                state.object_put(EFFECT_FAULT, (second.id().0, fault));
                state.apply();
            }
            let before = effect_snapshot(&app, &[&first, &second]).await?;
            assert_eq!(before.nullifiers.len(), 2);
            assert_eq!(before.notes.len(), 2);
            assert_eq!(before.volumes.len(), 1);
            assert_eq!(before.routes.len(), 1);
            match mode {
                BlockTxIndexingMode::PerTx => {
                    assert_eq!(before.indexed.len(), 1);
                    assert!(before.deferred.is_empty());
                }
                BlockTxIndexingMode::DeferredBatch => {
                    assert!(before.indexed.is_empty());
                    assert_eq!(before.deferred.len(), 1);
                }
                BlockTxIndexingMode::NoIndex => unreachable!("control covers production indexes"),
            }
            let error = app.deliver_tx_bytes(&bytes[1], Some(&cache)).await.expect_err("late injected fault");
            let expected = if fault == 1 { "fv.Transfer.after_routing" } else { "fv.Transfer.after_index" };
            assert!(format!("{error:#}").contains(expected), "{error:#}");
            assert_eq!(effect_snapshot(&app, &[&first, &second]).await?, before,
                "all target effects must roll back while the earlier genuine Transfer remains staged");
        }
    }
    Ok(())
}


// Warm cache validity is stateless. Every subcase uses the same canonical,
// genuinely proved transaction on the same unspent committed parent; only
// current pending state differs. No proof bytes or capability are fabricated.
#[tokio::test(flavor = "multi_thread")]
async fn genuine_transfer_cached_artifact_rechecks_volume_and_every_spend_slot() -> Result<()> {
    let fixtures = family_fixtures().await?;
    let bytes = &fixtures.fee_funding_fixture.tx_bytes;
    let tx = Transaction::decode_canonical(bytes)?;
    let spends = tx.spent_nullifiers().collect::<Vec<_>>();
    assert_eq!(spends.len(), 4, "both body slots then both fee slots, including padding");
    assert_eq!(spends.iter().copied().collect::<std::collections::BTreeSet<_>>().len(), 4,
        "each stale-slot control must be independent");
    let ordinary_volume = &body_transfer(&tx)?.body.volume_accumulator;
    let storage = build_fixture_storage().await?;
    let cache = StatelessCache::new();
    {
        let mut probe = App::new(storage.latest_snapshot(), registry(), storage.reader.clone()).await?;
        let context = probe.benchmark_block_context().await?;
        probe.begin_block(&cnidarium_component::BlockContext {
            height: context.height, time: context.time,
        }).await?;
        probe.deliver_tx_bytes(bytes, Some(&cache)).await
            .context("genuine positive delivery must warm the exact stateless cache")?;
        assert_exact_transfer_effects(&probe, &tx).await?;
        // Discard the working state: this positive must not commit its spends.
    }
    let hash = tx_hash(bytes);
    let cached = match cache.get(registry().id(), &hash, bytes) {
        Some(CacheEntry::FullyVerified(artifact)) => artifact,
        _ => anyhow::bail!("positive delivery did not retain the genuine verified artifact"),
    };
    assert_eq!(cached.tx().encode_to_vec(), *bytes);
    for stale_case in 0..=spends.len() {
        let mut app = App::new(storage.latest_snapshot(), registry(), storage.reader.clone()).await?;
        let context = app.benchmark_block_context().await?;
        app.begin_block(&cnidarium_component::BlockContext {
            height: context.height, time: context.time,
        }).await?;
        for nullifier in &spends {
            assert!(!app.state.is_nullifier_spent(*nullifier).await?);
        }
        assert!(!app.state.volume_nullifier_exists(ordinary_volume.day_start,
            ordinary_volume.nullifier).await?);
        let expected = {
            let mut state = app.state.try_begin_transaction().context("unique stale-control state")?;
            let expected = if stale_case == 0 {
                state.record_volume_nullifier(ordinary_volume.day_start,
                    ordinary_volume.nullifier).await?;
                format!("daily volume nullifier {} is already spent for UTC day {}",
                    ordinary_volume.nullifier, ordinary_volume.day_start)
            } else {
                let nullifier = spends[stale_case - 1];
                state.nullify_all(&[nullifier], tx.id().into()).await?;
                format!("nullifier {nullifier} was already spent in this block")
            };
            let _ = state.apply();
            expected
        };
        let before = effect_snapshot(&app, &[&tx]).await?;
        // The hit is still the exact previously verified Arc after state changes.
        assert!(matches!(cache.get(registry().id(), &hash, bytes),
            Some(CacheEntry::FullyVerified(ref artifact)) if Arc::ptr_eq(artifact, &cached)));
        expected_rejection(app.deliver_tx_bytes(bytes, Some(&cache)).await, &expected);
        assert_eq!(effect_snapshot(&app, &[&tx]).await?, before,
            "stale cached case {stale_case} leaked effects or indexes");
        assert!(matches!(cache.get(registry().id(), &hash, bytes),
            Some(CacheEntry::FullyVerified(ref artifact)) if Arc::ptr_eq(artifact, &cached)),
            "state rejection must not poison the valid stateless cache");
    }
    Ok(())
}
