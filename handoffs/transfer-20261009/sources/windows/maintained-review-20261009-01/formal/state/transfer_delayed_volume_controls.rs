// Append only to a fresh prepared Transfer effect-control child.
// Both original carriers are genuinely proved and fully verified. The valid
// native plans deliberately share a padding seed to target the same Ordinary
// day/nullifier. This is not a regulated aggregate-volume-cap control.
mod delayed_volume {
    use super::*;
    use shieldd_sdk_fee::component::StateReadExt as _;
    use shieldd_sdk_sct::component::source::SourceContext as _;
    use shieldd_sdk_shielded_pool::{TransferProofContext, VolumeAccumulatorPlan};
    use shieldd_sdk_shielded_pool::component::{
        transfer_execute_validated, transfer_validate_verified,
    };

    #[tokio::test(flavor = "multi_thread")]
    async fn genuine_delayed_ordinary_token_rechecks_volume_then_child_drop_restores_state() -> Result<()> {
        let storage = TempStorage::new_with_prefixes(SUBSTORE_PREFIXES.to_vec()).await?;
        let genesis = AppState::Content(Content {
            chain_id: TEST_CHAIN_ID.to_owned(),
            shielded_pool_content: shieldd_sdk_shielded_pool::genesis::Content {
                allocations: (0..2).map(|_| Allocation {
                    raw_amount: 1_000_000u128.into(),
                    raw_denom: BASE_ASSET_DENOM.deref().base_denom().denom,
                    address: test_keys::ADDRESS_0.to_owned(),
                }).collect(),
                ..Default::default()
            },
            ..Default::default()
        });
        let mut node = TestHost::new(storage.as_ref().clone(), genesis,
            Time::parse_from_rfc3339("2026-01-01T00:00:00Z")?, registry()).await?;
        node.execute(Vec::new()).await?;
        let client = MockClient::new(test_keys::SPEND_KEY.clone())
            .with_sync_to_storage(&storage).await?;
        let notes = client.notes.values().filter(|note|
            note.asset_id() == *BASE_ASSET_ID && note.address() == test_keys::ADDRESS_0.deref().clone())
            .cloned().collect::<Vec<_>>();
        anyhow::ensure!(notes.len() == 2 && notes[0].commit() != notes[1].commit(),
            "two distinct genuine genesis notes are required");
        let mut plans = Vec::new();
        for (index, note) in notes.into_iter().enumerate() {
            let intent = shieldd_sdk_mock_client::TransactionIntent {
                actions: vec![shieldd_sdk_mock_client::TransferIntent {
                    spends: vec![spend_plan(&client, note.clone())?],
                    outputs: vec![
                        ShieldedOutputPlan::new(&mut OsRng, Value {
                            amount: Amount::from(1u64), asset_id: note.asset_id(),
                        }, test_keys::ADDRESS_1.deref().clone()),
                        ShieldedOutputPlan::new(&mut OsRng, Value {
                            amount: note.amount() - Amount::from(1u64), asset_id: note.asset_id(),
                        }, note.address()),
                    ],
                    value_blinding: Fr::from(u64::try_from(index)? + 1),
                }.into()],
                memo: None, fee_funding: None,
                transaction_parameters: TransactionParameters {
                    chain_id: TEST_CHAIN_ID.to_owned(), ..Default::default()
                },
            };
            plans.push(client.complete_intent(intent, storage.latest_snapshot()).await?);
        }
        let common_nonce = match &plans[0].actions[0] {
            ActionPlan::Transfer(plan) => plan.compliance.nonce.clone(),
            _ => anyhow::bail!("completed intent must contain Transfer"),
        };
        for plan in &mut plans {
            let transfer = match &mut plan.actions[0] {
                ActionPlan::Transfer(transfer) => transfer,
                _ => anyhow::bail!("completed intent must contain Transfer"),
            };
            assert_eq!(transfer.proof_context, TransferProofContext::Ordinary);
            assert!(!transfer.compliance.witness.asset.is_regulated);
            assert!(matches!(transfer.volume_accumulator, VolumeAccumulatorPlan::Padding { .. }));
            // Native input selection precedes all ciphertext/statement/proof/signature
            // construction. No proof bytes, public claim or completed action is patched.
            transfer.compliance.nonce = common_nonce.clone();
            transfer.validate()?;
        }
        let mut transactions = Vec::new();
        for plan in &plans {
            let tx = client.witness_auth_build(plan, registry()).await
                .context("genuine native witness/auth/prove/build required")?;
            transactions.push(Arc::new(Transaction::decode_canonical(&tx.encode_to_vec())?));
        }
        // The production full-carrier pipeline verifies exact proof occurrences,
        // binding and authorization signatures before a saved token is minted.
        let artifacts = App::build_tx_artifacts(registry(), &transactions).await?;
        assert_eq!(artifacts.len(), 2);
        let saved = &transactions[0];
        let competitor = &transactions[1];
        assert_ne!(saved.id(), competitor.id());
        let saved_transfer = body_transfer(saved)?;
        let competitor_transfer = body_transfer(competitor)?;
        let saved_volume = &saved_transfer.body.volume_accumulator;
        let competitor_volume = &competitor_transfer.body.volume_accumulator;
        assert_eq!((saved_volume.day_start, saved_volume.nullifier),
            (competitor_volume.day_start, competitor_volume.nullifier));
        let saved_spends = saved.spent_nullifiers().collect::<Vec<_>>();
        let competitor_spends = competitor.spent_nullifiers().collect::<Vec<_>>();
        assert_eq!(saved_spends.len(), 2);
        assert_eq!(competitor_spends.len(), 2);
        assert_eq!(saved_spends.iter().chain(&competitor_spends).copied()
            .collect::<std::collections::BTreeSet<_>>().len(), 4,
            "each real/padded input must be distinct so volume is the intended failure");
        let mut app = App::new(storage.latest_snapshot(), registry(), node.execution.nullifier_reader()).await?;
        app.set_block_tx_indexing_mode(BlockTxIndexingMode::PerTx);
        let context = app.benchmark_block_context().await?;
        app.begin_block(&cnidarium_component::BlockContext {
            height: context.height, time: context.time,
        }).await?;
        let saved_context = saved.context();
        let validated = {
            let mut validation_child = app.state.try_begin_transaction()
                .context("unique pre-interleaving validation state")?;
            transfer_validate_verified(saved_transfer, &saved_context,
                artifacts[0].proof_for_slot(ProofSlot::BodyAction(0))?,
                TransferProofContext::Ordinary, &mut validation_child).await?
        };
        assert!(!app.state.volume_nullifier_exists(saved_volume.day_start, saved_volume.nullifier).await?);
        app.deliver_tx_bytes(&competitor.encode_to_vec(), None).await
            .context("the genuine competing live body must actually succeed")?;
        assert_exact_transfer_effects(&app, competitor).await?;
        app.end_block(context.height).await;
        app.commit_for_testing(storage.as_ref().clone()).await?;
        let published = storage.latest_snapshot();
        let published_root = published.root_hash().await?;
        let published_boundary = shieldd_sdk_sct::permanent_nullifiers::read_boundary(&published).await?;
        let published_compact = published.compact_block(context.height).await?.context("competing compact block")?;
        let compact: shieldd_sdk_compact_block::CompactBlock = published_compact.clone().try_into()?;
        assert_eq!(compact.state_payloads.iter().map(|payload| *payload.commitment()).collect::<Vec<_>>(),
            competitor.state_commitments().collect::<Vec<_>>());
        assert_eq!(compact.nullifiers, competitor_spends);
        let published_index = published.transactions_by_height(context.height).await?;
        assert_eq!(published_index.transactions.len(), 1);
        assert_eq!(published_index.transactions[0].encode_to_vec(), competitor.encode_to_vec());
        assert!(published.volume_nullifier_exists(saved_volume.day_start, saved_volume.nullifier).await?);
        for nullifier in &saved_spends {
            assert!(!app.nullifier_reader().contains(&published, &[*nullifier]).await?[0]);
        }
        for nullifier in &competitor_spends {
            assert!(app.nullifier_reader().contains(&published, &[*nullifier]).await?[0]);
        }
        // Crossing a successful publication makes the published-root assertions
        // meaningful. This deliberately exercises the exported delayed-token API,
        // not the production immediate Ordinary body caller.
        let next = app.benchmark_block_context().await?;
        app.begin_block(&cnidarium_component::BlockContext { height: next.height, time: next.time }).await?;
        let before = effect_snapshot(&app, &[saved, competitor]).await?;
        let before_sct = app.state.try_get_sct().await?.root();
        let before_fees = app.state.block_fees();
        {
            let mut child = app.state.try_begin_transaction().context("unique delayed-token child")?;
            child.put_current_source(Some(saved.id()));
            let error = transfer_execute_validated(saved_transfer, &saved_context, validated, &mut child)
                .await.expect_err("saved Ordinary token must recheck the now-spent volume NF");
            let expected = format!("daily volume nullifier {} is already spent for UTC day {}",
                saved_volume.nullifier, saved_volume.day_start);
            assert_eq!(format!("{error:#}"), expected, "other admission failures do not count");
            // Raw execute is not itself atomic: observe its two spend and two note
            // writes after Err, before separately testing StateTransaction drop.
            assert_eq!(child.pending_nullifiers().iter().copied().collect::<Vec<_>>(), saved_spends);
            for nullifier in &saved_spends { assert!(child.is_nullifier_spent(*nullifier).await?); }
            assert_eq!(child.pending_note_payloads().iter().map(|(_, note, _)| note.encode_to_vec())
                .collect::<Vec<_>>(), saved_transfer.body.outputs.iter()
                    .map(|output| output.note_payload.encode_to_vec()).collect::<Vec<_>>());
            assert!(child.pending_volume_accumulator_payloads().is_empty(),
                "conflict must stop before appending the saved volume payload");
            assert!(child.volume_nullifier_exists(saved_volume.day_start, saved_volume.nullifier).await?);
            assert_ne!(child.try_get_sct().await?.root(), before_sct);
            assert!(child.pending_routing_actions().is_empty());
            assert_eq!(child.block_fees(), before_fees);
            eprintln!("DELAYED_ORDINARY_VOLUME raw_error_after_two_spends_two_notes");
            // No apply(): the enclosing child is discarded at this scope boundary.
        }
        assert_eq!(effect_snapshot(&app, &[saved, competitor]).await?, before);
        assert_eq!(app.state.try_get_sct().await?.root(), before_sct);
        assert_eq!(app.state.block_fees(), before_fees);
        let after = storage.latest_snapshot();
        assert_eq!(after.root_hash().await?, published_root);
        assert_eq!(shieldd_sdk_sct::permanent_nullifiers::read_boundary(&after).await?, published_boundary);
        assert_eq!(after.compact_block(context.height).await?.context("published compact block")?.encode_to_vec(),
            published_compact.encode_to_vec());
        assert_eq!(after.transactions_by_height(context.height).await?.encode_to_vec(), published_index.encode_to_vec());
        for nullifier in &saved_spends {
            assert!(!app.nullifier_reader().contains(&after, &[*nullifier]).await?[0]);
        }
        for nullifier in &competitor_spends {
            assert!(app.nullifier_reader().contains(&after, &[*nullifier]).await?[0]);
        }
        eprintln!("DELAYED_ORDINARY_VOLUME child_discard_preserves_parent_and_published_competitor");
        Ok(())
    }
}
