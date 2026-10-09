// Deferred append to the already prepared Transfer effect-control module.
// Test-genesis reachability only: two native MAX allocations, real proofs,
// original complete carriers, signatures and current-state delivery. This does
// not assert the external host permits this aggregate supply on a live chain.
mod fee_reachability {
    use super::*;
    use futures::FutureExt as _;
    use shieldd_sdk_fee::{component::StateReadExt as _, Fee};
    use std::panic::AssertUnwindSafe;

    fn addition_overflow(payload: Box<dyn std::any::Any + Send>) {
        let message = payload.downcast_ref::<String>().map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .expect("native panic must carry the intended arithmetic message");
        assert!(message.contains("attempt to add with overflow"),
            "unrelated native panic cannot establish this control: {message}");
    }

    #[tokio::test(flavor = "multi_thread")]
    async fn genuine_transfer_test_genesis_high_tips_observe_native_accumulation() -> Result<()> {
        let storage = TempStorage::new_with_prefixes(SUBSTORE_PREFIXES.to_vec()).await?;
        let allocations = (0..2).map(|_| Allocation {
            raw_amount: u128::MAX.into(),
            raw_denom: BASE_ASSET_DENOM.deref().base_denom().denom,
            address: test_keys::ADDRESS_0.to_owned(),
        }).collect();
        let genesis = AppState::Content(Content {
            chain_id: TEST_CHAIN_ID.to_owned(),
            shielded_pool_content: shieldd_sdk_shielded_pool::genesis::Content {
                allocations, ..Default::default()
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
        anyhow::ensure!(notes.len() == 2 && notes.iter().all(|note|
            note.amount() == Amount::from(u128::MAX)) && notes[0].commit() != notes[1].commit(),
            "actual MAX test-genesis notes must be distinct and present");
        let prices = storage.latest_snapshot().get_gas_prices().await?;
        assert_eq!(prices, shieldd_sdk_fee::GasPrices::zero(),
            "native zero base prices are checked, not supplied as an inference");
        let fee_amount = Amount::from(u128::MAX - 1);
        let mut transactions = Vec::new();
        for (index, note) in notes.into_iter().enumerate() {
            let intent = shieldd_sdk_mock_client::TransferIntent {
                spends: vec![spend_plan(&client, note.clone())?],
                outputs: vec![
                    ShieldedOutputPlan::new(&mut OsRng, Value {
                        amount: Amount::from(1u64), asset_id: *BASE_ASSET_ID,
                    }, test_keys::ADDRESS_1.deref().clone()),
                    ShieldedOutputPlan::new(&mut OsRng, Value {
                        amount: Amount::zero(), asset_id: *BASE_ASSET_ID,
                    }, note.address()),
                ],
                value_blinding: Fr::from(u64::try_from(index)? + 1),
            };
            let plan = client.complete_intent(shieldd_sdk_mock_client::TransactionIntent {
                actions: vec![intent.into()], memo: None, fee_funding: None,
                transaction_parameters: TransactionParameters {
                    chain_id: TEST_CHAIN_ID.to_owned(),
                    fee: Fee::from_staking_token_amount(fee_amount),
                    ..Default::default()
                },
            }, storage.latest_snapshot()).await?;
            let tx = client.witness_auth_build(&plan, registry()).await
                .context("actual same-carrier high-fee Transfer prove/auth/build")?;
            let decoded = Transaction::decode_canonical(&tx.encode_to_vec())?;
            assert_eq!(decoded.transaction_body.transaction_parameters.fee.amount(), fee_amount);
            let extracted = App::build_tx_artifacts_extracted(&[Arc::new(decoded.clone())]).await?;
            let items = &extracted[0].proof_items[&shieldd_sdk_circuits::proof::Family::Transfer];
            assert_eq!(items.len(), 1);
            registry().verify_item(&items[0]).context("positive genuine same-key proof verification")?;
            transactions.push(decoded);
        }
        let first = &transactions[0];
        let second = &transactions[1];
        assert_ne!(first.id(), second.id());
        let first_spends = first.spent_nullifiers().collect::<Vec<_>>();
        let second_spends = second.spent_nullifiers().collect::<Vec<_>>();
        assert_eq!(first_spends.len(), 2);
        assert_eq!(second_spends.len(), 2);
        assert!(second_spends.iter().all(|nullifier| !first_spends.contains(nullifier)),
            "all genuine real and padded spend slots must be disjoint");
        let first_volume = &body_transfer(first)?.body.volume_accumulator;
        let second_volume = &body_transfer(second)?.body.volume_accumulator;
        assert_ne!((first_volume.day_start, first_volume.nullifier),
            (second_volume.day_start, second_volume.nullifier), "volume replay is a different failure");
        let mut app = App::new(storage.latest_snapshot(), registry(), node.execution.nullifier_reader()).await?;
        let context = app.benchmark_block_context().await?;
        app.begin_block(&cnidarium_component::BlockContext {
            height: context.height, time: context.time,
        }).await?;
        assert_eq!(app.state.block_fees(), shieldd_sdk_fee::component::BlockFees::default());
        app.deliver_tx_bytes(&first.encode_to_vec(), None).await
            .context("first genuine high-fee positive delivery required")?;
        assert_eq!(app.state.block_fees(), shieldd_sdk_fee::component::BlockFees {
            base: Amount::zero(), tip: fee_amount,
        });
        assert_exact_transfer_effects(&app, first).await?;
        let before = effect_snapshot(&app, &[first, second]).await?;
        let second_bytes = second.encode_to_vec();
        let result = AssertUnwindSafe(app.deliver_tx_bytes(&second_bytes, None)).catch_unwind().await;
        match result {
            Ok(Ok(_)) => {
                assert_eq!(app.state.block_fees(), shieldd_sdk_fee::component::BlockFees {
                    base: Amount::zero(), tip: Amount::from(u128::MAX - 3),
                });
                for nullifier in first.spent_nullifiers().chain(second.spent_nullifiers()) {
                    assert!(app.state.is_nullifier_spent(nullifier).await?);
                }
                let after = effect_snapshot(&app, &[first, second]).await?;
                assert_eq!(after.nullifiers.len(), before.nullifiers.len() + 2);
                assert_eq!(after.notes.len(), before.notes.len() + 2);
                assert_eq!(after.volumes.len(), before.volumes.len() + 1);
                eprintln!("native genuine fee reachability mode: wrapped tips after two actual positive deliveries");
            }
            Ok(Err(error)) => anyhow::bail!("unrelated rejection is not an arithmetic control: {error:#}"),
            Err(payload) => {
                addition_overflow(payload);
                assert_eq!(app.state.block_fees(), shieldd_sdk_fee::component::BlockFees {
                    base: Amount::zero(), tip: fee_amount,
                });
                assert_eq!(effect_snapshot(&app, &[first, second]).await?, before,
                    "actual delivery unwind must drop second transaction effects");
                eprintln!("native genuine fee reachability mode: checked tip addition panic; second delta dropped");
            }
        }
        Ok(())
    }
}
