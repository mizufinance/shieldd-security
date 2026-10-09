// Native no-prover branch diagnostic. Included inside app::host::tests.
// Queue entries are deliberate canonical no-action fixtures injected directly
// into the private deferred queue; they are NOT stateless-admitted transactions
// or genuine Transfer proofs. PASS demonstrates this source branch only.
use futures::FutureExt as _;
use shieldd_sdk_proto::DomainType as _;

async fn fv_indexing_host() -> Result<(TempStorage, HostExecution)> {
    let storage = temp_storage().await;
    let mut host = HostExecution::new(storage.deref().clone(), crate::app::tests::registry()).await?;
    host.init_genesis(host_genesis()).await?;
    host.commit().await?;
    host.begin_block(host_block(1)).await?;
    Ok((storage, host))
}

fn fv_indexing_canonical_no_action_entry() -> Result<shieldd_sdk_proto::core::transaction::v1::Transaction> {
    let tx = Transaction {
        transaction_body: shieldd_sdk_transaction::TransactionBody::default(),
        binding_sig: [0u8; 64].into(),
        anchor: shieldd_sdk_tct::Tree::default().root(),
    };
    let decoded = Transaction::decode_canonical(&tx.encode_to_vec())?;
    anyhow::ensure!(decoded.id() == tx.id(), "canonical no-action fixture identity");
    Ok(decoded.into())
}

async fn fv_indexing_duplicate_queue_fault(host: &mut HostExecution) -> Result<()> {
    let entry = fv_indexing_canonical_no_action_entry()?;
    host.app.deferred_block_transactions = vec![entry.clone(), entry];
    anyhow::ensure!(host.app.state.block_transaction_count(1).await? == 0, "empty entry index");
    let outcome = std::panic::AssertUnwindSafe(host.end_block(1)).catch_unwind().await;
    let payload = match outcome {
        Err(payload) => payload,
        Ok(Err(error)) => anyhow::bail!("expected exact end-block flush panic, got ordinary error: {error:#}"),
        Ok(Ok(_)) => anyhow::bail!("duplicate diagnostic queue unexpectedly flushed"),
    };
    let message = payload.downcast_ref::<String>().map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied()).unwrap_or("non-string panic");
    anyhow::ensure!(message.contains("must be able to flush deferred block transactions in end_block")
        && message.contains("duplicate committed transaction"), "unexpected panic cause: {message}");
    anyhow::ensure!(host.phase() == HostExecutionPhase::InBlock, "native panic phase changed");
    anyhow::ensure!(host.app.deferred_block_transactions.is_empty(), "native failed flush did not drain");
    anyhow::ensure!(host.app.state.block_transaction_count(1).await? == 0,
        "failed separate index savepoint was applied");
    Ok(())
}

#[tokio::test]
async fn fv_deferred_queue_fault_drains_without_durable_commit() -> Result<()> {
    let (_storage, mut host) = fv_indexing_host().await?;
    let committed = host.committed_state().await?;
    fv_indexing_duplicate_queue_fault(&mut host).await?;
    anyhow::ensure!(host.committed_state().await? == committed, "fault advanced durable boundary");
    anyhow::ensure!(host.commit().await.is_err(), "unsealed faulted host committed");
    anyhow::ensure!(host.committed_state().await? == committed, "rejected commit advanced boundary");
    Ok(())
}

#[tokio::test]
async fn fv_same_instance_endblock_retry_after_queue_fault() -> Result<()> {
    let (storage, mut host) = fv_indexing_host().await?;
    let committed = host.committed_state().await?;
    fv_indexing_duplicate_queue_fault(&mut host).await?;
    host.end_block(1).await?;
    anyhow::ensure!(host.app.deferred_block_transactions.is_empty(), "retry recreated consumed queue");
    anyhow::ensure!(host.committed_state().await? == committed, "end-block made state durable");
    host.seal_commit()?;
    host.commit().await?;
    anyhow::ensure!(host.committed_state().await?.height == 1, "retry did not commit diagnostic empty block");
    anyhow::ensure!(storage.latest_snapshot().block_transaction_count(1).await? == 0,
        "drained diagnostic entries unexpectedly indexed");
    // This expected branch behavior is NOT a security-positive retry assertion:
    // no queue entry was admitted, and no Transfer effects were constructed.
    Ok(())
}

#[tokio::test]
async fn fv_host_rollback_after_queue_fault_restores_committed_parent() -> Result<()> {
    let (_storage, mut host) = fv_indexing_host().await?;
    let committed = host.committed_state().await?;
    fv_indexing_duplicate_queue_fault(&mut host).await?;
    host.rollback().await?;
    anyhow::ensure!(host.phase() == HostExecutionPhase::Idle, "rollback phase");
    anyhow::ensure!(host.committed_state().await? == committed, "rollback changed committed parent");
    anyhow::ensure!(host.app.deferred_block_transactions.is_empty(), "rollback retained failed queue");
    anyhow::ensure!(host.app.state.get_block_height().await? == committed.height, "working height not restored");
    host.begin_block(host_block(1)).await?;
    host.end_block(1).await?;
    host.seal_commit()?;
    host.commit().await?;
    anyhow::ensure!(host.committed_state().await?.height == 1, "fresh empty block failed after rollback");
    Ok(())
}
