// Source-only diagnostic, included in the existing service_contract_tests module.
// Empty native blocks exercise exact boundaries, not proved Transfer admission.
// No prover, genuine-transfer or power-loss durability credit is implied.
#[tokio::test]
async fn fv_old_published_nullifier_boundary_is_unavailable_until_republication() -> Result<()> {
    let (_storage, mut client) = initialized_client().await?;
    let queries = client.queries().clone();
    let old_snapshot = queries.snapshot()?;
    let nullifier = shieldd_sdk_sct::Nullifier(shieldd_sdk_crypto::Fq::from(777u64));
    let request = || NullifierRequest { nullifier: Some(nullifier.into()) };
    let before: shieldd_sdk_sct::permanent_nullifiers::Status =
        queries.nullifier_status(request()).await?.try_into()?;
    assert!(!before.spent);
    before.verify(&before.boundary)?;
    assert_eq!(before.boundary.height, Some(0));

    let mut begin = BeginBlockRequest {
        block_id: vec![1u8; 32], height: 1, time: Some(Default::default()),
    };
    begin.time.as_mut().unwrap().seconds = 1_700_000_000;
    client.begin_block(begin).await?;
    let ended = client.end_block(EndBlockRequest { height: 1 }).await?;
    client.seal_commit(SealCommitRequest { expected: ended.prepared }).await?;
    client.commit(CommitRequest {}).await?;
    let durable = client.get_committed_state(GetCommittedStateRequest {}).await?;
    assert_eq!(durable.height, 1);
    assert_eq!(queries.snapshot()?.version(), old_snapshot.version());
    // Even an empty block changes the exact boundary. The published snapshot
    // remains old while the shared permanent reader follows durable state.
    let stale = queries.nullifier_status(request()).await
        .expect_err("old published boundary must not return an absence proof");
    assert_eq!(stale.kind(), ErrorKind::Unavailable);
    assert!(queries.nullifiers()?.validate_boundary(&before.boundary).is_err());
    let mut wrong = durable.clone();
    wrong.block_id[0] ^= 1;
    assert!(queries.publish_committed(wrong).await.is_err());
    assert_eq!(queries.snapshot()?.version(), old_snapshot.version());
    assert_eq!(queries.nullifier_status(request()).await.unwrap_err().kind(), ErrorKind::Unavailable);

    queries.publish_committed(durable).await?;
    let after: shieldd_sdk_sct::permanent_nullifiers::Status =
        queries.nullifier_status(request()).await?.try_into()?;
    assert!(!after.spent);
    assert_eq!(after.boundary.height, Some(1));
    after.verify(&after.boundary)?;
    assert!(before.verify(&after.boundary).is_err());
    assert!(queries.snapshot()?.version() > old_snapshot.version());
    Ok(())
}
