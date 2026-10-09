// One genuine transaction's effect bundle, replayed through HostExecution.
// Proof/signature validity and atomic storage batches are explicit abstractions.
// Cancellation is permitted before OR after durable write, never equated with
// no write. The Rust driver observes the actual boundary and all effect slots.
module execution {
  type Effects = { spent: bool, outputs: bool, indexed: bool }
  pure val empty: Effects = { spent: false, outputs: false, indexed: false }
  pure val applied: Effects = { spent: true, outputs: true, indexed: true }
  var pending: Effects
  var durable: Effects
  var phase: int // 0 idle, 1 in block, 2 ended, 3 commit interrupted
  var height: int
  var committedHeight: int
  var cache: bool
  var op: str
  var result: str
  var count: int
  var prior: Effects

  action init = all { pending' = empty, durable' = empty, phase' = 0,
    height' = 1, committedHeight' = 1, cache' = false,
    op' = "init", result' = "none", count' = 0, prior' = empty }

  action update(p: Effects, d: Effects, ph: int, h: int, ch: int, c: bool,
                name: str, outcome: str): bool = all {
    count < 12, pending' = p, durable' = d, phase' = ph, height' = h,
    committedHeight' = ch, cache' = c, op' = name, result' = outcome,
    prior' = pending, count' = count + 1 }

  action begin = all { phase == 0, committedHeight < 3,
    update(pending, durable, 1, committedHeight + 1, committedHeight, cache, "begin", "ok") }
  // HostExecution::check_tx has no mutation-phase guard: it always validates
  // against storage.latest_snapshot(), including during CommitInterrupted.
  action check = update(pending, durable, phase, height, committedHeight, true,
    "check", if (durable.spent) "rejected" else "ok")
  action deliver = all { phase == 1,
    update(if (pending.spent) pending else applied, durable, phase, height,
      committedHeight, true, "deliver", if (pending.spent) "rejected" else "ok") }
  action invalid = all { phase == 1,
    update(pending, durable, phase, height, committedHeight, cache, "invalid", "rejected") }
  action end = all { phase == 1,
    update(pending, durable, 2, height, committedHeight, cache, "end", "ok") }
  action commit = all { phase == 2,
    update(pending, pending, 0, height, height, cache, "commit", "ok") }
  action cancelBefore = all { phase == 2,
    update(durable, durable, 3, committedHeight, committedHeight, cache, "cancel_before", "interrupted") }
  action cancelAfter = all { phase == 2,
    update(durable, pending, 3, committedHeight, height, cache, "cancel_after", "interrupted") }
  action blocked = all { phase == 3,
    update(pending, durable, phase, height, committedHeight, cache, "blocked", "rejected") }
  // Rebuilding from latest_snapshot is also permitted when already Idle.
  action rollback = update(durable, durable, 0, committedHeight, committedHeight, cache, "rollback", "ok")
  action reopen = update(durable, durable, 0, committedHeight, committedHeight, false, "reopen", "ok")
  action step = any { begin, check, deliver, invalid, end, commit,
    cancelBefore, cancelAfter, blocked, rollback, reopen }

  val invariant = all {
    pending.spent == pending.outputs, pending.outputs == pending.indexed,
    durable.spent == durable.outputs, durable.outputs == durable.indexed,
    phase == 0 implies (pending == durable and height == committedHeight),
    result == "rejected" implies pending == prior,
    committedHeight >= 1, committedHeight <= 3 }

  run durableTrace = init.then(begin).then(deliver).then(check).then(deliver).then(end)
    .then(commit).then(reopen).then(begin).then(deliver).then(rollback)
  run cachedTrace = init.then(begin).then(check).then(deliver).then(invalid)
    .then(rollback).then(begin).then(deliver).then(end).then(commit).then(reopen)
  run beforeTrace = init.then(begin).then(deliver).then(end).then(cancelBefore)
    .then(blocked).then(rollback).then(begin).then(deliver).then(end).then(commit).then(reopen)
  run afterTrace = init.then(begin).then(deliver).then(end).then(cancelAfter)
    .then(blocked).then(rollback).then(begin).then(deliver).then(rollback).then(reopen)
  run abandonTrace = init.then(begin).then(deliver).then(reopen).then(begin)
    .then(deliver).then(end).then(commit).then(reopen)
  run readOnlyTrace = init.then(check).then(rollback).then(begin).then(deliver)
    .then(end).then(check).then(commit).then(check).then(reopen).then(check)
  run interruptedCheckTrace = init.then(begin).then(deliver).then(end).then(cancelBefore)
    .then(check).then(rollback).then(begin).then(deliver).then(end).then(cancelAfter)
    .then(check).then(reopen)
}

// PR160 SOURCE candidate, unrun. The execution module above remains historical.
// Opaque roots/IDs and proof-validity flags are assumptions, not hash semantics.
module permanentJointRecovery {
  type Boundary = { height: int, root: int, blockID: int }
  pure val genesis: Boundary = { height: 0, root: 100, blockID: 200 }
  pure val current: Boundary = { height: 1, root: 101, blockID: 201 }
  pure val nextBoundary: Boundary = { height: 2, root: 102, blockID: 202 }
  pure val unknown: Boundary = { height: 2, root: 999, blockID: 999 }
  pure val alphabet: Set[int] = 0.to(15)
  // Nullifier n denotes an opaque key in partition n. No private padding bit.
  pure val batches: Set[List[int]] = Set([], [0], [1], [0, 1], [1, 0],
    [0, 0], [2, 3], [0, 1, 2, 3, 4, 5, 6, 7], [8, 9, 10, 11, 12, 13, 14, 15])
  pure def members(xs: List[int]): Set[int] = xs.foldl(Set(), (a, x) => a.union(Set(x)))
  pure def distinct(xs: List[int]): bool = members(xs).size() == xs.length()
  type State = {
    phase: int, // 0 joint ready,1 disposable,2 prepared,3 sealed,4 interrupted,5 local ready
    accepted: List[int], tx: List[int], txOpen: bool, txCount: int,
    frozen: List[int], frozenValid: bool, oldSpent: Set[int], spent: Set[int], progress: int,
    changedPartitions: Set[int], // next-root partitions; empty scans do not change a root
    app: Boundary, bank: Boundary, bankPrevious: Boundary, previous: Boundary, candidate: Boundary,
    recordCurrent: Boundary, recordPrevious: Boundary,
    exportValid: bool, exportBoundary: Boundary, exportSpent: Set[int],
    intent: int, record: int, // intent0absent/1valid/2invalid; record0absent/1pending/2ready/3invalid
    historyValid: bool, absenceValid: bool, bankAuthenticated: bool,
    cometAuthenticated: bool, restoreAuthenticated: bool,
    locallyReady: bool, published: bool, poisoned: bool,
    publishedBoundary: Boundary, op: str, result: str, count: int
  }
  type BoundaryFrame = { app: Boundary, bank: Boundary, spent: Set[int], intent: int,
    record: int, recordCurrent: Boundary, recordPrevious: Boundary }
  pure def boundaryFrame(st: State): BoundaryFrame = { app: st.app, bank: st.bank,
    spent: st.spent, intent: st.intent, record: st.record,
    recordCurrent: st.recordCurrent, recordPrevious: st.recordPrevious }
  pure val initial: State = { phase: 0, accepted: [], tx: [], txOpen: false,
    txCount: 0, frozen: [], frozenValid: false, oldSpent: Set(), spent: Set(), progress: 0,
    changedPartitions: Set(), app: current, bank: current, bankPrevious: genesis, previous: current,
    recordCurrent: current, recordPrevious: genesis,
    exportValid: false, exportBoundary: current, exportSpent: Set(),
    candidate: nextBoundary, intent: 0, record: 2, historyValid: true,
    absenceValid: true, bankAuthenticated: true, cometAuthenticated: true,
    restoreAuthenticated: true, locallyReady: true, published: true, poisoned: false,
    publishedBoundary: current, op: "init", result: "none", count: 0 }
  var s: State
  var priorAccepted: List[int]
  var priorFrame: BoundaryFrame
  action init = all { s' = initial, priorAccepted' = [], priorFrame' = boundaryFrame(initial) }
  action initPriorSpent = all {
    s' = initial.with("oldSpent", Set(0)).with("spent", Set(0)), priorAccepted' = [],
    priorFrame' = boundaryFrame(initial.with("spent", Set(0))) }
  action initGenesis = all {
    s' = initial.with("app", genesis).with("bank", genesis).with("previous", genesis)
      .with("candidate", current).with("record", 0).with("published", false)
      .with("publishedBoundary", genesis), priorAccepted' = [],
    priorFrame' = boundaryFrame(initial.with("app", genesis).with("bank", genesis).with("record", 0)) }
  action change(t: State, name: str, outcome: str): bool = all {
    s.count < 76, s' = t.with("op", name).with("result", outcome).with("count", s.count + 1),
    priorAccepted' = s.accepted, priorFrame' = boundaryFrame(s) }
  action begin = all { s.phase == 0, s.app.height < 2, s.bankAuthenticated,
    s.app == s.bank, s.locallyReady, not(s.poisoned),
    change(s.with("phase", 1).with("published", false).with("accepted", [])
      .with("tx", []).with("txOpen", false).with("txCount", 0).with("frozen", []).with("frozenValid", false)
      .with("absenceValid", true)
      .with("previous", s.app).with("candidate", if (s.app == genesis) current else nextBoundary)
      .with("oldSpent", s.spent).with("progress", 0).with("changedPartitions", Set()), "begin", "ok") }
  action startTx = all { s.phase == 1, not(s.txOpen), s.txCount < 2,
    change(s.with("txOpen", true).with("tx", []), "start_tx", "ok") }
  // Whole batch checked before staging. Order is execution order, never set order.
  action stage(xs: List[int]): bool = {
    val allowed = distinct(xs) and members(xs).forall(n => alphabet.contains(n)
      and not(s.oldSpent.contains(n)) and not(members(s.accepted).contains(n))
      and not(members(s.tx).contains(n)))
    all { s.phase == 1, s.txOpen, batches.contains(xs), s.tx.length() + xs.length() <= 8,
    change(if (allowed) s.with("tx", s.tx.concat(xs)) else s.with("tx", [])
      .with("txOpen", false).with("txCount", s.txCount + 1), "stage_slots",
      if (allowed) "ok" else "rejected") } }
  action acceptTx = all { s.phase == 1, s.txOpen,
    change(s.with("accepted", s.accepted.concat(s.tx)).with("tx", [])
      .with("txOpen", false).with("txCount", s.txCount + 1), "accept_tx", "ok") }
  // Later action/fee failure drops all of this transaction, retaining prior txs.
  action failTx = all { s.phase == 1, s.txOpen,
    change(s.with("tx", []).with("txOpen", false).with("txCount", s.txCount + 1),
      "fail_tx", "rejected") }
  action checkTx = change(s, "check_tx", "read_only")
  action invalidAbsence = all { s.phase == 1,
    change(s.with("absenceValid", false), "invalid_absence_witness", "untrusted") }
  action refusePrepare = all { s.phase == 1, not(s.txOpen),
    not(s.absenceValid and s.historyValid and not(s.poisoned) and s.intent == 0),
    change(s.with("phase", 4).with("locallyReady", false).with("published", false)
      .with("tx", []).with("txOpen", false), "prepare", "rejected") }
  action prepare = all { s.phase == 1, not(s.txOpen), s.absenceValid,
    s.historyValid, not(s.poisoned), s.intent == 0,
    change(s.with("phase", 2).with("frozen", s.accepted).with("frozenValid", true), "prepare", "ok") }
  action discard = all { s.phase == 2,
    change(s.with("phase", 0).with("accepted", []).with("frozen", []).with("frozenValid", false)
      .with("published", s.app != genesis).with("publishedBoundary", s.app), "discard", "ok") }
  action seal = all { s.phase == 2,
    change(s.with("phase", 3).with("intent", 1), "seal_intent", "ok") }
  action pendingRecord = all { s.phase == 3, s.intent == 1, Set(0, 2).contains(s.record),
    change(s.with("record", 1).with("recordCurrent", s.candidate)
      .with("recordPrevious", s.previous), "pending_record_durable", "ok") }
  action bankCommit = all { s.phase == 3, s.intent == 1, s.record == 1,
    s.bankAuthenticated, s.bank == s.previous,
    s.recordCurrent == s.candidate, s.recordPrevious == s.previous,
    change(s.with("bankPrevious", s.bank).with("bank", s.candidate), "bank_commit", "ok") }
  // One logical ordered partition scan. Production skips empty session commits.
  action scanPartition = {
    val touched = members(s.frozen).contains(s.progress)
    all { s.phase == 3, s.intent == 1, s.record == 1, s.bank == s.candidate, s.progress < 16,
    change(s.with("progress", s.progress + 1).with("locallyReady", false)
      .with("spent", if (touched) s.spent.union(Set(s.progress)) else s.spent)
      .with("changedPartitions", if (touched)
        s.changedPartitions.union(Set(s.progress)) else s.changedPartitions),
      "partition_scan", if (touched) "physical_commit" else "empty_skip") } }
  action appCommit = all { s.phase == 3, s.intent == 1, s.progress == 16,
    s.spent == s.oldSpent.union(members(s.frozen)),
    change(s.with("app", s.candidate), "application_commit", "ok") }
  action complete = all { s.phase == 3, s.app == s.candidate, s.progress == 16,
    change(s.with("intent", 0).with("historyValid", true).with("phase", 5)
      .with("locallyReady", true), "retain_complete_native", "ok") }
  action readyRecord = all { s.phase == 5, s.locallyReady, s.app == s.bank,
    s.bankAuthenticated, s.record == 1,
    s.recordCurrent == s.bank, s.recordPrevious == s.bankPrevious,
    change(s.with("record", 2), "ready_record_durable", "ok") }
  val publicationEligible = s.phase == 5 and s.locallyReady and s.record == 2
    and s.bankAuthenticated and s.app == s.bank and s.historyValid and not(s.poisoned)
    and s.recordCurrent == s.bank and s.recordPrevious == s.bankPrevious
    and s.recordCurrent.height >= 1
    and s.recordCurrent.height == s.recordPrevious.height + 1
  action publish = all { publicationEligible,
    change(s.with("phase", 0).with("published", true)
      .with("publishedBoundary", s.app), "publish_authenticated", "ok") }
  action interrupt = all { s.phase != 0,
    change(s.with("phase", 4).with("published", false).with("locallyReady", false),
      "interrupt", "interrupted") }
  action reopen = change(s.with("phase", 4).with("published", false)
    .with("locallyReady", false), "reopen_local", "interrupted")
  // Local consistency is not joint authority. Invalid/unknown/missing history refuses.
  action recoverLocal = {
    val old = s.app == s.previous
    val new = s.app == s.candidate and s.progress == 16
      and s.spent == s.oldSpent.union(members(s.frozen))
    val allowed = s.historyValid and s.intent != 2 and not(s.poisoned)
      and (old or new) and (s.intent == 1 or s.progress == 0 or new)
    val recovered = if (old) s.with("spent", s.oldSpent).with("progress", 0)
      .with("changedPartitions", Set()) else s
    all { s.phase == 4,
    change(if (allowed) recovered.with("phase", 5).with("intent", 0)
      .with("locallyReady", true).with("tx", []).with("txOpen", false) else s.with("poisoned", true),
      "recover_local", if (allowed) "ok" else "rejected") } }
  val currentRecord = Set(1, 2).contains(s.record) and s.recordCurrent == s.bank
    and s.recordPrevious == s.bankPrevious
  val abandonedRecord = s.record == 1 and s.recordCurrent.height == s.bank.height + 1
    and s.recordPrevious == s.bank
  val alignedAdmission = s.bankAuthenticated and s.app == s.bank
    and (currentRecord or abandonedRecord) and s.historyValid
  val alignedEligible = s.phase == 5 and s.locallyReady and not(s.poisoned)
    and s.app.height >= 1 and alignedAdmission
  action authenticateAligned = all { alignedEligible,
    change(s.with("record", 2).with("recordCurrent", s.bank)
      .with("recordPrevious", s.bankPrevious), "authenticate_aligned", "ok") }
  // Bankd-ahead recovery rolls the authenticated joint state back; never trusts intent alone.
  // Genesis B1/S0 is explicitly excluded; Comet/retained-target checks are abstract premises.
  val rollbackEligibleWithoutGenesisGuard = s.phase == 5 and s.locallyReady and not(s.poisoned)
    and s.app == s.previous and s.bank.height == s.app.height + 1 and s.bank == s.candidate
    and s.bankAuthenticated and s.cometAuthenticated and s.historyValid and s.record == 1
    and s.bankPrevious == s.app and s.recordCurrent == s.bank and s.recordPrevious == s.bankPrevious
  val rollbackEligible = rollbackEligibleWithoutGenesisGuard and s.app.height >= 1
  action rollbackBank = all { rollbackEligible,
    change(s.with("bank", s.app).with("bankPrevious", genesis).with("record", 2)
      .with("recordCurrent", s.app).with("recordPrevious", genesis),
      "authenticated_joint_rollback", "ok") }
  action refuseJoint = all { s.phase == 5,
    not(alignedEligible or rollbackEligible or publicationEligible),
    change(s, "joint_admission", "rejected") }
  // These endpoint assertions are trace-only and never enter step. Eligibility
  // deliberately excludes count76, so exhaustion cannot masquerade as refusal.
  action assertJointRefusal = all { s.result == "rejected", s.phase == 5,
    not(alignedEligible), not(rollbackEligible), not(publicationEligible), not(s.published),
    s.accepted == priorAccepted, boundaryFrame(s) == priorFrame,
    s' = s, priorAccepted' = priorAccepted, priorFrame' = priorFrame }
  action assertPrepareRefusal = all { s.op == "prepare", s.result == "rejected",
    s.phase == 4, not(s.locallyReady), not(s.published), not(s.txOpen),
    s.accepted == priorAccepted, boundaryFrame(s) == priorFrame,
    s' = s, priorAccepted' = priorAccepted, priorFrame' = priorFrame }
  val authenticatedAppBoundary = s.bankAuthenticated and (s.app == s.bank
    or (s.bank.height == s.app.height + 1 and s.app == s.bankPrevious))
  // History.export writes a checkpoint only after completed canonical history.
  // This retained copy is separate from a subsequently damaged live store.
  action retainExport = all { s.locallyReady, s.historyValid, authenticatedAppBoundary,
    Set(0, 5).contains(s.phase), not(s.poisoned),
    change(s.with("exportValid", true).with("exportBoundary", s.app)
      .with("exportSpent", s.spent), "retain_immutable_export", "ok") }
  val restoreContext = s.phase == 4 and s.exportValid and s.exportBoundary == s.app
    and authenticatedAppBoundary and s.restoreAuthenticated
  def restoreEligible(validProofs: bool, canonicalReplay: bool): bool =
    restoreContext and validProofs and canonicalReplay
  // canonicalReplay=false represents input records omitting key0. Verification
  // rejects that input; the mutation below adopts its content without the check.
  pure def replayContent(canonicalReplay: bool, data: Set[int]): Set[int] =
    if (canonicalReplay) data else data.filter(n => n != 0)
  pure def restoredState(st: State, data: Set[int]): State =
    st.with("phase", 5).with("spent", data)
      .with("progress", if (st.app == st.candidate) 16 else 0)
      .with("changedPartitions", if (st.app == st.candidate)
        data.intersect(members(st.frozen)) else Set())
      .with("intent", 0).with("historyValid", true).with("locallyReady", true)
      .with("poisoned", false).with("tx", []).with("txOpen", false)
  // Atomic fresh working-NOMT reconstruction: expected comes from the existing
  // authenticated application. Application state is NEVER installed by restore.
  action restore(validProofs: bool, canonicalReplay: bool): bool = {
    val allowed = restoreEligible(validProofs, canonicalReplay)
    all { s.phase == 4,
    change(if (allowed) restoredState(s, replayContent(canonicalReplay, s.exportSpent))
      else s.with("poisoned", true).with("locallyReady", false).with("published", false),
      "restore_authenticated_replay",
      if (allowed) "ok" else "rejected") } }
  action assertRestoreRefusal = all { s.op == "restore_authenticated_replay",
    s.result == "rejected", s.phase == 4, not(s.locallyReady), not(s.published),
    not(restoreEligible(true, false)),
    s.accepted == priorAccepted, s.app == priorFrame.app, s.bank == priorFrame.bank,
    s' = s, priorAccepted' = priorAccepted, priorFrame' = priorFrame }
  // Finite explicit corrupt observations; they never silently become authenticated.
  action corrupt(kind: int): bool = all { s.phase == 4, Set(0, 1, 2, 3, 4).contains(kind),
    change(if (kind == 0) s.with("intent", 2)
      else if (kind == 1) s.with("app", unknown)
      else if (kind == 2) s.with("historyValid", false)
      else if (kind == 3) s.with("record", 3)
      else s.with("recordCurrent", unknown),
      "corrupt_observation", "untrusted") }
  action chooseStage = { nondet xs = batches.oneOf(); stage(xs) }
  action chooseRestore = { nondet p = Set(false, true).oneOf()
    nondet c = Set(false, true).oneOf(); restore(p, c) }
  action chooseCorrupt = { nondet k = Set(0, 1, 2, 3, 4).oneOf(); corrupt(k) }
  action step = any { begin, startTx, chooseStage, acceptTx, failTx, checkTx,
    invalidAbsence, refusePrepare, prepare, discard, seal, pendingRecord, bankCommit, scanPartition, appCommit,
    complete, readyRecord, publish, interrupt, reopen, recoverLocal, authenticateAligned,
    rollbackBank, refuseJoint, retainExport, chooseRestore, chooseCorrupt }
  // Unready/poisoned fresh targets may hold partial data; no read authority.
  val insertionCompleteness = (s.locallyReady and s.app == s.candidate) implies
    s.spent == s.oldSpent.union(members(s.frozen))
  val jointPublication = s.published implies (s.phase == 0 and s.locallyReady
    and not(s.poisoned) and s.bankAuthenticated and s.app == s.bank
    and s.record == 2 and s.recordCurrent == s.bank and s.recordPrevious == s.bankPrevious
    and s.recordCurrent.height >= 1 and s.publishedBoundary == s.app and s.historyValid)
  val readyRecordWellFormed = s.record == 2 implies (s.recordCurrent.height >= 1
    and s.recordCurrent.height == s.recordPrevious.height + 1)
  val retainedCheckpointContent = (s.locallyReady and s.exportValid
    and s.app == s.exportBoundary) implies s.spent == s.exportSpent
  val orderedFrozen = s.frozenValid implies s.accepted == s.frozen
  val rejectionIsolation = s.result == "rejected" implies s.accepted == priorAccepted
  val transactionRefusal = (s.op == "stage_slots" and s.result == "rejected")
    implies (not(s.txOpen) and s.tx.length() == 0)
  val invariant = all {
    s.count >= 0, s.count <= 76, s.progress >= 0, s.progress <= 16,
    s.txCount >= 0, s.txCount <= 2, s.tx.length() <= 8, s.accepted.length() <= 16,
    distinct(s.accepted), distinct(s.tx), members(s.accepted).forall(n => alphabet.contains(n)),
    members(s.accepted).intersect(s.oldSpent).size() == 0,
    members(s.tx).forall(n => alphabet.contains(n)),
    members(s.tx).intersect(s.oldSpent.union(members(s.accepted))).size() == 0,
    orderedFrozen,
    s.changedPartitions == members(s.frozen).filter(n => n < s.progress),
    insertionCompleteness, jointPublication, rejectionIsolation, transactionRefusal,
    readyRecordWellFormed, retainedCheckpointContent,
    s.op == "check_tx" implies s.accepted == priorAccepted }

  // Intended mutations only; EXCLUDED from step. Future controls must observe
  // the named safety predicate failing, not a parser/dependency/timeout failure.
  action earlyPublishMutation = change(s.with("published", true)
    .with("publishedBoundary", s.candidate), "MUTATION_early_publish", "bad")
  action omitInsertionMutation = all { s.phase == 3, s.frozen.length() > 0,
    change(s.with("app", s.candidate).with("progress", 16), "MUTATION_omit_insertion", "bad") }
  action localIntentAuthorityMutation = all { s.phase == 3, s.intent == 1,
    change(s.with("app", s.candidate).with("published", true).with("phase", 0),
      "MUTATION_local_intent_authority", "bad") }
  action forgedRestoreMutation = all { restoreContext, s.exportSpent.contains(0),
    change(restoredState(s, replayContent(false, s.exportSpent)),
      "MUTATION_forged_restore", "bad") }
  // Supplemental focused D4 control: omit only S>=1 from rollback eligibility.
  action genesisRollbackGuardMutation = all { rollbackEligibleWithoutGenesisGuard,
    change(s.with("bank", s.app).with("bankPrevious", genesis).with("record", 2)
      .with("recordCurrent", s.app).with("recordPrevious", genesis),
      "MUTATION_genesis_rollback_guard", "bad") }

  // Explicit deterministic trace contract. Prefix cuts of allPartitionsTrace
  // cover progress0..16; two eight-slot transactions populate every partition.
  run allPartitionsTrace = init.then(begin).then(startTx)
    .then(stage([0, 1, 2, 3, 4, 5, 6, 7])).then(acceptTx).then(startTx)
    .then(stage([8, 9, 10, 11, 12, 13, 14, 15])).then(acceptTx)
    .then(prepare).then(seal).then(pendingRecord).then(bankCommit)
    .then(scanPartition).then(scanPartition).then(scanPartition).then(scanPartition)
    .then(scanPartition).then(scanPartition).then(scanPartition).then(scanPartition)
    .then(scanPartition).then(scanPartition).then(scanPartition).then(scanPartition)
    .then(scanPartition).then(scanPartition).then(scanPartition).then(scanPartition)
    .then(appCommit).then(complete).then(retainExport).then(readyRecord).then(publish)
    .then(reopen).then(corrupt(2)).then(restore(true, true))
    .then(authenticateAligned).then(publish).then(checkTx)
  run duplicateBatchRefusalTrace = init.then(begin).then(startTx)
    .then(stage([0, 0])).then(prepare).then(discard)
  run earlierActionConflictTrace = init.then(begin).then(startTx)
    .then(stage([0])).then(stage([0])).then(prepare).then(discard)
  run lateFeeFailureTrace = init.then(begin).then(startTx).then(stage([0]))
    .then(failTx).then(startTx).then(stage([1, 0])).then(acceptTx).then(prepare).then(discard)
  run priorCommittedConflictTrace = initPriorSpent.then(begin).then(startTx)
    .then(stage([0])).then(prepare).then(discard)
  run earlierTransactionConflictTrace = init.then(begin).then(startTx).then(stage([0]))
    .then(acceptTx).then(startTx).then(stage([0])).then(prepare).then(discard)
  run emptyPartitionTrace = init.then(begin).then(prepare).then(seal)
    .then(pendingRecord).then(bankCommit)
    .then(scanPartition).then(scanPartition).then(scanPartition).then(scanPartition)
    .then(scanPartition).then(scanPartition).then(scanPartition).then(scanPartition)
    .then(scanPartition).then(scanPartition).then(scanPartition).then(scanPartition)
    .then(scanPartition).then(scanPartition).then(scanPartition).then(scanPartition)
    .then(appCommit).then(complete).then(readyRecord).then(publish)
    .then(reopen).then(recoverLocal).then(authenticateAligned).then(publish)
  run sparsePartialRollbackTrace = init.then(begin).then(startTx).then(stage([0]))
    .then(acceptTx).then(prepare).then(seal).then(pendingRecord).then(bankCommit)
    .then(scanPartition).then(interrupt).then(recoverLocal).then(rollbackBank).then(publish)
  run invalidAbsenceRefusalTrace = init.then(begin).then(invalidAbsence)
    .then(refusePrepare).then(assertPrepareRefusal)
  run disposableTrace = init.then(begin).then(startTx).then(stage([1, 0]))
    .then(acceptTx).then(prepare).then(discard).then(checkTx)
  run bankAheadRollbackTrace = init.then(begin).then(prepare).then(seal)
    .then(pendingRecord).then(bankCommit).then(interrupt).then(recoverLocal)
    .then(rollbackBank).then(publish)
  run abandonedPendingRecordTrace = init.then(begin).then(prepare).then(seal)
    .then(pendingRecord).then(interrupt).then(recoverLocal)
    .then(authenticateAligned).then(publish)
  run abandonedTransactionTrace = init.then(begin).then(startTx).then(stage([0]))
    .then(reopen).then(recoverLocal).then(authenticateAligned).then(publish)
    .then(begin).then(startTx).then(stage([0])).then(acceptTx)
  run genesisRefusalTrace = initGenesis.then(begin).then(prepare).then(seal)
    .then(pendingRecord).then(bankCommit).then(interrupt).then(recoverLocal)
    .then(refuseJoint).then(assertJointRefusal)
  run forgedRestoreRefusalTrace = init.then(begin).then(startTx)
    .then(stage([0, 1, 2, 3, 4, 5, 6, 7])).then(acceptTx).then(startTx)
    .then(stage([8, 9, 10, 11, 12, 13, 14, 15])).then(acceptTx)
    .then(prepare).then(seal).then(pendingRecord).then(bankCommit)
    .then(scanPartition).then(scanPartition).then(scanPartition).then(scanPartition)
    .then(scanPartition).then(scanPartition).then(scanPartition).then(scanPartition)
    .then(scanPartition).then(scanPartition).then(scanPartition).then(scanPartition)
    .then(scanPartition).then(scanPartition).then(scanPartition).then(scanPartition)
    .then(appCommit).then(complete).then(retainExport).then(interrupt).then(corrupt(2))
    .then(restore(true, false)).then(assertRestoreRefusal)
  run corruptHistoryRefusalTrace = init.then(begin).then(prepare).then(seal)
    .then(interrupt).then(corrupt(2)).then(recoverLocal)
  run mismatchedRecordRefusalTrace = init.then(reopen).then(corrupt(4))
    .then(recoverLocal).then(refuseJoint).then(assertJointRefusal)
  run earlyPublishControl = init.then(begin).then(earlyPublishMutation)
  run omitInsertionControl = init.then(begin).then(startTx).then(stage([0]))
    .then(acceptTx).then(prepare).then(seal).then(pendingRecord).then(bankCommit)
    .then(omitInsertionMutation)
  run localIntentControl = init.then(begin).then(prepare).then(seal)
    .then(localIntentAuthorityMutation)
  run forgedRestoreControl = init.then(begin).then(startTx)
    .then(stage([0, 1, 2, 3, 4, 5, 6, 7])).then(acceptTx).then(startTx)
    .then(stage([8, 9, 10, 11, 12, 13, 14, 15])).then(acceptTx)
    .then(prepare).then(seal).then(pendingRecord).then(bankCommit)
    .then(scanPartition).then(scanPartition).then(scanPartition).then(scanPartition)
    .then(scanPartition).then(scanPartition).then(scanPartition).then(scanPartition)
    .then(scanPartition).then(scanPartition).then(scanPartition).then(scanPartition)
    .then(scanPartition).then(scanPartition).then(scanPartition).then(scanPartition)
    .then(appCommit).then(complete).then(retainExport).then(interrupt).then(corrupt(2))
    .then(forgedRestoreMutation)
  run genesisRollbackGuardControl = initGenesis.then(begin).then(prepare).then(seal)
    .then(pendingRecord).then(bankCommit).then(interrupt).then(recoverLocal)
    .then(genesisRollbackGuardMutation)
}
