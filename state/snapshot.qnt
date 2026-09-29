// Snapshot admission policy. Root integers denote distinct authenticated roots;
// neither hashing nor proof verification is modeled. Time/epochs never wrap.
module snapshot {
  type Snap = { user: int, asset: int, epoch: int, time: int, height: int }
  type State = { user: int, asset: int, epoch: int, time: int, height: int,
                 grace: int, phase: int, frozen: bool, snapshots: Set[Snap] }
  pure val start: State = { user: 0, asset: 0, epoch: 0, time: 0, height: 1,
    grace: 2, phase: 0, frozen: false,
    snapshots: Set({ user: -1, asset: -1, epoch: 0, time: 0, height: 1 },
                   { user: 0, asset: 0, epoch: 0, time: 0, height: 1 }) }
  var s: State
  var durable: State
  var cached: (int, int)
  var cacheValid: bool
  var op: str
  var x: int
  var y: int
  var result: str
  var count: int

  pure def admit(st: State, u: int, a: int): str = {
    val matches = st.snapshots.filter(p => p.user == u and p.asset == a)
    if (u == st.user and a == st.asset) "ok"
    else if (matches.size() == 0) "unknown"
    else if (matches.exists(p => p.epoch != st.epoch)) "frozen"
    else if (matches.exists(p => p.time > st.time)) "future"
    else if (st.grace == 0 or matches.exists(p => st.time - p.time > st.grace)) "expired"
    else "ok"
  }

  // At most five snapshot observations exist in this finite instance: the real
  // deletion budget of 64 cannot bind. A separate runtime case crosses 64.
  pure def observed(st: State): State = {
    val renewed = st.snapshots.filter(p => p.user != st.user or p.asset != st.asset)
      .union(Set({user: st.user, asset: st.asset, epoch: st.epoch,
                  time: st.time, height: st.height}))
    st.with("snapshots", renewed.filter(p => p.epoch == st.epoch and
      ((p.user == st.user and p.asset == st.asset) or
       (st.grace > 0 and st.time - p.time <= st.grace))))
      .with("phase", 2)
  }

  action init = all { s' = start, durable' = start, cached' = (0, 0),
    cacheValid' = false, op' = "init", x' = 0, y' = 0,
    result' = "none", count' = 0 }

  action change(nextState: State, name: str, arg: int, other: int, outcome: str): bool = all {
    count < 10, s' = nextState, durable' = durable, cached' = cached,
    cacheValid' = cacheValid, op' = name, x' = arg, y' = other,
    result' = outcome, count' = count + 1 }

  action begin(t: int): bool = all {
    s.phase == 0, s.height < 4, t >= 0, t <= 4,
    change(if (t < s.time) s else s.with("phase", 1)
      .with("height", s.height + 1).with("time", t),
      "begin", t, 0, if (t < s.time) "backward" else "ok") }
  action asset = all { s.phase == 1, s.asset < 2,
    change(s.with("asset", s.asset + 1), "asset", 0, 0, "ok") }
  action freeze = all { s.phase == 1, not(s.frozen), s.epoch < 2,
    change(s.with("user", (s.epoch + 1) * 10 + s.height).with("epoch", s.epoch + 1)
      .with("frozen", true), "freeze", 0, 0, "ok") }
  action unfreeze = all { s.phase == 1, s.frozen,
    change(s.with("user", s.epoch * 10).with("frozen", false),
      "unfreeze", 0, 0, "ok") }
  action grace(g: int): bool = all { s.phase == 1, Set(0, 2).contains(g),
    change(s.with("grace", g), "grace", g, 0, "ok") }
  action check(u: int, a: int): bool = all { s.phase == 1,
    change(s, "check", u, a, admit(s, u, a)) }
  // This abstracts a previously verified proof. Actual byte-bound cache reuse is
  // covered by the separate runtime delivery trace with a genuine Pari proof.
  action remember = all { s.phase == 1, count < 10, s' = s, durable' = durable,
    cached' = (s.user, s.asset), cacheValid' = true,
    op' = "remember", x' = s.user, y' = s.asset, result' = "ok", count' = count + 1 }
  action cachedCheck = all { s.phase == 1, cacheValid,
    change(s, "cached", cached._1, cached._2, admit(s, cached._1, cached._2)) }
  action end = all { s.phase == 1, change(observed(s), "end", 0, 0, "ok") }
  action commit = all { s.phase == 2, count < 10,
    s' = s.with("phase", 0), durable' = s.with("phase", 0),
    cached' = cached, cacheValid' = cacheValid,
    op' = "commit", x' = 0, y' = 0, result' = "ok", count' = count + 1 }
  action rollback = all { s.phase != 0,
    change(durable, "rollback", 0, 0, "ok") }
  action restart = all { s.phase == 0, count < 10, s' = durable,
    durable' = durable, cached' = (0, 0), cacheValid' = false,
    op' = "restart", x' = 0, y' = 0, result' = "ok", count' = count + 1 }

  action chooseBegin = { nondet t = 0.to(4).oneOf(); begin(t) }
  action chooseGrace = { nondet g = Set(0, 2).oneOf(); grace(g) }
  action chooseCheck = {
    nondet u = s.snapshots.map(p => p.user).union(Set(s.user)).oneOf()
    nondet a = s.snapshots.map(p => p.asset).union(Set(s.asset)).oneOf()
    check(u, a)
  }
  // Choices belong only to the operation consuming them. Selecting all choices
  // before this disjunction multiplies duplicate successors without adding states.
  action step = any { chooseBegin, asset, freeze, unfreeze, chooseGrace, chooseCheck,
                     remember, cachedCheck, end, commit, rollback, restart }

  val invariant = all {
    s.epoch >= 0,
    s.time >= durable.time,
    s.snapshots.forall(p => p.epoch <= s.epoch and p.time <= s.time),
    s.snapshots.forall(p => s.snapshots.filter(q => q.user == p.user and q.asset == p.asset).size() == 1),
    durable.phase == 0,
    if (op == "check" or op == "cached") result == admit(s, x, y) else true,
    if ((op == "check" or op == "cached") and result == "ok" and
        (x != s.user or y != s.asset))
      s.grace > 0 and s.snapshots.exists(p => p.user == x and p.asset == y and
        p.epoch == s.epoch and s.time - p.time <= s.grace)
      else true,
    if (op == "rollback" or op == "restart") s == durable else true
  }

  // Deterministic traces are exported from Quint, then replayed by Rust.
  run freezeTrace = init.then(begin(0)).then(remember).then(freeze)
    .then(cachedCheck).then(unfreeze).then(cachedCheck).then(rollback).then(restart)
  run graceTrace = init.then(begin(2)).then(asset).then(check(0,0))
    .then(grace(0)).then(check(0,0)).then(rollback).then(begin(3)).then(asset).then(check(0,0))
  run durableTrace = init.then(begin(0)).then(freeze).then(end).then(commit)
    .then(restart).then(begin(0)).then(unfreeze).then(rollback).then(restart)
  run pairsTrace = init.then(begin(0)).then(asset).then(end).then(commit)
    .then(begin(0)).then(freeze).then(check(13,0)).then(check(0,1)).then(check(13,1))
  run timeTrace = init.then(begin(2)).then(end).then(commit).then(begin(1)).then(restart)
  run beforeTrace = init.then(begin(1)).then(asset).then(check(0,0))
    .then(check(0,1)).then(end).then(commit).then(restart)
}
