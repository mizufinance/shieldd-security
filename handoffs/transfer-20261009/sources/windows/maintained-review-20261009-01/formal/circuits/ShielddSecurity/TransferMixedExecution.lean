import ShielddSecurity.TransferMixedBody

set_option maxHeartbeats 250000

namespace ShielddSecurity.TransferMixedExecution

open TransferMixedBody TransferProjection

/-!
Independent mixed-body execution with complete source B and whole state S.
Every validator observes its own input state and may return an updated state;
its native state frame, including any read-side caching, remains explicit.
FeeFunding validation occurs before the body and its retained token is used
after the body. Sibling handlers are separate operations, not Transfer effects.
The source/API refinement of these operations, native savepoints, signatures,
proof knowledge, circuit interpretation and persistence remain open contracts.
-/

structure Api (S B V : Type) where
  putSource : S → Option S
  payFee : S → Option S
  appendAudit : S → Option S
  validate : Slot → B → S → Option (S × V)
  execute : Slot → B → V → S → Option S
  sibling : Nat → Action B → S → Option S
  route : Nat → Action B → S → S → Option S

structure Step (S B V : Type) where
  index : Nat
  action : Action B
  before : S
  checked : S
  executed : S
  after : S
  token : Option V

def runAction {S B V : Type} (api : Api S B V) (index : Nat)
    (action : Action B) (state : S) : Option (Step S B V) :=
  if action.kind = .transfer then
    (api.validate (.bodyAction index) action.source state).bind fun validated =>
      (api.execute (.bodyAction index) action.source validated.2 validated.1).bind fun executed =>
        (api.route index action state executed).map fun after =>
          ⟨index, action, state, validated.1, executed, after, some validated.2⟩
  else
    (api.sibling index action state).bind fun executed =>
      (api.route index action state executed).map fun after =>
        ⟨index, action, state, state, executed, after, none⟩

def StepChecks {S B V : Type} (api : Api S B V) (step : Step S B V) : Prop :=
  (step.action.kind = .transfer ∧ ∃ token,
    step.token = some token ∧
    api.validate (.bodyAction step.index) step.action.source step.before = some (step.checked, token) ∧
    api.execute (.bodyAction step.index) step.action.source token step.checked = some step.executed) ∨
  (step.action.kind ≠ .transfer ∧ step.token = none ∧ step.checked = step.before ∧
    api.sibling step.index step.action step.before = some step.executed)

theorem action_success {S B V : Type} (api : Api S B V) (index : Nat)
    (action : Action B) (state : S) (step : Step S B V)
    (success : runAction api index action state = some step) :
    step.index = index ∧ step.action = action ∧ step.before = state ∧
      StepChecks api step ∧ api.route index action state step.executed = some step.after := by
  by_cases kind : action.kind = .transfer
  · cases validated : api.validate (.bodyAction index) action.source state with
    | none => simp [runAction, kind, validated] at success
    | some pair =>
      cases executed : api.execute (.bodyAction index) action.source pair.2 pair.1 with
      | none => simp [runAction, kind, validated, executed] at success
      | some middle =>
        cases routed : api.route index action state middle with
        | none => simp [runAction, kind, validated, executed, routed] at success
        | some after =>
          have same : (⟨index, action, state, pair.1, middle, after, some pair.2⟩ : Step S B V) = step :=
            Option.some.inj (by simpa [runAction, kind, validated, executed, routed] using success)
          subst step
          exact ⟨rfl, rfl, rfl, Or.inl ⟨kind, pair.2, rfl, validated, executed⟩, routed⟩
  · cases executed : api.sibling index action state with
    | none => simp [runAction, kind, executed] at success
    | some middle =>
      cases routed : api.route index action state middle with
      | none => simp [runAction, kind, executed, routed] at success
      | some after =>
        have same : (⟨index, action, state, state, middle, after, none⟩ : Step S B V) = step :=
          Option.some.inj (by simpa [runAction, kind, executed, routed] using success)
        subst step
        exact ⟨rfl, rfl, rfl, Or.inr ⟨kind, rfl, rfl, executed⟩, routed⟩

def runBody {S B V : Type} (api : Api S B V) (index : Nat) (state : S) :
    List (Action B) → Option (S × List (Step S B V))
  | [] => some (state, [])
  | action :: rest => (runAction api index action state).bind fun step =>
      (runBody api (index + 1) step.after rest).map fun result => (result.1, step :: result.2)

inductive Trace {S B V : Type} (api : Api S B V) :
    Nat → S → List (Action B) → S → List (Step S B V) → Prop where
  | nil (index state) : Trace api index state [] state []
  | cons {index state action rest after step steps}
      (head : runAction api index action state = some step)
      (tail : Trace api (index + 1) step.after rest after steps) :
      Trace api index state (action :: rest) after (step :: steps)

theorem body_success_trace {S B V : Type} (api : Api S B V) (index : Nat)
    (state after : S) (body : List (Action B)) (steps : List (Step S B V))
    (success : runBody api index state body = some (after, steps)) :
    Trace api index state body after steps := by
  induction body generalizing index state steps with
  | nil =>
    have same : (state, []) = (after, steps) := Option.some.inj success
    cases same
    exact Trace.nil _ _
  | cons action rest ih =>
    cases head : runAction api index action state with
    | none => simp [runBody, head] at success
    | some step =>
      cases tail : runBody api (index + 1) step.after rest with
      | none => simp [runBody, head, tail] at success
      | some pair =>
        have same : (pair.1, step :: pair.2) = (after, steps) :=
          Option.some.inj (by simpa [runBody, head, tail] using success)
        cases same
        exact Trace.cons head (ih (index + 1) step.after pair.2 tail)

theorem trace_original_slots {S B V : Type} (api : Api S B V)
    {index state body after steps} (trace : Trace api index state body after steps) :
    steps.map (fun step => (step.index, step.action)) = bodyFrom index body := by
  induction trace with
  | nil => rfl
  | @cons index state action rest after step steps head tail ih =>
    have checks := action_success api index action state step head
    simp only [List.map_cons, bodyFrom, checks.1, checks.2.1, ih]

theorem trace_each_operation {S B V : Type} (api : Api S B V)
    {index state body after steps} (trace : Trace api index state body after steps) :
    ∀ step ∈ steps, StepChecks api step ∧
      api.route step.index step.action step.before step.executed = some step.after := by
  induction trace with
  | nil => simp
  | @cons index state action rest after step steps head tail ih =>
    intro selected inside
    rcases List.mem_cons.mp inside with same | later
    · subst selected
      have checks := action_success api index action state step head
      exact ⟨checks.2.2.2.1, by simpa only [checks.1, checks.2.1, checks.2.2.1] using checks.2.2.2.2⟩
    · exact ih selected later

def validateFunding {S B V : Type} (api : Api S B V) (fee : Option B) (state : S) :
    Option (S × Option (B × V)) :=
  match fee with
  | none => some (state, none)
  | some source => (api.validate .feeFunding source state).map fun result =>
      (result.1, some (source, result.2))

def executeFunding {S B V : Type} (api : Api S B V) (index : Nat)
    (retained : Option (B × V)) (state : S) : Option S :=
  match retained with
  | none => some state
  | some pair => (api.execute .feeFunding pair.1 pair.2 state).bind fun executed =>
      api.route index ⟨.transfer, pair.1⟩ state executed

structure Outcome (S B V : Type) where
  sourceSet : S
  feePaid : S
  audited : S
  preBody : S
  retainedFunding : Option (B × V)
  bodyAfter : S
  steps : List (Step S B V)
  after : S

def run {S B V : Type} (api : Api S B V) (body : List (Action B))
    (fee : Option B) (state : S) : Option (Outcome S B V) :=
  (api.putSource state).bind fun sourceSet =>
    (api.payFee sourceSet).bind fun feePaid =>
      (api.appendAudit feePaid).bind fun audited =>
        (validateFunding api fee audited).bind fun prepared =>
          (runBody api 0 prepared.1 body).bind fun result =>
            (executeFunding api body.length prepared.2 result.1).map fun after =>
              ⟨sourceSet, feePaid, audited, prepared.1, prepared.2, result.1, result.2, after⟩

theorem funding_validation_source {S B V : Type} (api : Api S B V)
    (source : B) (before after : S) (retained : Option (B × V))
    (success : validateFunding api (some source) before = some (after, retained)) :
    ∃ token, retained = some (source, token) ∧
      api.validate .feeFunding source before = some (after, token) := by
  cases result : api.validate .feeFunding source before with
  | none => simp [validateFunding, result] at success
  | some pair =>
    have same : (pair.1, some (source, pair.2)) = (after, retained) :=
      Option.some.inj (by simpa [validateFunding, result] using success)
    have stateSame : pair.1 = after := congrArg Prod.fst same
    have tokenSame : some (source, pair.2) = retained := congrArg Prod.snd same
    exact ⟨pair.2, tokenSame.symm,
      congrArg (fun savedState : S => some (savedState, pair.2)) stateSame⟩

theorem funding_execution_retains_token {S B V : Type} (api : Api S B V)
    (index : Nat) (source : B) (token : V) (before after : S)
    (success : executeFunding api index (some (source, token)) before = some after) :
    ∃ executed, api.execute .feeFunding source token before = some executed ∧
      api.route index ⟨.transfer, source⟩ before executed = some after := by
  cases result : api.execute .feeFunding source token before with
  | none => simp [executeFunding, result] at success
  | some executed => exact ⟨executed, rfl, by simpa [executeFunding, result] using success⟩

def Checks {S B V : Type} (api : Api S B V) (body : List (Action B))
    (fee : Option B) (before : S) (result : Outcome S B V) : Prop :=
  api.putSource before = some result.sourceSet ∧
  api.payFee result.sourceSet = some result.feePaid ∧
  api.appendAudit result.feePaid = some result.audited ∧
  validateFunding api fee result.audited = some (result.preBody, result.retainedFunding) ∧
  Trace api 0 result.preBody body result.bodyAfter result.steps ∧
  executeFunding api body.length result.retainedFunding result.bodyAfter = some result.after

theorem run_success_checks {S B V : Type} (api : Api S B V) (body : List (Action B))
    (fee : Option B) (state : S) (result : Outcome S B V)
    (success : run api body fee state = some result) : Checks api body fee state result := by
  cases sourced : api.putSource state with
  | none => simp [run, sourced] at success
  | some sourceSet =>
    cases paid : api.payFee sourceSet with
    | none => simp [run, sourced, paid] at success
    | some feePaid =>
      cases audited : api.appendAudit feePaid with
      | none => simp [run, sourced, paid, audited] at success
      | some auditState =>
        cases prepared : validateFunding api fee auditState with
        | none => simp [run, sourced, paid, audited, prepared] at success
        | some validation =>
          cases executed : runBody api 0 validation.1 body with
          | none => simp [run, sourced, paid, audited, prepared, executed] at success
          | some bodyResult =>
            cases funded : executeFunding api body.length validation.2 bodyResult.1 with
            | none => simp [run, sourced, paid, audited, prepared, executed, funded] at success
            | some after =>
              have same : (⟨sourceSet, feePaid, auditState, validation.1, validation.2,
                  bodyResult.1, bodyResult.2, after⟩ : Outcome S B V) = result :=
                Option.some.inj (by simpa [run, sourced, paid, audited, prepared, executed, funded] using success)
              subst result
              exact ⟨sourced, paid, audited, prepared,
                body_success_trace api 0 validation.1 bodyResult.1 body bodyResult.2 executed, funded⟩

theorem fee_prevalidation_postbody_execution {S B V : Type} (api : Api S B V)
    (body : List (Action B)) (fee : B) (state : S) (result : Outcome S B V)
    (success : run api body (some fee) state = some result) :
    ∃ token executed,
      api.validate .feeFunding fee result.audited = some (result.preBody, token) ∧
      Trace api 0 result.preBody body result.bodyAfter result.steps ∧
      api.execute .feeFunding fee token result.bodyAfter = some executed ∧
      api.route body.length ⟨.transfer, fee⟩ result.bodyAfter executed = some result.after := by
  have checks := run_success_checks api body (some fee) state result success
  obtain ⟨token, retained, validated⟩ :=
    funding_validation_source api fee result.audited result.preBody result.retainedFunding checks.2.2.2.1
  have funded := checks.2.2.2.2.2
  rw [retained] at funded
  obtain ⟨executed, applied, routed⟩ :=
    funding_execution_retains_token api body.length fee token result.bodyAfter result.after funded
  exact ⟨token, executed, validated, checks.2.2.2.2.1, applied, routed⟩

set_option pp.all true in
#check @action_success
#print axioms action_success
set_option pp.all true in
#check @body_success_trace
#print axioms body_success_trace
set_option pp.all true in
#check @trace_original_slots
#print axioms trace_original_slots
set_option pp.all true in
#check @trace_each_operation
#print axioms trace_each_operation
set_option pp.all true in
#check @funding_validation_source
#print axioms funding_validation_source
set_option pp.all true in
#check @funding_execution_retains_token
#print axioms funding_execution_retains_token
set_option pp.all true in
#check @run_success_checks
#print axioms run_success_checks
set_option pp.all true in
#check @fee_prevalidation_postbody_execution
#print axioms fee_prevalidation_postbody_execution

end ShielddSecurity.TransferMixedExecution
