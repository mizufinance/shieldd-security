"""Exact original binding/inverse rows after native-seeded fixed construction.

Only a strict actual EPK program plan reaches this renderer. Native scalar
success and the global standard generator order discharge inverse legality;
neither an endpoint equality nor row truth is accepted as a new input.
"""
from .generate_hash_round import linear,_signature_audits
from . import transfer_relation as relation


def generate(accepted,scope_id):
    boundary=accepted['boundary'];raw=accepted['boundary_raw'];stage=boundary['inverse_constructor']
    q,p,a=(stage[key] for key in ('quotient','product','auxiliary'))
    x,y=(terms[0][0] for terms in boundary['published']);copy=accepted['checked']['parent']['constant_copy']
    inverse_indices=boundary['inverse_certificate']['rows']
    binding_indices=[i for binding in boundary['bindings'] for i in binding['rows']]
    copy_indices=[i for i,row in raw.items() if row==(((0,1),(copy,relation.MODULUS-1)),())]
    # Canonical raw LC ordering may place the positive constant first; use the
    # actual already checked singleton copy row, not a synthetic replacement.
    if len(copy_indices)!=1:raise relation.RelationError('EPK native boundary exact retained copy row')
    binding_indices=sorted(set(binding_indices+copy_indices))
    def rows(indices):return '['+',\n'.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in indices)+']'
    stem=f'RuntimeTransferEpk{scope_id}';ns=stem+'NativeBoundary'
    N='ShielddSecurity.'+stem+'FixedNativeEndpoint';A='ShielddSecurity.'+stem+'Fixed'
    C=A+'Completion';frame=A+'Frame';last='ShielddSecurity.'+stem+'FixedWindow125'
    chunk='ShielddSecurity.'+stem+'FixedChunk112';rem=linear(stage['remainder'])
    cx,cy=map(linear,boundary['computed'])
    common=f'''{{F J : Type}} [Field F] [CharP F Scalar.modulus] [AddCommGroup J]
    (base : Nat → F) (n : Nat) (positive : 0 < n) (canonical : n < Scalar.order)
    (meaning : base {accepted['scalar']['value']} = (n : F)) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare ({A}.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J)
    (parameter : ({A}.generator : Group.Point F) = model.coordinates generator)
    (exactOrder : addOrderOf generator = Scalar.order) (linked : base {copy} = base 0)'''
    args='base n canonical meaning one four imaginary nonSquare imaginarySquare model generator parameter linked'
    source=f'''import {N}
import {frame}
import ShielddSecurity.CompilerSignedCompletion
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
def modulus : Nat := {relation.MODULUS}
def denominator : Linear := [({x},1)]
def remainder : Linear := {rem}
def ownedWrites : List Nat := [{q},{p},{a}]
def inverseRows : List Row := {rows(inverse_indices)}
def bindingRows : List Row := {rows(binding_indices)}
def expectedBindings : List Row := [⟨Compiler.subtract {cx} [({x},1)],[]⟩,
  ⟨Compiler.subtract {cy} [({y},1)],[]⟩,⟨[],[]⟩]
def extend {{F : Type}} [Field F] (base : Nat → F) :=
  GroupRowCompletion.extendQuotient base [(0,1)] denominator remainder {q} {p} {a}
def construct {{F J : Type}} [Field F] [AddCommGroup J] (base : Nat → F)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J) (n : Nat) :=
  extend ({N}.construct base model generator n)
def totalWrites (n : Nat) : List Nat := {N}.seedWrites ++ {frame}.ownedWrites n ++ ownedWrites
theorem outside_total {{F J : Type}} [Field F] [AddCommGroup J] (base : Nat → F)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J) (n column : Nat)
    (fresh : column ∉ totalWrites n) : construct base model generator n column = base column := by
  have seedFresh : column ∉ {N}.seedWrites := by
    intro member
    exact fresh (List.mem_append_left _ (List.mem_append_left _ member))
  have loopFresh : column ∉ {frame}.ownedWrites n := by
    intro member
    exact fresh (List.mem_append_left _ (List.mem_append_right _ member))
  have inverseFresh : column ∉ ownedWrites := by
    intro member
    exact fresh (List.mem_append_right _ member)
  exact (GroupRowCompletion.extend_preserves ({N}.construct base model generator n) [(0,1)]
    denominator remainder {q} {p} {a} column inverseFresh).trans
      (({frame}.outside_column ({N}.seed base model generator n) n column loopFresh).trans
        ({N}.seed_outside base model generator n column seedFresh))
theorem outside_total_eval {{F J : Type}} [Field F] [AddCommGroup J] (base : Nat → F)
    (model : Group.StandardCurveModel J ({A}.coefficientD : F)) (generator : J) (n : Nat) (terms : Linear)
    (fresh : ∀ term ∈ terms, term.1 ∉ totalWrites n) :
    eval (construct base model generator n) terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact outside_total base model generator n term.1 (fresh term member)
theorem outside {{F : Type}} [Field F] (base : Nat → F) (column : Nat)
    (fresh : column ∉ ownedWrites) : extend base column = base column :=
  GroupRowCompletion.extend_preserves base [(0,1)] denominator remainder {q} {p} {a} column fresh
theorem inverse_coverage : ∀ actual ∈ inverseRows, ∃ expected ∈
    GroupRowCompletion.quotientRows [(0,1)] denominator remainder {q} {p} {a},
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
      Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
      Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  have checked : inverseRows.all (fun actual =>
      (GroupRowCompletion.quotientRows [(0,1)] denominator remainder {q} {p} {a}).any (fun expected =>
        decide ((Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
          Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
          Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b))) = true := by decide
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp (List.all_eq_true.mp checked actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩
theorem inverse_rows_complete {common} :
    Satisfies (construct base model generator n) inverseRows := by
  let prior := {N}.construct base model generator n
  have supplied := {N}.seed_published base model generator n
  have initialScalar := ({N}.seed_outside base model generator n {accepted['scalar']['value']} (by decide)).trans meaning
  have initialOne := ({N}.seed_outside base model generator n 0 (by decide)).trans one
  have initialLink : {N}.seed base model generator n {copy} = {N}.seed base model generator n 0 := by
    rw [{N}.seed_outside base model generator n {copy} (by decide),
      {N}.seed_outside base model generator n 0 (by decide),linked]
  have completed := {C}.actual_rows_complete ({N}.seed base model generator n) n canonical initialScalar
    initialOne four imaginary nonSquare imaginarySquare initialLink
  have value : eval prior denominator = (model.coordinates (n • generator)).x := by
    simpa only [denominator,eval,Int.cast_one,one_mul,add_zero] using
      (completed.2.2 {x} (by decide)).trans supplied.1
  have legal : eval prior denominator ≠ 0 := by
    rw [value]
    exact {N}.native_x_nonzero model generator exactOrder n positive canonical
  have copyLink : prior {copy} = prior 0 := by
    rw [completed.2.2 {copy} (by decide),completed.2.2 0 (by decide),initialLink]
  have localRows := GroupRowCompletion.extend_complete prior [(0,1)] denominator remainder {q} {p} {a}
    (by decide) (by decide) (by decide) (by decide) legal
  have keptCopy : extend prior {copy} = extend prior 0 := by
    rw [outside prior {copy} (by decide),outside prior 0 (by decide),copyLink]
  exact CompilerSignedCompletion.original_rows (extend prior)
    (GroupRowCompletion.quotientRows [(0,1)] denominator remainder {q} {p} {a}) inverseRows
    {copy} keptCopy localRows inverse_coverage
theorem binding_rows_complete {common} :
    Satisfies (construct base model generator n) bindingRows := by
  let prior := {N}.construct base model generator n
  have same := {N}.published_equal {args}
  change (⟨prior {x},prior {y}⟩ : Group.Point F) =
    ⟨eval prior {cx},eval prior {cy}⟩ at same
  have xValue := congrArg Group.Point.x same
  have yValue := congrArg Group.Point.y same
  dsimp only at xValue yValue
  have preservedX := GroupRowCompletion.eval_preserves prior [(0,1)] denominator remainder {cx}
    {q} {p} {a} (by decide)
  have preservedY := GroupRowCompletion.eval_preserves prior [(0,1)] denominator remainder {cy}
    {q} {p} {a} (by decide)
  have suppliedX : eval (extend prior) [({x},1)] = prior {x} := by
    simpa only [eval,Int.cast_one,one_mul,add_zero] using outside prior {x} (by decide)
  have suppliedY : eval (extend prior) [({y},1)] = prior {y} := by
    simpa only [eval,Int.cast_one,one_mul,add_zero] using outside prior {y} (by decide)
  have equations : Satisfies (extend prior) expectedBindings := by
    intro row member
    simp only [expectedBindings,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · change Square (eval (extend prior) (Compiler.subtract {cx} [({x},1)])) 0
      rw [Compiler.eval_subtract,preservedX,suppliedX,← xValue]
      simp [Square]
    · change Square (eval (extend prior) (Compiler.subtract {cy} [({y},1)])) 0
      rw [Compiler.eval_subtract,preservedY,suppliedY,← yValue]
      simp [Square]
    · simp [Square,eval]
  have initialScalar := ({N}.seed_outside base model generator n {accepted['scalar']['value']} (by decide)).trans meaning
  have initialOne := ({N}.seed_outside base model generator n 0 (by decide)).trans one
  have initialLink : {N}.seed base model generator n {copy} = {N}.seed base model generator n 0 := by
    rw [{N}.seed_outside base model generator n {copy} (by decide),
      {N}.seed_outside base model generator n 0 (by decide),linked]
  have completed := {C}.actual_rows_complete ({N}.seed base model generator n) n canonical initialScalar
    initialOne four imaginary nonSquare imaginarySquare initialLink
  have copyLink : extend prior {copy} = extend prior 0 := by
    rw [outside prior {copy} (by decide),outside prior 0 (by decide),completed.2.2 {copy} (by decide),
      completed.2.2 0 (by decide),initialLink]
  apply CompilerSignedCompletion.original_rows (extend prior) expectedBindings bindingRows {copy} copyLink equations
  have checked : bindingRows.all (fun actual => expectedBindings.any (fun expected => decide
      ((Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
        Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
      Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b))) = true := by decide
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp (List.all_eq_true.mp checked actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩
theorem prior_fresh_checked : {A}.blocks.all (fun block => block.all (fun row =>
    (row.a ++ row.b).all (fun term => decide (term.1 ∉ ownedWrites)))) = true := by decide
theorem prior_fresh : ∀ row ∈ {A}.rawRows, ∀ term ∈ row.a ++ row.b, term.1 ∉ ownedWrites := by
  intro row member term present
  obtain ⟨block,inside,member⟩ := List.mem_flatten.mp member
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp prior_fresh_checked block inside) row member) term present)
theorem cone_rows_complete {common} :
    Satisfies (construct base model generator n) ({A}.rawRows ++ inverseRows ++ bindingRows) := by
  let prior := {N}.construct base model generator n
  have previous := {N}.rows_complete base n canonical meaning one four imaginary nonSquare
    imaginarySquare model generator linked
  have retained := GroupRowCompletion.preserves_rows prior [(0,1)] denominator remainder
    {q} {p} {a} {A}.rawRows previous prior_fresh
  have inverse := inverse_rows_complete base n positive canonical meaning one four imaginary nonSquare
    imaginarySquare model generator parameter exactOrder linked
  have bindings := binding_rows_complete base n positive canonical meaning one four imaginary nonSquare
    imaginarySquare model generator parameter exactOrder linked
  intro row member
  rcases List.mem_append.mp member with earlier | final
  · rcases List.mem_append.mp earlier with fixed | fresh
    · exact retained row fixed
    · exact inverse row fresh
  · exact bindings row final
#print axioms outside
#print axioms outside_total
#print axioms outside_total_eval
#print axioms inverse_coverage
#print axioms inverse_rows_complete
#print axioms binding_rows_complete
#print axioms prior_fresh_checked
#print axioms prior_fresh
#print axioms cone_rows_complete
end ShielddSecurity.{ns}
'''
    # Match the computed endpoint through its exact retained definitions before
    # constructor congruence; no unobserved endpoint equality is introduced.
    source=source.replace('  change (⟨prior',f'  dsimp only [{A}.contribution,{chunk}.output,{last}.output] at same\n  change (⟨prior')
    return _signature_audits(source)
