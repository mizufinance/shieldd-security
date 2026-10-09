import ShielddSecurity.TransferPoseidonFirstTwo02Proof01
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.PoseidonFirstTwoChecked02
open Compiler CompilerIndexed01 CompilerCompletion TransferPoseidonFirstTwo02

def boundaryCheck (candidate : Poseidon.State Linear 6) : Bool :=
  (List.finRange 6).all (fun column => decide
    (candidate column=TransferPoseidonAbsorb02SemanticData01.after column ∧
     candidate column=TransferPoseidonRound01.inputTerms column.val))
def arkCheck (candidate : Poseidon.Parameters Int 6) : Bool :=
  (List.finRange 6).all (fun column => decide
    (candidate.ark 0 column=TransferPoseidonAbsorb02SemanticData01.parameters.ark 0 column ∧
     candidate.ark 1 column=TransferPoseidonRound01SemanticData01.parameters.ark 1 column))
def matrixCheck (candidate : Poseidon.Parameters Int 6) : Bool :=
  (List.finRange 6).all (fun row => (List.finRange 6).all (fun column => decide
    (candidate.mds row column=TransferPoseidonAbsorb02SemanticData01.parameters.mds row column ∧
     candidate.mds row column=TransferPoseidonRound01SemanticData01.parameters.mds row column)))
def check (rows : Array Row) (firstMap secondMap reverseMap : Array Nat)
    (boundary : Poseidon.State Linear 6) (candidate : Poseidon.Parameters Int 6) : Bool :=
  CompilerRawInclusion02.check p TransferPoseidonAbsorb02.originalRows rows firstMap &&
  CompilerRawInclusion02.check p TransferPoseidonRound01.originalRows rows secondMap &&
  checkOriginalCoverage p copy rows emittedRows reverseMap &&
  checkRowAt p rows 40 ⟨[(0,1),(copy,-1)],[]⟩ &&
  boundaryCheck boundary && arkCheck candidate && matrixCheck candidate

theorem checked_fields (rows : Array Row) (firstMap secondMap reverseMap : Array Nat)
    (boundary : Poseidon.State Linear 6) (candidate : Poseidon.Parameters Int 6)
    (accepted : check rows firstMap secondMap reverseMap boundary candidate=true) :
    CompilerRawInclusion02.check p TransferPoseidonAbsorb02.originalRows rows firstMap=true ∧
    CompilerRawInclusion02.check p TransferPoseidonRound01.originalRows rows secondMap=true ∧
    checkOriginalCoverage p copy rows emittedRows reverseMap=true ∧
    checkRowAt p rows 40 ⟨[(0,1),(copy,-1)],[]⟩=true ∧
    boundaryCheck boundary=true ∧ arkCheck candidate=true ∧ matrixCheck candidate=true := by
  simp only [check,Bool.and_eq_true] at accepted
  exact ⟨accepted.1.1.1.1.1.1,accepted.1.1.1.1.1.2,accepted.1.1.1.1.2,
    accepted.1.1.1.2,accepted.1.1.2,accepted.1.2,accepted.2⟩

theorem boundary_sound (boundary : Poseidon.State Linear 6) (accepted : boundaryCheck boundary=true)
    (column : Fin 6) : TransferPoseidonRound01.inputTerms column.val=TransferPoseidonAbsorb02SemanticData01.after column := by
  have both : boundary column=TransferPoseidonAbsorb02SemanticData01.after column ∧
      boundary column=TransferPoseidonRound01.inputTerms column.val :=
    of_decide_eq_true (List.all_eq_true.mp accepted column (List.mem_finRange column))
  exact both.2.symm.trans both.1

theorem ark_sound (candidate : Poseidon.Parameters Int 6) (accepted : arkCheck candidate=true) :
    candidate.ark 0=TransferPoseidonAbsorb02SemanticData01.parameters.ark 0 ∧
    candidate.ark 1=TransferPoseidonRound01SemanticData01.parameters.ark 1 := by
  have both (column : Fin 6) : candidate.ark 0 column=TransferPoseidonAbsorb02SemanticData01.parameters.ark 0 column ∧
      candidate.ark 1 column=TransferPoseidonRound01SemanticData01.parameters.ark 1 column :=
    of_decide_eq_true (List.all_eq_true.mp accepted column (List.mem_finRange column))
  exact ⟨funext (fun column => (both column).1),funext (fun column => (both column).2)⟩

theorem matrix_sound (candidate : Poseidon.Parameters Int 6) (accepted : matrixCheck candidate=true) :
    candidate.mds=TransferPoseidonAbsorb02SemanticData01.parameters.mds ∧
    candidate.mds=TransferPoseidonRound01SemanticData01.parameters.mds := by
  have both (row column : Fin 6) : candidate.mds row column=TransferPoseidonAbsorb02SemanticData01.parameters.mds row column ∧
      candidate.mds row column=TransferPoseidonRound01SemanticData01.parameters.mds row column :=
    of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp accepted row (List.mem_finRange row)) column (List.mem_finRange column))
  exact ⟨funext (fun row => funext (fun column => (both row column).1)),funext (fun row => funext (fun column => (both row column).2))⟩

variable {F : Type} [Field F] [CharP F p]

theorem checked_sound (rows : Array Row) (firstMap secondMap reverseMap : Array Nat)
    (boundary : Poseidon.State Linear 6) (candidate : Poseidon.Parameters Int 6)
    (accepted : check rows firstMap secondMap reverseMap boundary candidate=true)
    (rho : Nat → F) (one : rho 0=1) (four : (4:F)≠0) (satisfied : Satisfies rho rows.toList) :
    (fun column => expressionValue rho (TransferPoseidonRound01.expressions (finalPorts column))) =
      Poseidon.rounds (Poseidon.castParameters candidate) 2
        (Poseidon.absorb (Poseidon.initial 23 4)
          (TransferPoseidonAbsorb02SemanticData01.orderedInputs.map (fun input => eval rho (TransferPoseidonAbsorb02.inputTerms input)))) := by
  obtain ⟨firstRows,secondRows,_,_,boundaryAccepted,arkAccepted,matrixAccepted⟩ :=
    checked_fields rows firstMap secondMap reverseMap boundary candidate accepted
  have firstSat := CompilerRawInclusion02.checked_satisfies _ _ firstMap firstRows rho satisfied
  have secondSat := CompilerRawInclusion02.checked_satisfies _ _ secondMap secondRows rho satisfied
  have firstResult := TransferPoseidonAbsorb02SemanticProof01.arbitrary_round_sound rho one four firstSat
  have secondResult := TransferPoseidonRound01SemanticProof01.arbitrary_round_sound rho one four secondSat
  have ports : (fun column : Fin 6 => eval rho (TransferPoseidonRound01.inputTerms column.val)) =
      (fun column => expressionValue rho (TransferPoseidonAbsorb02.expressions (TransferPoseidonAbsorb02SemanticData01.outputPorts column))) := by
    funext column
    rw [boundary_sound boundary boundaryAccepted,TransferPoseidonAbsorb02SemanticProof01.output_binding]
    rfl
  have ark := ark_sound candidate arkAccepted
  have matrix := matrix_sound candidate matrixAccepted
  have firstJoin := PoseidonRoundComposition.cast_round_agrees (F:=F) TransferPoseidonAbsorb02SemanticData01.parameters candidate 0 _ ark.1.symm matrix.1.symm
  have secondJoin := PoseidonRoundComposition.cast_round_agrees (F:=F) TransferPoseidonRound01SemanticData01.parameters candidate 1 _ ark.2.symm matrix.2.symm
  rw [ports,firstResult,firstJoin] at secondResult
  exact secondResult.trans secondJoin

theorem checked_constructive (rows : Array Row) (firstMap secondMap reverseMap : Array Nat)
    (boundary : Poseidon.State Linear 6) (candidate : Poseidon.Parameters Int 6)
    (accepted : check rows firstMap secondMap reverseMap boundary candidate=true)
    (base : Nat → F) (one : base 0=1) (linked : base copy=base 0) (four : (4:F)≠0) :
    Satisfies (TransferPoseidonFirstTwo02Proof01.completed base) rows.toList ∧
    (∀ column<22738,TransferPoseidonFirstTwo02Proof01.completed base column=base column) ∧
    TransferPoseidonFirstTwo02Proof01.completed base copy=base copy ∧
    (fun column => expressionValue (TransferPoseidonFirstTwo02Proof01.completed base) (TransferPoseidonRound01.expressions (finalPorts column))) =
      Poseidon.rounds (Poseidon.castParameters candidate) 2
        (Poseidon.absorb (Poseidon.initial 23 4)
          (TransferPoseidonAbsorb02SemanticData01.orderedInputs.map (fun input => eval base (TransferPoseidonAbsorb02.inputTerms input)))) := by
  have fields := checked_fields rows firstMap secondMap reverseMap boundary candidate accepted
  have coverage : ∀ actual∈rows.toList,∃ expected∈emitted steps,
      canonical p (unoutline copy actual.a)=canonical p expected.a ∧ canonical p (unoutline copy actual.b)=canonical p expected.b := by
    simpa [emittedRows] using checkOriginalCoverage_sound p copy rows emittedRows reverseMap fields.2.2.1
  have satisfaction := (original_rows_complete base steps [0,copy] rows.toList copy
    TransferPoseidonFirstTwo02Proof01.ordered (TransferPoseidonFirstTwo02Proof01.legal base)
    (by simp) (by simp) linked coverage).1
  have roundResult := checked_sound rows firstMap secondMap reverseMap boundary candidate accepted
    (TransferPoseidonFirstTwo02Proof01.completed base)
    ((TransferPoseidonFirstTwo02Proof01.original_columns_preserved base 0 (by decide)).trans one) four satisfaction
  have inputValues := congrArg (fun f : Nat → F => TransferPoseidonAbsorb02SemanticData01.orderedInputs.map f)
    (TransferPoseidonFirstTwo02Proof01.original_input_values base)
  refine ⟨satisfaction,TransferPoseidonFirstTwo02Proof01.original_columns_preserved base,
    TransferPoseidonFirstTwo02Proof01.copy_preserved base,?_⟩
  exact roundResult.trans (congrArg (fun values => Poseidon.rounds (Poseidon.castParameters candidate) 2 (Poseidon.absorb (Poseidon.initial 23 4) values)) inputValues)
end ShielddSecurity.PoseidonFirstTwoChecked02
set_option pp.all true in
#check @ShielddSecurity.PoseidonFirstTwoChecked02.checked_fields
#print axioms ShielddSecurity.PoseidonFirstTwoChecked02.checked_fields
set_option pp.all true in
#check @ShielddSecurity.PoseidonFirstTwoChecked02.boundary_sound
#print axioms ShielddSecurity.PoseidonFirstTwoChecked02.boundary_sound
set_option pp.all true in
#check @ShielddSecurity.PoseidonFirstTwoChecked02.ark_sound
#print axioms ShielddSecurity.PoseidonFirstTwoChecked02.ark_sound
set_option pp.all true in
#check @ShielddSecurity.PoseidonFirstTwoChecked02.matrix_sound
#print axioms ShielddSecurity.PoseidonFirstTwoChecked02.matrix_sound
set_option pp.all true in
#check @ShielddSecurity.PoseidonFirstTwoChecked02.checked_sound
#print axioms ShielddSecurity.PoseidonFirstTwoChecked02.checked_sound
set_option pp.all true in
#check @ShielddSecurity.PoseidonFirstTwoChecked02.checked_constructive
#print axioms ShielddSecurity.PoseidonFirstTwoChecked02.checked_constructive
