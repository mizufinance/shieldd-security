import ShielddSecurity.CapturedRegistryTail21R1Proof01
import ShielddSecurity.TransferPoseidonTailTemplate05Semantic01
import ShielddSecurity.CompilerWindowRenaming05
-- Handwritten SOURCE22 fallback; all audits UNRUN, no execution allowance.
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.R22
open Compiler CompilerCompletion CompilerSegmentCompletion11 Poseidon
open CapturedInitial73419Generic01 (p copy writeCheck supportCheck makeSegment)
def ren : Nat → Nat := CompilerWindowRenaming05.swap 23076 396 1988


set_option pp.all true in
#check @ShielddSecurity.R22.ren
#print axioms ShielddSecurity.R22.ren
def steps := CompilerColumnRenaming05.steps ren TransferPoseidonTailTemplate05Program01.steps


set_option pp.all true in
#check @ShielddSecurity.R22.steps
#print axioms ShielddSecurity.R22.steps
def rows := CompilerColumnRenaming05.rows ren TransferPoseidonTailTemplate05Program01.originalRows


set_option pp.all true in
#check @ShielddSecurity.R22.rows
#print axioms ShielddSecurity.R22.rows
theorem injective : Function.Injective ren := CompilerWindowRenaming05.injective 23076 396 1988 (by decide)


set_option pp.all true in
#check @ShielddSecurity.R22.injective
#print axioms ShielddSecurity.R22.injective
theorem fixed : ren 0=0 ∧ ren copy=copy := by decide +kernel


set_option pp.all true in
#check @ShielddSecurity.R22.fixed
#print axioms ShielddSecurity.R22.fixed
theorem seam : CapturedRegistryTail21R1Data01.after=(fun i => CompilerColumnRenaming05.linear ren (TransferPoseidonCall04Semantic01.before 2 i)) := by
  funext i
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by have h:=i.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel


set_option pp.all true in
#check @ShielddSecurity.R22.seam
#print axioms ShielddSecurity.R22.seam
theorem write_append (a b : List Step) : writeCheck 25088 25460 (a++b)=(writeCheck 25088 25460 a && writeCheck 25088 25460 b) := by
  simp only [writeCheck,PoseidonCompletion.writes,List.flatMap_append,List.all_append]

set_option pp.all true in
#check @ShielddSecurity.R22.write_append
#print axioms ShielddSecurity.R22.write_append
theorem support_append (a b : List Row) : supportCheck 25460 (a++b)=(supportCheck 25460 a && supportCheck 25460 b) := by
  simp only [supportCheck,List.all_append]

set_option pp.all true in
#check @ShielddSecurity.R22.support_append
#print axioms ShielddSecurity.R22.support_append
theorem block0 : writeCheck 25088 25460 (CompilerColumnRenaming05.steps ren TransferPoseidonCall04R02.materializedSteps)=true ∧ supportCheck 25460 (CompilerColumnRenaming05.rows ren TransferPoseidonCall04R02.arithmeticRows.toList)=true := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.R22.block0
#print axioms ShielddSecurity.R22.block0
theorem block1 : writeCheck 25088 25460 (CompilerColumnRenaming05.steps ren TransferPoseidonCall04R03.materializedSteps)=true ∧ supportCheck 25460 (CompilerColumnRenaming05.rows ren TransferPoseidonCall04R03.arithmeticRows.toList)=true := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.R22.block1
#print axioms ShielddSecurity.R22.block1
theorem block2 : writeCheck 25088 25460 (CompilerColumnRenaming05.steps ren TransferPoseidonCall04R04.materializedSteps)=true ∧ supportCheck 25460 (CompilerColumnRenaming05.rows ren TransferPoseidonCall04R04.arithmeticRows.toList)=true := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.R22.block2
#print axioms ShielddSecurity.R22.block2
theorem block3 : writeCheck 25088 25460 (CompilerColumnRenaming05.steps ren TransferPoseidonCall04R05.materializedSteps)=true ∧ supportCheck 25460 (CompilerColumnRenaming05.rows ren TransferPoseidonCall04R05.arithmeticRows.toList)=true := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.R22.block3
#print axioms ShielddSecurity.R22.block3
theorem block4 : writeCheck 25088 25460 (CompilerColumnRenaming05.steps ren TransferPoseidonCall04R06.materializedSteps)=true ∧ supportCheck 25460 (CompilerColumnRenaming05.rows ren TransferPoseidonCall04R06.arithmeticRows.toList)=true := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.R22.block4
#print axioms ShielddSecurity.R22.block4
theorem block5 : writeCheck 25088 25460 (CompilerColumnRenaming05.steps ren TransferPoseidonCall04R07.materializedSteps)=true ∧ supportCheck 25460 (CompilerColumnRenaming05.rows ren TransferPoseidonCall04R07.arithmeticRows.toList)=true := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.R22.block5
#print axioms ShielddSecurity.R22.block5
theorem block6 : writeCheck 25088 25460 (CompilerColumnRenaming05.steps ren TransferPoseidonCall04Block01.steps)=true ∧ supportCheck 25460 (CompilerColumnRenaming05.rows ren TransferPoseidonCall04Block01.rows)=true := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.R22.block6
#print axioms ShielddSecurity.R22.block6
theorem block7 : writeCheck 25088 25460 (CompilerColumnRenaming05.steps ren TransferPoseidonCall04Block02.steps)=true ∧ supportCheck 25460 (CompilerColumnRenaming05.rows ren TransferPoseidonCall04Block02.rows)=true := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.R22.block7
#print axioms ShielddSecurity.R22.block7
theorem block8 : writeCheck 25088 25460 (CompilerColumnRenaming05.steps ren TransferPoseidonCall04Block03.steps)=true ∧ supportCheck 25460 (CompilerColumnRenaming05.rows ren TransferPoseidonCall04Block03.rows)=true := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.R22.block8
#print axioms ShielddSecurity.R22.block8
theorem block9 : writeCheck 25088 25460 (CompilerColumnRenaming05.steps ren TransferPoseidonCall04Block04.steps)=true ∧ supportCheck 25460 (CompilerColumnRenaming05.rows ren TransferPoseidonCall04Block04.rows)=true := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.R22.block9
#print axioms ShielddSecurity.R22.block9
theorem block10 : writeCheck 25088 25460 (CompilerColumnRenaming05.steps ren TransferPoseidonCall04Block05.steps)=true ∧ supportCheck 25460 (CompilerColumnRenaming05.rows ren TransferPoseidonCall04Block05.rows)=true := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.R22.block10
#print axioms ShielddSecurity.R22.block10
theorem block11 : writeCheck 25088 25460 (CompilerColumnRenaming05.steps ren TransferPoseidonCall04Block06.steps)=true ∧ supportCheck 25460 (CompilerColumnRenaming05.rows ren TransferPoseidonCall04Block06.rows)=true := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.R22.block11
#print axioms ShielddSecurity.R22.block11
theorem block12 : writeCheck 25088 25460 (CompilerColumnRenaming05.steps ren TransferPoseidonCall04Block07.steps)=true ∧ supportCheck 25460 (CompilerColumnRenaming05.rows ren TransferPoseidonCall04Block07.rows)=true := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.R22.block12
#print axioms ShielddSecurity.R22.block12
theorem block13 : writeCheck 25088 25460 (CompilerColumnRenaming05.steps ren TransferPoseidonCall04Block08.steps)=true ∧ supportCheck 25460 (CompilerColumnRenaming05.rows ren TransferPoseidonCall04Block08.rows)=true := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.R22.block13
#print axioms ShielddSecurity.R22.block13
theorem copy_bounds : writeCheck 25088 25460 (CompilerColumnRenaming05.steps ren [TransferPoseidonCall04Shared01.copyStep])=true ∧ supportCheck 25460 (CompilerColumnRenaming05.rows ren [TransferPoseidonCall04Shared01.rawCopy])=true := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.R22.copy_bounds
#print axioms ShielddSecurity.R22.copy_bounds
theorem bounds : writeCheck 25088 25460 steps=true ∧ supportCheck 25460 rows=true := by
  have b0 := block0
  simp only [CompilerColumnRenaming05.steps,CompilerColumnRenaming05.rows] at b0
  have b1 := block1
  simp only [CompilerColumnRenaming05.steps,CompilerColumnRenaming05.rows] at b1
  have b2 := block2
  simp only [CompilerColumnRenaming05.steps,CompilerColumnRenaming05.rows] at b2
  have b3 := block3
  simp only [CompilerColumnRenaming05.steps,CompilerColumnRenaming05.rows] at b3
  have b4 := block4
  simp only [CompilerColumnRenaming05.steps,CompilerColumnRenaming05.rows] at b4
  have b5 := block5
  simp only [CompilerColumnRenaming05.steps,CompilerColumnRenaming05.rows] at b5
  have b6 := block6
  simp only [CompilerColumnRenaming05.steps,CompilerColumnRenaming05.rows] at b6
  have b7 := block7
  simp only [CompilerColumnRenaming05.steps,CompilerColumnRenaming05.rows] at b7
  have b8 := block8
  simp only [CompilerColumnRenaming05.steps,CompilerColumnRenaming05.rows] at b8
  have b9 := block9
  simp only [CompilerColumnRenaming05.steps,CompilerColumnRenaming05.rows] at b9
  have b10 := block10
  simp only [CompilerColumnRenaming05.steps,CompilerColumnRenaming05.rows] at b10
  have b11 := block11
  simp only [CompilerColumnRenaming05.steps,CompilerColumnRenaming05.rows] at b11
  have b12 := block12
  simp only [CompilerColumnRenaming05.steps,CompilerColumnRenaming05.rows] at b12
  have b13 := block13
  simp only [CompilerColumnRenaming05.steps,CompilerColumnRenaming05.rows] at b13
  have bc := copy_bounds
  simp only [CompilerColumnRenaming05.steps,CompilerColumnRenaming05.rows] at bc
  constructor
  · simp only [steps,TransferPoseidonTailTemplate05Program01.steps,TransferPoseidonTailTemplate05Program01.materializedSteps,TransferPoseidonTailTemplate05Program01.prefixSteps0,TransferPoseidonTailTemplate05Program01.prefixSteps1,TransferPoseidonTailTemplate05Program01.prefixSteps2,TransferPoseidonTailTemplate05Program01.prefixSteps3,TransferPoseidonTailTemplate05Program01.prefixSteps4,TransferPoseidonTailTemplate05Program01.prefixSteps5,TransferPoseidonTailTemplate05Program01.prefixSteps6,TransferPoseidonTailTemplate05Program01.prefixSteps7,TransferPoseidonTailTemplate05Program01.prefixSteps8,TransferPoseidonTailTemplate05Program01.prefixSteps9,TransferPoseidonTailTemplate05Program01.prefixSteps10,TransferPoseidonTailTemplate05Program01.prefixSteps11,TransferPoseidonTailTemplate05Program01.prefixSteps12,TransferPoseidonTailTemplate05Program01.prefixSteps13,CompilerColumnRenaming05.steps,List.map_append,write_append]
    simp only [b0.1,b1.1,b2.1,b3.1,b4.1,b5.1,b6.1,b7.1,b8.1,b9.1,b10.1,b11.1,b12.1,b13.1,bc.1,Bool.and_self]
  · simp only [rows,TransferPoseidonTailTemplate05Program01.originalRows,TransferPoseidonTailTemplate05Program01.arithmeticRows,TransferPoseidonTailTemplate05Program01.prefixRows0,TransferPoseidonTailTemplate05Program01.prefixRows1,TransferPoseidonTailTemplate05Program01.prefixRows2,TransferPoseidonTailTemplate05Program01.prefixRows3,TransferPoseidonTailTemplate05Program01.prefixRows4,TransferPoseidonTailTemplate05Program01.prefixRows5,TransferPoseidonTailTemplate05Program01.prefixRows6,TransferPoseidonTailTemplate05Program01.prefixRows7,TransferPoseidonTailTemplate05Program01.prefixRows8,TransferPoseidonTailTemplate05Program01.prefixRows9,TransferPoseidonTailTemplate05Program01.prefixRows10,TransferPoseidonTailTemplate05Program01.prefixRows11,TransferPoseidonTailTemplate05Program01.prefixRows12,TransferPoseidonTailTemplate05Program01.prefixRows13,CompilerColumnRenaming05.rows,List.map_append,support_append]
    simp only [b0.2,b1.2,b2.2,b3.2,b4.2,b5.2,b6.2,b7.2,b8.2,b9.2,b10.2,b11.2,b12.2,b13.2,bc.2,Bool.and_self]


set_option pp.all true in
#check @ShielddSecurity.R22.bounds
#print axioms ShielddSecurity.R22.bounds
theorem counts : steps.length=280 ∧ rows.length=373 ∧ TransferPoseidonTailTemplate05Program01.materializedSteps.length=279 ∧ TransferPoseidonTailTemplate05Program01.arithmeticRows.length=372 := by
  have stepCount : steps.length=280 := by
    simpa only [steps,CompilerColumnRenaming05.steps,List.length_map] using TransferPoseidonTailTemplate05Program01.step_count
  have rowCount : rows.length=373 := by
    simpa only [rows,CompilerColumnRenaming05.rows,List.length_map] using TransferPoseidonTailTemplate05Program01.row_count
  have arithmeticCount : TransferPoseidonTailTemplate05Program01.arithmeticRows.length=372 := by
    have h:=TransferPoseidonTailTemplate05Program01.row_count
    simp only [TransferPoseidonTailTemplate05Program01.originalRows,List.length_append,List.length_singleton] at h
    omega
  exact ⟨stepCount,rowCount,TransferPoseidonTailTemplate05Program01.materialized_count,arithmeticCount⟩


set_option pp.all true in
#check @ShielddSecurity.R22.counts
#print axioms ShielddSecurity.R22.counts
variable {F : Type} [Field F] [CharP F p]
theorem complete (base : Nat → F) (linked : base copy=base 0) : Satisfies (run base steps) rows := by
  apply CompilerColumnRenaming05.completed_rows ren injective
  exact TransferPoseidonTailTemplate05Program01.completed_rows (fun i => base (ren i))
    (by simpa only [fixed.1,fixed.2] using linked)


set_option pp.all true in
#check @ShielddSecurity.R22.complete
#print axioms ShielddSecurity.R22.complete
def segment : Segment F copy := makeSegment steps rows 25088 25460 bounds.1 bounds.2 complete


set_option pp.all true in
#check @ShielddSecurity.R22.segment
#print axioms ShielddSecurity.R22.segment
theorem outside (base : Nat → F) (column : Nat) (h : column<25088 ∨ 25460≤column) : run base steps column=base column :=
  CompilerSegmentCompletion11.outside copy segment base column h


set_option pp.all true in
#check @ShielddSecurity.R22.outside
#print axioms ShielddSecurity.R22.outside
theorem columns (base : Nat → F) : run base steps 0=base 0 ∧ run base steps 1=base 1 ∧ run base steps 2=base 2 ∧ run base steps copy=base copy ∧
    ∀ input : Nat,input<22735 → run base steps (3+input)=base (3+input) := by
  refine ⟨outside base 0 (Or.inl (by decide)),outside base 1 (Or.inl (by decide)),outside base 2 (Or.inl (by decide)),outside base copy (Or.inr (by decide)),?_⟩
  intro input h
  exact outside base _ (Or.inl (by omega))


set_option pp.all true in
#check @ShielddSecurity.R22.columns
#print axioms ShielddSecurity.R22.columns
theorem suffix (rho : Nat → F) (one : rho 0=1) (sat : Satisfies rho rows) :
    (fun i => eval rho (CompilerColumnRenaming05.linear ren (TransferPoseidonCall04Semantic01.after 64 i)))=
    PoseidonRoundSuffix05.roundsFrom (castParameters CapturedRegistryTail21R1Data01.parameters) 2 63
      (fun i => eval rho (CapturedRegistryTail21R1Data01.after i)) := by
  have old := (CompilerColumnRenaming05.satisfies_rows ren rho TransferPoseidonTailTemplate05Program01.originalRows).mp sat
  have result := TransferPoseidonTailTemplate05Semantic01.arbitrary_suffix (fun c => rho (ren c))
    (by simpa only [fixed.1] using one) CapturedRegistryTail21R1Proof01.four_ne_zero old
  rw [seam]
  simpa only [CompilerColumnRenaming05.eval_linear] using result


set_option pp.all true in
#check @ShielddSecurity.R22.suffix
#print axioms ShielddSecurity.R22.suffix
end ShielddSecurity.R22
