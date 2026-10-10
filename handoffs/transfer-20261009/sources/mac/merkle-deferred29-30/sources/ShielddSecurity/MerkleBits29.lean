import ShielddSecurity.MerkleInputMeaning28
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleBits29
open Compiler CompilerIndexed01
open CapturedInitial73419Generic01 (p copy)
def columns : List Nat := List.range' 184 32
def actualRows : List Row := [⟨[(184,1)],[(184,1)]⟩,⟨[(185,1)],[(185,1)]⟩,⟨[(186,1)],[(186,1)]⟩,⟨[(187,1)],[(187,1)]⟩,⟨[(188,1)],[(188,1)]⟩,⟨[(189,1)],[(189,1)]⟩,⟨[(190,1)],[(190,1)]⟩,⟨[(191,1)],[(191,1)]⟩,⟨[(192,1)],[(192,1)]⟩,⟨[(193,1)],[(193,1)]⟩,⟨[(194,1)],[(194,1)]⟩,⟨[(195,1)],[(195,1)]⟩,⟨[(196,1)],[(196,1)]⟩,⟨[(197,1)],[(197,1)]⟩,⟨[(198,1)],[(198,1)]⟩,⟨[(199,1)],[(199,1)]⟩,⟨[(200,1)],[(200,1)]⟩,⟨[(201,1)],[(201,1)]⟩,⟨[(202,1)],[(202,1)]⟩,⟨[(203,1)],[(203,1)]⟩,⟨[(204,1)],[(204,1)]⟩,⟨[(205,1)],[(205,1)]⟩,⟨[(206,1)],[(206,1)]⟩,⟨[(207,1)],[(207,1)]⟩,⟨[(208,1)],[(208,1)]⟩,⟨[(209,1)],[(209,1)]⟩,⟨[(210,1)],[(210,1)]⟩,⟨[(211,1)],[(211,1)]⟩,⟨[(212,1)],[(212,1)]⟩,⟨[(213,1)],[(213,1)]⟩,⟨[(214,1)],[(214,1)]⟩,⟨[(215,1)],[(215,1)]⟩,⟨[(135,52435875175126190479447740508185965837690552500527637822603658699938581184512),(184,1),(185,2),(186,4),(187,8),(188,16),(189,32),(190,64),(191,128),(192,256),(193,512),(194,1024),(195,2048),(196,4096),(197,8192),(198,16384),(199,32768),(200,65536),(201,131072),(202,262144),(203,524288),(204,1048576),(205,2097152),(206,4194304),(207,8388608),(208,16777216),(209,33554432),(210,67108864),(211,134217728),(212,268435456),(213,536870912),(214,1073741824),(215,2147483648)],[]⟩,⟨[(135,52435875175126190479447740508185965837690552500527637822603658699938581184512),(184,1),(185,2),(186,4),(187,8),(188,16),(189,32),(190,64),(191,128),(192,256),(193,512),(194,1024),(195,2048),(196,4096),(197,8192),(198,16384),(199,32768),(200,65536),(201,131072),(202,262144),(203,524288),(204,1048576),(205,2097152),(206,4194304),(207,8388608),(208,16777216),(209,33554432),(210,67108864),(211,134217728),(212,268435456),(213,536870912),(214,1073741824),(215,2147483648)],[]⟩]
def referenceRows := columns.map booleanRow++[reconstructionRow 135 columns,reconstructionRow 135 columns]
def captureIndices := List.range' 178083 34
def mapping : Array Nat := (List.range 34).toArray
theorem actual_to_reference_checked : checkOriginalCoverage p 0 actualRows.toArray referenceRows.toArray mapping=true := by decide +kernel
theorem reference_to_actual_checked : checkOriginalCoverage p 0 referenceRows.toArray actualRows.toArray mapping=true := by decide +kernel
theorem counts : actualRows.length=34 ∧ referenceRows.length=34 ∧ captureIndices.length=34 ∧ columns.length=32 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem transfer (rho : Nat → F) (localRows fullRows : List Row)
    (checked : checkOriginalCoverage p 0 localRows.toArray fullRows.toArray (List.range localRows.length).toArray=true)
    (sat : Satisfies rho fullRows) : Satisfies rho localRows := by
  intro row member
  obtain ⟨expected,included,left,right⟩ := checked_inclusion p localRows.toArray fullRows.toArray _ checked row (by simpa using member)
  have square := sat expected (by simpa using included)
  change Square (eval rho row.a) (eval rho row.b)
  rw [canonical_equal rho row.a expected.a left,canonical_equal rho row.b expected.b right]
  exact square
theorem reference_satisfied (rho : Nat → F) (sat : Satisfies rho actualRows) : Satisfies rho referenceRows := transfer rho referenceRows actualRows reference_to_actual_checked sat
theorem bits_sound (rho : Nat → F) (sat : Satisfies rho actualRows) (index : Fin 32) : rho (184+index.val)=0 ∨ rho (184+index.val)=1 := by
  have inColumns : 184+index.val∈columns := List.mem_range'.mpr ⟨index.val,index.isLt,by simp⟩
  have present : booleanRow (184+index.val)∈referenceRows := List.mem_append_left _ (List.mem_map.mpr ⟨184+index.val,inColumns,rfl⟩)
  apply boolean_sound
  simpa [booleanRow,eval] using reference_satisfied rho sat _ present
theorem position_bound (rho : Nat → F) (sat : Satisfies rho actualRows) : ∃ n : Nat,n<2^32 ∧ (n:F)=rho 135 := by
  have checked : columns.all (fun i => decide (booleanRow i∈referenceRows))=true := by decide +kernel
  have reconstruction : reconstructionRow 135 columns∈referenceRows := List.mem_append_right _ (by simp)
  simpa [columns] using rows_range_sound referenceRows 135 columns checked reconstruction rho (reference_satisfied rho sat)
def seed (base : Nat → F) (n : Nat) := writeBits base 184 (encodeBits 32 n)
omit [CharP F p] in
theorem seed_outside (base : Nat → F) (n column : Nat) (outside : column<184 ∨ 216≤column) : seed base n column=base column :=
  writeBits_preserves base 184 (encodeBits 32 n) column (by simpa using outside)
theorem seed_complete (base : Nat → F) (n : Nat) (bound : n<2^32) (meaning : base 135=(n:F)) : Satisfies (seed base n) actualRows := by
  have block := writeBits_range_complete base 135 184 32 n bound meaning (Or.inl (by decide))
  have references : Satisfies (seed base n) referenceRows := by
    intro row member
    rcases List.mem_append.mp member with member|member
    · exact block row (List.mem_append_left _ member)
    · have same : row=reconstructionRow 135 columns := by simpa using member
      subst row
      exact block _ (List.mem_append_right _ (by simp [columns]))
  exact transfer (seed base n) actualRows referenceRows actual_to_reference_checked references
theorem support_checked : actualRows.all (fun row => (row.a++row.b).all (fun term => decide (term.1<22738)))=true := by decide +kernel
theorem final_preserves_assertions (base : Nat → F) (sat : Satisfies base actualRows) : Satisfies (MerkleHash27Whole.final base) actualRows := by
  intro row member
  have agrees (term : Nat×Int) (present : term∈row.a++row.b) : MerkleHash27Whole.final base term.1=base term.1 := by
    have bound := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp support_checked row member) term present)
    exact MerkleHash27Whole.final_outside base term.1 (Or.inl bound)
  have left : eval (MerkleHash27Whole.final base) row.a=eval base row.a := eval_agrees _ _ _ (fun term present => agrees term (List.mem_append_left _ present))
  have right : eval (MerkleHash27Whole.final base) row.b=eval base row.b := eval_agrees _ _ _ (fun term present => agrees term (List.mem_append_right _ present))
  change Square (eval (MerkleHash27Whole.final base) row.a) (eval (MerkleHash27Whole.final base) row.b)
  rw [left,right]
  exact sat row member
theorem total (base : Nat → F) (n : Nat) (bound : n<2^32) (meaning : base 135=(n:F))
    (one : base 0=1) (linked : base copy=base 0) :
    Satisfies (MerkleHash27Whole.final (seed base n)) MerkleHash27Whole.priorRows ∧
    Satisfies (MerkleHash27Whole.final (seed base n)) MerkleHash27Whole.selectedRows ∧
    Satisfies (MerkleHash27Whole.final (seed base n)) actualRows ∧
    eval (MerkleHash27Whole.final (seed base n)) MerkleHash27Whole.actualResult=MerkleInputMeaning28.pathMeaning (seed base n) := by
  have seedOne : seed base n 0=1 := (seed_outside base n 0 (Or.inl (by decide))).trans one
  have seedLink : seed base n copy=seed base n 0 := by rw [seed_outside base n copy (Or.inr (by decide)),seed_outside base n 0 (Or.inl (by decide))];exact linked
  have done := MerkleInputMeaning28.total (seed base n) seedOne seedLink
  exact ⟨done.1,done.2.1,final_preserves_assertions _ (seed_complete base n bound meaning),done.2.2⟩
end ShielddSecurity.MerkleBits29

set_option pp.all true in
#check @ShielddSecurity.MerkleBits29.columns
#print axioms ShielddSecurity.MerkleBits29.columns
set_option pp.all true in
#check @ShielddSecurity.MerkleBits29.actualRows
#print axioms ShielddSecurity.MerkleBits29.actualRows
set_option pp.all true in
#check @ShielddSecurity.MerkleBits29.referenceRows
#print axioms ShielddSecurity.MerkleBits29.referenceRows
set_option pp.all true in
#check @ShielddSecurity.MerkleBits29.captureIndices
#print axioms ShielddSecurity.MerkleBits29.captureIndices
set_option pp.all true in
#check @ShielddSecurity.MerkleBits29.mapping
#print axioms ShielddSecurity.MerkleBits29.mapping
set_option pp.all true in
#check @ShielddSecurity.MerkleBits29.actual_to_reference_checked
#print axioms ShielddSecurity.MerkleBits29.actual_to_reference_checked
set_option pp.all true in
#check @ShielddSecurity.MerkleBits29.reference_to_actual_checked
#print axioms ShielddSecurity.MerkleBits29.reference_to_actual_checked
set_option pp.all true in
#check @ShielddSecurity.MerkleBits29.counts
#print axioms ShielddSecurity.MerkleBits29.counts
set_option pp.all true in
#check @ShielddSecurity.MerkleBits29.transfer
#print axioms ShielddSecurity.MerkleBits29.transfer
set_option pp.all true in
#check @ShielddSecurity.MerkleBits29.reference_satisfied
#print axioms ShielddSecurity.MerkleBits29.reference_satisfied
set_option pp.all true in
#check @ShielddSecurity.MerkleBits29.bits_sound
#print axioms ShielddSecurity.MerkleBits29.bits_sound
set_option pp.all true in
#check @ShielddSecurity.MerkleBits29.position_bound
#print axioms ShielddSecurity.MerkleBits29.position_bound
set_option pp.all true in
#check @ShielddSecurity.MerkleBits29.seed
#print axioms ShielddSecurity.MerkleBits29.seed
set_option pp.all true in
#check @ShielddSecurity.MerkleBits29.seed_outside
#print axioms ShielddSecurity.MerkleBits29.seed_outside
set_option pp.all true in
#check @ShielddSecurity.MerkleBits29.seed_complete
#print axioms ShielddSecurity.MerkleBits29.seed_complete
set_option pp.all true in
#check @ShielddSecurity.MerkleBits29.support_checked
#print axioms ShielddSecurity.MerkleBits29.support_checked
set_option pp.all true in
#check @ShielddSecurity.MerkleBits29.final_preserves_assertions
#print axioms ShielddSecurity.MerkleBits29.final_preserves_assertions
set_option pp.all true in
#check @ShielddSecurity.MerkleBits29.total
#print axioms ShielddSecurity.MerkleBits29.total
