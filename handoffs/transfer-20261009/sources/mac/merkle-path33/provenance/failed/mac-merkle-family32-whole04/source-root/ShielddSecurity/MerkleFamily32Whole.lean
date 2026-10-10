import ShielddSecurity.MerkleFamily32Tables
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleFamily32Whole
open Compiler CompilerCompletion CompilerSegmentCompletion11 Poseidon
open CapturedInitial73419Generic01 (p copy)
namespace T
abbrev data0 := MerkleFamily32Tables.data0
abbrev data1 := MerkleFamily32Tables.data1
abbrev offset := MerkleFamily32Tables.offset
end T
variable {F : Type} [Field F] [CharP F p]
def phase0 (i : Fin 15) : Segment F copy := ReusablePoseidonPhase31.segment (T.data0 i) (MerkleFamily32Tables.certificate0 i)
def phase1 (i : Fin 15) : Segment F copy := ReusablePoseidonPhase31.segment (T.data1 i) (MerkleFamily32Tables.certificate1 i)
def tail (i : Fin 15) : Segment F copy := ReusableWideTail25.segment (T.offset i) (by unfold T.offset MerkleFamily32Tables.offset;omega)
  (by have h := i.isLt;change 25460+424*(i.val+2)≤200692;omega)
def prefixSegment (i : Fin 15) : Segment F copy := append copy (phase0 i) (phase1 i)
  (by change (T.data0 i).high≤(T.data1 i).low;rw [(MerkleFamily32Tables.bounds0 i).2,(MerkleFamily32Tables.bounds1 i).1])
  (by change (T.data0 i).low≤(T.data1 i).low;rw [(MerkleFamily32Tables.bounds0 i).1,(MerkleFamily32Tables.bounds1 i).1];omega)
  (by change (T.data0 i).high≤(T.data1 i).high;rw [(MerkleFamily32Tables.bounds0 i).2,(MerkleFamily32Tables.bounds1 i).2];omega)
  (by change 0<(T.data0 i).low;rw [(MerkleFamily32Tables.bounds0 i).1];omega)
  (by change (T.data0 i).high≤copy ∧ (T.data1 i).high≤copy;rw [(MerkleFamily32Tables.bounds0 i).2,(MerkleFamily32Tables.bounds1 i).2];have h := i.isLt;unfold T.offset MerkleFamily32Tables.offset copy;omega)
def hashSegment (i : Fin 15) : Segment F copy := append copy (prefixSegment i) (tail i)
  (by change (T.data1 i).high≤25088+T.offset i;rw [(MerkleFamily32Tables.bounds1 i).2])
  (by change (T.data0 i).low≤25088+T.offset i;rw [(MerkleFamily32Tables.bounds0 i).1];omega)
  (by change (T.data1 i).high≤25460+T.offset i;rw [(MerkleFamily32Tables.bounds1 i).2];omega)
  (by change 0<(T.data0 i).low;rw [(MerkleFamily32Tables.bounds0 i).1];omega)
  (by change (T.data1 i).high≤copy ∧ 25460+T.offset i≤copy;rw [(MerkleFamily32Tables.bounds1 i).2];have h := i.isLt;unfold T.offset MerkleFamily32Tables.offset copy;omega)
def segment (i : Fin 15) : Segment F copy := append copy (MerkleFamily32Selection.segment i) (hashSegment i)
  (by change MerkleFamily32Selection.high i≤(T.data0 i).low;rw [(MerkleFamily32Tables.bounds0 i).1];unfold MerkleFamily32Selection.high MerkleFamily32Selection.offset T.offset MerkleFamily32Tables.offset;omega)
  (by change MerkleFamily32Selection.low i≤(T.data0 i).low;rw [(MerkleFamily32Tables.bounds0 i).1];unfold MerkleFamily32Selection.low MerkleFamily32Selection.offset T.offset MerkleFamily32Tables.offset;omega)
  (by change MerkleFamily32Selection.high i≤25460+T.offset i;unfold MerkleFamily32Selection.high MerkleFamily32Selection.offset T.offset MerkleFamily32Tables.offset;omega)
  (by change 0<MerkleFamily32Selection.low i;unfold MerkleFamily32Selection.low;omega)
  (by change MerkleFamily32Selection.high i≤copy ∧ 25460+T.offset i≤copy;have h := i.isLt;unfold MerkleFamily32Selection.high MerkleFamily32Selection.offset T.offset MerkleFamily32Tables.offset copy;omega)
def rows (i : Fin 15) := (segment (F:=F) i).rows
def completed (i : Fin 15) (base : Nat → F) := run base (segment (F:=F) i).steps
theorem complete (i : Fin 15) (base : Nat → F) (linked : base copy=base 0) : Satisfies (completed i base) (rows (F:=F) i) :=
  (segment (F:=F) i).complete base linked
theorem outside (i : Fin 15) (base : Nat → F) (column : Nat) (bound : column<25884+424*i.val ∨ 26308+424*i.val≤column) : completed i base column=base column := by
  apply CompilerSegmentCompletion11.outside copy (segment (F:=F) i) base column
  change column<MerkleFamily32Selection.low i ∨ 25460+T.offset i≤column
  unfold MerkleFamily32Selection.low MerkleFamily32Selection.offset T.offset MerkleFamily32Tables.offset
  omega
omit [CharP F p] in
def inputs (i : Fin 15) (rho : Nat → F) : List F :=
  [((i.val+2 : Nat) : F),eval rho (MerkleFamily32Selection.outputs i 0),eval rho (MerkleFamily32Selection.outputs i 1),eval rho (MerkleFamily32Selection.outputs i 2),eval rho (MerkleFamily32Selection.outputs i 3)]
omit [CharP F p] in
theorem absorption (i : Fin 15) (rho : Nat → F) (one : rho 0=1) :
    (fun k => eval rho (MerkleFamily32Tables.expectedBefore i k))=Poseidon.absorb (Poseidon.initial 2 5) (inputs i rho) := by
  funext k
  have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by have h := k.isLt;simp only [Fin.ext_iff];omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · change eval rho [(0,1282)]=(1282:F)
    simp [eval,one]
  · change eval rho [(0,(i.val+2 : Nat))]=((i.val+2 : Nat) : F)
    simp [eval,one]
  · rfl
  · rfl
  · rfl
  · rfl
theorem arbitrary_hash (i : Fin 15) (rho : Nat → F) (one : rho 0=1) (sat : Satisfies rho (rows (F:=F) i)) :
    eval rho (MerkleFamily32Tables.actualResult i)=Poseidon.hash6 (castParameters TransferPoseidonCall04Shared01.parameters) 2 (inputs i rho) := by
  have a : Satisfies rho (T.data0 i).rows := fun row member => sat row (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ member)))
  have b : Satisfies rho (T.data1 i).rows := fun row member => sat row (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ member)))
  have c : Satisfies rho (tail (F:=F) i).rows := fun row member => sat row (List.mem_append_right _ (List.mem_append_right _ member))
  have result := ReusableWideTail25.suffix (T.offset i) (by unfold T.offset MerkleFamily32Tables.offset;omega)
    (by have h := i.isLt;change 25460+424*(i.val+2)≤200692;omega) rho one c
  have first := ReusablePoseidonPhase31.arbitrary_round (T.data0 i) (MerkleFamily32Tables.certificate0 i) rho one a
  have second := ReusablePoseidonPhase31.arbitrary_round (T.data1 i) (MerkleFamily32Tables.certificate1 i) rho one b
  rw [MerkleFamily32Tables.parameters0,MerkleFamily32Tables.index0] at first
  rw [MerkleFamily32Tables.parameters1,MerkleFamily32Tables.index1,MerkleFamily32Tables.phase_seam] at second
  rw [MerkleFamily32Tables.tail_seam,second,first] at result
  change (fun k => eval rho (ReusableWideTail25.after (T.offset i) k))=PoseidonRoundSuffix05.roundsFrom
    (castParameters TransferPoseidonCall04Shared01.parameters) 2 63 (Poseidon.round (castParameters TransferPoseidonCall04Shared01.parameters) 1
      (Poseidon.round (castParameters TransferPoseidonCall04Shared01.parameters) 0 (fun k => eval rho ((T.data0 i).before k)))) at result
  rw [RegistryWhole23.rounds_bridge,MerkleFamily32Tables.before_values,absorption i rho one] at result
  have hash := Poseidon.hash6_of_one_block (castParameters TransferPoseidonCall04Shared01.parameters) 2 (inputs i rho)
    (Poseidon.initial 2 5) (fun k => eval rho (ReusableWideTail25.after (T.offset i) k)) (by rfl) (by rfl) result
  rw [MerkleFamily32Tables.result_values] at hash
  exact hash
theorem bounds (i : Fin 15) : (segment (F:=F) i).low=25884+424*i.val ∧ (segment (F:=F) i).high=26308+424*i.val := by
  change MerkleFamily32Selection.low i=_ ∧ 25460+T.offset i=_
  unfold MerkleFamily32Selection.low MerkleFamily32Selection.offset T.offset MerkleFamily32Tables.offset
  constructor <;> omega
theorem copy_from_rows (i : Fin 15) (rho : Nat → F) (sat : Satisfies rho (rows (F:=F) i)) : rho copy=rho 0 := by
  have a : Satisfies rho (T.data0 i).rows := fun row member => sat row (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ member)))
  have same := checked_assertion_sound (p:=p) rho (T.data0 i).rows [(0,1)] [(copy,1)] a
    (by simpa [subtract,scaleLinear] using (MerkleFamily32Tables.certificate0 i).copyLink)
  simpa [eval] using same.symm
omit [CharP F p] in
theorem bit_port (i : Fin 15) (column : Nat) (lower : 184≤column) (upper : column<186) :
    MerkleFamily32Selection.rename i column=column+2*(i.val+1) := by
  have h := i.isLt
  have a := CompilerWindowRenaming05.above_fixed 136 3 (3*(i.val+1)) column (by omega) (by omega)
  have b := CompilerWindowRenaming05.translated 184 2 (2*(i.val+1)) column lower upper
  have c := CompilerWindowRenaming05.below_fixed 25438 22 (MerkleFamily32Selection.offset i) (column+2*(i.val+1)) (by omega)
  have d := CompilerWindowRenaming05.below_fixed 25460 12 (MerkleFamily32Selection.offset i) (column+2*(i.val+1)) (by omega)
  simp only [MerkleFamily32Selection.rename,a,b,c,d]
omit [CharP F p] in
theorem sibling_port (i : Fin 15) (column : Nat) (lower : 136≤column) (upper : column<139) :
    MerkleFamily32Selection.rename i column=column+3*(i.val+1) := by
  have h := i.isLt
  have a := CompilerWindowRenaming05.translated 136 3 (3*(i.val+1)) column lower upper
  have b := CompilerWindowRenaming05.below_fixed 184 2 (2*(i.val+1)) (column+3*(i.val+1)) (by omega)
  have c := CompilerWindowRenaming05.below_fixed 25438 22 (MerkleFamily32Selection.offset i) (column+3*(i.val+1)) (by omega)
  have d := CompilerWindowRenaming05.below_fixed 25460 12 (MerkleFamily32Selection.offset i) (column+3*(i.val+1)) (by omega)
  simp only [MerkleFamily32Selection.rename,a,b,c,d]
omit [CharP F p] in
def next (i : Fin 15) (rho : Nat → F) (node : F) :=
  let children := MerkleSelection26Semantic.formula
    (rho (184+2*(i.val+1))) (rho (185+2*(i.val+1))) node
    (rho (136+3*(i.val+1))) (rho (137+3*(i.val+1))) (rho (138+3*(i.val+1)))
  Poseidon.hash6 (castParameters TransferPoseidonCall04Shared01.parameters) 2 [((i.val+2 : Nat) : F),children 0,children 1,children 2,children 3]
theorem arbitrary_step (i : Fin 15) (rho : Nat → F) (one : rho 0=1) (sat : Satisfies rho (rows (F:=F) i)) :
    eval rho (MerkleFamily32Tables.actualResult i)=next i rho (eval rho (MerkleFamily32Tables.previousResult i)) := by
  have selected : Satisfies rho (MerkleFamily32Selection.actualRows i) := fun row member => sat row (List.mem_append_left _ member)
  have values := MerkleFamily32Selection.arbitrary i rho (copy_from_rows i rho sat) selected
  rw [bit_port i 184 (by decide) (by decide),bit_port i 185 (by decide) (by decide),
    sibling_port i 136 (by decide) (by decide),sibling_port i 137 (by decide) (by decide),sibling_port i 138 (by decide) (by decide),MerkleFamily32Tables.leaf_values] at values
  have result := arbitrary_hash i rho one sat
  change eval rho (MerkleFamily32Tables.actualResult i)=Poseidon.hash6 _ 2
    [((i.val+2 : Nat) : F),eval rho (MerkleFamily32Selection.outputs i 0),eval rho (MerkleFamily32Selection.outputs i 1),eval rho (MerkleFamily32Selection.outputs i 2),eval rho (MerkleFamily32Selection.outputs i 3)] at result
  rw [congrFun values 0,congrFun values 1,congrFun values 2,congrFun values 3] at result
  exact result
end ShielddSecurity.MerkleFamily32Whole

set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.phase0
#print axioms ShielddSecurity.MerkleFamily32Whole.phase0
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.phase1
#print axioms ShielddSecurity.MerkleFamily32Whole.phase1
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.tail
#print axioms ShielddSecurity.MerkleFamily32Whole.tail
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.prefixSegment
#print axioms ShielddSecurity.MerkleFamily32Whole.prefixSegment
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.hashSegment
#print axioms ShielddSecurity.MerkleFamily32Whole.hashSegment
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.segment
#print axioms ShielddSecurity.MerkleFamily32Whole.segment
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.rows
#print axioms ShielddSecurity.MerkleFamily32Whole.rows
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.completed
#print axioms ShielddSecurity.MerkleFamily32Whole.completed
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.complete
#print axioms ShielddSecurity.MerkleFamily32Whole.complete
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.outside
#print axioms ShielddSecurity.MerkleFamily32Whole.outside
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.inputs
#print axioms ShielddSecurity.MerkleFamily32Whole.inputs
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.absorption
#print axioms ShielddSecurity.MerkleFamily32Whole.absorption
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.arbitrary_hash
#print axioms ShielddSecurity.MerkleFamily32Whole.arbitrary_hash
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.bounds
#print axioms ShielddSecurity.MerkleFamily32Whole.bounds
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.copy_from_rows
#print axioms ShielddSecurity.MerkleFamily32Whole.copy_from_rows
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.bit_port
#print axioms ShielddSecurity.MerkleFamily32Whole.bit_port
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.sibling_port
#print axioms ShielddSecurity.MerkleFamily32Whole.sibling_port
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.next
#print axioms ShielddSecurity.MerkleFamily32Whole.next
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.arbitrary_step
#print axioms ShielddSecurity.MerkleFamily32Whole.arbitrary_step
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.T.data0
#print axioms ShielddSecurity.MerkleFamily32Whole.T.data0
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.T.data1
#print axioms ShielddSecurity.MerkleFamily32Whole.T.data1
set_option pp.all true in
#check @ShielddSecurity.MerkleFamily32Whole.T.offset
#print axioms ShielddSecurity.MerkleFamily32Whole.T.offset
