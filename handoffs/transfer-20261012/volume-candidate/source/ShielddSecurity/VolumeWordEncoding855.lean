import ShielddSecurity.VolumeCandidateSeed848
import ShielddSecurity.HeaderRegisteredConstruction310
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeWordEncoding855
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 WordHints210
attribute [local irreducible] model

theorem encoded (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
    (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers))
    (entry : Slot × Nat) (member : entry∈CapturedWordRoot213.words) :
    (columns entry.1).map (SharedWordWitness221.completed base numbers fallback)=
      (encodeBits entry.1.width (numbers entry.1.value)).map (BooleanHints207.bitValue (F:=F)) := by
  have limits := (CapturedWordRoot213.originals entry member).1
  calc
    _ = (columns entry.1).map (SharedWordWitness221.seeded base numbers fallback) := by
      apply List.map_congr_left
      intro column inside
      obtain ⟨offset,before,equal⟩ := List.mem_range'.mp inside
      simp only [Nat.one_mul] at equal
      exact SharedRegisteredGeneral308.candidate_original _ column (by omega) (by omega)
    _ = ((columns entry.1).map (SharedWordWitness221.bits numbers fallback)).map BooleanHints207.bitValue :=
      SharedWordSeed212.seeded_map base _ SharedWordWitness221.seedColumns entry.1
        (SharedWordWitness221.word_coverage entry member)
    _ = _ := congrArg (List.map BooleanHints207.bitValue)
      (SharedWordWitness221.encoded numbers fallback coherent entry member)

theorem header_limit (original : Nat → F) (c : TransferSem.Crypto) (w : TransferSem.Witness)
    (canonical : TransferSem.CanonicalWitness w) (bound : w.registry.dailyLimit<2^128)
    (initial : Fin 4 → Group.Point F) :
    fieldBinary ((List.range' 7999 128).map (HeaderRegisteredConstruction310.completed original c w initial))=
      (w.registry.dailyLimit:F) := by
  let entry : Slot × Nat := (CapturedWordSlots211B008.W34.slot,CapturedWordSlots211B008.W34.first)
  have member : entry∈CapturedWordRoot213.words := by simp [entry,CapturedWordRoot213.words]
  have number : HeaderRegisteredConstruction310.numbers original c w 21=w.registry.dailyLimit := by
    have frame := HeaderRegisteredConstruction310.number_frame original c w entry member
    have recovered := congrArg (fun leaf : TransferSem.AssetLeaf => leaf.dailyLimit)
      (HeaderRegistrySeed299.recover_registry original c w canonical)
    exact frame.trans recovered
  have normalized : LegalWordNormalization272.normalized (HeaderRegisteredConstruction310.numbers original c w) 21=w.registry.dailyLimit :=
    (LegalWordNormalization272.fixed _ 21 (by decide +kernel)).trans number
  have bits := encoded (CapturedFourSubgroupSeed89.seeded (RegisteredConstructorFrame309.prepared original c w) initial)
    (LegalWordNormalization272.normalized (HeaderRegisteredConstruction310.numbers original c w))
    (HeaderRegisteredConstruction310.fallback original c w)
    (LegalWordNormalization272.coherent _) entry member
  change (List.range' 7999 128).map (HeaderRegisteredConstruction310.completed original c w initial)=
    (encodeBits 128 (LegalWordNormalization272.normalized (HeaderRegisteredConstruction310.numbers original c w) 21)).map BooleanHints207.bitValue at bits
  rw [bits,normalized]
  exact (binary_cast (encodeBits 128 w.registry.dailyLimit)).trans (congrArg (fun n : Nat => (n:F)) (encodeBits_value _ _ bound))

theorem candidate (rho : Nat → F) (w : TransferSem.Witness)
    (bound : VolumeCandidateSeed848.candidate w<2^128)
    (bits : ∀ i : Nat, i<128 → rho (8127+i)=BooleanHints207.bitValue (VolumeCandidateSeed848.flag w i)) :
    fieldBinary ((List.range' 8127 128).map rho)=(VolumeCandidateSeed848.candidate w:F) := by
  have equal : (List.range' 8127 128).map rho=
      (encodeBits 128 (VolumeCandidateSeed848.candidate w)).map BooleanHints207.bitValue := by
    apply List.ext_getElem
    · simp
    · intro i left right
      have before : i<128 := by simpa using left
      simp only [List.getElem_map,List.getElem_range',Nat.one_mul]
      rw [bits i before]
      simp only [VolumeCandidateSeed848.flag,List.getElem?_eq_getElem (show i<(encodeBits 128 (VolumeCandidateSeed848.candidate w)).length by simpa using before),Option.getD_some]
  rw [equal]
  exact (binary_cast (encodeBits 128 (VolumeCandidateSeed848.candidate w))).trans
    (congrArg (fun n : Nat => (n:F)) (encodeBits_value _ _ bound))
end ShielddSecurity.VolumeWordEncoding855

set_option pp.all true in
#check @ShielddSecurity.VolumeWordEncoding855.encoded
#print axioms ShielddSecurity.VolumeWordEncoding855.encoded

set_option pp.all true in
#check @ShielddSecurity.VolumeWordEncoding855.header_limit
#print axioms ShielddSecurity.VolumeWordEncoding855.header_limit

set_option pp.all true in
#check @ShielddSecurity.VolumeWordEncoding855.candidate
#print axioms ShielddSecurity.VolumeWordEncoding855.candidate
