import ShielddSecurity.NativeTransferAdmission

set_option maxHeartbeats 150000
set_option maxRecDepth 2048

namespace ShielddSecurity.TransferSignedMagnitude

abbrev Inputs := Fin 4 → NativeTransferAdmission.Amount

def inputTotal (amounts : Inputs) : Nat := (amounts 0).val + (amounts 1).val
def outputTotal (amounts : Inputs) : Nat := (amounts 2).val + (amounts 3).val
def negative (amounts : Inputs) : Bool := decide (inputTotal amounts < outputTotal amounts)
def magnitude (amounts : Inputs) : Nat :=
  if inputTotal amounts < outputTotal amounts then outputTotal amounts-inputTotal amounts
  else inputTotal amounts-outputTotal amounts

theorem magnitude_bound (amounts : Inputs) : magnitude amounts < 2^129 := by
  have a := (amounts 0).isLt
  have b := (amounts 1).isLt
  have c := (amounts 2).isLt
  have d := (amounts 3).isLt
  unfold magnitude inputTotal outputTotal
  split <;> omega

theorem negative_boolean {F : Type} [Field F] (amounts : Inputs) :
    Square (if negative amounts then (1 : F) else 0)
      (if negative amounts then (1 : F) else 0) := by
  cases negative amounts <;> simp only [Bool.false_eq_true,if_false,if_true,Square,one_mul,zero_mul]

/-- The native signed values are calculated from four bounded amounts; the
desired signed field equation is a conclusion, never an input hypothesis. -/
theorem field_equation {F : Type} [Field F] (amounts : Inputs) :
    ((amounts 0).val : F) + ((amounts 1).val : F) -
      ((amounts 2).val : F) - ((amounts 3).val : F) =
    (magnitude amounts : F) - 2 * (if negative amounts then (1 : F) else 0) * (magnitude amounts : F) := by
  have castInput : ((amounts 0).val : F) + ((amounts 1).val : F) = (inputTotal amounts : F) := by
    simp only [inputTotal,Nat.cast_add]
  have castOutput : ((amounts 2).val : F) + ((amounts 3).val : F) = (outputTotal amounts : F) := by
    simp only [outputTotal,Nat.cast_add]
  rw [← sub_add_eq_sub_sub,castInput,castOutput]
  by_cases less : inputTotal amounts < outputTotal amounts
  · have difference : outputTotal amounts-inputTotal amounts+inputTotal amounts=outputTotal amounts :=
      Nat.sub_add_cancel (Nat.le_of_lt less)
    have cast := congrArg (fun n : Nat => (n : F)) difference
    simp only [Nat.cast_add] at cast
    simp only [magnitude,negative,less,decide_true,if_true]
    rw [← cast]
    ring
  · have difference : inputTotal amounts-outputTotal amounts+outputTotal amounts=inputTotal amounts :=
      Nat.sub_add_cancel (Nat.le_of_not_gt less)
    have cast := congrArg (fun n : Nat => (n : F)) difference
    simp only [Nat.cast_add] at cast
    simp only [magnitude,negative,less,decide_false,Bool.false_eq_true,if_false]
    rw [← cast]
    ring

set_option pp.all true in
#check @magnitude_bound
#print axioms magnitude_bound
set_option pp.all true in
#check @negative_boolean
#print axioms negative_boolean
set_option pp.all true in
#check @field_equation
#print axioms field_equation

end ShielddSecurity.TransferSignedMagnitude
