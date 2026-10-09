import ShielddSecurity.ConcretePointTraceStep151
import ShielddSecurity.ConcretePointScalarRecurrence01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcretePointTraceStep152
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
variable [DecidableEq F]
local notation "base" => ConcretePointOperationPilot01.base

def baseX : F := 39680211447325986415026918192437531897852916166128269978655486138252525496083
def baseY : F := 43044799768094727361329244498846272665229388789665544224645223436242971151146
def inputX : F := 8546699611385590940827842050899672520723875975458564781221614448166593430857
def inputY : F := 36560873442994454358221483337331433721597935770518524736843426816175207837731
def doubleX : F := 31377089600692335345539465202229641755185991732207410461614767105978359494774
def doubleY : F := 18540913326032609200191315319724757365728071065355860251325188698499579073829
def doubleSlope : F := 30596457031495815373087546116579057080825569443913104721834705683560261976633
def outX : F := 31377089600692335345539465202229641755185991732207410461614767105978359494774
def outY : F := 18540913326032609200191315319724757365728071065355860251325188698499579073829

theorem next_double : ∃ output : curve.Equation doubleX doubleY,
    ((5170576494588253443952275824166409374034985481 : Nat) • base) + ((5170576494588253443952275824166409374034985481 : Nat) • base) = WeierstrassCurve.Affine.Point.mk output := by
  obtain ⟨inputValid, inputImage⟩ := ConcretePointTraceStep151.prefix_image
  have valid : curve.Equation inputX inputY := inputValid
  have nonzero : (2 : F) * inputY ≠ 0 := by
    have integer : ((2 : Int) * (36560873442994454358221483337331433721597935770518524736843426816175207837731 : Int)) * (28668597730297490823201234007917473706725415026672309873997020239135293948809 : Int) =
        (1 : Int) + (39978315224258185810717845310309975943878287672793539320937082405832164988789 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_nonzero _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have slopeRow : doubleSlope * (2 * inputY) = 3 * inputX ^ 2 + 2 * (A * B) * inputX + B * B := by
    have integer : (30596457031495815373087546116579057080825569443913104721834705683560261976633 : Int) * ((2 : Int) * (36560873442994454358221483337331433721597935770518524736843426816175207837731 : Int)) =
        (3 : Int) * (8546699611385590940827842050899672520723875975458564781221614448166593430857 : Int) ^ 2 + (2 : Int) * ((40962 : Int) * (-40964 : Int)) * (8546699611385590940827842050899672520723875975458564781221614448166593430857 : Int) + (-40964 : Int) * (-40964 : Int) + (38487546115767485941916213742727721067150537947848506877485986997499764835235 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have xRow : doubleX = doubleSlope ^ 2 - A * B - inputX - inputX := by
    have integer : (31377089600692335345539465202229641755185991732207410461614767105978359494774 : Int) =
        (30596457031495815373087546116579057080825569443913104721834705683560261976633 : Int) ^ 2 - (40962 : Int) * (-40964 : Int) - (8546699611385590940827842050899672520723875975458564781221614448166593430857 : Int) - (8546699611385590940827842050899672520723875975458564781221614448166593430857 : Int) + (-17853104954453863191449576974357040812315878930962787366415626623963770875313 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  have yRow : doubleY = doubleSlope * (inputX - doubleX) - inputY := by
    have integer : (18540913326032609200191315319724757365728071065355860251325188698499579073829 : Int) =
        (30596457031495815373087546116579057080825569443913104721834705683560261976633 : Int) * ((8546699611385590940827842050899672520723875975458564781221614448166593430857 : Int) - (31377089600692335345539465202229641755185991732207410461614767105978359494774 : Int)) - (36560873442994454358221483337331433721597935770518524736843426816175207837731 : Int) + (13321586489920447019627217452688926113086974721456885887921729246257049175117 : Int) * (Scalar.modulus : Int) := by decide +kernel
    have equal := ConcreteIntegerCertificates01.field_eq _ _ _ integer
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, A, B, baseX, baseY, inputX, inputY, doubleX, doubleY, doubleSlope, outX, outY] using equal
  obtain ⟨output, doubled⟩ := ConcretePointOperationRows01.tangent_rows valid nonzero slopeRow xRow yRow
  refine ⟨output, ?_⟩
  rw [inputImage]
  exact doubled

theorem prefix_image : ∃ output : curve.Equation outX outY,
    (10341152989176506887904551648332818748069970962 : Nat) • base = WeierstrassCurve.Affine.Point.mk output := by
  simpa only [outX, outY, doubleX, doubleY, show (10341152989176506887904551648332818748069970962 : Nat) = 5170576494588253443952275824166409374034985481 + 5170576494588253443952275824166409374034985481 by rfl, ConcretePointScalarRecurrence01.even_prefix] using next_double

end ShielddSecurity.ConcretePointTraceStep152
