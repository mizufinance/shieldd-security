import ShielddSecurity.ArithmeticCoefficients39C00
import ShielddSecurity.ArithmeticCoefficients39C01
import ShielddSecurity.ArithmeticCoefficients39C02
import ShielddSecurity.ArithmeticCoefficients39C03
import ShielddSecurity.ArithmeticCoefficients39C04
import ShielddSecurity.ArithmeticCoefficients39C05
import ShielddSecurity.ArithmeticCoefficients39C06
import ShielddSecurity.ArithmeticCoefficients39C07
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.ArithmeticCoefficients39
def value (index : Nat) : Int := (if index<4096 then (if index<2048 then (if index<1024 then ArithmeticCoefficients39C00.value index else ArithmeticCoefficients39C01.value index) else (if index<3072 then ArithmeticCoefficients39C02.value index else ArithmeticCoefficients39C03.value index)) else (if index<6144 then (if index<5120 then ArithmeticCoefficients39C04.value index else ArithmeticCoefficients39C05.value index) else (if index<7168 then ArithmeticCoefficients39C06.value index else ArithmeticCoefficients39C07.value index)))
end ShielddSecurity.ArithmeticCoefficients39
set_option pp.all true in
#check @ShielddSecurity.ArithmeticCoefficients39.value
#print axioms ShielddSecurity.ArithmeticCoefficients39.value
