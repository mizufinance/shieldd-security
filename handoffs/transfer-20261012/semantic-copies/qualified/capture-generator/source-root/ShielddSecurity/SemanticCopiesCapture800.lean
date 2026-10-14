-- GENERATED from maintained exact data/template; do not edit.
import ShielddSecurity.SemanticCopiesCapture800F0
import ShielddSecurity.SemanticCopiesCapture800F1
import ShielddSecurity.SemanticCopiesCapture800F2
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SemanticCopiesCapture800
open CompilerAssertionBlock51 ConcreteJubjubField01

def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+6057+i)) 1 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+7460+i)) 1 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+19301+i)) 1

theorem rows (rho : Nat → F) (first : rho 4790=rho 4921) (second : rho 6195=rho 6325)
    (timestamp : rho 7=rho 8541) : Rows rho :=
  ⟨SemanticCopiesCapture800F0.satisfies rho first,SemanticCopiesCapture800F1.satisfies rho second,
    SemanticCopiesCapture800F2.satisfies rho timestamp⟩
end ShielddSecurity.SemanticCopiesCapture800

set_option pp.all true in
#check @ShielddSecurity.SemanticCopiesCapture800.Rows
#print axioms ShielddSecurity.SemanticCopiesCapture800.Rows

set_option pp.all true in
#check @ShielddSecurity.SemanticCopiesCapture800.rows
#print axioms ShielddSecurity.SemanticCopiesCapture800.rows
