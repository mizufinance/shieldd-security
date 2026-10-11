import ShielddSecurity.ComparisonCertificate101
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.ComparisonComposition103
open ComparisonCertificate101
 theorem output_append (initial : Linear) (left right : List Entry) :
    output initial (left++right)=output (output initial left) right := by
  induction left generalizing initial with
  | nil => rfl
  | cons entry tail ih => exact ih entry.after
 theorem check_append (initial : Linear) (left right : List Entry)
    (before : chainCheck initial left=true)
    (after : chainCheck (output initial left) right=true) :
    chainCheck initial (left++right)=true := by
  induction left generalizing initial with
  | nil => exact after
  | cons entry tail ih =>
    have parts:=Bool.and_eq_true_iff.mp before
    have rest:=Bool.and_eq_true_iff.mp parts.2
    change (_ && (_ && chainCheck entry.after (tail++right)))=true
    exact Bool.and_eq_true_iff.mpr ⟨parts.1,Bool.and_eq_true_iff.mpr ⟨rest.1,ih entry.after rest.2 after⟩⟩
 variable {F : Type} [Field F]
 theorem scan_append (rho : Nat → F) (flag : F) (left right : List Entry) :
    rawScan rho flag (left++right)=rawScan rho (rawScan rho flag left) right := by
  induction left generalizing flag with
  | nil => rfl
  | cons entry tail ih => exact ih _
end ShielddSecurity.ComparisonComposition103

set_option pp.all true in
#check @ShielddSecurity.ComparisonComposition103.output_append
#print axioms ShielddSecurity.ComparisonComposition103.output_append
set_option pp.all true in
#check @ShielddSecurity.ComparisonComposition103.check_append
#print axioms ShielddSecurity.ComparisonComposition103.check_append
set_option pp.all true in
#check @ShielddSecurity.ComparisonComposition103.scan_append
#print axioms ShielddSecurity.ComparisonComposition103.scan_append
