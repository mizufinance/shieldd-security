import ShielddSecurity.VariableTraceBits446
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationTraceIndex450

def column (family window component limb : Nat) : Nat := 2253+756*family+6*window+2*component+limb

theorem window_decode (family window component limb : Nat)
    (familyBound : family<2) (windowLower : 1≤window) (windowBound : window<126)
    (componentBound : component<3) (limbBound : limb<2) :
    2253≤column family window component limb ∧ column family window component limb≤3764 ∧
    (column family window component limb-2253)/756=family ∧
    ((column family window component limb-2253)%756)/2=3*window+component ∧
    (column family window component limb-2253)%2=limb ∧
    3≤3*window+component ∧
    (3*window+component-3)/3+1=window ∧ (3*window+component-3)%3=component := by
  unfold column
  omega

theorem prefix_decode (family point limb : Nat) (familyBound : family<2)
    (pointBound : point<3) (limbBound : limb<2) :
    2253≤column family 0 point limb ∧ column family 0 point limb≤3764 ∧
    (column family 0 point limb-2253)/756=family ∧
    ((column family 0 point limb-2253)%756)/2=point ∧
    (column family 0 point limb-2253)%2=limb := by
  unfold column
  omega

theorem previous_decode (window : Nat) (lower : 1<window) :
    3≤3*window-1 ∧ (3*window-1-3)/3+1=window-1 ∧ (3*window-1-3)%3=2 := by omega
end ShielddSecurity.AuthorizationTraceIndex450

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceIndex450.column
#print axioms ShielddSecurity.AuthorizationTraceIndex450.column

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceIndex450.window_decode
#print axioms ShielddSecurity.AuthorizationTraceIndex450.window_decode

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceIndex450.prefix_decode
#print axioms ShielddSecurity.AuthorizationTraceIndex450.prefix_decode

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceIndex450.previous_decode
#print axioms ShielddSecurity.AuthorizationTraceIndex450.previous_decode
