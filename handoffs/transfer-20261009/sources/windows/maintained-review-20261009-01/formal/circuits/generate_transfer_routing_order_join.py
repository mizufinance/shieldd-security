"""Derive precision ordering and active thresholds from one actual assignment."""
from pathlib import Path


def _member(index):
    proof='List.mem_cons.mpr (Or.inl rfl)'
    for _ in range(index):proof='List.mem_cons.mpr (Or.inr ('+proof+'))'
    return proof


def generate():
    hand=(Path(__file__).resolve().parent/'ShielddSecurity/RoutingBitSemantics.lean').read_text()
    theory=hand.replace('ShielddSecurity.RoutingBitSemantics','ShielddSecurity.RuntimeRoutingBitTheory')
    names=[f'RuntimeRoutingOrderActive{i:02}' for i in range(32)]
    d0,d1='RuntimeRoutingPrecision0Domain','RuntimeRoutingPrecision1Domain'
    p0,p1='RuntimeRoutingPrecision0Prefix','RuntimeRoutingPrecision1Prefix'
    name='RuntimeRoutingOrderActiveJoin'
    source=''.join(f'import ShielddSecurity.{module}\n' for module in names+[p0,p1,'RuntimeRoutingBitTheory'])
    source+=('set_option maxHeartbeats 2000000\nset_option maxRecDepth 4096\n'
             f'namespace ShielddSecurity.{name}\n')
    source+='def rowPages : List (List Row) := ['+','.join(module+'.rawRows' for module in names)+']\n'
    source+=f'def rawRows : List Row := {d0}.rawRows ++ {d1}.rawRows ++ rowPages.flatten\n'
    source+=f'def regulated : Linear := {names[0]}.regulated\n'
    source+='def active (index : Nat) : Linear := match index with\n'
    source+=''.join(f'  | {index} => {module}.active\n' for index,module in enumerate(names))+'  | _ => []\n'
    source+='''variable {F : Type} [Field F] [CharP F Scalar.modulus]
private theorem first_rows (rho : Nat → F) (satisfied : Satisfies rho rawRows) : Satisfies rho '''+d0+'''.rawRows := by
  intro row member
  exact satisfied row (List.mem_append_left _ member)
private theorem second_rows (rho : Nat → F) (satisfied : Satisfies rho rawRows) : Satisfies rho '''+d1+'''.rawRows := by
  intro row member
  exact satisfied row (List.mem_append_right _ (List.mem_append_left _ member))
private theorem equations (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) (index : Nat) (bound : index < 32) :
    eval rho ('''+p0+'''.«prefix» index) * (1-eval rho ('''+p1+'''.«prefix» index)) = 0 ∧
    eval rho (active index) = eval rho ('''+p1+'''.«prefix» index) + eval rho regulated *
      (eval rho ('''+p0+'''.«prefix» index)-eval rho ('''+p1+'''.«prefix» index)) ∧
    Square (eval rho regulated) (eval rho regulated) ∧ Square (eval rho (active index)) (eval rho (active index)) := by
  have choices : '''+' ∨ '.join(f'index = {i}' for i in range(32))+''' := by omega
  rcases choices with '''+' | '.join('rfl' for _ in names)+'\n'
    for index,module in enumerate(names):
        source+=f'''  · have localRows : Satisfies rho {module}.rawRows := by
      intro row member
      apply satisfied row
      apply List.mem_append_right
      apply List.mem_append_right
      apply List.mem_flatten.mpr
      exact ⟨{module}.rawRows,{_member(index)},member⟩
    have firstLink : {module}.first = {p0}.«prefix» {index} := by decide
    have secondLink : {module}.second = {p1}.«prefix» {index} := by decide
    have regulatorLink : {module}.regulated = regulated := by decide
    have activeLink : {module}.active = active {index} := rfl
    have combined := And.intro ({module}.order_sound rho one four localRows)
      (And.intro ({module}.active_sound rho four localRows) ({module}.booleans_sound rho localRows))
    simpa only [firstLink,secondLink,regulatorLink,activeLink] using combined
'''
    source+='''theorem semantics (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    ∃ first second : Nat, ∃ flag : Bool,
      first < 33 ∧ second < 33 ∧ first ≤ second ∧
      eval rho '''+d0+'''.input = (first : F) ∧ eval rho '''+d1+'''.input = (second : F) ∧
      eval rho regulated = (if flag then 1 else 0) ∧
      ∀ index : Nat, index < 32 → eval rho (active index) =
        if index < (if flag then first else second) then 1 else 0 := by
  have firstRows := first_rows rho satisfied
  have secondRows := second_rows rho satisfied
  obtain ⟨first,firstBound,firstInput⟩ := '''+d0+'''.domain_sound rho one four firstRows
  obtain ⟨second,secondBound,secondInput⟩ := '''+d1+'''.domain_sound rho one four secondRows
  have products : ∀ index : Nat, index < 32 →
      (if index < first then (1 : F) else 0) * (1-(if index < second then (1 : F) else 0)) = 0 := by
    intro index bound
    have equation := (equations rho one four satisfied index bound).1
    rw ['''+p0+'''.prefix_sound rho one four firstRows first firstBound firstInput index bound,
        '''+p1+'''.prefix_sound rho one four secondRows second secondBound secondInput index bound] at equation
    exact equation
  have ordered : first ≤ second :=
    RuntimeRoutingBitTheory.precision_order_sound (F := F) first second (by omega) (by omega)
      (by intro index bound; simpa [RuntimeRoutingBitTheory.bit] using products index bound)
  have boolean := (equations rho one four satisfied 0 (by decide)).2.2.1
  rcases boolean_sound (eval rho regulated) boolean with zero | unit
  · refine ⟨first,second,false,firstBound,secondBound,ordered,firstInput,secondInput,?_,?_⟩
    · simpa using zero
    · intro index bound
      have selected := (equations rho one four satisfied index bound).2.1
      rw ['''+p0+'''.prefix_sound rho one four firstRows first firstBound firstInput index bound,
          '''+p1+'''.prefix_sound rho one four secondRows second secondBound secondInput index bound,zero] at selected
      simpa only [Bool.false_eq_true,ite_false,zero_mul,add_zero] using selected
  · refine ⟨first,second,true,firstBound,secondBound,ordered,firstInput,secondInput,?_,?_⟩
    · simpa using unit
    · intro index bound
      have selected := (equations rho one four satisfied index bound).2.1
      rw ['''+p0+'''.prefix_sound rho one four firstRows first firstBound firstInput index bound,
          '''+p1+'''.prefix_sound rho one four secondRows second secondBound secondInput index bound,unit] at selected
      have meaning : eval rho (active index) = if index < first then 1 else 0 := by
        calc
          eval rho (active index) = _ := selected
          _ = (if index < first then 1 else 0) := by ring
      simpa using meaning
set_option pp.all true in
#check @semantics
#print axioms semantics
'''
    return {'RuntimeRoutingBitTheory':theory,name:source+f'end ShielddSecurity.{name}\n'}
