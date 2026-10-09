import ShielddSecurity.ScalarBooleanCanonical

set_option maxHeartbeats 100000
namespace ShielddSecurity.ScalarWordColumn

theorem value {F : Type} [Field F] (rho : Nat → F) (columns : List Nat) (bits : List Bool)
    (length : bits.length = columns.length)
    (word : columns.map rho = bits.map (fun bit => if bit then (1 : F) else 0))
    (index : Nat) (bound : index < columns.length) :
    rho columns[index] = (if bits[index]?.getD false then 1 else 0) := by
  have bitBound : index < bits.length := by omega
  have same := congrArg (fun xs : List F => xs[index]?.getD 0) word
  simpa only [List.getElem?_map,List.getElem?_eq_getElem bound,
    List.getElem?_eq_getElem bitBound,Option.map_some,Option.getD_some] using same

theorem consecutive {F : Type} [Field F] (rho : Nat → F) (start width : Nat) (bits : List Bool)
    (length : bits.length = width)
    (word : (List.range' start width).map rho = bits.map (fun bit => if bit then (1 : F) else 0))
    (index : Nat) (bound : index < width) :
    rho (start + index) = (if bits[index]?.getD false then 1 else 0) := by
  have result := value rho (List.range' start width) bits
    (by simpa only [List.length_range'] using length) word index
    (by simpa only [List.length_range'] using bound)
  simpa only [List.getElem_range',Nat.one_mul] using result

set_option pp.all true in
#check @value
#print axioms value
set_option pp.all true in
#check @consecutive
#print axioms consecutive
end ShielddSecurity.ScalarWordColumn
