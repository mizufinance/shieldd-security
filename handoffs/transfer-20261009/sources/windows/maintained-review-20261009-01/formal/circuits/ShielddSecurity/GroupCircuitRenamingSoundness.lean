import ShielddSecurity.GroupCircuitRenaming
import ShielddSecurity.GroupVariableCircuitSoundness

set_option maxHeartbeats 200000

namespace ShielddSecurity.GroupCircuitRenamingSoundness

open GroupFixedCircuitCompletion GroupVariableCircuitCompletion
variable {F : Type} [Field F]

theorem point_pullback (rho : Nat → F) (columns : Nat → Nat) (coordinates : Linear × Linear) :
    point rho (RowRenaming.linear columns coordinates.1,RowRenaming.linear columns coordinates.2) =
      point (fun column => rho (columns column)) coordinates := by
  simp only [point,RowRenaming.eval_linear]

/-- Pull back an arbitrary satisfying assignment. This transports semantic
soundness directly; it invokes neither a constructor nor its output formula. -/
theorem local_sound (columns : Nat → Nat) (zero : columns 0 = 0)
    (copy : Nat) (copyFixed : columns copy = copy) (d : F)
    (sourceTables : Tables) (source : Program)
    (sound : GroupVariableCircuitSoundness.LocalSound d copy sourceTables source) :
    GroupVariableCircuitSoundness.LocalSound d copy
      (GroupCircuitRenaming.tables columns sourceTables) (GroupCircuitRenaming.program columns source) := by
  intro rho one linked incoming curved low high satisfied
  have sourceOne : (fun column => rho (columns column)) 0 = 1 := by
    simpa only [zero] using one
  have sourceLink : (fun column => rho (columns column)) copy =
      (fun column => rho (columns column)) 0 := by
    simpa only [zero,copyFixed] using linked
  have sourceIncoming : Group.OnCurve d (point (fun column => rho (columns column)) source.input) := by
    simpa only [GroupCircuitRenaming.program,point_pullback] using incoming
  have sourceCurved : Curved d sourceTables (fun column => rho (columns column)) := by
    simpa only [GroupCircuitRenaming.tables,Curved,point_pullback] using curved
  have sourceLow : eval (fun column => rho (columns column)) source.low =
      if source.lowBit then 1 else 0 := by
    simpa only [GroupCircuitRenaming.program,RowRenaming.eval_linear] using low
  have sourceHigh : eval (fun column => rho (columns column)) source.high =
      if source.highBit then 1 else 0 := by
    simpa only [GroupCircuitRenaming.program,RowRenaming.eval_linear] using high
  have sourceRows : Satisfies (fun column => rho (columns column)) source.rows := by
    apply RowRenaming.satisfied_rows rho columns source.rows _ _ satisfied
    intro row member
    exact List.mem_map_of_mem member
  have result := sound _ sourceOne sourceLink sourceIncoming sourceCurved sourceLow sourceHigh sourceRows
  simpa only [GroupCircuitRenaming.program,GroupCircuitRenaming.tables,
    point_pullback,RowRenaming.eval_linear] using result

set_option pp.all true in
#check @point_pullback
#print axioms point_pullback
set_option pp.all true in
#check @local_sound
#print axioms local_sound
end ShielddSecurity.GroupCircuitRenamingSoundness
