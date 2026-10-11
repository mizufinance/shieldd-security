def selectedRows := arithmetic.toList++[actualCopy]
def decodedRecipes := CompilerIndexedRecipe38.decodeList ArithmeticCoefficients39.value recipes
def expectedRows := CompilerFreshArithmetic35.rows 22738 decodedRecipes++[⟨[(0,1),(copy,-1)],[]⟩]
def mapping : Array Nat := (List.range 129).toArray
def captureIndices := List.range 128++[200769]
theorem support_checked : CompilerIndexedRecipe38.check copy 22738 recipes=true := by decide +kernel
theorem checked : CompilerFreshArithmetic35.check copy 22738 decodedRecipes=true := by rw [decodedRecipes,CompilerIndexedRecipe38.decode_list_check];exact support_checked
theorem rows_exact : CompilerFreshArithmetic35.rows 22738 decodedRecipes=arithmetic.toList := by rfl
theorem span_exact : CompilerFreshArithmetic35.span decodedRecipes=128 := by rw [decodedRecipes,CompilerIndexedRecipe38.decode_span];decide +kernel
def production (candidate : List Row) (indices : Array Nat) : Bool :=
  checkOriginalCoverage p 0 candidate.toArray expectedRows.toArray indices &&
  checkOriginalCoverage p 0 expectedRows.toArray candidate.toArray indices
theorem copy_equal : canonical p actualCopy.a=canonical p [(0,1),(copy,-1)] ∧ canonical p actualCopy.b=canonical p ([] : Linear) := by decide +kernel
theorem positive : production selectedRows mapping=true := by
  unfold production expectedRows selectedRows
  rw [rows_exact]
  apply Bool.and_eq_true_iff.mpr
  constructor
  · exact CompilerIndexedCoverage36.append_coverage p arithmetic.toList actualCopy ⟨[(0,1),(copy,-1)],[]⟩ copy_equal.1 copy_equal.2
  · exact CompilerIndexedCoverage36.append_coverage p arithmetic.toList ⟨[(0,1),(copy,-1)],[]⟩ actualCopy copy_equal.1.symm copy_equal.2.symm
theorem every_position : ∀ index : Fin 129,checkOriginalAt p 0 selectedRows.toArray expectedRows.toArray mapping index.val=true := by
  intro index
  have first : checkOriginalCoverage p 0 selectedRows.toArray expectedRows.toArray mapping=true := (Bool.and_eq_true_iff.mp positive).1
  have parts := Bool.and_eq_true_iff.mp first
  apply List.all_eq_true.mp parts.2 index.val
  apply List.mem_range.mpr
  have size : selectedRows.toArray.size=129 := by decide +kernel
  rw [size]
  exact index.isLt
theorem counts : recipes.length=72 ∧ selectedRows.length=129 ∧ captureIndices.length=129 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
def completed (base : Nat → F) := CompilerFreshArithmetic35.run 22738 base decodedRecipes
omit [CharP F p] in
theorem outside (base : Nat → F) (column : Nat) (bound : column<22738 ∨ 22866≤column) : completed base column=base column :=
  CompilerFreshArithmetic35.run_outside decodedRecipes 22738 base column (by rw [span_exact];exact bound)
theorem complete (base : Nat → F) (linked : base copy=base 0) : Satisfies (completed base) selectedRows := by
  have done := CompilerFreshArithmetic35.complete decodedRecipes copy 22738 base checked (by rw [span_exact];decide) (CompilerArithmeticTransport41.four_ne_zero (F:=F))
  have reference : Satisfies (completed base) expectedRows := by
    intro row member
    rcases List.mem_append.mp member with member|member
    · exact done row member
    · have eq : row=⟨[(0,1),(copy,-1)],[]⟩ := by simpa only [List.mem_singleton] using member
      subst row
      change Square (eval (completed base) [(0,1),(copy,-1)]) (eval (completed base) [])
      simp only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_one_mul,add_zero,
        outside base 0 (Or.inl (by decide)),outside base copy (Or.inr (by decide)),linked,add_neg_cancel]
      simp [Square]
  apply CompilerArithmeticTransport41.transfer _ selectedRows expectedRows
  · have part:= (Bool.and_eq_true_iff.mp positive).1
    have equal : (List.range selectedRows.length).toArray=mapping := by rw [counts.2.1];rfl
    rw [equal]
    exact part
  · exact reference
omit [CharP F p] in
theorem original_inputs (base : Nat → F) (input : Nat) (bound : input<22735) : completed base (3+input)=base (3+input) :=
  outside base _ (Or.inl (by omega))
omit [CharP F p] in
theorem fixed (base : Nat → F) : completed base 0=base 0 ∧ completed base 1=base 1 ∧ completed base 2=base 2 ∧ completed base copy=base copy :=
  ⟨outside base 0 (Or.inl (by decide)),outside base 1 (Or.inl (by decide)),outside base 2 (Or.inl (by decide)),outside base copy (Or.inr (by decide))⟩
def badCoefficient : List Row := let row := selectedRows.headD ⟨[],[]⟩;⟨row.a.map (fun term => (term.1,term.2+1)),row.b⟩::selectedRows.tail
theorem coefficient_rejected : production badCoefficient mapping=false := by
  have bad : checkOriginalCoverage p 0 badCoefficient.toArray expectedRows.toArray mapping=false :=
    CompilerIndexedCoverage36.reject_position p _ _ _ 0 (by decide +kernel) (by decide +kernel)
  unfold production
  rw [bad]
  rfl
theorem existing_index_rejected : production selectedRows (mapping.set! 0 1)=false := by
  have bad : checkOriginalCoverage p 0 selectedRows.toArray expectedRows.toArray (mapping.set! 0 1)=false :=
    CompilerIndexedCoverage36.reject_position p _ _ _ 0 (by decide +kernel) (by decide +kernel)
  unfold production
  rw [bad]
  rfl
theorem omission_rejected : production selectedRows.tail mapping=false := by decide +kernel
def badCopyRows := arithmetic.toList++[⟨[(0,-1),(copy,2)],[]⟩]
theorem copy_rejected : production badCopyRows mapping=false := by
  have bad : checkOriginalCoverage p 0 badCopyRows.toArray expectedRows.toArray mapping=false :=
    CompilerIndexedCoverage36.reject_position p _ _ _ 128 (by decide +kernel) (by decide +kernel)
  unfold production
  rw [bad]
  rfl
end ShielddSecurity.CapturedIndexedArithmetic40Pilot
