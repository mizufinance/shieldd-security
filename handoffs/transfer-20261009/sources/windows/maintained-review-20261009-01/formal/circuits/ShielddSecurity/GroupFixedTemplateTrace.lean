import ShielddSecurity.GroupFixedWindowTemplate
import ShielddSecurity.GroupFixedTableTemplate
import ShielddSecurity.GroupFixedCircuitCompletion
import ShielddSecurity.GroupFixedChunks

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ShielddSecurity.GroupFixedTemplateTrace

/-- Physical window data contains no proposed output value. Its output is the
two actual quotient columns evaluated in the common constructed assignment.
The folded initial window remains a separately proved prefix. -/
structure Window where
  program : GroupFixedCircuitCompletion.Program
  layout : GroupFixedWindowTemplate.Layout
  products : GroupFixedWindowTemplate.ProductData
  x : GroupQuotientPairCompletion.Coordinate
  y : GroupQuotientPairCompletion.Coordinate
  nextBase : Group.Point Int

def Window.output (window : Window) : Linear × Linear :=
  ([(window.x.output,1)],[(window.y.output,1)])

def Window.input (window : Window) : Linear × Linear :=
  (window.layout.inputX,window.layout.inputY)

def Window.normalRows (copy : Nat) (window : Window) : List Row :=
  Compiler.unoutlineRows copy window.program.rows

def Window.productX (window : Window) : Linear :=
  [(window.x.product,1)] ++ window.x.remainder

def Window.productY (window : Window) : Linear :=
  [(window.y.product,1)] ++ window.y.remainder

/-- Every condition here is a finite coefficient, physical-row, or Boolean
source-data check. No row truth or coordinate of a desired result is stored. -/
def Window.Checked (p copy : Nat) (d : Int) (window : Window) : Prop :=
  window.program.input = window.input ∧
  window.program.output = window.output ∧
  window.program.low = window.layout.low ∧
  window.program.high = window.layout.high ∧
  window.layout.d = d ∧
  Compiler.checkRow p window.program.rows ⟨[(0,1),(copy,-1)],[]⟩ = true ∧
  GroupFixedWindowTemplate.checkProducts p (window.normalRows copy)
    (window.layout.products window.products) = true ∧
  ScalarRows.checkProduct p (window.normalRows copy) [(window.x.output,1)]
    window.x.denominator window.productX (.product [(window.x.auxiliary,1)]) = true ∧
  Compiler.checkRow p (window.normalRows copy)
    ⟨Compiler.subtract window.productX window.x.numerator,[]⟩ = true ∧
  ScalarRows.checkProduct p (window.normalRows copy) [(window.y.output,1)]
    window.y.denominator window.productY (.product [(window.y.auxiliary,1)]) = true ∧
  Compiler.checkRow p (window.normalRows copy)
    ⟨Compiler.subtract window.productY window.y.numerator,[]⟩ = true ∧
  Compiler.canonical p window.x.numerator = Compiler.canonical p window.layout.numeratorX ∧
  Compiler.canonical p window.x.denominator = Compiler.canonical p window.layout.denominatorX ∧
  Compiler.canonical p window.y.numerator = Compiler.canonical p window.layout.numeratorY ∧
  Compiler.canonical p window.y.denominator = Compiler.canonical p window.layout.denominatorY

def Window.TableChecked (p : Nat) (window : Window) : Prop :=
  Compiler.canonical p [(0,(window.layout.base.y*window.layout.base.y-
    window.layout.base.x*window.layout.base.x)-
    (1+window.layout.d*window.layout.base.x*window.layout.base.x*
      window.layout.base.y*window.layout.base.y))] = [] ∧
  Compiler.canonical p [(0,(window.layout.twice.y*window.layout.twice.y-
    window.layout.twice.x*window.layout.twice.x)-
    (1+window.layout.d*window.layout.twice.x*window.layout.twice.x*
      window.layout.twice.y*window.layout.twice.y))] = [] ∧
  GroupFixedTableTemplate.xCertificate p window.layout.d
    ⟨window.layout.base,window.layout.base,window.layout.twice⟩ ∧
  GroupFixedTableTemplate.yCertificate p window.layout.d
    ⟨window.layout.base,window.layout.base,window.layout.twice⟩ ∧
  GroupFixedTableTemplate.xCertificate p window.layout.d
    ⟨window.layout.twice,window.layout.base,window.layout.triple⟩ ∧
  GroupFixedTableTemplate.yCertificate p window.layout.d
    ⟨window.layout.twice,window.layout.base,window.layout.triple⟩ ∧
  GroupFixedTableTemplate.xCertificate p window.layout.d
    ⟨window.layout.twice,window.layout.twice,window.nextBase⟩ ∧
  GroupFixedTableTemplate.yCertificate p window.layout.d
    ⟨window.layout.twice,window.layout.twice,window.nextBase⟩

variable {F : Type} [Field F]

def Window.witness (window : Window) (rho : Nat → F) : GroupFixedWindows.FixedWindowWitness F :=
  ⟨window.program.lowBit,window.program.highBit,
   GroupFixedWindowTemplate.castPoint window.layout.twice,
   GroupFixedWindowTemplate.castPoint window.layout.triple,
   GroupFixedWindowTemplate.castPoint window.nextBase,
   GroupQuotientPairCompletion.point window.x window.y rho⟩

/-- Soundness of one finite actual row/table certificate. Whole completion
below supplies row satisfaction from the local constructors and frame proof;
it never assumes these individual row predicates at the native boundary. -/
theorem checked_window {p : Nat} [CharP F p]
    (copy : Nat) (d : Int) (rho : Nat → F) (one : rho 0 = 1)
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (d : F)) (imaginarySquare : imaginary*imaginary = -1)
    (window : Window) (checked : window.Checked p copy d)
    (table : window.TableChecked p) (rows : Satisfies rho window.program.rows)
    (low : eval rho window.program.low = if window.program.lowBit then 1 else 0)
    (high : eval rho window.program.high = if window.program.highBit then 1 else 0) :
    GroupFixedWindows.FixedWindowEquations (d : F)
      (GroupFixedCircuitCompletion.point rho window.input)
      (GroupFixedWindowTemplate.castPoint window.layout.base) (window.witness rho) := by
  rcases checked with ⟨inputEq,outputEq,lowEq,highEq,dEq,link,products,
    productX,assertX,productY,assertY,numX,denX,numY,denY⟩
  have normal : Satisfies rho (window.normalRows copy) :=
    Compiler.unoutline_rows_sound rho copy window.program.rows rows link
  have formulas := GroupFixedWindowTemplate.checked_formulas window.layout window.products
    rho one four (window.normalRows copy) normal products
  have xProduct := ScalarRows.checked_product_sound rho one four (window.normalRows copy)
    normal [(window.x.output,1)] window.x.denominator window.productX
    (.product [(window.x.auxiliary,1)]) productX
  have yProduct := ScalarRows.checked_product_sound rho one four (window.normalRows copy)
    normal [(window.y.output,1)] window.y.denominator window.productY
    (.product [(window.y.auxiliary,1)]) productY
  have xAssertion := Compiler.checked_assertion_sound rho (window.normalRows copy)
    window.productX window.x.numerator normal assertX
  have yAssertion := Compiler.checked_assertion_sound rho (window.normalRows copy)
    window.productY window.y.numerator normal assertY
  have numeratorX := Compiler.canonical_equal rho _ _ numX
  have denominatorX := Compiler.canonical_equal rho _ _ denX
  have numeratorY := Compiler.canonical_equal rho _ _ numY
  have denominatorY := Compiler.canonical_equal rho _ _ denY
  simp only [eval,Int.cast_one,one_mul,add_zero] at xProduct yProduct
  rw [xAssertion,numeratorX,denominatorX,formulas.2.1,formulas.2.2.2.1] at xProduct
  rw [yAssertion,numeratorY,denominatorY,formulas.2.2.1,formulas.2.2.2.2] at yProduct
  have selected := formulas.1
  rw [← lowEq,← highEq,low,high] at selected
  rw [selected,dEq] at xProduct yProduct
  have baseValid := GroupFixedWindowTemplate.checked_table_curve window.layout.d
    window.layout.base rho one table.1
  have twiceValid := GroupFixedWindowTemplate.checked_table_curve window.layout.d
    window.layout.twice rho one table.2.1
  have ns : Group.NoUnitSquare (window.layout.d : F) := by rw [dEq]; exact nonSquare
  have twice := GroupFixedTableTemplate.checked_add window.layout.d
    ⟨window.layout.base,window.layout.base,window.layout.twice⟩ rho one imaginary ns
    imaginarySquare baseValid baseValid table.2.2.1 table.2.2.2.1
  have triple := GroupFixedTableTemplate.checked_add window.layout.d
    ⟨window.layout.twice,window.layout.base,window.layout.triple⟩ rho one imaginary ns
    imaginarySquare twiceValid baseValid table.2.2.2.2.1 table.2.2.2.2.2.1
  have next := GroupFixedTableTemplate.checked_add window.layout.d
    ⟨window.layout.twice,window.layout.twice,window.nextBase⟩ rho one imaginary ns
    imaginarySquare twiceValid twiceValid table.2.2.2.2.2.2.1 table.2.2.2.2.2.2.2
  rw [dEq] at twice triple next
  refine ⟨⟨twice,triple,next⟩,?_,?_⟩
  · convert xProduct.symm using 1 <;>
      simp only [Window.witness,Window.input,GroupFixedCircuitCompletion.point,
        GroupFixedWindowTemplate.Layout.input,GroupQuotientPairCompletion.point,Group.cross] <;>
      ring
  · simpa only [Window.witness,Window.input,GroupFixedCircuitCompletion.point,
      GroupFixedWindowTemplate.Layout.input,GroupQuotientPairCompletion.point,Group.diagonal]
      using yProduct.symm

/-- Source alignment is a finite equality of actual LC lists and successive
native table constants. It contains no field assignment or output meaning. -/
def Aligned (input : Linear × Linear) (base : Group.Point Int) : List Window → Prop
  | [] => True
  | window :: tail => window.input = input ∧ window.layout.base = base ∧
      Aligned window.output window.nextBase tail

def endpoint (input : Linear × Linear) : List Window → Linear × Linear
  | [] => input
  | window :: tail => endpoint window.output tail

theorem checked_trace {p : Nat} [CharP F p]
    (copy : Nat) (d : Int) (rho : Nat → F) (one : rho 0 = 1)
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (d : F)) (imaginarySquare : imaginary*imaginary = -1)
    (windows : List Window) (input : Linear × Linear) (base : Group.Point Int)
    (aligned : Aligned input base windows)
    (checked : ∀ window ∈ windows, window.Checked p copy d ∧ window.TableChecked p)
    (rows : Satisfies rho (GroupFixedCircuitCompletion.rows (windows.map Window.program)))
    (bits : ∀ window ∈ windows,
      eval rho window.program.low = (if window.program.lowBit then 1 else 0) ∧
      eval rho window.program.high = (if window.program.highBit then 1 else 0)) :
    GroupFixedWindows.FixedTraceEquations (d : F)
      (GroupFixedCircuitCompletion.point rho input) (GroupFixedWindowTemplate.castPoint base)
      (windows.map (fun window => window.witness rho)) := by
  induction windows generalizing input base with
  | nil => exact True.intro
  | cons window tail ih =>
      have localRows : Satisfies rho window.program.rows := by
        intro row member
        exact rows row (List.mem_append_left _ member)
      have facts := checked window (by simp)
      have values := bits window (by simp)
      have first := checked_window copy d rho one four imaginary nonSquare imaginarySquare
        window facts.1 facts.2 localRows values.1 values.2
      rw [aligned.1,aligned.2.1] at first
      have remaining : Satisfies rho (GroupFixedCircuitCompletion.rows (tail.map Window.program)) := by
        intro row member
        exact rows row (List.mem_append_right _ member)
      have rest := ih window.output window.nextBase aligned.2.2
        (by intro next member; exact checked next (List.mem_cons_of_mem _ member))
        remaining (by intro next member; exact bits next (List.mem_cons_of_mem _ member))
      have outputSame : GroupFixedCircuitCompletion.point rho window.output =
          (window.witness rho).output := by
        simp only [Window.output,Window.witness,GroupFixedCircuitCompletion.point,
          GroupQuotientPairCompletion.point,eval,Int.cast_one,one_mul,add_zero]
      rw [outputSame] at rest
      exact ⟨first,rest⟩

theorem endpoint_trace (rho : Nat → F) (windows : List Window) (input : Linear × Linear) :
    GroupFixedCircuitCompletion.point rho (endpoint input windows) =
      GroupFixedWindows.fixedTraceOutput (GroupFixedCircuitCompletion.point rho input)
        (windows.map (fun window => window.witness rho)) := by
  induction windows generalizing input with
  | nil => rfl
  | cons window tail ih =>
      change GroupFixedCircuitCompletion.point rho (endpoint window.output tail) = _
      rw [ih]
      have outputSame : GroupFixedCircuitCompletion.point rho window.output =
          (window.witness rho).output := by
        simp only [Window.output,Window.witness,GroupFixedCircuitCompletion.point,
          GroupQuotientPairCompletion.point,eval,Int.cast_one,one_mul,add_zero]
      rw [outputSame]
      rfl

/-- The native endpoint is derived on the one assignment constructed by all
actual local programs. Only finite frames/checker data and independent source
bit/initial-prefix meanings enter; there is no component row-truth premise.
The standard curve and exact initial generator/prefix interpretation are named
global/native source obligations. The scalar recurrence is the existing one. -/
theorem constructs_native {p : Nat} [CharP F p] {J : Type} [AddCommGroup J]
    (copy : Nat) (d : Int) (model : Group.StandardCurveModel J (d : F))
    (rho : Nat → F) (windows : List Window) (input : Linear × Linear) (base : Group.Point Int)
    (kept : List Nat) (acc generator : J) (one : rho 0 = 1)
    (linked : rho copy = rho 0) (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (d : F)) (imaginarySquare : imaginary*imaginary = -1)
    (inputMeaning : GroupFixedCircuitCompletion.point rho input = model.coordinates acc)
    (baseMeaning : GroupFixedWindowTemplate.castPoint base = model.coordinates generator)
    (constructors : ∀ window ∈ windows,
      GroupFixedCircuitCompletion.LocalConstruct (d : F) copy window.program)
    (protectedColumns : ∀ program ∈ windows.map Window.program,
      GroupFixedCircuitCompletion.Protected kept program)
    (inputSupports : ∀ term ∈ input.1 ++ input.2, term.1 ∈ kept)
    (bitSupports : ∀ program ∈ windows.map Window.program,
      ∀ term ∈ program.low ++ program.high, term.1 ∈ kept)
    (fresh : GroupFixedCircuitCompletion.Fresh [] (windows.map Window.program))
    (programAligned : GroupFixedCircuitCompletion.Aligned input (windows.map Window.program))
    (aligned : Aligned input base windows)
    (zeroKept : 0 ∈ kept) (copyKept : copy ∈ kept)
    (checked : ∀ window ∈ windows, window.Checked p copy d ∧ window.TableChecked p)
    (bits : ∀ program ∈ windows.map Window.program,
      eval rho program.low = (if program.lowBit then 1 else 0) ∧
      eval rho program.high = (if program.highBit then 1 else 0)) :
    let completed := GroupFixedCircuitCompletion.run rho (windows.map Window.program)
    Satisfies completed (GroupFixedCircuitCompletion.rows (windows.map Window.program)) ∧
    (∀ column ∈ kept, completed column = rho column) ∧
    GroupFixedCircuitCompletion.point completed (endpoint input windows) =
      model.coordinates (acc + TransferWindows.digitsValue
        ((windows.map (fun window => window.witness completed)).map GroupFixedWindows.fixedDigit) • generator) := by
  let programs := windows.map Window.program
  let completed := GroupFixedCircuitCompletion.run rho programs
  have localConstructors : ∀ program ∈ programs,
      GroupFixedCircuitCompletion.LocalConstruct (d : F) copy program := by
    intro program member
    obtain ⟨window,present,rfl⟩ := List.mem_map.mp member
    exact constructors window present
  have incoming : Group.OnCurve (d : F) (GroupFixedCircuitCompletion.point rho input) := by
    rw [inputMeaning]
    exact model.onCurve acc
  have done := GroupFixedCircuitCompletion.constructs (d : F) copy rho programs input [] kept
    localConstructors protectedColumns bitSupports fresh programAligned zeroKept copyKept
    one linked (by intro row member; cases member) incoming bits
  have allRows : Satisfies completed (GroupFixedCircuitCompletion.rows programs) := by
    simpa only [List.nil_append] using done.1
  have preserves : ∀ column ∈ kept, completed column = rho column := done.2.2
  have inputKept : GroupFixedCircuitCompletion.point completed input =
      GroupFixedCircuitCompletion.point rho input := by
    apply congrArg₂ Group.Point.mk
    · apply eval_agrees
      intro term member
      exact preserves term.1 (inputSupports term (List.mem_append_left _ member))
    · apply eval_agrees
      intro term member
      exact preserves term.1 (inputSupports term (List.mem_append_right _ member))
  have completedBits : ∀ window ∈ windows,
      eval completed window.program.low = (if window.program.lowBit then 1 else 0) ∧
      eval completed window.program.high = (if window.program.highBit then 1 else 0) := by
    intro window member
    have present : window.program ∈ programs := List.mem_map_of_mem member
    have values := bits window.program present
    have same (terms : Linear) (inside : ∀ term ∈ terms, term ∈ window.program.low ++ window.program.high) :
        eval completed terms = eval rho terms := by
      apply eval_agrees
      intro term termMember
      exact preserves term.1 (bitSupports window.program present term (inside term termMember))
    exact ⟨(same _ (by intro term member; exact List.mem_append_left _ member)).trans values.1,
      (same _ (by intro term member; exact List.mem_append_right _ member)).trans values.2⟩
  have trace := checked_trace copy d completed ((preserves 0 zeroKept).trans one)
    four imaginary nonSquare imaginarySquare windows input base aligned checked allRows completedBits
  rw [inputKept,inputMeaning,baseMeaning] at trace
  have native := GroupFixedWindows.fixed_trace_value_coordinates (d : F) imaginary model
    nonSquare imaginarySquare (windows.map (fun window => window.witness completed)) acc generator trace
  refine ⟨allRows,preserves,?_⟩
  exact (endpoint_trace completed windows input).trans (by rw [inputKept,inputMeaning]; exact native)

set_option pp.all true in
#check @checked_window
#print axioms checked_window
set_option pp.all true in
#check @checked_trace
#print axioms checked_trace
set_option pp.all true in
#check @endpoint_trace
#print axioms endpoint_trace
set_option pp.all true in
#check @constructs_native
#print axioms constructs_native
end ShielddSecurity.GroupFixedTemplateTrace
