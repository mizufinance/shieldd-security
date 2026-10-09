import ShielddSecurity.GroupQuotientPairCompletion
import ShielddSecurity.ScalarRandomizerCompletion
import ShielddSecurity.CompilerOrder

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ShielddSecurity.GroupFixedWindowTemplate

/-- The six affine materializations of an ordinary fixed window. The folded
initial window is handled by its separate actual constructor. Coordinates here
are linear expressions, not assumed values of a selected or outgoing point. -/
structure Layout where
  inputX : Linear
  inputY : Linear
  low : Linear
  high : Linear
  selectedX : Linear
  selectedY : Linear
  xx : Linear
  yy : Linear
  sum : Linear
  xy : Linear
  base : Group.Point Int
  twice : Group.Point Int
  triple : Group.Point Int
  d : Int

def castPoint {F : Type} [Field F] (point : Group.Point Int) : Group.Point F :=
  ⟨(point.x : F), (point.y : F)⟩

def Layout.input {F : Type} [Field F] (layout : Layout) (rho : Nat → F) : Group.Point F :=
  ⟨eval rho layout.inputX, eval rho layout.inputY⟩

def Layout.selected {F : Type} [Field F] (layout : Layout) (rho : Nat → F) : Group.Point F :=
  ⟨eval rho layout.selectedX, eval rho layout.selectedY⟩

def Layout.loX (layout : Layout) : Linear := scaleLinear layout.base.x layout.low
def Layout.loY (layout : Layout) : Linear :=
  [(0,1)] ++ scaleLinear (layout.base.y-1) layout.low
def Layout.hiX (layout : Layout) : Linear :=
  [(0,layout.twice.x)] ++ scaleLinear (layout.triple.x-layout.twice.x) layout.low
def Layout.hiY (layout : Layout) : Linear :=
  [(0,layout.twice.y)] ++ scaleLinear (layout.triple.y-layout.twice.y) layout.low

structure Product where
  left : Linear
  right : Linear
  output : Linear
  data : ScalarRows.ProductData

structure ProductData where
  selectX : ScalarRows.ProductData
  selectY : ScalarRows.ProductData
  xx : ScalarRows.ProductData
  yy : ScalarRows.ProductData
  sum : ScalarRows.ProductData
  xy : ScalarRows.ProductData

def Layout.products (layout : Layout) (data : ProductData) : List Product :=
  [⟨layout.high, Compiler.subtract layout.hiX layout.loX,
      Compiler.subtract layout.selectedX layout.loX, data.selectX⟩,
   ⟨layout.high, Compiler.subtract layout.hiY layout.loY,
      Compiler.subtract layout.selectedY layout.loY, data.selectY⟩,
   ⟨layout.inputX, layout.selectedX, layout.xx, data.xx⟩,
   ⟨layout.inputY, layout.selectedY, layout.yy, data.yy⟩,
   ⟨layout.inputX ++ layout.inputY, layout.selectedX ++ layout.selectedY, layout.sum, data.sum⟩,
   ⟨layout.xx, layout.yy, layout.xy, data.xy⟩]

def checkProducts (p : Nat) (rows : List Row) (products : List Product) : Bool :=
  products.all (fun product => ScalarRows.checkProduct p rows
    product.left product.right product.output product.data)

def Layout.numeratorX (layout : Layout) : Linear :=
  Compiler.subtract (Compiler.subtract layout.sum layout.xx) layout.yy
def Layout.numeratorY (layout : Layout) : Linear := layout.yy ++ layout.xx
def Layout.denominatorX (layout : Layout) : Linear := [(0,1)] ++ scaleLinear layout.d layout.xy
def Layout.denominatorY (layout : Layout) : Linear := [(0,1)] ++ scaleLinear (-layout.d) layout.xy

variable {F : Type} [Field F]

/-- Constant table membership follows from its exact modular polynomial
certificate, independently of the accumulator and selected scalar bits. -/
theorem checked_table_curve {p : Nat} [CharP F p] (d : Int) (point : Group.Point Int)
    (rho : Nat → F) (one : rho 0 = 1)
    (checked : Compiler.canonical p
      [(0,(point.y*point.y-point.x*point.x)-(1+d*point.x*point.x*point.y*point.y))] = []) :
    Group.OnCurve (d : F) (castPoint point) := by
  have identity := Compiler.canonical_equal rho
    [(0,(point.y*point.y-point.x*point.x)-(1+d*point.x*point.x*point.y*point.y))] [] checked
  simp only [eval,one,mul_one,add_zero,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_one] at identity
  exact sub_eq_zero.mp identity

theorem checked_product {p : Nat} [CharP F p] (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (rows : List Row)
    (satisfied : Satisfies rho rows) (products : List Product)
    (checked : checkProducts p rows products = true) (product : Product)
    (member : product ∈ products) :
    eval rho product.output = eval rho product.left * eval rho product.right :=
  ScalarRows.checked_product_sound rho one four rows satisfied _ _ _ _
    (List.all_eq_true.mp checked product member)

/-- All desired selector and denominator values follow from the finite product
checks. In the constructive theorem below, satisfaction used here is produced
by the materialization constructor, never passed in by the native caller. -/
theorem checked_formulas {p : Nat} [CharP F p] (layout : Layout) (data : ProductData)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (rows : List Row) (satisfied : Satisfies rho rows)
    (checked : checkProducts p rows (layout.products data) = true) :
    layout.selected rho = Group.windowPoint (eval rho layout.low) (eval rho layout.high)
      (castPoint layout.base) (castPoint layout.twice) (castPoint layout.triple) ∧
    eval rho layout.numeratorX = Group.cross (layout.input rho) (layout.selected rho) ∧
    eval rho layout.numeratorY = Group.diagonal (layout.input rho) (layout.selected rho) ∧
    eval rho layout.denominatorX = 1 + Group.delta (layout.d : F) (layout.input rho) (layout.selected rho) ∧
    eval rho layout.denominatorY = 1 - Group.delta (layout.d : F) (layout.input rho) (layout.selected rho) := by
  have sx := checked_product rho one four rows satisfied (layout.products data) checked
    ⟨layout.high,Compiler.subtract layout.hiX layout.loX,
      Compiler.subtract layout.selectedX layout.loX,data.selectX⟩ (by simp [Layout.products])
  have sy := checked_product rho one four rows satisfied (layout.products data) checked
    ⟨layout.high,Compiler.subtract layout.hiY layout.loY,
      Compiler.subtract layout.selectedY layout.loY,data.selectY⟩ (by simp [Layout.products])
  have xx := checked_product rho one four rows satisfied (layout.products data) checked
    ⟨layout.inputX,layout.selectedX,layout.xx,data.xx⟩ (by simp [Layout.products])
  have yy := checked_product rho one four rows satisfied (layout.products data) checked
    ⟨layout.inputY,layout.selectedY,layout.yy,data.yy⟩ (by simp [Layout.products])
  have total := checked_product rho one four rows satisfied (layout.products data) checked
    ⟨layout.inputX ++ layout.inputY,layout.selectedX ++ layout.selectedY,layout.sum,data.sum⟩
    (by simp [Layout.products])
  have xy := checked_product rho one four rows satisfied (layout.products data) checked
    ⟨layout.xx,layout.yy,layout.xy,data.xy⟩ (by simp [Layout.products])
  simp only [Compiler.eval_subtract] at sx sy
  have selected : layout.selected rho = Group.windowPoint (eval rho layout.low) (eval rho layout.high)
      (castPoint layout.base) (castPoint layout.twice) (castPoint layout.triple) := by
    apply congrArg₂ Group.Point.mk
    · change eval rho layout.selectedX = _
      calc
        _ = eval rho layout.loX + eval rho layout.high * (eval rho layout.hiX-eval rho layout.loX) :=
          (sub_eq_iff_eq_add.mp sx).trans (add_comm _ _)
        _ = _ := by
          simp only [Layout.loX,Layout.hiX,eval_append,eval_scale,eval,one,
            Int.cast_sub,Int.cast_one,one_mul,mul_one,add_zero,castPoint,Group.windowPoint,Group.chooseCoordinate]
          ring
    · change eval rho layout.selectedY = _
      calc
        _ = eval rho layout.loY + eval rho layout.high * (eval rho layout.hiY-eval rho layout.loY) :=
          (sub_eq_iff_eq_add.mp sy).trans (add_comm _ _)
        _ = _ := by
          simp only [Layout.loY,Layout.hiY,eval_append,eval_scale,eval,one,
            Int.cast_sub,Int.cast_one,one_mul,mul_one,add_zero,castPoint,Group.windowPoint,Group.chooseCoordinate]
          ring
  simp only [eval_append] at total
  refine ⟨selected,?_,?_,?_,?_⟩
  · simp only [Layout.numeratorX,Compiler.eval_subtract,xx,yy,total,Group.cross,Layout.input,Layout.selected]
    ring
  · simp only [Layout.numeratorY,eval_append,xx,yy,Group.diagonal,Layout.input,Layout.selected]
  · simp only [Layout.denominatorX,eval_append,eval_scale,eval,one,Int.cast_one,one_mul,add_zero,
      xy,xx,yy,Group.delta,Layout.input,Layout.selected]
    ring
  · simp only [Layout.denominatorY,eval_append,eval_scale,eval,one,Int.cast_one,Int.cast_neg,
      one_mul,add_zero,xy,xx,yy,Group.delta,Layout.input,Layout.selected]
    ring

def construct (base : Nat → F) (stages : List CompilerCompletion.Step)
    (x y : GroupQuotientPairCompletion.Coordinate) : Nat → F :=
  GroupQuotientPairCompletion.build x y (CompilerCompletion.run base stages)

/-- A universal ordinary-window constructor. All structural premises are finite
LC/row/write data: a material-only stage list, freshness, four canonical quotient
LC identities, and the six product checker results. No prior row truth,
computed selector, denominator nonzero, or wanted output is supplied. -/
theorem construct_complete {p : Nat} [CharP F p]
    (layout : Layout) (data : ProductData) (stages : List CompilerCompletion.Step)
    (kept : List Nat) (base : Nat → F)
    (ordered : CompilerCompletion.Topological kept [] stages)
    (material : ScalarRandomizerCompletion.Products stages)
    (checked : checkProducts p (CompilerCompletion.emitted stages) (layout.products data) = true)
    (zeroKept : 0 ∈ kept)
    (inputsKept : ∀ term ∈ layout.inputX ++ layout.inputY ++ layout.low ++ layout.high, term.1 ∈ kept)
    (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare (layout.d : F))
    (imaginarySquare : imaginary*imaginary = -1)
    (low high : Bool) (lowValue : eval base layout.low = if low then 1 else 0)
    (highValue : eval base layout.high = if high then 1 else 0)
    (inputValid : Group.OnCurve (layout.d : F) (layout.input base))
    (baseValid : Group.OnCurve (layout.d : F) (castPoint layout.base))
    (twiceValid : Group.OnCurve (layout.d : F) (castPoint layout.twice))
    (tripleValid : Group.OnCurve (layout.d : F) (castPoint layout.triple))
    (x y : GroupQuotientPairCompletion.Coordinate)
    (shapeX : x.Shape) (shapeY : y.Shape)
    (separate : ∀ term ∈ y.inputs, term.1 ∉ x.writes)
    (fresh : ∀ row ∈ x.rows, ∀ term ∈ row.a ++ row.b, term.1 ∉ y.writes)
    (keepX : x.output ∉ y.writes)
    (prefixFresh : ∀ row ∈ CompilerCompletion.emitted stages,
      ∀ term ∈ row.a ++ row.b, term.1 ∉ x.writes ∧ term.1 ∉ y.writes)
    (quotientKept : ∀ column ∈ kept, column ∉ x.writes ∧ column ∉ y.writes)
    (quotientLCs : Compiler.canonical p x.numerator = Compiler.canonical p layout.numeratorX ∧
      Compiler.canonical p x.denominator = Compiler.canonical p layout.denominatorX ∧
      Compiler.canonical p y.numerator = Compiler.canonical p layout.numeratorY ∧
      Compiler.canonical p y.denominator = Compiler.canonical p layout.denominatorY) :
    Satisfies (construct base stages x y)
      (CompilerCompletion.emitted stages ++ GroupQuotientPairCompletion.rows x y) ∧
    Group.OnCurve (layout.d : F) (GroupQuotientPairCompletion.point x y (construct base stages x y)) ∧
    (∀ column ∈ kept, construct base stages x y column = base column) ∧
    GroupQuotientPairCompletion.point x y (construct base stages x y) =
      Group.affineAdd (layout.d : F) (layout.input base)
        (Group.windowPoint (if low then 1 else 0) (if high then 1 else 0)
          (castPoint layout.base) (castPoint layout.twice) (castPoint layout.triple)) := by
  let built := CompilerCompletion.run base stages
  have prefixDone : Satisfies built (CompilerCompletion.emitted stages) := by
    simpa only [List.nil_append] using CompilerCompletion.run_complete base stages kept [] ordered
      (ScalarRandomizerCompletion.products_legal base stages material) (by intro row member; cases member)
  have preserves := CompilerCompletion.run_preserves base stages kept [] ordered
  have oneBuilt : built 0 = 1 := (preserves 0 zeroKept).trans one
  have termsSame (terms : Linear)
      (included : ∀ term ∈ terms, term ∈ layout.inputX ++ layout.inputY ++ layout.low ++ layout.high) :
      eval built terms = eval base terms := by
    apply eval_agrees
    intro term member
    exact preserves term.1 (inputsKept term (included term member))
  have inputSame : layout.input built = layout.input base := by
    apply congrArg₂ Group.Point.mk
    · exact termsSame layout.inputX (by intro term member; simp [member])
    · exact termsSame layout.inputY (by intro term member; simp [member])
  have lowSame := termsSame layout.low (by intro term member; simp [member])
  have highSame := termsSame layout.high (by intro term member; simp [member])
  have formulas := checked_formulas layout data built oneBuilt four _ prefixDone checked
  have selectedValid : Group.OnCurve (layout.d : F) (layout.selected built) := by
    rw [formulas.1,lowSame,highSame,lowValue,highValue]
    exact Group.window_onCurve _ low high _ _ _ baseValid twiceValid tripleValid
  have incomingValid : Group.OnCurve (layout.d : F) (layout.input built) := by
    rw [inputSame]
    exact inputValid
  have pairDone := GroupQuotientPairCompletion.add_complete (layout.d : F) imaginary nonSquare
    imaginarySquare (layout.input built) (layout.selected built) incomingValid selectedValid
    x y built shapeX shapeY separate fresh keepX
    ((Compiler.canonical_equal built _ _ quotientLCs.1).trans formulas.2.1)
    ((Compiler.canonical_equal built _ _ quotientLCs.2.1).trans formulas.2.2.2.1)
    ((Compiler.canonical_equal built _ _ quotientLCs.2.2.1).trans formulas.2.2.1)
    ((Compiler.canonical_equal built _ _ quotientLCs.2.2.2).trans formulas.2.2.2.2)
  have prior : Satisfies (construct base stages x y) (CompilerCompletion.emitted stages) := by
    intro row member
    have same (terms : Linear) (included : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
        eval (construct base stages x y) terms = eval built terms := by
      apply eval_agrees
      intro term present
      have outside := prefixFresh row member term (included term present)
      exact GroupQuotientPairCompletion.pair_preserves x y built term.1 outside.1 outside.2
    rw [same row.a (by intro term member; exact List.mem_append_left row.b member),
      same row.b (by intro term member; exact List.mem_append_right row.a member)]
    exact prefixDone row member
  refine ⟨?_,?_,?_,?_⟩
  · intro row member
    rcases List.mem_append.mp member with earlier | current
    · exact prior row earlier
    · exact pairDone.1 row current
  · change Group.OnCurve (layout.d : F)
      (GroupQuotientPairCompletion.point x y (GroupQuotientPairCompletion.build x y built))
    rw [pairDone.2]
    apply Group.affine_rows_onCurve (layout.d : F) imaginary nonSquare imaginarySquare
      (layout.input built) (layout.selected built) _ incomingValid selectedValid
    · change (Group.cross (layout.input built) (layout.selected built) /
        (1 + Group.delta (layout.d : F) (layout.input built) (layout.selected built))) *
        (1 + Group.delta (layout.d : F) (layout.input built) (layout.selected built)) = _
      exact div_mul_cancel₀ _
        (Group.denominators_nonzero _ imaginary nonSquare imaginarySquare _ _ incomingValid selectedValid).1
    · change (Group.diagonal (layout.input built) (layout.selected built) /
        (1 - Group.delta (layout.d : F) (layout.input built) (layout.selected built))) *
        (1 - Group.delta (layout.d : F) (layout.input built) (layout.selected built)) = _
      exact div_mul_cancel₀ _
        (Group.denominators_nonzero _ imaginary nonSquare imaginarySquare _ _ incomingValid selectedValid).2
  · intro column member
    exact (GroupQuotientPairCompletion.pair_preserves x y built column
      (quotientKept column member).1 (quotientKept column member).2).trans (preserves column member)
  · have selectedSame : layout.selected built =
        Group.windowPoint (if low then 1 else 0) (if high then 1 else 0)
          (castPoint layout.base) (castPoint layout.twice) (castPoint layout.triple) := by
      rw [formulas.1,lowSame,highSame,lowValue,highValue]
    exact pairDone.2.trans (congrArg₂ (Group.affineAdd (layout.d : F)) inputSame selectedSame)

set_option pp.all true in
#check @checked_table_curve
#print axioms checked_table_curve
set_option pp.all true in
#check @checked_product
#print axioms checked_product
set_option pp.all true in
#check @checked_formulas
#print axioms checked_formulas
set_option pp.all true in
#check @construct_complete
#print axioms construct_complete

end ShielddSecurity.GroupFixedWindowTemplate
