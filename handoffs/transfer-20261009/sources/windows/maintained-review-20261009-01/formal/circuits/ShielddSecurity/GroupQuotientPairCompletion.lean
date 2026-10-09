import ShielddSecurity.GroupRowCompletion

set_option maxHeartbeats 300000

namespace ShielddSecurity.GroupQuotientPairCompletion

structure Coordinate where
  numerator : Linear
  denominator : Linear
  remainder : Linear
  output : Nat
  product : Nat
  auxiliary : Nat

def Coordinate.inputs (coordinate : Coordinate) : Linear :=
  coordinate.numerator ++ coordinate.denominator ++ coordinate.remainder

def Coordinate.writes (coordinate : Coordinate) : List Nat :=
  GroupRowCompletion.writes coordinate.output coordinate.product coordinate.auxiliary

def Coordinate.rows (coordinate : Coordinate) : List Row :=
  GroupRowCompletion.quotientRows coordinate.numerator coordinate.denominator coordinate.remainder
    coordinate.output coordinate.product coordinate.auxiliary

def Coordinate.Shape (coordinate : Coordinate) : Prop :=
  coordinate.output ≠ coordinate.product ∧ coordinate.output ≠ coordinate.auxiliary ∧
  coordinate.product ≠ coordinate.auxiliary ∧
  ∀ term ∈ coordinate.inputs, term.1 ∉ coordinate.writes

variable {F : Type} [Field F]

def Coordinate.build (coordinate : Coordinate) (base : Nat → F) : Nat → F :=
  GroupRowCompletion.extendQuotient base coordinate.numerator coordinate.denominator coordinate.remainder
    coordinate.output coordinate.product coordinate.auxiliary

def build (x y : Coordinate) (base : Nat → F) : Nat → F := y.build (x.build base)
def rows (x y : Coordinate) : List Row := x.rows ++ y.rows
def point (x y : Coordinate) (rho : Nat → F) : Group.Point F := ⟨rho x.output,rho y.output⟩

theorem second_eval (x y : Coordinate) (base : Nat → F)
    (separate : ∀ term ∈ y.inputs, term.1 ∉ x.writes)
    (terms : Linear) (included : ∀ term ∈ terms, term ∈ y.inputs) :
    eval (x.build base) terms = eval base terms :=
  GroupRowCompletion.eval_preserves base x.numerator x.denominator x.remainder terms
    x.output x.product x.auxiliary (by intro term member; exact separate term (included term member))

theorem pair_preserves (x y : Coordinate) (base : Nat → F) (column : Nat)
    (outsideX : column ∉ x.writes) (outsideY : column ∉ y.writes) :
    build x y base column = base column :=
  (GroupRowCompletion.extend_preserves (x.build base) y.numerator y.denominator y.remainder
    y.output y.product y.auxiliary column outsideY).trans
    (GroupRowCompletion.extend_preserves base x.numerator x.denominator x.remainder
      x.output x.product x.auxiliary column outsideX)

private theorem assemble (x y : Coordinate) (base : Nat → F) (target : Group.Point F)
    (fresh : ∀ row ∈ x.rows, ∀ term ∈ row.a ++ row.b, term.1 ∉ y.writes)
    (keepX : x.output ∉ y.writes)
    (first : Satisfies (x.build base) x.rows ∧ x.build base x.output = target.x)
    (second : Satisfies (build x y base) y.rows ∧ build x y base y.output = target.y) :
    Satisfies (build x y base) (rows x y) ∧ point x y (build x y base) = target := by
  have earlier : Satisfies (build x y base) x.rows :=
    GroupRowCompletion.preserves_rows (x.build base) y.numerator y.denominator y.remainder
      y.output y.product y.auxiliary x.rows first.1 fresh
  have xValue : build x y base x.output = target.x :=
    (GroupRowCompletion.extend_preserves (x.build base) y.numerator y.denominator y.remainder
      y.output y.product y.auxiliary x.output keepX).trans first.2
  constructor
  · intro row member
    rcases List.mem_append.mp member with left | right
    · exact earlier row left
    · exact second.1 row right
  · exact congrArg₂ Group.Point.mk xValue second.2

/-- Actual optimized double coordinates are constructed in source x/y order.
The caller proves input polynomial meanings from its already constructed
materializations. Complete-curve facts derive both legal denominators; no
computed quotient, desired point, or initial row truth is supplied. -/
theorem double_complete (d imaginary : F)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary*imaginary = -1)
    (input : Group.Point F) (valid : Group.OnCurve d input) (x y : Coordinate) (base : Nat → F)
    (shapeX : x.Shape) (shapeY : y.Shape)
    (separate : ∀ term ∈ y.inputs, term.1 ∉ x.writes)
    (fresh : ∀ row ∈ x.rows, ∀ term ∈ row.a ++ row.b, term.1 ∉ y.writes)
    (keepX : x.output ∉ y.writes)
    (numeratorX : eval base x.numerator = GroupExtended.doubleNumerator input)
    (denominatorX : eval base x.denominator = GroupExtended.doubleXDenominator input)
    (numeratorY : eval base y.numerator = Group.diagonal input input)
    (denominatorY : eval base y.denominator = GroupExtended.doubleYDenominator input) :
    Satisfies (build x y base) (rows x y) ∧
      point x y (build x y base) = Group.affineAdd d input input := by
  have first := GroupRowCompletion.complete_double_coordinate d imaginary nonSquare imaginarySquare
    input valid false base x.numerator x.denominator x.remainder x.output x.product x.auxiliary
    shapeX.1 shapeX.2.1 shapeX.2.2.1 shapeX.2.2.2 numeratorX denominatorX
  have yNumerator : eval (x.build base) y.numerator = Group.diagonal input input :=
    (second_eval x y base separate y.numerator
      (by intro term member; simp [Coordinate.inputs,member])).trans numeratorY
  have yDenominator : eval (x.build base) y.denominator = GroupExtended.doubleYDenominator input :=
    (second_eval x y base separate y.denominator
      (by intro term member; simp [Coordinate.inputs,member])).trans denominatorY
  have second := GroupRowCompletion.complete_double_coordinate d imaginary nonSquare imaginarySquare
    input valid true (x.build base) y.numerator y.denominator y.remainder y.output y.product y.auxiliary
    shapeY.1 shapeY.2.1 shapeY.2.2.1 shapeY.2.2.2 yNumerator yDenominator
  exact assemble x y base (Group.affineAdd d input input) fresh keepX first second

/-- The variable-base affine addition uses two independent quotient writes.
Input curve validity derives denominator legality even when an intermediate
coordinate or its fused product has value zero. -/
theorem add_complete (d imaginary : F)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary*imaginary = -1)
    (left right : Group.Point F) (leftValid : Group.OnCurve d left) (rightValid : Group.OnCurve d right)
    (x y : Coordinate) (base : Nat → F) (shapeX : x.Shape) (shapeY : y.Shape)
    (separate : ∀ term ∈ y.inputs, term.1 ∉ x.writes)
    (fresh : ∀ row ∈ x.rows, ∀ term ∈ row.a ++ row.b, term.1 ∉ y.writes)
    (keepX : x.output ∉ y.writes)
    (numeratorX : eval base x.numerator = Group.cross left right)
    (denominatorX : eval base x.denominator = 1 + Group.delta d left right)
    (numeratorY : eval base y.numerator = Group.diagonal left right)
    (denominatorY : eval base y.denominator = 1 - Group.delta d left right) :
    Satisfies (build x y base) (rows x y) ∧
      point x y (build x y base) = Group.affineAdd d left right := by
  have first := GroupRowCompletion.complete_add_coordinate d imaginary nonSquare imaginarySquare
    left right leftValid rightValid false base x.numerator x.denominator x.remainder x.output x.product x.auxiliary
    shapeX.1 shapeX.2.1 shapeX.2.2.1 shapeX.2.2.2 numeratorX denominatorX
  have yNumerator : eval (x.build base) y.numerator = Group.diagonal left right :=
    (second_eval x y base separate y.numerator
      (by intro term member; simp [Coordinate.inputs,member])).trans numeratorY
  have yDenominator : eval (x.build base) y.denominator = 1 - Group.delta d left right :=
    (second_eval x y base separate y.denominator
      (by intro term member; simp [Coordinate.inputs,member])).trans denominatorY
  have second := GroupRowCompletion.complete_add_coordinate d imaginary nonSquare imaginarySquare
    left right leftValid rightValid true (x.build base) y.numerator y.denominator y.remainder y.output y.product y.auxiliary
    shapeY.1 shapeY.2.1 shapeY.2.2.1 shapeY.2.2.2 yNumerator yDenominator
  exact assemble x y base (Group.affineAdd d left right) fresh keepX first second

set_option pp.all true in
#check @second_eval
#print axioms second_eval
set_option pp.all true in
#check @pair_preserves
#print axioms pair_preserves
set_option pp.all true in
#check @double_complete
#print axioms double_complete
set_option pp.all true in
#check @add_complete
#print axioms add_complete

end ShielddSecurity.GroupQuotientPairCompletion
