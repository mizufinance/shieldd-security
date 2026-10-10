This is a candidate shorter proof route for the actual curve cardinality, not an established theorem. The retained desktop worker chooses whether to use it.

The exact concrete curve has W equation Y²=X³+ABX²+B²X, A=40962, B=−40964. The integer candidates give a cyclic eight-point list, four order-eight points with just two X coordinates, and Euler residues p−1 for those X values and A²−4.

For this form, an ordinary double has X(2Q)=(X(Q)²−B²)²/(4Y(Q)²), hence square X. An order-eight point with nonsquare X cannot be a double. The only affine points with 2Q=0 should be (0,0), since the remaining quadratic has nonsquare discriminant B²(A²−4); these statements require kernel proofs using the qualified concrete addition model.

Use the finite doubling homomorphism: unique nonzero two-torsion gives |ker[8]|≤8, and the eight-point witness gives equality. Thus every eight-torsion point is in the displayed cyclic list; all its order-eight points have no half. If image[8] had even cardinality, Cauchy's theorem supplies its nonzero two-torsion point 8Q, producing a point Q with order16, contradicted by the absence of halves of order-eight points. Consequently image[8] has odd cardinality.

The existing qualified r-order base point yields r dividing curve cardinality. Combining this with eight-torsion and coprimality gives 8r dividing N. The elementary affine-fibre bound N≤2p+1<24r leaves N=8r or16r. Odd image[8] excludes16r. Then N=8r yields the global exponent used by subgroup soundness.

All finite-model, cardinality, square/nonresidue, kernel/image, Cauchy and concrete binding obligations remain unproved in this packet. The Python recipe performs integer DATA checks only. It neither imports Lean nor invokes a compiler, and successful integer output does not prove this argument. No Hasse theorem is assumed or weakened.
