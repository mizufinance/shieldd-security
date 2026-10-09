import ShielddSecurity.ShielddNativeAddress

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddNativeAddressLegality

open ShielddNativeAddress

variable {F : Type} [Field F]
  {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

/-- Prime-subgroup membership is the named global native point-type contract.
Nonidentity below is obtained from an executed owned constructor guard. -/
def LegalPoint
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (point : S) : Prop :=
  Scalar.order • upstream.embed (upstream.promote point) = 0 ∧
    upstream.embed (upstream.promote point) ≠ 0

/-- ka::Public::from_point retains its actual input only after rejecting its
identity. A plain Public record supplies neither this guard nor its success. -/
theorem public_from_point_legal
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (point : S) (key : Public S)
    (accepted : publicFromPoint upstream point = some key) :
    key.point = point ∧ LegalPoint upstream key.point := by
  cases identity : upstream.isIdentity point with
  | true =>
      simp only [publicFromPoint,identity,ite_true] at accepted
      cases accepted
  | false =>
      have same : (⟨point⟩ : Public S) = key :=
        Option.some.inj (by
          simpa only [publicFromPoint,identity,Bool.false_eq_true,ite_false] using accepted)
      rw [← same]
      refine ⟨rfl,upstream.subgroup point,?_⟩
      intro zero
      have checked := (upstream.identityReflects point).mpr zero
      rw [identity] at checked
      cases checked

/-- Successful Secret::diversified_public excludes an identity input base
because its actual multiplied output passed Public::from_point. This uses
only the global functional multiplication/identity contracts and nsmul_zero;
neither a desired transmission value nor a nonzero scalar is a premise. -/
theorem diversified_public_legal
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (secret : Secret) (generator : S) (key : Public S)
    (accepted : diversifiedPublic upstream primitives secret generator = some key) :
    LegalPoint upstream generator ∧ LegalPoint upstream key.point := by
  cases parsed : primitives.parseFr secret.bytes with
  | none =>
      simp only [diversifiedPublic,parsed] at accepted
      cases accepted
  | some scalar =>
      have constructed : publicFromPoint upstream (primitives.multiply generator scalar) = some key := by
        simpa only [diversifiedPublic,parsed] using accepted
      have guarded := public_from_point_legal upstream _ key constructed
      refine ⟨⟨upstream.subgroup generator,?_⟩,guarded.2⟩
      intro baseZero
      apply guarded.2.2
      rw [guarded.1,primitives.promoteMultiply,upstream.multiplyEmbedding,baseZero,nsmul_zero]

/-- Successful payment_address performs both diversified_public and
Address::from_components. Both stored points therefore meet the independent
native input legality needed by subgroup multiplication. This is success,
not a totality claim for every diversifier: Rust uses expect on failure. -/
theorem payment_address_legal
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (secret : Secret) (key : ShortBytes)
    (index : Index) (address : Address S)
    (accepted : paymentAddress upstream primitives secret key index = some address) :
    LegalPoint upstream address.diversified ∧ LegalPoint upstream address.transmission.point := by
  let diversifier := diversifierForIndex upstream primitives key index
  let generator := diversifiedGenerator upstream primitives diversifier
  change (match diversifiedPublic upstream primitives secret generator with
    | some publicKey => fromComponents upstream primitives diversifier publicKey
    | none => none) = some address at accepted
  cases publicRead : diversifiedPublic upstream primitives secret generator with
  | none =>
      simp only [publicRead] at accepted
      cases accepted
  | some publicKey =>
      have guarded := diversified_public_legal upstream primitives secret generator publicKey publicRead
      simp only [publicRead] at accepted
      change (if upstream.isIdentity generator then none else
        some (⟨diversifier,generator,publicKey⟩ : Address S)) = some address at accepted
      cases identity : upstream.isIdentity generator with
      | true =>
          simp only [identity,ite_true] at accepted
          cases accepted
      | false =>
          have same : (⟨diversifier,generator,publicKey⟩ : Address S) = address :=
            Option.some.inj (by
              simpa only [identity,Bool.false_eq_true,ite_false] using accepted)
          rw [← same]
          exact guarded

/-- views_address true executes the multiplied Public guard and matches that
actual Public with the stored transmission. It is sufficient even without
presuming an Address record invariant or a desired coordinate equation. -/
theorem viewed_address_legal [DecidableEq S]
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream) (secret : Secret) (address : Address S)
    (viewed : viewsAddress upstream primitives secret address = true) :
    LegalPoint upstream address.diversified ∧ LegalPoint upstream address.transmission.point := by
  cases publicRead : diversifiedPublic upstream primitives secret address.diversified with
  | none =>
      simp only [viewsAddress,publicRead] at viewed
      cases viewed
  | some key =>
      have same : key = address.transmission :=
        of_decide_eq_true (by simpa only [viewsAddress,publicRead] using viewed)
      have guarded := diversified_public_legal upstream primitives secret address.diversified key publicRead
      rw [same] at guarded
      exact guarded

set_option pp.all true in
#check @public_from_point_legal
#print axioms public_from_point_legal
set_option pp.all true in
#check @diversified_public_legal
#print axioms diversified_public_legal
set_option pp.all true in
#check @payment_address_legal
#print axioms payment_address_legal
set_option pp.all true in
#check @viewed_address_legal
#print axioms viewed_address_legal

end ShielddSecurity.ShielddNativeAddressLegality
