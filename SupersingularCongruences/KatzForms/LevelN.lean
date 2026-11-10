/-
Assembled by AxiomProver.
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import SupersingularCongruences.EllipticCurve.Scaling
public import SupersingularCongruences.EllipticCurve.PointMap
public import SupersingularCongruences.LevelOne.IntegralQExpansion

/-!
# Algebraic modular forms of full level `N`

Let `L` be an algebraically closed field of characteristic `p ∤ N` and fix a primitive `N`-th root
of unity `ζ ∈ L`, the image of `ζ_N` under a homomorphism `ℤ[ζ_N, 1/N] → L`. The compactified
moduli `M_N` of elliptic curves with a basis `(P₁, P₂)` of the `N`-torsion with Weil pairing
`e_N(P₁, P₂) = ζ_N` is a smooth proper geometrically connected curve over `ℤ[ζ_N, 1/N]`
[katz-mazur, Corollary 10.9.2], [katz1973, Section 1.4]. Algebraic modular forms of weight `k` on
`M_N` [katz1973, Section 1.2]
are represented, after base change to `L`, by their values on test objects
`(E, (P₁, P₂), λ ω_E)` over `L` with `e_N(P₁, P₂) = ζ` (`LevelNTest.IsValid`).

* `WeilPairing N L` bundles the properties of the Weil pairing `e_N` that we use
  [silverman-aec, Section III.8], since Mathlib has no Weil pairing.
* `LevelNForms N L e ζ` bundles the cited facts about algebraic forms of level `N` over `L`.

These are used in the manuscript's eta-power proof of Theorem 1.3 (Proposition 4.5).
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine CongruenceSubgroup

/-- A test object `(E, (P₁, P₂), ω)` for level `N`: a short Weierstrass elliptic curve over `L`,
two points, and the differential `ω = diff • (dx / (2y))`. -/
structure LevelNTest (L : Type*) [Field L] [DecidableEq L] where
  /-- The short Weierstrass model. -/
  curve : WeierstrassCurve L
  [isElliptic : curve.IsElliptic]
  [isShortNF : curve.IsShortNF]
  /-- The first basis point. -/
  P₁ : curve.toAffine.Point
  /-- The second basis point. -/
  P₂ : curve.toAffine.Point
  /-- The scalar `λ` with `ω = λ · dx / (2y)`. -/
  diff : Lˣ

attribute [instance] LevelNTest.isElliptic LevelNTest.isShortNF

/-- `(P₁, P₂)` is a basis of the `N`-torsion `E[N] ≅ (ℤ / N)²`. -/
def IsTorsionBasis {L : Type*} [Field L] [DecidableEq L] {W : WeierstrassCurve L} (N : ℕ)
    (P₁ P₂ : W.toAffine.Point) : Prop :=
  N • P₁ = 0 ∧ N • P₂ = 0 ∧ ∀ a b : ℕ, a • P₁ + b • P₂ = 0 → N ∣ a ∧ N ∣ b

/-- **The Weil pairing** `e_N` on `N`-torsion points (cited facts [silverman-aec, Section III.8]).
Only the properties used in the manuscript are recorded. -/
structure WeilPairing (N : ℕ) (L : Type*) [Field L] [DecidableEq L] where
  /-- The pairing `e_N(P, Q)` (values in `μ_N(L)` on `N`-torsion points). -/
  pair (W : WeierstrassCurve L) : W.toAffine.Point → W.toAffine.Point → L
  /-- Bilinearity gives `e_N(-P, -Q) = e_N(P, Q)` [silverman-aec, Proposition III.8.1(a)]. -/
  pair_neg_neg (W : WeierstrassCurve L) {P Q : W.toAffine.Point} (hP : N • P = 0)
    (hQ : N • Q = 0) : pair W (-P) (-Q) = pair W P Q
  /-- Compatibility with isomorphisms [silverman-aec, Proposition III.8.2]. -/
  pair_scaling (W : WeierstrassCurve L) (u : Lˣ) (P Q : W.toAffine.Point) :
    pair (W.scaling u) (Point.scaling W u P) (Point.scaling W u Q) = pair W P Q
  /-- Galois equivariance [silverman-aec, Proposition III.8.1(d)]. -/
  pair_map (W : WeierstrassCurve L) (σ : L ≃+* L) (P Q : W.toAffine.Point) :
    pair (W.map (σ : L →+* L)) (Point.mapRingHom (σ : L →+* L) P)
      (Point.mapRingHom (σ : L →+* L) Q) = σ (pair W P Q)
  /-- For every primitive `N`-th root of unity `ζ` there is a basis of `E[N]` with pairing `ζ`
  (`E[N] ≅ (ℤ / N)²` for `p ∤ N` [silverman-aec, Corollary III.6.4(b)], and `e_N` is alternating
  and nondegenerate, so `e_N(P₁, P₂)` is a primitive root for a basis and changes by `det` under a
  change of basis [silverman-aec, Proposition III.8.1]). -/
  exists_basis (W : WeierstrassCurve L) [W.IsElliptic] [W.IsShortNF] {ζ : L}
    (hζ : IsPrimitiveRoot ζ N) :
    ∃ P₁ P₂ : W.toAffine.Point, IsTorsionBasis N P₁ P₂ ∧ pair W P₁ P₂ = ζ

namespace LevelNTest

variable {N : ℕ} {L : Type*} [Field L] [DecidableEq L]

/-- The test object is a point of `M_N ⊗ L`: `(P₁, P₂)` is a basis of `E[N]` with
`e_N(P₁, P₂) = ζ`. -/
def IsValid (e : WeilPairing N L) (ζ : L) (T : LevelNTest L) : Prop :=
  IsTorsionBasis N T.P₁ T.P₂ ∧ e.pair T.curve T.P₁ T.P₂ = ζ

/-- The isomorphic test object `(W.scaling u, (ψ P₁, ψ P₂), (λ u) ω)`. -/
noncomputable def scale (T : LevelNTest L) (u : Lˣ) : LevelNTest L where
  curve := T.curve.scaling u
  P₁ := Point.scaling T.curve u T.P₁
  P₂ := Point.scaling T.curve u T.P₂
  diff := T.diff * u

/-- The test object `(E, (P₁, P₂), c ω)`. -/
def smulDiff (T : LevelNTest L) (c : Lˣ) : LevelNTest L where
  curve := T.curve
  P₁ := T.P₁
  P₂ := T.P₂
  diff := c * T.diff

/-- The test object `(E, (-P₁, -P₂), ω)`. -/
def neg (T : LevelNTest L) : LevelNTest L where
  curve := T.curve
  P₁ := -T.P₁
  P₂ := -T.P₂
  diff := T.diff

/-- The conjugate test object by a field automorphism `σ` of `L`. -/
noncomputable def map (T : LevelNTest L) (σ : L ≃+* L) : LevelNTest L where
  curve := T.curve.map (σ : L →+* L)
  isShortNF := ⟨by simp, by simp, by simp⟩
  P₁ := Point.mapRingHom (σ : L →+* L) T.P₁
  P₂ := Point.mapRingHom (σ : L →+* L) T.P₂
  diff := Units.map (σ : L →* L) T.diff

/-- The discriminant rule `Δ(E, λ ω_E) = λ⁻¹² Δ(E)`. -/
noncomputable def discriminantRule (T : LevelNTest L) : L :=
  ((T.diff : L) ^ 12)⁻¹ * T.curve.Δ

end LevelNTest

/-- **Algebraic modular forms of full level `N` over `L`** (cited facts). Forms are represented by
their values on the test objects `T` with `T.IsValid e ζ`; their values at other test objects are
irrelevant, and all statements are restricted to valid test objects. Two forms are identified when
they agree on all valid test objects (`LevelNForms.Agree`).

Sources: [katz1973, Sections 1.1–1.2, 1.4, Corollary 1.6.2, Theorem 1.7.1],
[katz-mazur, (8.8) and Corollary 10.9.2]. -/
structure LevelNForms (N : ℕ) (L : Type*) [Field L] [DecidableEq L] (e : WeilPairing N L)
    (ζ : L) where
  /-- The forms of weight `k`, as functions of test objects. -/
  form : ℤ → Submodule L (LevelNTest L → L)
  /-- Products of forms are forms. -/
  mul_mem {a b : ℤ} {f g : LevelNTest L → L} : f ∈ form a → g ∈ form b → f * g ∈ form (a + b)
  /-- Forms only depend on the isomorphism class of the test object
  [katz1973, Section 1.1, condition 1]. -/
  apply_scale {k : ℤ} {f : LevelNTest L → L} (hf : f ∈ form k) {T : LevelNTest L}
    (hT : T.IsValid e ζ) (u : Lˣ) : f (T.scale u) = f T
  /-- The weight condition [katz1973, Section 1.1, condition 2]. -/
  apply_smulDiff {k : ℤ} {f : LevelNTest L → L} (hf : f ∈ form k) {T : LevelNTest L}
    (hT : T.IsValid e ζ) (c : Lˣ) : f (T.smulDiff c) = (c : L) ^ (-k) * f T
  /-- The `q`-expansion at the standard cusp, a power series in `q^{1/N}`: the value on the Tate
  curve `Tate(q)` over `L((q^{1/N}))` with level structure `(ζ, q^{1/N})` and `du / u`
  [katz1973, Section 1.2]. -/
  qExp (k : ℤ) : form k →ₗ[L] PowerSeries L
  /-- The `q`-expansion principle on the geometrically connected curve `M_N`: a form with zero
  `q`-expansion vanishes at every valid test object [katz1973, Theorem 1.6.1 and
  Corollary 1.6.2]. -/
  eq_of_qExp_eq {k : ℤ} (f g : form k) (h : qExp k f = qExp k g) {T : LevelNTest L}
    (hT : T.IsValid e ζ) : f.1 T = g.1 T
  /-- The `q`-expansion of a product. -/
  qExp_mul {a b : ℤ} (f : form a) (g : form b) :
    qExp (a + b) ⟨f.1 * g.1, mul_mem f.2 g.2⟩ = qExp a f * qExp b g
  /-- Galois equivariance: for `σ ∈ Aut(L)` fixing `ζ`, the conjugate of a form is a form whose
  `q`-expansion is the conjugate `q`-expansion (base change along `σ`)
  [katz1973, Section 1.1, condition 3, and Section 1.2]. -/
  galois_mem {k : ℤ} {f : LevelNTest L → L} (hf : f ∈ form k) (σ : L ≃+* L) (hσ : σ ζ = ζ) :
    (fun T ↦ σ (f (T.map σ.symm))) ∈ form k
  qExp_galois {k : ℤ} (f : form k) (σ : L ≃+* L) (hσ : σ ζ = ζ) :
    qExp k ⟨fun T ↦ σ (f.1 (T.map σ.symm)), galois_mem f.2 σ hσ⟩ =
      PowerSeries.map (σ : L →+* L) (qExp k f)
  /-- A classical form on `Γ(N)` whose `q`-expansion in `q^{1/N}` has integer coefficients is an
  algebraic form over `ℤ[ζ_N, 1/N]` [katz1973, Section 1.6, Corollary 1.6.2 and Theorem 1.7.1],
  whose base change to `L` has the reduced `q`-expansion. -/
  algebraize {k : ℤ} (f : ModularForm (Gamma N) k) (G : PowerSeries ℤ)
    (hfG : PowerSeries.map (Int.castRingHom ℂ) G = UpperHalfPlane.qExpansion N f) : form k
  qExp_algebraize {k : ℤ} (f : ModularForm (Gamma N) k) (G : PowerSeries ℤ)
    (hfG : PowerSeries.map (Int.castRingHom ℂ) G = UpperHalfPlane.qExpansion N f) :
    qExp k (algebraize f G hfG) = PowerSeries.map (Int.castRingHom L) G
  /-- The discriminant is a form of weight `12` with `q`-expansion `Δ(q)`, a series in
  `q = (q^{1/N})^N` [katz-mazur, Section 8.8]. -/
  discriminant_mem : LevelNTest.discriminantRule ∈ form 12
  qExp_discriminant :
    qExp 12 ⟨LevelNTest.discriminantRule, discriminant_mem⟩ =
      PowerSeries.mk fun n ↦ if N ∣ n then
        ((LevelOne.integralDiscriminant.coeff (n / N) : ℤ) : L) else 0
