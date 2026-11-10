/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.EllipticCurve.Scaling
public import SupersingularCongruences.Isogeny.Velu

/-!
# Points of `X₀(ℓ)` and test objects for modular forms on `Γ₀(ℓ)`

Let `L` be a field (in applications an algebraic closure of `𝔽_p`, `p ≥ 5`). A non-cuspidal
geometric point of the modular curve `X₀(ℓ)` is an isomorphism class of pairs `(E, C)` of an
elliptic curve over `L` and a subgroup `C ⊆ E(L)` of order `ℓ`. Since every elliptic curve over a
field of characteristic `≠ 2, 3` has a short Weierstrass model and every isomorphism between short
models is a scaling `(x, y) ↦ (u² x, u³ y)`, we represent pairs by short Weierstrass models
(`Gamma0.Pair`), and isomorphisms by scalings (`Gamma0.Pair.scale`).

A *test object* (`Gamma0.Test`) is a pair together with a nonzero invariant differential. Every
invariant differential on a short model `W` is `λ · ω_W` with `λ ∈ Lˣ` and `ω_W = dx / (2y)`; we
record the scalar `λ` (`Gamma0.Test.diff`). Under the scaling `ψ (x, y) = (u² x, u³ y)` from `W` to
`W.scaling u` one has `ψ^* ω_{W.scaling u} = u⁻¹ ω_W`, so `(W, C, λ ω_W)` is isomorphic to
`(W.scaling u, ψ C, (λ u) ω_{W.scaling u})`. A Katz modular form of weight `k` on `Γ₀(ℓ)` over
`L` [katz1973, Section 1.1] is in particular a function of test objects, invariant under these
isomorphisms and homogeneous of degree `-k` in `λ`; see `SupersingularCongruences.KatzForms`.

## Main definitions

* `Gamma0.Pair ℓ L`, `Gamma0.Test ℓ L`;
* `Gamma0.Pair.scale`, `Gamma0.Test.scale`: transport along the scaling by `u`;
* `Gamma0.Test.smulDiff`: multiplication of the differential by a scalar;
* `Gamma0.Pair.map`, `Gamma0.Test.map`: conjugation by a field automorphism of `L`;
* `Gamma0.Pair.veluRatio`: `ℓ⁻¹² Δ(E / C) / Δ(E)`, the value of `R_ℓ = V_ℓ(Δ) / Δ` at the point
  `(E, C)` (Lemma 4.1 of the manuscript; Vélu's model of `E / C` is normalized).
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace Gamma0

variable (ℓ : ℕ) (L : Type*) [Field L] [DecidableEq L]

/-- A pair `(E, C)`: a short Weierstrass elliptic curve `E` over `L` and a subgroup `C` of `E(L)`
of order `ℓ`. -/
structure Pair where
  /-- The short Weierstrass model of the elliptic curve. -/
  curve : WeierstrassCurve L
  [isElliptic : curve.IsElliptic]
  [isShortNF : curve.IsShortNF]
  /-- The subgroup `C ⊆ E(L)`. -/
  subgroup : AddSubgroup curve.toAffine.Point
  card_subgroup : Nat.card subgroup = ℓ

attribute [instance] Pair.isElliptic Pair.isShortNF

/-- A test object `(E, C, ω)` for modular forms on `Γ₀(ℓ)`: a pair `(E, C)` and the invariant
differential `ω = diff • (dx / (2y))`. -/
structure Test extends Pair ℓ L where
  /-- The scalar `λ` with `ω = λ · dx / (2y)`. -/
  diff : Lˣ

variable {ℓ L}

namespace Pair

/-- The pair `(W.scaling u, ψ C)` isomorphic to `(W, C)` via `ψ (x, y) = (u² x, u³ y)`. -/
noncomputable def scale (P : Pair ℓ L) (u : Lˣ) : Pair ℓ L where
  curve := P.curve.scaling u
  subgroup := P.subgroup.map (Point.scaling P.curve u)
  card_subgroup := (Nat.card_congr
      (AddSubgroup.equivMapOfInjective _ _ (Point.scaling_injective P.curve u)).toEquiv.symm).trans
    P.card_subgroup

/-- The value `R_ℓ(E, C) = ℓ⁻¹² Δ(E / C) / Δ(E)` of the modular function `R_ℓ = V_ℓ(Δ) / Δ` at the
point represented by `(E, C)`, computed with Vélu's normalized model of `E / C` (manuscript,
equation (4.1)). -/
noncomputable def veluRatio (P : Pair ℓ L) : L :=
  ((ℓ : L) ^ 12)⁻¹ * (P.curve.velu P.subgroup).Δ / P.curve.Δ

/-- The conjugate pair `(E^σ, σ C)` for a field automorphism `σ` of `L`. -/
noncomputable def map (P : Pair ℓ L) (σ : L ≃+* L) : Pair ℓ L where
  curve := P.curve.map (σ : L →+* L)
  isShortNF := ⟨by simp, by simp, by simp⟩
  subgroup := P.subgroup.map (Point.mapRingHom (σ : L →+* L))
  card_subgroup := (Nat.card_congr
      (AddSubgroup.equivMapOfInjective _ _ (Point.mapRingHom_injective _)).toEquiv.symm).trans
    P.card_subgroup

@[simp] lemma scale_curve (P : Pair ℓ L) (u : Lˣ) : (P.scale u).curve = P.curve.scaling u :=
  (rfl)

lemma veluRatio_def (P : Pair ℓ L) :
    P.veluRatio = ((ℓ : L) ^ 12)⁻¹ * (P.curve.velu P.subgroup).Δ / P.curve.Δ :=
  (rfl)

end Pair

namespace Test

/-- The test object `(W.scaling u, ψ C, (λ u) ω_{W.scaling u})`, isomorphic to `(W, C, λ ω_W)`. -/
noncomputable def scale (T : Test ℓ L) (u : Lˣ) : Test ℓ L where
  toPair := T.toPair.scale u
  diff := T.diff * u

/-- The test object `(E, C, c ω)`. -/
def smulDiff (T : Test ℓ L) (c : Lˣ) : Test ℓ L where
  toPair := T.toPair
  diff := c * T.diff

/-- The conjugate test object `(E^σ, σ C, σ ω)` for a field automorphism `σ` of `L`. -/
noncomputable def map (T : Test ℓ L) (σ : L ≃+* L) : Test ℓ L where
  toPair := T.toPair.map σ
  diff := Units.map (σ : L →* L) T.diff

end Test

end Gamma0
