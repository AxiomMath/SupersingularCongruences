/-
Assembled by AxiomProver.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Supersingular curves and Deuring models over finite fields

Let `K` be a field of characteristic `p` and `W` a Weierstrass curve over `K`.

* `WeierstrassCurve.IsSupersingular`: `W` has no nonzero `p`-torsion point over the algebraic
  closure of `K` (one of the equivalent characterisations of [silverman-aec, Theorem V.3.1]).
* `WeierstrassCurve.frobeniusPoint`: for finite `K`, the `#K`-power Frobenius endomorphism
  `π_E : (x, y) ↦ (x ^ #K, y ^ #K)` acting on the points of `W` over `AlgebraicClosure K`.
* `WeierstrassCurve.IsDeuringModel`: the condition `π_E = [-p]` of the manuscript (Section 1),
  i.e. `π_E(P) = -(p • P)` for every point `P` over the algebraic closure. (An endomorphism of an
  elliptic curve is determined by its action on points over the algebraic closure.)

The group law on points needs decidable equality of the base field; since `AlgebraicClosure K`
carries no such instance, the definitions below use classical decidability.
-/

public section

open WeierstrassCurve.Affine

open IntermediateField in
/-- Every element `x` of a field `L` algebraic over a finite field `K` of characteristic `p` lies in
a finite subfield, hence satisfies `x ^ (p ^ k) = x` for some `k ≥ 1`. (For `L` algebraically
closed this says that `L` is an algebraic closure of `𝔽_p`.) -/
theorem exists_pow_char_pow_eq_self_of_isAlgebraic {K L : Type*} [Field K] [Finite K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] (p : ℕ) [Fact p.Prime] [CharP L p] (x : L) :
    ∃ k, 0 < k ∧ x ^ p ^ k = x := by
  have : FiniteDimensional K K⟮x⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have : Finite K⟮x⟯ := Module.finite_of_finite K
  have : Fintype K⟮x⟯ := Fintype.ofFinite _
  have : CharP K⟮x⟯ p := (Algebra.charP_iff K⟮x⟯ L p).mpr inferInstance
  obtain ⟨n, hn, hcard⟩ := FiniteField.card K⟮x⟯ p
  refine ⟨n, n.pos, ?_⟩
  have h := FiniteField.pow_card (⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ : K⟮x⟯)
  rw [hcard] at h
  exact congrArg Subtype.val h

namespace WeierstrassCurve

variable {K : Type*} [Field K]

open scoped Classical in
/-- A Weierstrass curve over a field `K` of characteristic `p = ringChar K` is *supersingular* if
it has no nonzero `p`-torsion point over the algebraic closure of `K`
(cf. [silverman-aec, Theorem V.3.1]). -/
def IsSupersingular (W : WeierstrassCurve K) : Prop :=
  ∀ P : (W⁄(AlgebraicClosure K)).Point, ringChar K • P = 0 → P = 0

open scoped Classical in
lemma IsSupersingular.eq_zero {W : WeierstrassCurve K} (hW : W.IsSupersingular)
    {P : (W⁄(AlgebraicClosure K)).Point} (hP : ringChar K • P = 0) : P = 0 :=
  hW P hP

variable [Fintype K]

open scoped Classical in
/-- The `#K`-power Frobenius endomorphism `(x, y) ↦ (x ^ #K, y ^ #K)` of a Weierstrass curve over
a finite field `K`, acting on its points over `AlgebraicClosure K`. It is induced by the
`K`-algebra endomorphism `x ↦ x ^ #K` of `AlgebraicClosure K`. -/
noncomputable def frobeniusPoint (W : WeierstrassCurve K) :
    (W⁄(AlgebraicClosure K)).Point →+ (W⁄(AlgebraicClosure K)).Point :=
  Point.map (FiniteField.frobeniusAlgHom K (AlgebraicClosure K))

open scoped Classical in
lemma frobeniusPoint_some (W : WeierstrassCurve K) {x y : AlgebraicClosure K}
    (h : (W⁄(AlgebraicClosure K)).Nonsingular x y) :
    ∃ h' : (W⁄(AlgebraicClosure K)).Nonsingular (x ^ Fintype.card K) (y ^ Fintype.card K),
      W.frobeniusPoint (.some x y h) = .some _ _ h' :=
  ⟨_, Point.map_some _ h⟩

open scoped Classical in
/-- A Weierstrass curve over a finite field `K` of characteristic `p` is a *Deuring model* if its
`#K`-power Frobenius endomorphism equals `[-p]`, i.e. `π_E(P) = -(p • P)` for every point `P`
over `AlgebraicClosure K`. (The manuscript uses this for `#K = p ^ 2`.) -/
def IsDeuringModel (W : WeierstrassCurve K) : Prop :=
  ∀ P : (W⁄(AlgebraicClosure K)).Point, W.frobeniusPoint P = -(ringChar K • P)

open scoped Classical in
lemma IsDeuringModel.frobeniusPoint_eq {W : WeierstrassCurve K} (hW : W.IsDeuringModel)
    (P : (W⁄(AlgebraicClosure K)).Point) : W.frobeniusPoint P = -(ringChar K • P) :=
  hW P

end WeierstrassCurve
