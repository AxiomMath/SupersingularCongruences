/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.EllipticCurve.OverClosure
public import SupersingularCongruences.EllipticCurve.PointMap
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.OrderOfElement
import all SupersingularCongruences.EllipticCurve.OverClosure

/-!
# The shadow of Lemma 4.2 on points

Lemma 4.2 of the manuscript says that a supersingular elliptic curve `E` over an algebraically
closed field `k` of characteristic `p` has a unique subgroup scheme of order `p`, the kernel of the
relative Frobenius `F : E → E^{(p)}`, and a unique connected subgroup scheme of order `p²`, the
kernel of `F^{(p)} ∘ F`. These subgroup schemes are infinitesimal (non-reduced, with a single
`k`-point), so the lemma is a statement about group schemes and is not stated here. This file
records its shadow on `k`-points, which is what is visible to the points-level API of
`Mathlib.AlgebraicGeometry.EllipticCurve`.

Let `L` be a field, `W` a Weierstrass curve over `L` and `W.IsSupersingularOver p` the condition
that `W` has no nonzero `p`-torsion `L`-point.

* `WeierstrassCurve.IsSupersingularOver.eq_zero_of_pow_smul_points`: `E(L)[p ^ k] = 0`.
* `WeierstrassCurve.IsSupersingularOver.eq_bot_of_card_eq_pow_points`: the only subgroup of
  `E(L)` of order `p ^ k` is trivial; `..._card_ne_prime_points` and `..._card_ne_sq_points`
  record the cases `k = 1, 2`: for `p ≠ 1` there is no subgroup of order `p` or `p ^ 2`.
  The subgroup schemes of Lemma 4.2 have trivial group of `L`-points.
* `WeierstrassCurve.Affine.Point.mapRingHom_frobenius_injective_points`,
  `..._ker_eq_bot_points`, `..._bijective_points`: for any Weierstrass curve over a field of
  characteristic `p`, the map `(x, y) ↦ (x ^ p, y ^ p)` from `E(L)` to `E^{(p)}(L)` (the relative
  Frobenius on `L`-points, `E^{(p)} = W.map (frobenius L p)`) is injective, so `(ker F)(L) = 0`;
  for `L` algebraically closed it is bijective.
* `WeierstrassCurve.Affine.Point.mapRingHom_frobenius_comp_injective_points`: the same for
  `F^{(p)} ∘ F : E(L) → E^{(p²)}(L)`, so `(ker (F^{(p)} ∘ F))(L) = 0`.
-/

public section

open WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {L : Type*} [Field L] [DecidableEq L] {p : ℕ} {W : WeierstrassCurve L}

/-- If `W` has no nonzero `p`-torsion `L`-point, it has no nonzero `p ^ k`-torsion `L`-point:
`E(L)[p ^ k] = 0`. -/
theorem IsSupersingularOver.eq_zero_of_pow_smul_points (hW : W.IsSupersingularOver p)
    {P : W.toAffine.Point} {k : ℕ} (hP : p ^ k • P = 0) : P = 0 := by
  have hW' : ∀ Q : W.toAffine.Point, p • Q = 0 → Q = 0 := hW
  induction k generalizing P with
  | zero => simpa using hP
  | succ k ih =>
    refine ih (hW' _ ?_)
    rwa [smul_smul, ← pow_succ']

/-- If `W` has no nonzero `p`-torsion `L`-point, every subgroup of `E(L)` of order `p ^ k` is
trivial. This is a statement about subgroups of `L`-points, not about subgroup schemes. -/
theorem IsSupersingularOver.eq_bot_of_card_eq_pow_points (hW : W.IsSupersingularOver p)
    (H : AddSubgroup W.toAffine.Point) {k : ℕ} (hH : Nat.card H = p ^ k) : H = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall H).2 fun x hx => hW.eq_zero_of_pow_smul_points (k := k) ?_
  have h : Nat.card H • (⟨x, hx⟩ : H) = 0 := card_nsmul_eq_zero'
  rw [hH] at h
  simpa using congrArg Subtype.val h

/-- If `W` has no nonzero `p`-torsion `L`-point, `E(L)` has no subgroup of order `p` for
`p ≠ 1`. -/
theorem IsSupersingularOver.card_ne_prime_points (hW : W.IsSupersingularOver p) (hp : p ≠ 1)
    (H : AddSubgroup W.toAffine.Point) : Nat.card H ≠ p := fun hH => by
  have hbot := hW.eq_bot_of_card_eq_pow_points H (k := 1) (by rw [hH, pow_one])
  subst hbot
  exact hp (by rw [← hH, AddSubgroup.card_bot])

/-- If `W` has no nonzero `p`-torsion `L`-point, `E(L)` has no subgroup of order `p ^ 2` for
`p ≠ 1`. -/
theorem IsSupersingularOver.card_ne_sq_points (hW : W.IsSupersingularOver p) (hp : p ≠ 1)
    (H : AddSubgroup W.toAffine.Point) : Nat.card H ≠ p ^ 2 := fun hH => by
  have hbot := hW.eq_bot_of_card_eq_pow_points H hH
  subst hbot
  rw [AddSubgroup.card_bot] at hH
  exact hp (by simpa using hH.symm)

end WeierstrassCurve

namespace WeierstrassCurve.Affine.Point

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K] {W : Affine F}

/-- For a surjective field homomorphism `σ`, the map `(x, y) ↦ (σ x, σ y)` on points is
surjective. -/
lemma mapRingHom_surjective {σ : F →+* K} (hσ : Function.Surjective σ) :
    Function.Surjective (mapRingHom (W := W) σ) := by
  rintro (_ | ⟨x', y', h'⟩)
  · refine ⟨0, ?_⟩
    exact _root_.map_zero (mapRingHom σ)
  · obtain ⟨x, rfl⟩ := hσ x'
    obtain ⟨y, rfl⟩ := hσ y'
    exact ⟨some x y ((map_nonsingular W σ.injective x y).mp h'), mapRingHom_some σ _⟩

variable {L : Type*} [Field L] [DecidableEq L] (p : ℕ) [ExpChar L p] (W : Affine L)

/-- The relative Frobenius `F : E → E^{(p)}`, `(x, y) ↦ (x ^ p, y ^ p)`, is injective on
`L`-points, where `E^{(p)} = W.map (frobenius L p)`. -/
theorem mapRingHom_frobenius_injective_points :
    Function.Injective (mapRingHom (W := W) (frobenius L p)) :=
  mapRingHom_injective _

/-- The kernel of the relative Frobenius `F : E → E^{(p)}` has trivial group of `L`-points. -/
theorem mapRingHom_frobenius_ker_eq_bot_points :
    (mapRingHom (W := W) (frobenius L p)).ker = ⊥ :=
  (AddMonoidHom.ker_eq_bot_iff _).2 (mapRingHom_frobenius_injective_points p W)

/-- The composite `F^{(p)} ∘ F : E → E^{(p)} → E^{(p²)}` of relative Frobenius maps is injective
on `L`-points, so `ker (F^{(p)} ∘ F)` has trivial group of `L`-points. -/
theorem mapRingHom_frobenius_comp_injective_points :
    Function.Injective ((mapRingHom (W := (W.map (frobenius L p)).toAffine) (frobenius L p)).comp
      (mapRingHom (W := W) (frobenius L p))) :=
  (mapRingHom_injective _).comp (mapRingHom_injective _)

/-- Over an algebraically closed field of characteristic `p`, the relative Frobenius
`F : E → E^{(p)}` is bijective on `L`-points. -/
theorem mapRingHom_frobenius_bijective_points [IsAlgClosed L] (hp : p.Prime) :
    Function.Bijective (mapRingHom (W := W) (frobenius L p)) := by
  refine ⟨mapRingHom_frobenius_injective_points p W, mapRingHom_surjective fun x => ?_⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq x hp.pos
  exact ⟨z, by rw [frobenius_def, hz]⟩

end WeierstrassCurve.Affine.Point
