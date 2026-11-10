/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.ModularCurve.Legendre
import all SupersingularCongruences.ModularCurve.Legendre
import all SupersingularCongruences.ModularCurve.Gamma0Pair
import all SupersingularCongruences.Isogeny.Velu

/-!
# The coordinate `x = 64 R₂` on `X₀(2)`

Let `L` be a field with `2, 3 ≠ 0`. A pair `(E, C)` with `C` of order `2` (`Gamma0.Pair 2 L`) on a
short Weierstrass curve `E : y² = x³ + a₄ x + a₆` has `C = {0, (e, 0)}` with `e` a root of
`x³ + a₄ x + a₆`. Vélu's sums are `t = 3 e² + a₄` and `w = e t`, and the value of the coordinate
`x = 64 R₂ = μ / ε` of Lemma 3.2 of the manuscript at `(E, C)` is

`x(E, C) = 64 · 2⁻¹² Δ(E / C) / Δ(E) = -(3 e² + 4 a₄) / (4 (3 e² + a₄))`.

On the Legendre pair `(E_λ, ⟨(0, 0)⟩)` this is `(λ - 1)² / (4 λ)`, and `x + 1 = (λ + 1)² / (4 λ)`.

## Main definitions and results

* `Gamma0.Pair.xCoordinate`: `x(P) = 64 R₂(P)`.
* `Gamma0.Pair.exists_subgroup_diff_zero_eq`: the nonzero point of `C` is `(e, 0)`.
* `Gamma0.Pair.xCoordinate_eq_of_mem`: the closed formula for `x` above.
* `Gamma0.Pair.xCoordinate_scale`, `Gamma0.Pair.veluRatio_scale_two`: `x` and `R₂` are invariants
  of isomorphism classes of pairs.
* `Gamma0.Pair.xCoordinate_ne_zero`: `x` does not vanish at non-cuspidal points.
* `Gamma0.xCoordinate_legendrePair`: `x(E_λ, ⟨(0, 0)⟩) = (λ - 1)² / (4 λ)`.
* `Gamma0.legendreFibrePolynomial_eq_sq_iff`: ramification of `λ ↦ x(λ)` (Lemma 3.3): for
  `ξ ≠ 0`, `(λ - 1)² - 4 ξ λ` is a square of a linear polynomial iff `ξ = -1`.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

namespace Gamma0

variable {L : Type*} [Field L] [DecidableEq L]

namespace Pair

/-- The coordinate `x = 64 R₂ = μ / ε` on `X₀(2)` (Lemma 3.2 of the manuscript), evaluated at the
pair `P = (E, C)`: `x(P) = 64 · 2⁻¹² Δ(E / C) / Δ(E)`. -/
noncomputable def xCoordinate (P : Pair 2 L) : L :=
  64 * P.veluRatio

lemma xCoordinate_eq_mul_veluRatio (P : Pair 2 L) : P.xCoordinate = 64 * P.veluRatio := (rfl)

lemma xCoordinate_def (P : Pair 2 L) :
    P.xCoordinate = 64 * (((2 : L) ^ 12)⁻¹ * (P.curve.velu P.subgroup).Δ / P.curve.Δ) := by
  simp [xCoordinate, veluRatio]

private lemma scale_subgroup {ℓ : ℕ} (P : Pair ℓ L) (u : Lˣ) :
    (P.scale u).subgroup = P.subgroup.map (Point.scaling P.curve u) := (rfl)

/-- The nonzero point of a subgroup of order `2` of a short Weierstrass curve is of the form
`(e, 0)`. -/
lemma exists_subgroup_diff_zero_eq (h2 : (2 : L) ≠ 0) (P : Pair 2 L) :
    ∃ e : L, ∃ he : P.curve.toAffine.Nonsingular e 0,
      (P.subgroup : Set P.curve.toAffine.Point) \ {0} = {Point.some e 0 he} := by
  obtain ⟨⟨Q, hQ⟩, hQ0, huniq⟩ := (Nat.card_eq_two_iff' (0 : P.subgroup)).mp P.card_subgroup
  have h2Q : (2 : ℕ) • (⟨Q, hQ⟩ : P.subgroup) = 0 := by
    have := card_nsmul_eq_zero' (G := P.subgroup) (x := ⟨Q, hQ⟩)
    rwa [P.card_subgroup] at this
  have h2Q' : (2 : ℕ) • Q = 0 := congrArg Subtype.val h2Q
  rcases Q with _ | ⟨x, y, h⟩
  · exact absurd rfl hQ0
  have hy : y = 0 := by
    rw [two_nsmul, add_eq_zero_iff_eq_neg, Point.neg_some] at h2Q'
    simp only [Point.some.injEq, Affine.negY, a₁_of_isShortNF, a₃_of_isShortNF] at h2Q'
    have : (2 : L) * y = 0 := by linear_combination h2Q'.2
    exact (mul_eq_zero.mp this).resolve_left h2
  subst hy
  refine ⟨x, h, ?_⟩
  ext R
  simp only [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hR, hR0⟩
    have := huniq ⟨R, hR⟩ (fun h' => hR0 (congrArg Subtype.val h'))
    exact congrArg Subtype.val this
  · rintro rfl
    exact ⟨hQ, Point.some_ne_zero h⟩

lemma veluT_eq_of_diff_zero_eq (W : WeierstrassCurve L) (C : AddSubgroup W.toAffine.Point) {e : L}
    (he : W.toAffine.Nonsingular e 0)
    (hC : (C : Set W.toAffine.Point) \ {0} = {Point.some e 0 he}) :
    W.veluT C = 3 * e ^ 2 + W.a₄ := by
  rw [veluT, hC, finsum_mem_singleton, Point.xCoord_some]

lemma veluW_eq_of_diff_zero_eq (W : WeierstrassCurve L) (C : AddSubgroup W.toAffine.Point) {e : L}
    (he : W.toAffine.Nonsingular e 0)
    (hC : (C : Set W.toAffine.Point) \ {0} = {Point.some e 0 he}) :
    W.veluW C = 5 * e ^ 3 + 3 * W.a₄ * e + 2 * W.a₆ := by
  rw [veluW, hC, finsum_mem_singleton, Point.xCoord_some]

omit [DecidableEq L] in
/-- A point `(e, 0)` of a short Weierstrass curve: `e` is a root of `x³ + a₄ x + a₆`. -/
lemma cubic_eq_zero_of_nonsingular (W : WeierstrassCurve L) [W.IsShortNF] {e : L}
    (he : W.toAffine.Nonsingular e 0) : e ^ 3 + W.a₄ * e + W.a₆ = 0 := by
  have := he.1
  rw [Affine.equation_iff] at this
  simp only [a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF] at this
  linear_combination -this

omit [DecidableEq L] in
/-- A point `(e, 0)` of a short Weierstrass curve: `e` is a simple root of `x³ + a₄ x + a₆`. -/
lemma derivative_ne_zero_of_nonsingular (W : WeierstrassCurve L) [W.IsShortNF] {e : L}
    (he : W.toAffine.Nonsingular e 0) : 3 * e ^ 2 + W.a₄ ≠ 0 := by
  have := ((Affine.nonsingular_iff e 0).mp he).2
  simp only [a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF] at this
  rcases this with h | h
  · intro h'
    exact h (by linear_combination -h')
  · exact absurd (by ring) h

omit [DecidableEq L] in
/-- The discriminant of a short Weierstrass curve with a point `(e, 0)`:
`Δ = 16 t² (-(3 e² + 4 a₄))`, `t = 3 e² + a₄`. -/
lemma Δ_eq_of_nonsingular (W : WeierstrassCurve L) [W.IsShortNF] {e : L}
    (he : W.toAffine.Nonsingular e 0) :
    W.Δ = -16 * (3 * e ^ 2 + W.a₄) ^ 2 * (3 * e ^ 2 + 4 * W.a₄) := by
  have hc := cubic_eq_zero_of_nonsingular W he
  rw [Δ_of_isShortNF]
  linear_combination (-16 * 27) * (W.a₆ - e ^ 3 - W.a₄ * e) * hc

/-- **The coordinate `x` at a pair** `(E, ⟨(e, 0)⟩)`:
`x = -(3 e² + 4 a₄) / (4 (3 e² + a₄))`. -/
lemma xCoordinate_eq_of_mem (h2 : (2 : L) ≠ 0) (P : Pair 2 L) {Q : P.curve.toAffine.Point}
    (hQ : Q ∈ P.subgroup) (hQ0 : Q ≠ 0) :
    P.xCoordinate =
      -(3 * Q.xCoord ^ 2 + 4 * P.curve.a₄) / (4 * (3 * Q.xCoord ^ 2 + P.curve.a₄)) := by
  obtain ⟨e, he, hC⟩ := exists_subgroup_diff_zero_eq h2 P
  have hQe : Q = Point.some e 0 he := by
    have : Q ∈ (P.subgroup : Set P.curve.toAffine.Point) \ {0} := ⟨hQ, hQ0⟩
    rwa [hC] at this
  subst hQe
  rw [Point.xCoord_some, xCoordinate_def, Δ_of_isShortNF (P.curve.velu P.subgroup), velu_a₄,
    velu_a₆, veluT_eq_of_diff_zero_eq _ _ he hC, veluW_eq_of_diff_zero_eq _ _ he hC]
  have hΔ := P.curve.isUnit_Δ.ne_zero
  rw [Δ_eq_of_nonsingular _ he] at hΔ ⊢
  have ht := derivative_ne_zero_of_nonsingular _ he
  have hD : 3 * e ^ 2 + 4 * P.curve.a₄ ≠ 0 := fun h => hΔ (by rw [h]; ring)
  have ha6 : P.curve.a₆ = -e ^ 3 - P.curve.a₄ * e := by
    linear_combination cubic_eq_zero_of_nonsingular _ he
  rw [ha6]
  have h4 : (4 : L) ≠ 0 := by rw [show (4 : L) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have h16 : (16 : L) ≠ 0 := by rw [show (16 : L) = 4 * 4 by norm_num]; exact mul_ne_zero h4 h4
  have h64 : (64 : L) ≠ 0 := by rw [show (64 : L) = 16 * 4 by norm_num]; exact mul_ne_zero h16 h4
  field_simp
  ring

lemma xCoord_scaling (W : WeierstrassCurve L) (u : Lˣ) (Q : W.toAffine.Point) :
    (Point.scaling W u Q).xCoord = u ^ 2 * Q.xCoord := by
  rcases Q with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, Point.scaling_zero, Point.xCoord_zero, Point.xCoord_zero, mul_zero]
  · rw [Point.scaling_some, Point.xCoord_some, Point.xCoord_some]

/-- `x` is an invariant of the isomorphism class of a pair. -/
lemma xCoordinate_scale (h2 : (2 : L) ≠ 0) (P : Pair 2 L) (u : Lˣ) :
    (P.scale u).xCoordinate = P.xCoordinate := by
  obtain ⟨e, he, hC⟩ := exists_subgroup_diff_zero_eq h2 P
  have hmem : Point.some e 0 he ∈ (P.subgroup : Set P.curve.toAffine.Point) \ {0} := by
    rw [hC]; rfl
  have hmem' : Point.scaling P.curve u (Point.some e 0 he) ∈ (P.scale u).subgroup :=
    AddSubgroup.mem_map_of_mem _ hmem.1
  have hne : Point.scaling P.curve u (Point.some e 0 he) ≠ 0 := by
    rw [← Point.scaling_zero P.curve u]
    exact fun h => hmem.2 (Point.scaling_injective P.curve u h)
  have hx : (show (P.scale u).curve.toAffine.Point from
      Point.scaling P.curve u (Point.some e 0 he)).xCoord = u ^ 2 * e :=
    (xCoord_scaling P.curve u _).trans (by rw [Point.xCoord_some])
  have ha : (P.scale u).curve.a₄ = u ^ 4 * P.curve.a₄ := scaling_a₄ _ _
  rw [xCoordinate_eq_of_mem h2 _ hmem' hne, xCoordinate_eq_of_mem h2 _ hmem.1 hmem.2, hx, ha,
    Point.xCoord_some]
  have hu : (u : L) ≠ 0 := u.ne_zero
  have ht := derivative_ne_zero_of_nonsingular _ he
  rw [div_eq_div_iff (by
      have : 4 * (3 * ((u : L) ^ 2 * e) ^ 2 + u ^ 4 * P.curve.a₄) =
        4 * u ^ 4 * (3 * e ^ 2 + P.curve.a₄) := by ring
      rw [this]
      exact mul_ne_zero (mul_ne_zero (by
        rw [show (4 : L) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2) (pow_ne_zero _ hu)) ht)
    (mul_ne_zero (by rw [show (4 : L) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2) ht)]
  ring

/-- For `ℓ = 2`, `R₂ = ℓ⁻¹² Δ(E / C) / Δ(E)` is an invariant of the isomorphism class of a pair. -/
lemma veluRatio_scale_two (h2 : (2 : L) ≠ 0) (P : Pair 2 L) (u : Lˣ) :
    (P.scale u).veluRatio = P.veluRatio := by
  have h := xCoordinate_scale h2 P u
  rw [xCoordinate_eq_mul_veluRatio, xCoordinate_eq_mul_veluRatio] at h
  have h64 : (64 : L) ≠ 0 := by
    rw [show (64 : L) = 2 ^ 6 by norm_num]; exact pow_ne_zero _ h2
  exact mul_left_cancel₀ h64 h

/-- `x` does not vanish at non-cuspidal points (the zero of `x` is the cusp `∞`). -/
lemma xCoordinate_ne_zero (h2 : (2 : L) ≠ 0) (P : Pair 2 L) : P.xCoordinate ≠ 0 := by
  obtain ⟨e, he, hC⟩ := exists_subgroup_diff_zero_eq h2 P
  have hmem : Point.some e 0 he ∈ (P.subgroup : Set P.curve.toAffine.Point) \ {0} := by
    rw [hC]; rfl
  rw [xCoordinate_eq_of_mem h2 _ hmem.1 hmem.2, Point.xCoord_some]
  have hΔ := P.curve.isUnit_Δ.ne_zero
  rw [Δ_eq_of_nonsingular _ he] at hΔ
  have hD : 3 * e ^ 2 + 4 * P.curve.a₄ ≠ 0 := fun h => hΔ (by rw [h]; ring)
  have ht := derivative_ne_zero_of_nonsingular _ he
  have h4 : (4 : L) ≠ 0 := by rw [show (4 : L) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  exact div_ne_zero (neg_ne_zero.mpr hD) (mul_ne_zero h4 ht)

end Pair

section FibrePolynomial

omit [DecidableEq L]

/-- The numerator `(λ - 1)² - 4 ξ λ` of `x(E_λ, ⟨(0, 0)⟩) - ξ` as a polynomial in `λ`. -/
noncomputable def legendreFibrePolynomial (ξ : L) : L[X] :=
  (X - 1) ^ 2 - C (4 * ξ) * X

lemma eval_legendreFibrePolynomial (ξ lam : L) :
    (legendreFibrePolynomial ξ).eval lam = (lam - 1) ^ 2 - 4 * ξ * lam := by
  simp [legendreFibrePolynomial]

/-- Over the elliptic point `x = -1` the fibre polynomial is `(λ + 1)²`. -/
lemma legendreFibrePolynomial_neg_one : legendreFibrePolynomial (-1 : L) = (X - C (-1)) ^ 2 := by
  simp only [legendreFibrePolynomial, map_neg, C_1, map_mul]
  ring_nf
  simp only [map_ofNat]
  ring

/-- **Ramification of `λ ↦ x(λ)`** (Lemma 3.3 of the manuscript): for `ξ ≠ 0` (a non-cuspidal
value), `x(λ) - ξ` has a double zero in `λ` iff `ξ = -1`, in which case the zero is `λ = -1`. -/
theorem legendreFibrePolynomial_eq_sq_iff (h2 : (2 : L) ≠ 0) {ξ : L} (hξ : ξ ≠ 0) :
    (∃ μ : L, legendreFibrePolynomial ξ = (X - C μ) ^ 2) ↔ ξ = -1 := by
  constructor
  · rintro ⟨μ, hμ⟩
    have e0 := congrArg (eval 0) hμ
    have e1 := congrArg (eval 1) hμ
    simp only [eval_legendreFibrePolynomial, eval_pow, eval_sub, eval_X, eval_C] at e0 e1
    have hμ1 : μ = 1 + 2 * ξ := by
      have : (2 : L) * (μ - 1 - 2 * ξ) = 0 := by linear_combination e1 - e0
      linear_combination (mul_eq_zero.mp this).resolve_left h2
    subst hμ1
    have : (2 : L) * 2 * (ξ * (ξ + 1)) = 0 := by linear_combination -e0
    have h4 : (2 : L) * 2 ≠ 0 := mul_ne_zero h2 h2
    have := ((mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h4)).resolve_left hξ)
    linear_combination this
  · rintro rfl
    exact ⟨-1, legendreFibrePolynomial_neg_one⟩

/-- For `ξ ∉ {0, -1}` (over an algebraically closed field) `x(λ) - ξ` has two simple zeros
`μ ≠ ν` in `λ`, with `μ ν = 1` and `μ, ν ∉ {0, 1}`. -/
theorem exists_legendreFibrePolynomial_eq_mul [IsAlgClosed L] (h2 : (2 : L) ≠ 0) {ξ : L}
    (hξ0 : ξ ≠ 0) (hξ1 : ξ ≠ -1) :
    ∃ μ ν : L, μ ≠ ν ∧ μ * ν = 1 ∧ μ ≠ 0 ∧ μ ≠ 1 ∧ ν ≠ 0 ∧ ν ≠ 1 ∧
      legendreFibrePolynomial ξ = (X - C μ) * (X - C ν) := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (4 * ξ * (ξ + 1))
  have h4 : (2 : L) * 2 ≠ 0 := mul_ne_zero h2 h2
  have hs0 : s ≠ 0 := by
    rintro rfl
    have : (2 : L) * 2 * (ξ * (ξ + 1)) = 0 := by linear_combination hs
    rcases mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h4) with h | h
    · exact hξ0 h
    · exact hξ1 (by linear_combination h)
  have hne : 1 + 2 * ξ + s ≠ 1 + 2 * ξ - s := fun h => hs0 <| by
    have : (2 : L) * s = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left h2
  have hprod : (1 + 2 * ξ + s) * (1 + 2 * ξ - s) = 1 := by linear_combination hs
  refine ⟨1 + 2 * ξ + s, 1 + 2 * ξ - s, hne, hprod, left_ne_zero_of_mul_eq_one hprod,
    fun h => hne ?_, right_ne_zero_of_mul_eq_one hprod, fun h => hne ?_, ?_⟩
  · rw [h, one_mul] at hprod; rw [h, hprod]
  · rw [h, mul_one] at hprod; rw [h, hprod]
  · simp only [legendreFibrePolynomial]
    have : C s * C s = C (4 * ξ * (ξ + 1)) := by rw [hs, C_mul]
    simp only [map_mul, map_add, map_sub, map_one, map_ofNat] at this ⊢
    linear_combination this

@[simp] lemma legendreCurve_a₄ (lam : L) : (legendreCurve lam).a₄ = -(lam ^ 2 - lam + 1) / 3 :=
  (rfl)

@[simp] lemma legendreCurve_a₆ (lam : L) :
    (legendreCurve lam).a₆ = -((lam - 2) * (lam + 1) * (2 * lam - 1)) / 27 := (rfl)

end FibrePolynomial

section Legendre

variable (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) {lam : L} (h0 : lam ≠ 0) (h1 : lam ≠ 1)

include h2 h3 h0 h1 in
@[simp] lemma legendrePair_curve : (legendrePair h2 h3 h0 h1).curve = legendreCurve lam := (rfl)

private lemma legendrePair_subgroup :
    (legendrePair h2 h3 h0 h1).subgroup =
      AddSubgroup.zmultiples (Point.some _ _ (legendreCurve_nonsingular h2 h3 h0 h1)) := (rfl)

/-- **The coordinate `x` on the Legendre family**: `x(E_λ, ⟨(0, 0)⟩) = (λ - 1)² / (4 λ)`. -/
theorem xCoordinate_legendrePair :
    (legendrePair h2 h3 h0 h1).xCoordinate = (lam - 1) ^ 2 / (4 * lam) := by
  have h' : (legendrePair h2 h3 h0 h1).curve.toAffine.Nonsingular (-(1 + lam) / 3) 0 :=
    legendreCurve_nonsingular h2 h3 h0 h1
  have hmem : Point.some _ _ h' ∈
      (legendrePair h2 h3 h0 h1).subgroup := by
    rw [legendrePair_subgroup]; exact AddSubgroup.mem_zmultiples _
  rw [Pair.xCoordinate_eq_of_mem h2 _ hmem (Point.some_ne_zero _), Point.xCoord_some,
    legendrePair_curve, legendreCurve_a₄]
  have h4 : (4 : L) ≠ 0 := by rw [show (4 : L) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hden : 4 * (3 * (-(1 + lam) / 3) ^ 2 + -(lam ^ 2 - lam + 1) / 3) = 4 * lam := by
    field_simp; ring
  have hnum : -(3 * (-(1 + lam) / 3) ^ 2 + 4 * (-(lam ^ 2 - lam + 1) / 3)) = (lam - 1) ^ 2 := by
    field_simp; ring
  rw [hden, hnum]

/-- `x(E_λ, ⟨(0, 0)⟩) + 1 = (λ + 1)² / (4 λ)`. -/
theorem xCoordinate_legendrePair_add_one :
    (legendrePair h2 h3 h0 h1).xCoordinate + 1 = (lam + 1) ^ 2 / (4 * lam) := by
  rw [xCoordinate_legendrePair]
  have h4 : (4 : L) ≠ 0 := by rw [show (4 : L) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  field_simp
  ring

/-- `x(E_λ, ⟨(0, 0)⟩) - ξ = ((λ - 1)² - 4 ξ λ) / (4 λ)`. -/
theorem xCoordinate_legendrePair_sub (ξ : L) :
    (legendrePair h2 h3 h0 h1).xCoordinate - ξ =
      (legendreFibrePolynomial ξ).eval lam / (4 * lam) := by
  rw [xCoordinate_legendrePair]
  have h4 : (4 : L) ≠ 0 := by rw [show (4 : L) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  rw [eval_legendreFibrePolynomial]
  field_simp

end Legendre

end Gamma0
