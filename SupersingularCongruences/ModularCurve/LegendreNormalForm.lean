/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.ModularCurve.LevelTwoCoordinate
import all SupersingularCongruences.ModularCurve.Legendre
import all SupersingularCongruences.ModularCurve.Gamma0Pair

/-!
# Legendre normal form of pairs `(E, C)` with `C` of order `2`; Lemmas 3.2 and 3.3

Let `L` be an algebraically closed field with `2, 3 ≠ 0`. We represent the non-cuspidal points of
the modular curves concretely:

* `X₀(2)` minus its cusps: isomorphism classes of pairs `P = (E, C)` (`Gamma0.Pair 2 L`), two
  pairs being isomorphic iff `P.scale u = Q` for some `u ∈ Lˣ`;
* `X(2)` minus its cusps: the `λ`-line minus `{0, 1}`, with `π : X(2) → X₀(2)` given by
  `λ ↦ (E_λ, ⟨(0, 0)⟩)` (`Gamma0.legendrePair`).

## Main results

* `Gamma0.Pair.exists_scale_eq_legendrePair` (Legendre normal form): every pair is isomorphic to a
  Legendre pair. If `C = ⟨(e, 0)⟩` and `e₁, e₂` are the other roots of `x³ + a₄ x + a₆`, take
  `λ = (e₂ - e) / (e₁ - e)` and `u² = 1 / (e₁ - e)`.
* `Gamma0.exists_legendrePair_scale_eq_iff`: `(E_λ, ⟨(0,0)⟩) ≅ (E_λ', ⟨(0,0)⟩)` iff
  `λ' ∈ {λ, 1 / λ}`.
* Lemma 3.2 (`x = 64 R₂` is a bijection from the non-cuspidal points of `X₀(2)` onto
  `L \ {0}`; the cusps `∞` and `0` are `x = 0` and `x = ∞`):
  `Gamma0.Pair.xCoordinate_ne_zero`, `Gamma0.Pair.exists_xCoordinate_eq`,
  `Gamma0.Pair.xCoordinate_eq_iff`; and the elliptic point:
  `Gamma0.Pair.xCoordinate_eq_neg_one_iff` (`x(P) = -1` iff `P ≅ (E_{-1}, ⟨(0, 0)⟩)`,
  `E_{-1} : y² = x³ - x`, `j = 1728`: `Gamma0.j_legendrePair_neg_one`), with `⟨(0, 0)⟩` fixed
  by `[i]` (`Gamma0.legendrePair_neg_one_scale_eq_of_sq_eq_neg_one`).
* Lemma 3.3 (fibres of `π`): `Gamma0.exists_legendreFibre_eq` (the fibre over every non-cuspidal
  point is `{λ₀, 1 / λ₀}`) and `Gamma0.exists_legendreFibre_eq_singleton_iff` (it is a single
  point iff `x = -1`). The ramification statement in the coordinate `x` is
  `Gamma0.legendreFibrePolynomial_eq_sq_iff` (file `LevelTwoCoordinate`).
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace Gamma0

variable {L : Type*} [Field L] [DecidableEq L]

namespace Pair

/-- Two pairs `(E, ⟨(e, 0)⟩)` built on equal curves and equal points are equal. -/
lemma ofTwoTorsion_congr {W W' : WeierstrassCurve L} [W.IsElliptic] [W.IsShortNF]
    [W'.IsElliptic] [W'.IsShortNF] (hW : W = W') {e e' : L} (he : e = e')
    (h : W.toAffine.Nonsingular e 0) (h' : W'.toAffine.Nonsingular e' 0) :
    ofTwoTorsion W e h = ofTwoTorsion W' e' h' := by
  subst hW he
  rfl

/-- Every pair `(E, C)` with `C` of order `2` is `(E, ⟨(e, 0)⟩)` for a root `e` of
`x³ + a₄ x + a₆`. -/
theorem exists_eq_ofTwoTorsion (h2 : (2 : L) ≠ 0) (P : Pair 2 L) :
    ∃ e : L, ∃ he : P.curve.toAffine.Nonsingular e 0, P = ofTwoTorsion P.curve e he := by
  obtain ⟨e, he, hC⟩ := exists_subgroup_diff_zero_eq h2 P
  refine ⟨e, he, ?_⟩
  have hmem : Point.some e 0 he ∈ (P.subgroup : Set P.curve.toAffine.Point) \ {0} := by
    rw [hC]; rfl
  have hsub : P.subgroup = AddSubgroup.zmultiples (Point.some e 0 he) := by
    refine le_antisymm (fun R hR => ?_) (AddSubgroup.zmultiples_le.mpr hmem.1)
    by_cases hR0 : R = 0
    · rw [hR0]; exact zero_mem _
    · have : R ∈ (P.subgroup : Set P.curve.toAffine.Point) \ {0} := ⟨hR, hR0⟩
      rw [hC, Set.mem_singleton_iff] at this
      rw [this]; exact AddSubgroup.mem_zmultiples _
  cases P
  simp only at hsub
  unfold ofTwoTorsion
  congr

lemma scale_ofTwoTorsion (W : WeierstrassCurve L) [W.IsElliptic] [W.IsShortNF] {e : L}
    (he : W.toAffine.Nonsingular e 0) (u : Lˣ)
    (he' : (W.scaling u).toAffine.Nonsingular (u ^ 2 * e) 0) :
    (ofTwoTorsion W e he).scale u = ofTwoTorsion (W.scaling u) (u ^ 2 * e) he' := by
  have : Point.scaling W u (Point.some e 0 he) = Point.some (u ^ 2 * e) 0 he' := by
    rw [Point.scaling_some]
    simp only [mul_zero]
  simp only [scale, ofTwoTorsion]
  congr 1
  exact (AddMonoidHom.map_zmultiples (Point.scaling W u) _).trans (by rw [this])

/-- A scaling of a pair `(E, ⟨(e, 0)⟩)` equals a pair `(E', ⟨(e', 0)⟩)` as soon as the
coefficients and the points match. -/
lemma scale_ofTwoTorsion_eq (W : WeierstrassCurve L) [W.IsElliptic] [W.IsShortNF] {e : L}
    (he : W.toAffine.Nonsingular e 0) (u : Lˣ) (W' : WeierstrassCurve L) [W'.IsElliptic]
    [W'.IsShortNF] {e' : L} (he' : W'.toAffine.Nonsingular e' 0)
    (ha₄ : (u : L) ^ 4 * W.a₄ = W'.a₄) (ha₆ : (u : L) ^ 6 * W.a₆ = W'.a₆)
    (hpt : (u : L) ^ 2 * e = e') :
    (ofTwoTorsion W e he).scale u = ofTwoTorsion W' e' he' := by
  have hW : W.scaling u = W' := by
    ext
    · rw [scaling_a₁, a₁_of_isShortNF, a₁_of_isShortNF, mul_zero]
    · rw [scaling_a₂, a₂_of_isShortNF, a₂_of_isShortNF, mul_zero]
    · rw [scaling_a₃, a₃_of_isShortNF, a₃_of_isShortNF, mul_zero]
    · rw [scaling_a₄, ha₄]
    · rw [scaling_a₆, ha₆]
  have he'' : (W.scaling u).toAffine.Nonsingular (u ^ 2 * e) 0 := by
    have := (nonsingular_scaling_iff W u e 0).mpr he
    rwa [mul_zero] at this
  rw [scale_ofTwoTorsion W he u he'']
  exact ofTwoTorsion_congr hW hpt he'' he'

lemma scale_one (h2 : (2 : L) ≠ 0) (P : Pair 2 L) : P.scale 1 = P := by
  obtain ⟨e, he, hP⟩ := exists_eq_ofTwoTorsion h2 P
  rw [hP]
  exact scale_ofTwoTorsion_eq _ he 1 _ he (by simp) (by simp) (by simp)

lemma scale_scale (h2 : (2 : L) ≠ 0) (P : Pair 2 L) (u v : Lˣ) :
    (P.scale u).scale v = P.scale (u * v) := by
  obtain ⟨e, he, hP⟩ := exists_eq_ofTwoTorsion h2 P
  have he' : (P.curve.scaling u).toAffine.Nonsingular (u ^ 2 * e) 0 := by
    have := (nonsingular_scaling_iff P.curve u e 0).mpr he
    rwa [mul_zero] at this
  have he'' : ((P.curve.scaling u).scaling v).toAffine.Nonsingular (v ^ 2 * (u ^ 2 * e)) 0 := by
    have := (nonsingular_scaling_iff _ v _ 0).mpr he'
    rwa [mul_zero] at this
  rw [hP, scale_ofTwoTorsion _ he u he', scale_ofTwoTorsion _ he' v he'']
  symm
  refine scale_ofTwoTorsion_eq _ he _ _ he'' ?_ ?_ ?_
  · simp only [scaling_a₄, Units.val_mul]; ring
  · simp only [scaling_a₆, Units.val_mul]; ring
  · simp only [Units.val_mul]; ring

/-- Isomorphism of pairs is symmetric. -/
lemma scale_eq_symm (h2 : (2 : L) ≠ 0) {P Q : Pair 2 L} {u : Lˣ} (h : P.scale u = Q) :
    Q.scale u⁻¹ = P := by
  rw [← h, scale_scale h2, mul_inv_cancel, scale_one h2]

end Pair

section Legendre

variable (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0)

lemma legendrePair_eq_ofTwoTorsion {lam : L} (h0 : lam ≠ 0) (h1 : lam ≠ 1)
    [(legendreCurve lam).IsElliptic] :
    legendrePair h2 h3 h0 h1 =
      Pair.ofTwoTorsion (legendreCurve lam) _ (legendreCurve_nonsingular h2 h3 h0 h1) := (rfl)

/-- **Legendre normal form**: over an algebraically closed field (with `2, 3 ≠ 0`), every pair
`(E, C)` with `C` of order `2` is isomorphic to a Legendre pair `(E_λ, ⟨(0, 0)⟩)`, `λ ≠ 0, 1`. -/
theorem Pair.exists_scale_eq_legendrePair [IsAlgClosed L] (P : Pair 2 L) :
    ∃ (lam : L) (h0 : lam ≠ 0) (h1 : lam ≠ 1) (u : Lˣ), P.scale u = legendrePair h2 h3 h0 h1 := by
  obtain ⟨e, he, hP⟩ := Pair.exists_eq_ofTwoTorsion h2 P
  have hc := Pair.cubic_eq_zero_of_nonsingular _ he
  have ht := Pair.derivative_ne_zero_of_nonsingular _ he
  have hΔ := P.curve.isUnit_Δ.ne_zero
  rw [Pair.Δ_eq_of_nonsingular _ he] at hΔ
  have hD : 3 * e ^ 2 + 4 * P.curve.a₄ ≠ 0 := fun h => hΔ (by rw [h]; ring)
  -- the other two roots `e₁, e₂ = -e - e₁` of `x³ + a₄ x + a₆`
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (-3 * e ^ 2 - 4 * P.curve.a₄)
  set e₁ := (-e + s) / 2 with he₁
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hD (by linear_combination -hs)
  have ha₄ : P.curve.a₄ = -(e₁ ^ 2 + e * e₁ + e ^ 2) := by
    rw [he₁]; field_simp; linear_combination -hs
  have ha₆ : P.curve.a₆ = e * e₁ * (e + e₁) := by
    linear_combination hc - e * ha₄
  have hd₁ : e₁ - e ≠ 0 := by
    intro h
    apply ht
    rw [ha₄, show e₁ = e by linear_combination h]
    ring
  have hd₂ : -2 * e - e₁ ≠ 0 := by
    intro h
    apply ht
    rw [ha₄, show e₁ = -2 * e by linear_combination -h]
    ring
  have hd : -2 * e - e₁ ≠ e₁ - e := by
    intro h
    apply hs0
    have : (-2 * e - e₁) - (e₁ - e) = -s := by rw [he₁]; field_simp; ring
    rw [h, sub_self] at this
    linear_combination this
  set lam := (-2 * e - e₁) / (e₁ - e) with hlam
  have h0 : lam ≠ 0 := div_ne_zero hd₂ hd₁
  have h1 : lam ≠ 1 := fun h => hd ((div_eq_one_iff_eq hd₁).mp h)
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_eq_mul_self (e₁ - e)⁻¹
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact inv_ne_zero hd₁ (by rw [hv, mul_zero])
  refine ⟨lam, h0, h1, Units.mk0 v hv0, ?_⟩
  have hu2 : ((Units.mk0 v hv0 : Lˣ) : L) ^ 2 = (e₁ - e)⁻¹ := by
    rw [Units.val_mk0, hv, sq]
  have : (legendreCurve lam).IsElliptic := ⟨isUnit_legendreCurve_Δ h2 h3 h0 h1⟩
  rw [hP, legendrePair_eq_ofTwoTorsion]
  refine Pair.scale_ofTwoTorsion_eq _ he _ _ _ ?_ ?_ ?_
  · rw [show ((Units.mk0 v hv0 : Lˣ) : L) ^ 4 = (((Units.mk0 v hv0 : Lˣ) : L) ^ 2) ^ 2 by ring,
      hu2, ha₄, legendreCurve_a₄, hlam]
    field_simp
    ring
  · rw [show ((Units.mk0 v hv0 : Lˣ) : L) ^ 6 = (((Units.mk0 v hv0 : Lˣ) : L) ^ 2) ^ 3 by ring,
      hu2, ha₆, legendreCurve_a₆, hlam]
    have h27 : (27 : L) ≠ 0 := by
      rw [show (27 : L) = 3 ^ 3 by norm_num]; exact pow_ne_zero _ h3
    field_simp
    ring
  · rw [hu2, hlam]
    field_simp
    ring

/-- A scaling of a Legendre pair is a Legendre pair as soon as the coefficients and the
distinguished points match. -/
lemma legendrePair_scale_eq {lam lam' : L} (h0 : lam ≠ 0) (h1 : lam ≠ 1) (h0' : lam' ≠ 0)
    (h1' : lam' ≠ 1) (u : Lˣ)
    (ha₄ : (u : L) ^ 4 * (-(lam ^ 2 - lam + 1) / 3) = -(lam' ^ 2 - lam' + 1) / 3)
    (ha₆ : (u : L) ^ 6 * (-((lam - 2) * (lam + 1) * (2 * lam - 1)) / 27) =
      -((lam' - 2) * (lam' + 1) * (2 * lam' - 1)) / 27)
    (hpt : (u : L) ^ 2 * (-(1 + lam) / 3) = -(1 + lam') / 3) :
    (legendrePair h2 h3 h0 h1).scale u = legendrePair h2 h3 h0' h1' := by
  have : (legendreCurve lam).IsElliptic := ⟨isUnit_legendreCurve_Δ h2 h3 h0 h1⟩
  have : (legendreCurve lam').IsElliptic := ⟨isUnit_legendreCurve_Δ h2 h3 h0' h1'⟩
  rw [legendrePair_eq_ofTwoTorsion, legendrePair_eq_ofTwoTorsion]
  exact Pair.scale_ofTwoTorsion_eq _ _ _ _ _ ha₄ ha₆ hpt

/-- `λ ↦ 1 / λ` preserves the Legendre pair up to isomorphism (it exchanges `(1, 0)` and
`(λ, 0)`). -/
theorem exists_legendrePair_scale_eq_inv [IsAlgClosed L] {lam : L} (h0 : lam ≠ 0) (h1 : lam ≠ 1)
    (h0' : lam⁻¹ ≠ 0) (h1' : lam⁻¹ ≠ 1) :
    ∃ u : Lˣ, (legendrePair h2 h3 h0 h1).scale u = legendrePair h2 h3 h0' h1' := by
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_eq_mul_self lam⁻¹
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact h0' (by rw [hv, mul_zero])
  refine ⟨Units.mk0 v hv0, ?_⟩
  have hu2 : ((Units.mk0 v hv0 : Lˣ) : L) ^ 2 = lam⁻¹ := by
    rw [Units.val_mk0, hv, sq]
  have h27 : (27 : L) ≠ 0 := by
    rw [show (27 : L) = 3 ^ 3 by norm_num]; exact pow_ne_zero _ h3
  refine legendrePair_scale_eq h2 h3 h0 h1 h0' h1' _ ?_ ?_ ?_
  · rw [show ((Units.mk0 v hv0 : Lˣ) : L) ^ 4 = (((Units.mk0 v hv0 : Lˣ) : L) ^ 2) ^ 2 by ring,
      hu2]
    field_simp
    ring
  · rw [show ((Units.mk0 v hv0 : Lˣ) : L) ^ 6 = (((Units.mk0 v hv0 : Lˣ) : L) ^ 2) ^ 3 by ring,
      hu2]
    field_simp
    ring
  · rw [hu2]
    field_simp
    ring

/-- If two Legendre pairs are isomorphic then `λ' = λ` or `λ' = 1 / λ`. -/
theorem eq_or_eq_inv_of_legendrePair_scale_eq {lam lam' : L} (h0 : lam ≠ 0) (h1 : lam ≠ 1)
    (h0' : lam' ≠ 0) (h1' : lam' ≠ 1) {u : Lˣ}
    (h : (legendrePair h2 h3 h0 h1).scale u = legendrePair h2 h3 h0' h1') :
    lam' = lam ∨ lam' = lam⁻¹ := by
  have hx := congrArg Pair.xCoordinate h
  rw [Pair.xCoordinate_scale h2, xCoordinate_legendrePair, xCoordinate_legendrePair] at hx
  have h4 : (4 : L) ≠ 0 := by rw [show (4 : L) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  rw [div_eq_div_iff (mul_ne_zero h4 h0) (mul_ne_zero h4 h0')] at hx
  have : 4 * ((lam' - lam) * (lam * lam' - 1)) = 0 := by linear_combination -hx
  rcases mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h4) with h | h
  · exact Or.inl (by linear_combination h)
  · exact Or.inr (eq_inv_of_mul_eq_one_right (by linear_combination h))

/-- **Isomorphism classes of Legendre pairs** (the fibres of `X(2) → X₀(2)`, Lemma 3.3): the
Legendre pairs for `λ` and `λ'` are isomorphic iff `λ' = λ` or `λ' = 1 / λ`. -/
theorem exists_legendrePair_scale_eq_iff [IsAlgClosed L] {lam lam' : L} (h0 : lam ≠ 0)
    (h1 : lam ≠ 1) (h0' : lam' ≠ 0) (h1' : lam' ≠ 1) :
    (∃ u : Lˣ, (legendrePair h2 h3 h0 h1).scale u = legendrePair h2 h3 h0' h1') ↔
      lam' = lam ∨ lam' = lam⁻¹ := by
  refine ⟨fun ⟨u, h⟩ => eq_or_eq_inv_of_legendrePair_scale_eq h2 h3 h0 h1 h0' h1' h, ?_⟩
  rintro (rfl | rfl)
  · exact ⟨1, Pair.scale_one h2 _⟩
  · exact exists_legendrePair_scale_eq_inv h2 h3 h0 h1 h0' h1'

omit [DecidableEq L] in
lemma neg_one_ne_one_of_two_ne_zero (h2 : (2 : L) ≠ 0) : (-1 : L) ≠ 1 :=
  fun h => h2 (by linear_combination -h)

/-- `x(E_{-1}, ⟨(0, 0)⟩) = -1`. -/
lemma xCoordinate_legendrePair_neg_one :
    (legendrePair h2 h3 (neg_ne_zero.mpr one_ne_zero)
      (neg_one_ne_one_of_two_ne_zero h2)).xCoordinate = -1 := by
  rw [xCoordinate_legendrePair]
  have h4 : (4 : L) ≠ 0 := by rw [show (4 : L) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  field_simp
  ring

/-- `x(E_λ, ⟨(0, 0)⟩) = -1` iff `λ = -1`. -/
lemma xCoordinate_legendrePair_eq_neg_one_iff {lam : L} (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    (legendrePair h2 h3 h0 h1).xCoordinate = -1 ↔ lam = -1 := by
  rw [← sub_eq_zero, sub_neg_eq_add, xCoordinate_legendrePair_add_one, div_eq_zero_iff,
    pow_eq_zero_iff two_ne_zero]
  have h4 : (4 : L) ≠ 0 := by rw [show (4 : L) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  simp only [mul_eq_zero, h4, h0, or_self, or_false]
  exact ⟨fun h => by linear_combination h, fun h => by rw [h]; ring⟩

/-- The curve `E_{-1} : y² = x³ - x` has `j = 1728`. -/
lemma j_legendrePair_neg_one :
    (legendrePair h2 h3 (neg_ne_zero.mpr one_ne_zero) (neg_one_ne_one_of_two_ne_zero h2)).curve.j
      = 1728 := by
  rw [j_of_isShortNF, legendrePair_curve, legendreCurve_a₄, legendreCurve_a₆]
  have h27 : (27 : L) ≠ 0 := by
    rw [show (27 : L) = 3 ^ 3 by norm_num]; exact pow_ne_zero _ h3
  have h4 : (4 : L) ≠ 0 := by rw [show (4 : L) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have ha : -((-1 : L) ^ 2 - -1 + 1) / 3 = -1 := by field_simp; ring
  have hb : -(((-1 : L) - 2) * (-1 + 1) * (2 * -1 - 1)) / 27 = 0 := by ring
  have hc : 4 * (-1 : L) ^ 3 + 27 * 0 ^ 2 = -4 := by ring
  rw [ha, hb, hc, div_eq_iff (neg_ne_zero.mpr h4)]
  ring

/-- The automorphism `[i] (x, y) = (-x, i y)` of `E_{-1} : y² = x³ - x` (the scaling by `i`,
`i² = -1`) fixes the subgroup `⟨(0, 0)⟩`. -/
lemma legendrePair_neg_one_scale_eq_of_sq_eq_neg_one {i : Lˣ} (hi : (i : L) ^ 2 = -1) :
    (legendrePair h2 h3 (neg_ne_zero.mpr one_ne_zero) (neg_one_ne_one_of_two_ne_zero h2)).scale i =
      legendrePair h2 h3 (neg_ne_zero.mpr one_ne_zero) (neg_one_ne_one_of_two_ne_zero h2) := by
  refine legendrePair_scale_eq h2 h3 _ _ _ _ i ?_ ?_ ?_
  · rw [show (i : L) ^ 4 = ((i : L) ^ 2) ^ 2 by ring, hi]; ring
  · ring
  · ring

namespace Pair

/-- **Lemma 3.2** (surjectivity of `x` onto `L \ {0}`): over an algebraically closed field every
`ξ ≠ 0` is the coordinate `x(P)` of a pair (even of a Legendre pair). -/
theorem exists_xCoordinate_eq [IsAlgClosed L] {ξ : L} (hξ : ξ ≠ 0) :
    ∃ (lam : L) (h0 : lam ≠ 0) (h1 : lam ≠ 1), (legendrePair h2 h3 h0 h1).xCoordinate = ξ := by
  -- a root of `λ² - (2 + 4 ξ) λ + 1`
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self ((2 + 4 * ξ) ^ 2 - 4)
  have hroot : ((2 + 4 * ξ + s) / 2 - 1) ^ 2 - 4 * ξ * ((2 + 4 * ξ + s) / 2) = 0 := by
    field_simp
    linear_combination -hs
  have hprod : ((2 + 4 * ξ + s) / 2) * ((2 + 4 * ξ - s) / 2) = 1 := by
    field_simp
    linear_combination hs
  have h0 : (2 + 4 * ξ + s) / 2 ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have h1 : (2 + 4 * ξ + s) / 2 ≠ 1 := by
    intro h
    rw [h] at hroot
    have h4 : (4 : L) ≠ 0 := by rw [show (4 : L) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
    exact mul_ne_zero h4 hξ (by linear_combination -hroot)
  refine ⟨_, h0, h1, ?_⟩
  rw [← sub_eq_zero, xCoordinate_legendrePair_sub, eval_legendreFibrePolynomial, hroot,
    zero_div]

include h2 h3 in
/-- **Lemma 3.2** (injectivity of `x` on isomorphism classes): over an algebraically closed field,
two pairs have the same coordinate `x` iff they are isomorphic. -/
theorem xCoordinate_eq_iff [IsAlgClosed L] (P Q : Pair 2 L) :
    P.xCoordinate = Q.xCoordinate ↔ ∃ u : Lˣ, P.scale u = Q := by
  refine ⟨fun h => ?_, fun ⟨u, hu⟩ => by rw [← hu, xCoordinate_scale h2]⟩
  obtain ⟨lam, h0, h1, u, hu⟩ := exists_scale_eq_legendrePair h2 h3 P
  obtain ⟨mu, h0', h1', v, hv⟩ := exists_scale_eq_legendrePair h2 h3 Q
  have hx : (legendrePair h2 h3 h0 h1).xCoordinate = (legendrePair h2 h3 h0' h1').xCoordinate := by
    rw [← hu, ← hv, xCoordinate_scale h2, xCoordinate_scale h2, h]
  rw [xCoordinate_legendrePair, xCoordinate_legendrePair] at hx
  have h4 : (4 : L) ≠ 0 := by rw [show (4 : L) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  rw [div_eq_div_iff (mul_ne_zero h4 h0) (mul_ne_zero h4 h0')] at hx
  have hmu : mu = lam ∨ mu = lam⁻¹ := by
    have : 4 * ((mu - lam) * (lam * mu - 1)) = 0 := by linear_combination -hx
    rcases mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h4) with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (eq_inv_of_mul_eq_one_right (by linear_combination h))
  obtain ⟨w, hw⟩ := (exists_legendrePair_scale_eq_iff h2 h3 h0 h1 h0' h1').mpr hmu
  refine ⟨u * w * v⁻¹, ?_⟩
  rw [← scale_scale h2, ← scale_scale h2, hu, hw, scale_eq_symm h2 hv]

/-- **Lemma 3.2** (the elliptic point): `x(P) = -1` iff `P` is isomorphic to
`(E_{-1}, ⟨(0, 0)⟩)`, where `E_{-1} : y² = x³ - x` has `j = 1728`. -/
theorem xCoordinate_eq_neg_one_iff [IsAlgClosed L] (P : Pair 2 L) :
    P.xCoordinate = -1 ↔ ∃ u : Lˣ, P.scale u =
      legendrePair h2 h3 (neg_ne_zero.mpr one_ne_zero) (neg_one_ne_one_of_two_ne_zero h2) := by
  rw [← xCoordinate_eq_iff h2 h3, xCoordinate_legendrePair_neg_one]

end Pair

/-- The fibre of `X(2) → X₀(2)` over the point represented by `P`, as a set of Legendre
parameters: the `λ ≠ 0, 1` with `(E_λ, ⟨(0, 0)⟩) ≅ P`. -/
def legendreFibre (P : Pair 2 L) : Set L :=
  {lam | ∃ (h0 : lam ≠ 0) (h1 : lam ≠ 1), ∃ u : Lˣ, (legendrePair h2 h3 h0 h1).scale u = P}

/-- **Lemma 3.3** (fibres of `X(2) → X₀(2)`): over an algebraically closed field the fibre over
every non-cuspidal point of `X₀(2)` is `{λ₀, 1 / λ₀}` for some `λ₀ ≠ 0, 1`. -/
theorem exists_legendreFibre_eq [IsAlgClosed L] (P : Pair 2 L) :
    ∃ lam₀ : L, lam₀ ≠ 0 ∧ lam₀ ≠ 1 ∧ legendreFibre h2 h3 P = {lam₀, lam₀⁻¹} := by
  obtain ⟨lam, h0, h1, u, hu⟩ := Pair.exists_scale_eq_legendrePair h2 h3 P
  have hP := Pair.scale_eq_symm h2 hu
  refine ⟨lam, h0, h1, ?_⟩
  ext mu
  simp only [legendreFibre, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h0', h1', v, hv⟩
    refine eq_or_eq_inv_of_legendrePair_scale_eq h2 h3 h0 h1 h0' h1' (u := u⁻¹ * v⁻¹) ?_
    rw [← Pair.scale_scale h2, hP, Pair.scale_eq_symm h2 hv]
  · intro hmu
    have h0' : mu ≠ 0 := by
      rcases hmu with rfl | rfl
      · exact h0
      · exact inv_ne_zero h0
    have h1' : mu ≠ 1 := by
      rcases hmu with rfl | rfl
      · exact h1
      · exact fun h => h1 (inv_eq_one.mp h)
    obtain ⟨w, hw⟩ := (exists_legendrePair_scale_eq_iff h2 h3 h0' h1' h0 h1).mpr (by
      rcases hmu with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (inv_inv lam).symm)
    exact ⟨h0', h1', w * u⁻¹, by rw [← Pair.scale_scale h2, hw, hP]⟩

/-- **Lemma 3.3** (the ramified fibre): the fibre over `P` is a single point iff `x(P) = -1`,
i.e. iff `P ≅ (E_{-1}, ⟨(0, 0)⟩)` (`j = 1728`, `C` fixed by `[i]`); the point is then `λ = -1`.
Over every other non-cuspidal point the fibre `{λ₀, 1 / λ₀}` consists of two distinct points. -/
theorem exists_legendreFibre_eq_singleton_iff [IsAlgClosed L] (P : Pair 2 L) :
    (∃ lam₀ : L, legendreFibre h2 h3 P = {lam₀}) ↔ P.xCoordinate = -1 := by
  obtain ⟨lam, h0, h1, hF⟩ := exists_legendreFibre_eq h2 h3 P
  have hmem : lam ∈ legendreFibre h2 h3 P := by rw [hF]; exact Set.mem_insert _ _
  obtain ⟨h0', h1', u, hu⟩ := hmem
  have hx : P.xCoordinate = (legendrePair h2 h3 h0' h1').xCoordinate := by
    rw [← hu, Pair.xCoordinate_scale h2]
  rw [hx, xCoordinate_legendrePair_eq_neg_one_iff, hF]
  constructor
  · rintro ⟨mu, hmu⟩
    have ha : lam = mu := by
      have : lam ∈ ({lam, lam⁻¹} : Set L) := Set.mem_insert _ _
      rwa [hmu] at this
    have hb : lam⁻¹ = mu := by
      have : lam⁻¹ ∈ ({lam, lam⁻¹} : Set L) := Set.mem_insert_of_mem _ rfl
      rwa [hmu] at this
    have hsq : (lam - 1) * (lam + 1) = 0 := by
      have : lam * lam⁻¹ = 1 := mul_inv_cancel₀ h0
      rw [hb, ← ha] at this
      linear_combination this
    rcases mul_eq_zero.mp hsq with h | h
    · exact absurd (by linear_combination h) h1
    · linear_combination h
  · rintro rfl
    exact ⟨-1, by rw [inv_neg, inv_one, Set.pair_eq_singleton]⟩

end Legendre

end Gamma0
