/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.LevelTwo.Divisibility
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Algebra.Field.ZMod

/-!
# The examples `p = 11` and `p = 13` (Section 6 and Remark 4.1 of the manuscript)

Larson [larson2020, Section 5] computed, up to units, the level-two factorizations
`A₁₁ = δ (μ + 3ε) (μ + 4ε)` and `A₁₃ = (μ + 12ε) (μ² + 5με + ε²)` of the Hasse invariant.
For these explicit polynomials we verify the conclusion of Proposition 5.3:
`A^j ∣ L₂(Δ^t)` in `𝔽_p[δ, ε]` iff `j ≤ p^n`, where `t = i (p² - 1) / 12` with `i = r pⁿ`.
Their identification with the Hasse invariant on `Γ₀(2)` is proved for Katz forms in
`SupersingularCongruences.LevelTwo.LarsonExamples` (`KatzForms.hasse_eq_C_mul_hasseElevenLevelTwo`,
`KatzForms.hasse_eq_C_mul_hasseThirteenLevelTwo`). We also record the numerical facts of Section 6
and Remark 4.1.
-/

public section

open MvPolynomial

namespace LevelTwo

section ElevenFacts

/-- `64 ≡ 9 (mod 11)` and `9 ^ 5 = 1` in `𝔽₁₁`. -/
theorem sixtyFour_zmod_eleven : (64 : ZMod 11) = 9 ∧ (9 : ZMod 11) ^ 5 = 1 := by decide

/-- The supersingular `x`-values `-1, -3, -4` at `p = 11` satisfy `ξ ^ 10 = 1 = 64 ^ 10`
(Corollary 4.6 at `p = 11`). -/
theorem xValues_pow_ten_zmod_eleven :
    (-1 : ZMod 11) ^ 10 = 1 ∧ (-3 : ZMod 11) ^ 10 = 1 ∧ (-4 : ZMod 11) ^ 10 = 1 ∧
      (64 : ZMod 11) ^ 10 = 1 := by decide

/-- Remark 4.1: at `p = 11` one has `64⁻¹ = 5`, so the values `R₂ = x / 64` at the
supersingular points `x = -1, -3, -4` are `6, 7, 2`; each satisfies `R₂ ^ 10 = 1` but
`R₂ ^ 5 = -1` (so none is a `24`th power in `𝔽₁₂₁`). -/
theorem remark_sharp_zmod_eleven :
    (64 : ZMod 11) * 5 = 1 ∧ (5 : ZMod 11) * (-1) = 6 ∧ (5 : ZMod 11) * (-3) = 7 ∧
      (5 : ZMod 11) * (-4) = 2 ∧
      (6 : ZMod 11) ^ 10 = 1 ∧ (7 : ZMod 11) ^ 10 = 1 ∧ (2 : ZMod 11) ^ 10 = 1 ∧
      (6 : ZMod 11) ^ 5 = -1 ∧ (7 : ZMod 11) ^ 5 = -1 ∧ (2 : ZMod 11) ^ 5 = -1 := by decide

end ElevenFacts

section ThirteenFacts

/-- `64 ≡ -1 (mod 13)`, and `x² + 5x + 1` has no root in `𝔽₁₃`. -/
theorem zmod_thirteen_facts :
    (64 : ZMod 13) = -1 ∧ ∀ x : ZMod 13, x ^ 2 + 5 * x + 1 ≠ 0 := by decide

/-- Every root `α` of `x² + 5x + 1` in a field of characteristic `13` satisfies `α ^ 14 = 1`
(Section 6.2). -/
theorem pow_fourteen_eq_one_of_root {F : Type*} [Field F] [CharP F 13] {x : F}
    (hx : x ^ 2 + 5 * x + 1 = 0) : x ^ 14 = 1 := by
  have h13 : (13 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 13
  linear_combination (
    (153027601) + (-31938720) * x + (6665999) * x ^ 2 + (-1391275) * x ^ 3 + (290376) * x ^ 4 +
      (-60605) * x ^ 5 + (12649) * x ^ 6 + (-2640) * x ^ 7 + (551) * x ^ 8 + (-115) * x ^ 9 +
      (24) * x ^ 10 + (-5) * x ^ 11 + (1) * x ^ 12) * hx + (-56399945 * x - 11771354) * h13

end ThirteenFacts

section Eleven

instance fact_prime_eleven : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- Larson's level-two factorization of the Hasse invariant at `p = 11`, up to a unit
[larson2020, Section 5]: `δ (μ + 3ε) (μ + 4ε)`. -/
noncomputable def hasseElevenLevelTwo : MvPolynomial (Fin 2) (ZMod 11) :=
  delta (ZMod 11) * (mu (ZMod 11) + 3 * eps (ZMod 11)) * (mu (ZMod 11) + 4 * eps (ZMod 11))

/-- **Section 6.1**: for `i = r * 11 ^ n` with `11 ∤ r` and `t = 10 i`,
`A₁₁ ^ j ∣ L₂(Δ^t)` in `𝔽₁₁[δ, ε]` iff `j ≤ 11 ^ n`. -/
theorem hasseElevenLevelTwo_pow_dvd_larsonL2_iff {n r : ℕ} (hr : ¬ 11 ∣ r) (j : ℕ) :
    hasseElevenLevelTwo ^ j ∣ larsonL2 (ZMod 11) (11 ^ n * (10 * r)) ↔ j ≤ 11 ^ n := by
  have ht' : ¬ 11 ∣ 10 * r := by omega
  have h11 : (11 : AlgebraicClosure (ZMod 11)) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (AlgebraicClosure (ZMod 11)) 11
  have hcast : ∀ m : ℕ, ¬ 11 ∣ m → (m : AlgebraicClosure (ZMod 11)) ≠ 0 := fun m hm h =>
    hm ((CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod 11)) 11 m).mp h)
  have h64 : (64 : AlgebraicClosure (ZMod 11)) = 9 := by linear_combination 5 * h11
  have h9 : (9 : AlgebraicClosure (ZMod 11)) ^ 10 = 1 := by
    linear_combination 316980400 * h11
  let ξ : Fin 2 → AlgebraicClosure (ZMod 11) := ![-3, -4]
  have hξ0 : ξ 0 = -3 := rfl
  have hξ1 : ξ 1 = -4 := rfl
  refine pow_dvd_larsonL2_iff_of_map 11 (by norm_num) ht' (s := 2) (by norm_num) ξ ?_ ?_ ?_ ?_
    (α := 1) le_rfl ?_ one_ne_zero ?_ j
  · intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · exact absurd (hξ0.symm.trans (hxy.trans hξ1)) fun h =>
        hcast 1 (by norm_num) (by push_cast; linear_combination h)
    · exact absurd (hξ1.symm.trans (hxy.trans hξ0)) fun h =>
        hcast 1 (by norm_num) (by push_cast; linear_combination -h)
    · rfl
  · intro i
    fin_cases i
    · intro h
      exact hcast 3 (by norm_num) (by push_cast; linear_combination -(hξ0.symm.trans h))
    · intro h
      exact hcast 4 (by norm_num) (by push_cast; linear_combination -(hξ1.symm.trans h))
  · intro i
    fin_cases i
    · intro h
      exact hcast 2 (by norm_num) (by push_cast; linear_combination -(hξ0.symm.trans h))
    · intro h
      exact hcast 3 (by norm_num) (by push_cast; linear_combination -(hξ1.symm.trans h))
  · intro i
    rw [pow_mul, pow_mul, h64, h9, one_pow]
    fin_cases i
    · have : (-3 : AlgebraicClosure (ZMod 11)) ^ 10 = 1 := by linear_combination 5368 * h11
      rw [show ξ ((fun i => i) ⟨0, by norm_num⟩) = -3 from rfl, this, one_pow]
    · have : (-4 : AlgebraicClosure (ZMod 11)) ^ 10 = 1 := by linear_combination 95325 * h11
      rw [show ξ ((fun i => i) ⟨1, by norm_num⟩) = -4 from rfl, this, one_pow]
  · intro _
    rw [pow_mul, pow_mul, h64, h9]
    norm_num
  · simp only [hasseElevenLevelTwo, map_mul, map_add, map_delta, map_mu, map_eps, map_ofNat,
      Fin.prod_univ_two, hξ0, hξ1, map_neg, map_one, pow_one, one_mul]
    ring

end Eleven

section Thirteen

instance fact_prime_thirteen : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- Larson's level-two factorization of the Hasse invariant at `p = 13`, up to a unit
[larson2020, Section 5]: `(μ + 12ε) (μ² + 5με + ε²)`. -/
noncomputable def hasseThirteenLevelTwo : MvPolynomial (Fin 2) (ZMod 13) :=
  (mu (ZMod 13) + 12 * eps (ZMod 13)) *
    (mu (ZMod 13) ^ 2 + 5 * mu (ZMod 13) * eps (ZMod 13) + eps (ZMod 13) ^ 2)

/-- **Section 6.2**: for `i = r * 13 ^ n` with `13 ∤ r` and `t = 14 i`,
`A₁₃ ^ j ∣ L₂(Δ^t)` in `𝔽₁₃[δ, ε]` iff `j ≤ 13 ^ n`. -/
theorem hasseThirteenLevelTwo_pow_dvd_larsonL2_iff {n r : ℕ} (hr : ¬ 13 ∣ r) (j : ℕ) :
    hasseThirteenLevelTwo ^ j ∣ larsonL2 (ZMod 13) (13 ^ n * (14 * r)) ↔ j ≤ 13 ^ n := by
  have ht' : ¬ 13 ∣ 14 * r := by omega
  have h13 : (13 : AlgebraicClosure (ZMod 13)) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (AlgebraicClosure (ZMod 13)) 13
  have hcast : ∀ m : ℕ, ¬ 13 ∣ m → (m : AlgebraicClosure (ZMod 13)) ≠ 0 := fun m hm h =>
    hm ((CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod 13)) 13 m).mp h)
  -- the roots `a` and `b = -5 - a` of `x² + 5x + 1`, via `a = (s - 5) / 2 = 7 (s - 5)`, `s² = 21`
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (21 : AlgebraicClosure (ZMod 13)) two_pos
  obtain ⟨a, ha⟩ : ∃ a : AlgebraicClosure (ZMod 13), a = 7 * (s - 5) := ⟨_, rfl⟩
  have hroot : a ^ 2 + 5 * a + 1 = 0 := by
    rw [ha]; linear_combination 49 * hs + (160 - 35 * s) * h13
  obtain ⟨b, hb⟩ : ∃ b : AlgebraicClosure (ZMod 13), b = -5 - a := ⟨_, rfl⟩
  have hrootb : b ^ 2 + 5 * b + 1 = 0 := by rw [hb]; linear_combination hroot
  have hab : a * b = 1 := by rw [hb]; linear_combination -hroot
  have ha1 : a ≠ 1 := fun h => hcast 7 (by norm_num) (by
    push_cast; linear_combination hroot - (a + 6) * h)
  have hb1 : b ≠ 1 := fun h => hcast 7 (by norm_num) (by
    push_cast; linear_combination hrootb - (b + 6) * h)
  have hab' : a ≠ b := fun h => hcast 8 (by norm_num) (by
    push_cast; linear_combination (2 * a + 5) * h + (2 * a + 5) * hb - 4 * hroot - h13)
  have ha0 : a ≠ 0 := fun h => one_ne_zero (by linear_combination hroot - (a + 5) * h)
  have hb0 : b ≠ 0 := fun h => one_ne_zero (by linear_combination -hab + a * h)
  have ham1 : a ≠ -1 := fun h => hcast 3 (by norm_num) (by
    push_cast; linear_combination (a + 4) * h - hroot)
  have hbm1 : b ≠ -1 := fun h => hcast 3 (by norm_num) (by
    push_cast; linear_combination (b + 4) * h - hrootb)
  have h11 : (1 : AlgebraicClosure (ZMod 13)) ≠ -1 := fun h => hcast 2 (by norm_num) (by
    push_cast; linear_combination h)
  have h64 : (64 : AlgebraicClosure (ZMod 13)) ^ 14 = 1 := by
    have : (64 : AlgebraicClosure (ZMod 13)) = -1 := by linear_combination 5 * h13
    rw [this]; norm_num
  let ξ : Fin 3 → AlgebraicClosure (ZMod 13) := ![1, a, b]
  have hξ0 : ξ 0 = 1 := rfl
  have hξ1 : ξ 1 = a := rfl
  have hξ2 : ξ 2 = b := rfl
  refine pow_dvd_larsonL2_iff_of_map 13 (by norm_num) ht' (s := 3) (by norm_num) ξ ?_ ?_ ?_ ?_
    (α := 0) (by norm_num) (fun h => absurd h zero_ne_one) one_ne_zero ?_ j
  · intro x y hxy
    fin_cases x <;> fin_cases y
    all_goals first
      | rfl
      | exact absurd (hξ0.symm.trans (hxy.trans hξ1)) (Ne.symm ha1)
      | exact absurd (hξ0.symm.trans (hxy.trans hξ2)) (Ne.symm hb1)
      | exact absurd (hξ1.symm.trans (hxy.trans hξ0)) ha1
      | exact absurd (hξ2.symm.trans (hxy.trans hξ0)) hb1
      | exact absurd (hξ1.symm.trans (hxy.trans hξ2)) hab'
      | exact absurd (hξ2.symm.trans (hxy.trans hξ1)) (Ne.symm hab')
  · intro i
    fin_cases i
    · exact one_ne_zero
    · exact ha0
    · exact hb0
  · intro i
    fin_cases i
    · exact h11
    · exact ham1
    · exact hbm1
  · intro i
    rw [pow_mul, pow_mul, h64, one_pow]
    fin_cases i
    · rw [show ξ ((fun i => i) ⟨0, by norm_num⟩) = 1 from rfl, one_pow, one_pow]
    · rw [show ξ ((fun i => i) ⟨1, by norm_num⟩) = a from rfl,
        pow_fourteen_eq_one_of_root hroot, one_pow]
    · rw [show ξ ((fun i => i) ⟨2, by norm_num⟩) = b from rfl,
        pow_fourteen_eq_one_of_root hrootb, one_pow]
  · have hC13 : (13 : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod 13))) = 0 := by
      rw [← map_ofNat C 13, h13, map_zero]
    have hCab : C a * C b = (1 : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod 13))) := by
      rw [← map_mul, hab, map_one]
    have hCsum : C a + C b = (-5 : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod 13))) := by
      rw [← map_add, hb, add_sub_cancel, map_neg, map_ofNat]
    simp only [hasseThirteenLevelTwo, map_mul, map_add, map_pow, map_mu, map_eps, map_ofNat,
      Fin.prod_univ_three, hξ0, hξ1, hξ2, pow_zero, map_one, one_mul, mul_one]
    linear_combination (eps _ * (mu _ ^ 2 + 5 * mu _ * eps _ + eps _ ^ 2)) * hC13 +
      ((mu _ - eps _) * mu _ * eps _) * hCsum - ((mu _ - eps _) * eps _ ^ 2) * hCab

end Thirteen

end LevelTwo
