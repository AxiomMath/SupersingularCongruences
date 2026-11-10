/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.LevelOne.IntegralQExpansion
public import SupersingularCongruences.Algebra.ExpandSeries
import all SupersingularCongruences.LevelOne.IntegralQExpansion

/-!
# The expansion of `R₂ = V₂(Δ) / Δ` (Lemma 3.2(a))

The `q`-expansion of `Δ` is `integralDiscriminant = q - 24 q² + 252 q³ + ⋯`
(`LevelOne.isIntegralQExpansion_discriminant`), and that of `V₂(Δ) = Δ(2τ)` is
`Gamma0.expandSeries 2 integralDiscriminant = Δ(q²)`. Since `Δ(q) = q · (unit)` in `ℤ⟦q⟧`, the
quotient `R₂ = Δ(q²) / Δ(q)` is a well-defined power series with integer coefficients, and the
manuscript's expansion `R₂ = q + 24 q² + 300 q³ + ⋯` is a finite computation from the first
coefficients of `Δ`.

## Main results

* `LevelOne.coeff_two_integralDiscriminant`, `LevelOne.coeff_three_integralDiscriminant`:
  `Δ = q - 24 q² + 252 q³ + ⋯`.
* `LevelOne.existsUnique_integralDiscriminant_mul_eq`: there is a unique `R ∈ ℤ⟦q⟧` with
  `Δ(q) · R = Δ(q²)`.
* `LevelOne.coeff_of_integralDiscriminant_mul_eq`: such an `R` is `q + 24 q² + 300 q³ + O(q⁴)`.
* `LevelOne.discriminantRatioSeries`, `LevelOne.trunc_discriminantRatioSeries`: the series
  `R₂ = Δ(q²) / Δ(q)` and **Lemma 3.2(a)**, `R₂ ≡ q + 24 q² + 300 q³ (mod q⁴)`.
-/

public section

open PowerSeries ArithmeticFunction Gamma0

namespace LevelOne

/-- The coefficient of `q²` in `Δ` is `-24`. -/
lemma coeff_two_integralDiscriminant : integralDiscriminant.coeff 2 = -24 := by
  have h := congrArg (coeff 2) integralDiscriminant_mul
  rw [coeff_ofNat_mul] at h
  have h' : (integralE₄ ^ 3 - integralE₆ ^ 2).coeff 2 = 1728 * (-24) := by
    simp only [pow_succ, pow_zero, one_mul, map_sub, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      Finset.sum_range_zero, integralE₄, integralE₆, coeff_mk]
    simp [sigma_apply]
    decide
  rw [h'] at h
  omega

/-- The coefficient of `q³` in `Δ` is `252`. -/
lemma coeff_three_integralDiscriminant : integralDiscriminant.coeff 3 = 252 := by
  have h := congrArg (coeff 3) integralDiscriminant_mul
  rw [coeff_ofNat_mul] at h
  have h' : (integralE₄ ^ 3 - integralE₆ ^ 2).coeff 3 = 1728 * 252 := by
    simp only [pow_succ, pow_zero, one_mul, map_sub, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      Finset.sum_range_zero, integralE₄, integralE₆, coeff_mk]
    simp [sigma_apply]
    decide
  rw [h'] at h
  omega

lemma integralDiscriminant_ne_zero : integralDiscriminant ≠ 0 := by
  intro h
  have := coeff_one_integralDiscriminant
  rw [h, _root_.map_zero] at this
  exact zero_ne_one this

/-- `R₂ = Δ(q²) / Δ(q)` is a well-defined integral power series: there is a unique `R ∈ ℤ⟦q⟧`
with `Δ(q) · R = Δ(q²)`. -/
theorem existsUnique_integralDiscriminant_mul_eq :
    ∃! R : PowerSeries ℤ, integralDiscriminant * R = expandSeries 2 integralDiscriminant := by
  obtain ⟨R, hR⟩ := integralDiscriminant_dvd (G := expandSeries 2 integralDiscriminant)
    (by rw [coeff_expandSeries]; simp [coeff_zero_integralDiscriminant])
  exact ⟨R, hR.symm, fun R' hR' ↦ mul_left_cancel₀ integralDiscriminant_ne_zero (hR'.trans hR)⟩

/-- The first coefficients of `Δ(q²) / Δ(q)`: any `R` with `Δ(q) · R = Δ(q²)` is
`q + 24 q² + 300 q³ + O(q⁴)`. -/
theorem coeff_of_integralDiscriminant_mul_eq {R : PowerSeries ℤ}
    (hR : integralDiscriminant * R = expandSeries 2 integralDiscriminant) :
    R.coeff 0 = 0 ∧ R.coeff 1 = 1 ∧ R.coeff 2 = 24 ∧ R.coeff 3 = 300 := by
  have e : ∀ n, (integralDiscriminant * R).coeff n =
      (expandSeries 2 integralDiscriminant).coeff n := fun n ↦ by rw [hR]
  have e1 := e 1
  have e2 := e 2
  have e3 := e 3
  have e4 := e 4
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, coeff_expandSeries, coeff_zero_integralDiscriminant,
    coeff_one_integralDiscriminant, coeff_two_integralDiscriminant,
    coeff_three_integralDiscriminant] at e1 e2 e3 e4
  norm_num [coeff_one_integralDiscriminant, coeff_two_integralDiscriminant] at e1 e2 e3 e4
  rw [e1] at e2 e3 e4
  simp only [mul_zero, add_zero] at e2 e3 e4
  exact ⟨by rw [coeff_zero_eq_constantCoeff_apply]; exact e1, by linarith, by linarith,
    by linarith⟩

/-- The series `R₂ = V₂(Δ) / Δ = Δ(q²) / Δ(q) ∈ ℤ⟦q⟧`, the unique `R` with `Δ(q) · R = Δ(q²)`. -/
noncomputable def discriminantRatioSeries : PowerSeries ℤ :=
  existsUnique_integralDiscriminant_mul_eq.exists.choose

lemma integralDiscriminant_mul_discriminantRatioSeries :
    integralDiscriminant * discriminantRatioSeries = expandSeries 2 integralDiscriminant :=
  existsUnique_integralDiscriminant_mul_eq.exists.choose_spec

/-- **Lemma 3.2(a)**, the expansion: `R₂ = V₂(Δ) / Δ = q + 24 q² + 300 q³ + ⋯`, i.e. the
truncation of `Δ(q²) / Δ(q)` below `q⁴` is `q + 24 q² + 300 q³`. -/
theorem trunc_discriminantRatioSeries :
    trunc 4 discriminantRatioSeries =
      (Polynomial.X + 24 * Polynomial.X ^ 2 + 300 * Polynomial.X ^ 3 : Polynomial ℤ) := by
  obtain ⟨h0, h1, h2, h3⟩ :=
    coeff_of_integralDiscriminant_mul_eq integralDiscriminant_mul_discriminantRatioSeries
  ext n
  rw [coeff_trunc]
  rcases n with _ | _ | _ | _ | n
  · simp [h0]
  · simp [h1]
  · simp [h2, Polynomial.coeff_X]
  · simp [h3, Polynomial.coeff_X]
  · split_ifs with h
    · omega
    · simp only [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_ofNat_mul,
        Polynomial.coeff_X_pow]
      split_ifs <;> omega

end LevelOne
