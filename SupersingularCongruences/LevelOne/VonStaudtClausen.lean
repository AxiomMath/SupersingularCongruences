/-
Assembled by AxiomProver.
-/
module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import SupersingularCongruences.KatzForms.ReductionAlgebra

/-!
# The `q`-expansion of `E_{p-1}` modulo `p`

For a prime `p ≥ 5` the Eisenstein series `E_{p-1} = 1 - (2 (p - 1) / B_{p-1}) ∑ σ_{p-2}(n) qⁿ`
has a `p`-integral `q`-expansion congruent to `1` modulo `p`. This is a consequence of the theorem
of von Staudt–Clausen (Mathlib: `Bernoulli.padicValRat_bernoulli`, `Bernoulli.dvd_den_bernoulli`,
`Bernoulli.not_dvd_num_bernoulli`): `p` divides the denominator of `B_{p-1}` and not its
numerator, so `1 / B_{p-1}` is `p`-integral and divisible by `p` [swinnerton-dyer1973, Section 1]
(manuscript, Lemma 2.1(c)).

## Main results

* `Bernoulli.not_dvd_den_inv_bernoulli_sub_one`, `Bernoulli.dvd_num_inv_bernoulli_sub_one`;
* `LevelOne.eisensteinSeriesQExp p`: the rational `q`-expansion of `E_{p-1}`;
* `LevelOne.map_eisensteinSeriesQExp`: it is the `q`-expansion of `E_{p-1}`;
* `LevelOne.isPIntegral_eisensteinSeriesQExp`, `LevelOne.reduceTo_eisensteinSeriesQExp`: it is
  `p`-integral with reduction `1`.
-/

public section

open PowerSeries

namespace Bernoulli

variable {p : ℕ} [hp : Fact p.Prime]

lemma bernoulli_sub_one_eq (hp2 : p ≠ 2) :
    bernoulli (p - 1) = bernoulli (2 * ((p - 1) / 2)) := by
  rw [Nat.two_mul_div_two_of_even (hp.out.even_sub_one hp2)]

lemma pos_div_two_of_ne_two (hp2 : p ≠ 2) : 0 < (p - 1) / 2 := by
  have := hp.out.two_le
  have : 3 ≤ p := by omega
  omega

lemma sub_one_dvd_two_mul (hp2 : p ≠ 2) : p - 1 ∣ 2 * ((p - 1) / 2) := by
  rw [Nat.two_mul_div_two_of_even (hp.out.even_sub_one hp2)]

/-- **von Staudt–Clausen**: for an odd prime `p`, `1 / B_{p-1}` is `p`-integral. -/
lemma not_dvd_den_inv_bernoulli_sub_one (hp2 : p ≠ 2) : ¬ p ∣ ((bernoulli (p - 1))⁻¹).den := by
  rw [bernoulli_sub_one_eq hp2, Rat.den_inv]
  have hn := not_dvd_num_bernoulli (p := p) (pos_div_two_of_ne_two hp2) (sub_one_dvd_two_mul hp2)
  split_ifs with h
  · rw [h] at hn
    exact absurd (dvd_zero _) hn
  · rwa [← Int.natCast_dvd]

/-- **von Staudt–Clausen**: for an odd prime `p`, the numerator of `1 / B_{p-1}` is divisible by
`p`. -/
lemma dvd_num_inv_bernoulli_sub_one (hp2 : p ≠ 2) : (p : ℤ) ∣ ((bernoulli (p - 1))⁻¹).num := by
  rw [bernoulli_sub_one_eq hp2, Rat.num_inv]
  exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr
    (dvd_den_bernoulli (pos_div_two_of_ne_two hp2) (sub_one_dvd_two_mul hp2))) _

end Bernoulli

namespace LevelOne

/-- The rational `q`-expansion `1 - (2 (p - 1) / B_{p-1}) ∑ σ_{p-2}(n) qⁿ` of `E_{p-1}`. -/
noncomputable def eisensteinSeriesQExp (p : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n ↦ if n = 0 then 1 else
    (bernoulli (p - 1))⁻¹ * (-(2 * ((p - 1 : ℕ) : ℚ)) * (ArithmeticFunction.sigma (p - 1 - 1) n))

lemma coeff_eisensteinSeriesQExp (p n : ℕ) :
    (eisensteinSeriesQExp p).coeff n = if n = 0 then 1 else
      (bernoulli (p - 1))⁻¹ * (-(2 * ((p - 1 : ℕ) : ℚ)) *
        (ArithmeticFunction.sigma (p - 1 - 1) n)) := by
  simp [eisensteinSeriesQExp]

variable {p : ℕ} [hp : Fact p.Prime]

/-- The series `eisensteinSeriesQExp p` is the `q`-expansion of `E_{p-1}`. -/
theorem map_eisensteinSeriesQExp (hp2 : p ≠ 2) (hE : 3 ≤ p - 1) :
    PowerSeries.map (Rat.castHom ℂ) (eisensteinSeriesQExp p) =
      UpperHalfPlane.qExpansion 1 (ModularForm.E hE) := by
  ext n
  rw [coeff_map, EisensteinSeries.E_qExpansion_coeff hE (hp.out.even_sub_one hp2) n,
    coeff_eisensteinSeriesQExp]
  split_ifs
  · simp
  · simp only [eq_ratCast, Rat.cast_mul, Rat.cast_inv, Rat.cast_neg, Rat.cast_ofNat,
      Rat.cast_natCast]
    ring

/-- The `q`-expansion of `E_{p-1}` is `p`-integral (von Staudt–Clausen). -/
theorem isPIntegral_eisensteinSeriesQExp (hp2 : p ≠ 2) :
    (eisensteinSeriesQExp p).IsPIntegral p := by
  rw [isPIntegral_iff]
  intro n
  rw [coeff_eisensteinSeriesQExp]
  split_ifs
  · exact_mod_cast Rat.not_dvd_den_natCast (p := p) 1
  · refine Rat.not_dvd_den_mul (Bernoulli.not_dvd_den_inv_bernoulli_sub_one hp2) ?_
    refine Rat.not_dvd_den_mul ?_ (Rat.not_dvd_den_natCast _)
    exact_mod_cast Rat.not_dvd_den_intCast (p := p) (-(2 * ((p - 1 : ℕ) : ℤ)))

/-- The `q`-expansion of `E_{p-1}` is congruent to `1` modulo `p` (von Staudt–Clausen). -/
theorem reduceTo_eisensteinSeriesQExp (hp2 : p ≠ 2) (L : Type*) [Field L] [CharP L p] :
    (eisensteinSeriesQExp p).reduceTo L = 1 := by
  ext n
  rw [coeff_reduceTo, coeff_eisensteinSeriesQExp, coeff_one]
  split_ifs
  · simp
  · rw [Rat.cast_mul_of_not_dvd (Bernoulli.not_dvd_den_inv_bernoulli_sub_one hp2),
      Rat.cast_eq_zero_of_dvd_num (Bernoulli.dvd_num_inv_bernoulli_sub_one hp2), zero_mul]
    refine Rat.not_dvd_den_mul ?_ (Rat.not_dvd_den_natCast _)
    exact_mod_cast Rat.not_dvd_den_intCast (p := p) (-(2 * ((p - 1 : ℕ) : ℤ)))

end LevelOne
