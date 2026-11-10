/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.External
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Larson's structure theorem for `M_*(Γ₀(2), ℤ[1/2])` (manuscript, eq. (3.1))

[larson2020, Proposition 3.2] (Larson cites Hirzebruch–Berger–Jung, *Manifolds and modular
forms*, Appendix I): there are forms
`δ ∈ M₂(Γ₀(2))[1/2]`, `ε ∈ M₄(Γ₀(2))[1/2]` with
`δ = 1/4 + 6q + 6q² + 24q³ + ⋯` and `ε = 1/16 - q + 7q² - 28q³ + ⋯` such that
`M_*(Γ₀(2))[1/2] = ℤ[1/2][δ, ε]`. The surjectivity half of this statement is the cited result
`LevelTwoForms.LarsonLevelTwoStructure` (`SupersingularCongruences.External`). This file deduces the
`p`-integral form used in the manuscript's eq. (3.1): a form `f` such that `d f` has
`ℤ[1/2]`-integral `q`-expansion for some integer `d` prime to an odd prime `p` is a polynomial in
`δ, ε` with `p`-integral rational coefficients
(`LevelTwoForms.exists_mvPolynomial_eq_of_pIntegral`).

## Normalization

Larson's `δ` and `ε` are specified by their `q`-expansions. Ours are `LevelTwoForms.delta`
(`(2 E₂(2τ) - E₂(τ)) / 4`) and `LevelTwoForms.eps` (`(16 V₂E₄ - E₄) / 240`, equal to the eta
quotient `η(τ)¹⁶ / (16 η(2τ)⁸)` of the manuscript by `LevelTwoForms.eps_apply_eq_etaQuotient`).
Their `q`-expansions begin `1/4 + 6q + 6q² + 24q³` and `1/16 - q + 7q² - 28q³`
(`LevelTwoForms.coeff_delta`, `LevelTwoForms.coeff_eps`), matching Larson's; since a form of weight
`2` (resp. `4`) on `Γ₀(2)` is determined by its first coefficient (resp. first two coefficients)
by the Sturm bound, these are Larson's forms. `ℤ[1/2]` is represented as the rationals `a / 2^m`.
-/

public section

open ModularForm UpperHalfPlane CongruenceSubgroup

namespace LevelTwoForms

/-- **Eq. (3.1) of the manuscript, `p`-integral form.** Let `p` be an odd prime and `d` an integer
with `p ∤ d`. If `f ∈ M_k(Γ₀(2))` and `d f` has `ℤ[1/2]`-integral `q`-expansion, then
`f = P(δ, ε)` with `P` weighted homogeneous of weight `k` with `p`-integral rational
coefficients. -/
theorem exists_mvPolynomial_eq_of_pIntegral (hLarsonLevelTwoStructure : LarsonLevelTwoStructure)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ}
    (f : ModularForm (Gamma0 2) k) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d)
    (hf : ∀ n, ∃ (a : ℤ) (m : ℕ), (d : ℂ) * (qExpansion 1 f).coeff n = (a : ℂ) / 2 ^ m) :
    ∃ P : MvPolynomial (Fin 2) ℚ, P.IsWeightedHomogeneous ![2, 4] k ∧
      (∀ e, ¬ p ∣ (P.coeff e).den) ∧
      ∀ τ : ℍ, f τ = MvPolynomial.aeval ![delta τ, eps τ] P := by
  have hd0 : d ≠ 0 := by rintro rfl; exact hd (dvd_zero _)
  have hqd : qExpansion 1 ((d : ℂ) • f : ModularForm (Gamma0 2) k) =
      (d : ℂ) • qExpansion 1 f := by
    rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma0 2)]
  obtain ⟨P₀, hP₀, hP₀int, hP₀f⟩ := hLarsonLevelTwoStructure ((d : ℂ) • f)
    (fun n => by rw [hqd, PowerSeries.coeff_smul, smul_eq_mul]; exact hf n)
  refine ⟨(d : ℚ)⁻¹ • P₀, ?_, ?_, ?_⟩
  · intro e he
    apply hP₀
    rw [MvPolynomial.coeff_smul, smul_eq_mul] at he
    exact right_ne_zero_of_mul he
  · intro e
    obtain ⟨a, m, ha⟩ := hP₀int e
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hcoeff : ((d : ℚ)⁻¹ • P₀).coeff e = Rat.divInt a (d * 2 ^ m) := by
      rw [MvPolynomial.coeff_smul, smul_eq_mul, ha, Rat.divInt_eq_div]
      push_cast
      field_simp
    rw [hcoeff]
    intro hpd
    have h1 : (p : ℤ) ∣ d * 2 ^ m :=
      (Int.natCast_dvd_natCast.mpr hpd).trans (Rat.den_dvd a (d * 2 ^ m))
    rcases hpZ.dvd_or_dvd h1 with h | h
    · exact hd h
    · have h2 : (p : ℤ) ∣ 2 := hpZ.dvd_of_dvd_pow h
      have h3 : p ∣ 2 := Int.natCast_dvd_natCast.mp h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  · intro τ
    have h := hP₀f τ
    rw [map_smul, Rat.smul_def, ← h]
    simp only [smul_apply, smul_eq_mul]
    push_cast
    field_simp

end LevelTwoForms
