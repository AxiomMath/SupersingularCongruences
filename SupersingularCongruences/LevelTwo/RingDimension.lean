/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.LevelTwo.HasseFactorization

/-!
# The elementary parts of Remark 5.2

Remark 5.2 of the manuscript compares the geometric ring of mod `p` modular forms on `Γ₀(ℓ)`
with reductions of classical forms. This file proves the two elementary inputs of the remark;
its level-2 comparison statements are in `SupersingularCongruences.LevelTwo.RingComparison`. Its
cohomological content (Kodaira–Spencer, vanishing of `H¹`, cohomology and base change on the
moduli scheme over `ℤ_(p)`) is not formalized; see `SupersingularCongruences.External`.

## Main results

* `LevelTwo.finrank_weightedHomogeneousSubmodule`: for even `k`, the weight-`k` part of
  `F[δ, ε]` (weights `2, 4`) has dimension `⌊k / 4⌋ + 1`, the right-hand side of eq. (5.2).
* `LevelTwo.two_le_weight_quotient`: for `p ≥ 5`, `r ≥ 1`, `t = r pⁿ (p² - 1) / 12` and
  `j ≤ pⁿ`, the weight `12 t - j (p - 1)` of the quotient `A_p^{pⁿ - j} H^{pⁿ}` of
  Proposition 5.4 is at least `2`.
-/

public section

open MvPolynomial

namespace LevelTwo

/-- The exponents `(a, b)` with `2a + 4b = k` (`k` even) are indexed by `b ∈ {0, …, ⌊k / 4⌋}`. -/
noncomputable def weightTwoFourEquiv {k : ℕ} (hk : Even k) :
    {d : Fin 2 →₀ ℕ // d ∈ {d : Fin 2 →₀ ℕ | Finsupp.weight ![2, 4] d = k}} ≃ Fin (k / 4 + 1) where
  toFun d := ⟨d.1 1, by
    have h := d.2
    simp only [Set.mem_ofPred_eq, weight_two_four_apply] at h
    omega⟩
  invFun b := ⟨Finsupp.single 0 ((k - 4 * b.1) / 2) + Finsupp.single 1 b.1, by
    obtain ⟨m, rfl⟩ := hk
    have hb := b.2
    simp only [Set.mem_ofPred_eq, weight_two_four_apply, Finsupp.add_apply]
    simp
    omega⟩
  left_inv d := by
    obtain ⟨m, rfl⟩ := hk
    obtain ⟨d, hd⟩ := d
    simp only [Set.mem_ofPred_eq, weight_two_four_apply] at hd
    apply Subtype.ext
    ext i
    fin_cases i <;> (simp; try omega)
  right_inv b := by
    ext
    simp

/-- **Remark 5.2, eq. (5.2), the polynomial side**: for even `k`, the weight-`k` part of
`F[δ, ε]` (weights `2, 4`) has dimension `⌊k / 4⌋ + 1`. -/
theorem finrank_weightedHomogeneousSubmodule (F : Type*) [Field F] {k : ℕ} (hk : Even k) :
    Module.finrank F (weightedHomogeneousSubmodule F ![2, 4] k) = k / 4 + 1 := by
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported,
    (AddMonoidAlgebra.supportedEquivFinsupp (R := F) (S := F) _).finrank_eq,
    (Finsupp.domLCongr (M := F) (R := F) (weightTwoFourEquiv hk)).finrank_eq,
    Module.finrank_finsupp_self, Fintype.card_fin]

/-- **Remark 5.2, the weight of the quotient**: for `p ≥ 5`, `r ≥ 1`,
`t = r pⁿ (p² - 1) / 12` (with `12 ∣ p² - 1`) and `j ≤ pⁿ`, the weight `12 t - j (p - 1)` is at
least `2`. -/
theorem two_le_weight_quotient {p r n j t : ℕ} (hp5 : 5 ≤ p) (hr : 1 ≤ r)
    (ht : t = r * p ^ n * ((p ^ 2 - 1) / 12)) (h12 : 12 ∣ p ^ 2 - 1) (hjn : j ≤ p ^ n) :
    2 ≤ 12 * (t : ℤ) - j * ((p : ℤ) - 1) := by
  have hpn : 1 ≤ p ^ n := Nat.one_le_pow _ _ (by omega)
  have h12t : 12 * t = r * p ^ n * (p ^ 2 - 1) := by
    rw [ht, mul_comm 12, mul_assoc, Nat.div_mul_cancel h12]
  have hp2 : 1 ≤ p ^ 2 := by nlinarith
  have hcast : ((12 * t : ℕ) : ℤ) = r * p ^ n * ((p : ℤ) ^ 2 - 1) := by
    rw [h12t]; push_cast [Nat.cast_sub hp2]; ring
  push_cast at hcast
  rw [hcast]
  have hpz : (5 : ℤ) ≤ p := by exact_mod_cast hp5
  have hpnz : (1 : ℤ) ≤ (p : ℤ) ^ n := by exact_mod_cast hpn
  have hjz : (j : ℤ) ≤ (p : ℤ) ^ n := by exact_mod_cast hjn
  have hrz : (1 : ℤ) ≤ r := by exact_mod_cast hr
  nlinarith [mul_le_mul_of_nonneg_right hjz (show (0 : ℤ) ≤ p - 1 by linarith),
    mul_le_mul_of_nonneg_right hrz (show (0 : ℤ) ≤ (p : ℤ) ^ n * ((p : ℤ) ^ 2 - 1) by
      apply mul_nonneg <;> nlinarith)]

end LevelTwo
