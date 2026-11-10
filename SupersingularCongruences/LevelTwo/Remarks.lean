/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.LevelTwo.Divisibility

/-!
# Remarks on the level-two divisibility

* `LevelTwo.delta_pow_dvd_larsonL2_iff` (Remark 5.1): when `-1 ∈ W`, i.e. `(-1) ^ t' = 64 ^ t'`,
  the elliptic factor `δ` divides `L₂(Δ^t)` to order exactly `2 p ^ n` — twice the naive count —
  so a Hasse invariant consisting of `δ` alone would not give the sharp bound `j ≤ p ^ n`.
* `LevelTwo.pow_eq_sixtyFour_pow_of_div_pow_eq_one`: the deduction step of Corollary 4.6, from
  `R₂(P̃) ^ m = (x(P̃) / 64) ^ m = 1` (Theorem 1.2 at `ℓ = 2`, `Gamma0.Pair.veluRatio_pow_eq_one`)
  to
  `x(P̃) ^ (r m) = 64 ^ (r m)`.
-/

public section

open MvPolynomial

namespace LevelTwo

variable {K : Type*} [Field K]

/-- The deduction in Corollary 4.6: if `(x / 64) ^ m = 1` then `x ^ (r * m) = 64 ^ (r * m)`. -/
theorem pow_eq_sixtyFour_pow_of_div_pow_eq_one (h64 : (64 : K) ≠ 0) {x : K} {m : ℕ}
    (h : (x / 64) ^ m = 1) (r : ℕ) : x ^ (r * m) = 64 ^ (r * m) := by
  rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ h64)] at h
  rw [mul_comm, pow_mul, h, ← pow_mul]

variable (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]

/-- **Remark 5.1**: if `(-1) ^ t' = 64 ^ t'` (so that `x = -1` lies in `W`), then
`δ ^ j ∣ L₂(Δ^t)` iff `j ≤ 2 p ^ n`. -/
theorem delta_pow_dvd_larsonL2_iff (hp2 : p ≠ 2) {n t' : ℕ} (ht' : ¬ p ∣ t')
    (hW : (-1 : K) ^ t' = 64 ^ t') (j : ℕ) :
    delta K ^ j ∣ larsonL2 K (p ^ n * t') ↔ j ≤ 2 * p ^ n := by
  classical
  have h64 := sixtyFour_ne_zero (K := K) p hp2
  have ht0 : t' ≠ 0 := by rintro rfl; exact ht' (dvd_zero p)
  have hm1 : (-1 : K) ∈ rootSet64 K t' := (mem_rootSet64 ht0).mpr hW
  set M := mu K ^ (p ^ n * t') * eps K ^ (p ^ n * t') *
    ∏ ρ ∈ (rootSet64 K t').erase (-1), (mu K - C ρ * eps K) ^ p ^ n
  have hLM : larsonL2 K (p ^ n * t') = delta K ^ (2 * p ^ n) * M := by
    rw [larsonL2_eq_prod p h64 ht', ← Finset.mul_prod_erase _ _ hm1, mu_sub_neg_one_mul_eps,
      ← pow_mul]
    ring
  constructor
  · intro hdvd
    by_contra hj
    push Not at hj
    have h1 : delta K ^ (2 * p ^ n) * delta K ∣ delta K ^ (2 * p ^ n) * M := by
      rw [← pow_succ, ← hLM]
      exact (pow_dvd_pow _ hj).trans hdvd
    have hδM : delta K ∣ M := (mul_dvd_mul_iff_left (pow_ne_zero _ delta_ne_zero)).mp h1
    obtain ⟨q, hq⟩ := hδM
    have hev : eval ![(0 : K), 1] M = 0 := by
      rw [hq, map_mul, eval_delta, Matrix.cons_val_zero, zero_mul]
    have hmu : eval ![0, 1] (mu K) = -1 := by simp
    have heps : eval ![(0 : K), 1] (eps K) = 1 := by simp
    simp only [M, map_mul, map_pow, map_prod, map_sub, hmu, heps, eval_C, one_pow,
      mul_one] at hev
    refine (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (Finset.prod_ne_zero_iff.mpr ?_)) hev
    intro ρ hρ
    exact pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hρ).symm)
  · intro hj
    rw [hLM]
    exact (pow_dvd_pow _ hj).trans (dvd_mul_right _ _)

end LevelTwo
