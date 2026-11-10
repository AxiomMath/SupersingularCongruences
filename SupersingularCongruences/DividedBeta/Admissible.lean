/-
Assembled by AxiomProver.
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Admissible indices of order-`p` divided beta elements

Following [larson2020, Lemma 2.1] (as recalled in [ono-manuscript, Section 2.1]), write
`i = r * p ^ n` with `p ∤ r`. The order-`p` divided beta elements `β_{i/j}` are indexed by the
pairs `(i, j)` with

* `1 ≤ j ≤ p ^ n` if `r = 1`, and `1 ≤ j ≤ b_n` if `r > 1`,
* `j ∉ {p, 2p, …, b_{n-2} p}`,

where `b_m = 0` for `m < 0`, `b_0 = 1` and `b_m = p ^ m + p ^ (m - 1) - 1` for `m ≥ 1`.
Such pairs are called *admissible*.

## Main results

* `DividedBeta.isAdmissible_mul_pow_iff`: the explicit description above for `i = r * p ^ n`.
* `DividedBeta.exists_isAdmissible_gt_iff`: admissible indices `j > p ^ n` occur exactly when
  `r > 1` and `n ≥ 2`.
* `DividedBeta.mul_lt_pow_of_le_bIndex`: the excluded indices are all `< p ^ n`.
* `DividedBeta.isAdmissible_one`: `(i, 1)` is always admissible.
-/

public section

namespace DividedBeta

/-- Larson's sequence `b_m` for `m ≥ 0`: `b_0 = 1` and `b_m = p ^ m + p ^ (m - 1) - 1` for
`m ≥ 1` [larson2020, Lemma 2.1]. (Larson's convention `b_m = 0` for `m < 0` is encoded in
`IsAdmissible` by requiring `2 ≤ n` for the exclusions governed by `b_{n-2}`.) -/
def bIndex (p m : ℕ) : ℕ :=
  if m = 0 then 1 else p ^ m + p ^ (m - 1) - 1

@[simp] lemma bIndex_zero (p : ℕ) : bIndex p 0 = 1 := by
  simp [bIndex]

lemma bIndex_succ (p m : ℕ) : bIndex p (m + 1) = p ^ (m + 1) + p ^ m - 1 := by
  simp [bIndex]

lemma bIndex_one (p : ℕ) : bIndex p 1 = p := by
  simp [bIndex]

/-- The pair `(i, j)` is *admissible* (indexes an order-`p` divided beta element `β_{i/j}`)
in the sense of [larson2020, Lemma 2.1]. Here `n = ν_p(i)` and `r = i / p ^ n`; the excluded
indices are `j = c * p` with `1 ≤ c ≤ b_{n-2}`, which is an empty condition when `n < 2`. -/
def IsAdmissible (p i j : ℕ) : Prop :=
  1 ≤ i ∧ 1 ≤ j ∧
    (if i / p ^ padicValNat p i = 1 then j ≤ p ^ padicValNat p i
      else j ≤ bIndex p (padicValNat p i)) ∧
    ∀ c : ℕ, 1 ≤ c → 2 ≤ padicValNat p i → c ≤ bIndex p (padicValNat p i - 2) → j ≠ c * p

lemma IsAdmissible.one_le_left {p i j : ℕ} (h : IsAdmissible p i j) : 1 ≤ i := h.1

lemma IsAdmissible.one_le_right {p i j : ℕ} (h : IsAdmissible p i j) : 1 ≤ j := h.2.1

section

variable {p : ℕ} [hp : Fact p.Prime]

lemma padicValNat_mul_pow {r n : ℕ} (hr : ¬ p ∣ r) : padicValNat p (r * p ^ n) = n := by
  have hr0 : r ≠ 0 := by rintro rfl; exact hr (dvd_zero p)
  rw [padicValNat.mul hr0 (pow_ne_zero _ hp.out.ne_zero), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hr, zero_add]

/-- Explicit form of admissibility for `i = r * p ^ n` with `p ∤ r`. -/
theorem isAdmissible_mul_pow_iff {r n j : ℕ} (hr : ¬ p ∣ r) (hr1 : 1 ≤ r) :
    IsAdmissible p (r * p ^ n) j ↔
      1 ≤ j ∧ (if r = 1 then j ≤ p ^ n else j ≤ bIndex p n) ∧
        ∀ c : ℕ, 1 ≤ c → 2 ≤ n → c ≤ bIndex p (n - 2) → j ≠ c * p := by
  have hpos : 0 < p ^ n := pow_pos hp.out.pos n
  have hdiv : r * p ^ n / p ^ n = r := Nat.mul_div_cancel r hpos
  simp only [IsAdmissible, padicValNat_mul_pow hr, hdiv]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hpos.ne'), h⟩

/-- Every excluded index `c * p` with `1 ≤ c ≤ b_{n-2}` (and `n ≥ 2`) is strictly smaller
than `p ^ n`. -/
theorem mul_lt_pow_of_le_bIndex {n c : ℕ} (hc : 1 ≤ c) (hn : 2 ≤ n)
    (hcn : c ≤ bIndex p (n - 2)) : c * p < p ^ n := by
  have hp2 := hp.out.two_le
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [Nat.add_sub_cancel] at hcn
  rcases k with _ | k
  · rw [bIndex_zero] at hcn
    have : c = 1 := by omega
    subst this
    calc 1 * p = p ^ 1 := by ring
      _ < p ^ (0 + 2) := Nat.pow_lt_pow_right hp2 (by omega)
  · rw [bIndex_succ] at hcn
    have hle : c * p ≤ (p ^ (k + 1) + p ^ k - 1) * p := Nat.mul_le_mul_right p hcn
    have e1 : (p ^ (k + 1) + p ^ k - 1) * p = p ^ (k + 2) + p ^ (k + 1) - p := by
      rw [Nat.sub_mul, Nat.add_mul, one_mul, ← pow_succ, ← pow_succ]
    have e2 : p ^ (k + 1 + 2) = p * p ^ (k + 2) := by ring
    have h3 : p ^ (k + 1) ≤ p ^ (k + 2) := Nat.pow_le_pow_right hp.out.pos (by omega)
    have h4 : p ^ (k + 2) ≥ 1 := Nat.one_le_pow _ _ hp.out.pos
    have h5 : 2 * p ^ (k + 2) ≤ p * p ^ (k + 2) := Nat.mul_le_mul_right _ hp2
    omega

/-- For `r > 1`, every `j` with `p ^ n < j ≤ b_n` is admissible: the region `j > p ^ n`
contains no excluded indices. -/
theorem isAdmissible_of_pow_lt {r n j : ℕ} (hr : ¬ p ∣ r) (hr1 : 1 < r) (hj : p ^ n < j)
    (hjb : j ≤ bIndex p n) : IsAdmissible p (r * p ^ n) j := by
  rw [isAdmissible_mul_pow_iff hr hr1.le]
  refine ⟨by have := Nat.one_le_pow n p hp.out.pos; omega, by simpa [hr1.ne'] using hjb, ?_⟩
  intro c hc hn hcn hjc
  have := mul_lt_pow_of_le_bIndex hc hn hcn
  omega

/-- The pair `(i, 1)` is admissible for every `i ≥ 1` (the elements `β_i = β_{i/1}`). -/
theorem isAdmissible_one {i : ℕ} (hi : 1 ≤ i) : IsAdmissible p i 1 := by
  refine ⟨hi, le_rfl, ?_, ?_⟩
  · split_ifs
    · exact Nat.one_le_pow _ _ hp.out.pos
    · rcases (padicValNat p i).eq_zero_or_pos with h | h
      · simp [h]
      · obtain ⟨m, hm⟩ : ∃ m, padicValNat p i = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
        rw [hm, bIndex_succ]
        have := Nat.one_le_pow m p hp.out.pos
        have := Nat.one_le_pow (m + 1) p hp.out.pos
        omega
  · intro c hc _ _ h
    have h2 := hp.out.two_le
    have : p ≤ c * p := Nat.le_mul_of_pos_left p hc
    omega

/-- Admissible indices `j > p ^ n` exist exactly when `r > 1` and `n ≥ 2`
(the parenthetical claim in Theorem 1.1(ii) of the manuscript). -/
theorem exists_isAdmissible_gt_iff {r n : ℕ} (hr : ¬ p ∣ r) (hr1 : 1 ≤ r) :
    (∃ j, IsAdmissible p (r * p ^ n) j ∧ p ^ n < j) ↔ 1 < r ∧ 2 ≤ n := by
  have hp2 := hp.out.two_le
  constructor
  · rintro ⟨j, hadm, hj⟩
    rw [isAdmissible_mul_pow_iff hr hr1] at hadm
    obtain ⟨-, hle, -⟩ := hadm
    split_ifs at hle with h
    · omega
    · refine ⟨by omega, ?_⟩
      by_contra hn
      have hn' : n = 0 ∨ n = 1 := by omega
      rcases hn' with rfl | rfl
      · rw [bIndex_zero] at hle
        rw [pow_zero] at hj
        omega
      · rw [bIndex_one] at hle
        rw [pow_one] at hj
        omega
  · rintro ⟨hr', hn⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine ⟨p ^ (k + 1) + 1, isAdmissible_of_pow_lt hr hr' (by omega) ?_, by omega⟩
    rw [bIndex_succ]
    have : 2 ≤ p ^ k := by
      calc 2 ≤ p := hp2
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ k := Nat.pow_le_pow_right hp.out.pos (by omega)
    omega

end

end DividedBeta
