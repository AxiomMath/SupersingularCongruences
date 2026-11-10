/-
Assembled by AxiomProver.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable

/-!
# Uniform multiplicity of the roots of `X ^ t - b` in characteristic `p`

Lemma 5.1 of the manuscript: let `K` be an algebraically closed field of characteristic `p`,
`b ∈ Kˣ` and `t = p ^ n * t'` with `p ∤ t'`. Then
`X ^ t - b = (X ^ t' - b₀) ^ (p ^ n) = ∏_{ρ ∈ W} (X - ρ) ^ (p ^ n)`, where `b₀ ^ (p ^ n) = b`
and `W` is the set of the `t'` distinct (nonzero) roots of `X ^ t' - b₀`; in particular every
root of `X ^ t - b` has multiplicity exactly `p ^ n`.
-/

public section

open Polynomial

namespace Polynomial

variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Freshman's dream for `X ^ (p ^ n * t') - b`. -/
theorem X_pow_sub_C_eq_pow_of_pow_eq {n t' : ℕ} {b b₀ : K} (hb : b₀ ^ p ^ n = b) :
    (X ^ (p ^ n * t') - C b : K[X]) = (X ^ t' - C b₀) ^ p ^ n := by
  rw [sub_pow_char_pow, ← pow_mul, mul_comm, ← C_pow, hb]

omit [Fact p.Prime] in
/-- The `p`-power-free part `X ^ t' - b₀` is separable when `p ∤ t'` and `b₀ ≠ 0`. -/
theorem separable_X_pow_sub_C_of_not_dvd {t' : ℕ} {b₀ : K} (ht' : ¬ p ∣ t') (hb₀ : b₀ ≠ 0) :
    (X ^ t' - C b₀ : K[X]).Separable :=
  separable_X_pow_sub_C' p t' b₀ ht' hb₀

variable [IsAlgClosed K] [DecidableEq K]

omit [Fact p.Prime] in
/-- `X ^ t' - b₀` has exactly `t'` distinct roots. -/
theorem card_roots_toFinset_X_pow_sub_C {t' : ℕ} {b₀ : K} (ht' : ¬ p ∣ t') (hb₀ : b₀ ≠ 0) :
    (X ^ t' - C b₀ : K[X]).roots.toFinset.card = t' := by
  have hsep := separable_X_pow_sub_C_of_not_dvd p ht' hb₀
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
    natDegree_X_pow_sub_C]

omit [Fact p.Prime] in
/-- `X ^ t' - b₀` is the product of `X - ρ` over its distinct roots. -/
theorem X_pow_sub_C_eq_prod_roots {t' : ℕ} {b₀ : K} (ht' : ¬ p ∣ t') (hb₀ : b₀ ≠ 0) :
    (X ^ t' - C b₀ : K[X]) = ∏ ρ ∈ (X ^ t' - C b₀ : K[X]).roots.toFinset, (X - C ρ) := by
  have hsep := separable_X_pow_sub_C_of_not_dvd p ht' hb₀
  have ht0 : t' ≠ 0 := by rintro rfl; exact ht' (dvd_zero p)
  have hmonic : (X ^ t' - C b₀ : K[X]).Monic := monic_X_pow_sub_C b₀ ht0
  conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic
    IsAlgClosed.card_roots_eq_natDegree]
  rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr (nodup_roots hsep)]

/-- **Lemma 5.1** (uniform multiplicity). For `b ≠ 0` and `t = p ^ n * t'` with `p ∤ t'` there is
`b₀` with `b₀ ^ (p ^ n) = b` such that `X ^ t - b = (X ^ t' - b₀) ^ (p ^ n)`,
`X ^ t' - b₀` is separable with exactly `t'` roots, none of them zero, and
`X ^ t - b = ∏_{ρ ∈ W} (X - ρ) ^ (p ^ n)` over the root set `W` of `X ^ t' - b₀`. -/
theorem exists_X_pow_sub_C_eq_prod_pow {b : K} (hb : b ≠ 0) {n t' : ℕ} (ht' : ¬ p ∣ t') :
    ∃ b₀ : K, b₀ ^ p ^ n = b ∧
      (X ^ (p ^ n * t') - C b : K[X]) = (X ^ t' - C b₀) ^ p ^ n ∧
      (X ^ t' - C b₀ : K[X]).Separable ∧
      (X ^ t' - C b₀ : K[X]).roots.toFinset.card = t' ∧
      (0 : K) ∉ (X ^ t' - C b₀ : K[X]).roots.toFinset ∧
      (X ^ (p ^ n * t') - C b : K[X]) =
        ∏ ρ ∈ (X ^ t' - C b₀ : K[X]).roots.toFinset, (X - C ρ) ^ p ^ n := by
  obtain ⟨b₀, hb₀⟩ := IsAlgClosed.exists_pow_nat_eq b (pow_pos (Fact.out : p.Prime).pos n)
  have hb₀0 : b₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)] at hb₀
    exact hb hb₀.symm
  have ht0 : t' ≠ 0 := by rintro rfl; exact ht' (dvd_zero p)
  have hfac := X_pow_sub_C_eq_pow_of_pow_eq (t' := t') p hb₀
  refine ⟨b₀, hb₀, hfac, separable_X_pow_sub_C_of_not_dvd p ht' hb₀0,
    card_roots_toFinset_X_pow_sub_C p ht' hb₀0, ?_, ?_⟩
  · intro h0
    rw [Multiset.mem_toFinset, mem_roots (X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero ht0) b₀)] at h0
    rw [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, zero_pow ht0, zero_sub,
      neg_eq_zero] at h0
    exact hb₀0 h0
  · rw [hfac, Finset.prod_pow, ← X_pow_sub_C_eq_prod_roots p ht' hb₀0]

omit [DecidableEq K] in
/-- Every root of `X ^ (p ^ n * t') - b` (with `b ≠ 0`, `p ∤ t'`) has multiplicity exactly
`p ^ n`. -/
theorem rootMultiplicity_X_pow_sub_C {b : K} (hb : b ≠ 0) {n t' : ℕ} (ht' : ¬ p ∣ t') {ρ : K}
    (hρ : (X ^ (p ^ n * t') - C b : K[X]).IsRoot ρ) :
    (X ^ (p ^ n * t') - C b : K[X]).rootMultiplicity ρ = p ^ n := by
  classical
  obtain ⟨b₀, hb₀, hfac, hsep, -, -, -⟩ := exists_X_pow_sub_C_eq_prod_pow p hb (n := n) ht'
  have ht0 : t' ≠ 0 := by rintro rfl; exact ht' (dvd_zero p)
  have hne : (X ^ t' - C b₀ : K[X]) ≠ 0 := X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero ht0) b₀
  have hroot : (X ^ t' - C b₀ : K[X]).IsRoot ρ := by
    rw [hfac, IsRoot, eval_pow] at hρ
    exact pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) |>.mp hρ
  have h1 : (X ^ t' - C b₀ : K[X]).rootMultiplicity ρ = 1 :=
    le_antisymm (rootMultiplicity_le_one_of_separable hsep ρ)
      ((rootMultiplicity_pos hne).mpr hroot)
  rw [hfac, ← count_roots, roots_pow, Multiset.count_nsmul, count_roots, h1, mul_one]

end Polynomial
