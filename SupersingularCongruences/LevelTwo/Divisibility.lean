/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.LevelTwo.LarsonRing
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Divisibility of `L₂(Δ^t)` by powers of the Hasse invariant at level two

Proposition 5.3 of the manuscript: for `j ≥ 1`, `A_p^j ∣ L₂(Δ^t)` in `𝔽_p[δ, ε]` iff `j ≤ p^n`.

The manuscript deduces this from
* Proposition 3.4: over `𝔽̄_p`, `A_p = c δ^{α_p} ∏_{i=1}^s (μ - ξ_i ε)` with `c ≠ 0`, `α_p ∈ {0,1}`,
  `s ≥ 1` and distinct `ξ_i ∉ {0, -1}`;
* Corollary 4.6: `ξ_i ^ t' = 64 ^ t'` for all `i`, and `(-1) ^ t' = 64 ^ t'` if `α_p = 1`;
* Proposition 5.2 (`LevelTwo.larsonL2_eq_prod`).

Proposition 3.4 and Corollary 4.6 are formalized for Katz forms as `KatzForms.hasse_factorization`
and `KatzForms.xi_pow_eq_of_supersingular_eq`, and combined with this file in
`KatzForms.hasse_pow_dvd_larsonL2_iff`. The theorem `LevelTwo.pow_dvd_larsonL2_iff` below is the
algebraic core of
Proposition 5.3, with the conclusions of Proposition 3.4 and Corollary 4.6 as explicit
hypotheses on a polynomial `A`; `LevelTwo.pow_dvd_larsonL2_iff_of_map` descends it to a subfield
(such as `𝔽_p ⊆ 𝔽̄_p`), as in the first paragraph of the manuscript's proof.
-/

public section

open MvPolynomial

namespace MvPolynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {σ : Type*}

/-- Divisibility of multivariate polynomials descends along a field extension. -/
theorem dvd_of_map_dvd_map {a b : MvPolynomial σ K}
    (h : map (algebraMap K L) a ∣ map (algebraMap K L) b) : a ∣ b := by
  classical
  obtain ⟨g, hg⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective K L))
  have hgK : ∀ x : K, g (algebraMap K L x) = x := fun x => LinearMap.congr_fun hg x
  obtain ⟨h', hh'⟩ := h
  refine ⟨∑ m ∈ h'.support, monomial m (g (h'.coeff m)), ?_⟩
  refine MvPolynomial.ext _ _ fun m => ?_
  have hcoeff : ∀ v,
      (∑ m ∈ h'.support, monomial m (g (h'.coeff m))).coeff v = g (h'.coeff v) := by
    intro v
    rw [coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hv
    · rfl
    · rw [notMem_support_iff.mp hv, map_zero]
  have hm := congrArg (fun q => q.coeff m) hh'
  simp only [coeff_map, coeff_mul] at hm
  rw [coeff_mul]
  simp only [hcoeff]
  rw [← hgK (b.coeff m), hm, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

end MvPolynomial

namespace LevelTwo

variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]

omit [IsAlgClosed K] in
lemma sixtyFour_ne_zero (hp2 : p ≠ 2) : (64 : K) ≠ 0 := by
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : (p : ℕ) ∣ 2 := by
      have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
      exact this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp this)
  have : (64 : K) = 2 ^ 6 := by norm_num
  rw [this]
  exact pow_ne_zero _ h2

/-- **Proposition 5.3** (algebraic core, over an algebraically closed field of characteristic
`p ≠ 2`). Let `t = p ^ n * t'` with `p ∤ t'` and let
`A = c δ^α ∏_{i < s} (μ - ξ_i ε)` with `c ≠ 0`, `α ≤ 1`, `s ≥ 1`, distinct `ξ_i ∉ {0, -1}`
satisfying `ξ_i ^ t' = 64 ^ t'`, and `(-1) ^ t' = 64 ^ t'` if `α = 1` (the shape given by
Proposition 3.4 and Corollary 4.6). Then `A ^ j ∣ L₂(Δ^t)` iff `j ≤ p ^ n` (the manuscript
states this for `j ≥ 1`; it also holds trivially for `j = 0`). -/
theorem pow_dvd_larsonL2_iff (hp2 : p ≠ 2) {n t' : ℕ} (ht' : ¬ p ∣ t') {s : ℕ} (hs : 1 ≤ s)
    (ξ : Fin s → K) (hξ : Function.Injective ξ) (hξ0 : ∀ i, ξ i ≠ 0) (hξ1 : ∀ i, ξ i ≠ -1)
    (hξW : ∀ i, ξ i ^ t' = 64 ^ t') {α : ℕ} (hα : α ≤ 1)
    (hαW : α = 1 → (-1 : K) ^ t' = 64 ^ t') {c : K} (hc : c ≠ 0)
    {A : MvPolynomial (Fin 2) K} (hA : A = C c * delta K ^ α * ∏ i, (mu K - C (ξ i) * eps K))
    (j : ℕ) :
    A ^ j ∣ larsonL2 K (p ^ n * t') ↔ j ≤ p ^ n := by
  classical
  have h64 := sixtyFour_ne_zero (K := K) p hp2
  have ht0 : t' ≠ 0 := by rintro rfl; exact ht' (dvd_zero p)
  have hL := larsonL2_eq_prod p h64 (n := n) ht'
  set W := rootSet64 K t' with hWdef
  set S := Finset.univ.image ξ with hSdef
  have hSW : S ⊆ W := by
    intro ρ hρ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hρ
    exact (mem_rootSet64 ht0).mpr (hξW i)
  have hprodS : ∏ i, (mu K - C (ξ i) * eps K) = ∏ ρ ∈ S, (mu K - C ρ * eps K) := by
    rw [Finset.prod_image (fun x _ y _ h => hξ h)]
  constructor
  · -- if `j > p ^ n`, the factor `μ - ξ₀ ε` divides `A ^ j` to order `j` but `L₂(Δ^t)` only to
    -- order `p ^ n`.
    intro hdvd
    by_contra hjn
    push Not at hjn
    set ξ₀ := ξ ⟨0, hs⟩
    set π := mu K - C ξ₀ * eps K
    have hξ₀W : ξ₀ ∈ W := hSW (Finset.mem_image_of_mem ξ (Finset.mem_univ _))
    set M := mu K ^ (p ^ n * t') * eps K ^ (p ^ n * t') *
      ∏ ρ ∈ W.erase ξ₀, (mu K - C ρ * eps K) ^ p ^ n
    have hLM : larsonL2 K (p ^ n * t') = π ^ p ^ n * M := by
      rw [hL, ← Finset.mul_prod_erase W _ hξ₀W]
      ring
    have hπA : π ∣ A := by
      rw [hA]
      exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ _)) _
    have hπj : π ^ (p ^ n + 1) ∣ larsonL2 K (p ^ n * t') :=
      (pow_dvd_pow π hjn).trans ((pow_dvd_pow_of_dvd hπA j).trans hdvd)
    rw [hLM, pow_succ] at hπj
    have hπ0 : π ^ p ^ n ≠ 0 := by
      refine pow_ne_zero _ fun h0 => ?_
      have := congrArg (eval ![1, 0]) h0
      simp [π] at this
    have hπM : π ∣ M := (mul_dvd_mul_iff_left hπ0).mp hπj
    -- evaluate at a point `(δ₀, 1)` with `δ₀² = 1 + ξ₀`, where `π` vanishes but `M` does not
    obtain ⟨δ₀, hδ₀⟩ := IsAlgClosed.exists_pow_nat_eq (1 + ξ₀) two_pos
    obtain ⟨q, hq⟩ := hπM
    have hπev : eval ![δ₀, 1] π = 0 := by
      simp [π, hδ₀]
    have hMev : eval ![δ₀, 1] M = 0 := by rw [hq, map_mul, hπev, zero_mul]
    have hmu : eval ![δ₀, 1] (mu K) = ξ₀ := by simp [hδ₀]
    have heps : eval ![δ₀, 1] (eps K) = 1 := by simp
    simp only [M, map_mul, map_pow, map_prod, map_sub, hmu, heps, eval_C, one_pow,
      mul_one] at hMev
    refine (mul_ne_zero (pow_ne_zero _ (hξ0 _)) (Finset.prod_ne_zero_iff.mpr ?_)) hMev
    intro ρ hρ
    exact pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hρ).symm)
  · -- if `j ≤ p ^ n`, every factor of `A ^ (p ^ n)` occurs in `L₂(Δ^t)`.
    intro hjn
    refine (pow_dvd_pow A hjn).trans ?_
    rw [hL]
    refine Dvd.dvd.mul_left ?_ _
    have hunit : IsUnit (C c ^ p ^ n : MvPolynomial (Fin 2) K) :=
      ((Ne.isUnit hc).map C).pow _
    rw [hA, mul_pow, mul_pow, hprodS, ← Finset.prod_pow]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hα with rfl | rfl
    · rw [pow_zero, one_pow, mul_one]
      exact (hunit.mul_left_dvd).mpr (Finset.prod_dvd_prod_of_subset _ _ _ hSW)
    · have hm1W : (-1 : K) ∈ W := (mem_rootSet64 ht0).mpr (hαW rfl)
      have hm1S : (-1 : K) ∉ S := by
        intro h
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
        exact hξ1 i hi
      have hsub : insert (-1 : K) S ⊆ W := Finset.insert_subset hm1W hSW
      have hdvdW := Finset.prod_dvd_prod_of_subset _ _
        (fun ρ => (mu K - C ρ * eps K) ^ p ^ n) hsub
      rw [Finset.prod_insert hm1S, mu_sub_neg_one_mul_eps, ← pow_mul] at hdvdW
      rw [pow_one, mul_assoc]
      refine (hunit.mul_left_dvd).mpr (dvd_trans ?_ hdvdW)
      exact mul_dvd_mul_right (pow_dvd_pow _ (by omega)) _

/-- **Proposition 5.3** over a subfield: if `A, L ∈ k[δ, ε]` and the image of `A` in
`K[δ, ε]` (`K ⊇ k` algebraically closed) has the shape of `pow_dvd_larsonL2_iff`, then
`A ^ j ∣ L₂(Δ^t)` in `k[δ, ε]` iff `j ≤ p ^ n`. -/
theorem pow_dvd_larsonL2_iff_of_map {k : Type*} [Field k] [Algebra k K] (hp2 : p ≠ 2)
    {n t' : ℕ} (ht' : ¬ p ∣ t') {s : ℕ} (hs : 1 ≤ s)
    (ξ : Fin s → K) (hξ : Function.Injective ξ) (hξ0 : ∀ i, ξ i ≠ 0) (hξ1 : ∀ i, ξ i ≠ -1)
    (hξW : ∀ i, ξ i ^ t' = 64 ^ t') {α : ℕ} (hα : α ≤ 1)
    (hαW : α = 1 → (-1 : K) ^ t' = 64 ^ t') {c : K} (hc : c ≠ 0)
    {A : MvPolynomial (Fin 2) k}
    (hA : map (algebraMap k K) A = C c * delta K ^ α * ∏ i, (mu K - C (ξ i) * eps K))
    (j : ℕ) :
    A ^ j ∣ larsonL2 k (p ^ n * t') ↔ j ≤ p ^ n := by
  rw [← pow_dvd_larsonL2_iff p hp2 ht' hs ξ hξ hξ0 hξ1 hξW hα hαW hc hA j,
    ← map_larsonL2 (algebraMap k K), ← map_pow]
  exact ⟨fun h => map_dvd _ h, dvd_of_map_dvd_map⟩

end LevelTwo
