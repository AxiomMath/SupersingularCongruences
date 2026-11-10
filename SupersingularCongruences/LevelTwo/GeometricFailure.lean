/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.KatzForms.Legendre
public import SupersingularCongruences.KatzForms.HasseInvariant
public import SupersingularCongruences.ModularCurve.LevelTwoCoordinate
import all SupersingularCongruences.EllipticCurve.LegendreHasse

/-!
# Theorem 1.1(ii) at level `2` in the geometric ring

Let `p ≥ 5`, `L` an algebraically closed field of characteristic `p`, and `K` the Katz forms on
`Γ₀(2)` over `L`, regular on the Legendre family (`KatzForms.LegendreRegular`). Let
`t = pⁿ t'` with `p ∤ t'` and `j > pⁿ`. Then there is **no** Katz form `H` on `Γ₀(2)` (of any
weight, defined over `𝔽_p` or not) with

  `V₂(Δ̄ᵗ) - Δ̄ᵗ = A_p^j · H`.

In particular `Δᵗ` fails Behrens' condition (C4) at `ℓ = 2` when `t = r pⁿ (p² - 1) / 12`,
`p ∤ r` and `j > pⁿ`.

## Proof (Lean route; a deviation from the manuscript)

The manuscript deduces this from Proposition 5.3 (divisibility in Larson's ring `𝔽_p[δ, ε]`)
together with Remark 5.2 (the geometric ring at level `2` *is* `𝔽_p[δ, ε]`). Only the injective
half of that identification is formalized (`KatzForms.larsonToForm_injective`); instead we
compare orders of vanishing directly on the Legendre family
`T_λ = (E_λ, ⟨(0, 0)⟩, dx / (2y))`, `λ ≠ 0, 1`:

* by Lemma 4.1, `Δ(T_λ) = 16 λ² (λ - 1)²` and `x(λ) = (λ - 1)² / (4 λ)`, the left side at `T_λ`
  is `Q(λ) = 16⁻ᵗ λᵗ (λ - 1)^{2t} ((λ - 1)^{2t} - 256ᵗ λᵗ)`;
* `A_p(T_λ) = (-1)^{(p-1)/2} H_p(λ)` (Lemma 2.1(d)) and `H(T_λ) = P(λ) / (λᵃ (λ - 1)ᵇ)`
  (Legendre regularity), so `Q · Xᵃ (X - 1)ᵇ = ± H_p^j P` in `L[X]`;
* `H_p` has a root `λ₀ ∉ {0, 1, -1}` (it is separable of degree `(p - 1) / 2 ≥ 2` with
  `H_p(0) = 1`, `H_p(1) ≠ 0`), where the right side vanishes to order `≥ j`;
* by the freshman's dream, `(X - 1)^{2t} - 256ᵗ Xᵗ = G^{pⁿ}` with
  `G = (X - 1)^{2t'} - 256^{t'} X^{t'}`, and `G` has at most a simple zero at `λ₀`, because
  `λ (λ - 1) G'(λ) = t' 256^{t'} λ^{t'} (λ + 1)` at every zero `λ` of `G`; hence the left side
  vanishes to order `≤ pⁿ < j` at `λ₀`, a contradiction.

## Main results

* `KatzForms.not_exists_hasse_pow_mul_eq_levelRaise_sub_two`: the general non-divisibility for
  `t = pⁿ t'`, `p ∤ t'`, `j > pⁿ`.
* `KatzForms.not_exists_hasse_pow_mul_eq_levelRaise_sub_two_of_eq`: the case
  `t = r pⁿ (p² - 1) / 12`, `p ∤ r`.
-/

public section

open Polynomial Gamma0 LevelOne

universe u

namespace Nat

/-- For a prime `p ≥ 5`, `12 ∣ p² - 1`. -/
theorem twelve_dvd_sq_sub_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : 12 ∣ p ^ 2 - 1 := by
  have h2 : ¬ 2 ∣ p := fun h ↦ by have := hp.eq_one_or_self_of_dvd 2 h; omega
  have h3 : ¬ 3 ∣ p := fun h ↦ by have := hp.eq_one_or_self_of_dvd 3 h; omega
  have h12 : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by omega
  refine (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mp ?_
  unfold Nat.ModEq
  rw [Nat.pow_mod]
  rcases h12 with h | h | h | h <;> simp [h]

/-- For a prime `p ≥ 5`, `p ∤ (p² - 1) / 12`. -/
theorem not_dvd_sq_sub_one_div_twelve {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ (p ^ 2 - 1) / 12 := by
  intro h
  have h1 : p ∣ p ^ 2 - 1 := by
    rw [← Nat.div_mul_cancel (twelve_dvd_sq_sub_one hp hp5)]
    exact h.mul_right 12
  have h2 : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
  have h3 := Nat.dvd_sub h2 h1
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

end Nat

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The multiplicity of a root of a power. -/
lemma rootMultiplicity_pow_of_ne_zero {f : R[X]} (hf : f ≠ 0) (x : R) (n : ℕ) :
    rootMultiplicity x (f ^ n) = n * rootMultiplicity x f := by
  induction n with
  | zero =>
    rw [pow_zero, zero_mul]
    exact rootMultiplicity_eq_zero (by simp)
  | succ n ih =>
    rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hf) hf), ih]
    ring

end Polynomial

namespace KatzForms

variable {L : Type*} [Field L]

/-- The polynomial `G = (X - 1)^{2s} - 256ˢ Xˢ`; on the Legendre line,
`G(λ) = 0` iff `(x(λ) / 64)ˢ = 1` for `x(λ) = (λ - 1)² / (4 λ)`. -/
noncomputable def legendreBranchPolynomial (s : ℕ) : L[X] :=
  (X - 1) ^ (2 * s) - 256 ^ s * X ^ s

lemma eval_legendreBranchPolynomial (s : ℕ) (lam : L) :
    (legendreBranchPolynomial s).eval lam = (lam - 1) ^ (2 * s) - 256 ^ s * lam ^ s := by
  simp [legendreBranchPolynomial]

lemma legendreBranchPolynomial_ne_zero {s : ℕ} (hs : s ≠ 0) :
    (legendreBranchPolynomial s : L[X]) ≠ 0 := by
  intro h
  have := congrArg (eval 0) h
  rw [eval_legendreBranchPolynomial, eval_zero, zero_pow hs, mul_zero, sub_zero, zero_sub,
    pow_mul, neg_one_sq, one_pow] at this
  exact one_ne_zero this

/-- `G = (X - 1)^{2s} - 256ˢ Xˢ` has at most a simple zero at every `λ₀ ∉ {0, 1, -1}`, provided
`s ≠ 0` and `256 s ≠ 0` in `L`: at a zero, `λ₀ (λ₀ - 1) G'(λ₀) = s 256ˢ λ₀ˢ (λ₀ + 1) ≠ 0`. -/
theorem rootMultiplicity_legendreBranchPolynomial_le_one {s : ℕ} (hs : (s : L) ≠ 0)
    (h256 : (256 : L) ≠ 0) {lam : L} (h0 : lam ≠ 0) (h1 : lam ≠ 1) (hm1 : lam ≠ -1) :
    rootMultiplicity lam (legendreBranchPolynomial s : L[X]) ≤ 1 := by
  have hs0 : s ≠ 0 := by rintro rfl; exact hs Nat.cast_zero
  have hne := legendreBranchPolynomial_ne_zero (L := L) hs0
  by_contra hlt
  rw [not_le, one_lt_rootMultiplicity_iff_isRoot hne] at hlt
  obtain ⟨hroot, hder⟩ := hlt
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  rw [IsRoot, eval_legendreBranchPolynomial] at hroot
  have hd : derivative (legendreBranchPolynomial (k + 1) : L[X]) =
      C ((2 * (k + 1) : ℕ) : L) * (X - 1) ^ (2 * k + 1) -
        256 ^ (k + 1) * (C ((k + 1 : ℕ) : L) * X ^ k) := by
    rw [legendreBranchPolynomial, derivative_sub, derivative_pow, derivative_mul, derivative_pow,
      derivative_X_pow, derivative_sub, derivative_X, derivative_one, sub_zero, mul_one,
      show 2 * (k + 1) - 1 = 2 * k + 1 by omega, Nat.add_sub_cancel]
    simp only [derivative_ofNat, mul_zero, zero_mul, zero_add]
  rw [IsRoot, hd] at hder
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one, eval_ofNat] at hder
  have hsub : lam - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hadd : lam + 1 ≠ 0 := by
    intro h; exact hm1 (eq_neg_of_add_eq_zero_left h)
  have key : lam * (lam - 1) *
      (((2 * (k + 1) : ℕ) : L) * (lam - 1) ^ (2 * k + 1) -
        256 ^ (k + 1) * (((k + 1 : ℕ) : L) * lam ^ k)) =
      ((k + 1 : ℕ) : L) * 256 ^ (k + 1) * lam ^ (k + 1) * (lam + 1) := by
    have e1 : (lam - 1) ^ (2 * (k + 1)) = (lam - 1) ^ (2 * k + 1) * (lam - 1) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ]
    rw [e1] at hroot
    push_cast
    linear_combination (2 * ((k : L) + 1) * lam) * hroot
  rw [hder, mul_zero] at key
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hs (pow_ne_zero _ h256)) (pow_ne_zero _ h0))
    hadd) key.symm

section Legendre

variable {p : ℕ} [Fact p.Prime] {L : Type u} [Field L] [DecidableEq L] [CharP L p]

omit [Fact p.Prime] [DecidableEq L] in
lemma natCast_ne_zero_of_not_dvd {m : ℕ} (hm : ¬ p ∣ m) : (m : L) ≠ 0 := by
  rwa [ne_eq, CharP.cast_eq_zero_iff L p]

omit [Fact p.Prime] [DecidableEq L] in
lemma natCast_ne_zero_of_lt {m : ℕ} (hm0 : 0 < m) (hmp : m < p) : (m : L) ≠ 0 :=
  natCast_ne_zero_of_not_dvd fun h ↦ absurd (Nat.le_of_dvd hm0 h) (by omega)

/-- The value `Q(λ) = 16⁻ᵗ λᵗ (λ - 1)^{2t} ((λ - 1)^{2t} - 256ᵗ λᵗ)` of
`V₂(Δ̄ᵗ) - Δ̄ᵗ` on the Legendre family, as a polynomial in `λ`. -/
noncomputable def legendreLevelRaiseSub (t : ℕ) : L[X] :=
  C ((16 : L) ^ t)⁻¹ * X ^ t * (X - 1) ^ (2 * t) * ((X - 1) ^ (2 * t) - 256 ^ t * X ^ t)

omit [CharP L p] in
/-- **`L₂(Δ̄ᵗ)` on the Legendre family** (Lemma 4.1 and the Legendre computations of Lemma 3.2):
at `T_λ = (E_λ, ⟨(0, 0)⟩, dx / (2y))`, `V₂(Δ̄ᵗ) - Δ̄ᵗ` takes the value
`(λ (λ - 1)⁴ / 16)ᵗ - (16 λ² (λ - 1)²)ᵗ = Q(λ)`. -/
theorem levelRaiseReduction_sub_reductionAtLevel_legendre (K : KatzForms p 2 L)
    (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) (t : ℕ) {lam : L} (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    (levelRaiseReduction K (discriminantPow t) _ (isIntegralQExpansion_discriminantPow t)).1
        ⟨legendrePair h2 h3 h0 h1, 1⟩ -
      (reductionAtLevel K (discriminantPow t) _ (isIntegralQExpansion_discriminantPow t)).1
        ⟨legendrePair h2 h3 h0 h1, 1⟩ =
      (legendreLevelRaiseSub t).eval lam := by
  have h2' : ((2 : ℕ) : L) ≠ 0 := by exact_mod_cast h2
  rw [levelRaiseReduction_discriminantPow K h2' t, reductionAtLevel_discriminantPow K t]
  set T : Test 2 L := ⟨legendrePair h2 h3 h0 h1, 1⟩ with hT
  have hsub : lam - 1 ≠ 0 := sub_ne_zero.mpr h1
  have h4 : (4 : L) ≠ 0 := by rw [show (4 : L) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have h16 : (16 : L) ≠ 0 := by rw [show (16 : L) = 4 * 4 by norm_num]; exact mul_ne_zero h4 h4
  have h64 : (64 : L) ≠ 0 := by rw [show (64 : L) = 4 * 16 by norm_num]; exact mul_ne_zero h4 h16
  have hD : discriminantRule T = 16 * lam ^ 2 * (lam - 1) ^ 2 := by
    rw [discriminantRule_apply, hT]
    simp only [Units.val_one, one_pow, inv_one, one_mul]
    rw [legendrePair_curve]
    exact legendreCurve_Δ h3 lam
  have hDne : discriminantRule T ≠ 0 := by
    rw [hD]; exact mul_ne_zero (mul_ne_zero h16 (pow_ne_zero _ h0)) (pow_ne_zero _ hsub)
  have hx : T.toPair.veluRatio = (lam - 1) ^ 2 / (4 * lam) / 64 := by
    have := xCoordinate_legendrePair h2 h3 h0 h1
    rw [Pair.xCoordinate_eq_mul_veluRatio] at this
    change (legendrePair h2 h3 h0 h1).veluRatio = _
    rw [← this]
    field_simp
  have hU : (((2 : ℕ) : L) ^ 12)⁻¹ * veluDiscriminantRule T = lam * (lam - 1) ^ 4 / 16 := by
    rw [← div_mul_cancel₀ ((((2 : ℕ) : L) ^ 12)⁻¹ * veluDiscriminantRule T) hDne,
      ← Pair.veluRatio_eq_div T, hx, hD]
    field_simp
    ring
  simp only [Pi.pow_apply]
  rw [hU, hD, legendreLevelRaiseSub]
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one, eval_ofNat]
  have e1 : (lam * (lam - 1) ^ 4 / 16) ^ t = lam ^ t * ((lam - 1) ^ (2 * t)) ^ 2 / 16 ^ t := by
    rw [div_pow, mul_pow, ← pow_mul, ← pow_mul, show 4 * t = 2 * t * 2 by ring]
  have e2 : (16 * lam ^ 2 * (lam - 1) ^ 2) ^ t = 16 ^ t * (lam ^ t) ^ 2 * (lam - 1) ^ (2 * t) := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm 2 t]
  have e3 : (256 : L) ^ t = (16 ^ t) ^ 2 := by
    rw [← pow_mul, mul_comm t 2, pow_mul]; norm_num
  rw [e1, e2, e3]
  have h16t : (16 : L) ^ t ≠ 0 := pow_ne_zero _ h16
  field_simp

/-- The Hasse invariant on the Legendre family: `A_p(T_λ) = (-1)^{(p-1)/2} H_p(λ)`
(Lemma 2.1(d)). -/
theorem hasseRule_legendre (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) {lam : L} (h0 : lam ≠ 0)
    (h1 : lam ≠ 1) :
    hasseRule p (⟨legendrePair h2 h3 h0 h1, 1⟩ : Test 2 L) =
      (-1) ^ ((p - 1) / 2) * (deuringPolynomial L p).eval lam := by
  have hp := (Fact.out : p.Prime)
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h2 (by exact_mod_cast CharP.cast_eq_zero L 2)
  rw [hasseRule_apply]
  simp only [Units.val_one, one_pow, inv_one, one_mul]
  rw [legendrePair_curve]
  exact legendreCurve_hasseCoeff hp hp2 h3 lam

omit [Fact p.Prime] [DecidableEq L] in
lemma coeff_deuringPolynomial_half (p : ℕ) :
    (deuringPolynomial L p).coeff ((p - 1) / 2) = 1 := by
  rw [deuringPolynomial, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single ((p - 1) / 2)]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h

omit [Fact p.Prime] [DecidableEq L] in
/-- For `p ≥ 5`, the Deuring polynomial `H_p` has a root `λ₀ ∉ {0, 1, -1}`: it is separable of
degree `(p - 1) / 2 ≥ 2` (cited: `Polynomial.DeuringPolynomialSeparable`), with `H_p(0) = 1` and
`H_p(1) ≠ 0`. -/
theorem exists_deuringPolynomial_isRoot_ne
    (hDeuringPolynomialSeparable : DeuringPolynomialSeparable.{u})
    [IsAlgClosed L] (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∃ lam : L, (deuringPolynomial L p).IsRoot lam ∧ lam ≠ 0 ∧ lam ≠ 1 ∧ lam ≠ -1 := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hsep := deuringPolynomial_separable (L := L) hDeuringPolynomialSeparable hp hp2
  have hcoeff := coeff_deuringPolynomial_half (L := L) p
  have hne : deuringPolynomial L p ≠ 0 := by
    intro h; rw [h, coeff_zero] at hcoeff; exact zero_ne_one hcoeff
  have hdeg : (p - 1) / 2 ≤ (deuringPolynomial L p).natDegree :=
    le_natDegree_of_ne_zero (by rw [hcoeff]; exact one_ne_zero)
  have hcard : (deuringPolynomial L p).roots.toFinset.card = (deuringPolynomial L p).natDegree := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree]
  obtain ⟨lam, hmem, hlam⟩ :=
    Finset.exists_mem_ne (s := (deuringPolynomial L p).roots.toFinset) (by omega) (-1 : L)
  rw [Multiset.mem_toFinset, mem_roots hne] at hmem
  refine ⟨lam, hmem, ?_, ?_, hlam⟩
  · rintro rfl
    rw [IsRoot, deuringPolynomial_eval_zero] at hmem
    exact one_ne_zero hmem
  · rintro rfl
    exact deuringPolynomial_eval_one_ne_zero hp hp2 hmem

/-- **Theorem 1.1(ii) at `ℓ = 2`, geometric form**. Let
`p ≥ 5`, `L` algebraically closed of characteristic `p`, `K` the Katz forms on `Γ₀(2)` over `L`
(regular on the Legendre family), `t = pⁿ t'` with `p ∤ t'`, and `j > pⁿ`. Then there is no
Katz form `H` (of any weight `k`) with `V₂(Δ̄ᵗ) - Δ̄ᵗ = A_p^j · H`. -/
theorem not_exists_hasse_pow_mul_eq_levelRaise_sub_two
    (hDeuringPolynomialSeparable : DeuringPolynomialSeparable.{u}) [IsAlgClosed L] (hp5 : 5 ≤ p)
    (K : KatzForms p 2 L) (hK : K.LegendreRegular) {n t' j : ℕ} (ht' : ¬ p ∣ t')
    (hj : p ^ n < j) (k : ℤ) :
    ¬ ∃ H ∈ K.form k,
      (levelRaiseReduction K (discriminantPow (p ^ n * t')) _
          (isIntegralQExpansion_discriminantPow _)).1 -
        (reductionAtLevel K (discriminantPow (p ^ n * t')) _
          (isIntegralQExpansion_discriminantPow _)).1 = hasseRule p ^ j * H := by
  rintro ⟨H, hH, hEq⟩
  have hp := (Fact.out : p.Prime)
  have h2 : (2 : L) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (L := L) (p := p) two_pos (by omega)
  have h3 : (3 : L) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_lt (L := L) (p := p) three_pos (by omega)
  have h256 : (256 : L) ≠ 0 := by
    rw [show (256 : L) = 2 ^ 8 by norm_num]; exact pow_ne_zero _ h2
  have ht'L : (t' : L) ≠ 0 := natCast_ne_zero_of_not_dvd ht'
  have ht'0 : t' ≠ 0 := by rintro rfl; exact ht' (dvd_zero p)
  set t := p ^ n * t' with ht
  obtain ⟨P, a, b, hP⟩ := hK.exists_eq_div hH h2 h3
  set Hp : L[X] := deuringPolynomial L p with hHp
  -- Step 3: the polynomial identity on the Legendre line.
  have hpoly : legendreLevelRaiseSub t * X ^ a * (X - 1) ^ b =
      C (((-1 : L) ^ ((p - 1) / 2)) ^ j) * Hp ^ j * P := by
    apply eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ (Set.toFinite ({0, 1} : Set L)).infinite_compl
    intro lam hlam
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hlam
    obtain ⟨h0, h1⟩ := hlam
    have e := congrFun hEq ⟨legendrePair h2 h3 h0 h1, 1⟩
    rw [Pi.sub_apply, levelRaiseReduction_sub_reductionAtLevel_legendre K h2 h3 t h0 h1,
      Pi.mul_apply, Pi.pow_apply, hasseRule_legendre h2 h3 h0 h1, hP lam h0 h1] at e
    simp only [Set.mem_ofPred_eq, eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C]
    rw [e, ← hHp]
    have hsub : lam - 1 ≠ 0 := sub_ne_zero.mpr h1
    field_simp
    ring
  -- Step 4: a supersingular parameter `λ₀ ∉ {0, 1, -1}`.
  obtain ⟨lam0, hroot, h00, h01, h0m1⟩ :=
    exists_deuringPolynomial_isRoot_ne (L := L) hDeuringPolynomialSeparable hp hp5
  -- Step 5: multiplicities at `λ₀`.
  set A : L[X] := C ((16 : L) ^ t)⁻¹ * X ^ (t + a) * (X - 1) ^ (2 * t + b) with hA
  have hfac : legendreLevelRaiseSub t * X ^ a * (X - 1) ^ b =
      A * legendreBranchPolynomial t' ^ p ^ n := by
    rw [legendreLevelRaiseSub, legendreBranchPolynomial, sub_pow_char_pow, hA, ht]
    ring
  have hAroot : ¬ A.IsRoot lam0 := by
    rw [IsRoot, hA]
    simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
    have h16 : (16 : L) ≠ 0 := by
      rw [show (16 : L) = 2 ^ 4 by norm_num]; exact pow_ne_zero _ h2
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero (pow_ne_zero _ h16)) (pow_ne_zero _ h00))
      (pow_ne_zero _ (sub_ne_zero.mpr h01))
  have hA0 : A ≠ 0 := by
    rintro h; apply hAroot; simp [h]
  have hG0 := legendreBranchPolynomial_ne_zero (L := L) ht'0
  have hne : A * legendreBranchPolynomial t' ^ p ^ n ≠ 0 := mul_ne_zero hA0 (pow_ne_zero _ hG0)
  have hle : rootMultiplicity lam0 (legendreLevelRaiseSub t * X ^ a * (X - 1) ^ b) ≤ p ^ n := by
    rw [hfac, rootMultiplicity_mul hne, rootMultiplicity_eq_zero hAroot, zero_add,
      rootMultiplicity_pow_of_ne_zero hG0]
    calc p ^ n * rootMultiplicity lam0 (legendreBranchPolynomial t') ≤ p ^ n * 1 :=
          Nat.mul_le_mul_left _
            (rootMultiplicity_legendreBranchPolynomial_le_one ht'L h256 h00 h01 h0m1)
      _ = p ^ n := mul_one _
  have hge : j ≤ rootMultiplicity lam0 (legendreLevelRaiseSub t * X ^ a * (X - 1) ^ b) := by
    rw [hpoly, le_rootMultiplicity_iff (hpoly ▸ hfac ▸ hne)]
    exact ((pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr hroot) j).mul_left _).mul_right _
  omega

/-- **Theorem 1.1(ii) at `ℓ = 2`** for `t = r pⁿ (p² - 1) / 12`, `p ∤ r`, `j > pⁿ`: there is no
Katz form `H` on `Γ₀(2)` of weight `12t - j (p - 1)` with `V₂(Δ̄ᵗ) - Δ̄ᵗ = A_p^j · H`. -/
theorem not_exists_hasse_pow_mul_eq_levelRaise_sub_two_of_eq
    (hDeuringPolynomialSeparable : DeuringPolynomialSeparable.{u}) [IsAlgClosed L] (hp5 : 5 ≤ p)
    (K : KatzForms p 2 L) (hK : K.LegendreRegular) {r n j t : ℕ} (hr : ¬ p ∣ r)
    (ht : t = r * p ^ n * ((p ^ 2 - 1) / 12)) (hj : p ^ n < j) :
    ¬ ∃ H ∈ K.form (12 * (t : ℤ) - j * ((p : ℤ) - 1)),
      (levelRaiseReduction K (discriminantPow t) _ (isIntegralQExpansion_discriminantPow t)).1 -
        (reductionAtLevel K (discriminantPow t) _ (isIntegralQExpansion_discriminantPow t)).1 =
          hasseRule p ^ j * H := by
  have hp := (Fact.out : p.Prime)
  have ht' : t = p ^ n * (r * ((p ^ 2 - 1) / 12)) := by rw [ht]; ring
  rw [ht']
  refine not_exists_hasse_pow_mul_eq_levelRaise_sub_two hDeuringPolynomialSeparable hp5 K hK ?_ hj _
  rw [hp.dvd_mul, not_or]
  exact ⟨hr, Nat.not_dvd_sq_sub_one_div_twelve hp hp5⟩

end Legendre

end KatzForms
