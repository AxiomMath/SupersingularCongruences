/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.LarsonConjecture
import all SupersingularCongruences.DividedBeta.Admissible
import all SupersingularCongruences.LevelOne.IntegralQExpansion
import all SupersingularCongruences.LevelOne.BehrensConditions

/-!
# The example of Section 2.1: two candidates for `(i, j) = (25, 25)` at `p = 5`

At `p = 5` and the admissible pair `(i, j) = (25, 25)` (so `t = 50`, weight `600`), both
`Δ⁵⁰` and `Δ⁵⁰ + E₄²⁴ Δ⁴²` satisfy Behrens' conditions (C1)–(C4), although their reductions
modulo `5` have `q`-orders `50` and `42` and so are not proportional [ono-manuscript, Section 2.1].
The argument is the manuscript's:

* (C1), (C2): `E₄ ≡ 1 (mod 5)`, so the reduction of `Δ⁵⁰ + E₄²⁴ Δ⁴²` is `Δ̄⁴² (1 + Δ̄⁸)`, of
  `q`-order `42`, and `12 · 42 = 504 > 600 - 4 · 25`.
* (C3): the correction term vanishes at supersingular curves, so the argument of Lemma 2.3
  applies. If `g` of weight `k' < 600` had the same reduction, then `A^{600 - k'} ḡ⁴` and `f̄⁴`
  (both of weight `2400`; `A = Ē₄` is the Hasse invariant) would have the same `q`-expansion, hence
  be equal Katz forms; at a supersingular test object the first vanishes while the second is
  `(Δ⁵⁰)⁴ ≠ 0`. Raising to the fourth power makes the two weights congruent modulo `p - 1 = 4`;
  the manuscript obtains this congruence from the theory of Serre and Swinnerton-Dyer
  [swinnerton-dyer1973], which is not needed here.
* (C4): `V_ℓ A = A` by the `q`-expansion principle, and Proposition 5.4 for `(i, n, j) = (21, 0, 1)`
  gives `A ∣ L_ℓ(Δ⁴²)`, so `L_ℓ(A²⁴ Δ⁴²) = A²⁴ L_ℓ(Δ⁴²)` is divisible by `A²⁵`; Proposition 5.4
  for `(25, 2, 25)` gives `A²⁵ ∣ L_ℓ(Δ⁵⁰)`.
* The reduction of `E₄²⁴ Δ⁴²` is not divisible by `A²⁵` in the ring of Katz forms: cancel `A²⁴`
  and evaluate at a supersingular test object.

That the two forms then give distinct elements of Behrens' group of congruences, and so
correspond to different classes of order `5` on the `2`-line [behrens-laures2009, Section 3], is
a statement about that group and is not formalized.

## Main results

* `LevelOne.correctedDiscriminant_satisfiesBehrensConditions`,
  `LevelOne.discriminantPow_fifty_satisfiesBehrensConditions`: both forms satisfy (C1)–(C4).
* `LevelOne.order_reduction_correctedQExp`, `LevelOne.not_proportional_reduction_correctedQExp`:
  the `q`-orders `42` and `50`, and non-proportionality of the reductions.
* `LevelOne.not_exists_hasse_pow_mul_eq_reduction_correction`: `A²⁵ ∤ E₄²⁴ Δ⁴²` modulo `5`.
-/

public section

open Gamma0 KatzForms PowerSeries ModularForm
open scoped MatrixGroups

universe u

namespace LevelOne

/-- `5` is prime. -/
instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The pair `(i, j) = (25, 25)` is admissible at `p = 5` [larson2020, Example 2.3]. -/
theorem isAdmissible_twentyFive : DividedBeta.IsAdmissible 5 25 25 := by
  have h : padicValNat 5 25 = 2 := by
    rw [show (25 : ℕ) = 5 ^ 2 by norm_num, padicValNat.prime_pow]
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · rw [h]; norm_num
  · intro c _ _ hcb
    rw [h] at hcb
    rw [Nat.sub_self, DividedBeta.bIndex_zero] at hcb
    omega

/-- The correction term `E₄²⁴ Δ⁴²` of the example, of weight `600 = 12 · 50`. -/
noncomputable def eisensteinCorrection : ModularForm 𝒮ℒ (12 * (50 : ℕ)) :=
  ModularForm.mcast (by norm_num) ((ModularForm.E₄.pow 24).mul (discriminantPow 42))

/-- The integral `q`-expansion `E₄²⁴ Δ⁴²` of the correction term. -/
noncomputable def correctionQExp : PowerSeries ℤ := integralE₄ ^ 24 * integralDiscriminant ^ 42

theorem isIntegralQExpansion_eisensteinCorrection :
    IsIntegralQExpansion correctionQExp eisensteinCorrection := by
  rw [eisensteinCorrection, coe_mcast]
  exact isIntegralQExpansion_mul (isIntegralQExpansion_pow isIntegralQExpansion_E₄ 24)
    (isIntegralQExpansion_discriminantPow 42)

/-- The form `Δ⁵⁰ + E₄²⁴ Δ⁴²` of weight `600`. -/
noncomputable def correctedDiscriminant : ModularForm 𝒮ℒ (12 * (50 : ℕ)) :=
  discriminantPow 50 + eisensteinCorrection

/-- Its integral `q`-expansion. -/
noncomputable def correctedQExp : PowerSeries ℤ := integralDiscriminant ^ 50 + correctionQExp

theorem isIntegralQExpansion_correctedDiscriminant :
    IsIntegralQExpansion correctedQExp correctedDiscriminant :=
  isIntegralQExpansion_add (isIntegralQExpansion_discriminantPow 50)
    isIntegralQExpansion_eisensteinCorrection

/-- `E₄ ≡ 1 (mod 5)`: `240 ≡ 0 (mod 5)`. -/
lemma map_integralE₄_eq_one (R : Type*) [CommRing R] [CharP R 5] :
    PowerSeries.map (Int.castRingHom R) integralE₄ = 1 := by
  have h240 : ((240 : ℤ) : R) = 0 := by
    rw [CharP.intCast_eq_zero_iff R 5]
    norm_num
  ext n
  rcases n with _ | n
  · simp [integralE₄, coeff_one]
  · simp only [coeff_map, integralE₄, coeff_mk, coeff_one]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, eq_intCast, Int.cast_mul]
    rw [h240, zero_mul]

/-- The reduction modulo `5` of `Δ⁵⁰ + E₄²⁴ Δ⁴²` is `Δ̄⁵⁰ + Δ̄⁴²`. -/
lemma map_correctedQExp (R : Type*) [CommRing R] [CharP R 5] :
    PowerSeries.map (Int.castRingHom R) correctedQExp =
      PowerSeries.map (Int.castRingHom R) integralDiscriminant ^ 50 +
        PowerSeries.map (Int.castRingHom R) integralDiscriminant ^ 42 := by
  rw [correctedQExp, correctionQExp, map_add, map_mul, map_pow, map_pow, map_pow,
    map_integralE₄_eq_one, one_pow, one_mul]

/-- The reduction of `Δ⁵⁰ + E₄²⁴ Δ⁴²` modulo `5` has `q`-order `42`. -/
theorem order_reduction_correctedQExp :
    (PowerSeries.map (Int.castRingHom (ZMod 5)) correctedQExp).order = 42 := by
  set D := PowerSeries.map (Int.castRingHom (ZMod 5)) integralDiscriminant
  have hfac : PowerSeries.map (Int.castRingHom (ZMod 5)) correctedQExp = D ^ 42 * (1 + D ^ 8) := by
    rw [map_correctedQExp]
    ring
  have hD : D.order = 1 := order_reduction_integralDiscriminant
  have h1 : (1 + D ^ 8).order = 0 := by
    rw [show (0 : ℕ∞) = (0 : ℕ) from rfl, order_eq_nat]
    refine ⟨?_, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
    have hc : constantCoeff D = 0 := by
      simp [D, ← coeff_zero_eq_constantCoeff_apply, coeff_zero_integralDiscriminant]
    rw [coeff_zero_eq_constantCoeff_apply, map_add, map_pow, hc]
    simp
  rw [hfac, order_mul, order_pow, hD, h1]
  rfl

/-- The reduction of `Δ⁵⁰` has `q`-order `50`, that of `Δ⁵⁰ + E₄²⁴ Δ⁴²` has `q`-order `42`, and
neither reduction is a scalar multiple of the other. -/
theorem not_proportional_reduction_correctedQExp :
    (PowerSeries.map (Int.castRingHom (ZMod 5)) (integralDiscriminant ^ 50)).order = 50 ∧
      (PowerSeries.map (Int.castRingHom (ZMod 5)) correctedQExp).order = 42 ∧
      (¬ ∃ c : ZMod 5, PowerSeries.map (Int.castRingHom (ZMod 5)) correctedQExp =
          c • PowerSeries.map (Int.castRingHom (ZMod 5)) (integralDiscriminant ^ 50)) ∧
      ¬ ∃ c : ZMod 5, PowerSeries.map (Int.castRingHom (ZMod 5)) (integralDiscriminant ^ 50) =
          c • PowerSeries.map (Int.castRingHom (ZMod 5)) correctedQExp := by
  set F := PowerSeries.map (Int.castRingHom (ZMod 5)) correctedQExp
  set D := PowerSeries.map (Int.castRingHom (ZMod 5)) (integralDiscriminant ^ 50)
  have hD : D.order = 50 := order_reduction_integralDiscriminant_pow 50
  have hF : F.order = 42 := order_reduction_correctedQExp
  have hD42 : D.coeff 42 = 0 := coeff_of_lt_order 42 (by rw [hD]; norm_num)
  have hF0 : F ≠ 0 := by intro h; rw [h, order_zero] at hF; exact ENat.top_ne_ofNat 42 hF
  have hF42 : F.coeff 42 ≠ 0 := by
    have := coeff_order hF0
    rwa [hF] at this
  refine ⟨hD, hF, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    apply hF42
    rw [hc, coeff_smul, hD42, smul_zero]
  · rintro ⟨c, hc⟩
    have h42 := congrArg (coeff 42) hc
    rw [coeff_smul, hD42, smul_eq_mul] at h42
    have hc0 : c = 0 := (mul_eq_zero.mp h42.symm).resolve_right hF42
    rw [hc0, zero_smul] at hc
    exact reduction_integralDiscriminant_pow_ne_zero 50 hc

/-- (C1) for `Δ⁵⁰ + E₄²⁴ Δ⁴²` at `p = 5`. -/
theorem behrensC1_correctedQExp : BehrensC1 5 correctedQExp := by
  intro h
  have := order_reduction_correctedQExp
  rw [h, order_zero] at this
  exact ENat.top_ne_ofNat 42 this

/-- (C2) for `Δ⁵⁰ + E₄²⁴ Δ⁴²` and `j = 25` at `p = 5`: `12 · 42 = 504 > 600 - 4 · 25`. -/
theorem behrensC2_correctedQExp : BehrensC2 5 50 25 correctedQExp := by
  left
  rw [order_reduction_correctedQExp]
  norm_num

section Katz

variable {L : Type*} [Field L] [DecidableEq L] [CharP L 5]

lemma two_ne_zero_five : (2 : L) ≠ 0 := by
  intro h
  have := (CharP.cast_eq_zero_iff L 5 2).mp (by exact_mod_cast h)
  norm_num at this

lemma three_ne_zero_five : (3 : L) ≠ 0 := by
  intro h
  have := (CharP.cast_eq_zero_iff L 5 3).mp (by exact_mod_cast h)
  norm_num at this

/-- A supersingular test object on `Γ₀(2)` over `L` at `p = 5`: the Legendre curve at a root of
`H₅(λ) = 1 + 4 λ + λ²`. -/
theorem exists_test_hasseRule_eq_zero [IsAlgClosed L] :
    ∃ T : Test 2 L, hasseRule 5 T = 0 := by
  have hcoeff := KatzForms.coeff_deuringPolynomial_half (L := L) 5
  have hdeg : 0 < (Polynomial.deuringPolynomial L 5).natDegree :=
    lt_of_lt_of_le (by norm_num) (Polynomial.le_natDegree_of_ne_zero (n := (5 - 1) / 2)
      (by rw [hcoeff]; exact one_ne_zero))
  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_root (Polynomial.deuringPolynomial L 5)
    (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hdeg))
  have h0 : lam ≠ 0 := by
    rintro rfl
    rw [Polynomial.IsRoot, Polynomial.deuringPolynomial_eval_zero] at hlam
    exact one_ne_zero hlam
  have h1 : lam ≠ 1 := by
    rintro rfl
    exact Polynomial.deuringPolynomial_eval_one_ne_zero Nat.prime_five (by norm_num) hlam
  refine ⟨⟨legendrePair two_ne_zero_five three_ne_zero_five h0 h1, 1⟩, ?_⟩
  rw [KatzForms.hasseRule_legendre two_ne_zero_five three_ne_zero_five h0 h1, hlam.eq_zero,
    mul_zero]

variable {ℓ : ℕ}

lemma discriminantRule_ne_zero (T : Test ℓ L) : discriminantRule T ≠ 0 := by
  rw [discriminantRule_apply]
  exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ T.diff.ne_zero)) T.curve.isUnit_Δ.ne_zero

variable (K : KatzForms 5 ℓ L)

lemma hasse_mem_four : hasseRule 5 ∈ K.form 4 := K.mem_form_of_eq (by norm_num) K.hasse_mem

lemma qExp_hasse_four : K.qExp 4 ⟨hasseRule 5, hasse_mem_four K⟩ = 1 :=
  (K.qExp_congr (by norm_num) rfl (hasse_mem_four K) K.hasse_mem).trans K.qExp_hasse

/-- The `q`-expansion of `A^a · f` for a form `f`. -/
lemma qExp_discriminantRule_pow (t : ℕ) {k : ℤ} (hk : (t : ℤ) * 12 = k)
    (h : discriminantRule ^ t ∈ K.form k) :
    K.qExp k ⟨discriminantRule ^ t, h⟩ =
      PowerSeries.map (Int.castRingHom L) integralDiscriminant ^ t := by
  rw [← K.qExp_congr hk rfl (K.pow_mem K.discriminant_mem t) h, K.qExp_pow K.discriminant_mem t,
    K.qExp_discriminant]

lemma qExp_hasse_pow_mul {k : ℤ} (a : ℕ) {f : Test ℓ L → L} (hf : f ∈ K.form k) {k' : ℤ}
    (hk : (a : ℤ) * 4 + k = k') (h : hasseRule 5 ^ a * f ∈ K.form k') :
    K.qExp k' ⟨hasseRule 5 ^ a * f, h⟩ = K.qExp k ⟨f, hf⟩ := by
  rw [K.qExp_mul_of_eq hk (K.pow_mem (hasse_mem_four K) a) hf h, K.qExp_pow (hasse_mem_four K) a,
    qExp_hasse_four,
    one_pow, one_mul]

/-- The reduction of `Δ⁵⁰ + E₄²⁴ Δ⁴²` on `Γ₀(ℓ)` is the rule `Δ⁵⁰ + A²⁴ Δ⁴²`. -/
theorem reductionAtLevel_correctedDiscriminant :
    (reductionAtLevel K correctedDiscriminant correctedQExp
        isIntegralQExpansion_correctedDiscriminant).1 =
      discriminantRule ^ 50 + hasseRule 5 ^ 24 * discriminantRule ^ 42 := by
  have h50 := K.discriminant_pow_mem 50
  have h42 := K.discriminant_pow_mem 42
  have hc : hasseRule 5 ^ 24 * discriminantRule ^ 42 ∈ K.form (12 * (50 : ℕ)) :=
    K.mul_mem_of_eq (by norm_num) (K.pow_mem (hasse_mem_four K) 24) h42
  have hsum : discriminantRule ^ 50 + hasseRule 5 ^ 24 * discriminantRule ^ 42 ∈
      K.form (12 * (50 : ℕ)) := (K.form _).add_mem h50 hc
  refine K.eq_of_qExp_eq (reductionAtLevel K _ _ _).2 hsum ?_
  rw [qExp_reductionAtLevel, map_correctedQExp, K.qExp_add h50 hc,
    qExp_hasse_pow_mul K 24 h42 (by norm_num) hc]
  rw [qExp_discriminantRule_pow K 50 (by norm_num), qExp_discriminantRule_pow K 42 (by norm_num)]

/-- The rule `V = ℓ⁻¹² Δ(E / C, ω')` of Lemma 4.1. -/
noncomputable abbrev veluRule : Test ℓ L → L := fun T ↦ ((ℓ : L) ^ 12)⁻¹ * veluDiscriminantRule T

lemma veluRule_pow_mem (t : ℕ) : veluRule ^ t ∈ K.form (12 * (t : ℕ)) :=
  K.mem_form_of_eq (by ring) (K.pow_mem (K.normalizedVeluDiscriminant_mem (ℓ := ℓ)) t)

lemma qExp_veluRule_pow [NeZero ℓ] (hℓ : (ℓ : L) ≠ 0) (t : ℕ) :
    K.qExp _ ⟨veluRule ^ t, veluRule_pow_mem K t⟩ =
      expandSeries ℓ (PowerSeries.map (Int.castRingHom L) integralDiscriminant) ^ t := by
  rw [← K.qExp_congr (by ring) rfl (K.pow_mem (K.normalizedVeluDiscriminant_mem (ℓ := ℓ)) t)
    (veluRule_pow_mem K t), K.qExp_pow K.normalizedVeluDiscriminant_mem t,
    K.qExp_normalizedVeluDiscriminant hℓ]

/-- The reduction of `V_ℓ(Δ⁵⁰ + E₄²⁴ Δ⁴²)` on `Γ₀(ℓ)` is the rule `V⁵⁰ + A²⁴ V⁴²`
(`V_ℓ A = A` by the `q`-expansion principle). -/
theorem levelRaiseReduction_correctedDiscriminant [NeZero ℓ] (hℓ : (ℓ : L) ≠ 0) :
    (levelRaiseReduction K correctedDiscriminant correctedQExp
        isIntegralQExpansion_correctedDiscriminant).1 =
      veluRule ^ 50 + hasseRule 5 ^ 24 * veluRule ^ 42 := by
  have h42 := veluRule_pow_mem K 42
  have hc : hasseRule 5 ^ 24 * veluRule ^ 42 ∈ K.form (12 * (50 : ℕ)) :=
    K.mul_mem_of_eq (by norm_num) (K.pow_mem (hasse_mem_four K) 24) h42
  have hsum : veluRule ^ 50 + hasseRule 5 ^ 24 * veluRule ^ 42 ∈ K.form (12 * (50 : ℕ)) :=
    (K.form _).add_mem (veluRule_pow_mem K 50) hc
  refine K.eq_of_qExp_eq (levelRaiseReduction K _ _ _).2 hsum ?_
  rw [qExp_levelRaiseReduction, map_correctedQExp, expandSeries_add, expandSeries_pow
    (NeZero.ne ℓ), expandSeries_pow (NeZero.ne ℓ), K.qExp_add (veluRule_pow_mem K 50) hc,
    qExp_hasse_pow_mul K 24 h42 (by norm_num) hc, qExp_veluRule_pow K hℓ,
    qExp_veluRule_pow K hℓ]

/-- The reduction of `E₄²⁴ Δ⁴²` on `Γ₀(ℓ)` is the rule `A²⁴ Δ⁴²`. -/
theorem reductionAtLevel_eisensteinCorrection :
    (reductionAtLevel K eisensteinCorrection correctionQExp
        isIntegralQExpansion_eisensteinCorrection).1 =
      hasseRule 5 ^ 24 * discriminantRule ^ 42 := by
  have h42 := K.discriminant_pow_mem 42
  have hc : hasseRule 5 ^ 24 * discriminantRule ^ 42 ∈ K.form (12 * (50 : ℕ)) :=
    K.mul_mem_of_eq (by norm_num) (K.pow_mem (hasse_mem_four K) 24) h42
  refine K.eq_of_qExp_eq (reductionAtLevel K _ _ _).2 hc ?_
  rw [qExp_reductionAtLevel, qExp_hasse_pow_mul K 24 h42 (by norm_num) hc, correctionQExp,
    map_mul, map_pow, map_pow, map_integralE₄_eq_one, one_pow, one_mul,
    qExp_discriminantRule_pow K 42 (by norm_num)]

/-- **`A²⁵ ∤ E₄²⁴ Δ⁴²` modulo `5`** [ono-manuscript, Section 2.1]: in the ring of Katz forms on
`Γ₀(2)` over `L`, the reduction of `E₄²⁴ Δ⁴²` is not `A²⁵ H` for any form `H`. -/
theorem not_exists_hasse_pow_mul_eq_reduction_correction [IsAlgClosed L]
    (K : KatzForms 5 2 L) :
    ¬ ∃ H ∈ K.form (12 * (50 : ℕ) - 25 * ((5 : ℕ) - 1 : ℤ)),
      (reductionAtLevel K eisensteinCorrection correctionQExp
        isIntegralQExpansion_eisensteinCorrection).1 = hasseRule 5 ^ 25 * H := by
  rintro ⟨H, hH, hEq⟩
  rw [reductionAtLevel_eisensteinCorrection] at hEq
  obtain ⟨T, hT⟩ := exists_test_hasseRule_eq_zero (L := L)
  have hA : hasseRule 5 ^ 24 ≠ (0 : Test 2 L → L) := by
    intro h
    apply K.hasseRule_ne_zero
    funext T'
    exact pow_eq_zero_iff (n := 24) (by norm_num) |>.mp (congrFun h T')
  have hAH : hasseRule 5 * H ∈ K.form (12 * 42) :=
    K.mul_mem_of_eq (by norm_num) (hasse_mem_four K) hH
  have hprod : hasseRule 5 ^ 24 * (discriminantRule ^ 42 - hasseRule 5 * H) = 0 := by
    rw [mul_sub, hEq]
    ring
  rcases K.eq_zero_or_eq_zero_of_mul_eq_zero (K.pow_mem (hasse_mem_four K) 24)
    (sub_mem (K.discriminant_pow_mem 42) hAH) hprod with h | h
  · exact hA h
  · have h' := congrFun h T
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, hT, zero_mul, sub_zero,
      Pi.zero_apply] at h'
    exact discriminantRule_ne_zero T (pow_eq_zero_iff (by norm_num) |>.mp h')

/-- (C3) for `Δ⁵⁰ + E₄²⁴ Δ⁴²` at `p = 5`, by the argument of Lemma 2.3. -/
theorem behrensC3_correctedQExp [IsAlgClosed L] (K : KatzForms 5 2 L) :
    BehrensC3 5 50 correctedQExp := by
  intro k' hk' g H hH heq
  obtain ⟨T, hT⟩ := exists_test_hasseRule_eq_zero (L := L)
  set e := (600 - k').toNat with he
  have he' : (e : ℤ) = 600 - k' := Int.toNat_of_nonneg (by push_cast at hk'; omega)
  have he1 : e ≠ 0 := by omega
  set gr := reductionAtLevel K g H hH
  set fr := reductionAtLevel K correctedDiscriminant correctedQExp
    isIntegralQExpansion_correctedDiscriminant
  have hg4 := K.pow_mem gr.2 4
  have hf4 := K.pow_mem fr.2 4
  have hF1 : hasseRule 5 ^ e * gr.1 ^ 4 ∈ K.form ((4 : ℕ) * (12 * (50 : ℕ))) :=
    K.mul_mem_of_eq (by push_cast; linarith) (K.pow_mem (hasse_mem_four K) e) hg4
  -- The reductions of `H` and `G` agree in `L`.
  have hHG : PowerSeries.map (Int.castRingHom L) H =
      PowerSeries.map (Int.castRingHom L) correctedQExp := by
    ext n
    have := congrArg (fun F ↦ ZMod.castHom (dvd_refl 5) L (coeff n F)) heq
    simpa [coeff_map] using this
  have hq : K.qExp _ ⟨_, hF1⟩ = K.qExp _ ⟨_, hf4⟩ := by
    rw [qExp_hasse_pow_mul K e hg4 (by push_cast; linarith) hF1, K.qExp_pow, K.qExp_pow]
    change K.qExp k' gr ^ 4 = K.qExp _ fr ^ 4
    rw [qExp_reductionAtLevel, qExp_reductionAtLevel, hHG]
  have h := congrFun (K.eq_of_qExp_eq hF1 hf4 hq) T
  rw [show fr.1 = _ from reductionAtLevel_correctedDiscriminant K] at h
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, hT, zero_pow he1, zero_mul,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h
  exact discriminantRule_ne_zero T (pow_eq_zero_iff (n := 200) (by norm_num) |>.mp
    (by rw [← pow_mul] at h; exact h.symm))

end Katz

variable {L : Type u} [Field L] [DecidableEq L] [CharP L 5] [IsAlgClosed L]

/-- (C4) for `Δ⁵⁰ + E₄²⁴ Δ⁴²` and `j = 25` at `p = 5`, at every prime `ℓ ≠ 5`. -/
theorem behrensC4_correctedDiscriminant
    (hGonzalezDivisionPolynomial : WeierstrassCurve.GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : WeierstrassCurve.GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : WeierstrassCurve.SupersingularJInvariant.{u})
    (hVeluIsogeny : WeierstrassCurve.VeluIsogeny.{u})
    (hDeuringHasseCriterion : WeierstrassCurve.DeuringHasseCriterion.{u})
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ 5 ^ k = x)
    (K : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 5 → KatzForms 5 ℓ L)
    (Y : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ 5), LevelCover (K ℓ hℓ hℓp)) :
    BehrensC4 K 50 25 correctedDiscriminant correctedQExp
      isIntegralQExpansion_correctedDiscriminant := by
  rw [behrensC4_iff]
  intro ℓ hℓ hℓp
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hℓL : (ℓ : L) ≠ 0 := natCast_ne_zero_of_prime (L := L) hℓ hℓp
  set Kℓ := K ℓ hℓ hℓp
  obtain ⟨H₁, hH₁, hg₁, hE₁⟩ := exists_hasse_pow_mul_eq_levelRaise_sub hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hSupersingularJInvariant hVeluIsogeny hDeuringHasseCriterion
    (by norm_num) hL hℓ hℓp Kℓ (Y ℓ hℓ hℓp) (r := 1) (n := 2) (j := 25) (t := 50) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨H₂, hH₂, hg₂, hE₂⟩ := exists_hasse_pow_mul_eq_levelRaise_sub hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hSupersingularJInvariant hVeluIsogeny hDeuringHasseCriterion
    (by norm_num) hL hℓ hℓp Kℓ (Y ℓ hℓ hℓp) (r := 21) (n := 0) (j := 1) (t := 42) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  rw [levelRaiseReduction_discriminantPow (L := L) Kℓ hℓL,
    reductionAtLevel_discriminantPow (L := L)] at hE₁ hE₂
  refine ⟨H₁ + H₂, add_mem (Kℓ.mem_form_of_eq (by norm_num) hH₁)
    (Kℓ.mem_form_of_eq (by norm_num) hH₂), hg₁.add hg₂, ?_⟩
  rw [levelRaiseReduction_correctedDiscriminant (L := L) Kℓ hℓL,
    reductionAtLevel_correctedDiscriminant (L := L)]
  have e : (veluRule : Test ℓ L → L) ^ 50 + hasseRule 5 ^ 24 * veluRule ^ 42 -
      (discriminantRule ^ 50 + hasseRule 5 ^ 24 * discriminantRule ^ 42) =
      (veluRule ^ 50 - discriminantRule ^ 50) +
        hasseRule 5 ^ 24 * (veluRule ^ 42 - discriminantRule ^ 42) := by ring
  rw [e, hE₁, hE₂]
  ring

/-- **The example of Section 2.1**: at `p = 5` and `(i, j) = (25, 25)`, the form
`Δ⁵⁰ + E₄²⁴ Δ⁴²` satisfies Behrens' conditions (C1)–(C4). -/
theorem correctedDiscriminant_satisfiesBehrensConditions
    (hGonzalezDivisionPolynomial : WeierstrassCurve.GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : WeierstrassCurve.GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : WeierstrassCurve.SupersingularJInvariant.{u})
    (hVeluIsogeny : WeierstrassCurve.VeluIsogeny.{u})
    (hDeuringHasseCriterion : WeierstrassCurve.DeuringHasseCriterion.{u})
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ 5 ^ k = x)
    (K : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 5 → KatzForms 5 ℓ L)
    (Y : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ 5), LevelCover (K ℓ hℓ hℓp)) :
    SatisfiesBehrensConditions K 50 25 correctedDiscriminant correctedQExp where
  isIntegralQExpansion := isIntegralQExpansion_correctedDiscriminant
  c1 := behrensC1_correctedQExp
  c2 := behrensC2_correctedQExp
  c3 := behrensC3_correctedQExp (K 2 Nat.prime_two (by norm_num))
  c4 := behrensC4_correctedDiscriminant hGonzalezDivisionPolynomial hGonzalezMultiplicationByP
    hSupersingularJInvariant hVeluIsogeny hDeuringHasseCriterion hL K Y

/-- **The example of Section 2.1**: at `p = 5` and `(i, j) = (25, 25)`, the pure power `Δ⁵⁰`
satisfies Behrens' conditions (C1)–(C4) (Theorem 1.1(i) with `r = 1`, `n = 2`). -/
theorem discriminantPow_fifty_satisfiesBehrensConditions
    (hGonzalezDivisionPolynomial : WeierstrassCurve.GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : WeierstrassCurve.GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : WeierstrassCurve.SupersingularJInvariant.{u})
    (hVeluIsogeny : WeierstrassCurve.VeluIsogeny.{u})
    (hDeuringHasseCriterion : WeierstrassCurve.DeuringHasseCriterion.{u})
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ 5 ^ k = x)
    (K : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 5 → KatzForms 5 ℓ L)
    (Y : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ 5), LevelCover (K ℓ hℓ hℓp)) :
    SatisfiesBehrensConditions K 50 25 (discriminantPow 50) (integralDiscriminant ^ 50) :=
  discriminantPow_satisfiesBehrensConditions_of_eq hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hSupersingularJInvariant hVeluIsogeny
    hDeuringHasseCriterion (by norm_num) hL K Y (r := 1) (n := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end LevelOne
