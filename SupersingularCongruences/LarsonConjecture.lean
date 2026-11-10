/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.KatzForms.EveryLevel
public import SupersingularCongruences.LevelTwo.GeometricFailure
public import SupersingularCongruences.DividedBeta.Admissible
public import SupersingularCongruences.External

/-!
# Theorem 1.1 and Larson's conjecture

Let `p ≥ 5` be prime, `L` an algebraic closure of `𝔽_p`, `i = r pⁿ` with `p ∤ r`, and
`t = i (p² - 1) / 12`. Behrens' conditions (C1)–(C4) for `Δᵗ` and the index `j` are
`LevelOne.SatisfiesBehrensConditions K t j (discriminantPow t) (integralDiscriminant ^ t)`, where
(C4) is read in the geometric rings of Katz forms modulo `p` on `Γ₀(ℓ)`, supplied by
`K ℓ : KatzForms p ℓ L` for every prime `ℓ ≠ p` (with level covers `Y ℓ` and, at `ℓ = 2`,
regularity on the Legendre family).

## Main results

* `LevelOne.discriminantPow_satisfiesBehrensConditions`: **Theorem 1.1(i)**: for admissible
  `j ≤ pⁿ`, `Δᵗ` satisfies (C1)–(C4) (a candidate `f_{i/j}` in Larson's convention).
* `LevelOne.not_behrensC4_discriminantPow`: **Theorem 1.1(ii)** (and Remark 1.2): for every
  `j > pⁿ`, admissible or not, `Δᵗ` fails (C4), already at `ℓ = 2`.
* `LevelOne.not_behrensC4_discriminantPow_of_isAdmissible`: Theorem 1.1(ii) with its
  parenthetical claim: admissible `j > pⁿ` force `r > 1` and `n ≥ 2`; conversely such `j` exist
  when `r > 1`, `n ≥ 2` (`DividedBeta.exists_isAdmissible_gt_iff`).
* `LevelOne.discriminantPow_satisfiesBehrensConditions_iff`: **Larson's conjecture**
  [larson2020, Conjecture 5.21 of arXiv:1906.08906v1 (5.17 in the published numbering)]: for every
  admissible `j`, `Δᵗ` satisfies (C1)–(C4) iff `j ≤ pⁿ`.
* `LevelOne.discriminantPow_behrensC4_iff`, `LevelOne.not_behrensC4_discriminantPow_pow`:
  **Remark 1.2**: without admissibility, (C4) for `Δᵗ` holds iff `1 ≤ j ≤ pⁿ`; in particular it
  fails for `r = 1`, `n ≥ 2` and `pⁿ < j ≤ pⁿ + pⁿ⁻¹ - 1`.

## Proof

(i) combines Lemma 5.5 (`LevelOne.discriminantPow_satisfiesBehrensC123_of_isAdmissible`) with
Proposition 5.4 at every level (`KatzForms.discriminantPow_behrensC4`); the two expressions
`i (p² - 1) / 12` and `r pⁿ ((p² - 1) / 12)` for `t` agree since `12 ∣ p² - 1`.
(ii) is the failure of the divisibility at `ℓ = 2`
(`KatzForms.not_exists_hasse_pow_mul_eq_levelRaise_sub_two_of_eq`), proved directly in the
geometric ring by an order count on the Legendre family. This replaces the manuscript's route via
Proposition 5.3 in Larson's ring `𝔽_p[δ, ε]` and Remark 5.2 (the identification of the geometric
ring at level `2` with `𝔽_p[δ, ε]`), of which only the injective half is formalized
(`KatzForms.larsonToForm_injective`).
-/

public section

open Gamma0

universe u

namespace LevelOne

variable {p : ℕ} [Fact p.Prime] {L : Type u} [Field L] [DecidableEq L] [CharP L p]

omit [Fact p.Prime] in
/-- `i (p² - 1) / 12 = i ((p² - 1) / 12)` for a prime `p ≥ 5`. -/
lemma mul_sq_sub_one_div_twelve (hp : p.Prime) (hp5 : 5 ≤ p) (i : ℕ) :
    i * (p ^ 2 - 1) / 12 = i * ((p ^ 2 - 1) / 12) :=
  Nat.mul_div_assoc i (Nat.twelve_dvd_sq_sub_one hp hp5)

/-- (C1)–(C4) for `Δᵗ`, `t = r pⁿ (p² - 1) / 12`, `1 ≤ j ≤ pⁿ` (no admissibility needed). -/
theorem discriminantPow_satisfiesBehrensConditions_of_eq
    (hGonzalezDivisionPolynomial : WeierstrassCurve.GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : WeierstrassCurve.GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : WeierstrassCurve.SupersingularJInvariant.{u})
    (hVeluIsogeny : WeierstrassCurve.VeluIsogeny.{u})
    (hDeuringHasseCriterion : WeierstrassCurve.DeuringHasseCriterion.{u})
    [IsAlgClosed L] (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (K : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → KatzForms p ℓ L)
    (Y : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p), LevelCover (K ℓ hℓ hℓp)) {r n j t : ℕ}
    (hr : ¬ p ∣ r) (ht : t = r * p ^ n * ((p ^ 2 - 1) / 12)) (hj1 : 1 ≤ j) (hjn : j ≤ p ^ n) :
    SatisfiesBehrensConditions K t j (discriminantPow t) (integralDiscriminant ^ t) := by
  subst ht
  exact ⟨discriminantPow_satisfiesBehrensC123 _ hj1,
    KatzForms.discriminantPow_behrensC4 hGonzalezDivisionPolynomial hGonzalezMultiplicationByP
      hSupersingularJInvariant hVeluIsogeny hDeuringHasseCriterion hp5 hL K Y hr hj1 hjn⟩

/-- **Theorem 1.1(i)**. Let `p ≥ 5`, `L` an algebraic closure of `𝔽_p`, `p ∤ r`,
`i = r pⁿ`, `t = i (p² - 1) / 12`, and let `j` be admissible for `β_{i/j}` with `j ≤ pⁿ`. Then
`Δᵗ` satisfies Behrens' conditions (C1)–(C4): it is a candidate `f_{i/j}` in Larson's
convention. -/
theorem discriminantPow_satisfiesBehrensConditions
    (hcited : CitedResults.{u}) [IsAlgClosed L] (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (K : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → KatzForms p ℓ L)
    (Y : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p), LevelCover (K ℓ hℓ hℓp)) {r n j : ℕ}
    (hr : ¬ p ∣ r) (hadm : DividedBeta.IsAdmissible p (r * p ^ n) j) (hjn : j ≤ p ^ n) :
    SatisfiesBehrensConditions K (r * p ^ n * (p ^ 2 - 1) / 12) j
      (discriminantPow (r * p ^ n * (p ^ 2 - 1) / 12))
      (integralDiscriminant ^ (r * p ^ n * (p ^ 2 - 1) / 12)) :=
  discriminantPow_satisfiesBehrensConditions_of_eq hcited.gonzalezDivisionPolynomial
    hcited.gonzalezMultiplicationByP hcited.supersingularJInvariant hcited.veluIsogeny
    hcited.deuringHasseCriterion hp5 hL K Y hr
    (mul_sq_sub_one_div_twelve Fact.out hp5 _) hadm.one_le_right hjn

/-- Failure of (C4) at `ℓ = 2` for `t = r pⁿ (p² - 1) / 12` and `j > pⁿ`. -/
theorem not_behrensC4_discriminantPow_of_eq
    (hDeuringPolynomialSeparable : Polynomial.DeuringPolynomialSeparable.{u})
    [IsAlgClosed L] (hp5 : 5 ≤ p)
    (K : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → KatzForms p ℓ L)
    (hK2 : ∀ h : 2 ≠ p, (K 2 Nat.prime_two h).LegendreRegular) {r n j t : ℕ}
    (hr : ¬ p ∣ r) (ht : t = r * p ^ n * ((p ^ 2 - 1) / 12)) (hjn : p ^ n < j) :
    ¬ BehrensC4 K t j (discriminantPow t) (integralDiscriminant ^ t)
      (isIntegralQExpansion_discriminantPow t) := by
  have h2p : 2 ≠ p := by omega
  rw [behrensC4_iff]
  intro h
  obtain ⟨H, hH, -, hEq⟩ := h 2 Nat.prime_two h2p
  exact KatzForms.not_exists_hasse_pow_mul_eq_levelRaise_sub_two_of_eq hDeuringPolynomialSeparable
    hp5 _ (hK2 h2p) hr ht hjn ⟨H, hH, hEq⟩

/-- **Theorem 1.1(ii)** (and Remark 1.2). Let `p ≥ 5`, `L` algebraically closed of
characteristic `p`, `p ∤ r`, `t = r pⁿ (p² - 1) / 12` and `j > pⁿ` (admissible or not). Then `Δᵗ`
fails Behrens' condition (C4): the divisibility `A_p^j ∣ L₂(Δ̄ᵗ)` fails at `ℓ = 2`. -/
theorem not_behrensC4_discriminantPow
    (hDeuringPolynomialSeparable : Polynomial.DeuringPolynomialSeparable.{u})
    [IsAlgClosed L] (hp5 : 5 ≤ p)
    (K : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → KatzForms p ℓ L)
    (hK2 : ∀ h : 2 ≠ p, (K 2 Nat.prime_two h).LegendreRegular) {r n j : ℕ}
    (hr : ¬ p ∣ r) (hjn : p ^ n < j) :
    ¬ BehrensC4 K (r * p ^ n * (p ^ 2 - 1) / 12) j
      (discriminantPow (r * p ^ n * (p ^ 2 - 1) / 12))
      (integralDiscriminant ^ (r * p ^ n * (p ^ 2 - 1) / 12))
      (isIntegralQExpansion_discriminantPow _) :=
  not_behrensC4_discriminantPow_of_eq hDeuringPolynomialSeparable hp5 K hK2 hr
    (mul_sq_sub_one_div_twelve Fact.out hp5 _) hjn

/-- **Theorem 1.1(ii)** with its parenthetical claim. For admissible `j > pⁿ`, necessarily
`r > 1` and `n ≥ 2`, and `Δᵗ` fails (C4) (so it is not a candidate `f_{i/j}`). Conversely, by
`DividedBeta.exists_isAdmissible_gt_iff`, admissible `j > pⁿ` exist whenever `r > 1` and
`n ≥ 2`. -/
theorem not_behrensC4_discriminantPow_of_isAdmissible
    (hcited : CitedResults.{u}) [IsAlgClosed L] (hp5 : 5 ≤ p)
    (K : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → KatzForms p ℓ L)
    (hK2 : ∀ h : 2 ≠ p, (K 2 Nat.prime_two h).LegendreRegular) {r n j : ℕ}
    (hr : ¬ p ∣ r) (hadm : DividedBeta.IsAdmissible p (r * p ^ n) j) (hjn : p ^ n < j) :
    (1 < r ∧ 2 ≤ n) ∧
      ¬ BehrensC4 K (r * p ^ n * (p ^ 2 - 1) / 12) j
        (discriminantPow (r * p ^ n * (p ^ 2 - 1) / 12))
        (integralDiscriminant ^ (r * p ^ n * (p ^ 2 - 1) / 12))
        (isIntegralQExpansion_discriminantPow _) := by
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact hr (dvd_zero p))
  exact ⟨(DividedBeta.exists_isAdmissible_gt_iff hr hr1).mp ⟨j, hadm, hjn⟩,
    not_behrensC4_discriminantPow hcited.deuringPolynomialSeparable hp5 K hK2 hr hjn⟩

/-- `Δᵗ` is not a candidate for `j > pⁿ`: (C1)–(C4) fail. -/
theorem not_satisfiesBehrensConditions_discriminantPow
    (hDeuringPolynomialSeparable : Polynomial.DeuringPolynomialSeparable.{u})
    [IsAlgClosed L] (hp5 : 5 ≤ p)
    (K : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → KatzForms p ℓ L)
    (hK2 : ∀ h : 2 ≠ p, (K 2 Nat.prime_two h).LegendreRegular) {r n j : ℕ}
    (hr : ¬ p ∣ r) (hjn : p ^ n < j) :
    ¬ SatisfiesBehrensConditions K (r * p ^ n * (p ^ 2 - 1) / 12) j
      (discriminantPow (r * p ^ n * (p ^ 2 - 1) / 12))
      (integralDiscriminant ^ (r * p ^ n * (p ^ 2 - 1) / 12)) :=
  fun h ↦ not_behrensC4_discriminantPow hDeuringPolynomialSeparable hp5 K hK2 hr hjn h.c4

/-- **Larson's conjecture** [larson2020, Conjecture 5.21 of arXiv:1906.08906v1 (Conjecture 5.17
in the published numbering)], in Larson's candidate convention: for `p ≥ 5`, `i = r pⁿ` with
`p ∤ r`, `t = i (p² - 1) / 12` and every admissible `j`, the form `Δᵗ` satisfies Behrens'
conditions (C1)–(C4) if and only if `j ≤ pⁿ`. -/
theorem discriminantPow_satisfiesBehrensConditions_iff
    (hcited : CitedResults.{u}) [IsAlgClosed L] (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (K : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → KatzForms p ℓ L)
    (Y : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p), LevelCover (K ℓ hℓ hℓp))
    (hK2 : ∀ h : 2 ≠ p, (K 2 Nat.prime_two h).LegendreRegular) {r n j : ℕ}
    (hr : ¬ p ∣ r) (hadm : DividedBeta.IsAdmissible p (r * p ^ n) j) :
    SatisfiesBehrensConditions K (r * p ^ n * (p ^ 2 - 1) / 12) j
        (discriminantPow (r * p ^ n * (p ^ 2 - 1) / 12))
        (integralDiscriminant ^ (r * p ^ n * (p ^ 2 - 1) / 12)) ↔ j ≤ p ^ n := by
  refine ⟨fun h ↦ ?_, discriminantPow_satisfiesBehrensConditions hcited hp5 hL K Y hr hadm⟩
  by_contra hjn
  exact not_satisfiesBehrensConditions_discriminantPow hcited.deuringPolynomialSeparable hp5 K hK2
    hr (not_le.mp hjn) h

/-- **Remark 1.2** (divisibility without admissibility): for every `j ≥ 1`, `Δᵗ` with
`t = r pⁿ (p² - 1) / 12`, `p ∤ r`, satisfies (C4) iff `j ≤ pⁿ`. -/
theorem discriminantPow_behrensC4_iff
    (hGonzalezDivisionPolynomial : WeierstrassCurve.GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : WeierstrassCurve.GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : WeierstrassCurve.SupersingularJInvariant.{u})
    (hVeluIsogeny : WeierstrassCurve.VeluIsogeny.{u})
    (hDeuringHasseCriterion : WeierstrassCurve.DeuringHasseCriterion.{u})
    (hDeuringPolynomialSeparable : Polynomial.DeuringPolynomialSeparable.{u})
    [IsAlgClosed L] (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (K : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → KatzForms p ℓ L)
    (Y : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p), LevelCover (K ℓ hℓ hℓp))
    (hK2 : ∀ h : 2 ≠ p, (K 2 Nat.prime_two h).LegendreRegular) {r n j : ℕ}
    (hr : ¬ p ∣ r) (hj1 : 1 ≤ j) :
    BehrensC4 K (r * p ^ n * (p ^ 2 - 1) / 12) j
        (discriminantPow (r * p ^ n * (p ^ 2 - 1) / 12))
        (integralDiscriminant ^ (r * p ^ n * (p ^ 2 - 1) / 12))
        (isIntegralQExpansion_discriminantPow _) ↔ j ≤ p ^ n := by
  refine ⟨fun h ↦ ?_, fun hjn ↦ ?_⟩
  · by_contra hjn
    exact not_behrensC4_discriminantPow hDeuringPolynomialSeparable hp5 K hK2 hr (not_le.mp hjn) h
  · exact (discriminantPow_satisfiesBehrensConditions_of_eq hGonzalezDivisionPolynomial
      hGonzalezMultiplicationByP hSupersingularJInvariant hVeluIsogeny hDeuringHasseCriterion
      hp5 hL K Y hr
      (mul_sq_sub_one_div_twelve Fact.out hp5 _) hj1 hjn).c4

/-- **Remark 1.2**, the case `r = 1`: for `n ≥ 2` and `pⁿ < j ≤ pⁿ + pⁿ⁻¹ - 1` (indices with no
element `β_{pⁿ/j}` on the `2`-line), `Δᵗ` with `t = pⁿ (p² - 1) / 12` fails (C4). -/
theorem not_behrensC4_discriminantPow_pow
    (hDeuringPolynomialSeparable : Polynomial.DeuringPolynomialSeparable.{u})
    [IsAlgClosed L] (hp5 : 5 ≤ p)
    (K : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → KatzForms p ℓ L)
    (hK2 : ∀ h : 2 ≠ p, (K 2 Nat.prime_two h).LegendreRegular) {n j : ℕ}
    (_hn : 2 ≤ n) (hjn : p ^ n < j) (_hjb : j ≤ p ^ n + p ^ (n - 1) - 1) :
    ¬ BehrensC4 K (p ^ n * (p ^ 2 - 1) / 12) j (discriminantPow (p ^ n * (p ^ 2 - 1) / 12))
      (integralDiscriminant ^ (p ^ n * (p ^ 2 - 1) / 12))
      (isIntegralQExpansion_discriminantPow _) :=
  not_behrensC4_discriminantPow_of_eq hDeuringPolynomialSeparable hp5 K hK2 (r := 1)
    (fun h ↦ (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h))
    (by rw [mul_sq_sub_one_div_twelve Fact.out hp5, one_mul]) hjn

end LevelOne
