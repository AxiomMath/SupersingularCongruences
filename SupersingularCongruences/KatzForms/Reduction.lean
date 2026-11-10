/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.KatzForms.ReductionAlgebra
public import SupersingularCongruences.LevelOne.VonStaudtClausen
public import SupersingularCongruences.ModularCurve.Containment
public import SupersingularCongruences.External
import all SupersingularCongruences.ModularCurve.Gamma0Pair

/-!
# Reductions of classical forms as Katz forms; the moduli interpretation of `R_ℓ`

* `KatzForms.reductionAtLevel_discriminantPow`: the reduction of `Δᵗ` on `Γ₀(ℓ)` is the rule
  `(E, C, ω) ↦ Δ(E, ω)ᵗ`.
* `KatzForms.levelRaiseReduction_discriminantPow`: **Lemma 4.1**: the reduction of `V_ℓ(Δᵗ)` is
  `(Δ^{[ℓ]})ᵗ`, where `Δ^{[ℓ]}(E, C, ω) = ℓ⁻¹² Δ(E / C, ω')`.
* `KatzForms.containment`: **Theorem 1.2**: `R_ℓ = V_ℓ(Δ) / Δ` satisfies `R_ℓ(P̃) ^ m = 1` at every
  supersingular point.
-/

public section

open Gamma0 LevelOne

universe u

namespace Gamma0

variable {ℓ : ℕ} {L : Type*} [Field L] [DecidableEq L]

/-- On test objects over `L`, the rule `Δ(E / C, ω')` only depends on the isomorphism class:
Vélu's quotient of an isomorphic pair is the isomorphic quotient
(`WeierstrassCurve.velu_scaling`). -/
lemma veluDiscriminantRule_scale (T : Test ℓ L) (u : Lˣ) :
    veluDiscriminantRule (T.scale u) = veluDiscriminantRule T := by
  rw [veluDiscriminantRule_apply, veluDiscriminantRule_apply]
  change ((((T.diff * u : Lˣ) : L)) ^ 12)⁻¹ *
      ((T.curve.scaling u).velu (T.subgroup.map (WeierstrassCurve.Affine.Point.scaling
        T.curve u))).Δ = _
  rw [WeierstrassCurve.velu_scaling, WeierstrassCurve.Δ_scaling,
    Units.val_mul, mul_pow, mul_inv, mul_assoc, ← mul_assoc ((((u : L)) ^ 12)⁻¹),
    inv_mul_cancel₀ (pow_ne_zero _ u.ne_zero), one_mul]

/-- On test objects over `L`, the rule `Δ(E / C, ω')` has weight `12`: replacing `ω` by `c ω`
replaces `ω'` by `c ω'`. -/
lemma veluDiscriminantRule_smulDiff (T : Test ℓ L) (c : Lˣ) :
    veluDiscriminantRule (T.smulDiff c) = (c : L) ^ (-12 : ℤ) * veluDiscriminantRule T := by
  rw [veluDiscriminantRule_apply, veluDiscriminantRule_apply, Test.smulDiff_diff,
    Test.smulDiff_toPair, Units.val_mul, mul_pow, mul_inv, zpow_neg, mul_assoc]
  norm_num

end Gamma0

namespace KatzForms

variable {p ℓ : ℕ} [Fact p.Prime] {L : Type u} [Field L] [DecidableEq L] [CharP L p]
  (K : KatzForms p ℓ L)

omit [CharP L p] in
/-- The reduction of `Δᵗ`, viewed on `Γ₀(ℓ)`, is the rule `(E, C, ω) ↦ Δ(E, ω)ᵗ`. -/
theorem reductionAtLevel_discriminantPow (t : ℕ) :
    (reductionAtLevel K (discriminantPow t) _ (isIntegralQExpansion_discriminantPow t)).1 =
      discriminantRule ^ t := by
  refine K.eq_of_qExp_eq (reductionAtLevel K _ _ _).2 (K.discriminant_pow_mem t) ?_
  rw [qExp_reductionAtLevel, map_pow, ← K.qExp_discriminant, ← K.qExp_pow]
  exact K.qExp_congr (by ring) rfl _ _

omit [CharP L p] in
/-- **Lemma 4.1** (moduli interpretation of `V_ℓ(Δ)`), for powers: the reduction of `V_ℓ(Δᵗ)` is
`(Δ^{[ℓ]})ᵗ`, where `Δ^{[ℓ]}(E, C, ω) = ℓ⁻¹² Δ(E / C, ω')` with `φ^* ω' = ω` for the quotient
isogeny `φ : E → E / C`. -/
theorem levelRaiseReduction_discriminantPow [NeZero ℓ] (hℓ : (ℓ : L) ≠ 0) (t : ℕ) :
    (levelRaiseReduction K (discriminantPow t) _ (isIntegralQExpansion_discriminantPow t)).1 =
      (fun T ↦ ((ℓ : L) ^ 12)⁻¹ * veluDiscriminantRule T) ^ t := by
  have hmem := K.normalizedVeluDiscriminant_mem
  have hq := K.qExp_normalizedVeluDiscriminant hℓ
  refine K.eq_of_qExp_eq (levelRaiseReduction K _ _ _).2
    (K.mem_form_of_eq (show (t : ℤ) * 12 = 12 * t by ring) (K.pow_mem hmem t)) ?_
  rw [qExp_levelRaiseReduction, map_pow, expandSeries_pow (NeZero.ne ℓ), ← hq, ← K.qExp_pow]
  exact K.qExp_congr (by ring) rfl _ _

/-- **Lemma 2.1(c)** (the Hasse invariant is the reduction of `E_{p-1}`): for `p ≥ 5` the
`q`-expansion of `E_{p-1}` is `p`-integral with reduction `1` (von Staudt–Clausen), and the
reduction of `E_{p-1}` on `Γ₀(ℓ)` is the Hasse invariant rule
`(E, C, λ ω_E) ↦ λ^{-(p-1)} · (coefficient of x^{p-1} in (x³ + a₄ x + a₆)^{(p-1)/2})`. -/
theorem exists_reduce_eisenstein_eq_hasseRule (hp5 : 5 ≤ p) (hE : 3 ≤ p - 1) :
    ∃ (G : PowerSeries ℚ) (hG : G.IsPIntegral p) (hfG : PowerSeries.map (Rat.castHom ℂ) G =
        UpperHalfPlane.qExpansion 1 (LevelTwoForms.ofLevelOne ℓ (ModularForm.E hE))),
      PowerSeries.constantCoeff (G.reduceTo L) = 1 ∧
        ∀ T, (K.reduce _ G hG hfG).1 T = hasseRule p T := by
  have hp2 : p ≠ 2 := by omega
  have hfG : PowerSeries.map (Rat.castHom ℂ) (eisensteinSeriesQExp p) =
      UpperHalfPlane.qExpansion 1 (LevelTwoForms.ofLevelOne ℓ (ModularForm.E hE)) := by
    rw [LevelTwoForms.coe_ofLevelOne, map_eisensteinSeriesQExp hp2]
  refine ⟨eisensteinSeriesQExp p, isPIntegral_eisensteinSeriesQExp hp2, hfG, ?_, fun T ↦ ?_⟩
  · rw [reduceTo_eisensteinSeriesQExp hp2, map_one]
  have hk : (p : ℤ) - 1 = ((p - 1 : ℕ) : ℤ) := by
    have := (Fact.out : p.Prime).one_le
    push_cast [this]
    ring
  have hmem : hasseRule p ∈ K.form ((p - 1 : ℕ) : ℤ) := K.mem_form_of_eq hk K.hasse_mem
  refine congrFun (K.reduce_eq_of_qExp_eq _ _ _ hfG hmem ?_) T
  rw [reduceTo_eisensteinSeriesQExp hp2, ← K.qExp_hasse]
  exact K.qExp_congr hk.symm rfl _ _

/-- **Theorem 1.2** (supersingular containment), from the cited results it uses: for `p ≥ 5`, a
prime `ℓ ≠ p` and a test object `(E, C, ω)` with `E` supersingular, the value
`R_ℓ(P̃) = V_ℓ(Δ)(E, C, ω) / Δ(E, C, ω)` of the modular function `R_ℓ = V_ℓ(Δ) / Δ` satisfies
`R_ℓ(P̃) ^ ((p² - 1) / 12) = 1`. -/
theorem containment_of_cited
    (hGonzalezDivisionPolynomial : WeierstrassCurve.GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : WeierstrassCurve.GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : WeierstrassCurve.SupersingularJInvariant.{u})
    (hVeluIsogeny : WeierstrassCurve.VeluIsogeny.{u})
    [IsAlgClosed L] (hp5 : 5 ≤ p) (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x)
    (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (T : Test ℓ L) (hss : T.curve.IsSupersingularOver p) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ((levelRaiseReduction K (discriminantPow 1) _ (isIntegralQExpansion_discriminantPow 1)).1 T /
        (reductionAtLevel K (discriminantPow 1) _ (isIntegralQExpansion_discriminantPow 1)).1 T) ^
      ((p ^ 2 - 1) / 12) = 1 := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hℓL : (ℓ : L) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff L p] at h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).mp h).symm
  rw [levelRaiseReduction_discriminantPow K hℓL 1, reductionAtLevel_discriminantPow K 1, pow_one,
    pow_one, ← Pair.veluRatio_eq_div]
  exact Pair.veluRatio_pow_eq_one_of_cited hGonzalezDivisionPolynomial hGonzalezMultiplicationByP
    hSupersingularJInvariant hVeluIsogeny Fact.out hp5 hL hℓ hℓp T.toPair hss

/-- **Theorem 1.2** (supersingular containment): for `p ≥ 5`, a prime `ℓ ≠ p` and a test object
`(E, C, ω)` with `E` supersingular, the value `R_ℓ(P̃) = V_ℓ(Δ)(E, C, ω) / Δ(E, C, ω)` of the
modular function `R_ℓ = V_ℓ(Δ) / Δ` satisfies `R_ℓ(P̃) ^ ((p² - 1) / 12) = 1`. -/
theorem containment (hcited : CitedResults.{u}) [IsAlgClosed L] (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x)
    (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (T : Test ℓ L) (hss : T.curve.IsSupersingularOver p) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ((levelRaiseReduction K (discriminantPow 1) _ (isIntegralQExpansion_discriminantPow 1)).1 T /
        (reductionAtLevel K (discriminantPow 1) _ (isIntegralQExpansion_discriminantPow 1)).1 T) ^
      ((p ^ 2 - 1) / 12) = 1 :=
  containment_of_cited K hcited.gonzalezDivisionPolynomial hcited.gonzalezMultiplicationByP
    hcited.supersingularJInvariant hcited.veluIsogeny hp5 hL hℓ hℓp T hss

end KatzForms
