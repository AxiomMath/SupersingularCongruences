/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.LevelTwoForms.Identities
public import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# `ε` as an eta quotient

The manuscript defines `ε(τ) = η(τ)¹⁶ / (16 η(2τ)⁸)`. We show that this eta quotient agrees with
Larson's form `LevelTwoForms.eps = (16 V₂E₄ - E₄) / 240`, so that `LevelTwoForms.eps` is the
manuscript's `ε`.

The argument: by `Δ = η²⁴` and the identities `Δ = 64 μ ε²`, `V₂(Δ) = μ² ε`, both functions have
cube `Δ(τ)² / (4096 Δ(2τ))`. Their quotient is therefore a continuous function on the connected
space `ℍ` with values in the (finite, discrete) set of cube roots of unity, hence constant; both
functions tend to `1/16` at `i∞`, so the constant is `1`.

## Main results

* `LevelTwoForms.etaQuotient`: the function `τ ↦ η(τ)¹⁶ / (16 η(2τ)⁸)`.
* `LevelTwoForms.eps_apply_eq_etaQuotient`: `ε(τ) = η(τ)¹⁶ / (16 η(2τ)⁸)`.
-/

public section

open ModularForm UpperHalfPlane Filter Topology Complex
open scoped ModularForm

local notation "𝕢" => Function.Periodic.qParam

namespace LevelTwoForms

/-- The infinite product `∏_{n ≥ 1} (1 - qⁿ)`. -/
noncomputable def etaProd (q : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ (n + 1))

lemma eta_eq_qParam_mul_etaProd (z : ℂ) : η z = 𝕢 24 z * etaProd (𝕢 1 z) :=
  (rfl)

lemma tendsto_etaProd : Tendsto etaProd (𝓝 0) (𝓝 1) := by
  have := tendsto_tprod_one_add_of_dominated_convergence (𝓕 := 𝓝 0) (g := 0)
    (f := fun (q : ℂ) (n : ℕ) ↦ -q ^ (n + 1)) (bound := fun n ↦ (1 / 2 : ℝ) ^ (n + 1))
  simp only [Pi.zero_apply, norm_neg, norm_pow, add_zero, tprod_one] at this
  change Tendsto (fun q : ℂ ↦ ∏' n : ℕ, (1 - q ^ (n + 1))) _ _
  simp_rw [sub_eq_add_neg]
  refine this
    (by simpa only [pow_succ'] using (summable_geometric_of_abs_lt_one (by norm_num)).mul_left _)
    (fun k ↦ by simpa using ((continuous_pow (M := ℂ) (k + 1)).tendsto 0).neg) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with q hq k
  exact pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.mp hq).le _

/-- The eta quotient `η(τ)¹⁶ / (16 η(2τ)⁸)`. -/
noncomputable def etaQuotient (τ : ℍ) : ℂ :=
  η τ ^ 16 / (16 * η (2 * τ) ^ 8)

lemma two_mul_mem_upperHalfPlaneSet (τ : ℍ) : (2 * τ : ℂ) ∈ upperHalfPlaneSet := by
  change 0 < (2 * (τ : ℂ)).im
  simpa using τ.im_pos

lemma eta_two_mul_ne_zero (τ : ℍ) : η (2 * τ) ≠ 0 :=
  eta_ne_zero (two_mul_mem_upperHalfPlaneSet τ)

lemma etaQuotient_eq (τ : ℍ) :
    etaQuotient τ = etaProd (𝕢 1 τ) ^ 16 / (16 * etaProd (𝕢 1 τ ^ 2) ^ 8) := by
  have h1 : 𝕢 1 (2 * τ) = 𝕢 1 τ ^ 2 := by
    simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h24 : 𝕢 24 τ ^ 16 = 𝕢 24 (2 * τ) ^ 8 := by
    simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hne : 𝕢 24 (2 * τ) ≠ 0 := Function.Periodic.qParam_ne_zero _
  rw [etaQuotient, eta_eq_qParam_mul_etaProd, eta_eq_qParam_mul_etaProd, h1, mul_pow, mul_pow,
    h24]
  field_simp

lemma tendsto_etaQuotient : Tendsto etaQuotient atImInfty (𝓝 (1 / 16)) := by
  have hq := qParam_tendsto_atImInfty (h := 1) one_pos
  have h1 := tendsto_etaProd.comp hq
  have h2 := tendsto_etaProd.comp (by simpa using hq.pow 2)
  have := (h1.pow 16).div ((h2.pow 8).const_mul 16) (by norm_num)
  simp only [one_pow, mul_one] at this
  refine this.congr fun τ ↦ ?_
  rw [etaQuotient_eq]
  rfl

lemma etaQuotient_ne_zero (τ : ℍ) : etaQuotient τ ≠ 0 := by
  rw [etaQuotient]
  exact div_ne_zero (pow_ne_zero _ (eta_ne_zero τ.2))
    (mul_ne_zero (by norm_num) (pow_ne_zero _ (eta_two_mul_ne_zero τ)))

lemma continuous_etaQuotient : Continuous etaQuotient := by
  have hη : Continuous fun τ : ℍ ↦ η τ :=
    continuous_iff_continuousAt.mpr fun τ ↦
      (differentiableAt_eta_of_mem_upperHalfPlaneSet τ.2).continuousAt.comp
        continuous_coe.continuousAt
  have hη2 : Continuous fun τ : ℍ ↦ η (2 * τ) :=
    continuous_iff_continuousAt.mpr fun τ ↦
      (differentiableAt_eta_of_mem_upperHalfPlaneSet
        (two_mul_mem_upperHalfPlaneSet τ)).continuousAt.comp (f := fun x : ℍ ↦ (2 : ℂ) * x)
        (continuous_const.mul UpperHalfPlane.continuous_coe).continuousAt
  exact (hη.pow 16).div (continuous_const.mul (hη2.pow 8)) fun τ ↦
    mul_ne_zero (by norm_num) (pow_ne_zero _ (eta_two_mul_ne_zero τ))

lemma eps_pow_three_eq (τ : ℍ) : eps τ ^ 3 = etaQuotient τ ^ 3 := by
  have hΔ : ModularForm.discriminant τ = η τ ^ 24 := rfl
  have hΔ2 : ModularForm.discriminant (scaleMatrix 2 • τ) = η (2 * τ) ^ 24 := by
    change η (scaleMatrix 2 • τ : ℍ) ^ 24 = _
    rw [coe_scaleMatrix_smul]
    norm_num
  have h1 := discriminant_apply_eq τ
  have h2 := discriminant_scaleMatrix_apply_eq τ
  rw [hΔ] at h1
  rw [hΔ2] at h2
  have hne := pow_ne_zero 24 (eta_two_mul_ne_zero τ)
  have hR : etaQuotient τ ^ 3 * (4096 * η (2 * τ) ^ 24) = (η τ ^ 24) ^ 2 := by
    have h8 : (16 : ℂ) ^ 3 * (η (2 * τ) ^ 8) ^ 3 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero _ (pow_ne_zero _ (eta_two_mul_ne_zero τ)))
    rw [etaQuotient, div_pow, mul_pow, div_mul_eq_mul_div, div_eq_iff h8]
    ring
  have hL : eps τ ^ 3 * (4096 * η (2 * τ) ^ 24) = (η τ ^ 24) ^ 2 := by
    rw [h2, h1]
    ring
  exact mul_right_cancel₀ (mul_ne_zero (by norm_num) hne) (hL.trans hR.symm)

lemma tendsto_eps : Tendsto (fun τ ↦ eps τ) atImInfty (𝓝 (1 / 16)) := by
  have hs : ∀ τ : ℍ, HasSum (fun m ↦ (qExpansion 1 eps).coeff m • 𝕢 1 τ ^ m) (eps τ) :=
    fun τ ↦ by
      simpa [smul_eq_mul] using
        ModularForm.hasSum_qExpansion eps one_pos (one_mem_strictPeriods_Gamma0 2) τ
  have := tendsto_atImInfty_of_hasSum_qExpansion one_pos hs
  rwa [coeff_eps.1] at this

lemma finite_cube_roots : {z : ℂ | z ^ 3 = 1}.Finite :=
  (Polynomial.nthRoots 3 (1 : ℂ)).toFinset.finite_toSet.subset fun z hz ↦ by
    simpa [Polynomial.mem_nthRoots] using hz

/-- `ε(τ) = η(τ)¹⁶ / (16 η(2τ)⁸)`: Larson's form `LevelTwoForms.eps` is the eta quotient of the
manuscript. -/
theorem eps_apply_eq_etaQuotient (τ : ℍ) : eps τ = etaQuotient τ := by
  set g : ℍ → ℂ := fun τ ↦ eps τ / etaQuotient τ
  have hg3 : ∀ τ, g τ ^ 3 = 1 := fun τ ↦ by
    simp only [g, div_pow, eps_pow_three_eq]
    exact div_self (pow_ne_zero _ (etaQuotient_ne_zero τ))
  have hgc : Continuous g :=
    (ModularFormClass.continuous eps).div continuous_etaQuotient etaQuotient_ne_zero
  have hconst : ∀ τ τ', g τ = g τ' := fun τ τ' ↦
    isPreconnected_univ.constant_of_mapsTo finite_cube_roots.isDiscrete hgc.continuousOn
      (fun x _ ↦ hg3 x) (Set.mem_univ τ) (Set.mem_univ τ')
  have hlim : Tendsto g atImInfty (𝓝 1) := by
    have := tendsto_eps.div tendsto_etaQuotient (by norm_num)
    norm_num at this
    exact this
  have h1 : g τ = 1 := by
    have hg : g = fun _ ↦ g τ := funext fun τ' ↦ hconst τ' τ
    rw [hg] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  simpa [g, div_eq_one_iff_eq (etaQuotient_ne_zero τ)] using h1

end LevelTwoForms
