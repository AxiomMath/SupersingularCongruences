/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.LevelTwoForms.LevelRaise
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable

/-!
# The weight-two form `δ` on `Γ₀(2)`

Following [larson2020, Section 3], `δ(τ) = (2 E₂(2τ) - E₂(τ)) / 4`, where `E₂` is the
quasimodular Eisenstein series of weight `2`. The defects of `E₂(τ)` and `2 E₂(2τ)` under
`γ ∈ Γ₀(2)` cancel, so `δ ∈ M₂(Γ₀(2))`, with q-expansion `1/4 + 6q + 6q² + 24q³ + ⋯`.

## Main definitions and results

* `LevelTwoForms.delta`: `δ` as a modular form of weight `2` on `Γ₀(2)`, with
  `LevelTwoForms.delta_apply`: `δ(τ) = (2 E₂(2τ) - E₂(τ)) / 4`.
* `LevelTwoForms.qExpansion_delta_coeff`: the q-expansion coefficients of `δ`, and
  `LevelTwoForms.qExpansion_delta_coeff_zero` … `qExpansion_delta_coeff_three`.
-/

public section

open ModularForm UpperHalfPlane Matrix CongruenceSubgroup Matrix.SpecialLinearGroup
  EisensteinSeries OnePoint Complex
open scoped MatrixGroups ModularForm Real ArithmeticFunction.sigma ConjAct Pointwise

local notation "𝕢" => Function.Periodic.qParam

namespace LevelTwoForms

/-- The defect `D₂(γ)(z) = 2πi c / (cz + d)` is bounded at `i∞`. -/
lemma isBoundedAtImInfty_D2 (γ : SL(2, ℤ)) : IsBoundedAtImInfty (D2 γ) := by
  rw [isBoundedAtImInfty_iff]
  refine ⟨2 * π, 1, fun z hz ↦ ?_⟩
  by_cases hc : γ 1 0 = 0
  · rw [show D2 γ z = 0 by simp [D2, hc], norm_zero]
    positivity
  · have hc' : (1 : ℝ) ≤ |(γ 1 0 : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hc
    have hden : |(γ 1 0 : ℝ)| * z.im ≤ ‖denom γ z‖ := by
      calc |(γ 1 0 : ℝ)| * z.im = |(denom γ z).im| := by
            simp [denom, abs_mul, abs_of_pos z.im_pos]
        _ ≤ ‖denom γ z‖ := Complex.abs_im_le_norm _
    have hpos : 0 < |(γ 1 0 : ℝ)| * z.im := by
      have := z.im_pos
      positivity
    rw [D2, norm_div]
    have hnum : ‖2 * (π : ℂ) * Complex.I * (γ 1 0 : ℂ)‖ = 2 * π * |(γ 1 0 : ℝ)| := by
      simp [abs_of_pos Real.pi_pos]
    rw [hnum, div_le_iff₀ (hpos.trans_le hden)]
    calc 2 * π * |(γ 1 0 : ℝ)| ≤ 2 * π * (|(γ 1 0 : ℝ)| * z.im) := by
          gcongr
          exact le_mul_of_one_le_right (abs_nonneg _) hz
      _ ≤ 2 * π * ‖denom γ z‖ := by gcongr

lemma isBoundedAtImInfty_E2_slash (γ : SL(2, ℤ)) : IsBoundedAtImInfty (E2 ∣[(2 : ℤ)] γ) := by
  rw [E2_slash_action, sub_eq_add_neg]
  exact isBoundedAtImInfty_E2.add ((isBoundedAtImInfty_D2 γ).smul _).neg

/-- `E₂` is bounded at every cusp of `SL(2, ℤ)`. -/
lemma isBoundedAt_E2 {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) : c.IsBoundedAt E2 2 := by
  obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
  exact (isBoundedAt_iff_exists_SL2Z hc).mpr ⟨γ, rfl, isBoundedAtImInfty_E2_slash γ⟩

lemma isBoundedAt_smul {c : OnePoint ℝ} {f : ℍ → ℂ} {k : ℤ} (a : ℂ) (hf : c.IsBoundedAt f k) :
    c.IsBoundedAt (a • f) k := fun g hg ↦ by
  rw [smul_slash]
  exact (hf g hg).smul _

lemma isBoundedAt_sub {c : OnePoint ℝ} {f f' : ℍ → ℂ} {k : ℤ} (hf : c.IsBoundedAt f k)
    (hf' : c.IsBoundedAt f' k) : c.IsBoundedAt (f - f') k := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ f']
  exact hf.add (isBoundedAt_smul _ hf')

/-- The matrix `diag(N, 1)` over `ℚ`. -/
noncomputable def scaleMatrixRat (N : ℕ) [NeZero N] : GL (Fin 2) ℚ :=
  .mkOfDetNeZero !![(N : ℚ), 0; 0, 1] (by simp [det_fin_two, NeZero.ne])

lemma scaleMatrix_eq_map (N : ℕ) [NeZero N] :
    scaleMatrix N = (scaleMatrixRat N).map (Rat.castHom ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scaleMatrix_apply, scaleMatrixRat,
    Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- `E₂ ∣[2] diag(N, 1)` is bounded at every cusp of `SL(2, ℤ)`. -/
lemma isBoundedAt_E2_slash_scaleMatrix (N : ℕ) [NeZero N] {c : OnePoint ℝ}
    (hc : IsCusp c 𝒮ℒ) : c.IsBoundedAt (E2 ∣[(2 : ℤ)] scaleMatrix N) 2 := by
  rw [← IsBoundedAt.smul_iff]
  apply isBoundedAt_E2
  have h := hc.smul (scaleMatrix N)
  rw [scaleMatrix_eq_map] at h ⊢
  have := isArithmetic_conj_SL2Z (scaleMatrixRat N)
  exact (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp h

/-- The function `δ = (E₂ ∣[2] diag(2, 1) - E₂) / 4`, i.e. `δ(τ) = (2 E₂(2τ) - E₂(τ)) / 4`. -/
noncomputable def deltaFun : ℍ → ℂ :=
  (4⁻¹ : ℂ) • (E2 ∣[(2 : ℤ)] scaleMatrix 2 - E2)

lemma deltaFun_apply (τ : ℍ) :
    deltaFun τ = (2 * E2 (scaleMatrix 2 • τ) - E2 τ) / 4 := by
  simp only [deltaFun, Pi.smul_apply, Pi.sub_apply, scaleMatrix_slash_apply, smul_eq_mul]
  norm_num
  ring

/-- The defect of `E₂ ∣[2] diag(2, 1)` under `γ ∈ Γ₀(2)` equals the defect of `E₂`. -/
lemma D2_conjScale_slash (γ : Gamma0 2) :
    D2 (conjScale 2 γ) ∣[(2 : ℤ)] scaleMatrix 2 = D2 γ.1 := by
  obtain ⟨c, hc⟩ : (2 : ℤ) ∣ γ.1 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (Gamma0_mem.mp γ.2)
  ext τ
  rw [scaleMatrix_slash_apply]
  simp only [D2, denom, coe_scaleMatrix_smul]
  simp [coe_conjScale, SpecialLinearGroup.map_apply_coe, hc]
  field_simp

lemma slash_sub {G α : Type*} [Monoid G] [AddGroup α] [SlashAction ℤ G α] (k : ℤ) (g : G)
    (a b : α) : (a - b) ∣[k] g = a ∣[k] g - b ∣[k] g := by
  rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ← sub_eq_add_neg]

lemma deltaFun_slash (γ : Gamma0 2) : deltaFun ∣[(2 : ℤ)] γ.1 = deltaFun := by
  have h1 : (E2 ∣[(2 : ℤ)] scaleMatrix 2) ∣[(2 : ℤ)] mapGL ℝ γ.1 =
      E2 ∣[(2 : ℤ)] scaleMatrix 2 - (1 / (2 * riemannZeta 2)) • D2 γ.1 := by
    have e2 : E2 ∣[(2 : ℤ)] mapGL ℝ (conjScale 2 γ) =
        E2 - (1 / (2 * riemannZeta 2)) • D2 (conjScale 2 γ) :=
      E2_slash_action _
    rw [← SlashAction.slash_mul, ← mapGL_conjScale_mul, SlashAction.slash_mul, e2, slash_sub,
      smul_slash, D2_conjScale_slash]
    rw [UpperHalfPlane.σ, ite_eq_left (det_scaleMatrix_pos 2)]
    rfl
  have h2 : (E2 ∣[(2 : ℤ)] scaleMatrix 2) ∣[(2 : ℤ)] γ.1 =
      E2 ∣[(2 : ℤ)] scaleMatrix 2 - (1 / (2 * riemannZeta 2)) • D2 γ.1 := h1
  rw [deltaFun, SL_smul_slash, slash_sub, h2, E2_slash_action]
  congr 1
  abel

/-- `δ = (2 E₂(2τ) - E₂(τ)) / 4 ∈ M₂(Γ₀(2))` [larson2020, Section 3]. -/
noncomputable def delta : ModularForm (Gamma0 2) 2 where
  toFun := deltaFun
  slash_action_eq' := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact deltaFun_slash ⟨γ, hγ⟩
  holo' := by
    have := (E2_mdifferentiable.slash 2 (scaleMatrix 2)).sub E2_mdifferentiable
    exact this.const_smul _
  bdd_at_cusps' {c} hc := by
    have hc' : IsCusp c 𝒮ℒ := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc
    exact isBoundedAt_smul _
      (isBoundedAt_sub (isBoundedAt_E2_slash_scaleMatrix 2 hc') (isBoundedAt_E2 hc'))

lemma delta_apply (τ : ℍ) : delta τ = (2 * E2 (scaleMatrix 2 • τ) - E2 τ) / 4 :=
  deltaFun_apply τ

/-! ### The q-expansion of `δ` -/

/-- The q-expansion coefficients of `E₂ = 1 - 24 ∑ σ₁(n) qⁿ`. -/
noncomputable def e2Coeff (m : ℕ) : ℂ :=
  if m = 0 then 1 else -24 * σ 1 m

lemma hasSum_E2 (τ : ℍ) : HasSum (fun m ↦ e2Coeff m * 𝕢 1 τ ^ m) (E2 τ) := by
  simpa [e2Coeff, Function.Periodic.qParam] using hasSum_qExpansion_E2 (z := τ)

/-- The q-expansion coefficients of `δ`: `(2 [2 ∣ n] e(n/2) - e(n)) / 4`, where `e(n)` are the
coefficients of `E₂`. -/
noncomputable def deltaCoeff (n : ℕ) : ℂ :=
  (2 * (if 2 ∣ n then e2Coeff (n / 2) else 0) - e2Coeff n) / 4

lemma hasSum_delta (τ : ℍ) : HasSum (fun n ↦ deltaCoeff n * 𝕢 1 τ ^ n) (delta τ) := by
  have hA := hasSum_reindex_pow 2 (c := e2Coeff) (z := 𝕢 1 τ)
    (by rw [← qParam_scaleMatrix_smul]; exact hasSum_E2 _)
  have := ((hA.mul_left 2).sub (hasSum_E2 τ)).div_const 4
  rw [delta_apply]
  convert this using 1
  ext n
  simp only [deltaCoeff]
  ring

theorem qExpansion_delta_coeff (n : ℕ) : (qExpansion 1 delta).coeff n = deltaCoeff n :=
  qExpansion_coeff_of_hasSum (Γ := (Gamma0 2 : Subgroup (GL (Fin 2) ℝ)))
    (F := ModularForm (Gamma0 2) 2) one_pos (one_mem_strictPeriods_Gamma0 2) hasSum_delta n

lemma qExpansion_delta_coeff_zero : (qExpansion 1 delta).coeff 0 = 1 / 4 := by
  rw [qExpansion_delta_coeff]
  norm_num [deltaCoeff, e2Coeff]

lemma qExpansion_delta_coeff_one : (qExpansion 1 delta).coeff 1 = 6 := by
  rw [qExpansion_delta_coeff]
  norm_num [deltaCoeff, e2Coeff]

lemma qExpansion_delta_coeff_two : (qExpansion 1 delta).coeff 2 = 6 := by
  rw [qExpansion_delta_coeff]
  have : σ 1 2 = 3 := by decide
  norm_num [deltaCoeff, e2Coeff, this]

lemma qExpansion_delta_coeff_three : (qExpansion 1 delta).coeff 3 = 24 := by
  rw [qExpansion_delta_coeff]
  have : σ 1 3 = 4 := by decide
  norm_num [deltaCoeff, e2Coeff, this]

end LevelTwoForms
