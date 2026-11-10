/-
Assembled by AxiomProver.
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# The level-raising operator `V_N`

For a level-one modular form `f` of weight `k` and `N ≥ 1`, the function `τ ↦ f(Nτ)` is a modular
form of weight `k` on `Γ₀(N)`, denoted `V_N f`; its q-expansion is `f(q^N)`.

We construct `V_N f` from Mathlib's translation `ModularForm.translate f (diag(N, 1))`, using
`f ∣[k] diag(N, 1) = N^(k-1) f(N ·)`, and restrict it to `Γ₀(N)`.

## Main definitions and results

* `LevelTwoForms.restrictLevel`: restriction of a modular form to a smaller level.
* `LevelTwoForms.scaleMatrix N`: the matrix `diag(N, 1)` in `GL(2, ℝ)`.
* `LevelTwoForms.levelRaise N f`: the form `V_N f ∈ M_k(Γ₀(N))`, with
  `LevelTwoForms.levelRaise_apply`: `(V_N f)(τ) = f(Nτ)`.
* `LevelTwoForms.qExpansion_levelRaise_coeff`: the `n`-th q-expansion coefficient of `V_N f` is the
  `n / N`-th coefficient of `f` if `N ∣ n`, and `0` otherwise.
* `LevelTwoForms.qExpansion_coeff_of_hasSum`: identification of q-expansion coefficients from an
  expansion `f(τ) = ∑ cₘ qᵐ`.
-/

public section

open ModularForm UpperHalfPlane Matrix CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace LevelTwoForms

variable {k : ℤ}

/-- The restriction of a modular form of level `Γ'` to a subgroup `Γ ≤ Γ'`. -/
noncomputable def restrictLevel {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ ≤ Γ')
    (f : ModularForm Γ' k) : ModularForm Γ k where
  toFun := f
  slash_action_eq' γ hγ := f.slash_action_eq' γ (h hγ)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

@[simp]
lemma coe_restrictLevel {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ ≤ Γ') (f : ModularForm Γ' k) :
    ⇑(restrictLevel h f) = f :=
  (rfl)

/-- A level-one modular form regarded as a modular form on `Γ₀(N)`. -/
noncomputable def ofLevelOne (N : ℕ) {k : ℤ} (f : ModularForm 𝒮ℒ k) : ModularForm (Gamma0 N) k :=
  restrictLevel (Subgroup.map_le_range _ _) f

@[simp]
lemma coe_ofLevelOne (N : ℕ) {k : ℤ} (f : ModularForm 𝒮ℒ k) : ⇑(ofLevelOne N f) = f := by
  simp [ofLevelOne]

/-- The diagonal matrix `diag(N, 1)` in `GL(2, ℝ)`. -/
noncomputable def scaleMatrix (N : ℕ) [NeZero N] : GL (Fin 2) ℝ :=
  .mkOfDetNeZero !![(N : ℝ), 0; 0, 1] (by simp [det_fin_two, NeZero.ne])

variable (N : ℕ) [NeZero N]

lemma scaleMatrix_apply :
    (scaleMatrix N : Matrix (Fin 2) (Fin 2) ℝ) = !![(N : ℝ), 0; 0, 1] :=
  (rfl)

lemma det_scaleMatrix : (scaleMatrix N).det.val = N := by
  simp [scaleMatrix_apply, det_fin_two]

lemma det_scaleMatrix_pos : 0 < (scaleMatrix N).det.val := by
  rw [det_scaleMatrix]
  exact_mod_cast NeZero.pos N

lemma coe_scaleMatrix_smul (τ : ℍ) : ((scaleMatrix N • τ : ℍ) : ℂ) = N * τ := by
  rw [coe_smul_of_det_pos (det_scaleMatrix_pos N)]
  simp [num, denom, scaleMatrix_apply]

lemma scaleMatrix_slash_apply (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] scaleMatrix N) τ = (N : ℂ) ^ (k - 1) * f (scaleMatrix N • τ) := by
  rw [slash_apply, σ, ite_eq_left (det_scaleMatrix_pos N), det_scaleMatrix]
  simp [denom, scaleMatrix_apply, mul_comm]

/-- For `γ = [a, b; c, d] ∈ Γ₀(N)`, the matrix `[a, N b; c / N, d] ∈ SL(2, ℤ)`, which is
`diag(N, 1) γ diag(N, 1)⁻¹`. -/
noncomputable def conjScale (γ : Gamma0 N) : SL(2, ℤ) :=
  ⟨!![γ.1 0 0, N * γ.1 0 1; γ.1 1 0 / N, γ.1 1 1], by
    obtain ⟨c, hc⟩ : (N : ℤ) ∣ γ.1 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (Gamma0_mem.mp γ.2)
    have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hdet := γ.1.2
    rw [det_fin_two] at hdet
    rw [det_fin_two_of, hc, Int.mul_ediv_cancel_left _ hN]
    rw [hc] at hdet
    linear_combination hdet⟩

lemma coe_conjScale (γ : Gamma0 N) :
    (conjScale N γ : Matrix (Fin 2) (Fin 2) ℤ) =
      !![γ.1 0 0, N * γ.1 0 1; γ.1 1 0 / N, γ.1 1 1] :=
  (rfl)

lemma mapGL_conjScale_mul (γ : Gamma0 N) :
    mapGL ℝ (conjScale N γ) * scaleMatrix N = scaleMatrix N * mapGL ℝ γ.1 := by
  obtain ⟨c, hc⟩ : (N : ℤ) ∣ γ.1 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (Gamma0_mem.mp γ.2)
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, mapGL_coe_matrix, mapGL_coe_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_conjScale, scaleMatrix_apply, Matrix.mul_apply, Fin.sum_univ_two, hc,
      Int.mul_ediv_cancel_left _ hN, SpecialLinearGroup.map_apply_coe] <;> ring

open ConjAct Pointwise in
lemma Gamma0_le_conj_scaleMatrix :
    (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ≤ toConjAct (scaleMatrix N)⁻¹ • 𝒮ℒ := by
  rintro _ ⟨γ, hγ, rfl⟩
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
  refine ⟨conjScale N ⟨γ, hγ⟩, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact mapGL_conjScale_mul N ⟨γ, hγ⟩

omit [NeZero N] in
lemma one_mem_strictPeriods_Gamma0 :
    (1 : ℝ) ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

/-- The level-raising operator `V_N`: for `f ∈ M_k(SL(2, ℤ))`, the form `τ ↦ f(Nτ)` in
`M_k(Γ₀(N))`, defined as `N^(1-k) (f ∣[k] diag(N, 1))`. -/
noncomputable def levelRaise (f : ModularForm 𝒮ℒ k) : ModularForm (Gamma0 N) k :=
  ((N : ℂ) ^ (1 - k)) •
    restrictLevel (Gamma0_le_conj_scaleMatrix N) (ModularForm.translate f (scaleMatrix N))

lemma levelRaise_apply (f : ModularForm 𝒮ℒ k) (τ : ℍ) :
    levelRaise N f τ = f (scaleMatrix N • τ) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  simp only [levelRaise, IsSMulApply.smul_apply, coe_restrictLevel, coe_translate,
    scaleMatrix_slash_apply, smul_eq_mul]
  rw [← mul_assoc, ← zpow_add₀ hN, show 1 - k + (k - 1) = 0 by ring, zpow_zero, one_mul]

lemma qParam_scaleMatrix_smul (τ : ℍ) :
    Function.Periodic.qParam 1 (scaleMatrix N • τ : ℍ) = Function.Periodic.qParam 1 τ ^ N := by
  simp only [Function.Periodic.qParam, coe_scaleMatrix_smul, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Reindexing a power series in `z ^ N` as a power series in `z`. -/
lemma hasSum_reindex_pow {c : ℕ → ℂ} {z s : ℂ} (hs : HasSum (fun m ↦ c m * (z ^ N) ^ m) s) :
    HasSum (fun n ↦ (if N ∣ n then c (n / N) else 0) * z ^ n) s := by
  have hinj : Function.Injective (fun m : ℕ ↦ N * m) :=
    fun a b h ↦ Nat.eq_of_mul_eq_mul_left (NeZero.pos N) h
  rw [← hinj.hasSum_iff]
  · convert hs using 1
    ext m
    simp [pow_mul, Nat.mul_div_cancel_left _ (NeZero.pos N)]
  · intro n hn
    have hNn : ¬ N ∣ n := by
      rintro ⟨m, rfl⟩
      exact hn ⟨m, rfl⟩
    simp [hNn]

end LevelTwoForms

/-- The q-expansion coefficients of a modular form are determined by any expansion
`f(τ) = ∑ cₘ qᵐ` valid on all of `ℍ`. -/
lemma LevelTwoForms.qExpansion_coeff_of_hasSum {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ}
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k]
    {f : F} {c : ℕ → ℂ}
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m * Function.Periodic.qParam h τ ^ m) (f τ)) (m : ℕ) :
    (qExpansion h f).coeff m = c m :=
  (ModularFormClass.qExpansion_coeff_unique hh hΓ (by simpa using hf) m).symm

namespace LevelTwoForms

variable (N : ℕ) [NeZero N] {k : ℤ}

lemma hasSum_levelRaise (f : ModularForm 𝒮ℒ k) (τ : ℍ) :
    HasSum (fun n ↦ (if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0) *
      Function.Periodic.qParam 1 τ ^ n) (levelRaise N f τ) := by
  refine hasSum_reindex_pow N (c := fun m ↦ (qExpansion 1 f).coeff m)
    (z := Function.Periodic.qParam 1 τ) ?_
  rw [levelRaise_apply, ← qParam_scaleMatrix_smul]
  exact ModularForm.hasSum_qExpansion f one_pos (by simp) _

/-- The q-expansion of `V_N f` is `f(q^N)`. -/
theorem qExpansion_levelRaise_coeff (f : ModularForm 𝒮ℒ k) (n : ℕ) :
    (qExpansion 1 (levelRaise N f)).coeff n =
      if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 :=
  qExpansion_coeff_of_hasSum (Γ := (Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (F := ModularForm (Gamma0 N) k) one_pos (one_mem_strictPeriods_Gamma0 N)
    (hasSum_levelRaise N f) n

end LevelTwoForms
