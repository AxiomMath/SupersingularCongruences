/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.LevelTwoForms.WeightTwo
public import SupersingularCongruences.LevelTwoForms.Sturm
import SupersingularCongruences.LevelOne.IntegralQExpansion

/-!
# Larson's generators on `Γ₀(2)` and the identities `Δ = 64 μ ε²`, `V₂(Δ) = μ² ε`

We define the weight-four forms `ε, μ ∈ M₄(Γ₀(2))` of [larson2020, Section 3]:

* `ε = (16 V₂E₄ - E₄) / 240`, with q-expansion `1/16 - q + 7q² - 28q³ + ⋯`;
* `μ = δ² - ε`, with q-expansion `4q + 32q² + 112q³ + ⋯`.

The manuscript defines `ε` as the eta quotient `η(τ)¹⁶ / (16 η(2τ)⁸)`; here we use Larson's
characterization `16 ε = 16 V₂E₄ - E₄` in terms of the Eisenstein series `E₄`, which
exhibits `ε` directly as a modular form on `Γ₀(2)` (see `LevelTwoForms.eps`).

## Main results (Lemma 3.1 of the manuscript)

* `LevelTwoForms.discriminant_eq`: `Δ = 64 μ ε²` in `M₁₂(Γ₀(2))`;
* `LevelTwoForms.levelRaise_discriminant_eq`: `V₂(Δ) = μ² ε` in `M₁₂(Γ₀(2))`.

Both follow from the Sturm bound for `Γ₀(2)` (`LevelTwoForms.sturm_bound_Gamma0_two`) by comparing
q-expansions through `q³`. We also record Larson's identities `E₄ = 64 μ + 16 ε`,
`V₂E₄ = 4 μ + 16 ε` and `80 δ² = E₄ + 4 V₂E₄`.
-/

public section

open ModularForm UpperHalfPlane CongruenceSubgroup PowerSeries EisensteinSeries
open scoped MatrixGroups ArithmeticFunction.sigma

namespace LevelTwoForms

/-! ### Coefficients of products of power series in low degree -/

section Coeff

variable {R : Type*} [CommRing R] (A B : PowerSeries R)

lemma coeff_zero_mul' : coeff 0 (A * B) = coeff 0 A * coeff 0 B := by
  simp [coeff_mul]

lemma coeff_one_mul' : coeff 1 (A * B) = coeff 0 A * coeff 1 B + coeff 1 A * coeff 0 B := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

lemma coeff_two_mul' : coeff 2 (A * B) =
    coeff 0 A * coeff 2 B + coeff 1 A * coeff 1 B + coeff 2 A * coeff 0 B := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

lemma coeff_three_mul' : coeff 3 (A * B) = coeff 0 A * coeff 3 B + coeff 1 A * coeff 2 B +
    coeff 2 A * coeff 1 B + coeff 3 A * coeff 0 B := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

end Coeff

/-! ### Level-one forms on `Γ₀(N)` -/


/-- The discriminant `Δ` as a level-one modular form of weight `12`. -/
noncomputable def discriminantForm : ModularForm 𝒮ℒ 12 :=
  CuspForm.toModularFormₗ CuspForm.discriminant

@[simp]
lemma coe_discriminantForm : ⇑discriminantForm = ModularForm.discriminant := by
  ext τ
  simp [discriminantForm, CuspForm.toModularFormₗ_apply]

lemma mul_apply' {k₁ k₂ : ℤ} (f : ModularForm (Gamma0 2) k₁) (g : ModularForm (Gamma0 2) k₂)
    (τ : ℍ) : f.mul g τ = f τ * g τ := by
  rw [ModularForm.coe_mul]
  rfl

/-! ### The forms `ε` and `μ` -/

/-- Larson's weight-four form `ε = (16 V₂E₄ - E₄) / 240 ∈ M₄(Γ₀(2))` [larson2020, Section 3],
with q-expansion `1/16 - q + 7q² - 28q³ + ⋯`. The manuscript writes `ε` as the eta quotient
`η(τ)¹⁶ / (16 η(2τ)⁸)`. -/
noncomputable def eps : ModularForm (Gamma0 2) 4 :=
  (240⁻¹ : ℂ) • ((16 : ℂ) • levelRaise 2 E₄ - ofLevelOne 2 E₄)

/-- `μ = δ² - ε ∈ M₄(Γ₀(2))`. -/
noncomputable def mu : ModularForm (Gamma0 2) 4 :=
  ModularForm.mcast (by norm_num) (delta.mul delta) - eps

lemma eps_apply (τ : ℍ) : eps τ = (16 * E₄ (scaleMatrix 2 • τ) - E₄ τ) / 240 := by
  simp [eps, levelRaise_apply]
  ring

lemma mu_apply (τ : ℍ) : mu τ = delta τ ^ 2 - eps τ := by
  have h : (delta.mul delta : ModularForm (Gamma0 2) (2 + 2)) τ = delta τ * delta τ :=
    mul_apply' _ _ τ
  simp [mu, sq, h]

/-! ### q-expansions through `q³` -/

local notation "hΓ" => one_mem_strictPeriods_Gamma0 2

lemma coeff_E₄ (n : ℕ) :
    (qExpansion 1 E₄).coeff n = if n = 0 then 1 else 240 * (σ 3 n : ℂ) := by
  rw [E_qExpansion_coeff (by norm_num) ⟨2, rfl⟩ n]
  split_ifs
  · rfl
  · norm_num [show bernoulli 4 = -1 / 30 by decide +kernel]

lemma coeff_E₆ (n : ℕ) :
    (qExpansion 1 E₆).coeff n = if n = 0 then 1 else -504 * (σ 5 n : ℂ) := by
  rw [E_qExpansion_coeff (by norm_num) ⟨3, rfl⟩ n]
  split_ifs
  · rfl
  · norm_num [show bernoulli 6 = 1 / 42 by decide +kernel]

lemma qExpansion_eps : qExpansion 1 eps =
    (240⁻¹ : ℂ) • ((16 : ℂ) • qExpansion 1 (levelRaise 2 E₄) - qExpansion 1 E₄) := by
  rw [eps, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos hΓ, FunLike.coe_sub,
    ModularForm.qExpansion_sub one_pos hΓ, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos hΓ, coe_ofLevelOne]

lemma qExpansion_mu : qExpansion 1 mu = qExpansion 1 delta ^ 2 - qExpansion 1 eps := by
  rw [mu, FunLike.coe_sub, ModularForm.qExpansion_sub one_pos hΓ, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_mul one_pos hΓ, sq]

lemma coeff_levelRaise_E₄ :
    (qExpansion 1 (levelRaise 2 E₄)).coeff 0 = 1 ∧ (qExpansion 1 (levelRaise 2 E₄)).coeff 1 = 0 ∧
    (qExpansion 1 (levelRaise 2 E₄)).coeff 2 = 240 ∧
    (qExpansion 1 (levelRaise 2 E₄)).coeff 3 = 0 := by
  simp [qExpansion_levelRaise_coeff, coeff_E₄]

lemma coeff_E₄_le_three : (qExpansion 1 E₄).coeff 0 = 1 ∧ (qExpansion 1 E₄).coeff 1 = 240 ∧
    (qExpansion 1 E₄).coeff 2 = 2160 ∧ (qExpansion 1 E₄).coeff 3 = 6720 := by
  have h2 : σ 3 2 = 9 := by decide
  have h3 : σ 3 3 = 28 := by decide
  simp [coeff_E₄, h2, h3]
  norm_num

lemma coeff_eps : (qExpansion 1 eps).coeff 0 = 1 / 16 ∧ (qExpansion 1 eps).coeff 1 = -1 ∧
    (qExpansion 1 eps).coeff 2 = 7 ∧ (qExpansion 1 eps).coeff 3 = -28 := by
  obtain ⟨a0, a1, a2, a3⟩ := coeff_levelRaise_E₄
  obtain ⟨b0, b1, b2, b3⟩ := coeff_E₄_le_three
  simp only [qExpansion_eps, coeff_smul, map_sub, a0, a1, a2, a3, b0, b1, b2, b3, smul_eq_mul]
  norm_num

lemma coeff_delta : (qExpansion 1 delta).coeff 0 = 1 / 4 ∧ (qExpansion 1 delta).coeff 1 = 6 ∧
    (qExpansion 1 delta).coeff 2 = 6 ∧ (qExpansion 1 delta).coeff 3 = 24 :=
  ⟨qExpansion_delta_coeff_zero, qExpansion_delta_coeff_one, qExpansion_delta_coeff_two,
    qExpansion_delta_coeff_three⟩

lemma coeff_mu : (qExpansion 1 mu).coeff 0 = 0 ∧ (qExpansion 1 mu).coeff 1 = 4 ∧
    (qExpansion 1 mu).coeff 2 = 32 ∧ (qExpansion 1 mu).coeff 3 = 112 := by
  obtain ⟨a0, a1, a2, a3⟩ := coeff_delta
  obtain ⟨b0, b1, b2, b3⟩ := coeff_eps
  simp only [qExpansion_mu, map_sub, sq, coeff_zero_mul', coeff_one_mul', coeff_two_mul',
    coeff_three_mul', a0, a1, a2, a3, b0, b1, b2, b3]
  norm_num

lemma coeff_discriminant : (qExpansion 1 ModularForm.discriminant).coeff 0 = 0 ∧
    (qExpansion 1 ModularForm.discriminant).coeff 1 = 1 ∧
    (qExpansion 1 ModularForm.discriminant).coeff 2 = -24 ∧
    (qExpansion 1 ModularForm.discriminant).coeff 3 = 252 := by
  have h := LevelOne.qExpansion_discriminant_mul
  have h32 : σ 3 2 = 9 := by decide
  have h33 : σ 3 3 = 28 := by decide
  have h52 : σ 5 2 = 33 := by decide
  have h53 : σ 5 3 = 244 := by decide
  have hc (n : ℕ) := congrArg (coeff n) h
  simp only [coeff_ofNat_mul, map_sub, pow_succ, pow_zero, one_mul] at hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hc 0
    simp only [coeff_zero_mul', coeff_E₄, coeff_E₆] at this
    norm_num at this
    simpa using this
  · have := hc 1
    simp only [coeff_zero_mul', coeff_one_mul', coeff_E₄, coeff_E₆] at this
    norm_num at this
    exact this
  · have := hc 2
    simp only [coeff_zero_mul', coeff_one_mul', coeff_two_mul', coeff_E₄, coeff_E₆] at this
    norm_num [h32, h52] at this
    linear_combination this / 1728
  · have := hc 3
    simp only [coeff_zero_mul', coeff_one_mul', coeff_two_mul', coeff_three_mul', coeff_E₄,
      coeff_E₆] at this
    norm_num [h32, h33, h52, h53] at this
    linear_combination this / 1728

/-! ### The identities -/

/-- Two forms of weight `12` on `Γ₀(2)` with the same q-expansion through `q³` are equal. -/
lemma eq_of_coeff_eq_weight_twelve {f g : ModularForm (Gamma0 2) 12}
    (h : ∀ n < 4, (qExpansion 1 f).coeff n = (qExpansion 1 g).coeff n) : f = g := by
  rw [← sub_eq_zero]
  apply sturm_bound_Gamma0_two
  have h4 : ((4 : ℕ) : ℕ∞) ≤ (qExpansion 1 (f - g)).order := by
    refine PowerSeries.nat_le_order _ 4 fun i hi ↦ ?_
    rw [ModularForm.qExpansion_sub one_pos hΓ, map_sub, h i hi, sub_self]
  refine lt_of_lt_of_le ?_ h4
  norm_num

/-- Two forms of weight `4` on `Γ₀(2)` with the same q-expansion through `q` are equal. -/
lemma eq_of_coeff_eq_weight_four {f g : ModularForm (Gamma0 2) 4}
    (h : ∀ n < 2, (qExpansion 1 f).coeff n = (qExpansion 1 g).coeff n) : f = g := by
  rw [← sub_eq_zero]
  apply sturm_bound_Gamma0_two
  have h2 : ((2 : ℕ) : ℕ∞) ≤ (qExpansion 1 (f - g)).order := by
    refine PowerSeries.nat_le_order _ 2 fun i hi ↦ ?_
    rw [ModularForm.qExpansion_sub one_pos hΓ, map_sub, h i hi, sub_self]
  refine lt_of_lt_of_le ?_ h2
  norm_num

/-- **Lemma 3.1, first identity.** `Δ = 64 μ ε²` in `M₁₂(Γ₀(2))`. -/
theorem discriminant_eq :
    ofLevelOne 2 discriminantForm = (64 : ℂ) • ((mu.mul eps).mul eps : ModularForm _ 12) := by
  apply eq_of_coeff_eq_weight_twelve
  obtain ⟨a0, a1, a2, a3⟩ := coeff_mu
  obtain ⟨b0, b1, b2, b3⟩ := coeff_eps
  obtain ⟨c0, c1, c2, c3⟩ := coeff_discriminant
  intro n hn
  rw [coe_ofLevelOne, coe_discriminantForm, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos hΓ,
    ModularForm.qExpansion_mul one_pos hΓ, ModularForm.qExpansion_mul one_pos hΓ, coeff_smul]
  interval_cases n <;>
    simp only [coeff_zero_mul', coeff_one_mul', coeff_two_mul', coeff_three_mul', a0, a1, a2,
      a3, b0, b1, b2, b3, c0, c1, c2, c3, smul_eq_mul] <;> norm_num

/-- **Lemma 3.1, second identity.** `V₂(Δ) = μ² ε` in `M₁₂(Γ₀(2))`. -/
theorem levelRaise_discriminant_eq :
    levelRaise 2 discriminantForm = ((mu.mul mu).mul eps : ModularForm _ 12) := by
  apply eq_of_coeff_eq_weight_twelve
  obtain ⟨a0, a1, a2, a3⟩ := coeff_mu
  obtain ⟨b0, b1, b2, b3⟩ := coeff_eps
  obtain ⟨c0, c1, c2, c3⟩ := coeff_discriminant
  intro n hn
  rw [qExpansion_levelRaise_coeff, coe_discriminantForm, ModularForm.qExpansion_mul one_pos hΓ,
    ModularForm.qExpansion_mul one_pos hΓ]
  interval_cases n <;>
    simp only [coeff_zero_mul', coeff_one_mul', coeff_two_mul', coeff_three_mul', a0, a1, a2,
      a3, b0, b1, b2, b3, c0, c1] <;> norm_num [c1]

/-- `Δ(τ) = 64 μ(τ) ε(τ)²`. -/
theorem discriminant_apply_eq (τ : ℍ) : ModularForm.discriminant τ = 64 * mu τ * eps τ ^ 2 := by
  have := congrArg (fun f : ModularForm (Gamma0 2) 12 ↦ f τ) discriminant_eq
  simp only [coe_ofLevelOne, coe_discriminantForm] at this
  have h : ((mu.mul eps).mul eps : ModularForm (Gamma0 2) (4 + 4 + 4)) τ =
      mu τ * eps τ * eps τ := by
    rw [mul_apply', mul_apply']
  rw [this, IsSMulApply.smul_apply, smul_eq_mul]
  exact (congrArg _ h).trans (by ring)

/-- `Δ(2τ) = μ(τ)² ε(τ)`. -/
theorem discriminant_scaleMatrix_apply_eq (τ : ℍ) :
    ModularForm.discriminant (scaleMatrix 2 • τ) = mu τ ^ 2 * eps τ := by
  have := congrArg (fun f : ModularForm (Gamma0 2) 12 ↦ f τ) levelRaise_discriminant_eq
  simp only [levelRaise_apply, coe_discriminantForm] at this
  have h : ((mu.mul mu).mul eps : ModularForm (Gamma0 2) (4 + 4 + 4)) τ =
      mu τ * mu τ * eps τ := by
    rw [mul_apply', mul_apply']
  rw [this]
  exact h.trans (by ring)

/-- Larson's identity `E₄ = 64 μ + 16 ε` [larson2020, Section 3]. -/
theorem E₄_eq : ofLevelOne 2 E₄ = (64 : ℂ) • mu + (16 : ℂ) • eps := by
  apply eq_of_coeff_eq_weight_four
  obtain ⟨a0, a1, a2, a3⟩ := coeff_mu
  obtain ⟨b0, b1, b2, b3⟩ := coeff_eps
  obtain ⟨c0, c1, c2, c3⟩ := coeff_E₄_le_three
  intro n hn
  rw [coe_ofLevelOne, FunLike.coe_add, ModularForm.qExpansion_add one_pos hΓ, FunLike.coe_smul,
    FunLike.coe_smul, ModularForm.qExpansion_smul one_pos hΓ,
    ModularForm.qExpansion_smul one_pos hΓ]
  interval_cases n <;> simp only [map_add, coeff_smul, a0, a1, b0, b1, c0, c1, smul_eq_mul] <;>
    norm_num

/-- Larson's identity `V₂E₄ = 4 μ + 16 ε` [larson2020, Section 3]. -/
theorem levelRaise_E₄_eq : levelRaise 2 E₄ = (4 : ℂ) • mu + (16 : ℂ) • eps := by
  apply eq_of_coeff_eq_weight_four
  obtain ⟨a0, a1, a2, a3⟩ := coeff_mu
  obtain ⟨b0, b1, b2, b3⟩ := coeff_eps
  obtain ⟨c0, c1, c2, c3⟩ := coeff_levelRaise_E₄
  intro n hn
  rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos hΓ, FunLike.coe_smul,
    FunLike.coe_smul, ModularForm.qExpansion_smul one_pos hΓ,
    ModularForm.qExpansion_smul one_pos hΓ]
  interval_cases n <;> simp only [map_add, coeff_smul, a0, a1, b0, b1, c0, c1, smul_eq_mul] <;>
    norm_num

/-- `80 δ² = E₄ + 4 V₂E₄`. -/
theorem delta_sq_eq :
    (80 : ℂ) • ModularForm.mcast (by norm_num) (delta.mul delta) =
      ofLevelOne 2 E₄ + (4 : ℂ) • levelRaise 2 E₄ := by
  rw [E₄_eq, levelRaise_E₄_eq, mu]
  ext τ
  simp
  ring

end LevelTwoForms
