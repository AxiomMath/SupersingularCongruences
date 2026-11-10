/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.LevelTwoForms.LevelRaise
public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# A Sturm bound for `Γ₀(2)`

A modular form `f ∈ M_k(Γ₀(2))` whose q-expansion at `∞` vanishes to order greater than
`3k / 12` is zero. We deduce this from Mathlib's level-one Sturm bound
`ModularForm.sturm_bound_levelOne` applied to the norm `N(f) = ∏_{γ ∈ SL(2,ℤ)/Γ₀(2)} f ∣[k] γ⁻¹`
(`ModularForm.norm`), a level-one form of weight `k · [SL(2, ℤ) : Γ₀(2)]`:

* `[SL(2, ℤ) : Γ₀(2)] ≤ 3`, with coset representatives `1`, `S`, `TS`;
* every factor `f ∣[k] γ⁻¹` is invariant under `Γ(2)`, so all factors have q-expansions in
  `q^(1/2) = exp(πiτ)`; the factor for the trivial coset is `f` itself, so the order of vanishing
  of `N(f)` at `∞` is at least that of `f`.

## Main results

* `LevelTwoForms.card_quotient_Gamma0_two_le`: `[SL(2, ℤ) : Γ₀(2)] ≤ 3`.
* `LevelTwoForms.qExpansion_two_coeff`: the q-expansion in `exp(πiτ)` of a form of period `1`.
* `LevelTwoForms.sturm_bound_Gamma0_two`: the Sturm bound for `Γ₀(2)`.
-/

public section

open ModularForm UpperHalfPlane Matrix CongruenceSubgroup Matrix.SpecialLinearGroup
  SlashInvariantForm
open scoped MatrixGroups ModularForm ConjAct Pointwise

local notation "𝕢" => Function.Periodic.qParam

namespace LevelTwoForms

/-! ### The index of `Γ₀(2)` -/

/-- Coset representatives `1`, `S`, `TS` of `SL(2, ℤ) / Γ₀(2)`. -/
private def cosetRep : Fin 3 → SL(2, ℤ) := ![1, ModularGroup.S, ModularGroup.T * ModularGroup.S]

private lemma exists_cosetRep_inv_mul_mem (γ : SL(2, ℤ)) :
    ∃ i, (cosetRep i)⁻¹ * γ ∈ Gamma0 2 := by
  have hdet := γ.2
  rw [det_fin_two] at hdet
  have hnot : ¬ ((2 : ℤ) ∣ γ 0 0 ∧ (2 : ℤ) ∣ γ 1 0) := by
    rintro ⟨⟨a, ha⟩, ⟨c, hc⟩⟩
    have : (2 : ℤ) ∣ 1 :=
      ⟨a * γ 1 1 - γ 0 1 * c, by linear_combination -hdet + γ 1 1 * ha - γ 0 1 * hc⟩
    norm_num at this
  simp only [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_ofNat]
  by_cases hc : (2 : ℤ) ∣ γ 1 0
  · exact ⟨0, by simpa [cosetRep] using hc⟩
  by_cases ha : (2 : ℤ) ∣ γ 0 0
  · refine ⟨1, ?_⟩
    simpa [cosetRep, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two,
      SpecialLinearGroup.coe_inv, adjugate_fin_two] using ha
  · refine ⟨2, ?_⟩
    simp [cosetRep, ModularGroup.coe_S, ModularGroup.coe_T, Matrix.mul_apply, Fin.sum_univ_two,
      adjugate_fin_two]
    omega

/-- `[SL(2, ℤ) : Γ₀(2)] ≤ 3`. -/
lemma card_quotient_Gamma0_two_le :
    Nat.card (𝒮ℒ ⧸ (Gamma0 2 : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ≤ 3 := by
  let r : Fin 3 → (𝒮ℒ ⧸ (Gamma0 2 : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :=
    fun i ↦ QuotientGroup.mk ⟨mapGL ℝ (cosetRep i), ⟨_, rfl⟩⟩
  have hr : Function.Surjective r := by
    intro x
    induction x using QuotientGroup.induction_on with | H h =>
    obtain ⟨_, γ, rfl⟩ := h
    obtain ⟨i, hi⟩ := exists_cosetRep_inv_mul_mem γ
    refine ⟨i, QuotientGroup.eq.mpr ?_⟩
    rw [Subgroup.mem_subgroupOf]
    simpa using Subgroup.mem_map_of_mem (mapGL ℝ) hi
  simpa using Nat.card_le_card_of_surjective r hr

/-! ### Period doubling of q-expansions -/

lemma qParam_two_sq (τ : ℍ) : 𝕢 2 τ ^ 2 = 𝕢 1 τ := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- If `f` has period `1`, its q-expansion in `exp(πiτ)` is `f(q²)`. -/
lemma qExpansion_two_coeff {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) (h1 : (1 : ℝ) ∈ Γ.strictPeriods) (n : ℕ) :
    (qExpansion 2 f).coeff n = if 2 ∣ n then (qExpansion 1 f).coeff (n / 2) else 0 := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos h1⟩
  have h2 : (2 : ℝ) ∈ Γ.strictPeriods := by
    simpa [one_add_one_eq_two] using add_mem h1 h1
  refine qExpansion_coeff_of_hasSum (f := f)
    (c := fun n ↦ if 2 ∣ n then (qExpansion 1 f).coeff (n / 2) else 0) two_pos h2 (fun τ ↦ ?_) n
  refine hasSum_reindex_pow 2 (c := fun m ↦ (qExpansion 1 f).coeff m) (z := 𝕢 2 τ) ?_
  rw [qParam_two_sq]
  exact ModularForm.hasSum_qExpansion f one_pos h1 τ

/-! ### Analyticity of products of cusp functions -/

lemma cuspFunction_one (h : ℝ) : cuspFunction h (1 : ℍ → ℂ) = 1 := by
  ext q
  rcases eq_or_ne q 0 with rfl | hq
  · simpa [cuspFunction, Function.Periodic.cuspFunction] using!
      tendsto_const_nhds.limUnder_eq
  · simp [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero h _ hq]

lemma analyticAt_cuspFunction_prod {ι : Type*} {h : ℝ} (s : Finset ι) (φ : ι → ℍ → ℂ)
    (hφ : ∀ i ∈ s, AnalyticAt ℂ (cuspFunction h (φ i)) 0) :
    AnalyticAt ℂ (cuspFunction h (∏ i ∈ s, φ i)) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, cuspFunction_one]
    exact analyticAt_const (v := (1 : ℂ))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 := hφ a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi ↦ hφ i (Finset.mem_insert_of_mem hi)
    rw [cuspFunction_mul h1.continuousAt h2.continuousAt]
    exact h1.mul h2

/-! ### The norm of a form on `Γ₀(2)` -/

lemma Gamma_le_Gamma0 (N : ℕ) : Gamma N ≤ Gamma0 N := fun _ hγ ↦
  Gamma0_mem.mpr (Gamma_mem.mp hγ).2.2.1

/-- `Γ(2)` is contained in every `SL(2, ℤ)`-conjugate of `Γ₀(2)`. -/
lemma Gamma_two_le_conj (h : 𝒮ℒ) :
    (Gamma 2 : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct h.1 • (Gamma0 2 : Subgroup (GL (Fin 2) ℝ)) := by
  obtain ⟨_, γ, rfl⟩ := h
  rintro _ ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    ConjAct.toConjAct_smul, inv_inv, ← map_inv, ← map_mul, ← map_mul]
  refine Subgroup.mem_map_of_mem _ (Gamma_le_Gamma0 2 ?_)
  simpa using (Gamma_normal 2).conj_mem δ hδ γ⁻¹

lemma two_mem_strictPeriods_conj (h : 𝒮ℒ) :
    (2 : ℝ) ∈ (ConjAct.toConjAct h.1 • (Gamma0 2 : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  have h2 : (2 : ℝ) ∈ (Gamma 2 : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [AddSubgroup.mem_zmultiples]
  rw [Subgroup.mem_strictPeriods_iff] at h2 ⊢
  exact Gamma_two_le_conj h h2

variable {k : ℤ}

lemma analyticAt_cuspFunction_quotientFunc (f : ModularForm (Gamma0 2) k)
    (q : 𝒮ℒ ⧸ (Gamma0 2 : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :
    AnalyticAt ℂ (cuspFunction 2 (quotientFunc (k := k) f q)) 0 := by
  induction q using QuotientGroup.induction_on with | H h =>
  have hq : quotientFunc (k := k) f (QuotientGroup.mk h) = ⇑(ModularForm.translate f h.1⁻¹) :=
    quotientFunc_mk f h
  rw [hq]
  have h2 := two_mem_strictPeriods_conj h
  rw [← inv_inv h.1] at h2
  exact ModularFormClass.analyticAt_cuspFunction_zero _ two_pos h2

/-- The norm `N(f)` vanishes at `∞` to order at least the order of `f`. -/
lemma qExpansion_norm_coeff_eq_zero (f : ModularForm (Gamma0 2) k) {m : ℕ}
    (hf : ∀ n < m, (qExpansion 1 f).coeff n = 0) :
    ∀ n < m, (qExpansion 1 (ModularForm.norm 𝒮ℒ f)).coeff n = 0 := by
  classical
  let := Fintype.ofFinite (𝒮ℒ ⧸ (Gamma0 2 : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  set q₁ : 𝒮ℒ ⧸ (Gamma0 2 : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ := QuotientGroup.mk 1
  set G : ℍ → ℂ := ∏ q ∈ Finset.univ.erase q₁, quotientFunc (k := k) f q
  have hfun : ⇑(ModularForm.norm 𝒮ℒ f) = ⇑f * G := by
    rw [ModularForm.coe_norm, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₁)]
    congr 1
    simp [q₁]
  have hG : AnalyticAt ℂ (cuspFunction 2 G) 0 :=
    analyticAt_cuspFunction_prod _ _ fun q _ ↦ analyticAt_cuspFunction_quotientFunc f q
  have h1 := one_mem_strictPeriods_Gamma0 2
  have hf2 : AnalyticAt ℂ (cuspFunction 2 f) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero f two_pos (by
      simpa [one_add_one_eq_two] using add_mem h1 h1)
  have hdvd : PowerSeries.X ^ (2 * m) ∣ qExpansion 2 f := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    rw [qExpansion_two_coeff f h1]
    split_ifs with h2j
    · exact hf _ (by omega)
    · rfl
  have hmul : qExpansion 2 (ModularForm.norm 𝒮ℒ f) = qExpansion 2 f * qExpansion 2 G := by
    rw [hfun, UpperHalfPlane.qExpansion_mul hf2 hG]
  intro n hn
  have := qExpansion_two_coeff (ModularForm.norm 𝒮ℒ f) one_mem_strictPeriods_SL (2 * n)
  simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left n two_pos] at this
  rw [← this, hmul]
  exact PowerSeries.X_pow_dvd_iff.mp (dvd_mul_of_dvd_left hdvd _) _ (by omega)

private lemma toNat_mul_le {k : ℤ} {c : ℕ} (hc : c ≤ 3) : (k * c).toNat ≤ (3 * k).toNat := by
  interval_cases c <;> omega

/-- **Sturm bound for `Γ₀(2)`.** A modular form of weight `k` on `Γ₀(2)` whose q-expansion has
order greater than `3k / 12` (the Sturm bound `k [SL(2, ℤ) : Γ₀(2)] / 12`) is zero. -/
theorem sturm_bound_Gamma0_two (f : ModularForm (Gamma0 2) k)
    (h : (↑((3 * k).toNat / 12) : ℕ∞) < (qExpansion 1 f).order) : f = 0 := by
  set m := (3 * k).toNat / 12 + 1
  have hf : ∀ n < m, (qExpansion 1 f).coeff n = 0 := fun n hn ↦
    PowerSeries.coeff_of_lt_order _ (lt_of_le_of_lt (by exact_mod_cast Nat.lt_succ_iff.mp hn) h)
  have hN := PowerSeries.nat_le_order _ m (qExpansion_norm_coeff_eq_zero f hf)
  have hcard := card_quotient_Gamma0_two_le
  have hle : (k * (Nat.card (𝒮ℒ ⧸ (Gamma0 2 : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) : ℤ)).toNat
      / 12 < m := by
    have := Nat.div_le_div_right (c := 12) (toNat_mul_le (k := k) hcard)
    omega
  have hzero := ModularForm.sturm_bound_levelOne (f := ModularForm.norm 𝒮ℒ f)
    (lt_of_lt_of_le (by exact_mod_cast hle) hN)
  rw [ModularForm.norm_eq_zero_iff] at hzero
  ext τ
  simpa using congr_fun hzero τ

end LevelTwoForms
