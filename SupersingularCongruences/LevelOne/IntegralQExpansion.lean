/-
Assembled by AxiomProver.
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# Integral q-expansions of level-one modular forms

A power series `G ∈ ℤ⟦X⟧` is an *integral q-expansion* of a function `f : ℍ → ℂ` if its image in
`ℂ⟦X⟧` is the q-expansion `qExpansion 1 f` of `f` at `i∞`. Since `ℤ⟦X⟧ → ℂ⟦X⟧` is injective, the
integral q-expansion of `f` is unique when it exists; for a level-one form with integral
coefficients this is the series `∑ aₙ qⁿ` of the manuscript, and its reduction modulo `p` is
`PowerSeries.map (Int.castRingHom (ZMod p)) G`.

## Main results

* `LevelOne.isIntegralQExpansion_E₄`, `LevelOne.isIntegralQExpansion_E₆`: the Eisenstein series
  `E₄ = 1 + 240 ∑ σ₃(n) qⁿ` and `E₆ = 1 - 504 ∑ σ₅(n) qⁿ` have integral q-expansions.
* `LevelOne.isIntegralQExpansion_discriminant`: the discriminant `Δ = (E₄³ - E₆²) / 1728` has an
  integral q-expansion `LevelOne.integralDiscriminant`, with constant term `0` and `q`-coefficient
  `1`; it factors as `X * u` with `u` a unit of `ℤ⟦X⟧`.
* `LevelOne.exists_isIntegralQExpansion_coeff_zero_eq_one`: in every even weight `k ≥ 0`,
  `k ≠ 2`, there is a level-one form `E₄ᵃ E₆ᵇ` with integral q-expansion and constant term `1`.
* `LevelOne.exists_isIntegralQExpansion_discriminantEquiv`: if `f` has an integral q-expansion
  with constant term `0`, then so does `f / Δ`.
-/

public section

open ModularForm EisensteinSeries PowerSeries UpperHalfPlane
open scoped ArithmeticFunction.sigma MatrixGroups

namespace LevelOne

/-- `G ∈ ℤ⟦X⟧` is an integral q-expansion of `f`: its image in `ℂ⟦X⟧` is `qExpansion 1 f`. -/
def IsIntegralQExpansion (G : PowerSeries ℤ) (f : ℍ → ℂ) : Prop :=
  PowerSeries.map (Int.castRingHom ℂ) G = qExpansion 1 f

lemma isIntegralQExpansion_iff {G : PowerSeries ℤ} {f : ℍ → ℂ} :
    IsIntegralQExpansion G f ↔ PowerSeries.map (Int.castRingHom ℂ) G = qExpansion 1 f :=
  Iff.rfl

lemma IsIntegralQExpansion.coeff {G : PowerSeries ℤ} {f : ℍ → ℂ} (hG : IsIntegralQExpansion G f)
    (n : ℕ) : (qExpansion 1 f).coeff n = (G.coeff n : ℂ) := by
  rw [← hG, coeff_map, eq_intCast]

lemma map_intCast_injective :
    Function.Injective (PowerSeries.map (Int.castRingHom ℂ)) :=
  PowerSeries.map_injective _ (RingHom.injective_int _)

/-- The integral q-expansion of a function is unique. -/
lemma IsIntegralQExpansion.unique {G H : PowerSeries ℤ} {f : ℍ → ℂ}
    (hG : IsIntegralQExpansion G f) (hH : IsIntegralQExpansion H f) : G = H :=
  map_intCast_injective (hG.trans hH.symm)

/-- The integral q-expansion of the zero modular form is `0`. -/
lemma IsIntegralQExpansion.eq_zero {k : ℤ} {f : ModularForm 𝒮ℒ k} {G : PowerSeries ℤ}
    (hG : IsIntegralQExpansion G f) (hf : f = 0) : G = 0 := by
  apply map_intCast_injective
  rw [hG, hf, map_zero]
  exact qExpansion_zero 1

lemma isIntegralQExpansion_add {G H : PowerSeries ℤ} {k : ℤ} {f g : ModularForm 𝒮ℒ k}
    (hG : IsIntegralQExpansion G f) (hH : IsIntegralQExpansion H g) :
    IsIntegralQExpansion (G + H) ⇑(f + g) := by
  rw [isIntegralQExpansion_iff, map_add, hG, hH, FunLike.coe_add,
    ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL]

lemma isIntegralQExpansion_sub {G H : PowerSeries ℤ} {k : ℤ} {f g : ModularForm 𝒮ℒ k}
    (hG : IsIntegralQExpansion G f) (hH : IsIntegralQExpansion H g) :
    IsIntegralQExpansion (G - H) ⇑(f - g) := by
  rw [isIntegralQExpansion_iff, map_sub, hG, hH, FunLike.coe_sub,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]

lemma isIntegralQExpansion_mul {G H : PowerSeries ℤ} {k₁ k₂ : ℤ} {f : ModularForm 𝒮ℒ k₁}
    {g : ModularForm 𝒮ℒ k₂} (hG : IsIntegralQExpansion G f) (hH : IsIntegralQExpansion H g) :
    IsIntegralQExpansion (G * H) (f.mul g) := by
  rw [isIntegralQExpansion_iff, map_mul, hG, hH,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL]

lemma isIntegralQExpansion_pow {G : PowerSeries ℤ} {k : ℤ} {f : ModularForm 𝒮ℒ k}
    (hG : IsIntegralQExpansion G f) (n : ℕ) : IsIntegralQExpansion (G ^ n) (f.pow n) := by
  rw [isIntegralQExpansion_iff, map_pow, hG,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

lemma isIntegralQExpansion_intCast_smul {G : PowerSeries ℤ} {k : ℤ} {f : ModularForm 𝒮ℒ k}
    (hG : IsIntegralQExpansion G f) (c : ℤ) :
    IsIntegralQExpansion (PowerSeries.C c * G) ⇑((c : ℂ) • f) := by
  rw [isIntegralQExpansion_iff, map_mul, hG, map_C, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, smul_eq_C_mul]
  rfl

/-! ### The Eisenstein series `E₄` and `E₆` -/

/-- The integral power series `1 + 240 ∑_{n ≥ 1} σ₃(n) Xⁿ`, the q-expansion of `E₄`. -/
def integralE₄ : PowerSeries ℤ :=
  PowerSeries.mk fun n ↦ if n = 0 then 1 else 240 * (σ 3 n : ℤ)

/-- The integral power series `1 - 504 ∑_{n ≥ 1} σ₅(n) Xⁿ`, the q-expansion of `E₆`. -/
def integralE₆ : PowerSeries ℤ :=
  PowerSeries.mk fun n ↦ if n = 0 then 1 else -504 * (σ 5 n : ℤ)

/-- `E₄ = 1 + 240 ∑ σ₃(n) qⁿ`. -/
theorem isIntegralQExpansion_E₄ : IsIntegralQExpansion integralE₄ E₄ := by
  rw [isIntegralQExpansion_iff]
  ext n
  rw [coeff_map, E_qExpansion_coeff _ ⟨2, rfl⟩ n, integralE₄, coeff_mk]
  split_ifs
  · simp
  · norm_num [show bernoulli 4 = -1 / 30 by decide +kernel]

/-- `E₆ = 1 - 504 ∑ σ₅(n) qⁿ`. -/
theorem isIntegralQExpansion_E₆ : IsIntegralQExpansion integralE₆ E₆ := by
  rw [isIntegralQExpansion_iff]
  ext n
  rw [coeff_map, E_qExpansion_coeff _ ⟨3, rfl⟩ n, integralE₆, coeff_mk]
  split_ifs
  · simp
  · norm_num [show bernoulli 6 = 1 / 42 by decide +kernel]

lemma constantCoeff_integralE₄ : constantCoeff integralE₄ = 1 := by
  simp [integralE₄, ← coeff_zero_eq_constantCoeff_apply]

lemma constantCoeff_integralE₆ : constantCoeff integralE₆ = 1 := by
  simp [integralE₆, ← coeff_zero_eq_constantCoeff_apply]

/-! ### The discriminant -/

/-- The integral power series `(E₄³ - E₆²) / 1728`, computed coefficientwise in `ℤ`
(the division is exact, see `integralDiscriminant_mul`). -/
noncomputable def integralDiscriminant : PowerSeries ℤ :=
  PowerSeries.mk fun n ↦ (integralE₄ ^ 3 - integralE₆ ^ 2).coeff n / 1728

private lemma twelve_dvd_five_mul_pow_three_add_seven_mul_pow_five (d : ℕ) :
    12 ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
  apply Nat.dvd_of_mod_eq_zero
  have h := Nat.mod_lt d (show 0 < 12 by norm_num)
  rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mul_mod 7, Nat.pow_mod d 5]
  interval_cases d % 12 <;> norm_num

lemma twelve_dvd_sigma (n : ℕ) : 12 ∣ 5 * σ 3 n + 7 * σ 5 n := by
  simp only [ArithmeticFunction.sigma_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.dvd_sum fun d _ ↦ twelve_dvd_five_mul_pow_three_add_seven_mul_pow_five d

/-- The identity `E₄³ - E₆² = 1728 Δ` holds in `ℤ⟦X⟧`. -/
theorem integralDiscriminant_mul :
    1728 * integralDiscriminant = integralE₄ ^ 3 - integralE₆ ^ 2 := by
  set a : PowerSeries ℤ := PowerSeries.mk fun n ↦ (σ 3 n : ℤ)
  set b : PowerSeries ℤ := PowerSeries.mk fun n ↦ (σ 5 n : ℤ)
  set c : PowerSeries ℤ := PowerSeries.mk fun n ↦ (((5 * σ 3 n + 7 * σ 5 n) / 12 : ℕ) : ℤ)
  have h4 : integralE₄ = 1 + 240 * a := by
    ext n
    rcases n with _ | n <;> simp [integralE₄, a, coeff_one]
  have h6 : integralE₆ = 1 - 504 * b := by
    ext n
    rcases n with _ | n <;> simp [integralE₆, b, coeff_one]
  have hc : 5 * a + 7 * b = 12 * c := by
    ext n
    have := Nat.div_mul_cancel (twelve_dvd_sigma n)
    simp only [map_add, coeff_ofNat_mul, coeff_mk, a, b, c]
    omega
  have key : integralE₄ ^ 3 - integralE₆ ^ 2 =
      1728 * (c + 100 * a ^ 2 + 8000 * a ^ 3 - 147 * b ^ 2) := by
    rw [h4, h6]
    linear_combination 144 * hc
  rw [key]
  congr 1
  ext n
  rw [integralDiscriminant, coeff_mk, key, coeff_ofNat_mul]
  exact Int.mul_ediv_cancel_left _ (by norm_num)

/-- The q-expansion identity `1728 Δ = E₄³ - E₆²` in `ℂ⟦X⟧`. -/
lemma qExpansion_discriminant_mul :
    1728 * qExpansion 1 ModularForm.discriminant =
      qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2 := by
  set F : ModularForm 𝒮ℒ 12 :=
    ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)
  have hF : qExpansion 1 F = qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2 := by
    simp only [F, FunLike.coe_sub, coe_mcast,
      ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have hΔ : (ModularForm.discriminant : ℍ → ℂ) = (1 / 1728 : ℂ) • ⇑F := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, F, FunLike.coe_sub, coe_mcast, coe_pow, Pi.sub_apply,
      Pi.pow_apply, discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  rw [hΔ, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, hF, smul_eq_C_mul,
    ← mul_assoc, ← map_ofNat (C (R := ℂ)) 1728, ← map_mul]
  norm_num

/-- `Δ = (E₄³ - E₆²) / 1728` has integral q-expansion `integralDiscriminant`. -/
theorem isIntegralQExpansion_discriminant :
    IsIntegralQExpansion integralDiscriminant ModularForm.discriminant := by
  rw [isIntegralQExpansion_iff]
  have h := congrArg (PowerSeries.map (Int.castRingHom ℂ)) integralDiscriminant_mul
  rw [map_mul, map_sub, map_pow, map_pow, isIntegralQExpansion_E₄, isIntegralQExpansion_E₆,
    ← qExpansion_discriminant_mul, map_ofNat] at h
  refine mul_left_cancel₀ (fun h1728 ↦ ?_) h
  have := congrArg (constantCoeff (R := ℂ)) h1728
  rw [map_ofNat, map_zero] at this
  norm_num at this

lemma coeff_zero_integralDiscriminant : integralDiscriminant.coeff 0 = 0 := by
  have h := isIntegralQExpansion_discriminant.coeff 0
  have h0 : (qExpansion 1 ModularForm.discriminant).coeff 0 = 0 :=
    CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos one_mem_strictPeriods_SL
  rw [h0] at h
  exact_mod_cast h.symm

lemma coeff_one_integralDiscriminant : integralDiscriminant.coeff 1 = 1 := by
  have h := isIntegralQExpansion_discriminant.coeff 1
  rw [discriminant_qExpansion_coeff_one] at h
  exact_mod_cast h.symm

/-- `Δ = X * u` in `ℤ⟦X⟧` with `u` of constant term `1` (hence a unit). -/
theorem exists_integralDiscriminant_eq_X_mul :
    ∃ u : PowerSeries ℤ, constantCoeff u = 1 ∧ integralDiscriminant = X * u := by
  obtain ⟨u, hu⟩ := (X_dvd_iff (φ := integralDiscriminant)).mpr
    (by rw [← coeff_zero_eq_constantCoeff_apply]; exact coeff_zero_integralDiscriminant)
  refine ⟨u, ?_, hu⟩
  have h := coeff_one_integralDiscriminant
  rw [hu, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul] at h
  rwa [← coeff_zero_eq_constantCoeff_apply]

/-- A series with constant term `0` is divisible by `integralDiscriminant` in `ℤ⟦X⟧`. -/
theorem integralDiscriminant_dvd {G : PowerSeries ℤ} (hG : G.coeff 0 = 0) :
    integralDiscriminant ∣ G := by
  obtain ⟨u, hu1, hu⟩ := exists_integralDiscriminant_eq_X_mul
  obtain ⟨G', hG'⟩ := (X_dvd_iff (φ := G)).mpr
    (by rw [← coeff_zero_eq_constantCoeff_apply]; exact hG)
  obtain ⟨v, hv⟩ : IsUnit u := isUnit_iff_constantCoeff.mpr (by rw [hu1]; exact isUnit_one)
  refine ⟨G' * ↑v⁻¹, ?_⟩
  rw [hu, hG', ← hv]
  calc X * G' = X * (↑v * ↑v⁻¹) * G' := by rw [Units.mul_inv, mul_one]
    _ = X * ↑v * (G' * ↑v⁻¹) := by ring

/-! ### Forms of constant term one and division by `Δ` -/

/-- In every even weight `k ≥ 0` with `k ≠ 2` there is a level-one form (a product `E₄ᵃ E₆ᵇ`)
with integral q-expansion of constant term `1`. -/
theorem exists_isIntegralQExpansion_coeff_zero_eq_one {k : ℤ} (hk0 : 0 ≤ k) (hk : Even k)
    (hk2 : k ≠ 2) :
    ∃ (e : ModularForm 𝒮ℒ k) (E : PowerSeries ℤ), IsIntegralQExpansion E e ∧ E.coeff 0 = 1 := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, (a : ℤ) * 4 + (b : ℤ) * 6 = k := by
    obtain ⟨m, rfl⟩ := hk
    rcases Int.emod_two_eq_zero_or_one m with h | h
    · exact ⟨(m / 2).toNat, 0, by omega⟩
    · exact ⟨((m - 3) / 2).toNat, 1, by omega⟩
  refine ⟨ModularForm.mcast hab ((E₄.pow a).mul (E₆.pow b)), integralE₄ ^ a * integralE₆ ^ b,
    ?_, ?_⟩
  · rw [coe_mcast]
    exact isIntegralQExpansion_mul (isIntegralQExpansion_pow isIntegralQExpansion_E₄ a)
      (isIntegralQExpansion_pow isIntegralQExpansion_E₆ b)
  · rw [coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, map_pow, constantCoeff_integralE₄,
      constantCoeff_integralE₆, one_pow, one_pow, one_mul]

/-- If `f` has an integral q-expansion `G` with constant term `0`, then `f / Δ` has an integral
q-expansion `H` with `G = Δ * H`. -/
theorem exists_isIntegralQExpansion_discriminantEquiv {k : ℤ} (f : ModularForm 𝒮ℒ k)
    (h0 : (qExpansion 1 f).coeff 0 = 0) {G : PowerSeries ℤ} (hG : IsIntegralQExpansion G f) :
    ∃ H : PowerSeries ℤ,
      IsIntegralQExpansion H (CuspForm.discriminantEquiv (toCuspForm f h0)) ∧
        G = integralDiscriminant * H := by
  have hG0 : G.coeff 0 = 0 := by
    have h := hG.coeff 0
    rw [h0] at h
    exact_mod_cast h.symm
  obtain ⟨H, hH⟩ := integralDiscriminant_dvd hG0
  refine ⟨H, ?_, hH⟩
  have hne : qExpansion 1 ModularForm.discriminant ≠ 0 := by
    intro h
    have := discriminant_qExpansion_coeff_one
    rw [h, map_zero] at this
    exact zero_ne_one this
  have h := qExpansion_eq_qExpansion_discriminant_mul f h0
  rw [← hG, hH, map_mul, isIntegralQExpansion_discriminant] at h
  exact mul_left_cancel₀ hne h

end LevelOne
