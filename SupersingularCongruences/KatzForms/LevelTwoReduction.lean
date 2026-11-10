/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.KatzForms.Reduction
public import SupersingularCongruences.LevelTwoForms.Identities
import all SupersingularCongruences.LevelTwoForms.WeightTwo

/-!
# Larson's level-two forms modulo `p` (manuscript, Lemma 3.1 mod `p`, Lemma 4.1 at `ℓ = 2`)

For an odd prime `p`, Larson's forms `δ ∈ M₂(Γ₀(2))`, `ε, μ ∈ M₄(Γ₀(2))`
(`LevelTwoForms.delta`, `LevelTwoForms.eps`, `LevelTwoForms.mu`) have `p`-integral rational
`q`-expansions

* `δ = 1/4 + ∑_{n ≥ 1} (6 σ₁(n) - 12 σ₁(n/2)) qⁿ`,
* `ε = 1/16 + ∑_{n ≥ 1} (16 σ₃(n/2) - σ₃(n)) qⁿ` (with `σ(n/2) = 0` for odd `n`),
* `μ = δ² - ε`.

For a structure `K : KatzForms p 2 L` of Katz forms on `Γ₀(2)` over `L` (characteristic `p`) we
define their reductions `δ̄ ∈ K.form 2`, `ε̄ ∈ K.form 4` and `μ̄ = δ̄² - ε̄ ∈ K.form 4`, and prove
Lemma 3.1 modulo `p` on test objects:

* `KatzForms.discriminantRule_eq_muBar_mul_epsBar_sq`: `Δ(E, ω) = 64 μ̄ ε̄²`;
* `KatzForms.normalizedVeluDiscriminant_eq_muBar_sq_mul_epsBar`:
  `2⁻¹² Δ(E / C, ω') = μ̄² ε̄` (with Lemma 4.1);

and deduce the moduli description of the coordinate `x = 64 R₂ = μ / ε` (Lemma 4.1, last
sentence, and Lemma 3.2(c)):

* `KatzForms.epsBar_ne_zero`, `KatzForms.muBar_ne_zero`: `ε̄` and `μ̄` do not vanish at any test
  object;
* `KatzForms.veluRatio_eq_muBar_div_epsBar`: `x(E, C) = 64 · R₂(E, C) = μ̄ / ε̄`;
* `KatzForms.veluRatio_add_one_eq`: `x + 1 = δ̄² / ε̄`.
-/

public section

open PowerSeries Gamma0 LevelTwoForms CongruenceSubgroup UpperHalfPlane
open scoped ArithmeticFunction.sigma

namespace LevelTwoForms

/-- The rational `q`-expansion coefficients of `E₂ = 1 - 24 ∑ σ₁(n) qⁿ`. -/
noncomputable def e2CoeffRat (m : ℕ) : ℚ :=
  if m = 0 then 1 else -24 * σ 1 m

/-- The rational `q`-expansion of `δ`. -/
noncomputable def deltaSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n ↦ (2 * (if 2 ∣ n then e2CoeffRat (n / 2) else 0) - e2CoeffRat n) / 4

/-- The rational `q`-expansion of `ε`. -/
noncomputable def epsSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n ↦
    if n = 0 then 1 / 16 else 16 * (if 2 ∣ n then (σ 3 (n / 2) : ℚ) else 0) - σ 3 n

/-- The rational `q`-expansion of `μ = δ² - ε`. -/
noncomputable def muSeries : PowerSeries ℚ :=
  deltaSeries ^ 2 - epsSeries

lemma coeff_deltaSeries (n : ℕ) :
    deltaSeries.coeff n = (2 * (if 2 ∣ n then e2CoeffRat (n / 2) else 0) - e2CoeffRat n) / 4 := by
  simp [deltaSeries]

lemma coeff_epsSeries (n : ℕ) :
    epsSeries.coeff n =
      if n = 0 then 1 / 16 else 16 * (if 2 ∣ n then (σ 3 (n / 2) : ℚ) else 0) - σ 3 n := by
  simp [epsSeries]

theorem map_deltaSeries : PowerSeries.map (Rat.castHom ℂ) deltaSeries = qExpansion 1 delta := by
  ext n
  rw [coeff_map, qExpansion_delta_coeff, coeff_deltaSeries]
  simp only [deltaCoeff, e2Coeff, e2CoeffRat, eq_ratCast]
  split_ifs <;> push_cast <;> ring

theorem map_epsSeries : PowerSeries.map (Rat.castHom ℂ) epsSeries = qExpansion 1 eps := by
  ext n
  rw [coeff_map, qExpansion_eps, coeff_smul, map_sub, coeff_smul,
    qExpansion_levelRaise_coeff, coeff_E₄, coeff_epsSeries, eq_ratCast]
  by_cases hn : n = 0
  · subst hn
    simp only [↓reduceIte, dvd_zero, Nat.zero_div, coeff_E₄, smul_eq_mul]
    norm_num
  · by_cases h2 : 2 ∣ n
    · have hn2 : n / 2 ≠ 0 := by
        obtain ⟨m, rfl⟩ := h2
        omega
      simp only [hn, h2, hn2, ↓reduceIte, smul_eq_mul, coeff_E₄]
      push_cast
      ring
    · simp only [hn, h2, ↓reduceIte, smul_eq_mul, coeff_E₄]
      push_cast
      ring

theorem map_muSeries : PowerSeries.map (Rat.castHom ℂ) muSeries = qExpansion 1 mu := by
  rw [muSeries, map_sub, map_pow, map_deltaSeries, map_epsSeries, qExpansion_mu]

variable {p : ℕ} [hp : Fact p.Prime]

lemma not_dvd_of_ne_two (hp2 : p ≠ 2) {k : ℕ} : ¬ p ∣ 2 ^ k := fun h ↦
  hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow h))

lemma not_dvd_den_e2CoeffRat (m : ℕ) : ¬ p ∣ (e2CoeffRat m).den := by
  rw [e2CoeffRat]
  split_ifs
  · exact_mod_cast Rat.not_dvd_den_intCast (p := p) 1
  · exact_mod_cast Rat.not_dvd_den_intCast (p := p) (-24 * (σ 1 m : ℤ))

theorem isPIntegral_deltaSeries (hp2 : p ≠ 2) : deltaSeries.IsPIntegral p := by
  rw [isPIntegral_iff]
  intro n
  rw [coeff_deltaSeries, div_eq_mul_inv]
  refine Rat.not_dvd_den_mul (Rat.not_dvd_den_sub (Rat.not_dvd_den_mul ?_ ?_)
    (not_dvd_den_e2CoeffRat n)) ?_
  · exact_mod_cast Rat.not_dvd_den_natCast (p := p) 2
  · split_ifs
    · exact not_dvd_den_e2CoeffRat _
    · exact_mod_cast Rat.not_dvd_den_natCast (p := p) 0
  · have := Rat.not_dvd_den_inv_natCast (p := p) (n := 2 ^ 2) (not_dvd_of_ne_two hp2)
    exact_mod_cast this

theorem isPIntegral_epsSeries (hp2 : p ≠ 2) : epsSeries.IsPIntegral p := by
  rw [isPIntegral_iff]
  intro n
  rw [coeff_epsSeries]
  split_ifs with h0 h2
  · rw [one_div]
    have := Rat.not_dvd_den_inv_natCast (p := p) (n := 2 ^ 4) (not_dvd_of_ne_two hp2)
    exact_mod_cast this
  · exact_mod_cast Rat.not_dvd_den_intCast (p := p) (16 * (σ 3 (n / 2) : ℤ) - σ 3 n)
  · exact_mod_cast Rat.not_dvd_den_intCast (p := p) (16 * 0 - (σ 3 n : ℤ))

theorem isPIntegral_muSeries (hp2 : p ≠ 2) : muSeries.IsPIntegral p :=
  ((isPIntegral_deltaSeries hp2).pow 2).sub (isPIntegral_epsSeries hp2)

/-! ### Lemma 3.1 on rational `q`-expansions -/

lemma map_ratCast_injective : Function.Injective (PowerSeries.map (Rat.castHom ℂ)) :=
  PowerSeries.map_injective _ (Rat.castHom ℂ).injective

local notation "hΓ" => one_mem_strictPeriods_Gamma0 2

lemma isIntegralQExpansion_discriminantForm :
    LevelOne.IsIntegralQExpansion LevelOne.integralDiscriminant discriminantForm := by
  rw [coe_discriminantForm]
  exact LevelOne.isIntegralQExpansion_discriminant

/-- `Δ = 64 μ ε²` on rational `q`-expansions. -/
theorem discriminant_qExp_eq :
    PowerSeries.C (64 : ℚ) * (muSeries * epsSeries * epsSeries) =
      PowerSeries.map (Int.castRingHom ℚ) LevelOne.integralDiscriminant := by
  apply map_ratCast_injective
  rw [LevelOne.map_map_intCast_eq_qExpansion_ofLevelOne 2 isIntegralQExpansion_discriminantForm,
    discriminant_eq, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos hΓ,
    ModularForm.qExpansion_mul one_pos hΓ, ModularForm.qExpansion_mul one_pos hΓ, map_mul,
    map_mul, map_mul, map_C, map_ofNat, map_muSeries, map_epsSeries, smul_eq_C_mul]

/-- `V₂(Δ) = μ² ε` on rational `q`-expansions. -/
theorem levelRaise_discriminant_qExp_eq :
    muSeries * muSeries * epsSeries =
      PowerSeries.map (Int.castRingHom ℚ) (expandSeries 2 LevelOne.integralDiscriminant) := by
  apply map_ratCast_injective
  rw [LevelOne.map_map_intCast_eq_qExpansion_levelRaise 2 isIntegralQExpansion_discriminantForm,
    levelRaise_discriminant_eq, ModularForm.qExpansion_mul one_pos hΓ,
    ModularForm.qExpansion_mul one_pos hΓ, map_mul, map_mul, map_muSeries, map_epsSeries]

end LevelTwoForms

namespace KatzForms

lemma two_ne_zero_of_charP {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [CharP L p]
    (hp2 : p ≠ 2) : (2 : L) ≠ 0 := by
  rw [show (2 : L) = ((2 : ℕ) : L) by norm_num, ne_eq, CharP.cast_eq_zero_iff L p]
  exact fun h ↦ hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h)

lemma discriminantRule_ne_zero {L : Type*} [Field L] [DecidableEq L] {ℓ : ℕ} (T : Test ℓ L) :
    discriminantRule T ≠ 0 := by
  rw [discriminantRule_apply]
  exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ T.diff.ne_zero)) T.curve.isUnit_Δ.ne_zero

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [DecidableEq L] (K : KatzForms p 2 L)
  (hp2 : p ≠ 2)

/-- The reduction `δ̄ ∈ M₂(Γ₀(2))_{𝔽_p}` of Larson's `δ`. -/
noncomputable def deltaBar : K.form 2 :=
  K.reduce delta deltaSeries (isPIntegral_deltaSeries hp2) map_deltaSeries

/-- The reduction `ε̄ ∈ M₄(Γ₀(2))_{𝔽_p}` of Larson's `ε`. -/
noncomputable def epsBar : K.form 4 :=
  K.reduce eps epsSeries (isPIntegral_epsSeries hp2) map_epsSeries

/-- `μ̄ = δ̄² - ε̄`. -/
noncomputable def muBar : Test 2 L → L :=
  (K.deltaBar hp2).1 ^ 2 - (K.epsBar hp2).1

lemma muBar_apply (T : Test 2 L) :
    K.muBar hp2 T = (K.deltaBar hp2).1 T ^ 2 - (K.epsBar hp2).1 T := by
  rw [muBar]; rfl

lemma muBar_mem : K.muBar hp2 ∈ K.form 4 := by
  rw [muBar]
  exact (K.form 4).sub_mem (K.mem_form_of_eq (by norm_num) (K.pow_mem (K.deltaBar hp2).2 2))
    (K.epsBar hp2).2

lemma qExp_deltaBar : K.qExp 2 (K.deltaBar hp2) = deltaSeries.reduceTo L := by
  rw [deltaBar, K.qExp_reduce]

lemma qExp_epsBar : K.qExp 4 (K.epsBar hp2) = epsSeries.reduceTo L := by
  rw [epsBar, K.qExp_reduce]

variable [CharP L p]

lemma qExp_muBar : K.qExp 4 ⟨K.muBar hp2, K.muBar_mem hp2⟩ = muSeries.reduceTo L := by
  have h2 := K.pow_mem (K.deltaBar hp2).2 2
  have h2' : (K.deltaBar hp2).1 ^ 2 ∈ K.form 4 := K.mem_form_of_eq (by norm_num) h2
  have hsub := K.qExp_sub h2' (K.epsBar hp2).2
  have hpow : K.qExp 4 ⟨_, h2'⟩ = K.qExp 2 (K.deltaBar hp2) ^ 2 :=
    (K.qExp_congr (by norm_num) rfl h2' h2).trans (K.qExp_pow (K.deltaBar hp2).2 2)
  rw [muSeries, reduceTo_sub ((isPIntegral_deltaSeries hp2).pow 2) (isPIntegral_epsSeries hp2),
    reduceTo_pow (isPIntegral_deltaSeries (p := p) hp2), ← K.qExp_deltaBar hp2,
    ← K.qExp_epsBar hp2, ← hpow]
  exact (K.qExp_congr rfl (K.muBar_apply hp2 |> funext |>.trans rfl) _ _).trans hsub

/-- `μ̄` is the reduction of `μ`. -/
lemma muBar_eq_reduce :
    K.muBar hp2 = (K.reduce mu muSeries (isPIntegral_muSeries hp2) map_muSeries).1 :=
  (K.reduce_eq_of_qExp_eq _ _ _ _ (K.muBar_mem hp2) (K.qExp_muBar hp2)).symm

/-- **Lemma 3.1 modulo `p`** (first identity): `Δ = 64 μ̄ ε̄²` as Katz forms of weight `12`. -/
theorem discriminantRule_eq_smul :
    discriminantRule = (64 : L) • (K.muBar hp2 * (K.epsBar hp2).1 * (K.epsBar hp2).1) := by
  have hm1 := K.mul_mem_of_eq (show (4 : ℤ) + 4 = 8 by norm_num) (K.muBar_mem hp2)
    (K.epsBar hp2).2
  have hm2 := K.mul_mem_of_eq (show (8 : ℤ) + 4 = 12 by norm_num) hm1 (K.epsBar hp2).2
  have h64 : ¬ p ∣ ((64 : ℚ)).den := by exact_mod_cast Rat.not_dvd_den_natCast (p := p) 64
  have hme := (isPIntegral_muSeries hp2).mul (isPIntegral_epsSeries hp2)
  refine K.eq_of_qExp_eq K.discriminant_mem ((K.form 12).smul_mem _ hm2) ?_
  rw [K.qExp_discriminant, K.qExp_smul _ hm2,
    K.qExp_mul_of_eq (show (8 : ℤ) + 4 = 12 by norm_num) hm1 (K.epsBar hp2).2,
    K.qExp_mul_of_eq (show (4 : ℤ) + 4 = 8 by norm_num) (K.muBar_mem hp2) (K.epsBar hp2).2,
    qExp_muBar, qExp_epsBar, ← reduceTo_map_intCast, ← discriminant_qExp_eq,
    reduceTo_mul (isPIntegral_C _ h64) (hme.mul (isPIntegral_epsSeries hp2)), reduceTo_C,
    reduceTo_mul hme (isPIntegral_epsSeries hp2),
    reduceTo_mul (isPIntegral_muSeries hp2) (isPIntegral_epsSeries hp2), smul_eq_C_mul]
  norm_num

/-- **Lemma 3.1 modulo `p`** (first identity), at a test object: `Δ(E, ω) = 64 μ̄ ε̄²`. -/
theorem discriminantRule_eq_muBar_mul_epsBar_sq (T : Test 2 L) :
    discriminantRule T = 64 * K.muBar hp2 T * (K.epsBar hp2).1 T ^ 2 := by
  rw [K.discriminantRule_eq_smul hp2]
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- **Lemma 3.1 modulo `p`** (second identity, with Lemma 4.1):
`Δ^{[2]} = 2⁻¹² Δ(E / C, ω') = μ̄² ε̄` as Katz forms of weight `12`. -/
theorem normalizedVeluDiscriminant_eq_mul :
    (fun T ↦ ((2 : L) ^ 12)⁻¹ * veluDiscriminantRule T) =
      K.muBar hp2 * K.muBar hp2 * (K.epsBar hp2).1 := by
  have hm1 := K.mul_mem_of_eq (show (4 : ℤ) + 4 = 8 by norm_num) (K.muBar_mem hp2)
    (K.muBar_mem hp2)
  have hm2 := K.mul_mem_of_eq (show (8 : ℤ) + 4 = 12 by norm_num) hm1 (K.epsBar hp2).2
  have h2 : ((2 : ℕ) : L) ≠ 0 := by exact_mod_cast two_ne_zero_of_charP (L := L) hp2
  have hmemL : (fun T ↦ ((2 : L) ^ 12)⁻¹ * veluDiscriminantRule T) ∈ K.form 12 :=
    (K.form 12).smul_mem _ K.veluDiscriminant_mem
  have hq := (K.qExp_congr rfl (by simp) hmemL K.normalizedVeluDiscriminant_mem).trans
    (K.qExp_normalizedVeluDiscriminant h2)
  refine K.eq_of_qExp_eq hmemL hm2 (hq.trans ?_)
  rw [K.qExp_mul_of_eq (show (8 : ℤ) + 4 = 12 by norm_num) hm1 (K.epsBar hp2).2,
    K.qExp_mul_of_eq (show (4 : ℤ) + 4 = 8 by norm_num) (K.muBar_mem hp2) (K.muBar_mem hp2),
    qExp_muBar, qExp_epsBar,
    ← reduceTo_mul (isPIntegral_muSeries hp2) (isPIntegral_muSeries hp2),
    ← reduceTo_mul ((isPIntegral_muSeries hp2).mul (isPIntegral_muSeries hp2))
      (isPIntegral_epsSeries hp2),
    levelRaise_discriminant_qExp_eq, reduceTo_map_intCast, map_expandSeries]

/-- **Lemma 3.1 modulo `p`** (second identity), at a test object:
`2⁻¹² Δ(E / C, ω') = μ̄² ε̄`. -/
theorem normalizedVeluDiscriminant_eq_muBar_sq_mul_epsBar (T : Test 2 L) :
    ((2 : L) ^ 12)⁻¹ * veluDiscriminantRule T = K.muBar hp2 T ^ 2 * (K.epsBar hp2).1 T := by
  have := congrFun (K.normalizedVeluDiscriminant_eq_mul hp2) T
  simp only [Pi.mul_apply] at this
  rw [this]
  ring

/-- `ε̄` does not vanish at any test object (`Δ ≠ 0`; manuscript, Lemma 3.2(c)). -/
theorem epsBar_ne_zero (T : Test 2 L) : (K.epsBar hp2).1 T ≠ 0 := by
  intro h
  apply discriminantRule_ne_zero T
  rw [K.discriminantRule_eq_muBar_mul_epsBar_sq hp2, h]
  ring

/-- `μ̄` does not vanish at any test object (`Δ ≠ 0`; manuscript, Lemma 3.2(c)). -/
theorem muBar_ne_zero (T : Test 2 L) : K.muBar hp2 T ≠ 0 := by
  intro h
  apply discriminantRule_ne_zero T
  rw [K.discriminantRule_eq_muBar_mul_epsBar_sq hp2, h]
  ring

/-- **Lemma 4.1**, last sentence: `x = 64 R₂ = μ̄ / ε̄`, i.e. at every pair `(E, C)` with `|C| = 2`
and every differential, `64 · 2⁻¹² Δ(E / C) / Δ(E) = μ̄ / ε̄`. -/
theorem veluRatio_eq_muBar_div_epsBar (T : Test 2 L) :
    64 * T.toPair.veluRatio = K.muBar hp2 T / (K.epsBar hp2).1 T := by
  have he := K.epsBar_ne_zero hp2 T
  have hm := K.muBar_ne_zero hp2 T
  have h2 := two_ne_zero_of_charP (L := L) hp2
  have h64 : (64 : L) ≠ 0 := by
    rw [show (64 : L) = 2 ^ 6 by norm_num]; exact pow_ne_zero _ h2
  rw [Pair.veluRatio_eq_div, Nat.cast_ofNat,
    K.normalizedVeluDiscriminant_eq_muBar_sq_mul_epsBar hp2,
    K.discriminantRule_eq_muBar_mul_epsBar_sq hp2]
  field_simp

/-- `x + 1 = δ̄² / ε̄` (manuscript, Lemma 3.2(c)). -/
theorem veluRatio_add_one_eq (T : Test 2 L) :
    64 * T.toPair.veluRatio + 1 = (K.deltaBar hp2).1 T ^ 2 / (K.epsBar hp2).1 T := by
  have he := K.epsBar_ne_zero hp2 T
  rw [K.veluRatio_eq_muBar_div_epsBar hp2, K.muBar_apply hp2]
  field_simp
  ring

end KatzForms
