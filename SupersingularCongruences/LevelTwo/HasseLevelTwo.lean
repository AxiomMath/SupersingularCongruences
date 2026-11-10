/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.LevelTwo.LegendreValues
public import SupersingularCongruences.LevelTwo.HasseFactorization
public import SupersingularCongruences.LevelTwo.Divisibility
public import SupersingularCongruences.LevelTwo.Remarks
public import SupersingularCongruences.LevelTwoForms.Structure
public import SupersingularCongruences.KatzForms.HasseInvariant
public import Mathlib.Algebra.Algebra.ZMod
public import SupersingularCongruences.External

/-!
# The Hasse invariant in Larson's level-two ring (eq. (3.1), Prop. 3.4, Cor. 4.6, Prop. 5.3)

Let `p ≥ 5`, `L` an algebraic closure of `𝔽_p` (`hL`), `K : KatzForms p 2 L` with
`K.LegendreRegular`, and `δ̄, ε̄` the reductions of Larson's generators.

## Main results

* `KatzForms.exists_hasseRule_eq_aeval` (**eq. (3.1)**): there is a weighted homogeneous
  `P_A ∈ 𝔽_p[δ, ε]` of weight `p - 1` (weights `2, 4`) with `A_p = P_A(δ̄, ε̄)` as Katz forms.
  Proof: Larson's structure theorem (the cited result `LevelTwoForms.LarsonLevelTwoStructure`, in
  the form `LevelTwoForms.exists_mvPolynomial_eq_of_pIntegral`) applied to `E_{p-1}` (whose
  `q`-expansion is `p`-integral by von Staudt–Clausen) gives `E_{p-1} = P(δ, ε)` with
  `p`-integral `P`; comparing `q`-expansions (`LevelTwoForms.exists_mvPolynomial_eisenstein`), the
  reduction `P_A` of `P` satisfies `qExp(P_A(δ̄, ε̄)) = Ē_{p-1}(q) = 1 = qExp(A_p)`, and the
  `q`-expansion principle gives `A_p = P_A(δ̄, ε̄)`.
* `KatzForms.hasse_polynomial_unique`: such a `P_A` is unique.
* `KatzForms.hasse_factorization` (**Proposition 3.4**): in `L[δ, ε]`,
  `P_A = c' δ^{α_p} ∏_{i=1}^s (μ - ξ_i ε)` with `c' ≠ 0`, distinct `ξ_i ∉ {0, -1}`, `s ≥ 1`, and
  `{x(P) : P supersingular} = {ξ_i} ∪ {-1 | α_p = 1}`.
* `Gamma0.Pair.xCoordinate_pow_eq_of_supersingular`, `KatzForms.xi_pow_eq_of_supersingular_eq`,
  `KatzForms.hasse_factorization_pow_eq` (**Corollary 4.6**): `x(P)^{t'} = 64^{t'}` at
  supersingular points, hence `ξ_i^{t'} = 64^{t'}` and `(-1)^{t'} = 64^{t'}` if `α_p = 1`.
* `KatzForms.aeval_larsonL2` (**Proposition 5.2**, identification): `L₂(Δᵗ)(δ̄, ε̄) = V₂(Δᵗ) - Δᵗ`
  for the polynomial `LevelTwo.larsonL2 L t = (μ² ε)ᵗ - (64 μ ε²)ᵗ`.
* `KatzForms.hasse_pow_dvd_larsonL2_iff`, `KatzForms.exists_hasse_pow_dvd_larsonL2_iff`
  (**Proposition 5.3**): for `t = r pⁿ (p² - 1) / 12`, `p ∤ r`: `P_A^j ∣ L₂(Δᵗ)` in `𝔽_p[δ, ε]` iff
  `j ≤ pⁿ`.
* `KatzForms.delta_pow_dvd_larsonL2_iff_of_mod_four` (**Remark 5.1**): for `p ≡ 3 (mod 4)`,
  `δ^j ∣ L₂(Δᵗ)` iff `j ≤ 2 pⁿ`.

## Proof route for Proposition 3.4

On the Legendre family `T_λ`, `δ̄ ↦ c (λ + 1)`, `ε̄ ↦ ζ λ` with `4 c² = ζ`
(`KatzForms.exists_legendre_values`) and `A_p(T_λ) = (-1)^{(p-1)/2} H_p(λ)` (Lemma 2.1(d)), so
`P_A(c (λ + 1), ζ λ) = (-1)^{(p-1)/2} H_p(λ)` as polynomials in `λ`
(`KatzForms.aeval_legendre_eq_hasse`); the algebraic core `LevelTwo.exists_hasse_factorization_core`
then performs the order comparison at `λ = 0, 1, -1` and at the roots of `H_p`. The supersingular
points are read off via the Legendre normal form and Lemma 2.1(a),(e). This replaces the
manuscript's comparison of orders of `A_p^{12} / Δ^{p-1}` on `X₀(2)` and `X(2)`.
-/

public section

open MvPolynomial UpperHalfPlane Gamma0 CongruenceSubgroup

universe u

namespace LevelTwo

/-! ### Polynomials in two variables as sums of monomials -/

lemma aeval_eq_sum_fin_two {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (f : Fin 2 → A) (P : MvPolynomial (Fin 2) R) :
    aeval f P = ∑ e ∈ P.support, algebraMap R A (P.coeff e) * (f 0 ^ e 0 * f 1 ^ e 1) := by
  rw [aeval_def, eval₂_eq']
  simp [Fin.prod_univ_two]

lemma weight_eq_of_mem_support {R : Type*} [CommSemiring R] {P : MvPolynomial (Fin 2) R} {n : ℕ}
    (hP : P.IsWeightedHomogeneous ![2, 4] n) {e : Fin 2 →₀ ℕ} (he : e ∈ P.support) :
    2 * e 0 + 4 * e 1 = n := by
  rw [← weight_two_four_apply]; exact hP (mem_support_iff.mp he)

lemma isWeightedHomogeneous_map {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    {P : MvPolynomial (Fin 2) R} {n : ℕ} (hP : P.IsWeightedHomogeneous ![2, 4] n) :
    (map f P).IsWeightedHomogeneous ![2, 4] n := by
  intro d hd
  rw [coeff_map] at hd
  exact hP fun h => hd (by rw [h, map_zero])

/-- A weight-graded predicate `Q k f S` ("`f` has weight `k` and expansion `S`") that is closed
under products, powers, scalars and finite sums is closed under weighted homogeneous polynomials
in two generators of weights `2, 4`. Both `q`-expansion APIs below (complex forms on `Γ₀(2)` and
Katz forms) are instances. -/
theorem aeval_of_closed {R A B : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra R B] (Q : ℤ → A → B → Prop)
    (hmul : ∀ {a b : ℤ} {f g : A} {S T : B}, Q a f S → Q b g T → Q (a + b) (f * g) (S * T))
    (hpow : ∀ {a : ℤ} {f : A} {S : B} (n : ℕ), Q a f S → Q (n * a) (f ^ n) (S ^ n))
    (hscal : ∀ {a : ℤ} {f : A} {S : B} (c : R), Q a f S →
      Q a (algebraMap R A c * f) (algebraMap R B c * S))
    (hsum : ∀ {a : ℤ} (s : Finset (Fin 2 →₀ ℕ)) {f : (Fin 2 →₀ ℕ) → A}
      {S : (Fin 2 →₀ ℕ) → B}, (∀ i ∈ s, Q a (f i) (S i)) → Q a (∑ i ∈ s, f i) (∑ i ∈ s, S i))
    {f : Fin 2 → A} {S : Fin 2 → B} (h0 : Q 2 (f 0) (S 0)) (h1 : Q 4 (f 1) (S 1))
    {P : MvPolynomial (Fin 2) R} {n : ℕ} (hP : P.IsWeightedHomogeneous ![2, 4] n) :
    Q n (aeval f P) (aeval S P) := by
  rw [aeval_eq_sum_fin_two, aeval_eq_sum_fin_two]
  refine hsum _ fun e he => hscal _ ?_
  have hw := weight_eq_of_mem_support hP he
  have hm := hmul (hpow (e 0) h0) (hpow (e 1) h1)
  have hn : ((e 0 : ℕ) : ℤ) * 2 + ((e 1 : ℕ) : ℤ) * 4 = (n : ℤ) := by
    rw [← hw]; push_cast; ring
  exact hn ▸ hm

end LevelTwo

/-! ### `q`-expansions of polynomials in `δ, ε` over `ℂ` -/

namespace LevelTwoForms

local notation "hΓ" => one_mem_strictPeriods_Gamma0 2

/-- `f` is a modular form of weight `k` on `Γ₀(2)` with `q`-expansion `S`. -/
def HasQExp (k : ℤ) (f : ℍ → ℂ) (S : PowerSeries ℂ) : Prop :=
  ∃ F : ModularForm (Gamma0 2) k, ⇑F = f ∧ qExpansion 1 ⇑F = S

lemma HasQExp.mul {a b : ℤ} {f g : ℍ → ℂ} {S T : PowerSeries ℂ} (hf : HasQExp a f S)
    (hg : HasQExp b g T) : HasQExp (a + b) (f * g) (S * T) := by
  obtain ⟨F, rfl, rfl⟩ := hf
  obtain ⟨G, rfl, rfl⟩ := hg
  exact ⟨F.mul G, ModularForm.coe_mul F G, ModularForm.qExpansion_mul one_pos hΓ F G⟩

lemma HasQExp.pow {a : ℤ} {f : ℍ → ℂ} {S : PowerSeries ℂ} (hf : HasQExp a f S) (n : ℕ) :
    HasQExp (n * a) (f ^ n) (S ^ n) := by
  obtain ⟨F, rfl, rfl⟩ := hf
  exact ⟨F.pow n, ModularForm.coe_pow F n, ModularForm.qExpansion_pow one_pos hΓ F n⟩

lemma HasQExp.smul {a : ℤ} {f : ℍ → ℂ} {S : PowerSeries ℂ} (hf : HasQExp a f S) (c : ℂ) :
    HasQExp a (c • f) (c • S) := by
  obtain ⟨F, rfl, rfl⟩ := hf
  exact ⟨c • F, rfl, ModularForm.qExpansion_smul one_pos hΓ c F⟩

lemma HasQExp.sum {a : ℤ} {ι : Type*} (s : Finset ι) {f : ι → ℍ → ℂ} {S : ι → PowerSeries ℂ}
    (h : ∀ i ∈ s, HasQExp a (f i) (S i)) : HasQExp a (∑ i ∈ s, f i) (∑ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simpa using qExpansion_zero 1⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    obtain ⟨F, hF, hFS⟩ := h i (Finset.mem_insert_self _ _)
    obtain ⟨G, hG, hGS⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    refine ⟨F + G, by rw [FunLike.coe_add, hF, hG], ?_⟩
    rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos hΓ F G, hFS, hGS]

lemma hasQExp_delta : HasQExp 2 ⇑delta (qExpansion 1 ⇑delta) := ⟨delta, rfl, rfl⟩

lemma hasQExp_eps : HasQExp 4 ⇑eps (qExpansion 1 ⇑eps) := ⟨eps, rfl, rfl⟩

/-- A weighted homogeneous polynomial of weight `n` in `δ, ε` is a modular form of weight `n`
whose `q`-expansion is the same polynomial in the `q`-expansions of `δ, ε`. -/
theorem hasQExp_aeval {P : MvPolynomial (Fin 2) ℂ} {n : ℕ}
    (hP : P.IsWeightedHomogeneous ![2, 4] n) :
    HasQExp n (aeval ![⇑delta, ⇑eps] P) (aeval ![qExpansion 1 ⇑delta, qExpansion 1 ⇑eps] P) :=
  LevelTwo.aeval_of_closed HasQExp (fun hf hg ↦ hf.mul hg) (fun n hf ↦ hf.pow n)
    (fun c hf ↦ by rw [← Algebra.smul_def, ← Algebra.smul_def]; exact hf.smul c)
    (@fun _ s _ _ h ↦ HasQExp.sum s h) (f := ![⇑delta, ⇑eps])
    (S := ![qExpansion 1 ⇑delta, qExpansion 1 ⇑eps]) hasQExp_delta hasQExp_eps hP

end LevelTwoForms

/-! ### `q`-expansions of polynomials in `δ̄, ε̄` (Katz forms) -/

namespace KatzForms

variable {p ℓ : ℕ} {L : Type*} [Field L] [DecidableEq L] (K : KatzForms p ℓ L)

/-- `f` is a Katz form of weight `k` with `q`-expansion `S`. -/
def HasQExp (k : ℤ) (f : Test ℓ L → L) (S : PowerSeries L) : Prop :=
  ∃ h : f ∈ K.form k, K.qExp k ⟨f, h⟩ = S

variable {K}

lemma HasQExp.mul {a b : ℤ} {f g : Test ℓ L → L} {S T : PowerSeries L} (hf : K.HasQExp a f S)
    (hg : K.HasQExp b g T) : K.HasQExp (a + b) (f * g) (S * T) := by
  obtain ⟨hf, rfl⟩ := hf
  obtain ⟨hg, rfl⟩ := hg
  exact ⟨K.mul_mem hf hg, K.qExp_mul ⟨f, hf⟩ ⟨g, hg⟩⟩

lemma HasQExp.pow {a : ℤ} {f : Test ℓ L → L} {S : PowerSeries L} (hf : K.HasQExp a f S)
    (n : ℕ) : K.HasQExp (n * a) (f ^ n) (S ^ n) := by
  obtain ⟨hf, rfl⟩ := hf
  exact ⟨K.pow_mem hf n, K.qExp_pow hf n⟩

lemma HasQExp.smul {a : ℤ} {f : Test ℓ L → L} {S : PowerSeries L} (hf : K.HasQExp a f S)
    (c : L) : K.HasQExp a (c • f) (c • S) := by
  obtain ⟨hf, rfl⟩ := hf
  exact ⟨(K.form a).smul_mem c hf, K.qExp_smul c hf⟩

lemma HasQExp.sum {a : ℤ} {ι : Type*} (s : Finset ι) {f : ι → Test ℓ L → L}
    {S : ι → PowerSeries L} (h : ∀ i ∈ s, K.HasQExp a (f i) (S i)) :
    K.HasQExp a (∑ i ∈ s, f i) (∑ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simp, ?_⟩
    simp only [Finset.sum_empty]
    exact map_zero (K.qExp a)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    obtain ⟨hF, hFS⟩ := h i (Finset.mem_insert_self _ _)
    obtain ⟨hG, hGS⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    exact ⟨(K.form a).add_mem hF hG, by rw [K.qExp_add hF hG, hFS, hGS]⟩

lemma hasQExp_mem {k : ℤ} {f : Test ℓ L → L} (hf : f ∈ K.form k) :
    K.HasQExp k f (K.qExp k ⟨f, hf⟩) := ⟨hf, rfl⟩

/-- A weighted homogeneous polynomial of weight `n` in two forms `f₀, f₁` of weights `2, 4` is a
form of weight `n`, whose `q`-expansion is the same polynomial in their `q`-expansions. -/
theorem hasQExp_aeval {f : Fin 2 → Test ℓ L → L} {S : Fin 2 → PowerSeries L}
    (h0 : K.HasQExp 2 (f 0) (S 0)) (h1 : K.HasQExp 4 (f 1) (S 1)) {P : MvPolynomial (Fin 2) L}
    {n : ℕ} (hP : P.IsWeightedHomogeneous ![2, 4] n) :
    K.HasQExp n (aeval f P) (aeval S P) :=
  LevelTwo.aeval_of_closed K.HasQExp (fun hf hg ↦ hf.mul hg) (fun n hf ↦ hf.pow n)
    (fun c hf ↦ by rw [← Algebra.smul_def, ← Algebra.smul_def]; exact hf.smul c)
    (@fun _ s _ _ h ↦ HasQExp.sum s h) h0 h1 hP

end KatzForms

/-! ### Reduction of `p`-integral polynomials -/

namespace LevelTwo

variable {p : ℕ} [Fact p.Prime]

/-- The reduction modulo `p` of a polynomial with rational coefficients (meaningful for
`p`-integral coefficients): `∑_e (a_e mod p) δ^{e₀} ε^{e₁}`. -/
noncomputable def reduceModP (p : ℕ) [Fact p.Prime] (P : MvPolynomial (Fin 2) ℚ) :
    MvPolynomial (Fin 2) (ZMod p) :=
  ∑ e ∈ P.support, monomial e ((P.coeff e : ℚ) : ZMod p)

lemma isWeightedHomogeneous_reduceModP {P : MvPolynomial (Fin 2) ℚ} {n : ℕ}
    (hP : P.IsWeightedHomogeneous ![2, 4] n) :
    (reduceModP p P).IsWeightedHomogeneous ![2, 4] n :=
  IsWeightedHomogeneous.sum _ _ _ fun _ he => isWeightedHomogeneous_monomial _ _ _ (hP
    (mem_support_iff.mp he))

lemma castHom_ratCast {L : Type*} [Field L] [CharP L p] (q : ℚ) :
    ZMod.castHom (dvd_refl p) L (q : ZMod p) = (q : L) := by
  rw [Rat.cast_def, Rat.cast_def, map_div₀, map_intCast, map_natCast]

lemma map_reduceModP {L : Type*} [Field L] [CharP L p] (P : MvPolynomial (Fin 2) ℚ) :
    map (ZMod.castHom (dvd_refl p) L) (reduceModP p P) =
      ∑ e ∈ P.support, monomial e ((P.coeff e : ℚ) : L) := by
  simp only [reduceModP, map_sum, map_monomial, castHom_ratCast]

lemma aeval_monomial_fin_two {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (f : Fin 2 → A) (e : Fin 2 →₀ ℕ) (a : R) :
    aeval f (monomial e a) = algebraMap R A a * (f 0 ^ e 0 * f 1 ^ e 1) := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]

end LevelTwo

namespace PowerSeries

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [CharP L p]

lemma IsPIntegral.sum {ι : Type*} (s : Finset ι) {G : ι → PowerSeries ℚ}
    (h : ∀ i ∈ s, (G i).IsPIntegral p) : (∑ i ∈ s, G i).IsPIntegral p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isPIntegral_C (p := p) 0 (by simpa using (Fact.out : p.Prime).ne_one))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma reduceTo_sum {ι : Type*} (s : Finset ι) {G : ι → PowerSeries ℚ}
    (h : ∀ i ∈ s, (G i).IsPIntegral p) :
    (∑ i ∈ s, G i).reduceTo L = ∑ i ∈ s, (G i).reduceTo L := by
  classical
  induction s using Finset.induction_on with
  | empty => ext n; simp
  | insert i s hi ih =>
    have h' : ∀ j ∈ s, (G j).IsPIntegral p := fun j hj => h j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      reduceTo_add (h i (Finset.mem_insert_self _ _)) (IsPIntegral.sum s h'), ih h']

end PowerSeries

/-! ### Eq. (3.1): the Hasse invariant as a polynomial in `δ̄, ε̄` -/

namespace LevelTwoForms

open LevelOne

/-- **Eq. (3.1) over `ℚ`**: `E_{p-1} = P(δ, ε)` on `Γ₀(2)` for a weighted homogeneous `P` of weight
`p - 1` with `p`-integral coefficients (Larson's structure theorem); on `q`-expansions,
`P(δ(q), ε(q)) = E_{p-1}(q)`. -/
theorem exists_mvPolynomial_eisenstein
    (hLarsonLevelTwoStructure : LarsonLevelTwoStructure) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∃ P : MvPolynomial (Fin 2) ℚ, P.IsWeightedHomogeneous ![2, 4] (p - 1) ∧
      (∀ e, ¬ p ∣ (P.coeff e).den) ∧
      aeval ![deltaSeries, epsSeries] P = eisensteinSeriesQExp p := by
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hE : 3 ≤ p - 1 := by omega
  set E := ofLevelOne 2 (ModularForm.E hE) with hEdef
  have hqE : qExpansion 1 ⇑E = PowerSeries.map (Rat.castHom ℂ) (eisensteinSeriesQExp p) := by
    rw [hEdef, coe_ofLevelOne, map_eisensteinSeriesQExp hp2 hE]
  set d : ℤ := (((bernoulli (p - 1))⁻¹).den : ℤ) with hd
  have hdp : ¬ (p : ℤ) ∣ d := fun h =>
    Bernoulli.not_dvd_den_inv_bernoulli_sub_one hp2 (Int.natCast_dvd_natCast.mp h)
  have hf : ∀ n, ∃ (a : ℤ) (m : ℕ), (d : ℂ) * (qExpansion 1 E).coeff n = (a : ℂ) / 2 ^ m := by
    intro n
    rw [show qExpansion 1 E = qExpansion 1 ⇑E from rfl, hqE, PowerSeries.coeff_map,
      coeff_eisensteinSeriesQExp]
    split_ifs with hn
    · exact ⟨d, 0, by simp⟩
    · set a : ℤ := ((bernoulli (p - 1))⁻¹).num * (-(2 * ((p - 1 : ℕ) : ℤ)) *
        (ArithmeticFunction.sigma (p - 1 - 1) n : ℤ)) with ha
      refine ⟨a, 0, ?_⟩
      have key : (d : ℚ) * (bernoulli (p - 1))⁻¹ = ((bernoulli (p - 1))⁻¹).num := by
        rw [hd]; push_cast; exact Rat.den_mul_eq_num _
      have hq : (d : ℚ) * ((bernoulli (p - 1))⁻¹ * (-(2 * ((p - 1 : ℕ) : ℚ)) *
          (ArithmeticFunction.sigma (p - 1 - 1) n))) = (a : ℚ) := by
        rw [← mul_assoc, key, ha]; push_cast; ring
      have := congrArg (fun q : ℚ => (q : ℂ)) hq
      simp only [Rat.cast_mul, Rat.cast_intCast] at this
      simp only [eq_ratCast, pow_zero, div_one]
      rw [← this]
      push_cast
      ring
  obtain ⟨P, hPw, hPint, hPE⟩ := exists_mvPolynomial_eq_of_pIntegral hLarsonLevelTwoStructure hp hp2
    E hdp hf
  refine ⟨P, hPw, hPint, ?_⟩
  apply map_ratCast_injective
  rw [← hqE]
  have hfun : ⇑E = aeval ![⇑delta, ⇑eps] (MvPolynomial.map (algebraMap ℚ ℂ) P) := by
    funext τ
    rw [hPE τ, aeval_map_algebraMap]
    change _ = Pi.evalAlgHom ℚ (fun _ : ℍ => ℂ) τ (aeval ![⇑delta, ⇑eps] P)
    rw [← AlgHom.comp_apply, comp_aeval]
    rw [show (fun i => (Pi.evalAlgHom ℚ (fun _ : ℍ => ℂ) τ) (![⇑delta, ⇑eps] i)) =
      ![delta τ, eps τ] from by funext i; fin_cases i <;> rfl]
  obtain ⟨F, hF, hFS⟩ := hasQExp_aeval (LevelTwo.isWeightedHomogeneous_map (algebraMap ℚ ℂ) hPw)
  have h1 : (PowerSeries.map (Rat.castHom ℂ)).comp (algebraMap ℚ (PowerSeries ℚ)) =
      algebraMap ℚ (PowerSeries ℂ) := RingHom.ext_rat _ _
  have h2 : ⇑(PowerSeries.map (Rat.castHom ℂ)) ∘ ![deltaSeries, epsSeries] =
      ![qExpansion 1 ⇑delta, qExpansion 1 ⇑eps] := by
    funext i
    fin_cases i
    · simp [map_deltaSeries]
    · simp [map_epsSeries]
  rw [hfun, ← hF, hFS, aeval_map_algebraMap, aeval_def, aeval_def, eval₂_comp_left, h1, h2]

end LevelTwoForms

namespace KatzForms

open LevelTwoForms LevelTwo LevelOne PowerSeries

variable {p : ℕ} [Fact p.Prime] {L : Type u} [Field L] [DecidableEq L] [CharP L p]
  (K : KatzForms p 2 L) (hp2 : p ≠ 2)

omit [CharP L p] in
lemma hasQExp_deltaBar : K.HasQExp 2 (K.deltaBar hp2).1 (deltaSeries.reduceTo L) :=
  ⟨(K.deltaBar hp2).2, K.qExp_deltaBar hp2⟩

omit [CharP L p] in
lemma hasQExp_epsBar : K.HasQExp 4 (K.epsBar hp2).1 (epsSeries.reduceTo L) :=
  ⟨(K.epsBar hp2).2, K.qExp_epsBar hp2⟩

/-- **Eq. (3.1)** (the Hasse invariant in Larson's ring): for `p ≥ 5` there is a weighted
homogeneous `P_A ∈ 𝔽_p[δ, ε]` of weight `p - 1` (weights `2, 4`) with `A_p = P_A(δ̄, ε̄)` as Katz
forms on `Γ₀(2)` over `L`. (`P_A` is the reduction of Larson's polynomial expressing `E_{p-1}`;
`A_p` is the reduction of `E_{p-1}`, Lemma 2.1(c).) -/
theorem exists_hasseRule_eq_aeval
    (hLarsonLevelTwoStructure : LarsonLevelTwoStructure) (hp5 : 5 ≤ p) :
    ∃ PA : MvPolynomial (Fin 2) (ZMod p), PA.IsWeightedHomogeneous ![2, 4] (p - 1) ∧
      aeval ![(K.deltaBar hp2).1, (K.epsBar hp2).1] (map (ZMod.castHom (dvd_refl p) L) PA) =
        hasseRule p := by
  obtain ⟨P, hPw, hPint, hPeis⟩ := exists_mvPolynomial_eisenstein hLarsonLevelTwoStructure
    (Fact.out : p.Prime) hp5
  refine ⟨reduceModP p P, isWeightedHomogeneous_reduceModP hPw, ?_⟩
  rw [map_reduceModP]
  have hPLw : (∑ e ∈ P.support, monomial e ((P.coeff e : ℚ) : L)).IsWeightedHomogeneous
      ![2, 4] (p - 1) :=
    IsWeightedHomogeneous.sum _ _ _ fun _ he => isWeightedHomogeneous_monomial _ _ _ (hPw
      (mem_support_iff.mp he))
  have h0 : K.HasQExp 2 (![(K.deltaBar hp2).1, (K.epsBar hp2).1] 0)
      (![deltaSeries.reduceTo L, epsSeries.reduceTo L] 0) := K.hasQExp_deltaBar hp2
  have h1 : K.HasQExp 4 (![(K.deltaBar hp2).1, (K.epsBar hp2).1] 1)
      (![deltaSeries.reduceTo L, epsSeries.reduceTo L] 1) := K.hasQExp_epsBar hp2
  obtain ⟨hmem, hq⟩ := K.hasQExp_aeval h0 h1 hPLw
  have hk : (p : ℤ) - 1 = ((p - 1 : ℕ) : ℤ) := by
    have := (Fact.out : p.Prime).one_le
    push_cast [this]; ring
  refine K.eq_of_qExp_eq hmem (K.mem_form_of_eq hk K.hasse_mem) ?_
  rw [hq, ← K.qExp_congr hk rfl K.hasse_mem _, K.qExp_hasse,
    ← reduceTo_eisensteinSeriesQExp hp2 L, ← hPeis,
    aeval_eq_sum_fin_two ![deltaSeries, epsSeries] P,
    reduceTo_sum _ fun e _ => ?_, map_sum]
  · refine Finset.sum_congr rfl fun e _ => ?_
    have hc : ¬ p ∣ (P.coeff e).den := hPint e
    rw [aeval_monomial_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [show algebraMap ℚ (PowerSeries ℚ) (P.coeff e) = PowerSeries.C (P.coeff e) from rfl,
      reduceTo_mul (isPIntegral_C _ hc)
        (((isPIntegral_deltaSeries hp2).pow _).mul ((isPIntegral_epsSeries hp2).pow _)),
      reduceTo_mul ((isPIntegral_deltaSeries hp2).pow _) ((isPIntegral_epsSeries hp2).pow _),
      reduceTo_C, reduceTo_pow (isPIntegral_deltaSeries hp2),
      reduceTo_pow (isPIntegral_epsSeries hp2)]
    rfl
  · exact (isPIntegral_C _ (hPint e)).mul
      (((isPIntegral_deltaSeries hp2).pow _).mul ((isPIntegral_epsSeries hp2).pow _))

end KatzForms

/-! ### Vanishing and uniqueness -/

namespace LevelTwo

open Polynomial

variable {L : Type*} [Field L]

/-- A weighted homogeneous `P ∈ L[δ, ε]` of weight `2 (2m + α)` (`α ≤ 1`) vanishing at points
`(a, b)`, `a, b ≠ 0`, with infinitely many values of `a² / b` is zero. -/
theorem eq_zero_of_forall_eval_eq_zero [IsAlgClosed L] {P : MvPolynomial (Fin 2) L} {m α : ℕ}
    (hα : α ≤ 1) (hP : P.IsWeightedHomogeneous ![2, 4] (2 * (2 * m + α))) {S : Set L}
    (hS : S.Infinite)
    (h : ∀ y ∈ S, ∃ a b : L, a ≠ 0 ∧ b ≠ 0 ∧ a ^ 2 / b = y ∧ MvPolynomial.eval ![a, b] P = 0) :
    P = 0 := by
  have hG : dehom P m = 0 := Polynomial.eq_zero_of_infinite_isRoot _ (hS.mono fun y hy => by
    obtain ⟨a, b, ha, hb, rfl, h0⟩ := h y hy
    rw [eval_eq_dehom hα hP hb] at h0
    exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb)))
  rw [eq_C_mul_prod_of_isWeightedHomogeneous hα hP, hG]
  simp

/-- `p - 1 = 2 (2 s + α_p)` for odd `p`. -/
lemma sub_one_eq_two_mul (p : ℕ) (hp : Odd p) :
    p - 1 = 2 * (2 * hasseS p + hasseAlpha p) := by
  rw [← half_eq_two_mul_hasseS_add p hp]
  obtain ⟨k, rfl⟩ := hp
  omega

/-- Evaluating a polynomial in two polynomials at `λ`. -/
lemma eval_aeval_polynomial (g : Fin 2 → L[X]) (P : MvPolynomial (Fin 2) L) (x : L) :
    (aeval g P).eval x = MvPolynomial.eval (fun i => (g i).eval x) P := by
  rw [← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply, comp_aeval,
    ← MvPolynomial.coe_aeval_eq_eval]
  rfl

/-- Over `L` infinite with `c, ζ ≠ 0` and `4 c² = ζ`: a weighted homogeneous `P` of weight
`2 (2m + α)` with `P(c (λ + 1), ζ λ) = 0` is zero. -/
theorem eq_zero_of_aeval_legendre_eq_zero [IsAlgClosed L] (h2 : (2 : L) ≠ 0)
    {P : MvPolynomial (Fin 2) L} {m α : ℕ} (hα : α ≤ 1)
    (hP : P.IsWeightedHomogeneous ![2, 4] (2 * (2 * m + α))) {c ζ : L} (hc : c ≠ 0)
    (hcζ : 4 * c ^ 2 = ζ)
    (h : MvPolynomial.aeval ![Polynomial.C c * (Polynomial.X + 1), Polynomial.C ζ * Polynomial.X] P
      = 0) : P = 0 := by
  have h4 : (4 : L) ≠ 0 := by rw [show (4 : L) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  refine eq_zero_of_forall_eval_eq_zero hα hP (S := {y | y ≠ 0})
    (Set.infinite_of_finite_compl (by simp)) fun y hy => ?_
  -- a root `λ` of `λ² + (2 - 4y) λ + 1`, so that `(λ + 1)² = 4 y λ`
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self ((2 - 4 * y) ^ 2 - 4)
  set lam := (s - (2 - 4 * y)) * 2⁻¹ with hlam
  have hl2 : 2 * lam = s - (2 - 4 * y) := by rw [hlam]; field_simp
  have hroot : lam ^ 2 + (2 - 4 * y) * lam + 1 = 0 := by
    have e : 4 * (lam ^ 2 + (2 - 4 * y) * lam + 1) = 0 := by
      linear_combination (2 * lam + s + (2 - 4 * y)) * hl2 - hs
    exact (mul_eq_zero.mp e).resolve_left h4
  have h0 : lam ≠ 0 := fun h => by rw [h] at hroot; norm_num at hroot
  have h1 : lam + 1 ≠ 0 := fun h => by
    have : lam = -1 := by linear_combination h
    rw [this] at hroot
    have h4y : 4 * y = 0 := by linear_combination hroot
    exact hy ((mul_eq_zero.mp h4y).resolve_left h4)
  have hζ0 : ζ ≠ 0 := by rw [← hcζ]; exact mul_ne_zero h4 (pow_ne_zero _ hc)
  refine ⟨c * (lam + 1), ζ * lam, mul_ne_zero hc h1, mul_ne_zero hζ0 h0, ?_, ?_⟩
  · rw [div_eq_iff (mul_ne_zero hζ0 h0), ← hcζ]
    linear_combination (c ^ 2) * hroot
  · have := congrArg (Polynomial.eval lam) h
    rw [eval_aeval_polynomial, Polynomial.eval_zero] at this
    rw [← this]
    refine congrArg (fun f => MvPolynomial.eval f P) ?_
    funext i
    fin_cases i <;> simp

end LevelTwo

namespace Gamma0.Pair

variable {L : Type u} [Field L] [IsAlgClosed L] [DecidableEq L] {p : ℕ} [CharP L p]

/-- **Corollary 4.6**: at a supersingular point `P` of `X₀(2)`, `x(P)^m = 64^m`,
`m = (p² - 1) / 12`, hence `x(P)^{r m} = 64^{r m}` for every `r` (from Theorem 1.2,
`R₂(P)^m = 1`, and `x = 64 R₂`). -/
theorem xCoordinate_pow_eq_of_supersingular
    (hGonzalezDivisionPolynomial : WeierstrassCurve.GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : WeierstrassCurve.GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : WeierstrassCurve.SupersingularJInvariant.{u})
    (hVeluIsogeny : WeierstrassCurve.VeluIsogeny.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (P : Pair 2 L)
    (hss : P.curve.IsSupersingularOver p) (r : ℕ) :
    P.xCoordinate ^ (r * ((p ^ 2 - 1) / 12)) = 64 ^ (r * ((p ^ 2 - 1) / 12)) := by
  have h := veluRatio_pow_eq_one_of_cited hGonzalezDivisionPolynomial hGonzalezMultiplicationByP
    hSupersingularJInvariant hVeluIsogeny hp hp5 hL Nat.prime_two (by omega) P hss
  rw [xCoordinate_eq_mul_veluRatio, mul_pow, mul_comm r, pow_mul P.veluRatio, h, one_pow, mul_one]

end Gamma0.Pair

namespace KatzForms

open LevelTwo Polynomial

variable {p : ℕ} [Fact p.Prime] {L : Type u} [Field L] [DecidableEq L] [CharP L p]
  (K : KatzForms p 2 L) (hp2 : p ≠ 2)

omit [Fact p.Prime] [CharP L p] in
lemma aeval_apply_test {R : Type*} [CommSemiring R] [Algebra R L] (f : Fin 2 → Test 2 L → L)
    (P : MvPolynomial (Fin 2) R) (T : Test 2 L) :
    MvPolynomial.aeval f P T = MvPolynomial.aeval ![f 0 T, f 1 T] P := by
  change Pi.evalAlgHom R (fun _ : Test 2 L => L) T (MvPolynomial.aeval f P) = _
  rw [← AlgHom.comp_apply, comp_aeval]
  refine congrArg (fun f => MvPolynomial.aeval f P) ?_
  funext i
  fin_cases i <;> rfl

omit [Fact p.Prime] [DecidableEq L] in
lemma two_three_ne_zero (hp5 : 5 ≤ p) : (2 : L) ≠ 0 ∧ (3 : L) ≠ 0 := by
  have hsmall : ∀ n : ℕ, 0 < n → n < p → (n : L) ≠ 0 := fun n hn hnp h =>
    absurd (Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff L p n).mp h)) (by omega)
  exact ⟨by exact_mod_cast hsmall 2 (by norm_num) (by omega),
    by exact_mod_cast hsmall 3 (by norm_num) (by omega)⟩

/-- **Uniqueness in eq. (3.1)**: the weighted homogeneous `P_A ∈ 𝔽_p[δ, ε]` of weight `p - 1`
with `A_p = P_A(δ̄, ε̄)` is unique (`δ̄, ε̄` are algebraically independent in this weight: the
values `x + 1 = δ̄² / ε̄` take infinitely many values). -/
theorem hasse_polynomial_unique [IsAlgClosed L] (hp5 : 5 ≤ p)
    {P Q : MvPolynomial (Fin 2) (ZMod p)} (hP : P.IsWeightedHomogeneous ![2, 4] (p - 1))
    (hQ : Q.IsWeightedHomogeneous ![2, 4] (p - 1))
    (hPA : MvPolynomial.aeval ![(K.deltaBar hp2).1, (K.epsBar hp2).1]
      (MvPolynomial.map (ZMod.castHom (dvd_refl p) L) P) = hasseRule p)
    (hQA : MvPolynomial.aeval ![(K.deltaBar hp2).1, (K.epsBar hp2).1]
      (MvPolynomial.map (ZMod.castHom (dvd_refl p) L) Q) = hasseRule p) : P = Q := by
  obtain ⟨h2, h3⟩ := two_three_ne_zero (L := L) hp5
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  apply MvPolynomial.map_injective _ (ZMod.castHom (dvd_refl p) L).injective
  rw [← sub_eq_zero]
  have hw := sub_one_eq_two_mul p hodd
  have hR := (isWeightedHomogeneous_map (ZMod.castHom (dvd_refl p) L) hP).sub
    (isWeightedHomogeneous_map (ZMod.castHom (dvd_refl p) L) hQ)
  rw [hw] at hR
  refine eq_zero_of_forall_eval_eq_zero (hasseAlpha_le_one p) hR infinite_setOf_ne_zero_ne_one
    fun y ⟨hy0, hy1⟩ => ?_
  obtain ⟨lam, h0, h1, hx⟩ := Pair.exists_xCoordinate_eq h2 h3 (sub_ne_zero.mpr hy1)
  set T : Test 2 L := ⟨legendrePair h2 h3 h0 h1, 1⟩
  have hb := K.epsBar_ne_zero hp2 T
  have hab : (K.deltaBar hp2).1 T ^ 2 / (K.epsBar hp2).1 T = y := by
    rw [← K.veluRatio_add_one_eq hp2 T, ← Pair.xCoordinate_eq_mul_veluRatio]
    change (legendrePair h2 h3 h0 h1).xCoordinate + 1 = y
    rw [hx]; ring
  refine ⟨(K.deltaBar hp2).1 T, (K.epsBar hp2).1 T, fun ha => ?_, hb, hab, ?_⟩
  · rw [ha] at hab; simp at hab; exact hy0 hab.symm
  · have e1 := congrFun hPA T
    have e2 := congrFun hQA T
    rw [aeval_apply_test] at e1 e2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at e1 e2
    rw [← MvPolynomial.coe_aeval_eq_eval, map_sub]
    change MvPolynomial.aeval _ _ - MvPolynomial.aeval _ _ = _
    rw [e1, e2, sub_self]

omit [DecidableEq L] in
/-- Evaluation commutes with the reduction map `𝔽_p → L`. -/
lemma castHom_eval (P : MvPolynomial (Fin 2) (ZMod p)) (a b : ZMod p) :
    ZMod.castHom (dvd_refl p) L (MvPolynomial.eval ![a, b] P) =
      MvPolynomial.eval ![ZMod.castHom (dvd_refl p) L a, ZMod.castHom (dvd_refl p) L b]
        (MvPolynomial.map (ZMod.castHom (dvd_refl p) L) P) := by
  rw [MvPolynomial.eval_map]
  change ZMod.castHom (dvd_refl p) L (eval₂ (RingHom.id _) ![a, b] P) = _
  rw [eval₂_comp_left, RingHom.comp_id]
  congr 1
  funext i
  fin_cases i <;> rfl

omit [Fact p.Prime] in
lemma aeval_test_eq_eval {f : Fin 2 → Test 2 L → L} (P : MvPolynomial (Fin 2) L) (T : Test 2 L) :
    MvPolynomial.aeval f P T = MvPolynomial.eval ![f 0 T, f 1 T] P := by
  rw [aeval_apply_test]; rfl

omit [Fact p.Prime] [CharP L p] in
lemma test_scale_curve (T : Test 2 L) (u : Lˣ) : (T.scale u).curve = (T.toPair.scale u).curve := by
  rw [← Test.scale_toPair]

/-- On the Legendre family (with the values `δ̄ ↦ c (λ + 1)`, `ε̄ ↦ ζ λ`), a polynomial `P_A`
with `A_p = P_A(δ̄, ε̄)` becomes `(-1)^{(p-1)/2} H_p(λ)` (Lemma 2.1(d)). -/
theorem aeval_legendre_eq_hasse [IsAlgClosed L] (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) {ζ c : L}
    (hv : ∀ (lam : L) (h0 : lam ≠ 0) (h1 : lam ≠ 1),
      (K.epsBar hp2).1 ⟨legendrePair h2 h3 h0 h1, 1⟩ = ζ * lam ∧
        (K.deltaBar hp2).1 ⟨legendrePair h2 h3 h0 h1, 1⟩ = c * (lam + 1))
    {PA : MvPolynomial (Fin 2) (ZMod p)}
    (hPA : MvPolynomial.aeval ![(K.deltaBar hp2).1, (K.epsBar hp2).1]
      (MvPolynomial.map (ZMod.castHom (dvd_refl p) L) PA) = hasseRule p) :
    MvPolynomial.aeval ![Polynomial.C c * (Polynomial.X + 1), Polynomial.C ζ * Polynomial.X]
      (MvPolynomial.map (ZMod.castHom (dvd_refl p) L) PA) =
      Polynomial.C ((-1) ^ ((p - 1) / 2)) * Polynomial.deuringPolynomial L p := by
  have hp : p.Prime := Fact.out
  set κ : L := (-1) ^ ((p - 1) / 2) with hκ
  refine Polynomial.eq_of_infinite_eval_eq _ _
    (infinite_setOf_ne_zero_ne_one.mono fun lam hlam => ?_)
  obtain ⟨h0, h1⟩ := hlam
  have e1 := congrFun hPA ⟨legendrePair h2 h3 h0 h1, 1⟩
  rw [aeval_test_eq_eval] at e1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at e1
  rw [(hv lam h0 h1).1, (hv lam h0 h1).2] at e1
  simp only [Set.mem_ofPred_eq]
  rw [eval_aeval_polynomial, Polynomial.eval_mul, Polynomial.eval_C]
  rw [show (fun i => Polynomial.eval lam
      (![Polynomial.C c * (Polynomial.X + 1), Polynomial.C ζ * Polynomial.X] i)) =
      ![c * (lam + 1), ζ * lam] from by funext i; fin_cases i <;> simp]
  rw [e1, hasseRule_apply]
  change (((1 : Lˣ) : L) ^ (p - 1))⁻¹ * (legendrePair h2 h3 h0 h1).curve.hasseCoeff p = _
  rw [legendrePair_curve, legendreCurve_hasseCoeff hp hp2 h3, hκ]
  simp

/-- **Proposition 3.4** (factorization of `A_p` at level `2`). Let `p ≥ 5`, `L` an algebraic
closure of `𝔽_p` and `P_A ∈ 𝔽_p[δ, ε]` weighted homogeneous of weight `p - 1` with
`A_p = P_A(δ̄, ε̄)` (eq. (3.1), `KatzForms.exists_hasseRule_eq_aeval`). Then in `L[δ, ε]`,
`P_A = c' δ^{α_p} ∏_{i=1}^s (μ - ξ_i ε)` with `c' ≠ 0` the image of `P_A(1, 0) ∈ 𝔽_p^×`, distinct
`ξ_i ∉ {0, -1}`, `s ≥ 1`; and the `x`-coordinates of the supersingular points of `X₀(2)` are
exactly the `ξ_i`, together with `-1` when `α_p = 1`. -/
theorem hasse_factorization (hDeuringHasseCriterion : WeierstrassCurve.DeuringHasseCriterion.{u})
    (hDeuringPolynomialSeparable : Polynomial.DeuringPolynomialSeparable.{u})
    [IsAlgClosed L] (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (hK : K.LegendreRegular)
    {PA : MvPolynomial (Fin 2) (ZMod p)} (hw : PA.IsWeightedHomogeneous ![2, 4] (p - 1))
    (hPA : MvPolynomial.aeval ![(K.deltaBar hp2).1, (K.epsBar hp2).1]
      (MvPolynomial.map (ZMod.castHom (dvd_refl p) L) PA) = hasseRule p) :
    ∃ (c' : L) (ξ : Fin (hasseS p) → L), c' ≠ 0 ∧
      c' = ZMod.castHom (dvd_refl p) L (MvPolynomial.eval ![1, 0] PA) ∧ Function.Injective ξ ∧
      (∀ i, ξ i ≠ 0 ∧ ξ i ≠ -1) ∧
      MvPolynomial.map (ZMod.castHom (dvd_refl p) L) PA =
        MvPolynomial.C c' * delta L ^ hasseAlpha p *
          ∏ i, (mu L - MvPolynomial.C (ξ i) * eps L) ∧ 1 ≤ hasseS p ∧
      {x | ∃ P : Pair 2 L, P.curve.IsSupersingularOver p ∧ P.xCoordinate = x} =
        Set.range ξ ∪ {x | hasseAlpha p = 1 ∧ x = -1} := by
  have hp : p.Prime := Fact.out
  obtain ⟨h2, h3⟩ := two_three_ne_zero (L := L) hp5
  obtain ⟨ζ, c, hcζ, -, hv⟩ := K.exists_legendre_values hp2 h2 h3 hK
  set κ : L := (-1) ^ ((p - 1) / 2) with hκ
  have hκ0 : κ ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hPH := K.aeval_legendre_eq_hasse hp2 h2 h3 hv hPA
  rw [← hκ] at hPH
  obtain ⟨c', ξ, hc', hξinj, hξ, hfac, hroots, hs⟩ :=
    exists_hasse_factorization_core hDeuringPolynomialSeparable hp hp5
    (isWeightedHomogeneous_map (ZMod.castHom (dvd_refl p) L) hw) hκ0 hcζ hPH
  have hc'p : c' = ZMod.castHom (dvd_refl p) L (MvPolynomial.eval ![1, 0] PA) := by
    rw [castHom_eval, map_one, map_zero, hfac]
    simp
  refine ⟨c', ξ, hc', hc'p, hξinj, hξ, hfac, hs, ?_⟩
  ext ρ
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  rw [← hroots ρ]
  constructor
  · rintro ⟨P, hss, rfl⟩
    obtain ⟨lam, h0, h1, u, hu⟩ := Pair.exists_scale_eq_legendrePair h2 h3 P
    have hT : hasseRule p (⟨P, 1⟩ : Test 2 L) = 0 :=
      (hasseRule_eq_zero_iff hDeuringHasseCriterion hp hp2 hL _).mpr hss
    rw [← K.apply_scale K.hasse_mem _ u, hasseRule_eq_zero_iff hDeuringHasseCriterion hp hp2 hL,
      test_scale_curve] at hT
    change ((P.scale u).curve).IsSupersingularOver p at hT
    rw [hu, legendrePair_curve] at hT
    refine ⟨lam, (deuringPolynomial_isRoot_iff hDeuringHasseCriterion hp hp5 hL lam).mpr
      ⟨h0, h1, hT⟩, ?_⟩
    rw [← xCoordinate_legendrePair h2 h3 h0 h1, ← hu, Pair.xCoordinate_scale h2]
  · rintro ⟨l₀, hroot, rfl⟩
    obtain ⟨h0, h1, hss⟩ := (deuringPolynomial_isRoot_iff hDeuringHasseCriterion hp hp5 hL l₀).mp
      hroot
    exact ⟨legendrePair h2 h3 h0 h1, by rw [legendrePair_curve]; exact hss,
      xCoordinate_legendrePair h2 h3 h0 h1⟩

/-- **Corollary 4.6** in the notation of Proposition 3.4: if the supersingular `x`-values are
`range ξ ∪ {-1 | α_p = 1}`, then `ξ_i^{t'} = 64^{t'}` for all `i`, and `(-1)^{t'} = 64^{t'}` if
`α_p = 1`, where `t' = r m`, `m = (p² - 1) / 12`. -/
theorem xi_pow_eq_of_supersingular_eq
    (hGonzalezDivisionPolynomial : WeierstrassCurve.GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : WeierstrassCurve.GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : WeierstrassCurve.SupersingularJInvariant.{u})
    (hVeluIsogeny : WeierstrassCurve.VeluIsogeny.{u}) [IsAlgClosed L] (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) {s : ℕ} {ξ : Fin s → L}
    (hss : {x | ∃ P : Pair 2 L, P.curve.IsSupersingularOver p ∧ P.xCoordinate = x} =
      Set.range ξ ∪ {x | hasseAlpha p = 1 ∧ x = -1}) (r : ℕ) :
    (∀ i, ξ i ^ (r * ((p ^ 2 - 1) / 12)) = 64 ^ (r * ((p ^ 2 - 1) / 12))) ∧
      (hasseAlpha p = 1 → (-1 : L) ^ (r * ((p ^ 2 - 1) / 12)) = 64 ^ (r * ((p ^ 2 - 1) / 12))) := by
  have key : ∀ x ∈ Set.range ξ ∪ {x | hasseAlpha p = 1 ∧ x = -1},
      x ^ (r * ((p ^ 2 - 1) / 12)) = 64 ^ (r * ((p ^ 2 - 1) / 12)) := by
    intro x hx
    rw [← hss] at hx
    obtain ⟨P, hP, rfl⟩ := hx
    exact P.xCoordinate_pow_eq_of_supersingular hGonzalezDivisionPolynomial
      hGonzalezMultiplicationByP hSupersingularJInvariant hVeluIsogeny Fact.out hp5 hL hP r
  exact ⟨fun i => key _ (Or.inl ⟨i, rfl⟩), fun h => key _ (Or.inr ⟨h, rfl⟩)⟩

/-- **Proposition 3.4 with Corollary 4.6**: the factorization of `P_A` over `L`, with
`ξ_i^{t'} = 64^{t'}` and `(-1)^{t'} = 64^{t'}` if `α_p = 1`, for `t' = r (p² - 1) / 12`. -/
theorem hasse_factorization_pow_eq
    (hGonzalezDivisionPolynomial : WeierstrassCurve.GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : WeierstrassCurve.GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : WeierstrassCurve.SupersingularJInvariant.{u})
    (hVeluIsogeny : WeierstrassCurve.VeluIsogeny.{u})
    (hDeuringHasseCriterion : WeierstrassCurve.DeuringHasseCriterion.{u})
    (hDeuringPolynomialSeparable : Polynomial.DeuringPolynomialSeparable.{u})
    [IsAlgClosed L] (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (hK : K.LegendreRegular)
    {PA : MvPolynomial (Fin 2) (ZMod p)} (hw : PA.IsWeightedHomogeneous ![2, 4] (p - 1))
    (hPA : MvPolynomial.aeval ![(K.deltaBar hp2).1, (K.epsBar hp2).1]
      (MvPolynomial.map (ZMod.castHom (dvd_refl p) L) PA) = hasseRule p) (r : ℕ) :
    ∃ (c' : L) (ξ : Fin (hasseS p) → L), c' ≠ 0 ∧
      c' = ZMod.castHom (dvd_refl p) L (MvPolynomial.eval ![1, 0] PA) ∧ Function.Injective ξ ∧
      (∀ i, ξ i ≠ 0 ∧ ξ i ≠ -1) ∧
      MvPolynomial.map (ZMod.castHom (dvd_refl p) L) PA =
        MvPolynomial.C c' * delta L ^ hasseAlpha p *
          ∏ i, (mu L - MvPolynomial.C (ξ i) * eps L) ∧ 1 ≤ hasseS p ∧
      (∀ i, ξ i ^ (r * ((p ^ 2 - 1) / 12)) = 64 ^ (r * ((p ^ 2 - 1) / 12))) ∧
      (hasseAlpha p = 1 → (-1 : L) ^ (r * ((p ^ 2 - 1) / 12)) = 64 ^ (r * ((p ^ 2 - 1) / 12))) := by
  obtain ⟨c', ξ, hc', hc'p, hξinj, hξ, hfac, hs, hss⟩ :=
    K.hasse_factorization hp2 hDeuringHasseCriterion hDeuringPolynomialSeparable hp5 hL hK hw hPA
  obtain ⟨h1, h2⟩ := xi_pow_eq_of_supersingular_eq hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hSupersingularJInvariant hVeluIsogeny hp5 hL hss r
  exact ⟨c', ξ, hc', hc'p, hξinj, hξ, hfac, hs, h1, h2⟩

lemma not_dvd_mul_twelfth (hp5 : 5 ≤ p) {r : ℕ} (hr : ¬ p ∣ r) :
    ¬ p ∣ r * ((p ^ 2 - 1) / 12) := by
  have hp : p.Prime := Fact.out
  intro h
  rcases hp.dvd_mul.mp h with h | h
  · exact hr h
  · have h12 : 12 ∣ p ^ 2 - 1 := by
      have := Nat.Prime.eq_one_or_self_of_dvd hp
      -- `p² ≡ 1 (mod 12)` for primes `p ≥ 5`
      have h3 : ¬ 3 ∣ p := fun h3 => by
        rcases this 3 h3 with h | h <;> omega
      have h2 : ¬ 2 ∣ p := fun h2 => by
        rcases this 2 h2 with h | h <;> omega
      have : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by omega
      have hsq : (p ^ 2) % 12 = 1 := by
        rw [Nat.pow_mod]; rcases this with h | h | h | h <;> rw [h]
      have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
      omega
    have hdvd : p ∣ p ^ 2 - 1 := h.trans (Nat.div_dvd_of_dvd h12)
    have : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
    have h1 : p ∣ 1 := by
      exact (Nat.dvd_sub_iff_right (Nat.one_le_pow _ _ hp.pos) this).mp hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

/-- **Proposition 5.3** (divisibility at level `2`), over the interface `KatzForms` (with
`K.LegendreRegular`), so resting on its interface fields and on the cited facts it uses: let
`p ≥ 5`, `p ∤ r`, `t = r pⁿ (p² - 1) / 12`, and `P_A ∈ 𝔽_p[δ, ε]` the polynomial of eq. (3.1).
Then for every `j`,
`P_A^j ∣ L₂(Δᵗ)` in `𝔽_p[δ, ε]` iff `j ≤ pⁿ`. Here `L₂(Δᵗ)` is represented by
`LevelTwo.larsonL2 (ZMod p) t = (μ² ε)ᵗ - (64 μ ε²)ᵗ`, whose image `L₂(Δᵗ)(δ̄, ε̄)` is
`V₂(Δᵗ) - Δᵗ` by `KatzForms.aeval_larsonL2`. -/
theorem hasse_pow_dvd_larsonL2_iff
    (hGonzalezDivisionPolynomial : WeierstrassCurve.GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : WeierstrassCurve.GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : WeierstrassCurve.SupersingularJInvariant.{u})
    (hVeluIsogeny : WeierstrassCurve.VeluIsogeny.{u})
    (hDeuringHasseCriterion : WeierstrassCurve.DeuringHasseCriterion.{u})
    (hDeuringPolynomialSeparable : Polynomial.DeuringPolynomialSeparable.{u})
    [IsAlgClosed L] (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (hK : K.LegendreRegular)
    {PA : MvPolynomial (Fin 2) (ZMod p)} (hw : PA.IsWeightedHomogeneous ![2, 4] (p - 1))
    (hPA : MvPolynomial.aeval ![(K.deltaBar hp2).1, (K.epsBar hp2).1]
      (MvPolynomial.map (ZMod.castHom (dvd_refl p) L) PA) = hasseRule p)
    {r n t : ℕ} (hr : ¬ p ∣ r) (ht : t = r * p ^ n * ((p ^ 2 - 1) / 12)) (j : ℕ) :
    PA ^ j ∣ larsonL2 (ZMod p) t ↔ j ≤ p ^ n := by
  let _ : Algebra (ZMod p) L := ZMod.algebra L p
  obtain ⟨c', ξ, hc', -, hξinj, hξ, hfac, hs, hW, hW1⟩ :=
    K.hasse_factorization_pow_eq hp2 hGonzalezDivisionPolynomial hGonzalezMultiplicationByP
      hSupersingularJInvariant hVeluIsogeny hDeuringHasseCriterion hDeuringPolynomialSeparable
      hp5 hL hK hw hPA r
  have ht' : t = p ^ n * (r * ((p ^ 2 - 1) / 12)) := by rw [ht]; ring
  rw [ht']
  have hmap : algebraMap (ZMod p) L = ZMod.castHom (dvd_refl p) L := Subsingleton.elim _ _
  exact pow_dvd_larsonL2_iff_of_map p hp2 (not_dvd_mul_twelfth hp5 hr) hs ξ hξinj
    (fun i => (hξ i).1) (fun i => (hξ i).2) hW (hasseAlpha_le_one p) hW1 hc'
    (by rw [hmap]; exact hfac) j

/-- **Proposition 3.4, Corollary 4.6 and Proposition 5.3**, packaged with eq. (3.1): there is a
unique `P_A` as in eq. (3.1), and `P_A^j ∣ L₂(Δᵗ)` iff `j ≤ pⁿ`. -/
theorem exists_hasse_pow_dvd_larsonL2_iff
    (hGonzalezDivisionPolynomial : WeierstrassCurve.GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : WeierstrassCurve.GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : WeierstrassCurve.SupersingularJInvariant.{u})
    (hVeluIsogeny : WeierstrassCurve.VeluIsogeny.{u})
    (hDeuringHasseCriterion : WeierstrassCurve.DeuringHasseCriterion.{u})
    (hDeuringPolynomialSeparable : Polynomial.DeuringPolynomialSeparable.{u})
    (hLarsonLevelTwoStructure : LevelTwoForms.LarsonLevelTwoStructure) [IsAlgClosed L]
    (hp5 : 5 ≤ p) (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (hK : K.LegendreRegular) :
    ∃ PA : MvPolynomial (Fin 2) (ZMod p), PA.IsWeightedHomogeneous ![2, 4] (p - 1) ∧
      MvPolynomial.aeval ![(K.deltaBar hp2).1, (K.epsBar hp2).1]
        (MvPolynomial.map (ZMod.castHom (dvd_refl p) L) PA) = hasseRule p ∧
      ∀ {r n t : ℕ}, ¬ p ∣ r → t = r * p ^ n * ((p ^ 2 - 1) / 12) → ∀ j : ℕ,
        (PA ^ j ∣ larsonL2 (ZMod p) t ↔ j ≤ p ^ n) := by
  obtain ⟨PA, hw, hPA⟩ := K.exists_hasseRule_eq_aeval hp2 hLarsonLevelTwoStructure hp5
  exact ⟨PA, hw, hPA, fun hr ht j => K.hasse_pow_dvd_larsonL2_iff hp2 hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hSupersingularJInvariant hVeluIsogeny hDeuringHasseCriterion
    hDeuringPolynomialSeparable hp5 hL hK hw hPA hr ht j⟩

/-- **Proposition 5.2, identification** (Lemma 3.1 modulo `p` and Lemma 4.1): the polynomial
`L₂(Δᵗ) = (μ² ε)ᵗ - (64 μ ε²)ᵗ` of Larson's ring, evaluated at `δ̄, ε̄`, is the Katz form
`V₂(Δᵗ) - Δᵗ` (the reductions of `V₂(Δᵗ)` and of `Δᵗ` on `Γ₀(2)`). -/
theorem aeval_larsonL2 (t : ℕ) :
    MvPolynomial.aeval ![(K.deltaBar hp2).1, (K.epsBar hp2).1] (larsonL2 L t) =
      (LevelOne.levelRaiseReduction K (LevelOne.discriminantPow t) _
          (LevelOne.isIntegralQExpansion_discriminantPow t)).1 -
        (LevelOne.reductionAtLevel K (LevelOne.discriminantPow t) _
          (LevelOne.isIntegralQExpansion_discriminantPow t)).1 := by
  have h2L : ((2 : ℕ) : L) ≠ 0 := by exact_mod_cast two_ne_zero_of_charP (L := L) hp2
  rw [levelRaiseReduction_discriminantPow K h2L t, reductionAtLevel_discriminantPow]
  simp only [Nat.cast_ofNat]
  rw [K.normalizedVeluDiscriminant_eq_mul hp2, K.discriminantRule_eq_smul hp2]
  funext T
  rw [aeval_test_eq_eval, larsonL2_def]
  simp [mu_def, K.muBar_apply hp2]
  ring

/-- **Remark 5.1**, over the interface `KatzForms` (with `K.LegendreRegular`): for
`p ≡ 3 (mod 4)` (so that the elliptic point `x = -1` is supersingular), `p ∤ r` and
`t = r pⁿ (p² - 1) / 12`, the factor `δ` divides `L₂(Δᵗ)` in `𝔽_p[δ, ε]` exactly to the order
`2 pⁿ`. -/
theorem delta_pow_dvd_larsonL2_iff_of_mod_four
    (hGonzalezDivisionPolynomial : WeierstrassCurve.GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : WeierstrassCurve.GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : WeierstrassCurve.SupersingularJInvariant.{u})
    (hVeluIsogeny : WeierstrassCurve.VeluIsogeny.{u})
    (hDeuringHasseCriterion : WeierstrassCurve.DeuringHasseCriterion.{u})
    (hDeuringPolynomialSeparable : Polynomial.DeuringPolynomialSeparable.{u})
    (hLarsonLevelTwoStructure : LevelTwoForms.LarsonLevelTwoStructure) [IsAlgClosed L]
    (hp5 : 5 ≤ p) (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (hK : K.LegendreRegular)
    (h4 : p % 4 = 3)
    {r n t : ℕ} (hr : ¬ p ∣ r) (ht : t = r * p ^ n * ((p ^ 2 - 1) / 12)) (j : ℕ) :
    delta (ZMod p) ^ j ∣ larsonL2 (ZMod p) t ↔ j ≤ 2 * p ^ n := by
  let _ : Algebra (ZMod p) L := ZMod.algebra L p
  have hp2 : p ≠ 2 := by omega
  obtain ⟨PA, hw, hPA⟩ := K.exists_hasseRule_eq_aeval hp2 hLarsonLevelTwoStructure hp5
  obtain ⟨-, -, -, -, -, -, -, -, -, hW1⟩ := K.hasse_factorization_pow_eq hp2
    hGonzalezDivisionPolynomial hGonzalezMultiplicationByP hSupersingularJInvariant hVeluIsogeny
    hDeuringHasseCriterion hDeuringPolynomialSeparable hp5 hL hK hw hPA r
  have hα : hasseAlpha p = 1 := by rw [hasseAlpha_def, ite_eq_left_iff.mpr (fun h => absurd h4 h)]
  have ht' : t = p ^ n * (r * ((p ^ 2 - 1) / 12)) := by rw [ht]; ring
  rw [ht', ← delta_pow_dvd_larsonL2_iff (K := L) p hp2 (not_dvd_mul_twelfth hp5 hr) (hW1 hα) j,
    ← map_delta (algebraMap (ZMod p) L), ← map_larsonL2 (algebraMap (ZMod p) L), ← map_pow]
  exact ⟨fun h => map_dvd _ h, MvPolynomial.dvd_of_map_dvd_map⟩

end KatzForms
