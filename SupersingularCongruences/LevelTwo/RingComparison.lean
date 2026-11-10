/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.LevelTwo.HasseLevelTwo
public import SupersingularCongruences.LevelTwo.RingDimension
import all SupersingularCongruences.LevelTwo.HasseFactorization
import all SupersingularCongruences.LevelTwo.HasseLevelTwo
import all SupersingularCongruences.KatzForms.LevelTwoReduction

/-!
# Remark 5.2 at level `2`: Larson's ring inside the geometric ring

Let `p` be an odd prime, `L` a field of characteristic `p` and `K : KatzForms p 2 L`. Remark 5.2
shows that the inclusion of Larson's ring `L[δ, ε]` (weights `2, 4`) into the geometric ring of
Katz forms on `Γ₀(2)` over `L` is an isomorphism in every even weight. This file proves the parts
of this comparison that only use the `q`-expansion principle and the reduction of classical forms.

## Main results

* `KatzForms.eq_zero_of_aeval_deltaBar_epsBar_eq_zero`: a weighted homogeneous `P ∈ L[δ, ε]`
  with `P(δ̄, ε̄) = 0` as a Katz form is zero. So the map `L[δ, ε]_k → M_k(Γ₀(2))_L`,
  `P ↦ P(δ̄, ε̄)` (`KatzForms.larsonToForm`), is injective
  (`KatzForms.larsonToForm_injective`), and `⌊k / 4⌋ + 1 ≤ dim_L M_k(Γ₀(2))_L` for even `k` when
  the space of forms is finite-dimensional (`KatzForms.le_finrank_form`).
* `KatzForms.exists_reduce_eq_aeval`: every `P(δ̄, ε̄)` with `P ∈ 𝔽_p[δ, ε]` weighted homogeneous
  of weight `k` is the reduction `K.reduce f` of a classical form `f ∈ M_k(Γ₀(2))` with
  `p`-integral rational `q`-expansion.

The reverse inequality `dim_L M_k(Γ₀(2))_L ≤ ⌊k / 4⌋ + 1`, hence the equality of eq. (5.2) and the
surjectivity of `KatzForms.larsonToForm`, rests on `dim_{𝔽_p} M_k(2)_{ℤ/p} = dim_ℂ M_k(Γ₀(2), ℂ)`,
which the remark derives from the Kodaira–Spencer isomorphism, the vanishing of `H¹(ω^{⊗k})` and
cohomology and base change on the moduli scheme over `ℤ_(p)`; it is not proved here.

## Proof

The `q`-expansions `D, E ∈ L⟦q⟧` of `δ̄, ε̄` have constant terms `1/4` and `1/16`, and
`D² - E` (the `q`-expansion of `μ̄`) is `4 q + O(q²)`. For `P` of weight `2 (2m + α)`,
`α ≤ 1`, `P(D, E) = D^α E^m G(D² / E)` with `G = LevelTwo.dehom P m`
(`LevelTwo.aeval_eq_dehom_powerSeries`), and `D² / E = 1 + w` with `w` of `q`-order exactly `1`.
A nonzero polynomial does not vanish at a power series of order `1`
(`PowerSeries.aeval_ne_zero_of_order_one`: its lowest nonzero term gives a nonzero coefficient),
so `G = 0`, hence `P = 0` (`LevelTwo.eq_zero_of_dehom_eq_zero`). The `q`-expansion of
`P(δ̄, ε̄)` is `P(D, E)` (`KatzForms.hasQExp_aeval`), which proves the injectivity.
-/

public section

open MvPolynomial

namespace PowerSeries

/-- A nonzero polynomial over a field does not vanish at a power series of `q`-order exactly
`1`: if `j` is the lowest degree with `g_j ≠ 0`, then the coefficient of `q^j` in `g(w)` is
`g_j w₁^j ≠ 0`. -/
theorem aeval_ne_zero_of_order_one {L : Type*} [Field L] {w : PowerSeries L}
    (hw0 : constantCoeff w = 0) (hw1 : coeff 1 w ≠ 0) {g : Polynomial L} (hg : g ≠ 0) :
    Polynomial.aeval w g ≠ 0 := by
  obtain ⟨w', rfl⟩ := (PowerSeries.X_dvd_iff).mpr hw0
  have hw' : constantCoeff w' ≠ 0 := by
    rwa [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply] at hw1
  set j := g.natTrailingDegree
  intro h
  have hc := congrArg (PowerSeries.coeff j) h
  rw [Polynomial.aeval_eq_sum_range, map_sum, map_zero] at hc
  rw [Finset.sum_eq_single j] at hc
  · rw [coeff_smul, mul_pow, coeff_X_pow_mul'] at hc
    simp only [le_refl, ↓reduceIte, Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_pow,
      smul_eq_mul] at hc
    exact mul_ne_zero (mt Polynomial.trailingCoeff_eq_zero.mp hg) (pow_ne_zero _ hw') hc
  · intro i _ hij
    rw [coeff_smul, mul_pow, coeff_X_pow_mul', smul_eq_mul]
    split_ifs with hle
    · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (lt_of_le_of_ne hle hij), zero_mul]
    · rw [mul_zero]
  · intro hj
    exfalso; apply hj
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Polynomial.natTrailingDegree_le_natDegree g)

end PowerSeries

namespace LevelTwo

variable {L : Type*} [Field L]

/-- A weighted homogeneous `P` of weight `2 (2m + α)`, `α ≤ 1`, is determined by its
dehomogenization: if `dehom P m = 0` then `P = 0`. -/
lemma eq_zero_of_dehom_eq_zero {P : MvPolynomial (Fin 2) L} {m α : ℕ} (hα : α ≤ 1)
    (hP : P.IsWeightedHomogeneous ![2, 4] (2 * (2 * m + α))) (h : dehom P m = 0) : P = 0 := by
  ext d
  change P.coeff d = 0
  by_contra hd
  have hw := hP hd
  rw [weight_two_four_apply] at hw
  have hc := congrArg (fun g => Polynomial.coeff g (m - d 1)) h
  simp only [dehom, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single d] at hc
  · exact hd (by simpa using hc)
  · intro d' hd' hne
    have hw' := hP (mem_support_iff.mp hd')
    rw [weight_two_four_apply] at hw'
    refine ite_eq_right_iff.mpr fun heq => absurd ?_ hne
    ext i
    fin_cases i <;> simp <;> omega
  · intro h'; exact absurd (mem_support_iff.mpr hd) h'

/-- `P(D, E) = D^α E^m G(D² E⁻¹)` in a commutative ring, for `E` invertible with inverse `Einv`,
`P` of weight `2 (2m + α)`, `α ≤ 1`, and `G = dehom P m`. -/
lemma aeval_eq_dehom_powerSeries {A : Type*} [CommRing A] [Algebra L A]
    {P : MvPolynomial (Fin 2) L} {m α : ℕ} (hα : α ≤ 1)
    (hP : P.IsWeightedHomogeneous ![2, 4] (2 * (2 * m + α))) {D E Einv : A}
    (hE : E * Einv = 1) :
    aeval ![D, E] P = D ^ α * E ^ m * Polynomial.aeval (D ^ 2 * Einv) (dehom P m) := by
  rw [aeval_eq_sum_fin_two, dehom, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw := hP (mem_support_iff.mp hd)
  rw [weight_two_four_apply] at hw
  have h0 : d 0 = α + 2 * (m - d 1) := by omega
  have hbm : E ^ m = E ^ (m - d 1) * E ^ d 1 := by rw [← pow_add]; congr 1; omega
  have h1 : (E * Einv) ^ (m - d 1) = 1 := by rw [hE, one_pow]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, h0, hbm,
    map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
  rw [mul_pow] at h1
  rw [mul_pow, pow_add, pow_mul]
  linear_combination (algebraMap L A (P.coeff d) * D ^ α * (D ^ 2) ^ (m - d 1) *
    E ^ d 1) * h1.symm

/-- **Algebraic independence of `D, E` in every weight**: let `D, E ∈ L⟦q⟧` have nonzero constant
terms, and let `D² - E` have `q`-order exactly `1`. A weighted homogeneous `P ∈ L[δ, ε]`
(weights `2, 4`) with `P(D, E) = 0` is zero. -/
theorem eq_zero_of_aeval_powerSeries_eq_zero {D E : PowerSeries L}
    (hD : PowerSeries.constantCoeff D ≠ 0) (hE : PowerSeries.constantCoeff E ≠ 0)
    (hM0 : PowerSeries.constantCoeff (D ^ 2 - E) = 0) (hM1 : PowerSeries.coeff 1 (D ^ 2 - E) ≠ 0)
    {P : MvPolynomial (Fin 2) L} {k : ℕ} (hP : P.IsWeightedHomogeneous ![2, 4] k)
    (h : aeval ![D, E] P = 0) : P = 0 := by
  rcases Nat.even_or_odd k with hk | hk
  · have hα : k / 2 % 2 ≤ 1 := by omega
    have hk' : k = 2 * (2 * (k / 4) + k / 2 % 2) := by obtain ⟨r, rfl⟩ := hk; omega
    rw [hk'] at hP
    refine eq_zero_of_dehom_eq_zero hα hP ?_
    by_contra hg
    have hEE := PowerSeries.mul_inv_cancel E hE
    rw [aeval_eq_dehom_powerSeries hα hP hEE] at h
    have hD0 : D ≠ 0 := fun h0 => hD (by rw [h0, map_zero])
    have hE0 : E ≠ 0 := fun h0 => hE (by rw [h0, map_zero])
    have hz : Polynomial.aeval (D ^ 2 * E⁻¹) (dehom P (k / 4)) = 0 :=
      (mul_eq_zero.mp h).resolve_left (mul_ne_zero (pow_ne_zero _ hD0) (pow_ne_zero _ hE0))
    obtain ⟨u, hu⟩ := (PowerSeries.X_dvd_iff).mpr hM0
    have hw : D ^ 2 * E⁻¹ = PowerSeries.X * (u * E⁻¹) + 1 := by
      rw [← mul_assoc, ← hu, sub_mul, hEE]; ring
    have hcomp : (dehom P (k / 4)).comp (Polynomial.X + 1) ≠ 0 := by
      intro h0
      have := congrArg (fun f => f.comp (Polynomial.X - 1)) h0
      exact hg (by simpa [Polynomial.comp_assoc] using this)
    refine PowerSeries.aeval_ne_zero_of_order_one (w := PowerSeries.X * (u * E⁻¹)) ?_ ?_ hcomp ?_
    · simp
    · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
        PowerSeries.constantCoeff_inv]
      refine mul_ne_zero ?_ (inv_ne_zero hE)
      rwa [hu, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at hM1
    · rw [Polynomial.aeval_comp, map_add, Polynomial.aeval_X, map_one, ← hw, hz]
  · ext d
    change P.coeff d = 0
    by_contra hd
    have hw := hP hd
    rw [weight_two_four_apply] at hw
    obtain ⟨r, rfl⟩ := hk
    omega

end LevelTwo

namespace LevelTwoForms

open PowerSeries

lemma coeff_zero_deltaSeries : deltaSeries.coeff 0 = (((2 ^ 2 : ℕ) : ℚ))⁻¹ := by
  rw [coeff_deltaSeries]; simp [e2CoeffRat]; norm_num

lemma coeff_zero_epsSeries : epsSeries.coeff 0 = (((2 ^ 4 : ℕ) : ℚ))⁻¹ := by
  rw [coeff_epsSeries]; simp

lemma coeff_zero_muSeries : muSeries.coeff 0 = 0 := by
  rw [muSeries, map_sub, pow_two, PowerSeries.coeff_mul]
  simp [coeff_deltaSeries, coeff_epsSeries, e2CoeffRat]; norm_num

/-- `μ = 4 q + O(q²)`. -/
lemma coeff_one_muSeries : muSeries.coeff 1 = 4 := by
  rw [muSeries, map_sub, pow_two, PowerSeries.coeff_mul]
  simp [coeff_deltaSeries, coeff_epsSeries, e2CoeffRat, Finset.Nat.antidiagonal_succ]; norm_num

lemma ratCast_inv_two_pow_ne_zero {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [CharP L p]
    (hp2 : p ≠ 2) (n : ℕ) : (Rat.cast (((2 ^ n : ℕ) : ℚ))⁻¹ : L) ≠ 0 := by
  have ha : ¬ p ∣ (((2 ^ n : ℕ) : ℚ)).den := Rat.not_dvd_den_natCast (p := p) (2 ^ n)
  have hb : ¬ p ∣ (((2 ^ n : ℕ) : ℚ))⁻¹.den :=
    Rat.not_dvd_den_inv_natCast (not_dvd_of_ne_two hp2)
  have h := Rat.cast_mul_of_not_dvd (L := L) ha hb
  rw [mul_inv_cancel₀ (by positivity), Rat.cast_one] at h
  exact right_ne_zero_of_mul (h ▸ one_ne_zero)

end LevelTwoForms

namespace KatzForms

open LevelTwoForms LevelTwo PowerSeries

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [DecidableEq L] [CharP L p]
  (K : KatzForms p 2 L) (hp2 : p ≠ 2)

/-- **Remark 5.2, injectivity of `L[δ, ε]_k → M_k(Γ₀(2))_L`**: for `p` odd, a weighted
homogeneous `P ∈ L[δ, ε]` of weight `k` (weights `2, 4`) with `P(δ̄, ε̄) = 0` as a Katz form on
`Γ₀(2)` over `L` is zero. -/
theorem eq_zero_of_aeval_deltaBar_epsBar_eq_zero {P : MvPolynomial (Fin 2) L} {k : ℕ}
    (hP : P.IsWeightedHomogeneous ![2, 4] k)
    (h : aeval ![(K.deltaBar hp2).1, (K.epsBar hp2).1] P = 0) : P = 0 := by
  have h0 : K.HasQExp 2 (![(K.deltaBar hp2).1, (K.epsBar hp2).1] 0)
      (![deltaSeries.reduceTo L, epsSeries.reduceTo L] 0) := K.hasQExp_deltaBar hp2
  have h1 : K.HasQExp 4 (![(K.deltaBar hp2).1, (K.epsBar hp2).1] 1)
      (![deltaSeries.reduceTo L, epsSeries.reduceTo L] 1) := K.hasQExp_epsBar hp2
  obtain ⟨hmem, hq⟩ := K.hasQExp_aeval h0 h1 hP
  have hz : (⟨_, hmem⟩ : K.form k) = 0 := Subtype.ext h
  rw [hz, map_zero] at hq
  have hmu : (deltaSeries.reduceTo L) ^ 2 - epsSeries.reduceTo L = muSeries.reduceTo L := by
    rw [muSeries, reduceTo_sub ((isPIntegral_deltaSeries hp2).pow 2) (isPIntegral_epsSeries hp2),
      reduceTo_pow (isPIntegral_deltaSeries (p := p) hp2)]
  refine eq_zero_of_aeval_powerSeries_eq_zero ?_ ?_ ?_ ?_ hP hq.symm
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_reduceTo, coeff_zero_deltaSeries]
    exact ratCast_inv_two_pow_ne_zero hp2 2
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_reduceTo, coeff_zero_epsSeries]
    exact ratCast_inv_two_pow_ne_zero hp2 4
  · rw [hmu, ← coeff_zero_eq_constantCoeff_apply, coeff_reduceTo, coeff_zero_muSeries,
      Rat.cast_zero]
  · rw [hmu, coeff_reduceTo, coeff_one_muSeries, Rat.cast_ofNat,
      show (4 : L) = 2 ^ 2 by norm_num]
    exact pow_ne_zero _ (two_ne_zero_of_charP hp2)

/-- The map `L[δ, ε]_k → M_k(Γ₀(2))_L`, `P ↦ P(δ̄, ε̄)`, from the weight-`k` part of Larson's
ring (weights `2, 4`) to the Katz forms of weight `k` on `Γ₀(2)` over `L`. -/
noncomputable def larsonToForm (k : ℕ) :
    weightedHomogeneousSubmodule L ![2, 4] k →ₗ[L] K.form k where
  toFun P := ⟨aeval ![(K.deltaBar hp2).1, (K.epsBar hp2).1] P.1,
    (K.hasQExp_aeval (S := ![deltaSeries.reduceTo L, epsSeries.reduceTo L])
      (K.hasQExp_deltaBar hp2) (K.hasQExp_epsBar hp2)
      ((mem_weightedHomogeneousSubmodule _ _ _ _).mp P.2)).1⟩
  map_add' P Q := Subtype.ext (by simp)
  map_smul' c P := Subtype.ext (by simp)

/-- **Remark 5.2**: the inclusion `L[δ, ε]_k → M_k(Γ₀(2))_L` of Larson's ring into the geometric
ring is injective (`p` odd). -/
theorem larsonToForm_injective (k : ℕ) : Function.Injective (K.larsonToForm hp2 k) := by
  refine (injective_iff_map_eq_zero _).mpr fun P hP => Subtype.ext ?_
  exact K.eq_zero_of_aeval_deltaBar_epsBar_eq_zero hp2
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mp P.2) (congrArg Subtype.val hP)

include hp2 in
/-- **Remark 5.2, eq. (5.2), the inequality `dim F[δ, ε]_k ≤ dim M_k(2)`**: for `p` odd, even
`k` and a finite-dimensional space of Katz forms of weight `k` on `Γ₀(2)` over `L`,
`⌊k / 4⌋ + 1 ≤ dim_L M_k(Γ₀(2))_L`. -/
theorem le_finrank_form {k : ℕ} (hk : Even k) [FiniteDimensional L (K.form k)] :
    k / 4 + 1 ≤ Module.finrank L (K.form k) := by
  rw [← finrank_weightedHomogeneousSubmodule L hk]
  exact LinearMap.finrank_le_finrank_of_injective (K.larsonToForm_injective hp2 k)

/-- **Remark 5.2, the classical lift at level `2`**: for `p` odd, every element `P(δ̄, ε̄)` of
`𝔽_p[δ̄, ε̄]_k` (`P ∈ 𝔽_p[δ, ε]` weighted homogeneous of weight `k`) is the reduction of a
classical form `f ∈ M_k(Γ₀(2))` with `p`-integral rational `q`-expansion: lift the coefficients
of `P` to `ℤ` and take `f = P̃(δ, ε)`. -/
theorem exists_reduce_eq_aeval {P : MvPolynomial (Fin 2) (ZMod p)} {k : ℕ}
    (hP : P.IsWeightedHomogeneous ![2, 4] k) :
    ∃ (f : ModularForm (CongruenceSubgroup.Gamma0 2) k) (G : PowerSeries ℚ)
      (hG : G.IsPIntegral p)
      (hfG : PowerSeries.map (Rat.castHom ℂ) G = UpperHalfPlane.qExpansion 1 f),
      (K.reduce f G hG hfG).1 =
        aeval ![(K.deltaBar hp2).1, (K.epsBar hp2).1] (map (ZMod.castHom (dvd_refl p) L) P) := by
  set PQ : MvPolynomial (Fin 2) ℚ :=
    ∑ e ∈ P.support, monomial e (((P.coeff e).val : ℕ) : ℚ) with hPQ
  have hPQw : PQ.IsWeightedHomogeneous ![2, 4] k :=
    IsWeightedHomogeneous.sum _ _ _ fun _ he => isWeightedHomogeneous_monomial _ _ _
      (hP (mem_support_iff.mp he))
  obtain ⟨F, hF, hFS⟩ :=
    LevelTwoForms.hasQExp_aeval (isWeightedHomogeneous_map (algebraMap ℚ ℂ) hPQw)
  set G : PowerSeries ℚ := aeval ![deltaSeries, epsSeries] PQ with hGdef
  have hterm : ∀ e ∈ P.support, (aeval ![deltaSeries, epsSeries]
      (monomial e (((P.coeff e).val : ℕ) : ℚ))).IsPIntegral p := fun e _ => by
    rw [aeval_monomial_fin_two]
    exact (isPIntegral_C _ (by exact_mod_cast Rat.not_dvd_den_natCast (p := p) _)).mul
      (((isPIntegral_deltaSeries hp2).pow _).mul ((isPIntegral_epsSeries hp2).pow _))
  have hG : G.IsPIntegral p := by
    rw [hGdef, hPQ, map_sum]
    exact IsPIntegral.sum _ hterm
  have h1 : (PowerSeries.map (Rat.castHom ℂ)).comp (algebraMap ℚ (PowerSeries ℚ)) =
      algebraMap ℚ (PowerSeries ℂ) := RingHom.ext_rat _ _
  have h2 : ⇑(PowerSeries.map (Rat.castHom ℂ)) ∘ ![deltaSeries, epsSeries] =
      ![UpperHalfPlane.qExpansion 1 ⇑LevelTwoForms.delta,
        UpperHalfPlane.qExpansion 1 ⇑LevelTwoForms.eps] := by
    funext i
    fin_cases i
    · simp [map_deltaSeries]
    · simp [map_epsSeries]
  have hfG : PowerSeries.map (Rat.castHom ℂ) G = UpperHalfPlane.qExpansion 1 F := by
    rw [hFS, aeval_map_algebraMap, hGdef, aeval_def, aeval_def, eval₂_comp_left, h1, h2]
  refine ⟨F, G, hG, hfG, ?_⟩
  have hPLw := isWeightedHomogeneous_map (ZMod.castHom (dvd_refl p) L) hP
  have h0 : K.HasQExp 2 (![(K.deltaBar hp2).1, (K.epsBar hp2).1] 0)
      (![deltaSeries.reduceTo L, epsSeries.reduceTo L] 0) := K.hasQExp_deltaBar hp2
  have h1' : K.HasQExp 4 (![(K.deltaBar hp2).1, (K.epsBar hp2).1] 1)
      (![deltaSeries.reduceTo L, epsSeries.reduceTo L] 1) := K.hasQExp_epsBar hp2
  obtain ⟨hmem, hq⟩ := K.hasQExp_aeval h0 h1' hPLw
  refine K.eq_of_qExp_eq (K.reduce F G hG hfG).2 hmem ?_
  rw [hq]
  change K.qExp k (K.reduce F G hG hfG) = _
  rw [K.qExp_reduce, hGdef, hPQ, map_sum, reduceTo_sum _ hterm]
  conv_rhs => rw [P.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_monomial, aeval_monomial_fin_two, aeval_monomial_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [show algebraMap ℚ (PowerSeries ℚ) (((P.coeff e).val : ℕ) : ℚ) =
      PowerSeries.C (((P.coeff e).val : ℕ) : ℚ) from rfl,
    reduceTo_mul (isPIntegral_C _ (by exact_mod_cast Rat.not_dvd_den_natCast (p := p) _))
      (((isPIntegral_deltaSeries hp2).pow _).mul ((isPIntegral_epsSeries hp2).pow _)),
    reduceTo_mul ((isPIntegral_deltaSeries hp2).pow _) ((isPIntegral_epsSeries hp2).pow _),
    reduceTo_C, reduceTo_pow (isPIntegral_deltaSeries hp2),
    reduceTo_pow (isPIntegral_epsSeries hp2), Rat.cast_natCast, ZMod.natCast_val,
    ZMod.castHom_apply]
  rfl

end KatzForms
