/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.LevelOne.IntegralQExpansion

/-!
# Maximal `q`-order of mod `p` reductions of level-one forms

Let `g` be a level-one modular form of weight `k` whose q-expansion `G` has integral coefficients,
and let `Ḡ ∈ (ZMod p)⟦X⟧` be its reduction modulo a prime `p`. We show that if `Ḡ ≠ 0` then
`12 · ord_q(Ḡ) ≤ k` (manuscript, Lemma 2.2, in a form valid for every weight). In weight `12t`
this gives `ord_q(Ḡ) ≤ t`, and the reduction of `Δᵗ` has `q`-order exactly `t`. As a consequence
no integral level-one form of weight `k' < 12t` has the same reduction as `Δᵗ`
(manuscript, Lemma 2.3).

The proof of Lemma 2.3 here differs from the manuscript, which uses the theory of filtrations of
Serre and Swinnerton-Dyer: it is deduced directly from the weight bound of Lemma 2.2.

## Main results

* `LevelOne.twelve_mul_order_reduction_le_weight`: `12 · ord_q(Ḡ) ≤ k` for `Ḡ ≠ 0`.
* `LevelOne.order_reduction_le`: in weight `12t`, `ord_q(Ḡ) ≤ t`.
* `LevelOne.order_reduction_integralDiscriminant_pow`: `ord_q(Δᵗ mod p) = t`.
* `LevelOne.reduction_ne_reduction_discriminantPow`: no form of weight `< 12t` with integral
  q-expansion is congruent to `Δᵗ` modulo `p`.
-/

public section

open ModularForm PowerSeries UpperHalfPlane
open scoped MatrixGroups

namespace LevelOne

variable {p : ℕ} [Fact p.Prime]

/-- A nonzero level-one form has even weight `k ≥ 0` with `k ≠ 2`. -/
lemma weight_nonneg_even_ne_two {k : ℤ} {g : ModularForm 𝒮ℒ k} (hg : g ≠ 0) :
    0 ≤ k ∧ Even k ∧ k ≠ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra hk
    exact hg (DFunLike.coe_injective
      (ModularFormClass.levelOne_neg_weight_eq_zero (not_le.mp hk) g))
  · by_contra hk
    exact hg (levelOne_odd_weight_eq_zero (Int.not_even_iff_odd.mp hk) g)
  · rintro rfl
    exact hg (rank_zero_iff_forall_zero.mp levelOne_weight_two_rank_zero g)

/-- The reduction of `Δ` modulo `p` has `q`-order `1`. -/
theorem order_reduction_integralDiscriminant :
    (PowerSeries.map (Int.castRingHom (ZMod p)) integralDiscriminant).order = 1 := by
  rw [show (1 : ℕ∞) = (1 : ℕ) from rfl, order_eq_nat]
  refine ⟨?_, fun i hi ↦ ?_⟩
  · simp [coeff_one_integralDiscriminant]
  · obtain rfl : i = 0 := by omega
    simp [coeff_zero_integralDiscriminant]

/-- The reduction of `Δᵗ` modulo `p` has `q`-order exactly `t`. -/
theorem order_reduction_integralDiscriminant_pow (t : ℕ) :
    (PowerSeries.map (Int.castRingHom (ZMod p)) (integralDiscriminant ^ t)).order = t := by
  rw [map_pow, order_pow, order_reduction_integralDiscriminant, nsmul_eq_mul, mul_one]

private theorem twelve_mul_le_weight_of_order_eq (n : ℕ) {k : ℤ} (g : ModularForm 𝒮ℒ k)
    {G : PowerSeries ℤ} (hG : IsIntegralQExpansion G g)
    (hn : (PowerSeries.map (Int.castRingHom (ZMod p)) G).order = n) : 12 * (n : ℤ) ≤ k := by
  induction n generalizing k G with
  | zero =>
    have hg : g ≠ 0 := by
      rintro rfl
      rw [hG.eq_zero rfl, map_zero, order_zero] at hn
      exact ENat.top_ne_natCast 0 hn
    simpa using (weight_nonneg_even_ne_two hg).1
  | succ n ih =>
    set ρ := PowerSeries.map (Int.castRingHom (ZMod p))
    have hg : g ≠ 0 := by
      rintro rfl
      rw [hG.eq_zero rfl, map_zero, order_zero] at hn
      exact ENat.top_ne_natCast _ hn
    obtain ⟨hk0, hkev, hk2⟩ := weight_nonneg_even_ne_two hg
    obtain ⟨e, E, hE, hE0⟩ := exists_isIntegralQExpansion_coeff_zero_eq_one hk0 hkev hk2
    set c := G.coeff 0
    -- the constant term of `G` vanishes modulo `p`
    have hc : ((c : ℤ) : ZMod p) = 0 := by
      have := coeff_of_lt_order (φ := ρ G) 0 (by rw [hn]; exact_mod_cast Nat.succ_pos n)
      simpa [ρ, c] using this
    set G₁ := G - C c * E
    have hG₁ : IsIntegralQExpansion G₁ ⇑(g - (c : ℂ) • e) :=
      isIntegralQExpansion_sub hG (isIntegralQExpansion_intCast_smul hE c)
    have h0 : (qExpansion 1 ⇑(g - (c : ℂ) • e)).coeff 0 = 0 := by
      rw [hG₁.coeff 0]
      simp only [G₁, map_sub, coeff_C_mul, hE0, mul_one, c, sub_self, Int.cast_zero]
    obtain ⟨H, hH, hGH⟩ := exists_isIntegralQExpansion_discriminantEquiv _ h0 hG₁
    -- modulo `p`, `G ≡ G₁ = Δ * H`
    have hρ : ρ G = ρ integralDiscriminant * ρ H := by
      have : ρ G₁ = ρ G := by
        simp only [G₁, map_sub, map_mul, ρ, map_C, Int.coe_castRingHom, hc, map_zero, zero_mul,
          sub_zero]
      rw [← this, hGH, map_mul]
    have hHn : (ρ H).order = n := by
      rw [hρ, order_mul, order_reduction_integralDiscriminant] at hn
      have hne : (ρ H).order ≠ ⊤ := by
        intro h
        rw [h, add_top] at hn
        exact ENat.top_ne_natCast _ hn
      lift (ρ H).order to ℕ using hne with m hm
      norm_cast at hn ⊢
      omega
    have := ih _ hH hHn
    push_cast
    omega

/-- **Maximal `q`-order** (generalized form of [ono-manuscript, Lemma 2.2]). If a level-one modular
form `g` of weight `k` has integral q-expansion `G` whose reduction `Ḡ` modulo the prime `p` is
nonzero, then `12 · ord_q(Ḡ) ≤ k`. -/
theorem twelve_mul_order_reduction_le_weight {k : ℤ} (g : ModularForm 𝒮ℒ k)
    {G : PowerSeries ℤ} (hG : IsIntegralQExpansion G g)
    (hne : PowerSeries.map (Int.castRingHom (ZMod p)) G ≠ 0) :
    12 * ((PowerSeries.map (Int.castRingHom (ZMod p)) G).order.toNat : ℤ) ≤ k :=
  twelve_mul_le_weight_of_order_eq _ g hG (ENat.natCast_toNat (order_eq_top.not.mpr hne)).symm

/-- **Maximal `q`-order** [ono-manuscript, Lemma 2.2]: if `g` is a level-one form of weight `12t`
with integral q-expansion `G` whose reduction `Ḡ` modulo `p` is nonzero, then `ord_q(Ḡ) ≤ t`. -/
theorem order_reduction_le {t : ℕ} (g : ModularForm 𝒮ℒ (12 * t)) {G : PowerSeries ℤ}
    (hG : IsIntegralQExpansion G g) (hne : PowerSeries.map (Int.castRingHom (ZMod p)) G ≠ 0) :
    (PowerSeries.map (Int.castRingHom (ZMod p)) G).order ≤ t := by
  have h := twelve_mul_order_reduction_le_weight g hG hne
  rw [← ENat.natCast_toNat (order_eq_top.not.mpr hne)]
  exact_mod_cast (by omega : (PowerSeries.map (Int.castRingHom (ZMod p)) G).order.toNat ≤ t)

/-- The `t`-th power of the discriminant, as a level-one modular form of weight `12t`. -/
noncomputable def discriminantPow (t : ℕ) : ModularForm 𝒮ℒ (12 * t) :=
  ModularForm.mcast (by ring) ((CuspForm.toModularFormₗ CuspForm.discriminant).pow t)

/-- `Δᵗ` has integral q-expansion `integralDiscriminant ^ t`. -/
theorem isIntegralQExpansion_discriminantPow (t : ℕ) :
    IsIntegralQExpansion (integralDiscriminant ^ t) (discriminantPow t) := by
  rw [discriminantPow, coe_mcast]
  exact isIntegralQExpansion_pow isIntegralQExpansion_discriminant t

/-- The reduction of `Δᵗ` modulo `p` is nonzero. -/
theorem reduction_integralDiscriminant_pow_ne_zero (t : ℕ) :
    PowerSeries.map (Int.castRingHom (ZMod p)) (integralDiscriminant ^ t) ≠ 0 := by
  intro h
  have := order_reduction_integralDiscriminant_pow (p := p) t
  rw [h, order_zero] at this
  exact ENat.top_ne_natCast t this

/-- **No lower-weight congruence** [ono-manuscript, Lemma 2.3]: no level-one form `g` of weight
`k' < 12t` with integral q-expansion `H` has the same reduction modulo `p` as `Δᵗ`. -/
theorem reduction_ne_reduction_discriminantPow {t : ℕ} {k' : ℤ} (hk' : k' < 12 * t)
    (g : ModularForm 𝒮ℒ k') {H : PowerSeries ℤ} (hH : IsIntegralQExpansion H g) :
    PowerSeries.map (Int.castRingHom (ZMod p)) H ≠
      PowerSeries.map (Int.castRingHom (ZMod p)) (integralDiscriminant ^ t) := by
  intro heq
  have hne : PowerSeries.map (Int.castRingHom (ZMod p)) H ≠ 0 :=
    heq ▸ reduction_integralDiscriminant_pow_ne_zero t
  have h := twelve_mul_order_reduction_le_weight g hH hne
  rw [heq, order_reduction_integralDiscriminant_pow, ENat.toNat_natCast] at h
  omega

end LevelOne
