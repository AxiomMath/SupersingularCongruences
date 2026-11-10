/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.KatzForms.Reduction
public import SupersingularCongruences.KatzForms.LevelCover

/-!
# Divisibility by the Hasse invariant at every level (Proposition 5.4)

Let `p ≥ 5`, `L` an algebraic closure of `𝔽_p`, `ℓ ≠ p` a prime, `m = (p² - 1) / 12`,
`t = r pⁿ m` and `1 ≤ j ≤ pⁿ`. Then `A_p^j ∣ L_ℓ(Δᵗ) = V_ℓ(Δᵗ) - Δᵗ` in the ring of Katz forms
modulo `p` on `Γ₀(ℓ)`.

## Proof (manuscript, Proposition 5.4)

* Freshman's dream: with `t' = r m`, `L_ℓ(Δᵗ) = G ^ (pⁿ)` for `G = L_ℓ(Δ^{t'})`
  (Lemma 4.1 identifies the reductions with the rules `Δ^{[ℓ]}` and `Δ`).
* `G` vanishes at every supersingular test object (Theorem 1.2).
* On the level cover `Ȳ`: `A_p` has order `≤ 1` (Igusa), order `0` at ordinary points
  (Lemma 2.1(a)) and at cusps (Lemma 2.1(c)), so `G = A_p · h` with `h` a section; `h` is
  `Q`-invariant by cancellation and descends to a Katz form `H`.
* `H` is defined over `𝔽_p` by cancellation in the domain of Katz forms, since `G` and `A_p` are.
* Finally `L_ℓ(Δᵗ) = A_p^{pⁿ} H^{pⁿ} = A_p^j · (A_p^{pⁿ - j} H^{pⁿ})`.

## Main results

* `KatzForms.exists_hasse_mul_eq_levelRaise_sub`: `A_p ∣ L_ℓ(Δ^{r m})`.
* `KatzForms.exists_hasse_pow_mul_eq_levelRaise_sub`: Proposition 5.4 at the level `ℓ`.
* `KatzForms.discriminantPow_behrensC4`: condition (C4) for `Δᵗ`, in the shape
  `LevelOne.BehrensC4`.
-/

public section

open Gamma0 LevelOne

universe u

namespace Gamma0.IsDefinedOverPrimeField

variable {ℓ : ℕ} {L : Type*} [Field L] [DecidableEq L] {f g : Test ℓ L → L}

lemma zero : IsDefinedOverPrimeField (0 : Test ℓ L → L) := by
  rw [isDefinedOverPrimeField_iff]
  intro σ T
  simp

lemma mul (hf : IsDefinedOverPrimeField f) (hg : IsDefinedOverPrimeField g) :
    IsDefinedOverPrimeField (f * g) := by
  rw [isDefinedOverPrimeField_iff] at *
  intro σ T
  simp [hf σ T, hg σ T]

lemma sub (hf : IsDefinedOverPrimeField f) (hg : IsDefinedOverPrimeField g) :
    IsDefinedOverPrimeField (f - g) := by
  rw [isDefinedOverPrimeField_iff] at *
  intro σ T
  simp [hf σ T, hg σ T]

lemma add (hf : IsDefinedOverPrimeField f) (hg : IsDefinedOverPrimeField g) :
    IsDefinedOverPrimeField (f + g) := by
  rw [isDefinedOverPrimeField_iff] at *
  intro σ T
  simp [hf σ T, hg σ T]

lemma pow (hf : IsDefinedOverPrimeField f) (n : ℕ) : IsDefinedOverPrimeField (f ^ n) := by
  rw [isDefinedOverPrimeField_iff] at *
  intro σ T
  simp [hf σ T]

end Gamma0.IsDefinedOverPrimeField

namespace KatzForms

variable {p ℓ : ℕ} {L : Type u} [Field L] [DecidableEq L]

/-- The `q`-expansion principle, for a rule and a form. -/
lemma eq_of_qExp_eq_subtype (K : KatzForms p ℓ L) {k : ℤ} {f : Test ℓ L → L} (hf : f ∈ K.form k)
    (g : K.form k) (h : K.qExp k ⟨f, hf⟩ = K.qExp k g) : f = g.1 :=
  congrArg Subtype.val (K.qExp_injective k h)

/-- The Hasse invariant is a nonzero form. -/
lemma hasseRule_ne_zero (K : KatzForms p ℓ L) : (hasseRule p : Test ℓ L → L) ≠ 0 := by
  intro h0
  have h := K.qExp_hasse
  have h' : (⟨hasseRule p, K.hasse_mem⟩ : K.form ((p : ℤ) - 1)) = 0 := Subtype.ext h0
  rw [h', map_zero] at h
  exact zero_ne_one h

variable [Fact p.Prime]

/-- The discriminant rule is the reduction of `Δ` on `Γ₀(ℓ)` (comparison of `q`-expansions). -/
lemma discriminantRule_eq_reduce (K : KatzForms p ℓ L) :
    (discriminantRule : Test ℓ L → L) =
      (K.reduce (LevelTwoForms.ofLevelOne ℓ (discriminantPow 1))
        (PowerSeries.map (Int.castRingHom ℚ) (integralDiscriminant ^ 1))
        (PowerSeries.isPIntegral_map_intCast p _)
        (map_map_intCast_eq_qExpansion_ofLevelOne ℓ
          (isIntegralQExpansion_discriminantPow 1))).1 := by
  have h12 : (12 : ℤ) = 12 * ((1 : ℕ) : ℤ) := by norm_num
  have hD : discriminantRule ∈ K.form (12 * ((1 : ℕ) : ℤ)) := h12 ▸ K.discriminant_mem
  apply K.eq_of_qExp_eq_subtype hD
  rw [← K.qExp_congr h12 rfl K.discriminant_mem hD, K.qExp_discriminant, K.qExp_reduce]
  ext n
  simp [PowerSeries.coeff_map]

/-- The rule `Δ^{[ℓ]} = ℓ⁻¹² Δ(E / C, ω')` is the reduction of `V_ℓ Δ` (comparison of
`q`-expansions). -/
lemma veluRule_eq_reduce (K : KatzForms p ℓ L) [NeZero ℓ] (hℓ : (ℓ : L) ≠ 0) :
    (fun T : Test ℓ L ↦ ((ℓ : L) ^ 12)⁻¹ * veluDiscriminantRule T) =
      (K.reduce (LevelTwoForms.levelRaise ℓ (discriminantPow 1))
        (PowerSeries.map (Int.castRingHom ℚ) (expandSeries ℓ (integralDiscriminant ^ 1)))
        (PowerSeries.isPIntegral_map_intCast p _)
        (map_map_intCast_eq_qExpansion_levelRaise ℓ
          (isIntegralQExpansion_discriminantPow 1))).1 := by
  have h12 : (12 : ℤ) = 12 * ((1 : ℕ) : ℤ) := by norm_num
  have hfun : (fun T : Test ℓ L ↦ ((ℓ : L) ^ 12)⁻¹ * veluDiscriminantRule T) =
      ((ℓ : L) ^ 12)⁻¹ • (veluDiscriminantRule : Test ℓ L → L) := by
    funext T
    simp
  have hD12 : ((ℓ : L) ^ 12)⁻¹ • veluDiscriminantRule ∈ K.form 12 :=
    Submodule.smul_mem _ _ K.veluDiscriminant_mem
  have hD : ((ℓ : L) ^ 12)⁻¹ • veluDiscriminantRule ∈ K.form (12 * ((1 : ℕ) : ℤ)) := h12 ▸ hD12
  rw [hfun]
  apply K.eq_of_qExp_eq_subtype hD
  rw [← K.qExp_congr h12 rfl hD12 hD, K.qExp_reduce]
  have hsmul : (⟨((ℓ : L) ^ 12)⁻¹ • veluDiscriminantRule, hD12⟩ : K.form 12) =
      ((ℓ : L) ^ 12)⁻¹ • ⟨veluDiscriminantRule, K.veluDiscriminant_mem⟩ := rfl
  rw [hsmul, map_smul, K.qExp_veluDiscriminant hℓ, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ hℓ), one_smul]
  ext n
  simp only [coeff_expandSeries, PowerSeries.coeff_reduceTo, PowerSeries.coeff_map, pow_one]
  split_ifs <;> simp

lemma isDefinedOverPrimeField_discriminantRule (K : KatzForms p ℓ L) :
    IsDefinedOverPrimeField (discriminantRule : Test ℓ L → L) := by
  rw [K.discriminantRule_eq_reduce]
  exact K.reduce_isDefinedOverPrimeField _ _ _ _

lemma isDefinedOverPrimeField_veluRule (K : KatzForms p ℓ L) [NeZero ℓ] (hℓ : (ℓ : L) ≠ 0) :
    IsDefinedOverPrimeField (fun T : Test ℓ L ↦ ((ℓ : L) ^ 12)⁻¹ * veluDiscriminantRule T) := by
  rw [K.veluRule_eq_reduce hℓ]
  exact K.reduce_isDefinedOverPrimeField _ _ _ _


variable [CharP L p]

/-- The Hasse invariant rule is defined over `𝔽_p`: it is the reduction of `E_{p-1}`
(Lemma 2.1(c)). -/
lemma isDefinedOverPrimeField_hasseRule (K : KatzForms p ℓ L) (hp5 : 5 ≤ p) :
    IsDefinedOverPrimeField (hasseRule p : Test ℓ L → L) := by
  obtain ⟨E, hE, hfE, -, hEA⟩ := exists_reduce_eisenstein_eq_hasseRule K hp5 (by omega)
  have hAred : (K.reduce _ E hE hfE).1 = hasseRule p := funext hEA
  exact hAred ▸ K.reduce_isDefinedOverPrimeField _ _ _ _

omit [DecidableEq L] in
lemma natCast_ne_zero_of_prime (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) : (ℓ : L) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff L p] at h
  exact hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).1 h).symm

/-- **Proposition 5.4**, main step: with `m = (p² - 1) / 12`, the Hasse invariant divides
`L_ℓ(Δ^{r m}) = V_ℓ(Δ^{r m}) - Δ^{r m}` in the ring of Katz forms over `𝔽_p` on `Γ₀(ℓ)`. -/
theorem exists_hasse_mul_eq_levelRaise_sub
    (hGonzalezDivisionPolynomial : WeierstrassCurve.GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : WeierstrassCurve.GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : WeierstrassCurve.SupersingularJInvariant.{u})
    (hVeluIsogeny : WeierstrassCurve.VeluIsogeny.{u})
    (hDeuringHasseCriterion : WeierstrassCurve.DeuringHasseCriterion.{u})
    [IsAlgClosed L] (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (K : KatzForms p ℓ L) (Y : LevelCover K) (r : ℕ) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ∃ H ∈ K.form (12 * ((r * ((p ^ 2 - 1) / 12) : ℕ) : ℤ) - ((p : ℤ) - 1)),
      IsDefinedOverPrimeField H ∧
      (levelRaiseReduction K (discriminantPow (r * ((p ^ 2 - 1) / 12))) _
          (isIntegralQExpansion_discriminantPow _)).1 -
        (reductionAtLevel K (discriminantPow (r * ((p ^ 2 - 1) / 12))) _
          (isIntegralQExpansion_discriminantPow _)).1 = hasseRule p * H := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hp : p.Prime := Fact.out
  have hℓL : (ℓ : L) ≠ 0 := natCast_ne_zero_of_prime hℓ hℓp
  set m := (p ^ 2 - 1) / 12 with hm
  set s := r * m with hs
  set G := (levelRaiseReduction K (discriminantPow s) _
      (isIntegralQExpansion_discriminantPow _)).1 -
    (reductionAtLevel K (discriminantPow s) _ (isIntegralQExpansion_discriminantPow _)).1 with hGdef
  have hGmem : G ∈ K.form (12 * (s : ℤ)) := sub_mem (Subtype.mem _) (Subtype.mem _)
  have hGeq : G = (fun T ↦ ((ℓ : L) ^ 12)⁻¹ * veluDiscriminantRule T) ^ s -
      discriminantRule ^ s := by
    rw [hGdef, levelRaiseReduction_discriminantPow K hℓL, reductionAtLevel_discriminantPow]
  -- `G` vanishes at every supersingular test object (Theorem 1.2).
  have hGss : ∀ T : Test ℓ L, T.curve.IsSupersingularOver p → G T = 0 := by
    intro T hss
    have hc := containment_of_cited K hGonzalezDivisionPolynomial hGonzalezMultiplicationByP
      hSupersingularJInvariant hVeluIsogeny hp5 hL hℓ hℓp T hss
    rw [levelRaiseReduction_discriminantPow K hℓL, reductionAtLevel_discriminantPow] at hc
    simp only [pow_one] at hc
    have hD : discriminantRule T ≠ 0 := by
      rw [discriminantRule_apply]
      exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ T.diff.ne_zero)) T.curve.isUnit_Δ.ne_zero
    rw [hGeq, Pi.sub_apply, Pi.pow_apply, Pi.pow_apply, sub_eq_zero]
    set x := ((ℓ : L) ^ 12)⁻¹ * veluDiscriminantRule T
    have hx : x = x / discriminantRule T * discriminantRule T := (div_mul_cancel₀ _ hD).symm
    rw [hx, mul_pow, hs, mul_comm r m, pow_mul (x / _), hc, one_pow, one_mul]
  -- The Hasse invariant.
  have hE3 : 3 ≤ p - 1 := by omega
  obtain ⟨E, hE, hfE, hconst, hEA⟩ := exists_reduce_eisenstein_eq_hasseRule K hp5 hE3
  have hAgal := K.isDefinedOverPrimeField_hasseRule hp5
  have hGgal : IsDefinedOverPrimeField G := by
    rw [hGeq]
    exact ((K.isDefinedOverPrimeField_veluRule hℓL).pow s).sub
      ((K.isDefinedOverPrimeField_discriminantRule).pow s)
  -- Division on `Ȳ`.
  have ha := Y.pullback_mem K.hasse_mem
  have hg := Y.pullback_mem hGmem
  have hcusp : ∀ c, Y.ord (fun y c ↦ hasseRule p ⟨Y.pair y, c⟩) (Sum.inr c) = 0 := by
    intro c
    have := Y.ord_cusp_eq_zero (ModularForm.E hE3) E hE hfE (by rw [hconst]; exact one_ne_zero) c
    simpa only [hEA] using this
  have hle1 : ∀ y, Y.ord (fun y c ↦ hasseRule p ⟨Y.pair y, c⟩) (Sum.inl y) ≤ 1 :=
    Y.ord_hasse_le_one
  have hfin : ∀ z, Y.ord (fun y c ↦ hasseRule p ⟨Y.pair y, c⟩) z ≠ ⊤ := by
    rintro (y | c)
    · exact ne_top_of_le_ne_top ENat.one_ne_top (hle1 y)
    · rw [hcusp c]
      exact ENat.zero_ne_top
  have hle : ∀ z, Y.ord (fun y c ↦ hasseRule p ⟨Y.pair y, c⟩) z ≤
      Y.ord (fun y c ↦ G ⟨Y.pair y, c⟩) z := by
    rintro (y | c)
    · by_cases h0 : hasseRule p (⟨Y.pair y, 1⟩ : Test ℓ L) = 0
      · have hc0 : (Y.pair y).curve.hasseCoeff p = 0 := by
          rw [hasseRule_apply] at h0
          simpa using h0
        have hss := (hDeuringHasseCriterion hp (by omega) hL _).1 hc0
        have hG0 : G ⟨Y.pair y, 1⟩ = 0 := hGss _ hss
        have hpos := (Y.ord_pos_iff hg y).2 hG0
        exact (hle1 y).trans (Order.one_le_iff_pos.2 hpos)
      · have : Y.ord (fun y c ↦ hasseRule p ⟨Y.pair y, c⟩) (Sum.inl y) = 0 := by
          by_contra hne
          exact h0 ((Y.ord_pos_iff ha y).1 (pos_iff_ne_zero.2 hne))
        rw [this]
        exact zero_le
    · rw [hcusp c]
      exact zero_le
  obtain ⟨h, hh, hgh⟩ := Y.exists_eq_mul ha hg hfin hle
  -- `Q`-invariance of the quotient, by cancellation.
  have hinv : ∀ q y c, h (Y.act q y) c = h y c := by
    intro q
    have hh' := Y.act_mem hh q
    have hprod : (fun y c ↦ hasseRule p ⟨Y.pair y, c⟩) *
        ((fun y c ↦ h (Y.act q y) c) - h) = 0 := by
      funext y c
      have h1 := congrFun (congrFun hgh (Y.act q y)) c
      have h2 := congrFun (congrFun hgh y) c
      simp only [Pi.mul_apply, Y.pair_act] at h1 h2
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.zero_apply]
      rw [mul_sub, ← h1, ← h2, sub_self]
    have hd := sub_mem hh' hh
    have htop : ∀ z, Y.ord ((fun y c ↦ h (Y.act q y) c) - h) z = ⊤ := by
      intro z
      have hm := Y.ord_mul ha hd z
      rw [hprod, Y.ord_zero] at hm
      exact (WithTop.add_eq_top.1 hm.symm).resolve_left (hfin z)
    have hd0 := Y.eq_zero_of_ord_eq_top hd htop
    intro y c
    have := congrFun (congrFun hd0 y) c
    simpa [sub_eq_zero] using this
  obtain ⟨H, hH, hHeq⟩ := Y.descend hh hinv
  have hGAH : G = hasseRule p * H := by
    have key : ∀ (P : Pair ℓ L) (c : Lˣ), G ⟨P, c⟩ = hasseRule p ⟨P, c⟩ * H ⟨P, c⟩ := by
      intro P c
      obtain ⟨y, rfl⟩ := Y.exists_pair_eq P
      have := congrFun (congrFun hgh y) c
      simp only [Pi.mul_apply] at this
      rw [this, hHeq]
    funext T
    exact key T.toPair T.diff
  -- Galois invariance of the quotient, by cancellation in the domain of Katz forms.
  have hHgal : IsDefinedOverPrimeField H := by
    rw [isDefinedOverPrimeField_iff]
    intro σ T
    have hH₂ := K.galois_mem hH σ.symm
    have hprod : hasseRule p * ((fun T ↦ σ.symm (H (T.map σ.symm.symm))) - H) = 0 := by
      funext T'
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.zero_apply, RingEquiv.symm_symm, mul_sub]
      have h1 := isDefinedOverPrimeField_iff.1 hAgal σ T'
      have h2 := isDefinedOverPrimeField_iff.1 hGgal σ T'
      have h3 := congrFun hGAH (T'.map σ)
      have h4 := congrFun hGAH T'
      simp only [Pi.mul_apply] at h3 h4
      rw [← h4, sub_eq_zero]
      apply σ.injective
      rw [map_mul, RingEquiv.apply_symm_apply, ← h1, ← h3, h2]
    rcases K.eq_zero_or_eq_zero_of_mul_eq_zero K.hasse_mem (sub_mem hH₂ hH) hprod with h | h
    · exact absurd h K.hasseRule_ne_zero
    · have := congrFun h T
      simp only [Pi.sub_apply, Pi.zero_apply, RingEquiv.symm_symm, sub_eq_zero] at this
      rw [← this, RingEquiv.apply_symm_apply]
  exact ⟨H, hH, hHgal, hGAH⟩

/-- **Proposition 5.4** (divisibility at every level). Let `p ≥ 5`, `L` an algebraic closure of
`𝔽_p`, `ℓ ≠ p` a prime, `p ∤ r`, `t = r pⁿ (p² - 1) / 12` and `1 ≤ j ≤ pⁿ`. Then
`A_p^j ∣ L_ℓ(Δᵗ)` in the ring of Katz forms modulo `p` on `Γ₀(ℓ)`: `V_ℓ(Δᵗ) - Δᵗ = A_p^j H` for
a form `H` over `𝔽_p` of weight `12t - j (p - 1)` (the shape of `LevelOne.BehrensC4` at the
level `ℓ`). -/
theorem exists_hasse_pow_mul_eq_levelRaise_sub
    (hGonzalezDivisionPolynomial : WeierstrassCurve.GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : WeierstrassCurve.GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : WeierstrassCurve.SupersingularJInvariant.{u})
    (hVeluIsogeny : WeierstrassCurve.VeluIsogeny.{u})
    (hDeuringHasseCriterion : WeierstrassCurve.DeuringHasseCriterion.{u})
    [IsAlgClosed L] (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (K : KatzForms p ℓ L) (Y : LevelCover K) {r n j t : ℕ}
    (_hr : ¬ p ∣ r) (ht : t = r * p ^ n * ((p ^ 2 - 1) / 12)) (_hj1 : 1 ≤ j) (hjn : j ≤ p ^ n) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ∃ H ∈ K.form (12 * (t : ℤ) - j * ((p : ℤ) - 1)), IsDefinedOverPrimeField H ∧
      (levelRaiseReduction K (discriminantPow t) _ (isIntegralQExpansion_discriminantPow t)).1 -
        (reductionAtLevel K (discriminantPow t) _ (isIntegralQExpansion_discriminantPow t)).1 =
          hasseRule p ^ j * H := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hℓL : (ℓ : L) ≠ 0 := natCast_ne_zero_of_prime hℓ hℓp
  obtain ⟨H, hH, hHgal, hGH⟩ := exists_hasse_mul_eq_levelRaise_sub hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hSupersingularJInvariant hVeluIsogeny hDeuringHasseCriterion
    hp5 hL hℓ hℓp K Y r
  set s := r * ((p ^ 2 - 1) / 12) with hs
  have hts : t = s * p ^ n := by rw [ht, hs]; ring
  clear_value s
  -- Freshman's dream: `L_ℓ(Δᵗ) = L_ℓ(Δˢ) ^ (pⁿ)`.
  have hfresh :
      (levelRaiseReduction K (discriminantPow t) _ (isIntegralQExpansion_discriminantPow t)).1 -
        (reductionAtLevel K (discriminantPow t) _ (isIntegralQExpansion_discriminantPow t)).1 =
      ((levelRaiseReduction K (discriminantPow s) _ (isIntegralQExpansion_discriminantPow s)).1 -
        (reductionAtLevel K (discriminantPow s) _ (isIntegralQExpansion_discriminantPow s)).1) ^
          p ^ n := by
    simp only [levelRaiseReduction_discriminantPow K hℓL, reductionAtLevel_discriminantPow]
    funext T
    simp only [Pi.sub_apply, Pi.pow_apply]
    rw [hts, pow_mul _ s, pow_mul _ s, sub_pow_char_pow]
  refine ⟨hasseRule p ^ (p ^ n - j) * H ^ (p ^ n), ?_, ?_, ?_⟩
  · refine K.mem_form_of_eq ?_ (K.mul_mem (K.pow_mem K.hasse_mem _) (K.pow_mem hH _))
    rw [hts]
    push_cast [Nat.cast_sub hjn]
    ring
  · exact ((K.isDefinedOverPrimeField_hasseRule hp5).pow _).mul (hHgal.pow _)
  · rw [hfresh, hGH, mul_pow, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hjn]

/-- **Condition (C4) for `Δᵗ`** (Proposition 5.4 at every level): for `p ≥ 5`, `p ∤ r`,
`t = r pⁿ (p² - 1) / 12` and `1 ≤ j ≤ pⁿ`, the form `Δᵗ` satisfies Behrens' condition (C4) for
the index `j`, given the Katz forms `K ℓ` and level covers `Y ℓ` at every prime `ℓ ≠ p`. -/
theorem discriminantPow_behrensC4
    (hGonzalezDivisionPolynomial : WeierstrassCurve.GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : WeierstrassCurve.GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : WeierstrassCurve.SupersingularJInvariant.{u})
    (hVeluIsogeny : WeierstrassCurve.VeluIsogeny.{u})
    (hDeuringHasseCriterion : WeierstrassCurve.DeuringHasseCriterion.{u})
    [IsAlgClosed L] (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (K : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → KatzForms p ℓ L)
    (Y : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p), LevelCover (K ℓ hℓ hℓp)) {r n j : ℕ}
    (hr : ¬ p ∣ r) (hj1 : 1 ≤ j) (hjn : j ≤ p ^ n) :
    BehrensC4 K (r * p ^ n * ((p ^ 2 - 1) / 12)) j (discriminantPow _) _
      (isIntegralQExpansion_discriminantPow _) := by
  rw [behrensC4_iff]
  intro ℓ hℓ hℓp
  exact exists_hasse_pow_mul_eq_levelRaise_sub hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hSupersingularJInvariant hVeluIsogeny hDeuringHasseCriterion
    hp5 hL hℓ hℓp (K ℓ hℓ hℓp) (Y ℓ hℓ hℓp) hr rfl hj1
    hjn

end KatzForms
