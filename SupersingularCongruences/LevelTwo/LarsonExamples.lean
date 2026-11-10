/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.LevelTwo.HasseLevelTwo
public import SupersingularCongruences.LevelTwo.Examples
import all SupersingularCongruences.LevelTwo.Examples
import all SupersingularCongruences.LevelTwo.LarsonRing

/-!
# Remark 3.1: Larson's factorizations at `p = 11, 13` and the elliptic point

Proposition 3.4 recovers, up to units, Larson's factorizations of the Hasse invariant in
`𝔽_p[δ, ε]` [larson2020, Section 5]:

* `KatzForms.hasse_eq_C_mul_hasseElevenLevelTwo`: at `p = 11`, `P_A = u · δ (μ + 3ε) (μ + 4ε)`
  (`LevelTwo.hasseElevenLevelTwo`) for a unit `u ∈ 𝔽₁₁ˣ`;
* `KatzForms.hasse_eq_C_mul_hasseThirteenLevelTwo`: at `p = 13`,
  `P_A = u · (μ + 12ε) (μ² + 5με + ε²)` (`LevelTwo.hasseThirteenLevelTwo`);
* `KatzForms.isSupersingularOver_iff_of_xCoordinate_eq_neg_one`: the elliptic point `x = -1` of
  `X₀(2)` (the curve `j = 1728` with the subgroup fixed by `[i]`) is supersingular iff
  `p ≡ 3 (mod 4)`.

Here `P_A` is any weighted homogeneous polynomial of weight `p - 1` with `A_p = P_A(δ̄, ε̄)`
(eq. (3.1), `KatzForms.exists_hasseRule_eq_aeval`).

## Proof route

Both `P_A` and Larson's polynomial `Q` are weighted homogeneous of weight `p - 1`; on the Legendre
family (`δ̄ ↦ c (λ + 1)`, `ε̄ ↦ 4 c² λ`) both become multiples of the Deuring polynomial `H_p(λ)`
(for `Q` this is the explicit identity
`H₁₁ ≡ (λ + 1)(λ² + 10λ + 1)(λ² + 14λ + 1) (mod 11)`, resp.
`H₁₃ ≡ (λ² + 7λ + 1)(λ⁴ + 16λ³ - 18λ² + 16λ + 1) (mod 13)`), and a weighted homogeneous
polynomial vanishing on the Legendre family is zero (`LevelTwo.eq_zero_of_aeval_legendre_eq_zero`).
The unit is the value of `P_A` at `(δ, ε) = (1, 0)` (where `Q = 1`). The elliptic point is the
last clause of Proposition 3.4: `x = -1` is a supersingular value iff `α_p = 1`.
-/

public section

open MvPolynomial Gamma0 LevelTwo

universe u

namespace KatzForms

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [DecidableEq L] [CharP L p]
  (K : KatzForms p 2 L) (hp2 : p ≠ 2)

/-- **Comparison with an explicit polynomial**: if `Q ∈ 𝔽_p[δ, ε]` is weighted homogeneous of
weight `p - 1` with `Q(1, 0) = 1` and, on the Legendre family `δ ↦ c (λ + 1)`, `ε ↦ 4 c² λ`
(`c ≠ 0`), `Q` becomes a nonzero multiple of `H_p(λ)`, then `P_A = u Q` for a unit `u`. -/
theorem hasse_eq_C_mul_of_legendre [IsAlgClosed L] (hp5 : 5 ≤ p) (hK : K.LegendreRegular)
    {PA : MvPolynomial (Fin 2) (ZMod p)} (hw : PA.IsWeightedHomogeneous ![2, 4] (p - 1))
    (hPA : aeval ![(K.deltaBar hp2).1, (K.epsBar hp2).1]
      (map (ZMod.castHom (dvd_refl p) L) PA) = hasseRule p)
    {Q : MvPolynomial (Fin 2) (ZMod p)} (hQw : Q.IsWeightedHomogeneous ![2, 4] (p - 1))
    (hQ10 : eval ![1, 0] Q = 1)
    (hQleg : ∀ c : L, c ≠ 0 → ∃ κ' : L, κ' ≠ 0 ∧
      aeval ![Polynomial.C c * (Polynomial.X + 1), Polynomial.C (4 * c ^ 2) * Polynomial.X]
        (map (ZMod.castHom (dvd_refl p) L) Q) =
          Polynomial.C κ' * Polynomial.deuringPolynomial L p) :
    ∃ u : (ZMod p)ˣ, PA = C (u : ZMod p) * Q := by
  obtain ⟨h2, h3⟩ := two_three_ne_zero (L := L) hp5
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨ζ, c, hcζ, hζ, hv⟩ := K.exists_legendre_values hp2 h2 h3 hK
  have hc : c ≠ 0 := by
    rintro rfl
    rw [← hcζ] at hζ
    norm_num at hζ
  have hPH := K.aeval_legendre_eq_hasse hp2 h2 h3 hv hPA
  obtain ⟨κ', hκ', hQH⟩ := hQleg c hc
  set φ := ZMod.castHom (dvd_refl p) L
  set κ : L := (-1) ^ ((p - 1) / 2)
  have hκ : κ ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  set k : L := κ / κ'
  have hR : map φ PA - C k * map φ Q = 0 := by
    have hRw : (map φ PA - C k * map φ Q).IsWeightedHomogeneous ![2, 4]
        (2 * (2 * hasseS p + hasseAlpha p)) := by
      rw [← sub_one_eq_two_mul p hodd]
      refine (isWeightedHomogeneous_map φ hw).sub ?_
      simpa using (isWeightedHomogeneous_C ![2, 4] k).mul (isWeightedHomogeneous_map φ hQw)
    refine eq_zero_of_aeval_legendre_eq_zero h2 (hasseAlpha_le_one p) hRw hc hcζ ?_
    rw [map_sub, map_mul, aeval_C, hPH, ← hcζ, hQH, Polynomial.algebraMap_eq, ← mul_assoc,
      ← Polynomial.C_mul, div_mul_cancel₀ _ hκ', sub_self]
  rw [sub_eq_zero] at hR
  set a : ZMod p := eval ![1, 0] PA
  have hka : φ a = k := by
    have h1 := congrArg (eval ![(1 : L), 0]) hR
    rw [map_mul, eval_C] at h1
    have e1 := castHom_eval (L := L) PA 1 0
    have e2 := castHom_eval (L := L) Q 1 0
    rw [hQ10, map_one, map_zero] at e2
    rw [map_one, map_zero] at e1
    rw [e1, h1, ← e2, mul_one]
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hka
    exact div_ne_zero hκ hκ' hka.symm
  refine ⟨Units.mk0 a ha, MvPolynomial.map_injective φ φ.injective ?_⟩
  rw [hR, Units.val_mk0, map_mul, map_C, hka]

end KatzForms

namespace LevelTwo

variable {R : Type*} [Field R]

lemma isWeightedHomogeneous_delta : (delta R).IsWeightedHomogeneous ![2, 4] 2 :=
  isWeightedHomogeneous_X R _ 0

lemma isWeightedHomogeneous_eps : (eps R).IsWeightedHomogeneous ![2, 4] 4 :=
  isWeightedHomogeneous_X R _ 1

lemma isWeightedHomogeneous_mu : (mu R).IsWeightedHomogeneous ![2, 4] 4 := by
  rw [mu_def]
  exact (by simpa [sq] using isWeightedHomogeneous_delta.mul isWeightedHomogeneous_delta :
    (delta R ^ 2).IsWeightedHomogeneous ![2, 4] 4).sub isWeightedHomogeneous_eps

lemma isWeightedHomogeneous_ofNat_mul {f : MvPolynomial (Fin 2) R} {n : ℕ}
    (hf : f.IsWeightedHomogeneous ![2, 4] n) (a : ℕ) [a.AtLeastTwo] :
    ((OfNat.ofNat a : MvPolynomial (Fin 2) R) * f).IsWeightedHomogeneous ![2, 4] n := by
  rw [← map_ofNat C a]
  simpa using (isWeightedHomogeneous_C ![2, 4] (OfNat.ofNat a : R)).mul hf

/-- Larson's `δ (μ + 3ε) (μ + 4ε)` is weighted homogeneous of weight `10`. -/
lemma isWeightedHomogeneous_hasseElevenLevelTwo :
    hasseElevenLevelTwo.IsWeightedHomogeneous ![2, 4] 10 := by
  rw [hasseElevenLevelTwo]
  have h3 := isWeightedHomogeneous_mu.add (isWeightedHomogeneous_ofNat_mul
    (R := ZMod 11) isWeightedHomogeneous_eps 3)
  have h4 := isWeightedHomogeneous_mu.add (isWeightedHomogeneous_ofNat_mul
    (R := ZMod 11) isWeightedHomogeneous_eps 4)
  exact (isWeightedHomogeneous_delta.mul h3).mul h4

/-- Larson's `(μ + 12ε) (μ² + 5με + ε²)` is weighted homogeneous of weight `12`. -/
lemma isWeightedHomogeneous_hasseThirteenLevelTwo :
    hasseThirteenLevelTwo.IsWeightedHomogeneous ![2, 4] 12 := by
  rw [hasseThirteenLevelTwo]
  have h1 := isWeightedHomogeneous_mu.add (isWeightedHomogeneous_ofNat_mul
    (R := ZMod 13) isWeightedHomogeneous_eps 12)
  have hmm := isWeightedHomogeneous_mu (R := ZMod 13)
  have he := isWeightedHomogeneous_eps (R := ZMod 13)
  have h2 : (mu (ZMod 13) ^ 2 + 5 * mu (ZMod 13) * eps (ZMod 13) + eps (ZMod 13) ^ 2
      ).IsWeightedHomogeneous ![2, 4] 8 := by
    refine (IsWeightedHomogeneous.add ?_ ?_).add ?_
    · simpa [sq] using hmm.mul hmm
    · simpa [mul_assoc] using isWeightedHomogeneous_ofNat_mul (hmm.mul he) 5
    · simpa [sq] using he.mul he
  exact h1.mul h2

lemma eval_one_zero_hasseElevenLevelTwo : eval ![1, 0] hasseElevenLevelTwo = 1 := by
  simp [hasseElevenLevelTwo]

lemma eval_one_zero_hasseThirteenLevelTwo : eval ![1, 0] hasseThirteenLevelTwo = 1 := by
  simp [hasseThirteenLevelTwo]

/-- On the Legendre family,
`δ (μ + 3ε) (μ + 4ε) ↦ c⁵ (λ + 1)(λ² + 10λ + 1)(λ² + 14λ + 1) = c⁵ H₁₁(λ)`
in characteristic `11`. -/
lemma aeval_legendre_hasseElevenLevelTwo {L : Type*} [Field L] [CharP L 11] [Infinite L] (c : L) :
    aeval ![Polynomial.C c * (Polynomial.X + 1), Polynomial.C (4 * c ^ 2) * Polynomial.X]
      (map (ZMod.castHom (dvd_refl 11) L) hasseElevenLevelTwo) =
      Polynomial.C (c ^ 5) * Polynomial.deuringPolynomial L 11 := by
  have h11 : (11 : L) = 0 := by exact_mod_cast CharP.cast_eq_zero L 11
  refine Polynomial.funext fun x => ?_
  rw [eval_aeval_polynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_deuringPolynomial]
  simp [hasseElevenLevelTwo, map_delta, map_mu, map_eps, Finset.sum_range_succ, Nat.choose]
  linear_combination (6 * c ^ 5 * x ^ 2 * (x + 1)) * h11

/-- On the Legendre family, `(μ + 12ε)(μ² + 5με + ε²) ↦ c⁶ H₁₃(λ)` in characteristic `13`. -/
lemma aeval_legendre_hasseThirteenLevelTwo {L : Type*} [Field L] [CharP L 13] [Infinite L]
    (c : L) :
    aeval ![Polynomial.C c * (Polynomial.X + 1), Polynomial.C (4 * c ^ 2) * Polynomial.X]
      (map (ZMod.castHom (dvd_refl 13) L) hasseThirteenLevelTwo) =
      Polynomial.C (c ^ 6) * Polynomial.deuringPolynomial L 13 := by
  have h13 : (13 : L) = 0 := by exact_mod_cast CharP.cast_eq_zero L 13
  refine Polynomial.funext fun x => ?_
  rw [eval_aeval_polynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_deuringPolynomial]
  simp [hasseThirteenLevelTwo, map_mu, map_eps, Finset.sum_range_succ, Nat.choose]
  linear_combination (2 * c ^ 6 * x * (x ^ 4 + 19 * x ^ 3 - 46 * x ^ 2 + 19 * x + 1)) * h13

end LevelTwo

namespace KatzForms

variable {L : Type u} [Field L] [DecidableEq L] [IsAlgClosed L]

/-- **Remark 3.1** (`p = 11`): the polynomial `P_A` of eq. (3.1) is a unit multiple of Larson's
`A₁₁ = δ (μ + 3ε) (μ + 4ε)` [larson2020, eq. (5.4)]. -/
theorem hasse_eq_C_mul_hasseElevenLevelTwo [CharP L 11] (K : KatzForms 11 2 L)
    (hK : K.LegendreRegular) {PA : MvPolynomial (Fin 2) (ZMod 11)}
    (hw : PA.IsWeightedHomogeneous ![2, 4] (11 - 1))
    (hPA : aeval ![(K.deltaBar (by decide)).1, (K.epsBar (by decide)).1]
      (map (ZMod.castHom (dvd_refl 11) L) PA) = hasseRule 11) :
    ∃ u : (ZMod 11)ˣ, PA = C (u : ZMod 11) * hasseElevenLevelTwo :=
  K.hasse_eq_C_mul_of_legendre (by decide) (by norm_num) hK hw hPA
    isWeightedHomogeneous_hasseElevenLevelTwo eval_one_zero_hasseElevenLevelTwo
    fun c hc => ⟨c ^ 5, pow_ne_zero _ hc, aeval_legendre_hasseElevenLevelTwo c⟩

/-- **Remark 3.1** (`p = 13`): the polynomial `P_A` of eq. (3.1) is a unit multiple of Larson's
`A₁₃ = (μ + 12ε)(μ² + 5με + ε²)` [larson2020, eq. (5.14)]. -/
theorem hasse_eq_C_mul_hasseThirteenLevelTwo [CharP L 13] (K : KatzForms 13 2 L)
    (hK : K.LegendreRegular) {PA : MvPolynomial (Fin 2) (ZMod 13)}
    (hw : PA.IsWeightedHomogeneous ![2, 4] (13 - 1))
    (hPA : aeval ![(K.deltaBar (by decide)).1, (K.epsBar (by decide)).1]
      (map (ZMod.castHom (dvd_refl 13) L) PA) = hasseRule 13) :
    ∃ u : (ZMod 13)ˣ, PA = C (u : ZMod 13) * hasseThirteenLevelTwo :=
  K.hasse_eq_C_mul_of_legendre (by decide) (by norm_num) hK hw hPA
    isWeightedHomogeneous_hasseThirteenLevelTwo eval_one_zero_hasseThirteenLevelTwo
    fun c hc => ⟨c ^ 6, pow_ne_zero _ hc, aeval_legendre_hasseThirteenLevelTwo c⟩

variable {p : ℕ} [Fact p.Prime] [CharP L p]

/-- **Remark 3.1** (the elliptic point): the point `x = -1` of `X₀(2)` (the curve `j = 1728` with
the subgroup fixed by `[i]`, `Gamma0.Pair.xCoordinate_eq_neg_one_iff`) is supersingular iff
`p ≡ 3 (mod 4)` (from Proposition 3.4: `x = -1` is a supersingular value iff `α_p = 1`). -/
theorem isSupersingularOver_iff_of_xCoordinate_eq_neg_one
    (hDeuringHasseCriterion : WeierstrassCurve.DeuringHasseCriterion.{u})
    (hDeuringPolynomialSeparable : Polynomial.DeuringPolynomialSeparable.{u})
    (hLarsonLevelTwoStructure : LevelTwoForms.LarsonLevelTwoStructure)
    (K : KatzForms p 2 L) (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (hK : K.LegendreRegular) (P : Pair 2 L)
    (hx : P.xCoordinate = -1) : P.curve.IsSupersingularOver p ↔ p % 4 = 3 := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨h2, h3⟩ := two_three_ne_zero (L := L) hp5
  obtain ⟨PA, hw, hPA⟩ := K.exists_hasseRule_eq_aeval hp2 hLarsonLevelTwoStructure hp5
  obtain ⟨c', ξ, -, -, -, hξ, -, -, hss⟩ := K.hasse_factorization hp2 hDeuringHasseCriterion
    hDeuringPolynomialSeparable hp5 hL hK hw hPA
  have hα : hasseAlpha p = 1 ↔ p % 4 = 3 := by
    rw [hasseAlpha_def]; split_ifs with h <;> simp [h]
  rw [← hα]
  constructor
  · intro h
    have hmem : (-1 : L) ∈ {x | ∃ P : Pair 2 L, P.curve.IsSupersingularOver p ∧
        P.xCoordinate = x} := ⟨P, h, hx⟩
    rw [hss] at hmem
    rcases hmem with ⟨i, hi⟩ | ⟨h1, -⟩
    · exact absurd hi (hξ i).2
    · exact h1
  · intro h1
    have hmem : (-1 : L) ∈ Set.range ξ ∪ {x | hasseAlpha p = 1 ∧ x = -1} := Or.inr ⟨h1, rfl⟩
    rw [← hss] at hmem
    obtain ⟨Q, hQ, hQx⟩ := hmem
    obtain ⟨u, hu⟩ := (Pair.xCoordinate_eq_iff h2 h3 P Q).mp (hx.trans hQx.symm)
    have hT : hasseRule p ((⟨P, 1⟩ : Test 2 L).scale u) = 0 := by
      rw [hasseRule_eq_zero_iff hDeuringHasseCriterion hp hp2 hL, test_scale_curve]
      change ((P.scale u).curve).IsSupersingularOver p
      rw [hu]; exact hQ
    rw [K.apply_scale K.hasse_mem, hasseRule_eq_zero_iff hDeuringHasseCriterion hp hp2 hL] at hT
    exact hT

end KatzForms
