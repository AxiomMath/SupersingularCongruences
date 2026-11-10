/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.KatzForms.Reduction
public import SupersingularCongruences.ModularCurve.Legendre
import all SupersingularCongruences.ModularCurve.Legendre

/-!
# The Hasse invariant in the Katz model (manuscript, Lemma 2.1)

Let `p ≥ 5` and let `L` be an algebraic closure of `𝔽_p`. The Hasse invariant `A_p` is the Katz
form `Gamma0.hasseRule p` of weight `p - 1`; by `KatzForms.exists_reduce_eisenstein_eq_hasseRule`
it is the reduction of `E_{p-1}` (Lemma 2.1(c)). This file proves the remaining parts of
Lemma 2.1 in this model:

* (a) `Gamma0.hasseRule_eq_zero_iff`: `A_p(E, C, ω) = 0` iff `E` is supersingular (from the cited
  criterion `WeierstrassCurve.DeuringHasseCriterion` [silverman-aec, Theorem V.4.1(a)]);
* (c) `Gamma0.hasseRule_smulDiff_two`: the values at `dx / y` and `dx / (2y)` agree, as
  `2^{p-1} = 1` in characteristic `p`;
* (b) `LevelOne.eisenstein_slash_eq`, `LevelOne.qExpansion_eisenstein_slash`,
  `LevelOne.coeff_zero_qExpansion_eisenstein_slash`: `E_{p-1} ∣ γ = E_{p-1}` for all
  `γ ∈ SL(2, ℤ)`, so the expansion of `E_{p-1}` at every cusp is its `q`-expansion, which is
  `p`-integral with constant term `1` and reduction `1`;
* (e) `Gamma0.legendreCurve_hasseCoeff`: the Hasse invariant of the short model of the Legendre
  curve is `(-1)^{(p-1)/2} H_p(λ)` (the translation `x ↦ x + (1 + λ) / 3` does not change the
  coefficient of `x^{p-1}`; `Polynomial.coeff_taylor_sub_one`), hence
  `Gamma0.deuringPolynomial_isRoot_iff`: the roots of `H_p` in `L` are exactly the supersingular
  Legendre parameters, and `H_p` is separable (cited: `Polynomial.DeuringPolynomialSeparable`
  [silverman-aec, Theorem V.4.1(c)], [igusa1958]).
-/

public section

open Polynomial WeierstrassCurve
open scoped ModularForm MatrixGroups

universe u

/-! ### Translation invariance of the coefficient of `x^{p-1}` -/

namespace Nat

/-- For a prime `p` and `1 ≤ i < p`, `p ∣ binom(i + (p - 1), p - 1)`. -/
lemma Prime.dvd_choose_add_sub_one {p i : ℕ} (hp : p.Prime) (hi0 : 1 ≤ i) (hip : i < p) :
    p ∣ (i + (p - 1)).choose (p - 1) := by
  have hk : p - 1 ≤ i + (p - 1) := Nat.le_add_left _ _
  have h := Nat.choose_mul_factorial_mul_factorial hk
  rw [Nat.add_sub_cancel] at h
  have hdvd : p ∣ (i + (p - 1)).factorial :=
    (hp.dvd_factorial).mpr (by have := hp.one_le; omega)
  rw [← h] at hdvd
  rcases (hp.dvd_mul).mp hdvd with h1 | h1
  · rcases (hp.dvd_mul).mp h1 with h2 | h2
    · exact h2
    · exact absurd ((hp.dvd_factorial).mp h2) (by omega)
  · exact absurd ((hp.dvd_factorial).mp h1) (by omega)

end Nat

namespace Polynomial

variable {R : Type*} [CommRing R] {p : ℕ} [CharP R p]

/-- In characteristic `p`, the coefficient of `X^{p-1}` of a polynomial of degree `< 2p - 1` is
invariant under translation `X ↦ X + c`. -/
theorem coeff_taylor_sub_one (hp : p.Prime) {h : R[X]} (hdeg : h.natDegree < 2 * p - 1) (c : R) :
    (taylor c h).coeff (p - 1) = h.coeff (p - 1) := by
  rw [taylor_coeff, eval_eq_sum_range' (n := p)]
  · rw [Finset.sum_eq_single 0]
    · simp [hasseDeriv_coeff]
    · intro i hi hi0
      rw [Finset.mem_range] at hi
      rw [hasseDeriv_coeff, (CharP.cast_eq_zero_iff R p _).mpr
        (hp.dvd_choose_add_sub_one (Nat.one_le_iff_ne_zero.mpr hi0) hi)]
      ring
    · intro h0
      exact absurd (Finset.mem_range.mpr hp.pos) h0
  · have := natDegree_hasseDeriv_le h (p - 1)
    omega

end Polynomial

/-! ### The Legendre family -/

namespace Gamma0

section LegendreCoefficients

variable {L : Type*} [Field L]

lemma legendreCurve_a₄ (lam : L) : (legendreCurve lam).a₄ = -(lam ^ 2 - lam + 1) / 3 := by
  rw [legendreCurve]

lemma legendreCurve_a₆ (lam : L) :
    (legendreCurve lam).a₆ = -((lam - 2) * (lam + 1) * (2 * lam - 1)) / 27 := by
  rw [legendreCurve]

end LegendreCoefficients

variable {L : Type u} [Field L]

/-- The cubic of the short model of the Legendre curve is `f(x + (1 + λ) / 3)` for
`f = x (x - 1) (x - λ)`. -/
lemma legendreCurve_cubic_eq (h3 : (3 : L) ≠ 0) (lam : L) :
    X ^ 3 + C (legendreCurve lam).a₄ * X + C (legendreCurve lam).a₆ =
      (X * (X - 1) * (X - C lam)).comp (X + C ((1 + lam) / 3)) := by
  set c : L := (1 + lam) / 3 with hc
  have hc3 : 3 * c = 1 + lam := by rw [hc]; field_simp
  have ha4 : (legendreCurve lam).a₄ = 3 * c ^ 2 - 2 * (1 + lam) * c + lam := by
    rw [legendreCurve_a₄, hc]; field_simp; ring
  have ha6 : (legendreCurve lam).a₆ = c ^ 3 - (1 + lam) * c ^ 2 + lam * c := by
    rw [legendreCurve_a₆, hc]
    have h27 : (27 : L) ≠ 0 := by
      rw [show (27 : L) = 3 ^ 3 by norm_num]; exact pow_ne_zero _ h3
    field_simp
    ring
  have hC : 3 * C c = 1 + C lam := by
    rw [← C_1, ← C_add, ← hc3, C_mul]; rfl
  simp only [mul_comp, sub_comp, X_comp, C_comp, one_comp, ha4, ha6, C_add, C_sub, C_mul,
    C_pow, C_1]
  rw [show (C (3 : L)) = 3 from rfl, show (C (2 : L)) = 2 from rfl]
  linear_combination (-(X : L[X]) ^ 2) * hC

/-- **Lemma 2.1(d)** for the short model: the Hasse invariant of `legendreCurve λ` at `dx / (2y)`
is `(-1)^{(p-1)/2} H_p(λ)`. -/
theorem legendreCurve_hasseCoeff {p : ℕ} [CharP L p] (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : (3 : L) ≠ 0) (lam : L) :
    (legendreCurve lam).hasseCoeff p = (-1) ^ ((p - 1) / 2) * (deuringPolynomial L p).eval lam := by
  rw [hasseCoeff_def, legendreCurve_cubic_eq h3, ← pow_comp, ← taylor_apply,
    coeff_taylor_sub_one hp, coeff_legendre_pow_eq_deuringPolynomial (hp.odd_of_ne_two hp2)]
  calc ((X * (X - 1) * (X - C lam)) ^ ((p - 1) / 2)).natDegree
      ≤ (p - 1) / 2 * (X * (X - 1) * (X - C lam) : L[X]).natDegree := natDegree_pow_le
    _ ≤ (p - 1) / 2 * 3 := by
        gcongr
        refine (natDegree_mul_le).trans ?_
        refine (add_le_add (natDegree_mul_le) (natDegree_X_sub_C_le lam)).trans ?_
        have h1 : (X - 1 : L[X]).natDegree ≤ 1 := by
          rw [← C_1]; exact natDegree_X_sub_C_le 1
        have h2 : (X : L[X]).natDegree ≤ 1 := natDegree_X_le
        omega
    _ < 2 * p - 1 := by have := hp.two_le; omega

/-- **Lemma 2.1(e)**, separability (cited [silverman-aec, Theorem V.4.1(c)], [igusa1958]). -/
theorem deuringPolynomial_separable (hDeuringPolynomialSeparable : DeuringPolynomialSeparable.{u})
    {p : ℕ} [CharP L p] (hp : p.Prime) (hp2 : p ≠ 2) :
    (deuringPolynomial L p).Separable :=
  hDeuringPolynomialSeparable hp hp2

/-- In characteristic `p`, `2^{p-1} = 1` (for `p ≠ 2`). -/
lemma two_pow_sub_one_eq_one {p : ℕ} [CharP L p] (hp : p.Prime) (h2 : (2 : L) ≠ 0) :
    (2 : L) ^ (p - 1) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h : (2 : L) ^ p = 2 := by
    have := map_natCast (frobenius L p) 2
    rw [frobenius_def] at this
    exact_mod_cast this
  have hp1 : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.one_le).symm
  rw [hp1, pow_succ] at h
  exact (mul_left_eq_self₀.mp h).resolve_right h2

variable [DecidableEq L]

/-- **Lemma 2.1(e)**, pointwise: for `λ ≠ 0, 1` in `L = 𝔽̄_p`, `H_p(λ) = 0` iff the Legendre curve
`E_λ` is supersingular. -/
theorem deuringPolynomial_eval_eq_zero_iff (hDeuringHasseCriterion : DeuringHasseCriterion.{u})
    [IsAlgClosed L] {p : ℕ} [CharP L p] (hp : p.Prime)
    (hp5 : 5 ≤ p) (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) {lam : L} (h0 : lam ≠ 0)
    (h1 : lam ≠ 1) :
    (deuringPolynomial L p).eval lam = 0 ↔ (legendreCurve lam).IsSupersingularOver p := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : L) ≠ 0 := by
    rw [show (2 : L) = ((2 : ℕ) : L) by norm_num, ne_eq, CharP.cast_eq_zero_iff L p]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have h3 : (3 : L) ≠ 0 := by
    rw [show (3 : L) = ((3 : ℕ) : L) by norm_num, ne_eq, CharP.cast_eq_zero_iff L p]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have : (legendreCurve lam).IsElliptic := ⟨isUnit_legendreCurve_Δ h2 h3 h0 h1⟩
  rw [← hDeuringHasseCriterion hp hp2 hL, legendreCurve_hasseCoeff hp hp2 h3,
    mul_eq_zero, or_iff_right (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))]

/-- **Lemma 2.1(e)**: the roots of `H_p` in `L = 𝔽̄_p` are exactly the supersingular values of
`λ` (which are automatically `≠ 0, 1`). The separability of `H_p`, the other half of
Lemma 2.1(e), is the cited `deuringPolynomial_separable`; it is not used here. -/
theorem deuringPolynomial_isRoot_iff (hDeuringHasseCriterion : DeuringHasseCriterion.{u})
    [IsAlgClosed L] {p : ℕ} [CharP L p] (hp : p.Prime)
    (hp5 : 5 ≤ p) (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (lam : L) :
    (deuringPolynomial L p).IsRoot lam ↔
      lam ≠ 0 ∧ lam ≠ 1 ∧ (legendreCurve lam).IsSupersingularOver p := by
  have hp2 : p ≠ 2 := by omega
  constructor
  · intro h
    have h0 : lam ≠ 0 := by
      rintro rfl
      rw [IsRoot, deuringPolynomial_eval_zero] at h
      exact one_ne_zero h
    have h1 : lam ≠ 1 := by
      rintro rfl
      exact deuringPolynomial_eval_one_ne_zero hp hp2 h
    exact ⟨h0, h1, (deuringPolynomial_eval_eq_zero_iff hDeuringHasseCriterion hp hp5 hL h0 h1).mp h⟩
  · rintro ⟨h0, h1, hss⟩
    exact (deuringPolynomial_eval_eq_zero_iff hDeuringHasseCriterion hp hp5 hL h0 h1).mpr hss

/-! ### Lemma 2.1(a) and (c) for the rule `hasseRule` -/

variable {ℓ : ℕ}

/-- **Lemma 2.1(a)**: `A_p(E, C, ω) = 0` iff `E` is supersingular. -/
theorem hasseRule_eq_zero_iff (hDeuringHasseCriterion : DeuringHasseCriterion.{u})
    [IsAlgClosed L] {p : ℕ} [CharP L p] (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (T : Test ℓ L) :
    hasseRule p T = 0 ↔ T.curve.IsSupersingularOver p := by
  rw [hasseRule_apply, mul_eq_zero,
    or_iff_right (inv_ne_zero (pow_ne_zero _ T.diff.ne_zero)),
    hDeuringHasseCriterion hp hp2 hL]

/-- **Lemma 2.1(c)**, second sentence: the values of `A_p` at `(E, C, dx / y)` and
`(E, C, dx / (2y))` agree, since `A_p` has weight `p - 1` and `2^{p-1} = 1`. Here `dx / y` is the
differential `2 · (dx / (2y))`, i.e. the test object `T.smulDiff 2`. -/
theorem hasseRule_smulDiff_two {p : ℕ} [CharP L p] (hp : p.Prime) (h2 : (2 : L) ≠ 0)
    (T : Test ℓ L) : hasseRule p (T.smulDiff (Units.mk0 2 h2)) = hasseRule p T := by
  rw [hasseRule_apply, hasseRule_apply, Test.smulDiff_diff, Test.smulDiff_toPair, Units.val_mul,
    Units.val_mk0, mul_pow, two_pow_sub_one_eq_one hp h2, one_mul]

end Gamma0

/-! ### Lemma 2.1(b): `E_{p-1}` at the cusps -/

namespace LevelOne

variable {p : ℕ}

/-- `E_{p-1} ∣_{p-1} γ = E_{p-1}` for every `γ ∈ SL(2, ℤ)`. -/
theorem eisenstein_slash_eq (hE : 3 ≤ p - 1) (γ : SL(2, ℤ)) :
    (⇑(ModularForm.E hE)) ∣[((p - 1 : ℕ) : ℤ)] γ = ⇑(ModularForm.E hE) := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantForm.slash_action_eqn _ _ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)

variable [Fact p.Prime]

/-- **Lemma 2.1(b)**: for every `γ ∈ SL(2, ℤ)` (carrying `∞` to an arbitrary cusp), the expansion
of `E_{p-1}` at the cusp `γ ∞`, i.e. the `q`-expansion of `E_{p-1} ∣ γ`, is the `p`-integral
series `eisensteinSeriesQExp p`, whose reduction modulo `p` is `1`. -/
theorem qExpansion_eisenstein_slash (hp2 : p ≠ 2) (hE : 3 ≤ p - 1) (γ : SL(2, ℤ)) :
    UpperHalfPlane.qExpansion 1 ((⇑(ModularForm.E hE)) ∣[((p - 1 : ℕ) : ℤ)] γ) =
      PowerSeries.map (Rat.castHom ℂ) (eisensteinSeriesQExp p) := by
  rw [eisenstein_slash_eq hE γ, map_eisensteinSeriesQExp hp2]

/-- **Lemma 2.1(b)**: the constant term of the expansion of `E_{p-1}` at every cusp is `1`. -/
theorem coeff_zero_qExpansion_eisenstein_slash (hp2 : p ≠ 2) (hE : 3 ≤ p - 1) (γ : SL(2, ℤ)) :
    (UpperHalfPlane.qExpansion 1 ((⇑(ModularForm.E hE)) ∣[((p - 1 : ℕ) : ℤ)] γ)).coeff 0 = 1 := by
  rw [qExpansion_eisenstein_slash hp2 hE γ, PowerSeries.coeff_map, coeff_eisensteinSeriesQExp]
  simp

/-- **Lemma 2.1(b)**, modulo `p`: the reduction modulo `p` of the `q`-expansion of `E_{p-1}` at
`∞`, the series `eisensteinSeriesQExp p`, is `1`. By `qExpansion_eisenstein_slash` this series is
also the expansion at every other cusp `γ ∞`; the statement here concerns only the series. -/
theorem reduceTo_qExpansion_eisenstein_slash (hp2 : p ≠ 2) (L : Type*) [Field L] [CharP L p] :
    (eisensteinSeriesQExp p).reduceTo L = 1 :=
  reduceTo_eisensteinSeriesQExp hp2 L

end LevelOne
