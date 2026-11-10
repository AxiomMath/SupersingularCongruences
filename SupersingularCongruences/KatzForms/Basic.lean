/-
Assembled by AxiomProver.
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.RingTheory.Polynomial.Basic
public import SupersingularCongruences.ModularCurve.Gamma0Pair
public import SupersingularCongruences.EllipticCurve.HasseInvariant
public import SupersingularCongruences.LevelOne.IntegralQExpansion
public import SupersingularCongruences.LevelTwoForms.LevelRaise
public import SupersingularCongruences.Algebra.ExpandSeries
public import SupersingularCongruences.EllipticCurve.TateCurve
public import SupersingularCongruences.KatzForms.UniversalFormula

/-!
# Katz modular forms on `Γ₀(ℓ)` over an algebraic closure of `𝔽_p`

Mathlib has no theory of modular forms in the sense of Katz [katz1973, Section 1.1], i.e. of rules
`f` assigning to every triple `(E / R, C, ω)` over an algebra `R` an element of `R`, compatibly
with base change and isomorphisms. We work over an algebraically closed field `L` of
characteristic `p` and represent a Katz form of weight `k` on `Γ₀(ℓ)` over `L` by its values on
the test objects over `L` (`Gamma0.Test`); a form is determined by these values (it is a section
of a line bundle on the reduced curve `X₀(ℓ)_L`, determined by its values at closed points).

The structure `KatzForms p ℓ L` bundles the cited facts we use about the space of such forms. Each
field is a statement of the cited theory, recorded with its source in its docstring; the structure
contains none of the manuscript's conclusions. A theorem taking `K : KatzForms p ℓ L` as an
argument holds for the actual spaces of Katz forms, which satisfy all fields.

## Rules

* `Gamma0.discriminantRule`: `(E, C, λ ω_E) ↦ Δ(E, λ ω_E) = λ⁻¹² Δ(E)`;
* `Gamma0.hasseRule p`: `(E, C, λ ω_E) ↦ λ^{-(p-1)} · (coefficient of x^{p-1} in
  (x³ + a₄ x + a₆)^{(p-1)/2})` (`WeierstrassCurve.hasseCoeff`), the Hasse invariant
  [katz-mazur, Section 12.4];
* `Gamma0.veluDiscriminantRule`: `(E, C, λ ω_E) ↦ Δ(E / C, ω')` with `φ^* ω' = λ ω_E` for Vélu's
  normalized quotient isogeny `φ : E → E / C`, i.e. `λ⁻¹² Δ(E / C)`;
* `Gamma0.formulaRule k F`: the rule of a universal formula `F` of weight `k`, a polynomial in
  `a₄`, `a₆` and traces over `C \ {0}` of polynomials in `a₄, a₆, x`
  (`SupersingularCongruences.KatzForms.UniversalFormula`). Such rules are forms
  (`KatzForms.formulaRule_mem`); `veluDiscriminantRule` is one (`Gamma0.formulaRule_veluFormula`),
  which proves `KatzForms.veluDiscriminant_mem`.

## Forms over `𝔽_p`

A Katz form over `L` is defined over `𝔽_p` iff it is fixed by the action of `Aut(L) = Gal(L / 𝔽_p)`
(Galois descent; the formation of Katz forms commutes with the flat base change `𝔽_p → L`
[katz1973, Section 1.1, condition 3]). `Gamma0.IsDefinedOverPrimeField f` expresses
`f (T^σ) = σ (f T)` for all `σ` and `T`.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine Polynomial CongruenceSubgroup
open scoped MatrixGroups

namespace PowerSeries

/-- A power series over `ℚ` is `p`-integral if no coefficient has denominator divisible by `p`. -/
def IsPIntegral (p : ℕ) (G : PowerSeries ℚ) : Prop :=
  ∀ n, ¬ p ∣ (G.coeff n).den

/-- The reduction of a (`p`-integral) power series over `ℚ` to a field `L` of characteristic `p`,
coefficientwise via `ℚ → L`. -/
noncomputable def reduceTo (L : Type*) [Field L] (G : PowerSeries ℚ) : PowerSeries L :=
  PowerSeries.mk fun n ↦ ((G.coeff n : ℚ) : L)

lemma isPIntegral_iff {p : ℕ} {G : PowerSeries ℚ} : G.IsPIntegral p ↔ ∀ n, ¬ p ∣ (G.coeff n).den :=
  Iff.rfl

@[simp] lemma coeff_reduceTo (L : Type*) [Field L] (G : PowerSeries ℚ) (n : ℕ) :
    (G.reduceTo L).coeff n = ((G.coeff n : ℚ) : L) := by
  simp [reduceTo]

end PowerSeries

namespace Gamma0

variable {ℓ : ℕ} {L : Type*} [Field L] [DecidableEq L]

/-- The discriminant rule `Δ(E, λ ω_E) = λ⁻¹² Δ(E)`. -/
noncomputable def discriminantRule (T : Test ℓ L) : L :=
  ((T.diff : L) ^ 12)⁻¹ * T.curve.Δ

/-- The Hasse invariant rule `(E, C, λ ω_E) ↦ λ^{-(p-1)} · hasseCoeff p E`. -/
noncomputable def hasseRule (p : ℕ) (T : Test ℓ L) : L :=
  ((T.diff : L) ^ (p - 1))⁻¹ * T.curve.hasseCoeff p

/-- The rule `(E, C, λ ω_E) ↦ Δ(E / C, ω') = λ⁻¹² Δ(E / C)`, where `φ^* ω' = λ ω_E` for Vélu's
normalized quotient isogeny `φ : E → E / C`. -/
noncomputable def veluDiscriminantRule (T : Test ℓ L) : L :=
  ((T.diff : L) ^ 12)⁻¹ * (T.curve.velu T.subgroup).Δ

/-- The Tate curve `Tate(q)` over `L⟦q⟧`, the base change of `LevelOne.tateCurve`. Its standard
differential `dx / (2y + x)` is the canonical differential `du / u`. -/
noncomputable def tateCurveOver (L : Type*) [Field L] : WeierstrassCurve (PowerSeries L) :=
  LevelOne.tateCurve.map (PowerSeries.map (Int.castRingHom L))

/-- The rule `f` is defined over the prime field: `f (T^σ) = σ (f T)` for all field automorphisms
`σ` of `L` and all test objects `T`. -/
def IsDefinedOverPrimeField (f : Test ℓ L → L) : Prop :=
  ∀ (σ : L ≃+* L) (T : Test ℓ L), f (T.map σ) = σ (f T)

lemma discriminantRule_apply (T : Test ℓ L) :
    discriminantRule T = ((T.diff : L) ^ 12)⁻¹ * T.curve.Δ := (rfl)

lemma hasseRule_apply (p : ℕ) (T : Test ℓ L) :
    hasseRule p T = ((T.diff : L) ^ (p - 1))⁻¹ * T.curve.hasseCoeff p := (rfl)

lemma veluDiscriminantRule_apply (T : Test ℓ L) :
    veluDiscriminantRule T = ((T.diff : L) ^ 12)⁻¹ * (T.curve.velu T.subgroup).Δ := (rfl)

/-- The rule `Δ(E / C, ω')` is the rule of Vélu's universal formula
`-16 (4 (a₄ - 5 t)³ + 27 (a₆ - 7 w)²)`. -/
lemma veluDiscriminantRule_eq_formulaRule :
    (veluDiscriminantRule : Test ℓ L → L) = formulaRule 12 veluFormula :=
  funext fun T ↦ (formulaRule_veluFormula T).symm

lemma isDefinedOverPrimeField_iff {f : Test ℓ L → L} :
    IsDefinedOverPrimeField f ↔ ∀ (σ : L ≃+* L) (T : Test ℓ L), f (T.map σ) = σ (f T) :=
  Iff.rfl

end Gamma0

open Gamma0

/-- **The theory of Katz modular forms on `Γ₀(ℓ)` over `L`** (cited facts). Here `L` is an
algebraically closed field of characteristic `p` and `ℓ ≠ p` is a prime. A Katz form of weight `k`
is represented by its values on test objects over `L` (see the module docstring); `form k` is the
`L`-space of these functions.

Sources: [katz1973, Sections 1.1–1.7 and 1.11] for the definition, the `q`-expansion principle,
the comparison with classical forms and the Tate curve; [katz-mazur, (8.8), Corollary 10.9.2 and
Section 12.4] for the discriminant, connectedness and the Hasse invariant; [velu1971] for the
quotient by `C`. -/
structure KatzForms (p ℓ : ℕ) (L : Type*) [Field L] [DecidableEq L] where
  /-- The `L`-space of Katz forms of weight `k` on `Γ₀(ℓ)` over `L`, as functions on test
  objects. -/
  form : ℤ → Submodule L (Test ℓ L → L)
  /-- The constant `1` is a form of weight `0`. -/
  one_mem : (1 : Test ℓ L → L) ∈ form 0
  /-- Products of forms are forms, weights adding (the ring structure [katz1973, Section 1.1]). -/
  mul_mem {a b : ℤ} {f g : Test ℓ L → L} : f ∈ form a → g ∈ form b → f * g ∈ form (a + b)
  /-- A form only depends on the isomorphism class of the test object
  [katz1973, Section 1.1, condition 1]. -/
  apply_scale {k : ℤ} {f : Test ℓ L → L} (hf : f ∈ form k) (T : Test ℓ L) (u : Lˣ) :
    f (T.scale u) = f T
  /-- The weight condition `f (E, C, c ω) = c^{-k} f (E, C, ω)`
  [katz1973, Section 1.1, condition 2]. -/
  apply_smulDiff {k : ℤ} {f : Test ℓ L → L} (hf : f ∈ form k) (T : Test ℓ L) (c : Lˣ) :
    f (T.smulDiff c) = (c : L) ^ (-k) * f T
  /-- The conjugate `T ↦ σ (f (T^{σ⁻¹}))` of a form by a field automorphism `σ` of `L` is a form
  (base change of Katz forms along `σ` [katz1973, Section 1.1, condition 3]). -/
  galois_mem {k : ℤ} {f : Test ℓ L → L} (hf : f ∈ form k) (σ : L ≃+* L) :
    (fun T ↦ σ (f (T.map σ.symm))) ∈ form k
  /-- The ring of forms has no zero divisors: `X₀(ℓ)_L` is irreducible
  [katz-mazur, Corollary 10.9.2]: the compactified moduli curve is smooth with geometrically
  connected fibres. -/
  eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℤ} {f g : Test ℓ L → L} :
    f ∈ form a → g ∈ form b → f * g = 0 → f = 0 ∨ g = 0
  /-- The `q`-expansion at the cusp `∞`: the value on the Tate curve `(Tate(q), μ_ℓ, du / u)`
  [katz1973, Section 1.3]. -/
  qExp (k : ℤ) : form k →ₗ[L] PowerSeries L
  /-- The `q`-expansion principle [katz1973, Theorem 1.6.1 and Corollary 1.6.2] (stated there for
  level `n ≥ 3`; on `Γ₀(ℓ)` it follows by passing to a rigidifying auxiliary level, as in
  [katz1973, Section 1.13]). -/
  qExp_injective (k : ℤ) : Function.Injective (qExp k)
  /-- The `q`-expansion of a product is the product of the `q`-expansions. -/
  qExp_mul {a b : ℤ} (f : form a) (g : form b) :
    qExp (a + b) ⟨f.1 * g.1, mul_mem f.2 g.2⟩ = qExp a f * qExp b g
  /-- The `q`-expansion of `1` is `1`. -/
  qExp_one : qExp 0 ⟨1, one_mem⟩ = 1
  /-- A classical form on `Γ₀(ℓ)` whose `q`-expansion has `p`-integral rational coefficients
  defines a Katz form over `ℤ_(p)`, whose reduction modulo `p`, base changed to `L`, is a Katz
  form with the reduced `q`-expansion [katz1973, Corollary 1.6.2, Theorem 1.7.1 and
  Sections 1.4–1.5]. -/
  reduce {k : ℤ} (f : ModularForm (Gamma0 ℓ) k) (G : PowerSeries ℚ) (hG : G.IsPIntegral p)
    (hfG : PowerSeries.map (Rat.castHom ℂ) G = UpperHalfPlane.qExpansion 1 f) : form k
  /-- The `q`-expansion of the reduction is the reduction of the `q`-expansion. -/
  qExp_reduce {k : ℤ} (f : ModularForm (Gamma0 ℓ) k) (G : PowerSeries ℚ) (hG : G.IsPIntegral p)
    (hfG : PowerSeries.map (Rat.castHom ℂ) G = UpperHalfPlane.qExpansion 1 f) :
    qExp k (reduce f G hG hfG) = G.reduceTo L
  /-- The reductions of classical forms are defined over `𝔽_p`. -/
  reduce_isDefinedOverPrimeField {k : ℤ} (f : ModularForm (Gamma0 ℓ) k) (G : PowerSeries ℚ)
    (hG : G.IsPIntegral p)
    (hfG : PowerSeries.map (Rat.castHom ℂ) G = UpperHalfPlane.qExpansion 1 f) :
    IsDefinedOverPrimeField (reduce f G hG hfG).1
  /-- The Weierstrass discriminant `(E, ω) ↦ Δ(E, ω)` is a form of weight `12`
  [katz1973, Section 1.1], [silverman-aec, Section III.1]. -/
  discriminant_mem : discriminantRule ∈ form 12
  /-- **The `q`-expansion is the value on the Tate curve** (for the discriminant). The cusp `∞` of
  `X₀(ℓ)` is the test object `(Tate(q), μ_ℓ, du / u)`, and the `q`-expansion of a form is its value
  there [katz1973, Sections 1.1–1.2], [katz-mazur, Chapter 8]. For the rule `Δ`, whose value on a
  Weierstrass curve with differential `c · ω_W` is `c⁻¹² Δ(W)`, this value is
  `Δ(Tate(q), du / u)` (`du / u = dx / (2y + x)` is the standard differential of the Tate
  equation [silverman-ataec, Section V.1]). This field is definitional: it says how the
  `q`-expansion is computed. The Tate curve `LevelOne.tateCurve` is defined explicitly
  [silverman-ataec, Section V.1], [katz-mazur, (8.8)]; that its discriminant is `Δ(q)` is proved
  (`LevelOne.tateCurve_Δ`), and so is the resulting `q`-expansion
  (`KatzForms.qExp_discriminant`). -/
  qExp_discriminant_eq_tate :
    qExp 12 ⟨discriminantRule, discriminant_mem⟩ = (tateCurveOver L).discriminantValue 1
  /-- The Hasse invariant is a form of weight `p - 1`; on `(E, dx / (2y))` with
  `E : y² = x³ + a₄ x + a₆` it is the coefficient of `x^{p-1}` in `(x³ + a₄ x + a₆)^{(p-1)/2}`
  [katz1973, Section 2.0], [katz-mazur, (12.4.1)]; for the coefficient formula see
  [silverman-aec, Section V.4] and [katz1972, (2.3.7.14)]. -/
  hasse_mem : hasseRule p ∈ form ((p : ℤ) - 1)
  /-- The `q`-expansion of the Hasse invariant is `1` [katz1973, Section 2.0],
  [katz-mazur, Theorem 12.4.2]. -/
  qExp_hasse : qExp _ ⟨hasseRule p, hasse_mem⟩ = 1
  /-- **Rules given by universal formulas are forms.** Let `F` be a polynomial over `L` in `a₄`,
  `a₆` and the traces `∑_{Q ∈ C \ {0}} g(a₄, a₆, x_Q)` (`Gamma0.FormulaVar`), weighted
  homogeneous of weight `k` for the weights `4`, `6` and the weighted degree of `g` (with `x` of
  weight `2`). For `p ≥ 5` and `ℓ ≠ p`, so that `6` and `ℓ` are invertible in `L`, `F` defines a
  rule on the test objects `(E / R, C, ω)` over all `L`-algebras `R`: `(E, ω)` has a unique
  Weierstrass equation `y² = x³ + a₄ x + a₆` with `ω = dx / (2y)`, and the traces are the traces
  of the regular functions `g(a₄, a₆, x)` along the finite étale `R`-scheme `C \ {0}`. This rule
  is compatible with base change and isomorphisms, and has weight `k` because `F` is weighted
  homogeneous; these are the conditions of Katz's definition [katz1973, Section 1]. It is
  holomorphic at the cusps: on the Tate curve with any subgroup of order `ℓ`, over
  `L((q^{1/ℓ}))[ζ_ℓ]`, the Weierstrass coefficients and the `x`-coordinates of the nonzero points
  of the subgroup are power series in `q^{1/ℓ}` without poles (`1 - ζ` is a unit for `ζ ≠ 1` an
  `ℓ`-th root of unity), so the value of `F` has no pole.

  Sources. Katz's definition of a form as such a rule, and holomorphy at the cusps as the
  condition on the value at the Tate curve, are cited from [katz1973, Sections 1.1–1.7] and
  [katz-mazur, Chapter 8], the manuscript's references for both. No precise locator in a cited
  work is given for two further facts, which are elementary properties of the objects modelled
  rather than arguments of the manuscript. The first is the normalized Weierstrass equation of
  `(E, ω)` over a ring in which `6` is invertible, unique up to `(x, y) ↦ (u²x, u³y)`. The second
  is that the trace of a finite locally free algebra lies in the base ring and commutes with base
  change. The values of this form on test objects over `L` are `Gamma0.formulaRule k F`.

  Role. This is the step of the manuscript's proof of Lemma 4.1 that needs test objects over all
  `L`-algebras, and it follows from Katz's definition as above. The model has test objects over
  `L` only, so the field cannot be derived inside it. It is not the false statement that every
  isomorphism-invariant function of weight `k` on `L`-points is a form: it applies only to rules
  given by such formulas. Every result that uses Lemma 4.1 rests on it, including those that use
  it through the values of `δ̄, ε̄` on the Legendre family (`KatzForms.exists_legendre_values`,
  whose proof uses the level-2 case of Lemma 4.1): Theorem 1.1(i) and (ii), Larson's conjecture
  and Remark 1.2, the Katz-form statement of Theorem 1.2 (`KatzForms.containment`),
  Proposition 3.4, Remark 3.1, Propositions 5.3 and 5.4, Remark 5.1 and the §2.1 example. -/
  formulaRule_mem {k : ℕ} (F : MvPolynomial (FormulaVar L) L)
    (hF : F.IsWeightedHomogeneous FormulaVar.weight k) : formulaRule k F ∈ form k
  /-- A Weierstrass model `E'` over `L⟦q⟧` of the quotient `Tate(q) / μ_ℓ` of the Tate curve by its
  canonical subgroup `μ_ℓ` (definitional data). -/
  tateQuot : WeierstrassCurve (PowerSeries L)
  /-- The unit `c` with `ω' = c · ω_{E'}`, where `φ : Tate(q) → E'` is the quotient isogeny and
  `φ^* ω' = du / u` (definitional data). -/
  tateQuotDiff : (PowerSeries L)ˣ
  /-- **The `q`-expansion is the value on the Tate curve** (for the rule `Δ(E / C, ω')`): the
  `q`-expansion of this form is the value of the same rule on `(Tate(q), μ_ℓ, du / u)`, namely
  `Δ(E', ω')` [katz1973, Sections 1.1–1.2], [katz-mazur, Chapter 8]. This field is definitional.
  (The membership is `KatzForms.veluDiscriminant_mem`.) -/
  qExp_veluDiscriminant_eq_tate (h : veluDiscriminantRule ∈ form 12) :
    qExp 12 ⟨veluDiscriminantRule, h⟩ = tateQuot.discriminantValue tateQuotDiff
  /-- **`Tate(q) / μ_ℓ ≅ Tate(q^ℓ)`** [katz-mazur, Chapters 8–10], [silverman-ataec, Chapter V]:
  for `ℓ` invertible in `L`, the `ℓ`-th power map `u ↦ v = u^ℓ` induces an isomorphism
  `Tate(q) / μ_ℓ ≅ Tate(q^ℓ)`, and the quotient isogeny `φ` satisfies `φ^* (dv / v) = ℓ du / u`.
  Here `Tate(q^ℓ)` is the base change of `Tate(q)` along `q ↦ q^ℓ`, and `dv / v` is its standard
  differential. In Weierstrass terms: there is a change of variables `C = (u, r, s, t)` with
  `C • E' = Tate(q^ℓ)`, i.e. an isomorphism `ψ : Tate(q^ℓ) → E'` with
  `ψ^* ω_{E'} = u⁻¹ ω_{Tate(q^ℓ)}`, under which `ψ^* ω' = ℓ⁻¹ dv / v` (equivalent to
  `φ^* (dv / v) = ℓ du / u`, as `φ^*` is injective on differentials); that is, `u = ℓ c`. From
  this and the fields above, `qExp(Δ(E / C, ω')) = ℓ¹² Δ(q^ℓ)` is proved
  (`KatzForms.qExp_veluDiscriminant`). -/
  tateQuot_iso (hℓ : ℓ ≠ 0) (hℓL : (ℓ : L) ≠ 0) :
    ∃ C : WeierstrassCurve.VariableChange (PowerSeries L),
      C • tateQuot = (tateCurveOver L).map (expandRingHom hℓ) ∧
        (C.u : PowerSeries L) = (ℓ : PowerSeries L) * tateQuotDiff

namespace KatzForms

variable {p ℓ : ℕ} {L : Type*} [Field L] [DecidableEq L] (K : KatzForms p ℓ L)

/-- **Lemma 4.1** (the rule is a form): `(E, C, ω) ↦ Δ(E / C, ω')`, `φ^* ω' = ω`, is a form of
weight `12`. Vélu's model `y² = x³ + (a₄ - 5 t) x + (a₆ - 7 w)` of `E / C` [velu1971, §§2–3] is
given by the traces `t`, `w` over `C \ {0}` of `3 x² + a₄` and `5 x³ + 3 a₄ x + 2 a₆`, so its
discriminant `-16 (4 (a₄ - 5 t)³ + 27 (a₆ - 7 w)²)` is a universal formula of weight `12`
(`Gamma0.formulaRule_veluFormula`), and such rules are forms (`KatzForms.formulaRule_mem`). -/
theorem veluDiscriminant_mem : veluDiscriminantRule ∈ K.form 12 := by
  rw [veluDiscriminantRule_eq_formulaRule]
  exact K.formulaRule_mem veluFormula isWeightedHomogeneous_veluFormula

/-- The `q`-expansion of `Δ` is `Δ(q) = q ∏ (1 - qⁿ)²⁴`: its value `Δ(Tate(q), du / u)` on the
Tate curve (`LevelOne.tateCurve_Δ`). -/
theorem qExp_discriminant :
    K.qExp 12 ⟨discriminantRule, K.discriminant_mem⟩ =
      PowerSeries.map (Int.castRingHom L) LevelOne.integralDiscriminant := by
  rw [K.qExp_discriminant_eq_tate, WeierstrassCurve.discriminantValue_def, inv_one,
    Units.val_one, one_pow, one_mul, tateCurveOver, WeierstrassCurve.map_Δ,
    LevelOne.tateCurve_Δ]

/-- **Lemma 4.1**, the `q`-expansion computation: for `ℓ` invertible in `L`, the `q`-expansion of
the rule `Δ(E / C, ω')` is `ℓ¹² Δ(q^ℓ)`. On the Tate curve, `Tate(q) / μ_ℓ ≅ Tate(q^ℓ)` with
`ω' = ℓ⁻¹ dv / v` (`KatzForms.tateQuot_iso`), so by isomorphism invariance, the weight rule and
base change along `q ↦ q^ℓ`,
`Δ(E', ω') = Δ(Tate(q^ℓ), ℓ⁻¹ dv / v) = ℓ¹² Δ(Tate(q^ℓ), dv / v) = ℓ¹² Δ(q^ℓ)`. -/
theorem qExp_veluDiscriminant (hℓL : (ℓ : L) ≠ 0) :
    K.qExp 12 ⟨veluDiscriminantRule, K.veluDiscriminant_mem⟩ =
      (ℓ : L) ^ 12 • expandSeries ℓ (PowerSeries.map (Int.castRingHom L)
        LevelOne.integralDiscriminant) := by
  have hℓ : ℓ ≠ 0 := by rintro rfl; exact hℓL Nat.cast_zero
  obtain ⟨C, hC, hu⟩ := K.tateQuot_iso hℓ hℓL
  have hE : K.tateQuot.Δ =
      (C.u : PowerSeries L) ^ 12 * ((tateCurveOver L).map (expandRingHom hℓ)).Δ := by
    rw [← hC, WeierstrassCurve.variableChange_Δ, ← mul_assoc, ← mul_pow, Units.mul_inv,
      one_pow, one_mul]
  have hdu : ((K.tateQuotDiff⁻¹ : (PowerSeries L)ˣ) : PowerSeries L) * C.u = ℓ := by
    rw [hu, mul_left_comm, Units.inv_mul, mul_one]
  rw [K.qExp_veluDiscriminant_eq_tate K.veluDiscriminant_mem,
    WeierstrassCurve.discriminantValue_def, hE, ← mul_assoc,
    ← mul_pow, hdu, WeierstrassCurve.map_Δ, tateCurveOver, WeierstrassCurve.map_Δ,
    LevelOne.tateCurve_Δ, expandRingHom_apply, PowerSeries.smul_eq_C_mul, map_pow, map_natCast]

end KatzForms
