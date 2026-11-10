/-
Assembled by AxiomProver.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import SupersingularCongruences.EllipticCurve.HasseInvariant
public import SupersingularCongruences.Isogeny.Velu
public import SupersingularCongruences.LevelTwoForms.Identities

/-!
# External input: cited results and interface structures

The library proves its main theorems from two kinds of input that it does not prove. Every result
resting on either kind is conditional on it. Citation keys refer to `references.bib`.

1. **Cited results.** Seven theorems of the literature, each stated in this file as a definition
   `X : Prop` whose docstring gives the citation, the locator and the normalization. A result that
   uses `X` takes it as an explicit hypothesis `(hX : X)`. The main theorems take the bundle
   `(hcited : CitedResults)` instead.
2. **Interface structures.** `KatzForms`, `LevelCover`, `KatzForms.LegendreRegular`, `WeilPairing`
   and `LevelNForms` describe objects that Mathlib does not have: Katz modular forms on `Γ₀(ℓ)` and
   on full level `N` over `𝔽̄_p`, the modular curves, and the Weil pairing. Theorems that need these
   objects take the structures as explicit hypotheses. Each field is either a cited fact or a
   definitional property of the object modelled, and its docstring says which and gives the
   locator. One field, `KatzForms.formulaRule_mem`, carries the step of the manuscript's proof of
   Lemma 4.1 that needs test objects over all `L`-algebras; it is a consequence of Katz's
   definition, and its docstring explains why.

## Common setting

* `p ≥ 5` is prime, and `L` is an algebraic closure of `𝔽_p`, encoded as `IsAlgClosed L`,
  `CharP L p` and `hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x`.
* Elliptic curves are short Weierstrass models `W : y² = x³ + a₄x + a₆`
  (`[W.IsElliptic] [W.IsShortNF]`). Isomorphisms are the scalings `(x, y) ↦ (u²x, u³y)`.
* Supersingular means `W.IsSupersingularOver p`: `W` has no nonzero `p`-torsion point over `L`.
* A Deuring model, `W.IsDeuringModelOver p`, has coefficients fixed by `x ↦ x^{p²}` and
  `(x^{p²}, y^{p²}) = -(p • (x, y))` for every point.
* Invariant differentials are written `λ · dx/(2y)` with `λ ∈ Lˣ`.
* A Katz form is represented by its values on test objects over `L`.

## Conclusions resting on this input

Below, `K` is `KatzForms` and `Y` is `LevelCover`.

* **Theorem 1.1(i)** (`LevelOne.discriminantPow_satisfiesBehrensConditions`):
  `GonzalezDivisionPolynomial`, `GonzalezMultiplicationByP`, `SupersingularJInvariant`,
  `VeluIsogeny`, `DeuringHasseCriterion`; `K` for all `ℓ ≠ p`, and `Y`.
* **Theorem 1.1(ii)** (`LevelOne.not_behrensC4_discriminantPow_of_isAdmissible`):
  `DeuringPolynomialSeparable`; `K` at `ℓ = 2` and `LegendreRegular`.
* **Theorem 1.1, Larson's conjecture** (`LevelOne.discriminantPow_satisfiesBehrensConditions_iff`)
  and **Remark 1.2** (`LevelOne.discriminantPow_behrensC4_iff`): the cited results of (i) and
  `DeuringPolynomialSeparable`; `K`, `Y` and `LegendreRegular`.
* **Theorem 1.2**: `Gamma0.Pair.veluRatio_pow_eq_one` rests on `GonzalezDivisionPolynomial`,
  `GonzalezMultiplicationByP`, `SupersingularJInvariant` and `VeluIsogeny`;
  `KatzForms.containment` also takes `K`.
* **Theorem 1.3**: the eta-power proof `WeierstrassCurve.discriminant_pow_of_isDeuringModelOver_eta`
  uses no cited result; it takes `WeilPairing` and `LevelNForms` for `N = 3, 4`. The deduction from
  González (`WeierstrassCurve.unit_pow_twelve_mul_Δ_pow_of_isDeuringModel`,
  `WeierstrassCurve.Δ_pow_of_isDeuringModelOver`) rests on `GonzalezDivisionPolynomial` and
  `GonzalezMultiplicationByP`.
* **Lemma 2.1**: (a) `Gamma0.hasseRule_eq_zero_iff` rests on `DeuringHasseCriterion`; (b) the
  q-expansion statements use no input, and the cusp statement is the field
  `LevelCover.ord_cusp_eq_zero`, so (b) is only partly formalized;
  (c) `KatzForms.exists_reduce_eisenstein_eq_hasseRule` takes `K`; (e) the root statement
  `Gamma0.deuringPolynomial_isRoot_iff` rests on `DeuringHasseCriterion` only, and the
  separability `Gamma0.deuringPolynomial_separable` is `DeuringPolynomialSeparable`.
* **Eq. (3.1)** (`KatzForms.exists_hasseRule_eq_aeval`): `LarsonLevelTwoStructure` and `K`.
  **Proposition 3.4** (`KatzForms.hasse_factorization`): `DeuringHasseCriterion`,
  `DeuringPolynomialSeparable`, `K` and `LegendreRegular`. **Remark 3.1**
  (`KatzForms.hasse_eq_C_mul_hasseElevenLevelTwo`) and **Lemma 3.3, values on the Legendre
  family** (`KatzForms.exists_legendre_values`): no cited result; `K` at `ℓ = 2` and
  `LegendreRegular`.
* **Lemma 4.1** (`KatzForms.levelRaiseReduction_discriminantPow`): no cited result; `K`, through
  `KatzForms.formulaRule_mem`.
* **Lemma 4.3** (`WeierstrassCurve.exists_isDeuringModelOver_scaling`) and **Corollary 4.7**:
  `GonzalezDivisionPolynomial`, `GonzalezMultiplicationByP`, `SupersingularJInvariant`.
  **Corollary 4.6**: also `VeluIsogeny`. **Remark 4.1**: `GonzalezDivisionPolynomial` and
  `GonzalezMultiplicationByP`.
* **Proposition 5.3** (`KatzForms.hasse_pow_dvd_larsonL2_iff`): the cited results of Theorem 1.2,
  `DeuringHasseCriterion` and `DeuringPolynomialSeparable`; `K` at `ℓ = 2` and `LegendreRegular`.
  **Remark 5.1** (`KatzForms.delta_pow_dvd_larsonL2_iff_of_mod_four`): the input of
  Proposition 5.3 and `LarsonLevelTwoStructure`.
* **Proposition 5.4** (`KatzForms.exists_hasse_pow_mul_eq_levelRaise_sub`) and **the §2.1
  example** (`LevelOne.correctedDiscriminant_satisfiesBehrensConditions`,
  `LevelOne.discriminantPow_fifty_satisfiesBehrensConditions`): the cited results of
  Theorem 1.1(i); `K` and `Y`. The example's non-divisibility
  `LevelOne.not_exists_hasse_pow_mul_eq_reduction_correction` and (C3)
  `LevelOne.behrensC3_correctedQExp` use no cited result; they take `K` at `ℓ = 2`.

The remaining results (Lemmas 2.1(d), 2.2, 2.3, 3.1, the expansion of `R₂` in 3.2(a), 3.2 and 3.3
on the Legendre family, 4.4, 5.1, 5.5, Propositions 4.5(a), 5.2, the elementary parts of
Remark 5.2 and the Section 6 examples) use neither cited results nor interfaces, except
Proposition 4.5(b), which takes `LevelNForms`.

## Not formalized

* **Lemma 4.2** (a supersingular `E` has a unique subgroup scheme of order `p`, `ker F`, and a
  unique one of order `p²`, `E[p] = ker(F^{(p)}∘F)`). Mathlib cannot state it: its elliptic
  curves are `WeierstrassCurve`s with points over rings, with no attached scheme and no isogeny
  type; group objects exist only categorically (`GrpObj`), with no group schemes, finite flat
  subgroup schemes or their order; there is no relative Frobenius of schemes (only ring-level
  `frobenius`), no group-scheme kernel and no quotient by a subgroup scheme; and `FormalGroup` is
  a bare power-series structure, with no height and no formal group of a Weierstrass curve. The
  subgroup schemes in the lemma are non-reduced, with a single point, so no statement about points
  is equivalent to it. Its shadow on points is formalized, with no cited result
  (`SupersingularCongruences/EllipticCurve/SubgroupOrderP.lean`):
  * under `IsSupersingularOver p`, `E(L)[p^k] = 0`
    (`WeierstrassCurve.IsSupersingularOver.eq_zero_of_pow_smul_points`), and every subgroup of
    `E(L)` of order `p^k` is trivial, so none has order `p` or `p²`
    (`eq_bot_of_card_eq_pow_points`, `card_ne_prime_points`, `card_ne_sq_points`);
  * for any Weierstrass curve in characteristic `p`, `(x, y) ↦ (x^p, y^p)` from `E(L)` to
    `E^{(p)}(L)` is injective, and bijective when `L` is algebraically closed, and so is
    `F^{(p)}∘F` (`WeierstrassCurve.Affine.Point.mapRingHom_frobenius_injective_points`,
    `mapRingHom_frobenius_bijective_points`, `mapRingHom_frobenius_comp_injective_points`).

  The manuscript uses the lemma only in a parenthetical remark in the proof of Lemma 4.3, and the
  formal proof of Lemma 4.3 does not need it.
* **Remark 5.2, comparison of geometric and classical forms.** Proved at level 2, for `p` odd and
  any field `L` of characteristic `p`, from the `KatzForms` fields, with no cited result
  (`SupersingularCongruences/LevelTwo/RingComparison.lean`):
  * `P ↦ P(δ̄, ε̄)` from `L[δ, ε]_k` to the Katz forms of weight `k` on `Γ₀(2)` is injective
    (`KatzForms.eq_zero_of_aeval_deltaBar_epsBar_eq_zero`, `KatzForms.larsonToForm_injective`),
    by q-expansions;
  * hence `⌊k/4⌋ + 1 ≤ dim_L M_k(Γ₀(2))_L` for even `k` when that space is finite-dimensional
    (`KatzForms.le_finrank_form`);
  * every `P(δ̄, ε̄)` with `P ∈ 𝔽_p[δ, ε]` weighted homogeneous is the reduction of a classical
    form on `Γ₀(2)` with `p`-integral rational q-expansion (`KatzForms.exists_reduce_eq_aeval`);
  * the elementary inputs `dim F[δ, ε]_k = ⌊k/4⌋ + 1` for even `k`
    (`LevelTwo.finrank_weightedHomogeneousSubmodule`) and `12t − j(p − 1) ≥ 2`
    (`LevelTwo.two_le_weight_quotient`).

  The rest needs coherent cohomology of line bundles on the compactified moduli scheme over
  `ℤ_(p)`. Mathlib has no moduli scheme of elliptic curves with level structure, no Hodge bundle
  `ω` or sheaf of relative differentials on one, and no cohomology of quasi-coherent sheaves on
  schemes (hence no cohomology and base change). The interface sees only forms over `L`, so these
  statements cannot be expressed, and adding them as fields would assume the remark's conclusions:
  the base-change identity `M_k(Γ₀(ℓ), R) = M_k(Γ₀(ℓ), ℤ_(p)) ⊗ R`; the Kodaira–Spencer
  isomorphism; the vanishing of `H¹(ω^{⊗k})`; cohomology and base change; finiteness of
  `dim M_k(Γ₀(2))_L`, which `le_finrank_form` takes as a hypothesis; the equality
  `dim_{𝔽_p} M_k(2) = dim_ℂ M_k(Γ₀(2))`, without which eq. (5.2) and the equality of the geometric
  ring at level 2 with `𝔽_p[δ, ε]` are open; and surjectivity of reduction for general `ℓ`, and
  with it the classical lift `h` of Proposition 5.4's quotient. At `ℓ = 2` that lift could be
  assembled from Proposition 5.3 and `exists_reduce_eq_aeval`, given two further steps that are not
  done: the quotient's weighted homogeneity, and the conversion of the Katz identity into the
  q-expansion congruence `L₂(Δ^t) ≡ E_{p−1}^j h (mod p)`. (C4) is formalized in the manuscript's
  geometric sense, and Theorem 1.1(ii) is proved directly in the geometric ring at `ℓ = 2`, so
  none of this is needed for the main results.
* **Curve-level statements of Lemmas 3.2 and 3.3.** Mathlib has no modular curves `X(2)`, `X₀(2)`
  as schemes (no moduli of elliptic curves with level structure and no compactification by
  cusps), no Weil or principal divisors on curves, and no ramification indices of morphisms of
  curves, so there are no cusps as points and no morphism `x : X₀(2) → ℙ¹`; the model has only
  non-cuspidal points. Formalized instead, with no cited result
  (`SupersingularCongruences/LevelTwo/CurveLevel.lean`, unless noted):
  * **3.2(a).** `R₂ = V₂(Δ)/Δ = q + 24q² + 300q³ + ⋯`, as the series `Δ(q²)/Δ(q) ∈ ℤ⟦q⟧`
    (`LevelOne.trunc_discriminantRatioSeries`).
  * **3.2(b), on points.** Over an algebraically closed `L` with `2, 3 ≠ 0`, `x` induces a
    bijection from isomorphism classes of pairs `(E, C)` onto `L∖{0}`
    (`Gamma0.Pair.bijective_xCoordinateClass`, `Gamma0.Pair.range_xCoordinate`).
  * **3.2(c), on points.** `δ̄` vanishes exactly where `x = −1`, i.e. exactly on the class of
    `(E_{−1}, ⟨(0,0)⟩)` (`KatzForms.deltaBar_eq_zero_iff`,
    `KatzForms.deltaBar_eq_zero_iff_scale_eq`), and `ε̄` and `μ̄` do not vanish
    (`KatzForms.epsBar_ne_zero`, `KatzForms.muBar_ne_zero`). These take `K` at `ℓ = 2`.
  * **3.3, degree and separability.** With `x = (λ−1)²/(4λ)`, `[K(λ) : K(x)] = 2`, the minimal
    polynomial of `λ` is `T² − (2 + 4x)T + 1`, and the extension is separable when `2 ≠ 0`
    (`Gamma0.finrank_xRatFunc`, `Gamma0.minpoly_legendreX`, `Gamma0.isSeparable_xRatFunc`).
  * **3.3, fibres.** The fibre of `λ ↦ (E_λ, ⟨(0,0)⟩)` over a pair has two elements, except over
    `x = −1`, where it is `{−1}` (`j = 1728`) (`Gamma0.ncard_legendreFibre`,
    `Gamma0.legendreFibre_eq_singleton_neg_one`).
  * **Further point-level results.** `Gamma0.xCoordinate_legendrePair`,
    `Gamma0.Pair.xCoordinate_eq_iff`, `Gamma0.exists_legendreFibre_eq` and
    `KatzForms.exists_legendre_values`.

  Not formalized, with the reasons:
  * **Values at the cusps**: `x(∞) = 0`, `x(0) = ∞`, `x − ξ` as a uniformizer, the divisor
    `(∞) − (0)` of `R₂`, and the cusp values of `μ`, `ε`, `δ`. `LevelCover`'s `Cusp` is an opaque
    index type with no `∞`, no `0` and no widths; its `ord` is defined only on sections of
    `ω^{⊗k}`, not on weight-0 ratios; and its one cusp field, `ord_cusp_eq_zero`, concerns
    level-one forms.
  * **Function fields**: the identification of `K(λ)` and `K(x)` with the function fields of
    `X(2)` and `X₀(2)`, with `π^*` as the inclusion.
  * **Ramification**: the ramification index 2 over `x = −1`. Only the fibre count and
    `legendreFibrePolynomial_eq_sq_iff` (`(λ−1)² − 4ξλ` is a square iff `ξ = −1`) are proved.
  * **The elliptic point**: the converse, that every pair with `j = 1728` and `C` fixed by `[i]`
    has `x = −1`.
* **The §2.1 example, its homotopy-theoretic reading.** That the two forms give distinct elements
  of Behrens' group of congruences, and hence different classes on the `2`-line, is not
  formalized: Mathlib has neither Behrens' group of congruences (nor Katz's ring of divided
  congruences) nor the Adams–Novikov spectral sequence and its `2`-line, so the statement cannot
  be expressed. The congruence statements of the example are formalized.

## Arguments that differ from the manuscript

These are complete proofs of the manuscript's statements by a different route.

* **Lemma 4.3(a).** The factorization `π = u∘[p]` is taken from [gonzalez2022, Lemma 3.1] rather
  than [silverman-aec, Corollary II.2.12], and the twist is an explicit scaling.
* **Lemmas 3.2 and 3.3, Proposition 3.4.** Proved on the Legendre family by explicit polynomial
  identities in `λ`, instead of by orders on the curves `X(2)` and `X₀(2)`.
* **Theorem 1.1(ii).** Proved directly in the geometric ring at `ℓ = 2`, by comparing root
  multiplicities on the Legendre family, instead of through Remark 5.2.
* **Proposition 4.5(a).** The generation of `Γ(3)` and `Γ(4)` by parabolic elements is proved
  algebraically (`CongruenceSubgroup.Gamma_le_normalClosure_T_pow`, by explicit coset certificates
  evaluated with `decide`), instead of through the topology of `Y(N)`.
* **Lemma 2.3.** Proved from the weight bound of Lemma 2.2, not from the filtration theory of
  [swinnerton-dyer1973].
* **The §2.1 example, (C3).** Instead of Swinnerton-Dyer's filtration theory, the proof compares
  `A^{600−k'}·ḡ⁴` with `f̄⁴` in weight 2400 by the q-expansion principle and evaluates at a
  supersingular Legendre test object.
-/

@[expose] public section

namespace WeierstrassCurve

open Polynomial WeierstrassCurve.Affine

/-- **González's formula for the `p`-th division polynomial** [gonzalez2022, Theorem 3.2].
Let `p > 3` be prime and let `E : y² = x³ + A x + B` be a supersingular elliptic curve defined over
`𝔽̄_p`. Then `ψ_{E,p} = (-1 / p) (A ^ 3 + 27 B ^ 2 / 4) ^ ((p ^ 2 - 1) / 12)`, where `(-1 / p)` is
the Legendre symbol, written here as `(-1) ^ ((p - 1) / 2)`. (The manuscript uses this in its
deduction of Theorem 1.3, at the end of Section 4.2.)

Normalization: for odd `n`, Mathlib's `WeierstrassCurve.preΨ n` is the classical `n`-th division
polynomial `ψ_n ∈ L[x]` of [gonzalez2022, Section 3] (normalized by `ψ₂ = 2y`), so `ψ_{E,p}` is
`W.preΨ p`, a constant polynomial; `A = W.a₄`, `B = W.a₆`; supersingularity is "no nonzero
`p`-torsion point over `L`", which is [gonzalez2022, Section 2]; `L` is an algebraic closure of
`𝔽_p` (`IsAlgClosed L`, `CharP L p` and the hypothesis that every `x : L` has `x ^ (p ^ k) = x`
for some `k ≥ 1`). -/
def GonzalezDivisionPolynomial.{u} : Prop :=
  ∀ {L : Type u} [Field L] [IsAlgClosed L] [DecidableEq L] {p : ℕ} [CharP L p], p.Prime → 5 ≤ p →
    ∀ (W : WeierstrassCurve L) [W.IsElliptic] [W.IsShortNF],
      (∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) → (∀ P : W.toAffine.Point, p • P = 0 → P = 0) →
        W.preΨ p =
          C ((-1) ^ ((p - 1) / 2) * (W.a₄ ^ 3 + 27 * W.a₆ ^ 2 / 4) ^ ((p ^ 2 - 1) / 12))

/-- **González's description of multiplication by `p`** [gonzalez2022, Lemma 3.1].
Let `p > 3` be prime and let `E : y² = x³ + A x + B` be a supersingular elliptic curve defined over
`𝔽_{p²}`, with (constant) `p`-th division polynomial `ψ = ψ_{E,p}`. Then the automorphism `u` of
`E` with `[p] = u ∘ Frob_{p²}` acts as `u (x, y) = (ψ⁻² x, ψ⁻³ y)`, where
`Frob_{p²} (x, y) = (x ^ (p ^ 2), y ^ (p ^ 2))`. Equivalently, for every affine point `(x, y)`
over `𝔽̄_p`, `p • (x, y) = (ψ⁻² x ^ (p ^ 2), ψ⁻³ y ^ (p ^ 2))`; this pointwise form is stated here.

Normalization: `ψ` is the constant coefficient of `W.preΨ p` (see `GonzalezDivisionPolynomial`);
`A = W.a₄`, `B = W.a₆`, and "defined over `𝔽_{p²}`" is `A ^ (p ^ 2) = A` and `B ^ (p ^ 2) = B`;
supersingularity is "no nonzero `p`-torsion point over `L`"; `L` is an algebraic closure of `𝔽_p`,
encoded as in `GonzalezDivisionPolynomial`. -/
def GonzalezMultiplicationByP.{u} : Prop :=
  ∀ {L : Type u} [Field L] [IsAlgClosed L] [DecidableEq L] {p : ℕ} [CharP L p], p.Prime → 5 ≤ p →
    ∀ (W : WeierstrassCurve L) [W.IsElliptic] [W.IsShortNF],
      (∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) → W.a₄ ^ p ^ 2 = W.a₄ → W.a₆ ^ p ^ 2 = W.a₆ →
        (∀ P : W.toAffine.Point, p • P = 0 → P = 0) →
          ∀ {x y : L} (h : W.toAffine.Nonsingular x y),
            ∃ h' : W.toAffine.Nonsingular (((W.preΨ p).coeff 0)⁻¹ ^ 2 * x ^ (p ^ 2))
                (((W.preΨ p).coeff 0)⁻¹ ^ 3 * y ^ (p ^ 2)),
              p • Point.some x y h = Point.some _ _ h'

/-- **Supersingular `j`-invariants lie in `𝔽_{p²}`** [silverman-aec, Theorem V.3.1(a)]. Let `L` be a
field of characteristic `p` and `E / L` an elliptic curve with `E[p] = 0`. Then
`j(E) ∈ 𝔽_{p²}`. (The manuscript uses this in the proof of Lemma 4.3(a).)

Normalization: `L` is algebraically closed, so `E[p] = 0` is "no nonzero `p`-torsion point over
`L`", and `j(E) ∈ 𝔽_{p²}` is `j ^ (p ^ 2) = j`. -/
def SupersingularJInvariant.{u} : Prop :=
  ∀ {L : Type u} [Field L] [IsAlgClosed L] [DecidableEq L] {p : ℕ} [CharP L p], p.Prime →
    ∀ (W : WeierstrassCurve L) [W.IsElliptic], (∀ P : W.toAffine.Point, p • P = 0 → P = 0) →
      W.j ^ (p ^ 2) = W.j

/-- **Vélu's theorem** [velu1971, §§2–3, formulas (7)–(11)] (see also
[washington2008, Theorem 12.16]). Let `E` be an elliptic curve `y² = x³ + a₄ x + a₆` over an
algebraically closed field `F` of characteristic different from `2` and `3`, and let `C` be a
finite subgroup of `E(F)`. Then Vélu's curve `E / C : y² = x³ + (a₄ − 5t)x + (a₆ − 7w)`
(`WeierstrassCurve.velu`, with `t = ∑_{Q ∈ C \ {0}} (3x_Q² + a₄)` and
`w = ∑_{Q ∈ C \ {0}} (5x_Q³ + 3a₄x_Q + 2a₆)`) is an elliptic curve, and the map
`P ↦ (x_P + ∑_{Q ∈ C \ {0}} (x_{P + Q} - x_Q), y_P + ∑_{Q ∈ C \ {0}} (y_{P + Q} - y_Q))`
(for `P ∉ C`, and `P ↦ 0` for `P ∈ C`) is a surjective group homomorphism `E(F) → (E / C)(F)`
with kernel `C`: it is the separable isogeny with kernel `C`.

Normalization: short Weierstrass models, for which the sums over `C \ {0}` rewrite Vélu's sums
(see `SupersingularCongruences.Isogeny.Velu`); points are `F`-points of the affine model with the
point at infinity `0`; surjectivity on `F`-points is the surjectivity of a nonconstant morphism of
curves over an algebraically closed field [silverman-aec, Theorem II.2.3]. -/
def VeluIsogeny.{u} : Prop :=
  ∀ {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (C : AddSubgroup W.toAffine.Point) [IsAlgClosed F] [W.IsElliptic] [W.IsShortNF],
    (2 : F) ≠ 0 → (3 : F) ≠ 0 → (C : Set W.toAffine.Point).Finite →
      IsUnit (W.velu C).Δ ∧
        ∃ φ : W.toAffine.Point →+ (W.velu C).toAffine.Point, φ.ker = C ∧
          Function.Surjective φ ∧ ∀ P ∉ C,
            (φ P).xCoord = P.xCoord +
                ∑ᶠ Q ∈ (C : Set W.toAffine.Point) \ {0}, ((P + Q).xCoord - Q.xCoord) ∧
            (φ P).yCoord = P.yCoord +
                ∑ᶠ Q ∈ (C : Set W.toAffine.Point) \ {0}, ((P + Q).yCoord - Q.yCoord)

/-- **Supersingularity criterion** [silverman-aec, Theorem V.4.1(a)] (manuscript, Lemma 2.1(a)).
Let `p > 2` and let `E : y² = f(x)` be an elliptic curve over a finite field of characteristic `p`,
with `f` a cubic with distinct roots. Then `E` is supersingular iff the coefficient of `x^{p-1}` in
`f(x)^{(p-1)/2}` (`WeierstrassCurve.hasseCoeff`) is zero.

Normalization: `L` is an algebraic closure of `𝔽_p` (`IsAlgClosed L`, `CharP L p` and the
hypothesis that every `x : L` has `x ^ (p ^ k) = x` for some `k ≥ 1`), so that `E` is defined over
the finite field generated by its coefficients; `f = x³ + a₄ x + a₆`; supersingularity is
`E[p](L) = 0` (`WeierstrassCurve.IsSupersingularOver`), which is Silverman's definition
[silverman-aec, Section V.3]. -/
def DeuringHasseCriterion.{u} : Prop :=
  ∀ {L : Type u} [Field L] [IsAlgClosed L] [DecidableEq L] {p : ℕ} [CharP L p], p.Prime → p ≠ 2 →
    (∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) →
      ∀ (W : WeierstrassCurve L) [W.IsElliptic] [W.IsShortNF],
        W.hasseCoeff p = 0 ↔ W.IsSupersingularOver p

end WeierstrassCurve

namespace Polynomial

/-- **The Deuring polynomial has distinct roots** [silverman-aec, Theorem V.4.1(c)], [igusa1958]
(manuscript, Lemma 2.1(e)): for `p` an odd prime,
`H_p(t) = ∑_{i=0}^{(p-1)/2} binom((p-1)/2, i)² tⁱ` has distinct roots in an algebraic closure of
`𝔽_p`. Normalization: stated as separability of `H_p` (`Polynomial.deuringPolynomial`) over a
field of characteristic `p`. -/
def DeuringPolynomialSeparable.{u} : Prop :=
  ∀ {L : Type u} [Field L] {p : ℕ} [CharP L p], p.Prime → p ≠ 2 → (deuringPolynomial L p).Separable

end Polynomial

namespace LevelTwoForms

open ModularForm UpperHalfPlane CongruenceSubgroup

/-- **Larson's structure theorem** [larson2020, Proposition 3.2] (arXiv v1 numbering):
`M_*(Γ₀(2))[1/2] = ℤ[1/2][δ, ε]`, the surjectivity half. Every modular form `f` of weight `k` on
`Γ₀(2)` whose `q`-expansion coefficients lie in `ℤ[1/2]` is `P(δ, ε)` for a polynomial `P` with
`ℤ[1/2]` coefficients, weighted homogeneous of weight `k` for the weights `2` of `δ` and `4` of
`ε`.

Normalization: `δ = LevelTwoForms.delta` and `ε = LevelTwoForms.eps` are Larson's forms, identified
by their `q`-expansions in `SupersingularCongruences.LevelTwoForms.Structure`; `ε` equals the
manuscript's `η(τ)¹⁶ / (16 η(2τ)⁸)`. `ℤ[1/2]` is the set of rationals `a / 2^m`;
`P ∈ ℚ[δ, ε]` is `MvPolynomial (Fin 2) ℚ` with `δ = X 0`, `ε = X 1`, and `P(δ, ε)` is evaluated
pointwise on `ℍ`. The weight `k` is a natural number (there are no nonzero forms of negative
weight). -/
def LarsonLevelTwoStructure : Prop :=
  ∀ {k : ℕ} (f : ModularForm (Gamma0 2) k),
    (∀ n, ∃ (a : ℤ) (m : ℕ), (qExpansion 1 f).coeff n = (a : ℂ) / 2 ^ m) →
      ∃ P : MvPolynomial (Fin 2) ℚ, P.IsWeightedHomogeneous ![2, 4] k ∧
        (∀ e, ∃ (a : ℤ) (m : ℕ), P.coeff e = (a : ℚ) / 2 ^ m) ∧
        ∀ τ : ℍ, f τ = MvPolynomial.aeval ![delta τ, eps τ] P

end LevelTwoForms

/-- The seven cited results of the literature that the main theorems rest on, bundled. A main
theorem takes `(hcited : CitedResults)` and passes on the fields its proof uses. -/
structure CitedResults.{u} : Prop where
  /-- González's formula for the `p`-th division polynomial [gonzalez2022, Theorem 3.2]. -/
  gonzalezDivisionPolynomial : WeierstrassCurve.GonzalezDivisionPolynomial.{u}
  /-- González's description of multiplication by `p` [gonzalez2022, Lemma 3.1]. -/
  gonzalezMultiplicationByP : WeierstrassCurve.GonzalezMultiplicationByP.{u}
  /-- Supersingular `j`-invariants lie in `𝔽_{p²}` [silverman-aec, Theorem V.3.1(a)]. -/
  supersingularJInvariant : WeierstrassCurve.SupersingularJInvariant.{u}
  /-- Vélu's theorem [velu1971, §§2–3]. -/
  veluIsogeny : WeierstrassCurve.VeluIsogeny.{u}
  /-- The supersingularity criterion [silverman-aec, Theorem V.4.1(a)]. -/
  deuringHasseCriterion : WeierstrassCurve.DeuringHasseCriterion.{u}
  /-- The Deuring polynomial has distinct roots [silverman-aec, Theorem V.4.1(c)], [igusa1958]. -/
  deuringPolynomialSeparable : Polynomial.DeuringPolynomialSeparable.{u}
  /-- Larson's structure theorem for `M_*(Γ₀(2))[1/2]` [larson2020, Proposition 3.2]. -/
  larsonLevelTwoStructure : LevelTwoForms.LarsonLevelTwoStructure

end
