/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.ModularCurve.LegendreNormalForm
public import SupersingularCongruences.KatzForms.LevelTwoReduction
public import SupersingularCongruences.LevelTwo.LegendreValues
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.FieldTheory.Separable
import all SupersingularCongruences.ModularCurve.LegendreNormalForm

/-!
# Point-level and function-field forms of Lemmas 3.2 and 3.3 of the manuscript

Let `L` be an algebraically closed field with `2, 3 ≠ 0`. Non-cuspidal points of `X₀(2)` over `L`
are represented by isomorphism classes of pairs `(E, C)` (`Gamma0.Pair 2 L`), two pairs `P`, `Q`
being isomorphic iff `P.scale u = Q` for some `u ∈ Lˣ`; non-cuspidal points of `X(2)` by Legendre
parameters `λ ∉ {0, 1}`, with `π(λ) = (E_λ, ⟨(0, 0)⟩)`.

## Main results

* `Gamma0.Pair.isoSetoid`: isomorphism of pairs, as an equivalence relation.
* `Gamma0.Pair.bijective_xCoordinateClass` (Lemma 3.2(b), point-level part): the coordinate
  `x = 64 R₂ = μ / ε` induces a bijection from the set of isomorphism classes of pairs over `L`
  onto `L \ {0}`; `Gamma0.Pair.range_xCoordinate`: the set of values of `x` at pairs is exactly
  `L \ {0}`. So `x` takes every nonzero value at exactly one non-cuspidal point and never takes
  the value `0` there (in the manuscript `x = 0` is the cusp `∞`, and the pole of `x` is the cusp
  `0`).
* `Gamma0.ncard_legendreFibre` (Lemma 3.3, fibre count): the fibre of `π` over a non-cuspidal
  point `P` has two elements if `x(P) ≠ -1` and one element if `x(P) = -1`;
  `Gamma0.legendreFibre_eq_singleton_neg_one`: the latter fibre is `{-1}` (`E_{-1}` has
  `j = 1728`).
* `KatzForms.deltaBar_eq_zero_iff_scale_eq`, from `KatzForms.deltaBar_eq_zero_iff` (Lemma 3.2(c),
  last sentence, at non-cuspidal points): `δ̄` vanishes at a test object iff `x = -1` there, i.e.
  iff the underlying pair is isomorphic to `(E_{-1}, ⟨(0, 0)⟩)`.
* `Gamma0.finrank_xRatFunc`, `Gamma0.minpoly_legendreX`, `Gamma0.isSeparable_xRatFunc`
  (Lemma 3.3, degree and separability, in terms of function fields): in `L(λ)` (`RatFunc L`), put
  `x = (λ - 1)² / (4 λ)`, the formula of `Gamma0.xCoordinate_legendrePair` for the pullback of
  the coordinate `x` along `π`. Then `[L(λ) : L(x)] = 2`, the minimal polynomial of `λ` over
  `L(x)` is `T² - (2 + 4 x) T + 1`, and `L(λ) / L(x)` is separable (for `2 ≠ 0` in `L`).

## Scope

These are statements about non-cuspidal points, as moduli of pairs, and about an explicit
extension of rational function fields. They do not formalize the curves `X₀(2)`, `X(2)` as
schemes, their cusps, the morphism `x : X₀(2) → ℙ¹` as an isomorphism of curves, uniformizers,
orders of vanishing at the cusps (e.g. `div R₂ = (∞) - (0)`), or ramification indices. The
identification of `L(λ)` and `L(x)` with the function fields of `X(2)` and `X₀(2)`, and of the
inclusion `L(x) ⊆ L(λ)` with `π^*`, is not formalized.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace Gamma0

variable {L : Type*} [Field L] [DecidableEq L]

namespace Pair

/-- Isomorphism of pairs `(E, C)` with `C` of order `2`: `P ≅ Q` iff `P.scale u = Q` for some
`u ∈ Lˣ`. Every isomorphism between short Weierstrass models is such a scaling. -/
def isoSetoid (h2 : (2 : L) ≠ 0) : Setoid (Pair 2 L) where
  r P Q := ∃ u : Lˣ, P.scale u = Q
  iseqv := by
    refine ⟨fun P => ⟨1, scale_one h2 P⟩, fun {P Q} h => ?_, fun {P Q R} hPQ hQR => ?_⟩
    · obtain ⟨u, hu⟩ := h
      exact ⟨u⁻¹, scale_eq_symm h2 hu⟩
    · obtain ⟨u, hu⟩ := hPQ
      obtain ⟨v, hv⟩ := hQR
      exact ⟨u * v, by rw [← scale_scale h2, hu, hv]⟩

lemma isoSetoid_r_iff (h2 : (2 : L) ≠ 0) (P Q : Pair 2 L) :
    (isoSetoid h2).r P Q ↔ ∃ u : Lˣ, P.scale u = Q := Iff.rfl

/-- The coordinate `x` as a function on isomorphism classes of pairs, with values in `L \ {0}`. -/
noncomputable def xCoordinateClass (h2 : (2 : L) ≠ 0) :
    Quotient (isoSetoid h2) → {ξ : L // ξ ≠ 0} :=
  Quotient.lift (fun P => ⟨P.xCoordinate, xCoordinate_ne_zero h2 P⟩) (by
    intro P Q h
    obtain ⟨u, rfl⟩ := h
    exact Subtype.ext (xCoordinate_scale h2 P u).symm)

lemma xCoordinateClass_mk (h2 : (2 : L) ≠ 0) (P : Pair 2 L) :
    (xCoordinateClass h2 (Quotient.mk _ P) : L) = P.xCoordinate := (rfl)

/-- **Lemma 3.2(b)**, point-level part: over an algebraically closed field `L` with `2, 3 ≠ 0`,
the coordinate `x = 64 R₂ = μ / ε` is a bijection from the set of isomorphism classes of pairs
`(E, C)` over `L` (the non-cuspidal points of `X₀(2)` over `L`) onto `L \ {0}`. -/
theorem bijective_xCoordinateClass [IsAlgClosed L] (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) :
    Function.Bijective (xCoordinateClass h2) := by
  constructor
  · intro a b h
    induction a using Quotient.inductionOn with
    | h P =>
      induction b using Quotient.inductionOn with
      | h Q =>
        apply Quotient.sound
        have hx : P.xCoordinate = Q.xCoordinate := by
          rw [← xCoordinateClass_mk h2 P, ← xCoordinateClass_mk h2 Q, h]
        exact (xCoordinate_eq_iff h2 h3 P Q).mp hx
  · rintro ⟨ξ, hξ⟩
    obtain ⟨lam, h0, h1, hx⟩ := exists_xCoordinate_eq h2 h3 hξ
    exact ⟨Quotient.mk _ (legendrePair h2 h3 h0 h1), Subtype.ext hx⟩

/-- **Lemma 3.2(b)**, point-level part, as a statement about values: over an algebraically closed
field `L` with `2, 3 ≠ 0`, the set of values of `x` at pairs `(E, C)` is exactly `L \ {0}`. -/
theorem range_xCoordinate [IsAlgClosed L] (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) :
    Set.range (xCoordinate : Pair 2 L → L) = {ξ | ξ ≠ 0} := by
  ext ξ
  constructor
  · rintro ⟨P, rfl⟩
    exact xCoordinate_ne_zero h2 P
  · intro hξ
    obtain ⟨lam, h0, h1, hx⟩ := exists_xCoordinate_eq h2 h3 hξ
    exact ⟨_, hx⟩

end Pair

section Legendre

variable (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0)

/-- **Lemma 3.3** (fibre count): over an algebraically closed field `L` with `2, 3 ≠ 0`, the fibre
of `π : λ ↦ (E_λ, ⟨(0, 0)⟩)` over the non-cuspidal point `P` of `X₀(2)` has exactly two elements
if `x(P) ≠ -1` and exactly one element if `x(P) = -1`. -/
theorem ncard_legendreFibre [IsAlgClosed L] (P : Pair 2 L) :
    (legendreFibre h2 h3 P).ncard = if P.xCoordinate = -1 then 1 else 2 := by
  obtain ⟨lam, h0, h1, hF⟩ := exists_legendreFibre_eq h2 h3 P
  split_ifs with hx
  · obtain ⟨mu, hmu⟩ := (exists_legendreFibre_eq_singleton_iff h2 h3 P).mpr hx
    rw [hmu, Set.ncard_singleton]
  · rw [hF, Set.ncard_pair]
    intro h
    apply hx
    refine (exists_legendreFibre_eq_singleton_iff h2 h3 P).mp ⟨lam, ?_⟩
    rw [hF, ← h, Set.pair_eq_singleton]

/-- **Lemma 3.3** (the exceptional fibre): over the point with `x = -1` the fibre of `π` is the
single Legendre parameter `λ = -1` (`E_{-1} : y² = x³ - x`, `j = 1728`). -/
theorem legendreFibre_eq_singleton_neg_one [IsAlgClosed L] (P : Pair 2 L)
    (hx : P.xCoordinate = -1) : legendreFibre h2 h3 P = {-1} := by
  obtain ⟨lam, h0, h1, hF⟩ := exists_legendreFibre_eq h2 h3 P
  have hmem : lam ∈ legendreFibre h2 h3 P := by rw [hF]; exact Set.mem_insert _ _
  obtain ⟨h0', h1', u, hu⟩ := hmem
  have hlam : lam = -1 := by
    rw [← xCoordinate_legendrePair_eq_neg_one_iff h2 h3 h0' h1',
      ← Pair.xCoordinate_scale h2 (legendrePair h2 h3 h0' h1') u, hu, hx]
  rw [hF, hlam, inv_neg, inv_one, Set.pair_eq_singleton]

end Legendre

section FunctionField

open Polynomial IntermediateField

/-- The element `x = (λ - 1)² / (4 λ)` of `K(λ) = RatFunc K`: the formula of
`Gamma0.xCoordinate_legendrePair` for the coordinate `x` at `(E_λ, ⟨(0, 0)⟩)`. -/
noncomputable def xRatFunc (K : Type*) [Field K] : RatFunc K :=
  (RatFunc.X - 1) ^ 2 / (4 * RatFunc.X)

lemma xRatFunc_eq (K : Type*) [Field K] :
    xRatFunc K =
      algebraMap K[X] (RatFunc K) ((X - 1) ^ 2) / algebraMap K[X] (RatFunc K) (C 4 * X) := by
  simp only [xRatFunc, map_pow, map_sub, map_mul, RatFunc.algebraMap_X, map_one,
    RatFunc.algebraMap_C]
  rw [show RatFunc.C (4 : K) = 4 from map_ofNat _ 4]

/-- **Lemma 3.3** (degree): `[K(λ) : K(x)] = 2` for `x = (λ - 1)² / (4 λ)`, when `2 ≠ 0` in
`K`. -/
theorem finrank_xRatFunc {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    Module.finrank K⟮xRatFunc K⟯ (RatFunc K) = 2 := by
  have h4 : (4 : K) ≠ 0 := by rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  rw [RatFunc.finrank_eq_max_natDegree]
  set n := (xRatFunc K).num
  set d := (xRatFunc K).denom
  have hq0 : (C 4 * X : K[X]) ≠ 0 := mul_ne_zero (C_ne_zero.mpr h4) X_ne_zero
  have hp0 : ((X - 1) ^ 2 : K[X]) ≠ 0 := pow_ne_zero _ (by simpa using X_sub_C_ne_zero (1 : K))
  have hd0 : d ≠ 0 := RatFunc.denom_ne_zero _
  have heq : (X - 1) ^ 2 * d = C 4 * X * n := by
    have h : algebraMap K[X] (RatFunc K) n / algebraMap K[X] (RatFunc K) d =
        algebraMap K[X] (RatFunc K) ((X - 1) ^ 2) / algebraMap K[X] (RatFunc K) (C 4 * X) :=
      (RatFunc.num_div_denom (xRatFunc K)).trans (xRatFunc_eq K)
    rw [div_eq_div_iff] at h
    · apply RatFunc.algebraMap_injective K
      rw [map_mul, map_mul]
      linear_combination -h
    · exact (_root_.map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hd0
    · exact (_root_.map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hq0
  have hcop := RatFunc.isCoprime_num_denom (xRatFunc K)
  have hdq : d ∣ C 4 * X := hcop.symm.dvd_of_dvd_mul_right ⟨_, heq.symm.trans (mul_comm _ _)⟩
  have hdeg_d : d.natDegree ≤ 1 := by
    have := natDegree_le_of_dvd hdq hq0
    rwa [natDegree_C_mul_X _ h4] at this
  have hn0 : n ≠ 0 := by
    rintro hn
    rw [hn, mul_zero] at heq
    exact mul_ne_zero hp0 hd0 heq
  have hX1 : (X - 1 : K[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : K)
  have hdeg : 2 + d.natDegree = 1 + n.natDegree := by
    have := congrArg natDegree heq
    rwa [natDegree_mul hp0 hd0, natDegree_mul hq0 hn0, natDegree_C_mul_X _ h4,
      natDegree_pow, hX1] at this
  have hd1 : d.natDegree ≠ 0 := by
    intro h0
    have hd : d = 1 := eq_one_of_monic_natDegree_zero (RatFunc.monic_denom _) h0
    rw [hd, mul_one] at heq
    have := congrArg (eval 0) heq
    simp at this
  omega

/-- The polynomial `T² - (2 + 4 x) T + 1` over `K(x)`, `x = (λ - 1)² / (4 λ)`; its roots in
`K(λ)` are `λ` and `1 / λ`. -/
noncomputable def legendreXPoly (K : Type*) [Field K] : K⟮xRatFunc K⟯[X] :=
  X ^ 2 - C (2 + 4 * ⟨xRatFunc K, mem_adjoin_simple_self K _⟩) * X + 1

lemma natDegree_legendreXPoly (K : Type*) [Field K] : (legendreXPoly K).natDegree = 2 := by
  unfold legendreXPoly
  compute_degree!

lemma monic_legendreXPoly (K : Type*) [Field K] : (legendreXPoly K).Monic := by
  unfold legendreXPoly
  monicity!

/-- `λ` is a root of `T² - (2 + 4 x) T + 1` over `K(x)`, `x = (λ - 1)² / (4 λ)`. -/
lemma aeval_legendreXPoly {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    aeval (RatFunc.X : RatFunc K) (legendreXPoly K) = 0 := by
  have h4 : (4 : RatFunc K) ≠ 0 := by
    rw [show (4 : RatFunc K) = RatFunc.C 4 from (map_ofNat _ 4).symm]
    exact (_root_.map_ne_zero _).mpr
      (by rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2)
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hc : algebraMap K⟮xRatFunc K⟯ (RatFunc K)
      (2 + 4 * ⟨xRatFunc K, mem_adjoin_simple_self K _⟩) = 2 + 4 * xRatFunc K := by
    rw [map_add, map_mul, map_ofNat, map_ofNat, IntermediateField.algebraMap_apply]
  rw [legendreXPoly, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, hc, map_one, xRatFunc]
  field_simp
  ring

/-- **Lemma 3.3** (the double cover in function fields): the minimal polynomial of `λ` over
`K(x)`, `x = (λ - 1)² / (4 λ)`, is `T² - (2 + 4 x) T + 1`, when `2 ≠ 0` in `K`. -/
theorem minpoly_legendreX {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    minpoly K⟮xRatFunc K⟯ (RatFunc.X : RatFunc K) = legendreXPoly K := by
  have hroot := aeval_legendreXPoly h2
  have hint : IsIntegral K⟮xRatFunc K⟯ (RatFunc.X : RatFunc K) :=
    ⟨_, monic_legendreXPoly K, hroot⟩
  have hdvd := minpoly.dvd _ _ hroot
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (monic_legendreXPoly K) hdvd
    ?_).symm
  rw [natDegree_legendreXPoly]
  have hle := natDegree_le_of_dvd hdvd (monic_legendreXPoly K).ne_zero
  rw [natDegree_legendreXPoly] at hle
  have hpos := minpoly.natDegree_pos hint
  by_contra hlt
  have h1 : (minpoly K⟮xRatFunc K⟯ (RatFunc.X : RatFunc K)).natDegree = 1 := by omega
  obtain ⟨y, hy⟩ := minpoly.natDegree_eq_one_iff.mp h1
  have hmem : (RatFunc.X : RatFunc K) ∈ K⟮xRatFunc K⟯ := by rw [← hy]; exact y.2
  have htop : K⟮xRatFunc K⟯ = ⊤ := by
    rw [eq_top_iff, ← RatFunc.adjoin_X]
    exact adjoin_simple_le_iff.mpr hmem
  have hfin := finrank_xRatFunc h2
  rw [htop, IntermediateField.finrank_top] at hfin
  exact absurd hfin (by norm_num)

/-- A field extension of degree `2` in characteristic `≠ 2` is separable. -/
theorem isSeparable_of_finrank_eq_two {F E : Type*} [Field F] [Field E] [Algebra F E]
    (h : Module.finrank F E = 2) (h2 : (2 : F) ≠ 0) : Algebra.IsSeparable F E := by
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  refine ⟨fun y => ?_⟩
  have hint := Algebra.IsIntegral.isIntegral (R := F) y
  have hirr := minpoly.irreducible hint
  have hmon := minpoly.monic hint
  have hle : (minpoly F y).natDegree ≤ 2 := h ▸ minpoly.natDegree_le y
  have hpos : 0 < (minpoly F y).natDegree := minpoly.natDegree_pos hint
  rw [IsSeparable, Polynomial.separable_iff_derivative_ne_zero hirr]
  intro hd
  have hc := congrArg (fun q => q.coeff ((minpoly F y).natDegree - 1)) hd
  simp only [coeff_derivative, coeff_zero] at hc
  have : (minpoly F y).natDegree - 1 + 1 = (minpoly F y).natDegree := by omega
  rw [this, hmon.coeff_natDegree, one_mul] at hc
  obtain hm | hm : (minpoly F y).natDegree = 1 ∨ (minpoly F y).natDegree = 2 := by omega
  · rw [hm] at hc
    simp at hc
  · rw [hm] at hc
    push_cast at hc
    exact h2 (by linear_combination hc)

/-- **Lemma 3.3** (separability): `K(λ) / K(x)`, `x = (λ - 1)² / (4 λ)`, is separable when
`2 ≠ 0` in `K`. -/
theorem isSeparable_xRatFunc {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    Algebra.IsSeparable K⟮xRatFunc K⟯ (RatFunc K) := by
  refine isSeparable_of_finrank_eq_two (finrank_xRatFunc h2) ?_
  intro h
  apply h2
  apply (algebraMap K K⟮xRatFunc K⟯).injective
  rw [map_ofNat, h, map_zero]

end FunctionField

end Gamma0

namespace KatzForms

open Gamma0

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [DecidableEq L] (K : KatzForms p 2 L)
  (hp2 : p ≠ 2) [CharP L p]

/-- **Lemma 3.2(c)** (last sentence, at non-cuspidal points): over an algebraically closed field
of characteristic `p ≠ 2, 3`, `δ̄` vanishes at a test object `(E, C, ω)` iff `(E, C)` is
isomorphic to `(E_{-1}, ⟨(0, 0)⟩)`, `E_{-1} : y² = x³ - x` (`j = 1728`). Thus the zero locus of
`δ̄` on the non-cuspidal points of `X₀(2)` is a single point, the point with `x = -1`. -/
theorem deltaBar_eq_zero_iff_scale_eq [IsAlgClosed L] (h3 : (3 : L) ≠ 0) (T : Test 2 L) :
    (K.deltaBar hp2).1 T = 0 ↔
      ∃ u : Lˣ, T.toPair.scale u =
        legendrePair (two_ne_zero_of_charP (L := L) hp2) h3 (neg_ne_zero.mpr one_ne_zero)
          (neg_one_ne_one_of_two_ne_zero (two_ne_zero_of_charP (L := L) hp2)) := by
  rw [K.deltaBar_eq_zero_iff hp2,
    Pair.xCoordinate_eq_neg_one_iff (two_ne_zero_of_charP (L := L) hp2) h3]

end KatzForms
