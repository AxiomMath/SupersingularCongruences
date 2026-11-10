/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.KatzForms.LevelTwoReduction
public import SupersingularCongruences.KatzForms.Legendre
public import SupersingularCongruences.ModularCurve.LegendreNormalForm
import all SupersingularCongruences.ModularCurve.Gamma0Pair

/-!
# Larson's level-two forms on the Legendre family (manuscript, Lemmas 3.2 and 3.3)

Let `p ≥ 5`, `L` algebraically closed of characteristic `p`, and `K : KatzForms p 2 L` with the
regularity `K.LegendreRegular` of Katz forms on the Legendre family. Write `T_λ` for the test
object `(E_λ, ⟨(0, 0)⟩, dx / (2y))` (`λ ≠ 0, 1`), and `δ̄, ε̄, μ̄` for the reductions of Larson's
forms (`KatzForms.deltaBar`, `KatzForms.epsBar`, `KatzForms.muBar`).

## Main results

* `KatzForms.exists_legendre_values`: there are constants `ζ, c` with `ζ³ = 1`, `4 c² = ζ` such
  that `ε̄(T_λ) = ζ λ` and `δ̄(T_λ) = c (λ + 1)` for all `λ ≠ 0, 1` (the functions `e(λ)`,
  `h(λ)` of the proof of Lemma 3.3).
* `KatzForms.eq_of_forall_legendre`: forms on `Γ₀(2)` of the same weight are determined by their
  values on the Legendre test objects `T_λ`.
* Lemma 3.2(c), forms part: `KatzForms.deltaBar_eq_zero_iff` (`δ̄` vanishes exactly at the point
  `x = -1`), `KatzForms.exists_epsBar_legendre_eq_eval` (`ε̄` vanishes at the cusp `λ = 0` of the
  Legendre line), and the `q`-expansion `R₂ = q + 24 q² + 300 q³ + ⋯`
  (`LevelOne.coeff_expandSeries_two_integralDiscriminant`).

## Proof route

From Lemma 3.1 modulo `p` and the explicit values `Δ(T_λ) = 16 λ² (λ - 1)²`,
`x(T_λ) = (λ - 1)² / (4 λ)`: `ε̄(T_λ)³ = λ³` and `δ̄(T_λ)² = ε̄(T_λ) (λ + 1)² / (4 λ)`. By
regularity, `ε̄(T_λ)` and `δ̄(T_λ)` are rational functions of `λ`; a rational function whose
`n`-th power is that of a fixed rational function on infinitely many `λ` is a constant
`n`-th root of unity times it (`LevelTwo.exists_eq_C_mul_of_pow_eval_eq`).
-/

public section

open Polynomial Gamma0

namespace LevelTwo

variable {L : Type*} [Field L]

/-- If `P(λ)ⁿ = G(λ)ⁿ` for infinitely many `λ`, then `P = ζ G` for an `n`-th root of unity `ζ`. -/
theorem exists_eq_C_mul_of_pow_eval_eq {n : ℕ} (hn : 0 < n) {P G : L[X]} {S : Set L}
    (hS : S.Infinite) (h : ∀ x ∈ S, P.eval x ^ n = G.eval x ^ n) :
    ∃ ζ : L, ζ ^ n = 1 ∧ P = C ζ * G := by
  classical
  by_contra hne
  push Not at hne
  by_cases hG : G = 0
  · apply hne 1 (one_pow n)
    rw [hG, mul_zero]
    refine eq_zero_of_infinite_isRoot P (hS.mono fun x hx => ?_)
    have := h x hx
    rw [hG, eval_zero, zero_pow hn.ne'] at this
    exact pow_eq_zero_iff hn.ne' |>.mp this
  · apply hS
    refine ((finite_setOfPred_isRoot hG).union
      ((nthRoots n (1 : L)).toFinset.finite_toSet.biUnion fun ζ hζ =>
        finite_setOfPred_isRoot (sub_ne_zero.mpr (hne ζ ?_)))).subset ?_
    · exact (mem_nthRoots hn).mp (Multiset.mem_toFinset.mp hζ)
    · intro x hx
      by_cases hGx : G.eval x = 0
      · exact Or.inl hGx
      · right
        have hx' := h x hx
        refine Set.mem_biUnion (x := P.eval x / G.eval x) ?_ ?_
        · rw [Finset.mem_coe, Multiset.mem_toFinset, mem_nthRoots hn, div_pow, hx',
            div_self (pow_ne_zero _ hGx)]
        · simp only [Set.mem_ofPred_eq, IsRoot, eval_sub, eval_mul, eval_C]
          field_simp
          ring

/-- The set `L \ {0, 1}` of non-cuspidal Legendre parameters is infinite. -/
lemma infinite_setOf_ne_zero_ne_one [Infinite L] : {x : L | x ≠ 0 ∧ x ≠ 1}.Infinite := by
  have : {x : L | x ≠ 0 ∧ x ≠ 1} = ({0, 1} : Set L)ᶜ := by
    ext x; simp
  rw [this]
  exact (Set.toFinite _).infinite_compl

/-- A rational function `f(λ) = P(λ) / (λ^a (λ - 1)^b)` (on `λ ≠ 0, 1`) whose `n`-th power is
`g(λ)ⁿ` for a polynomial `g` is `ζ g` for an `n`-th root of unity `ζ`. -/
theorem exists_eq_mul_of_pow_eq [Infinite L] {n : ℕ} (hn : 0 < n) {f : L → L} (P : L[X])
    (a b : ℕ) (hf : ∀ x : L, x ≠ 0 → x ≠ 1 → f x = P.eval x / (x ^ a * (x - 1) ^ b)) (g : L[X])
    (hfg : ∀ x : L, x ≠ 0 → x ≠ 1 → f x ^ n = g.eval x ^ n) :
    ∃ ζ : L, ζ ^ n = 1 ∧ ∀ x : L, x ≠ 0 → x ≠ 1 → f x = ζ * g.eval x := by
  obtain ⟨ζ, hζ, hP⟩ := exists_eq_C_mul_of_pow_eval_eq hn (G := g * (X ^ a * (X - 1) ^ b))
    (P := P) infinite_setOf_ne_zero_ne_one (fun x ⟨h0, h1⟩ => by
      have hD : x ^ a * (x - 1) ^ b ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ h0) (pow_ne_zero _ (sub_ne_zero.mpr h1))
      have := hfg x h0 h1
      rw [hf x h0 h1, div_pow, div_eq_iff (pow_ne_zero _ hD)] at this
      simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one]
      rw [this]; ring)
  refine ⟨ζ, hζ, fun x h0 h1 => ?_⟩
  have hD : x ^ a * (x - 1) ^ b ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ h0) (pow_ne_zero _ (sub_ne_zero.mpr h1))
  rw [hf x h0 h1, hP]
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
  field_simp

end LevelTwo

namespace Gamma0.Test

variable {ℓ : ℕ} {L : Type*} [Field L] [DecidableEq L]

lemma scale_eq_smulDiff (T : Test ℓ L) (u : Lˣ) :
    T.scale u = (⟨T.toPair.scale u, 1⟩ : Test ℓ L).smulDiff (T.diff * u) := by
  simp only [scale, smulDiff, mul_one]

@[simp] lemma scale_toPair (T : Test ℓ L) (u : Lˣ) : (T.scale u).toPair = T.toPair.scale u := by
  simp only [scale]

lemma eq_smulDiff (T : Test ℓ L) : T = (⟨T.toPair, 1⟩ : Test ℓ L).smulDiff T.diff := by
  simp only [smulDiff, mul_one]

end Gamma0.Test

namespace KatzForms

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [DecidableEq L] [CharP L p]
  (K : KatzForms p 2 L) (hp2 : p ≠ 2) (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0)

omit [Fact p.Prime] [CharP L p] in
/-- The value of a form of weight `k` at a test object `T` in terms of `T.toPair.scale u`. -/
lemma apply_eq_of_scale_eq {ℓ : ℕ} (K : KatzForms p ℓ L) {k : ℤ} {f : Test ℓ L → L}
    (hf : f ∈ K.form k) (T : Test ℓ L) (u : Lˣ) :
    f T = ((T.diff * u : Lˣ) : L) ^ (-k) * f ⟨T.toPair.scale u, 1⟩ := by
  rw [← K.apply_scale hf T u, Test.scale_eq_smulDiff, K.apply_smulDiff hf]

omit [Fact p.Prime] [CharP L p] in
include h2 h3 in
/-- Forms on `Γ₀(2)` of the same weight are determined by their values on the Legendre test
objects `(E_λ, ⟨(0, 0)⟩, dx / (2y))`, `λ ≠ 0, 1` (Legendre normal form). -/
theorem eq_of_forall_legendre [IsAlgClosed L] {k : ℤ} {f g : Test 2 L → L} (hf : f ∈ K.form k)
    (hg : g ∈ K.form k)
    (h : ∀ (lam : L) (h0 : lam ≠ 0) (h1 : lam ≠ 1),
      f ⟨legendrePair h2 h3 h0 h1, 1⟩ = g ⟨legendrePair h2 h3 h0 h1, 1⟩) : f = g := by
  funext T
  obtain ⟨lam, h0, h1, u, hu⟩ := Pair.exists_scale_eq_legendrePair h2 h3 T.toPair
  rw [apply_eq_of_scale_eq K hf T u, apply_eq_of_scale_eq K hg T u, hu, h lam h0 h1]

omit [Fact p.Prime] [CharP L p] in
include h2 h3 in
lemma legendre_discriminantRule {lam : L} (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    discriminantRule (⟨legendrePair h2 h3 h0 h1, 1⟩ : Test 2 L) = 16 * lam ^ 2 * (lam - 1) ^ 2 := by
  rw [discriminantRule_apply]
  simp only [Units.val_one, one_pow, inv_one, one_mul]
  rw [legendrePair_curve]
  exact legendreCurve_Δ h3 lam

include h2 h3 in
/-- On the Legendre family, `ε̄(T_λ)³ = λ³` and `δ̄(T_λ)² = ε̄(T_λ) (λ + 1)² / (4 λ)`. -/
lemma legendre_epsBar_pow_three {lam : L} (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    (K.epsBar hp2).1 ⟨legendrePair h2 h3 h0 h1, 1⟩ ^ 3 = lam ^ 3 ∧
      (K.deltaBar hp2).1 ⟨legendrePair h2 h3 h0 h1, 1⟩ ^ 2 =
        (K.epsBar hp2).1 ⟨legendrePair h2 h3 h0 h1, 1⟩ * ((lam + 1) ^ 2 / (4 * lam)) := by
  set T : Test 2 L := ⟨legendrePair h2 h3 h0 h1, 1⟩
  have he := K.epsBar_ne_zero hp2 T
  have hx := K.veluRatio_eq_muBar_div_epsBar hp2 T
  have hx1 := K.veluRatio_add_one_eq hp2 T
  have hxl : 64 * T.toPair.veluRatio = (lam - 1) ^ 2 / (4 * lam) := by
    rw [← Pair.xCoordinate_eq_mul_veluRatio]; exact xCoordinate_legendrePair h2 h3 h0 h1
  have hxl1 : 64 * T.toPair.veluRatio + 1 = (lam + 1) ^ 2 / (4 * lam) := by
    rw [← Pair.xCoordinate_eq_mul_veluRatio]; exact xCoordinate_legendrePair_add_one h2 h3 h0 h1
  have hΔ := K.discriminantRule_eq_muBar_mul_epsBar_sq hp2 T
  rw [legendre_discriminantRule h2 h3 h0 h1] at hΔ
  have h4 : (4 : L) ≠ 0 := by rw [show (4 : L) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have h16 : (16 : L) ≠ 0 := by rw [show (16 : L) = 4 * 4 by norm_num]; exact mul_ne_zero h4 h4
  have hl1 : lam - 1 ≠ 0 := sub_ne_zero.mpr h1
  constructor
  · have hmu : K.muBar hp2 T = (K.epsBar hp2).1 T * ((lam - 1) ^ 2 / (4 * lam)) := by
      rw [← hxl, hx]; field_simp
    rw [hmu] at hΔ
    have hq : (lam - 1) ^ 2 / (4 * lam) * (4 * lam) = (lam - 1) ^ 2 :=
      div_mul_cancel₀ _ (mul_ne_zero h4 h0)
    have : 16 * (lam - 1) ^ 2 * ((K.epsBar hp2).1 T ^ 3 - lam ^ 3) = 0 := by
      linear_combination (-lam) * hΔ - 16 * (K.epsBar hp2).1 T ^ 3 * hq
    have h' := (mul_eq_zero.mp this).resolve_left (mul_ne_zero h16 (pow_ne_zero _ hl1))
    linear_combination h'
  · rw [← hxl1, hx1]; field_simp

include h2 h3 in
/-- **The values of `δ̄, ε̄` on the Legendre family** (proof of Lemma 3.3): there are `ζ, c ∈ L`
with `ζ³ = 1` and `4 c² = ζ` such that `ε̄(E_λ, ⟨(0, 0)⟩, dx / (2y)) = ζ λ` and
`δ̄(E_λ, ⟨(0, 0)⟩, dx / (2y)) = c (λ + 1)` for all `λ ≠ 0, 1`. -/
theorem exists_legendre_values [IsAlgClosed L] (hK : K.LegendreRegular) :
    ∃ ζ c : L, 4 * c ^ 2 = ζ ∧ ζ ^ 3 = 1 ∧
      ∀ (lam : L) (h0 : lam ≠ 0) (h1 : lam ≠ 1),
        (K.epsBar hp2).1 ⟨legendrePair h2 h3 h0 h1, 1⟩ = ζ * lam ∧
          (K.deltaBar hp2).1 ⟨legendrePair h2 h3 h0 h1, 1⟩ = c * (lam + 1) := by
  classical
  have h4 : (4 : L) ≠ 0 := by rw [show (4 : L) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  -- `ε̄` as a function of `λ`
  let e : L → L := fun lam =>
    if h : lam ≠ 0 ∧ lam ≠ 1 then (K.epsBar hp2).1 ⟨legendrePair h2 h3 h.1 h.2, 1⟩ else 0
  let d : L → L := fun lam =>
    if h : lam ≠ 0 ∧ lam ≠ 1 then (K.deltaBar hp2).1 ⟨legendrePair h2 h3 h.1 h.2, 1⟩ else 0
  have he : ∀ lam (h0 : lam ≠ 0) (h1 : lam ≠ 1),
      e lam = (K.epsBar hp2).1 ⟨legendrePair h2 h3 h0 h1, 1⟩ := fun lam h0 h1 => by
    exact dite_eq_left_of_eq_true (eq_true ⟨h0, h1⟩)
  have hd : ∀ lam (h0 : lam ≠ 0) (h1 : lam ≠ 1),
      d lam = (K.deltaBar hp2).1 ⟨legendrePair h2 h3 h0 h1, 1⟩ := fun lam h0 h1 => by
    exact dite_eq_left_of_eq_true (eq_true ⟨h0, h1⟩)
  obtain ⟨Pe, a, b, hPe⟩ := hK.exists_eq_div (K.epsBar hp2).2 h2 h3
  obtain ⟨ζ, hζ, hζe⟩ := LevelTwo.exists_eq_mul_of_pow_eq (f := e) (n := 3) (by norm_num) Pe a b
    (fun x h0 h1 => by rw [he x h0 h1, hPe x h0 h1]) X
    (fun x h0 h1 => by
      rw [he x h0 h1, eval_X]; exact (legendre_epsBar_pow_three K hp2 h2 h3 h0 h1).1)
  have hζ0 : ζ ≠ 0 := by rintro rfl; norm_num at hζ
  obtain ⟨c₀, hc₀⟩ := IsAlgClosed.exists_pow_nat_eq (ζ / 4) two_pos
  obtain ⟨Pd, a', b', hPd⟩ := hK.exists_eq_div (K.deltaBar hp2).2 h2 h3
  obtain ⟨ζ', hζ', hζd⟩ := LevelTwo.exists_eq_mul_of_pow_eq (f := d) (n := 2) (by norm_num) Pd a' b'
    (fun x h0 h1 => by rw [hd x h0 h1, hPd x h0 h1]) (C c₀ * (X + 1))
    (fun x h0 h1 => by
      rw [hd x h0 h1, (legendre_epsBar_pow_three K hp2 h2 h3 h0 h1).2, ← he x h0 h1,
        hζe x h0 h1]
      simp only [eval_X, eval_mul, eval_C, eval_add, eval_one, mul_pow, hc₀]
      field_simp)
  refine ⟨ζ, ζ' * c₀, ?_, hζ, fun lam h0 h1 => ⟨?_, ?_⟩⟩
  · rw [mul_pow, hζ', one_mul, hc₀]; field_simp
  · rw [← he lam h0 h1, hζe lam h0 h1, eval_X]
  · rw [← hd lam h0 h1, hζd lam h0 h1]
    simp only [eval_mul, eval_C, eval_add, eval_X, eval_one]
    ring

/-! ### Lemma 3.2(c), forms part -/

/-- **Lemma 3.2(c)**: `δ̄` vanishes at a test object iff its point of `X₀(2)` is the point
`x = -1` (`x + 1 = δ̄² / ε̄` with `ε̄ ≠ 0`). -/
theorem deltaBar_eq_zero_iff (T : Test 2 L) :
    (K.deltaBar hp2).1 T = 0 ↔ T.toPair.xCoordinate = -1 := by
  have he := K.epsBar_ne_zero hp2 T
  have h := K.veluRatio_add_one_eq hp2 T
  rw [← Pair.xCoordinate_eq_mul_veluRatio] at h
  rw [show T.toPair.xCoordinate = -1 ↔ T.toPair.xCoordinate + 1 = 0 from
      ⟨fun h => by rw [h]; ring, fun h => by linear_combination h⟩, h, div_eq_zero_iff,
    or_iff_left he, pow_eq_zero_iff two_ne_zero]

/-- **Lemma 3.2(c)**: `Δ`, `μ̄` and `ε̄` do not vanish at any test object (non-cuspidal point). -/
theorem discriminantRule_muBar_epsBar_ne_zero (T : Test 2 L) :
    discriminantRule T ≠ 0 ∧ K.muBar hp2 T ≠ 0 ∧ (K.epsBar hp2).1 T ≠ 0 :=
  ⟨discriminantRule_ne_zero T, K.muBar_ne_zero hp2 T, K.epsBar_ne_zero hp2 T⟩

include h2 h3 in
/-- **Lemma 3.2(c)** (`ε̄` vanishes at a cusp): on the Legendre line, `ε̄(T_λ) = e(λ)` for a
nonzero polynomial `e = ζ X` with `e(0) = 0`, i.e. `ε̄` vanishes at the cusp `λ = 0` (lying over
the cusp `0` of `X₀(2)`, where `x = (λ - 1)² / (4 λ)` has its pole). -/
theorem exists_epsBar_legendre_eq_eval [IsAlgClosed L] (hK : K.LegendreRegular) :
    ∃ e : L[X], e ≠ 0 ∧ e.eval 0 = 0 ∧
      ∀ (lam : L) (h0 : lam ≠ 0) (h1 : lam ≠ 1),
        (K.epsBar hp2).1 ⟨legendrePair h2 h3 h0 h1, 1⟩ = e.eval lam := by
  obtain ⟨ζ, c, -, hζ, hv⟩ := K.exists_legendre_values hp2 h2 h3 hK
  have hζ0 : ζ ≠ 0 := by rintro rfl; norm_num at hζ
  refine ⟨C ζ * X, mul_ne_zero (C_ne_zero.mpr hζ0) X_ne_zero, by simp, fun lam h0 h1 => ?_⟩
  rw [(hv lam h0 h1).1]
  simp

end KatzForms

namespace LevelOne

open PowerSeries

lemma integralDiscriminant_coeff_le_three :
    integralDiscriminant.coeff 0 = 0 ∧ integralDiscriminant.coeff 1 = 1 ∧
      integralDiscriminant.coeff 2 = -24 ∧ integralDiscriminant.coeff 3 = 252 := by
  obtain ⟨c0, c1, c2, c3⟩ := LevelTwoForms.coeff_discriminant
  have h := isIntegralQExpansion_discriminant.coeff
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := h 0; rw [c0] at this; exact_mod_cast this.symm
  · have := h 1; rw [c1] at this; exact_mod_cast this.symm
  · have := h 2; rw [c2] at this; exact_mod_cast this.symm
  · have := h 3; rw [c3] at this; exact_mod_cast this.symm

/-- **Lemma 3.2(a)**: `R₂ = V₂(Δ) / Δ = q + 24 q² + 300 q³ + ⋯`, as the congruence
`Δ(q²) ≡ Δ(q) · (q + 24 q² + 300 q³) (mod q⁵)` of integral `q`-expansions (which determines the
coefficients of `q, q², q³` of `R₂ = Δ(q²) / Δ(q)`, `Δ(q) = q + O(q²)`). -/
theorem coeff_expandSeries_two_integralDiscriminant (n : ℕ) (hn : n ≤ 4) :
    (expandSeries 2 integralDiscriminant).coeff n =
      (integralDiscriminant *
        (PowerSeries.X + 24 * PowerSeries.X ^ 2 + 300 * PowerSeries.X ^ 3)).coeff n := by
  obtain ⟨c0, c1, c2, c3⟩ := integralDiscriminant_coeff_le_three
  rw [coeff_expandSeries, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  interval_cases n <;>
    simp [Finset.sum_range_succ, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, c0, c1, c2, c3]

end LevelOne
