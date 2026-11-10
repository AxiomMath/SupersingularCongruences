/-
Assembled by AxiomProver.
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.MvPolynomial.Basic
public import SupersingularCongruences.Algebra.UniformMultiplicity

/-!
# Larson's level-two ring and the factorization of `L₂(Δ^t)`

By [larson2020, Section 3], the ring of modular forms modulo `p` on `Γ₀(2)` is the weighted
polynomial ring `𝔽_p[δ, ε]` with `δ` of weight `2` and `ε` of weight `4`; put `μ = δ² - ε`.
By Lemma 3.1 of the manuscript, `Δ = 64 μ ε²` and `V₂(Δ) = μ² ε` there, so that
`L₂(Δ^t) = V₂(Δ)^t - Δ^t = (μ² ε)^t - (64 μ ε²)^t`.

We model `K[δ, ε]` as `MvPolynomial (Fin 2) K` (with `δ = X 0`, `ε = X 1`; the grading plays no
role in the divisibility arguments) and *define* `LevelTwo.larsonL2 K t` as the polynomial
`(μ² ε)^t - (64 μ ε²)^t`. Its identification with the modular form `L₂(Δ^t)` (Lemma 3.1 of the
manuscript) is proved elsewhere: over `ℂ` in `LevelTwoForms.Bridge`, and for Katz forms modulo
`p` as `KatzForms.aeval_larsonL2`.

## Main results

* `LevelTwo.larsonL2_eq`: `L₂(Δ^t) = μ^t ε^t (μ^t - 64^t ε^t)` (Proposition 5.2, first identity).
* `LevelTwo.mu_pow_sub_eq_prod`: in characteristic `p` over an algebraically closed field, with
  `t = p ^ n * t'`, `p ∤ t'`, one has `μ^t - 64^t ε^t = ∏_{ρ ∈ W} (μ - ρ ε)^(p^n)`, where `W` is
  the set of the `t'` roots of `X^t' = 64^t'` (Proposition 5.2, second identity).
-/

public section

open MvPolynomial

namespace LevelTwo

variable (K : Type*) [Field K]

/-- Larson's weight-`2` generator `δ` of the level-two ring, as the variable `X 0`. -/
noncomputable def delta : MvPolynomial (Fin 2) K := X 0

/-- Larson's weight-`4` generator `ε` of the level-two ring, as the variable `X 1`. -/
noncomputable def eps : MvPolynomial (Fin 2) K := X 1

/-- `μ = δ² - ε`. -/
noncomputable def mu : MvPolynomial (Fin 2) K := delta K ^ 2 - eps K

/-- The polynomial representing `L₂(Δ^t) = V₂(Δ)^t - Δ^t`, using `V₂(Δ) = μ² ε` and
`Δ = 64 μ ε²` (Lemma 3.1 of the manuscript). -/
noncomputable def larsonL2 (t : ℕ) : MvPolynomial (Fin 2) K :=
  (mu K ^ 2 * eps K) ^ t - (64 * mu K * eps K ^ 2) ^ t

variable {K}

lemma mu_def : mu K = delta K ^ 2 - eps K := (rfl)

lemma larsonL2_def (t : ℕ) :
    larsonL2 K t = (mu K ^ 2 * eps K) ^ t - (64 * mu K * eps K ^ 2) ^ t := (rfl)

@[simp] lemma eval_delta (x : Fin 2 → K) : eval x (delta K) = x 0 := by simp [delta]

@[simp] lemma eval_eps (x : Fin 2 → K) : eval x (eps K) = x 1 := by simp [eps]

@[simp] lemma eval_mu (x : Fin 2 → K) : eval x (mu K) = x 0 ^ 2 - x 1 := by
  simp [mu]

lemma map_delta {L : Type*} [Field L] (f : K →+* L) : map f (delta K) = delta L := by
  simp [delta]

lemma map_eps {L : Type*} [Field L] (f : K →+* L) : map f (eps K) = eps L := by
  simp [eps]

lemma map_mu {L : Type*} [Field L] (f : K →+* L) : map f (mu K) = mu L := by
  simp [mu, map_delta, map_eps]

lemma map_larsonL2 {L : Type*} [Field L] (f : K →+* L) (t : ℕ) :
    map f (larsonL2 K t) = larsonL2 L t := by
  simp [larsonL2, map_mu, map_eps]

/-- `μ + ε = δ²`. -/
lemma mu_add_eps : mu K + eps K = delta K ^ 2 := by
  simp [mu]

/-- The factor `μ - ρ ε` at `ρ = -1` is `δ²`. -/
lemma mu_sub_neg_one_mul_eps : mu K - C (-1) * eps K = delta K ^ 2 := by
  simp [mu]

lemma delta_ne_zero : delta K ≠ 0 := X_ne_zero _

lemma eps_ne_zero : eps K ≠ 0 := X_ne_zero _

/-- **Proposition 5.2**, first identity: `L₂(Δ^t) = μ^t ε^t (μ^t - 64^t ε^t)`. -/
theorem larsonL2_eq (t : ℕ) :
    larsonL2 K t = mu K ^ t * eps K ^ t * (mu K ^ t - 64 ^ t * eps K ^ t) := by
  rw [larsonL2]
  ring

/-- Homogenization of a split polynomial `X ^ m - c` (with `m = #W`) over an infinite field:
`a ^ m - c e ^ m = ∏_{ρ ∈ W} (a - ρ e)` in any commutative `K`-algebra. -/
theorem pow_sub_mul_pow_eq_prod [Infinite K] {W : Finset K} {c : K}
    (hW : (Polynomial.X ^ W.card - Polynomial.C c : Polynomial K) =
      ∏ ρ ∈ W, (Polynomial.X - Polynomial.C ρ))
    {A : Type*} [CommRing A] [Algebra K A] (a e : A) :
    a ^ W.card - algebraMap K A c * e ^ W.card = ∏ ρ ∈ W, (a - algebraMap K A ρ * e) := by
  have hpoly : (X 0 ^ W.card - C c * X 1 ^ W.card : MvPolynomial (Fin 2) K) =
      ∏ ρ ∈ W, (X 0 - C ρ * X 1) := by
    apply MvPolynomial.funext
    intro x
    simp only [map_sub, map_mul, map_pow, eval_X, eval_C, map_prod]
    by_cases hx : x 1 = 0
    · rw [hx]
      simp only [mul_zero, sub_zero, Finset.prod_const]
      rcases Nat.eq_zero_or_pos W.card with h0 | hpos
      · have hc : c = 0 := by
          have := congrArg (Polynomial.eval 0) hW
          rw [Finset.card_eq_zero.mp h0] at this
          simpa using this
        simp [hc, h0]
      · rw [zero_pow hpos.ne', mul_zero, sub_zero]
    · have key := congrArg (Polynomial.eval (x 0 / x 1)) hW
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C, Polynomial.eval_prod] at key
      have e1 : x 0 ^ W.card - c * x 1 ^ W.card = x 1 ^ W.card * ((x 0 / x 1) ^ W.card - c) := by
        rw [div_pow]
        field_simp
      have e2 : ∏ ρ ∈ W, (x 0 - ρ * x 1) = ∏ ρ ∈ W, (x 1 * (x 0 / x 1 - ρ)) := by
        refine Finset.prod_congr rfl fun ρ _ => ?_
        field_simp
      rw [e1, e2, Finset.prod_mul_distrib, Finset.prod_const, key]
  have := congrArg (aeval ![a, e]) hpoly
  simpa [map_prod, Algebra.smul_def] using this

variable (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K] [DecidableEq K]

/-- The root set `W = {ρ : ρ ^ t' = 64 ^ t'}` of Proposition 5.2. -/
noncomputable abbrev rootSet64 (K : Type*) [Field K] [DecidableEq K] (t' : ℕ) : Finset K :=
  (Polynomial.X ^ t' - Polynomial.C (64 ^ t') : Polynomial K).roots.toFinset

/-- **Proposition 5.2**, second identity: for `t = p ^ n * t'` with `p ∤ t'` and `64 ≠ 0` in `K`,
`μ^t - 64^t ε^t = ∏_{ρ ∈ W} (μ - ρ ε)^(p^n)`, where `W = {ρ : ρ ^ t' = 64 ^ t'}` has
exactly `t'` elements, none of them zero. -/
theorem mu_pow_sub_eq_prod (h64 : (64 : K) ≠ 0) {n t' : ℕ} (ht' : ¬ p ∣ t') :
    mu K ^ (p ^ n * t') - 64 ^ (p ^ n * t') * eps K ^ (p ^ n * t') =
      ∏ ρ ∈ rootSet64 K t', (mu K - C ρ * eps K) ^ p ^ n := by
  have hb : (64 : K) ^ t' ≠ 0 := pow_ne_zero _ h64
  have hcard := Polynomial.card_roots_toFinset_X_pow_sub_C p ht' hb
  have hprod := Polynomial.X_pow_sub_C_eq_prod_roots p ht' hb
  have hhom := pow_sub_mul_pow_eq_prod (W := rootSet64 K t') (c := 64 ^ t')
    (by rw [hcard]; exact hprod) (mu K) (eps K)
  rw [hcard] at hhom
  have e1 : mu K ^ (p ^ n * t') = (mu K ^ t') ^ p ^ n := by rw [← pow_mul, mul_comm]
  have e2 : (64 : MvPolynomial (Fin 2) K) ^ (p ^ n * t') * eps K ^ (p ^ n * t') =
      (algebraMap K _ (64 ^ t') * eps K ^ t') ^ p ^ n := by
    rw [mul_pow, algebraMap_eq, map_pow, map_ofNat, ← pow_mul, ← pow_mul, mul_comm t']
  rw [e1, e2, ← sub_pow_char_pow, hhom, Finset.prod_pow]
  simp [algebraMap_eq]

omit [Fact p.Prime] [CharP K p] in
/-- `W` has exactly `t'` elements. -/
theorem card_rootSet64 (h64 : (64 : K) ≠ 0) {t' : ℕ} (ht' : ¬ p ∣ t') [Fact p.Prime]
    [CharP K p] : (rootSet64 K t').card = t' :=
  Polynomial.card_roots_toFinset_X_pow_sub_C p ht' (pow_ne_zero _ h64)

omit [Fact p.Prime] [CharP K p] [IsAlgClosed K] in
/-- Membership in `W`: `ρ ∈ W ↔ ρ ^ t' = 64 ^ t'` (for `t' ≠ 0`). -/
theorem mem_rootSet64 {t' : ℕ} (ht' : t' ≠ 0) {ρ : K} : ρ ∈ rootSet64 K t' ↔ ρ ^ t' = 64 ^ t' := by
  rw [Multiset.mem_toFinset, Polynomial.mem_roots
    (Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero ht') _)]
  simp [sub_eq_zero]

/-- **Proposition 5.2** (combined): `L₂(Δ^t) = μ^t ε^t ∏_{ρ ∈ W} (μ - ρ ε)^(p^n)`. -/
theorem larsonL2_eq_prod (h64 : (64 : K) ≠ 0) {n t' : ℕ} (ht' : ¬ p ∣ t') :
    larsonL2 K (p ^ n * t') = mu K ^ (p ^ n * t') * eps K ^ (p ^ n * t') *
      ∏ ρ ∈ rootSet64 K t', (mu K - C ρ * eps K) ^ p ^ n := by
  rw [larsonL2_eq, mu_pow_sub_eq_prod p h64 ht']

end LevelTwo
