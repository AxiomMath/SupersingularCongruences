/-
Assembled by AxiomProver.
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Data.Nat.Prime.Factorial

/-!
# The Hasse invariant of the Legendre family

For the Legendre curve `E_λ : y² = x (x - 1) (x - λ)` the Hasse invariant is the coefficient of
`x ^ (p - 1)` in `(x (x - 1) (x - λ)) ^ ((p - 1) / 2)`. The manuscript (Lemma 2.1(d)) computes this
coefficient as `(-1) ^ ((p - 1) / 2) H_p(λ)`, where
`H_p(λ) = ∑_{i=0}^{(p-1)/2} binom((p-1)/2, i)² λ^i` is the Deuring polynomial.

## Main results

* `Polynomial.deuringPolynomial R p`: the polynomial `H_p ∈ R[λ]`.
* `Polynomial.coeff_X_mul_X_sub_one_mul_X_sub_C_pow`: for every `w`, the coefficient of `X ^ (2w)`
  in `(X (X - 1) (X - λ)) ^ w` is `(-1) ^ w ∑_{i=0}^{w} binom(w, i)² λ^i`.
* `Polynomial.coeff_legendre_pow_eq_deuringPolynomial`: the case `w = (p - 1) / 2`, `p` odd.
* `Polynomial.deuringPolynomial_eval_zero`, `Polynomial.deuringPolynomial_eval_one`,
  `Polynomial.deuringPolynomial_eval_one_ne_zero`: `H_p(0) = 1` and
  `H_p(1) = binom(p - 1, (p - 1) / 2) ≠ 0` in characteristic `p`.

The identification of this coefficient with the Hasse invariant of the Legendre curve is
`Gamma0.legendreCurve_hasseCoeff` (`SupersingularCongruences.KatzForms.HasseInvariant`).
-/

public section

open Finset

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The coefficient of `X ^ k` in `(X - C r) ^ n`. -/
lemma coeff_X_sub_C_pow (r : R) (n k : ℕ) :
    ((X - C r) ^ n).coeff k = (-r) ^ (n - k) * n.choose k := by
  rw [sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow]

/-- The coefficient of `X ^ (2w)` in `(X (X - 1) (X - λ)) ^ w` is
`(-1) ^ w ∑_{i=0}^{w} binom(w, i)² λ^i` (manuscript, proof of Lemma 2.1(d)). -/
theorem coeff_X_mul_X_sub_one_mul_X_sub_C_pow (w : ℕ) (r : R) :
    ((X * (X - 1) * (X - C r)) ^ w).coeff (2 * w) =
      (-1) ^ w * ∑ i ∈ range (w + 1), ((w.choose i : R)) ^ 2 * r ^ i := by
  rw [mul_assoc, mul_pow, two_mul, coeff_X_pow_mul, mul_pow, coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi : i ≤ w := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [← C_1, coeff_X_sub_C_pow, coeff_X_sub_C_pow, Nat.sub_sub_self hi, Nat.choose_symm hi,
    neg_pow r]
  have : (-1 : R) ^ w = (-1) ^ (w - i) * (-1) ^ i := by rw [← pow_add, Nat.sub_add_cancel hi]
  rw [this]
  ring

variable (R) in
/-- The Deuring polynomial `H_p(λ) = ∑_{i=0}^{(p-1)/2} binom((p-1)/2, i)² λ^i` over `R`
(manuscript, Lemma 2.1(d)); over `R = ZMod p` its roots are the supersingular Legendre
parameters. -/
noncomputable def deuringPolynomial (p : ℕ) : R[X] :=
  ∑ i ∈ range ((p - 1) / 2 + 1), C ((((p - 1) / 2).choose i : R) ^ 2) * X ^ i

lemma eval_deuringPolynomial (p : ℕ) (r : R) :
    (deuringPolynomial R p).eval r =
      ∑ i ∈ range ((p - 1) / 2 + 1), (((p - 1) / 2).choose i : R) ^ 2 * r ^ i := by
  simp [deuringPolynomial, eval_finsetSum]

/-- `H_p(0) = 1`. -/
lemma deuringPolynomial_eval_zero (p : ℕ) : (deuringPolynomial R p).eval 0 = 1 := by
  rw [eval_deuringPolynomial, Finset.sum_range_succ']
  simp

/-- `H_p(1) = binom(2 ((p - 1) / 2), (p - 1) / 2)` (Vandermonde). -/
lemma deuringPolynomial_eval_one (p : ℕ) :
    (deuringPolynomial R p).eval 1 = ((2 * ((p - 1) / 2)).choose ((p - 1) / 2) : ℕ) := by
  rw [eval_deuringPolynomial, ← Nat.sum_range_choose_sq]
  push_cast
  simp

/-- `H_p(1) ≠ 0` in characteristic `p`: `p ∤ binom(p - 1, (p - 1) / 2)`. -/
lemma deuringPolynomial_eval_one_ne_zero {L : Type*} [Field L] {p : ℕ} [CharP L p]
    (hp : p.Prime) (hp2 : p ≠ 2) : (deuringPolynomial L p).eval 1 ≠ 0 := by
  rw [deuringPolynomial_eval_one, Nat.two_mul_div_two_of_even (hp.even_sub_one hp2), ne_eq,
    CharP.cast_eq_zero_iff L p]
  intro h
  have hk : (p - 1) / 2 ≤ p - 1 := Nat.div_le_self _ _
  have h' := Nat.choose_mul_factorial_mul_factorial hk
  have hdvd : p ∣ (p - 1).factorial := by
    rw [← h']; exact (h.mul_right _).mul_right _
  exact absurd ((hp.dvd_factorial).mp hdvd) (by have := hp.one_le; omega)

/-- **Lemma 2.1(d)** (the polynomial identity): for odd `p`, the coefficient of `x ^ (p - 1)` in
`(x (x - 1) (x - λ)) ^ ((p - 1) / 2)` equals `(-1) ^ ((p - 1) / 2) H_p(λ)`. -/
theorem coeff_legendre_pow_eq_deuringPolynomial {p : ℕ} (hp : Odd p) (r : R) :
    ((X * (X - 1) * (X - C r)) ^ ((p - 1) / 2)).coeff (p - 1) =
      (-1) ^ ((p - 1) / 2) * (deuringPolynomial R p).eval r := by
  obtain ⟨k, rfl⟩ := hp
  have h1 : 2 * k + 1 - 1 = 2 * k := by omega
  have h2 : (2 * k + 1 - 1) / 2 = k := by omega
  rw [eval_deuringPolynomial, h2, h1, coeff_X_mul_X_sub_one_mul_X_sub_C_pow]

end Polynomial
