/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.EllipticCurve.OverClosure
public import SupersingularCongruences.EllipticCurve.LegendreHasse
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable

/-!
# The Hasse invariant of a short Weierstrass curve

For a short Weierstrass curve `E : y² = f(x)`, `f = x³ + a₄ x + a₆`, over a field of
characteristic `p`, the value of the Hasse invariant at `(E, dx / (2y))` is the coefficient of
`x^{p-1}` in `f(x)^{(p-1)/2}` [katz-mazur, Section 12.4], [silverman-aec, Section V.4]
(manuscript, Lemma 2.1(c)). This file defines this coefficient. The cited results that it vanishes
exactly on supersingular curves (`WeierstrassCurve.DeuringHasseCriterion`) and that the Deuring
polynomial has distinct roots (`Polynomial.DeuringPolynomialSeparable`) are stated in
`SupersingularCongruences.External`.
-/

public section

open Polynomial

namespace WeierstrassCurve

variable {L : Type*} [Field L]

/-- The coefficient of `x ^ (p - 1)` in `(x³ + a₄ x + a₆) ^ ((p - 1) / 2)`: the value of the Hasse
invariant at `(E, dx / (2y))` for a short Weierstrass curve `E` in characteristic `p`. -/
noncomputable def hasseCoeff (p : ℕ) (W : WeierstrassCurve L) : L :=
  ((X ^ 3 + C W.a₄ * X + C W.a₆) ^ ((p - 1) / 2)).coeff (p - 1)

lemma hasseCoeff_def (p : ℕ) (W : WeierstrassCurve L) :
    W.hasseCoeff p = ((X ^ 3 + C W.a₄ * X + C W.a₆) ^ ((p - 1) / 2)).coeff (p - 1) := (rfl)

end WeierstrassCurve
