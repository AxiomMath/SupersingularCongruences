/-
Assembled by AxiomProver.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import SupersingularCongruences.EllipticCurve.PointMap

/-!
# Vélu's quotient curve

Let `W : y² = x³ + a₄ x + a₆` be a short Weierstrass elliptic curve over a field `F` and let `C` be
a finite subgroup of its points. Vélu's formulas [velu1971] give an explicit Weierstrass model of
the quotient `E / C` and of the quotient isogeny `φ : E → E / C`. For a short model, with all sums
over the nonzero points `Q = (x_Q, y_Q)` of `C`,

* `t = ∑ (3 x_Q² + a₄)` and `w = ∑ (5 x_Q³ + 3 a₄ x_Q + 2 a₆)`;
* `E / C : y² = x³ + (a₄ - 5 t) x + (a₆ - 7 w)`;
* `φ (P) = (x_P + ∑ (x_{P + Q} - x_Q), y_P + ∑ (y_{P + Q} - y_Q))` for `P ∉ C`.

These are Vélu's formulas (in the form of [washington2008, Theorem 12.16]) specialized to
`a₁ = a₂ = a₃ = 0`: Vélu sums `t_Q` and `u_Q + x_Q t_Q` over a set `S` containing the nonzero
`2`-torsion points of `C` and one point of each pair `{Q, -Q}` of the other nonzero points; since
`y_Q² = x_Q³ + a₄ x_Q + a₆` and `y_Q = 0` on `2`-torsion, these equal the sums over all nonzero
points written above. Vélu's isogeny is normalized: it pulls back the standard differential
`dx / (2y)` of `E / C` to the standard differential of `E`. That these formulas define an
elliptic curve and a surjective homomorphism with kernel `C` is the cited result
`WeierstrassCurve.VeluIsogeny` (`SupersingularCongruences.External`).

## Main definitions

* `WeierstrassCurve.veluT`, `WeierstrassCurve.veluW`: the sums `t` and `w`.
* `WeierstrassCurve.velu W C`: the short Weierstrass curve `E / C`.
-/

public section

open WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-- Vélu's sum `t = ∑_{Q ∈ C \ {0}} (3 x_Q² + a₄)` for a short Weierstrass curve. -/
noncomputable def veluT (C : AddSubgroup W.toAffine.Point) : F :=
  ∑ᶠ Q ∈ (C : Set W.toAffine.Point) \ {0}, (3 * Q.xCoord ^ 2 + W.a₄)

/-- Vélu's sum `w = ∑_{Q ∈ C \ {0}} (5 x_Q³ + 3 a₄ x_Q + 2 a₆)` for a short Weierstrass curve. -/
noncomputable def veluW (C : AddSubgroup W.toAffine.Point) : F :=
  ∑ᶠ Q ∈ (C : Set W.toAffine.Point) \ {0}, (5 * Q.xCoord ^ 3 + 3 * W.a₄ * Q.xCoord + 2 * W.a₆)

/-- Vélu's model `y² = x³ + (a₄ - 5 t) x + (a₆ - 7 w)` of the quotient `E / C` of a short
Weierstrass curve `E` by a finite subgroup `C` [velu1971]. -/
noncomputable def velu (C : AddSubgroup W.toAffine.Point) : WeierstrassCurve F where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := W.a₄ - 5 * W.veluT C
  a₆ := W.a₆ - 7 * W.veluW C

variable (C : AddSubgroup W.toAffine.Point)

@[simp] lemma velu_a₁ : (W.velu C).a₁ = 0 := (rfl)
@[simp] lemma velu_a₂ : (W.velu C).a₂ = 0 := (rfl)
@[simp] lemma velu_a₃ : (W.velu C).a₃ = 0 := (rfl)
@[simp] lemma velu_a₄ : (W.velu C).a₄ = W.a₄ - 5 * W.veluT C := (rfl)
@[simp] lemma velu_a₆ : (W.velu C).a₆ = W.a₆ - 7 * W.veluW C := (rfl)

instance : (W.velu C).IsShortNF :=
  ⟨velu_a₁ W C, velu_a₂ W C, velu_a₃ W C⟩

end WeierstrassCurve
