/-
Assembled by AxiomProver.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Supersingular curves and Deuring models over an algebraic closure of `𝔽_p`

Let `L` be an algebraically closed field of characteristic `p` (in applications, an algebraic
closure of `𝔽_p`).

* `WeierstrassCurve.IsSupersingularOver p W`: `W` has no nonzero `p`-torsion point over `L`. Over
  an algebraically closed field this is supersingularity [silverman-aec, Theorem V.3.1(a)].
* `WeierstrassCurve.IsDeuringModelOver p W`: the short Weierstrass curve `W` has coefficients in
  `𝔽_{p²}` (they are fixed by `x ↦ x ^ (p ^ 2)`) and its `p²`-power Frobenius endomorphism
  `π_E (x, y) = (x ^ (p ^ 2), y ^ (p ^ 2))` equals `[-p]`, i.e. `π_E (P) = -(p • P)` for every
  point `P` over `L`. This is the manuscript's notion of a *Deuring model* (Section 1), read over
  `L`; an endomorphism is determined by its action on points over `L`.
-/

public section

open WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {L : Type*} [Field L] [DecidableEq L]

/-- `W` has no nonzero `p`-torsion point over `L`. For `L` algebraically closed of characteristic
`p` this is supersingularity of `W` [silverman-aec, Theorem V.3.1(a)]. -/
def IsSupersingularOver (p : ℕ) (W : WeierstrassCurve L) : Prop :=
  ∀ P : W.toAffine.Point, p • P = 0 → P = 0

/-- `W` is a *Deuring model*: its coefficients lie in `𝔽_{p²}` and its `p²`-power Frobenius
endomorphism `(x, y) ↦ (x ^ (p ^ 2), y ^ (p ^ 2))` is `[-p]` on the points over `L`. -/
structure IsDeuringModelOver (p : ℕ) (W : WeierstrassCurve L) : Prop where
  a₁_pow : W.a₁ ^ p ^ 2 = W.a₁
  a₂_pow : W.a₂ ^ p ^ 2 = W.a₂
  a₃_pow : W.a₃ ^ p ^ 2 = W.a₃
  a₄_pow : W.a₄ ^ p ^ 2 = W.a₄
  a₆_pow : W.a₆ ^ p ^ 2 = W.a₆
  frobenius_eq : ∀ (x y : L) (h : W.toAffine.Nonsingular x y),
    ∃ h' : W.toAffine.Nonsingular (x ^ p ^ 2) (y ^ p ^ 2),
      Point.some _ _ h' = -(p • Point.some x y h)

end WeierstrassCurve
