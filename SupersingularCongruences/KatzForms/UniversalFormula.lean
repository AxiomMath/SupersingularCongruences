/-
Assembled by AxiomProver.
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import SupersingularCongruences.ModularCurve.Gamma0Pair
import all SupersingularCongruences.Isogeny.Velu

/-!
# Rules on `Γ₀(ℓ)` given by universal formulas

Let `E : y² = x³ + a₄ x + a₆` be a short Weierstrass curve, `C ⊆ E` a subgroup of order `ℓ` and
`ω = λ · dx / (2y)`. A *universal formula* of weight `k` is a polynomial `F`, with coefficients in
`L`, in the variables

* `a₄` (weight `4`) and `a₆` (weight `6`), and
* the traces `∑_{Q ∈ C \ {0}} g(a₄, a₆, x_Q)` (weight `j`), for every polynomial `g(A, B, X)`
  weighted homogeneous of degree `j` for the weights `4, 6, 2`,

which is weighted homogeneous of degree `k`. The associated rule is
`(E, C, λ ω_E) ↦ λ^{-k} F(a₄, a₆, traces)` (`Gamma0.formulaRule`).

Such formulas make sense over every base: for an elliptic curve `E` over a ring `R` in which `6`
is invertible, with a nowhere vanishing invariant differential `ω`, there is a unique Weierstrass
equation `y² = x³ + a₄ x + a₆` with `ω = dx / (2y)`; and when `ℓ` is
invertible on `R`, `C \ {0}` is a closed subscheme of the affine part `E \ {0}`, finite étale over
`R`, so the trace of the regular function `g(a₄, a₆, x)` along it is an element of `R`. Over an
algebraically closed field this trace is the sum over the `ℓ - 1` nonzero points of `C`. Both
facts are elementary properties of the objects modelled, for which no precise locator in a cited
work is given (see the field `KatzForms.formulaRule_mem`).

The main result here is that Vélu's discriminant `Δ(E / C, ω')`, `φ^* ω' = ω`, is the rule of a
universal formula of weight `12` (`Gamma0.formulaRule_veluFormula`): Vélu's sums `t` and `w` are
traces over `C \ {0}` of `3 x² + a₄` and `5 x³ + 3 a₄ x + 2 a₆`.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine MvPolynomial

namespace Gamma0

/-- The variables of universal formulas: the Weierstrass coefficients `a₄`, `a₆`, and the trace
over `C \ {0}` of a polynomial `g(a₄, a₆, x)` weighted homogeneous of degree `j` for the weights
`4, 6, 2` of `a₄, a₆, x`. -/
inductive FormulaVar (L : Type*) [CommSemiring L] where
  /-- The Weierstrass coefficient `a₄`. -/
  | a₄ : FormulaVar L
  /-- The Weierstrass coefficient `a₆`. -/
  | a₆ : FormulaVar L
  /-- The trace `∑_{Q ∈ C \ {0}} g(a₄, a₆, x_Q)`. -/
  | trace (g : MvPolynomial (Fin 3) L) (j : ℕ) (hg : g.IsWeightedHomogeneous ![4, 6, 2] j) :
      FormulaVar L

namespace FormulaVar

variable {L : Type*} [CommSemiring L]

/-- The weight of a variable: `4` for `a₄`, `6` for `a₆`, `j` for the trace of a polynomial of
weighted degree `j`. -/
def weight : FormulaVar L → ℕ
  | a₄ => 4
  | a₆ => 6
  | trace _ j _ => j

end FormulaVar

variable {ℓ : ℕ} {L : Type*} [Field L] [DecidableEq L]

/-- The values of the variables of universal formulas on a pair `(E, C)`. -/
noncomputable def Pair.formulaEval (P : Pair ℓ L) : FormulaVar L → L
  | .a₄ => P.curve.a₄
  | .a₆ => P.curve.a₆
  | .trace g _ _ => ∑ᶠ Q ∈ (P.subgroup : Set P.curve.toAffine.Point) \ {0},
      MvPolynomial.eval ![P.curve.a₄, P.curve.a₆, Q.xCoord] g

/-- The rule `(E, C, λ ω_E) ↦ λ^{-k} F(a₄, a₆, traces)` of a universal formula `F` of weight `k`. -/
noncomputable def formulaRule (k : ℕ) (F : MvPolynomial (FormulaVar L) L) (T : Test ℓ L) : L :=
  ((T.diff : L) ^ k)⁻¹ * MvPolynomial.eval T.toPair.formulaEval F

lemma formulaRule_apply (k : ℕ) (F : MvPolynomial (FormulaVar L) L) (T : Test ℓ L) :
    formulaRule k F T = ((T.diff : L) ^ k)⁻¹ * MvPolynomial.eval T.toPair.formulaEval F :=
  (rfl)

omit [DecidableEq L] in
/-- A constant multiple of a weighted homogeneous polynomial is weighted homogeneous. -/
lemma isWeightedHomogeneous_C_mul {σ : Type*} {w : σ → ℕ} {φ : MvPolynomial σ L} {m : ℕ}
    (c : L) (hφ : φ.IsWeightedHomogeneous w m) : (C c * φ).IsWeightedHomogeneous w m := by
  simpa using (isWeightedHomogeneous_C w c).mul hφ

/-- The polynomial `3 x² + a₄` (weighted degree `4`), whose trace over `C \ {0}` is Vélu's `t`. -/
noncomputable def veluTPoly : MvPolynomial (Fin 3) L := C 3 * (X 2 * X 2) + X 0

/-- The polynomial `5 x³ + 3 a₄ x + 2 a₆` (weighted degree `6`), whose trace over `C \ {0}` is
Vélu's `w`. -/
noncomputable def veluWPoly : MvPolynomial (Fin 3) L :=
  C 5 * (X 2 * X 2 * X 2) + C 3 * (X 0 * X 2) + C 2 * X 1

omit [DecidableEq L] in
lemma isWeightedHomogeneous_veluTPoly :
    (veluTPoly : MvPolynomial (Fin 3) L).IsWeightedHomogeneous ![4, 6, 2] 4 := by
  have h2 : (X 2 : MvPolynomial (Fin 3) L).IsWeightedHomogeneous ![4, 6, 2] 2 :=
    isWeightedHomogeneous_X L _ 2
  have h0 : (X 0 : MvPolynomial (Fin 3) L).IsWeightedHomogeneous ![4, 6, 2] 4 :=
    isWeightedHomogeneous_X L _ 0
  exact (isWeightedHomogeneous_C_mul 3 (h2.mul h2)).add h0

omit [DecidableEq L] in
lemma isWeightedHomogeneous_veluWPoly :
    (veluWPoly : MvPolynomial (Fin 3) L).IsWeightedHomogeneous ![4, 6, 2] 6 := by
  have h2 : (X 2 : MvPolynomial (Fin 3) L).IsWeightedHomogeneous ![4, 6, 2] 2 :=
    isWeightedHomogeneous_X L _ 2
  have h0 : (X 0 : MvPolynomial (Fin 3) L).IsWeightedHomogeneous ![4, 6, 2] 4 :=
    isWeightedHomogeneous_X L _ 0
  have h1 : (X 1 : MvPolynomial (Fin 3) L).IsWeightedHomogeneous ![4, 6, 2] 6 :=
    isWeightedHomogeneous_X L _ 1
  exact ((isWeightedHomogeneous_C_mul 5 ((h2.mul h2).mul h2)).add
    (isWeightedHomogeneous_C_mul 3 (h0.mul h2))).add (isWeightedHomogeneous_C_mul 2 h1)

/-- The variable `t = ∑_{Q ∈ C \ {0}} (3 x_Q² + a₄)`. -/
noncomputable def veluTVar : FormulaVar L :=
  .trace veluTPoly 4 isWeightedHomogeneous_veluTPoly

/-- The variable `w = ∑_{Q ∈ C \ {0}} (5 x_Q³ + 3 a₄ x_Q + 2 a₆)`. -/
noncomputable def veluWVar : FormulaVar L :=
  .trace veluWPoly 6 isWeightedHomogeneous_veluWPoly

/-- The coefficient `a₄ - 5 t` of Vélu's curve, of weight `4`. -/
noncomputable def veluA₄Formula : MvPolynomial (FormulaVar L) L :=
  X .a₄ + C (-5) * X veluTVar

/-- The coefficient `a₆ - 7 w` of Vélu's curve, of weight `6`. -/
noncomputable def veluA₆Formula : MvPolynomial (FormulaVar L) L :=
  X .a₆ + C (-7) * X veluWVar

/-- The universal formula `-16 (4 (a₄ - 5 t)³ + 27 (a₆ - 7 w)²)` for the discriminant of Vélu's
curve `y² = x³ + (a₄ - 5 t) x + (a₆ - 7 w)`. -/
noncomputable def veluFormula : MvPolynomial (FormulaVar L) L :=
  C (-16) * (C 4 * (veluA₄Formula * veluA₄Formula * veluA₄Formula) +
    C 27 * (veluA₆Formula * veluA₆Formula))

omit [DecidableEq L] in
/-- Vélu's discriminant formula is weighted homogeneous of weight `12`. -/
lemma isWeightedHomogeneous_veluFormula :
    (veluFormula : MvPolynomial (FormulaVar L) L).IsWeightedHomogeneous FormulaVar.weight 12 := by
  have hA : (veluA₄Formula : MvPolynomial (FormulaVar L) L).IsWeightedHomogeneous
      FormulaVar.weight 4 :=
    (isWeightedHomogeneous_X L FormulaVar.weight FormulaVar.a₄).add
      (isWeightedHomogeneous_C_mul _ (isWeightedHomogeneous_X L FormulaVar.weight veluTVar))
  have hB : (veluA₆Formula : MvPolynomial (FormulaVar L) L).IsWeightedHomogeneous
      FormulaVar.weight 6 :=
    (isWeightedHomogeneous_X L FormulaVar.weight FormulaVar.a₆).add
      (isWeightedHomogeneous_C_mul _ (isWeightedHomogeneous_X L FormulaVar.weight veluWVar))
  exact isWeightedHomogeneous_C_mul _ ((isWeightedHomogeneous_C_mul _ ((hA.mul hA).mul hA)).add
    (isWeightedHomogeneous_C_mul _ (hB.mul hB)))

/-- **Vélu's discriminant is a universal formula**: on a test object `(E, C, λ ω_E)`, the rule of
`veluFormula` is `λ⁻¹² Δ(E / C)`, the value `Δ(E / C, ω')` with `φ^* ω' = λ ω_E` for Vélu's
normalized quotient isogeny `φ`. -/
theorem formulaRule_veluFormula (T : Test ℓ L) :
    formulaRule 12 veluFormula T = ((T.diff : L) ^ 12)⁻¹ * (T.curve.velu T.subgroup).Δ := by
  rw [formulaRule_apply]
  congr 1
  have hT : T.toPair.formulaEval veluTVar = T.curve.veluT T.subgroup := by
    simp only [veluTVar, Pair.formulaEval, veluTPoly, WeierstrassCurve.veluT]
    refine finsum_mem_congr rfl fun Q _ ↦ ?_
    simp [pow_two]
  have hW : T.toPair.formulaEval veluWVar = T.curve.veluW T.subgroup := by
    simp only [veluWVar, Pair.formulaEval, veluWPoly, WeierstrassCurve.veluW]
    refine finsum_mem_congr rfl fun Q _ ↦ ?_
    simp; ring
  simp only [veluFormula, veluA₄Formula, veluA₆Formula, map_mul, map_add, eval_C, eval_X, hT, hW]
  simp only [Pair.formulaEval, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, velu_a₁, velu_a₂, velu_a₃, velu_a₄, velu_a₆]
  ring

end Gamma0
