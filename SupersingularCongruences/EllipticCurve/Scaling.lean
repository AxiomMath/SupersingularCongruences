/-
Assembled by AxiomProver.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Scaling the coordinates of a Weierstrass curve

For a unit `u` of a field `F` and a Weierstrass curve `W` over `F`, the admissible change of
variables `(x, y) ↦ (u ^ 2 x, u ^ 3 y)` transforms `W` into the curve `W.scaling u` with
coefficients `aᵢ ↦ u ^ i aᵢ`. This file constructs the induced group isomorphism on affine points,
`WeierstrassCurve.scalingPoint`; Mathlib provides variable changes of curves but not the induced
maps on points.

In Mathlib's convention for `VariableChange`, the change used here is `⟨u⁻¹, 0, 0, 0⟩`.
-/

public section

open WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {F : Type*} [Field F]

/-- The admissible change of variables `(x, y) ↦ (u ^ 2 x, u ^ 3 y)`, i.e. `⟨u⁻¹, 0, 0, 0⟩` in
Mathlib's convention. -/
def scalingChange (u : Fˣ) : VariableChange F :=
  ⟨u⁻¹, 0, 0, 0⟩

/-- The Weierstrass curve with coefficients `aᵢ ↦ u ^ i aᵢ`, obtained from `W` by the change of
variables `(x, y) ↦ (u ^ 2 x, u ^ 3 y)`. -/
abbrev scaling (W : WeierstrassCurve F) (u : Fˣ) : WeierstrassCurve F :=
  scalingChange u • W

variable (W : WeierstrassCurve F) (u : Fˣ)

@[simp] lemma scaling_a₁ : (W.scaling u).a₁ = u * W.a₁ := by
  simp [scaling, scalingChange, variableChange_a₁]

@[simp] lemma scaling_a₂ : (W.scaling u).a₂ = u ^ 2 * W.a₂ := by
  simp [scaling, scalingChange, variableChange_a₂]

@[simp] lemma scaling_a₃ : (W.scaling u).a₃ = u ^ 3 * W.a₃ := by
  simp [scaling, scalingChange, variableChange_a₃]

@[simp] lemma scaling_a₄ : (W.scaling u).a₄ = u ^ 4 * W.a₄ := by
  simp [scaling, scalingChange, variableChange_a₄]

@[simp] lemma scaling_a₆ : (W.scaling u).a₆ = u ^ 6 * W.a₆ := by
  simp [scaling, scalingChange, variableChange_a₆]

lemma scaling_j [W.IsElliptic] : (W.scaling u).j = W.j :=
  variableChange_j W _

instance [W.IsShortNF] : (W.scaling u).IsShortNF :=
  ⟨by simp, by simp, by simp⟩

lemma equation_scaling_iff (x y : F) :
    (W.scaling u).toAffine.Equation (u ^ 2 * x) (u ^ 3 * y) ↔ W.toAffine.Equation x y := by
  rw [Affine.equation_iff', Affine.equation_iff']
  simp only [scaling_a₁, scaling_a₂, scaling_a₃, scaling_a₄, scaling_a₆]
  have hu : (u : F) ^ 6 ≠ 0 := pow_ne_zero _ u.ne_zero
  constructor
  · intro h
    refine (mul_eq_zero.mp ?_).resolve_left hu
    linear_combination h
  · intro h
    linear_combination (u : F) ^ 6 * h

lemma nonsingular_scaling_iff (x y : F) :
    (W.scaling u).toAffine.Nonsingular (u ^ 2 * x) (u ^ 3 * y) ↔ W.toAffine.Nonsingular x y := by
  rw [Affine.nonsingular_iff', Affine.nonsingular_iff', equation_scaling_iff]
  simp only [scaling_a₁, scaling_a₂, scaling_a₄, scaling_a₃]
  have h4 : (u : F) ^ 4 ≠ 0 := pow_ne_zero _ u.ne_zero
  have h3 : (u : F) ^ 3 ≠ 0 := pow_ne_zero _ u.ne_zero
  have eX : u * W.a₁ * (u ^ 3 * y) - (3 * (u ^ 2 * x) ^ 2 + 2 * (u ^ 2 * W.a₂) * (u ^ 2 * x) +
      u ^ 4 * W.a₄) = (u : F) ^ 4 * (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) := by ring
  have eY : 2 * (u ^ 3 * y) + u * W.a₁ * (u ^ 2 * x) + u ^ 3 * W.a₃ =
      (u : F) ^ 3 * (2 * y + W.a₁ * x + W.a₃) := by ring
  rw [eX, eY, mul_ne_zero_iff, mul_ne_zero_iff]
  simp [h4, h3]

lemma negY_scaling (x y : F) :
    (W.scaling u).toAffine.negY (u ^ 2 * x) (u ^ 3 * y) = u ^ 3 * W.toAffine.negY x y := by
  simp only [Affine.negY, scaling_a₁, scaling_a₃]
  ring

lemma addX_scaling (x₁ x₂ ℓ : F) :
    (W.scaling u).toAffine.addX (u ^ 2 * x₁) (u ^ 2 * x₂) (u * ℓ) =
      u ^ 2 * W.toAffine.addX x₁ x₂ ℓ := by
  simp only [Affine.addX, scaling_a₁, scaling_a₂]
  ring

lemma addY_scaling (x₁ x₂ y₁ ℓ : F) :
    (W.scaling u).toAffine.addY (u ^ 2 * x₁) (u ^ 2 * x₂) (u ^ 3 * y₁) (u * ℓ) =
      u ^ 3 * W.toAffine.addY x₁ x₂ y₁ ℓ := by
  simp only [Affine.addY, Affine.negAddY, Affine.negY, Affine.addX, scaling_a₁, scaling_a₂,
    scaling_a₃]
  ring

variable [DecidableEq F]

lemma slope_scaling (x₁ x₂ y₁ y₂ : F) :
    (W.scaling u).toAffine.slope (u ^ 2 * x₁) (u ^ 2 * x₂) (u ^ 3 * y₁) (u ^ 3 * y₂) =
      u * W.toAffine.slope x₁ x₂ y₁ y₂ := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  by_cases hx : x₁ = x₂
  · subst hx
    by_cases hy : y₁ = W.toAffine.negY x₁ y₂
    · rw [Affine.slope_of_Y_eq rfl hy, Affine.slope_of_Y_eq rfl (by rw [negY_scaling, hy]),
        mul_zero]
    · have hy' : u ^ 3 * y₁ ≠ (W.scaling u).toAffine.negY (u ^ 2 * x₁) (u ^ 3 * y₂) := by
        rw [negY_scaling]
        exact fun h => hy (mul_left_cancel₀ (pow_ne_zero 3 hu) h)
      rw [Affine.slope_of_Y_ne rfl hy', Affine.slope_of_Y_ne rfl hy, negY_scaling]
      have eN : 3 * (u ^ 2 * x₁) ^ 2 + 2 * (W.scaling u).a₂ * (u ^ 2 * x₁) + (W.scaling u).a₄ -
          (W.scaling u).a₁ * (u ^ 3 * y₁) =
          (u : F) ^ 4 * (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) := by
        simp only [scaling_a₁, scaling_a₂, scaling_a₄]; ring
      have eD : u ^ 3 * y₁ - u ^ 3 * W.toAffine.negY x₁ y₁ =
          (u : F) ^ 3 * (y₁ - W.toAffine.negY x₁ y₁) := by ring
      rw [eN, eD, mul_div_mul_comm, show (u : F) ^ 4 / u ^ 3 = u by
        rw [pow_succ, mul_div_cancel_left₀ _ (pow_ne_zero 3 hu)]]
  · have hx' : u ^ 2 * x₁ ≠ u ^ 2 * x₂ := fun h => hx (mul_left_cancel₀ (pow_ne_zero 2 hu) h)
    rw [Affine.slope_of_X_ne hx', Affine.slope_of_X_ne hx]
    have : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    field_simp

namespace Affine.Point

/-- The group homomorphism `(x, y) ↦ (u ^ 2 x, u ^ 3 y)` from the points of `W` to the points of
`W.scaling u`. -/
noncomputable def scaling : W.toAffine.Point →+ (W.scaling u).toAffine.Point where
  toFun P := match P with
    | 0 => 0
    | some x y h => some (u ^ 2 * x) (u ^ 3 * y) ((nonsingular_scaling_iff W u x y).mpr h)
  map_zero' := rfl
  map_add' := by
    have hu : (u : F) ≠ 0 := u.ne_zero
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.left hxy.right,
        add_of_Y_eq (congr_arg _ hxy.left) <| by rw [hxy.right, negY_scaling]]
    · have hxy' : ¬(u ^ 2 * x₁ = u ^ 2 * x₂ ∧
          u ^ 3 * y₁ = (W.scaling u).toAffine.negY (u ^ 2 * x₂) (u ^ 3 * y₂)) := by
        rw [negY_scaling]
        exact fun h => hxy ⟨mul_left_cancel₀ (pow_ne_zero 2 hu) h.1,
          mul_left_cancel₀ (pow_ne_zero 3 hu) h.2⟩
      simp only [add_some hxy, add_some hxy', some.injEq]
      exact ⟨by rw [slope_scaling, addX_scaling], by rw [slope_scaling, addY_scaling]⟩

lemma scaling_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    scaling W u (some x y h) = some _ _ ((nonsingular_scaling_iff W u x y).mpr h) :=
  (rfl)

lemma scaling_zero : scaling W u 0 = 0 :=
  _root_.map_zero _

lemma scaling_injective : Function.Injective (scaling W u) := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · rw [← Point.zero_def, scaling_zero, scaling_some] at h
    exact absurd h.symm (some_ne_zero _)
  · rw [← Point.zero_def, scaling_zero, scaling_some] at h
    exact absurd h (some_ne_zero _)
  · simp only [scaling_some, some.injEq] at h
    simp only [some.injEq]
    exact ⟨mul_left_cancel₀ (pow_ne_zero 2 hu) h.1, mul_left_cancel₀ (pow_ne_zero 3 hu) h.2⟩

lemma scaling_surjective : Function.Surjective (scaling W u) := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨0, rfl⟩
  · have hx : (u : F) ^ 2 * ((u⁻¹ : Fˣ) ^ 2 * x) = x := by
      rw [Units.val_inv_eq_inv_val, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hu, one_pow, one_mul]
    have hy : (u : F) ^ 3 * ((u⁻¹ : Fˣ) ^ 3 * y) = y := by
      rw [Units.val_inv_eq_inv_val, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hu, one_pow, one_mul]
    have h' : W.toAffine.Nonsingular ((u⁻¹ : Fˣ) ^ 2 * x) ((u⁻¹ : Fˣ) ^ 3 * y) := by
      rw [← nonsingular_scaling_iff W u, hx, hy]; exact h
    refine ⟨some _ _ h', ?_⟩
    rw [scaling_some]
    congr

/-- If `W` has no nonzero `n`-torsion point, neither has `W.scaling u`. -/
lemma eq_zero_of_nsmul_eq_zero_scaling {n : ℕ} (h : ∀ P : W.toAffine.Point, n • P = 0 → P = 0)
    (P : (W.scaling u).toAffine.Point) (hP : n • P = 0) : P = 0 := by
  obtain ⟨Q, rfl⟩ := scaling_surjective W u P
  rw [← map_nsmul, ← scaling_zero W u] at hP
  rw [h Q (scaling_injective W u hP), scaling_zero]

end Affine.Point

end WeierstrassCurve
