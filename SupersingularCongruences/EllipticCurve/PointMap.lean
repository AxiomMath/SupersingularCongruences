/-
Assembled by AxiomProver.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Coordinates of points and conjugation of points by field homomorphisms

For a Weierstrass curve `W` over a field `F`:

* `WeierstrassCurve.Affine.Point.xCoord`, `WeierstrassCurve.Affine.Point.yCoord`: the affine
  coordinates of a point (junk value `0` at the point at infinity).
* `WeierstrassCurve.Affine.Point.mapRingHom σ`: for a field homomorphism `σ : F →+* K`, the group
  homomorphism `(x, y) ↦ (σ x, σ y)` from the points of `W` to the points of `W.map σ`. (Mathlib's
  `WeierstrassCurve.Affine.Point.map` only covers algebra homomorphisms between base changes.)
-/

public section

open WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.Point

variable {F K : Type*} [Field F] [Field K] {W : Affine F}

/-- The `x`-coordinate of a point; `0` at the point at infinity. -/
def xCoord : W.Point → F
  | 0 => 0
  | some x _ _ => x

/-- The `y`-coordinate of a point; `0` at the point at infinity. -/
def yCoord : W.Point → F
  | 0 => 0
  | some _ y _ => y

@[simp] lemma xCoord_zero : (0 : W.Point).xCoord = 0 := (rfl)

@[simp] lemma yCoord_zero : (0 : W.Point).yCoord = 0 := (rfl)

@[simp] lemma xCoord_some {x y : F} (h : W.Nonsingular x y) : (some x y h).xCoord = x := (rfl)

@[simp] lemma yCoord_some {x y : F} (h : W.Nonsingular x y) : (some x y h).yCoord = y := (rfl)

variable [DecidableEq F] [DecidableEq K] (σ : F →+* K)

/-- The group homomorphism `(x, y) ↦ (σ x, σ y)` from the points of `W` to the points of
`W.map σ`, for a homomorphism of fields `σ`. -/
noncomputable def mapRingHom : W.Point →+ (W.map σ).toAffine.Point where
  toFun P := match P with
    | 0 => 0
    | some x y h => some (σ x) (σ y) ((map_nonsingular W σ.injective x y).mpr h)
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
    · rw [add_of_Y_eq hxy.left hxy.right,
        add_of_Y_eq (congr_arg _ hxy.left) <| by rw [hxy.right, map_negY]]
    · have hxy' : ¬(σ x₁ = σ x₂ ∧ σ y₁ = (W.map σ).toAffine.negY (σ x₂) (σ y₂)) := by
        rw [map_negY]
        exact fun h => hxy ⟨σ.injective h.1, σ.injective h.2⟩
      simp only [add_some hxy, add_some hxy', some.injEq]
      exact ⟨by rw [map_slope, map_addX], by rw [map_slope, map_addY]⟩

lemma mapRingHom_some {x y : F} (h : W.Nonsingular x y) :
    mapRingHom σ (some x y h) = some _ _ ((map_nonsingular W σ.injective x y).mpr h) :=
  (rfl)

@[simp] lemma xCoord_mapRingHom (P : W.Point) : (mapRingHom σ P).xCoord = σ P.xCoord := by
  rcases P with _ | ⟨x, y, h⟩
  · exact σ.map_zero.symm
  · rfl

@[simp] lemma yCoord_mapRingHom (P : W.Point) : (mapRingHom σ P).yCoord = σ P.yCoord := by
  rcases P with _ | ⟨x, y, h⟩
  · exact σ.map_zero.symm
  · rfl

lemma mapRingHom_injective : Function.Injective (mapRingHom (W := W) σ) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (by rw [mapRingHom_some]; exact some_ne_zero _)
  · exact absurd h (by rw [mapRingHom_some]; exact some_ne_zero _)
  · simp only [mapRingHom_some, some.injEq] at h
    simp only [some.injEq]
    exact ⟨σ.injective h.1, σ.injective h.2⟩

end WeierstrassCurve.Affine.Point
