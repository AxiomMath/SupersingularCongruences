/-
Assembled by AxiomProver.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import SupersingularCongruences.LevelOne.IntegralQExpansion
import all SupersingularCongruences.LevelOne.IntegralQExpansion

/-!
# The Tate curve and the value of the discriminant on curves with a differential

* `WeierstrassCurve.discriminantValue W c`: the value `Δ(W, c · ω_W) = c⁻¹² Δ(W)` of the
  discriminant modular form on a Weierstrass curve `W` over a commutative ring with the
  differential `c · ω_W`, where `ω_W = dx / (2y + a₁x + a₃)` is the standard invariant
  differential and `c` is a unit [silverman-aec, Section III.1], [katz1973, Section 1.1]. Its
  transformation rules: the weight rule (`discriminantValue_mul`), invariance under isomorphisms
  (`discriminantValue_variableChange`) and compatibility with base change
  (`discriminantValue_map`).
* `LevelOne.tateCurve`: the Tate curve `Tate(q) : y² + xy = x³ + a₄(q) x + a₆(q)` over `ℤ⟦q⟧` with
  `a₄ = -5 s₃`, `a₆ = -(5 s₃ + 7 s₅) / 12`, `s_k = ∑ σ_k(n) qⁿ` [silverman-ataec, Section V.1],
  [katz-mazur, (8.8)]. Its standard differential `dx / (2y + x)` is the canonical differential
  `du / u` of `𝔾_m / q^ℤ`.
* `LevelOne.tateCurve_Δ`: `Δ(Tate(q), du / u) = q ∏ (1 - qⁿ)²⁴` (as the integral series
  `(E₄³ - E₆²) / 1728`), by direct computation from the Weierstrass formulas.
-/

public section

open PowerSeries
open scoped ArithmeticFunction.sigma

namespace WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The value `Δ(W, c · ω_W) = c⁻¹² Δ(W)` of the discriminant modular form on `W` with the
differential `c · ω_W`, `ω_W = dx / (2y + a₁x + a₃)`. -/
noncomputable def discriminantValue (W : WeierstrassCurve R) (c : Rˣ) : R :=
  ((c⁻¹ : Rˣ) : R) ^ 12 * W.Δ

lemma discriminantValue_def (W : WeierstrassCurve R) (c : Rˣ) :
    W.discriminantValue c = ((c⁻¹ : Rˣ) : R) ^ 12 * W.Δ := (rfl)

/-- The weight rule `Δ(W, a c ω_W) = a⁻¹² Δ(W, c ω_W)`. -/
lemma discriminantValue_mul (W : WeierstrassCurve R) (a c : Rˣ) :
    W.discriminantValue (a * c) = ((a⁻¹ : Rˣ) : R) ^ 12 * W.discriminantValue c := by
  rw [discriminantValue_def, discriminantValue_def, mul_inv, Units.val_mul, mul_pow, mul_assoc]

/-- Invariance under isomorphisms. The change of variables `C = (u, r, s, t)` is an isomorphism
`ψ : C • W → W` with `ψ^* ω_W = u⁻¹ ω_{C • W}` [silverman-aec, Table 3.1], so
`(W, c ω_W) ≅ (C • W, c u⁻¹ ω_{C • W})` and the two values agree. -/
lemma discriminantValue_variableChange (W : WeierstrassCurve R) (C : VariableChange R) (c : Rˣ) :
    (C • W).discriminantValue (c * C.u⁻¹) = W.discriminantValue c := by
  rw [discriminantValue_def, discriminantValue_def, variableChange_Δ, mul_inv, inv_inv,
    Units.val_mul, mul_pow, mul_assoc, ← mul_assoc ((C.u : R) ^ 12), ← mul_pow,
    Units.mul_inv, one_pow, one_mul]

/-- Compatibility with base change. -/
lemma discriminantValue_map (W : WeierstrassCurve R) (f : R →+* S) (c : Rˣ) :
    (W.map f).discriminantValue (Units.map (f : R →* S) c) = f (W.discriminantValue c) := by
  rw [discriminantValue_def, discriminantValue_def, map_Δ, map_mul, map_pow, ← map_inv,
    Units.coe_map, MonoidHom.coe_coe]

end WeierstrassCurve

namespace LevelOne

/-- The series `s₃ = ∑ σ₃(n) qⁿ`. -/
noncomputable def tateS₃ : PowerSeries ℤ := PowerSeries.mk fun n ↦ (σ 3 n : ℤ)

/-- The series `(5 s₃ + 7 s₅) / 12 = ∑ ((5 σ₃(n) + 7 σ₅(n)) / 12) qⁿ`, with integral
coefficients (`LevelOne.twelve_dvd_sigma`). -/
noncomputable def tateA₆Series : PowerSeries ℤ :=
  PowerSeries.mk fun n ↦ (((5 * σ 3 n + 7 * σ 5 n) / 12 : ℕ) : ℤ)

/-- **The Tate curve** `Tate(q) : y² + xy = x³ + a₄(q) x + a₆(q)` over `ℤ⟦q⟧`, with
`a₄ = -5 s₃` and `a₆ = -(5 s₃ + 7 s₅) / 12` [silverman-ataec, Section V.1, Theorem V.1.1],
[katz-mazur, (8.8)]. -/
noncomputable def tateCurve : WeierstrassCurve (PowerSeries ℤ) where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := -5 * tateS₃
  a₆ := -tateA₆Series

/-- The discriminant of the Tate curve with its canonical differential `du / u = dx / (2y + x)` is
`Δ(q) = q ∏ (1 - qⁿ)²⁴`, the series `(E₄³ - E₆²) / 1728`. -/
theorem tateCurve_Δ : tateCurve.Δ = integralDiscriminant := by
  have h4 : integralE₄ = 1 + 240 * tateS₃ := by
    ext n
    rcases n with _ | n <;> simp [integralE₄, tateS₃, coeff_one]
  have h6 : integralE₆ = 1 - 504 * PowerSeries.mk fun n ↦ (σ 5 n : ℤ) := by
    ext n
    rcases n with _ | n <;> simp [integralE₆, coeff_one]
  have hc : 5 * tateS₃ + 7 * (PowerSeries.mk fun n ↦ (σ 5 n : ℤ)) = 12 * tateA₆Series := by
    ext n
    have := Nat.div_mul_cancel (twelve_dvd_sigma n)
    simp only [map_add, coeff_ofNat_mul, coeff_mk, tateS₃, tateA₆Series]
    omega
  have hΔ : tateCurve.Δ = tateA₆Series + 25 * tateS₃ ^ 2 + 8000 * tateS₃ ^ 3 -
      432 * tateA₆Series ^ 2 + 360 * tateS₃ * tateA₆Series := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, tateCurve]
    ring
  have hmul : (1728 : PowerSeries ℤ) * tateCurve.Δ = 1728 * integralDiscriminant := by
    rw [integralDiscriminant_mul, h4, h6, hΔ]
    linear_combination (5184 * (12 * tateA₆Series - 5 * tateS₃ +
      7 * (PowerSeries.mk fun n ↦ (σ 5 n : ℤ))) - 144) * hc
  refine mul_left_cancel₀ (fun h ↦ ?_) hmul
  have := congrArg (PowerSeries.constantCoeff) h
  rw [map_ofNat, map_zero] at this
  norm_num at this

end LevelOne
