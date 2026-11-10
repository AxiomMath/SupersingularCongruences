/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.LevelTwoForms.Identities
public import SupersingularCongruences.LevelTwo.LarsonRing

/-!
# The polynomial model of `L₂(Δ^t)` evaluated at Larson's forms

`LevelTwo.larsonL2 K t = (μ² ε)^t - (64 μ ε²)^t` is the polynomial in `K[δ, ε]` that represents
`L₂(Δ^t) = V₂(Δ)^t - Δ^t` (manuscript, Section 5). By Lemma 3.1
(`LevelTwoForms.discriminant_apply_eq`, `LevelTwoForms.discriminant_scaleMatrix_apply_eq`),
evaluating this polynomial at the actual modular forms `δ, ε ∈ M_*(Γ₀(2))` over `ℂ` gives
`Δ(2τ)^t - Δ(τ)^t`. Consequently the first identity of Proposition 5.2 holds for the complex
modular forms themselves (`LevelTwoForms.levelRaise_discriminant_pow_sub_discriminant_pow`).
The passage to Katz forms modulo `p` is `KatzForms.aeval_larsonL2`: the same polynomial evaluated
at the reductions `δ̄, ε̄` is the Katz form `V₂(Δ^t) - Δ^t` on `Γ₀(2)`.
-/

public section

open ModularForm UpperHalfPlane MvPolynomial

namespace LevelTwoForms

/-- Evaluating the polynomial model `LevelTwo.larsonL2 ℂ t` at `(δ(τ), ε(τ))` gives
`L₂(Δ^t)(τ) = Δ(2τ)^t - Δ(τ)^t`. -/
theorem eval_larsonL2 (t : ℕ) (τ : ℍ) :
    eval ![delta τ, eps τ] (LevelTwo.larsonL2 ℂ t) =
      ModularForm.discriminant (scaleMatrix 2 • τ) ^ t - ModularForm.discriminant τ ^ t := by
  have hmu : mu τ = delta τ ^ 2 - eps τ := mu_apply τ
  rw [LevelTwo.larsonL2_def, discriminant_scaleMatrix_apply_eq, discriminant_apply_eq]
  simp [LevelTwo.mu_def, hmu]

/-- **Proposition 5.2**, first identity, for the complex modular forms: with `μ = δ² - ε`,
`V₂(Δ)^t - Δ^t = μ^t ε^t (μ^t - 64^t ε^t)` pointwise on the upper half-plane. -/
theorem levelRaise_discriminant_pow_sub_discriminant_pow (t : ℕ) (τ : ℍ) :
    ModularForm.discriminant (scaleMatrix 2 • τ) ^ t - ModularForm.discriminant τ ^ t =
      mu τ ^ t * eps τ ^ t * (mu τ ^ t - 64 ^ t * eps τ ^ t) := by
  rw [discriminant_scaleMatrix_apply_eq, discriminant_apply_eq]
  ring

end LevelTwoForms
