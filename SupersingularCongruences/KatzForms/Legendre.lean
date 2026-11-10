/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.KatzForms.Basic
public import SupersingularCongruences.ModularCurve.Legendre

/-!
# Katz forms on `Γ₀(2)` on the Legendre family

A Katz form `f` of weight `k` on `Γ₀(2)` over `L` is a rule on test objects over all
`L`-algebras `R`, compatible with base change [katz1973, Section 1.1, condition 3]. Applied to
the Legendre
family `(E_λ, ⟨(0, 0)⟩, dx / (2y))` over `R = L[λ, 1 / (λ (λ - 1))]` (with `6` invertible), it
gives an element of `R`, whose specialization at `λ₀ ≠ 0, 1` is the value of `f` at the Legendre
pair `E_{λ₀}`. This is used in the proof of Lemma 3.3 of the manuscript ("`h(λ)` and `e(λ)` are
regular functions on the `λ`-line minus the cusps").
-/

public section

open Gamma0 Polynomial

/-- **Regularity on the Legendre family** (cited fact; see the module docstring): the value of a
Katz form on `Γ₀(2)` at `(E_λ, ⟨(0, 0)⟩, dx / (2y))` is a regular function of `λ ≠ 0, 1`, i.e.
of the form `P(λ) / (λ^a (λ - 1)^b)` with `P ∈ L[λ]` [katz1973, Section 1.1, condition 3]. -/
structure KatzForms.LegendreRegular {p : ℕ} {L : Type*} [Field L] [DecidableEq L]
    (K : KatzForms p 2 L) : Prop where
  exists_eq_div {k : ℤ} {f : Test 2 L → L} (hf : f ∈ K.form k) (h2 : (2 : L) ≠ 0)
    (h3 : (3 : L) ≠ 0) :
    ∃ (P : L[X]) (a b : ℕ), ∀ (lam : L) (h0 : lam ≠ 0) (h1 : lam ≠ 1),
      f ⟨legendrePair h2 h3 h0 h1, 1⟩ = P.eval lam / (lam ^ a * (lam - 1) ^ b)
