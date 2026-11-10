/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.DividedBeta.Admissible
public import SupersingularCongruences.LevelOne.MaximalOrder

/-!
# Behrens' conditions (C1)–(C3) and the forms `Δᵗ`

For an admissible pair `(i, j)`, `t = i (p² - 1) / 12` and a level-one form `f` of weight `12t`
with integral q-expansion `G` and reduction `f̄ = Ḡ ∈ (ZMod p)⟦X⟧`, Behrens' conditions are
(manuscript, Section 2.1; [larson2020, Section 1]):

* (C1) `f̄ ≠ 0`;
* (C2) `12 · ord_q(f̄) > 12t - (p - 1) j` or `12 · ord_q(f̄) = 12t - (p - 1) j - 2`;
* (C3) no level-one form of weight `k' < 12t` with integral q-expansion is congruent to `f`
  modulo `p`;
* (C4) a divisibility condition on `L_ℓ(f̄)` in Katz's ring of mod `p` modular forms on `Γ₀(ℓ)`.

This file formalizes (C1)–(C3), which only involve `q`-expansions. Condition (C4), which needs
Katz's ring of mod `p` modular forms on `Γ₀(ℓ)`, is `LevelOne.BehrensC4` in
`SupersingularCongruences.KatzForms.BehrensC4`, stated over the interface `KatzForms`; the four
conditions together are `LevelOne.SatisfiesBehrensConditions` there. All arithmetic in (C2)
takes place in `ℤ`.

## Main results

* `LevelOne.SatisfiesBehrensC123`: `f` (with integral q-expansion `G`) satisfies (C1)–(C3).
* `LevelOne.discriminantPow_satisfiesBehrensC123`: `Δᵗ` satisfies (C1)–(C3) for every `j ≥ 1`
  (manuscript, Lemma 5.5).
* `LevelOne.discriminantPow_satisfiesBehrensC123_of_isAdmissible`: the same for every admissible
  pair `(i, j)` with `t = i (p² - 1) / 12`.
-/

public section

open ModularForm PowerSeries
open scoped MatrixGroups

namespace LevelOne

/-- Behrens' condition (C1) for an integral q-expansion `G`: its reduction modulo `p` is nonzero.
-/
def BehrensC1 (p : ℕ) (G : PowerSeries ℤ) : Prop :=
  PowerSeries.map (Int.castRingHom (ZMod p)) G ≠ 0

/-- Behrens' condition (C2) for an integral q-expansion `G` in weight `12t` and index `j`:
`12 · ord_q(Ḡ) > 12t - (p - 1) j` or `12 · ord_q(Ḡ) = 12t - (p - 1) j - 2`, in `ℤ`. Here
`ord_q(Ḡ)` is `(Ḡ.order).toNat`, which is the `q`-order of `Ḡ` when (C1) holds. -/
def BehrensC2 (p t j : ℕ) (G : PowerSeries ℤ) : Prop :=
  12 * ((PowerSeries.map (Int.castRingHom (ZMod p)) G).order.toNat : ℤ) >
      12 * (t : ℤ) - ((p : ℤ) - 1) * j ∨
    12 * ((PowerSeries.map (Int.castRingHom (ZMod p)) G).order.toNat : ℤ) =
      12 * (t : ℤ) - ((p : ℤ) - 1) * j - 2

/-- Behrens' condition (C3) for an integral q-expansion `G` in weight `12t`: no level-one modular
form of weight `k' < 12t` with integral q-expansion `H` satisfies `H̄ = Ḡ` modulo `p`. -/
def BehrensC3 (p t : ℕ) (G : PowerSeries ℤ) : Prop :=
  ∀ (k' : ℤ), k' < 12 * (t : ℤ) → ∀ (g : ModularForm 𝒮ℒ k') (H : PowerSeries ℤ),
    IsIntegralQExpansion H g →
      PowerSeries.map (Int.castRingHom (ZMod p)) H ≠ PowerSeries.map (Int.castRingHom (ZMod p)) G

/-- The level-one form `f` of weight `12t`, with integral q-expansion `G`, satisfies Behrens'
conditions (C1)–(C3) for the prime `p` and index `j`. -/
structure SatisfiesBehrensC123 (p t j : ℕ) (f : ModularForm 𝒮ℒ (12 * t)) (G : PowerSeries ℤ) :
    Prop where
  isIntegralQExpansion : IsIntegralQExpansion G f
  c1 : BehrensC1 p G
  c2 : BehrensC2 p t j G
  c3 : BehrensC3 p t G

variable {p : ℕ} [hp : Fact p.Prime]

/-- `Δᵗ` satisfies (C1). -/
theorem behrensC1_integralDiscriminant_pow (t : ℕ) : BehrensC1 p (integralDiscriminant ^ t) :=
  reduction_integralDiscriminant_pow_ne_zero t

/-- `Δᵗ` satisfies (C2), via its first alternative `12t > 12t - (p - 1) j`, for every `j ≥ 1`. -/
theorem behrensC2_integralDiscriminant_pow (t : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    BehrensC2 p t j (integralDiscriminant ^ t) := by
  left
  rw [order_reduction_integralDiscriminant_pow, ENat.toNat_natCast]
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  nlinarith

/-- `Δᵗ` satisfies (C3) (manuscript, Lemma 2.3). -/
theorem behrensC3_integralDiscriminant_pow (t : ℕ) : BehrensC3 p t (integralDiscriminant ^ t) :=
  fun _ hk' g _ hH ↦ reduction_ne_reduction_discriminantPow hk' g hH

/-- **(C1)–(C3) for `Δᵗ`** [ono-manuscript, Lemma 5.5]: for every prime `p`, every `t` and every
`j ≥ 1`, the form `Δᵗ` of weight `12t` satisfies Behrens' conditions (C1)–(C3); (C2) holds via
its first alternative. -/
theorem discriminantPow_satisfiesBehrensC123 (t : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    SatisfiesBehrensC123 p t j (discriminantPow t) (integralDiscriminant ^ t) where
  isIntegralQExpansion := isIntegralQExpansion_discriminantPow t
  c1 := behrensC1_integralDiscriminant_pow t
  c2 := behrensC2_integralDiscriminant_pow t hj
  c3 := behrensC3_integralDiscriminant_pow t

/-- **(C1)–(C3) for `Δᵗ` at admissible pairs** [ono-manuscript, Lemma 5.5]: for every admissible
pair `(i, j)` and `t = i (p² - 1) / 12`, the form `Δᵗ` satisfies (C1)–(C3). -/
theorem discriminantPow_satisfiesBehrensC123_of_isAdmissible {i j : ℕ}
    (h : DividedBeta.IsAdmissible p i j) :
    SatisfiesBehrensC123 p (i * (p ^ 2 - 1) / 12) j (discriminantPow (i * (p ^ 2 - 1) / 12))
      (integralDiscriminant ^ (i * (p ^ 2 - 1) / 12)) :=
  discriminantPow_satisfiesBehrensC123 _ h.one_le_right

end LevelOne
