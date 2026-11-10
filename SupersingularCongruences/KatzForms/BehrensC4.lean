/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.KatzForms.Basic
public import SupersingularCongruences.LevelOne.BehrensConditions

/-!
# Behrens' condition (C4)

For a prime `ℓ ≠ p` let `L_ℓ = V_ℓ - ι`, where `V_ℓ f (τ) = f (ℓ τ)` and `ι` is the inclusion of
level-one forms into forms on `Γ₀(ℓ)`. For a level-one form `f` of weight `12t` with integral
`q`-expansion, condition (C4) for the index `j` is [ono-manuscript, Section 2.1],
[larson2020, Section 1], [behrens2009, Theorem 1.3] (numbering of arXiv:0804.0363v2; Theorem 1.2
in the published version):

  for every prime `ℓ ≠ p`, `A_p^j ∣ L_ℓ(f̄)` in the ring `M_*(ℓ)_{ℤ/p}` of Katz modular forms
  modulo `p` on `Γ₀(ℓ)`.

Here `A_p` is the Hasse invariant. The ring `M_*(ℓ)_{ℤ/p}` is the graded ring of Katz forms on
`Γ₀(ℓ)` over `𝔽_p`; by Galois descent these are the Katz forms over an algebraic closure `L` of
`𝔽_p` that are fixed by `Aut(L)` (`Gamma0.IsDefinedOverPrimeField`). Since the ring is a graded
domain, the divisibility `A_p^j ∣ L_ℓ(f̄)` of homogeneous elements means `L_ℓ(f̄) = A_p^j H` for a
form `H` over `𝔽_p` of weight `12t - j (p - 1)`.

The Katz forms on `Γ₀(ℓ)` over `L` are supplied by `K ℓ : KatzForms p ℓ L` for every prime
`ℓ ≠ p`; the reductions `f̄` and `V_ℓ f̄` are `KatzForms.reduce` of the classical forms.

## Main definitions

* `LevelOne.reductionAtLevel K f G hG`, `LevelOne.levelRaiseReduction K f G hG`: the reductions of
  `ι f` and `V_ℓ f` as Katz forms on `Γ₀(ℓ)` over `L`.
* `LevelOne.BehrensC4`: condition (C4).
* `LevelOne.SatisfiesBehrensConditions`: conditions (C1)–(C4).
-/

public section

open ModularForm PowerSeries Gamma0 CongruenceSubgroup
open scoped MatrixGroups

namespace PowerSeries

/-- An integral power series is `p`-integral. -/
lemma isPIntegral_map_intCast (p : ℕ) [hp : Fact p.Prime] (G : PowerSeries ℤ) :
    (PowerSeries.map (Int.castRingHom ℚ) G).IsPIntegral p := by
  rw [isPIntegral_iff]
  intro n
  rw [coeff_map, eq_intCast, Rat.den_intCast, Nat.dvd_one]
  exact hp.out.one_lt.ne'

end PowerSeries

namespace LevelOne

variable {k : ℤ}

lemma map_map_intCast_eq_qExpansion_ofLevelOne (ℓ : ℕ) {f : ModularForm 𝒮ℒ k}
    {G : PowerSeries ℤ} (hG : IsIntegralQExpansion G f) :
    PowerSeries.map (Rat.castHom ℂ) (PowerSeries.map (Int.castRingHom ℚ) G) =
      UpperHalfPlane.qExpansion 1 (LevelTwoForms.ofLevelOne ℓ f) := by
  rw [LevelTwoForms.coe_ofLevelOne, ← isIntegralQExpansion_iff.mp hG]
  ext n
  simp [coeff_map]

lemma map_map_intCast_eq_qExpansion_levelRaise (ℓ : ℕ) [NeZero ℓ] {f : ModularForm 𝒮ℒ k}
    {G : PowerSeries ℤ} (hG : IsIntegralQExpansion G f) :
    PowerSeries.map (Rat.castHom ℂ) (PowerSeries.map (Int.castRingHom ℚ) (expandSeries ℓ G)) =
      UpperHalfPlane.qExpansion 1 (LevelTwoForms.levelRaise ℓ f) := by
  ext n
  rw [LevelTwoForms.qExpansion_levelRaise_coeff, coeff_map, coeff_map, coeff_expandSeries]
  split_ifs
  · rw [hG.coeff]; simp
  · simp

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [DecidableEq L]

/-- The reduction `ι f̄` of a level-one form `f` with integral `q`-expansion `G`, as a Katz form
on `Γ₀(ℓ)` over `L`. -/
noncomputable def reductionAtLevel {ℓ : ℕ} (K : KatzForms p ℓ L) (f : ModularForm 𝒮ℒ k)
    (G : PowerSeries ℤ) (hG : IsIntegralQExpansion G f) : K.form k :=
  K.reduce (LevelTwoForms.ofLevelOne ℓ f) (PowerSeries.map (Int.castRingHom ℚ) G)
    (PowerSeries.isPIntegral_map_intCast p G) (map_map_intCast_eq_qExpansion_ofLevelOne ℓ hG)

/-- The reduction `V_ℓ f̄` of `V_ℓ f` for a level-one form `f` with integral `q`-expansion `G`, as
a Katz form on `Γ₀(ℓ)` over `L`. -/
noncomputable def levelRaiseReduction {ℓ : ℕ} [NeZero ℓ] (K : KatzForms p ℓ L)
    (f : ModularForm 𝒮ℒ k) (G : PowerSeries ℤ) (hG : IsIntegralQExpansion G f) : K.form k :=
  K.reduce (LevelTwoForms.levelRaise ℓ f) (PowerSeries.map (Int.castRingHom ℚ) (expandSeries ℓ G))
    (PowerSeries.isPIntegral_map_intCast p _) (map_map_intCast_eq_qExpansion_levelRaise ℓ hG)

/-- **Behrens' condition (C4)** for a level-one form `f` of weight `12t` with integral
`q`-expansion `G` and the index `j`: for every prime `ℓ ≠ p`, `A_p^j ∣ L_ℓ(f̄)` in the ring of Katz
forms modulo `p` on `Γ₀(ℓ)`, i.e. `V_ℓ f̄ - ι f̄ = A_p^j H` with `H` a form over `𝔽_p` of weight
`12t - j (p - 1)`. -/
def BehrensC4 (K : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → KatzForms p ℓ L) (t j : ℕ)
    (f : ModularForm 𝒮ℒ (12 * t)) (G : PowerSeries ℤ) (hG : IsIntegralQExpansion G f) : Prop :=
  ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p),
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ∃ H ∈ (K ℓ hℓ hℓp).form (12 * t - j * ((p : ℤ) - 1)), IsDefinedOverPrimeField H ∧
      (levelRaiseReduction (K ℓ hℓ hℓp) f G hG).1 - (reductionAtLevel (K ℓ hℓ hℓp) f G hG).1 =
        hasseRule p ^ j * H

lemma behrensC4_iff (K : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → KatzForms p ℓ L) (t j : ℕ)
    (f : ModularForm 𝒮ℒ (12 * t)) (G : PowerSeries ℤ) (hG : IsIntegralQExpansion G f) :
    BehrensC4 K t j f G hG ↔ ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      ∃ H ∈ (K ℓ hℓ hℓp).form (12 * t - j * ((p : ℤ) - 1)), IsDefinedOverPrimeField H ∧
        (levelRaiseReduction (K ℓ hℓ hℓp) f G hG).1 -
            (reductionAtLevel (K ℓ hℓ hℓp) f G hG).1 = hasseRule p ^ j * H :=
  Iff.rfl

/-- The level-one form `f` of weight `12t`, with integral `q`-expansion `G`, satisfies Behrens'
conditions (C1)–(C4) for the prime `p` and the index `j`: it is a *candidate* `f_{i/j}` in
Larson's convention [larson2020, Section 1]. -/
structure SatisfiesBehrensConditions (K : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → KatzForms p ℓ L)
    (t j : ℕ) (f : ModularForm 𝒮ℒ (12 * t)) (G : PowerSeries ℤ) : Prop
    extends SatisfiesBehrensC123 p t j f G where
  c4 : BehrensC4 K t j f G isIntegralQExpansion

end LevelOne
