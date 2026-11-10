/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.ModularCurve.Gamma0Pair
public import SupersingularCongruences.EllipticCurve.DeuringModel
public import SupersingularCongruences.Isogeny.VeluProperties
public import SupersingularCongruences.External

/-!
# Supersingular containment (Theorem 1.2, isogeny form)

For a pair `(E, C)` over an algebraic closure `L` of `𝔽_p` with `E` supersingular and `C` of prime
order `ℓ ≠ p`, the value `R_ℓ(E, C) = ℓ⁻¹² Δ(E / C) / Δ(E)` (`Gamma0.Pair.veluRatio`) satisfies
`R_ℓ(E, C) ^ m = 1`, `m = (p² - 1) / 12`.

Proof (manuscript, Section 4.4): replace `(E, C)` by an isomorphic pair `(E.scaling u, ψ_u C)`
with `E.scaling u` a Deuring model (Lemma 4.3(a),
`WeierstrassCurve.exists_isDeuringModelOver_scaling`; `R_ℓ` is invariant,
`Gamma0.Pair.veluRatio_scale`). Vélu's quotient is again a Deuring model
(Lemma 4.3(c), `WeierstrassCurve.IsDeuringModelOver.velu`), so by Lemma 4.4
(`Gamma0.Pair.veluRatio_pow_eq`) and Theorem 1.3 for both curves
(`WeierstrassCurve.Δ_pow_of_isDeuringModelOver`), `R_ℓ ^ m = (-1)^((p+1)/2) / (-1)^((p+1)/2) = 1`.
-/

public section

universe u

namespace Gamma0.Pair

variable {ℓ : ℕ} {L : Type u} [Field L] [IsAlgClosed L] [DecidableEq L] {p : ℕ} [CharP L p]

/-- **Theorem 1.2** (supersingular containment), in terms of Vélu's quotient, from the cited
results it uses: for `p ≥ 5`, a prime `ℓ ≠ p` and a pair `(E, C)` over `L` with `E`
supersingular, `R_ℓ(E, C) ^ ((p² - 1) / 12) = 1`. -/
theorem veluRatio_pow_eq_one_of_cited
    (hGonzalezDivisionPolynomial : WeierstrassCurve.GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : WeierstrassCurve.GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : WeierstrassCurve.SupersingularJInvariant.{u})
    (hVeluIsogeny : WeierstrassCurve.VeluIsogeny.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (P : Pair ℓ L)
    (hss : P.curve.IsSupersingularOver p) : P.veluRatio ^ ((p ^ 2 - 1) / 12) = 1 := by
  obtain ⟨u, hu⟩ := WeierstrassCurve.exists_isDeuringModelOver_scaling hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hSupersingularJInvariant hp hp5 hL P.curve hss
  rw [← veluRatio_scale P u]
  have hD : (P.scale u).curve.IsDeuringModelOver p := by rw [scale_curve]; exact hu
  have hC := (P.scale u).finite_subgroup hℓ.ne_zero
  have hsmall : ∀ n : ℕ, 0 < n → n < p → (n : L) ≠ 0 := fun n hn hnp h =>
    absurd (Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff L p n).mp h)) (by omega)
  have h2 : (2 : L) ≠ 0 := by exact_mod_cast hsmall 2 (by norm_num) (by omega)
  have h3 : (3 : L) ≠ 0 := by exact_mod_cast hsmall 3 (by norm_num) (by omega)
  obtain ⟨hΔ', -⟩ := hVeluIsogeny (P.scale u).curve (P.scale u).subgroup h2 h3 hC
  have : ((P.scale u).curve.velu (P.scale u).subgroup).IsElliptic := ⟨hΔ'⟩
  have hD' := hD.velu hVeluIsogeny hp hp5 _ hC
  rw [veluRatio_pow_eq hp hp5 hℓ hℓp,
    WeierstrassCurve.Δ_pow_of_isDeuringModelOver_of_cited hGonzalezDivisionPolynomial
      hGonzalezMultiplicationByP hp hp5 hL _ hD',
    WeierstrassCurve.Δ_pow_of_isDeuringModelOver_of_cited hGonzalezDivisionPolynomial
      hGonzalezMultiplicationByP hp hp5 hL _ hD,
    div_self (pow_ne_zero _ (by norm_num))]

/-- **Theorem 1.2** (supersingular containment), in terms of Vélu's quotient: for `p ≥ 5`, a
prime `ℓ ≠ p` and a pair `(E, C)` over `L` with `E` supersingular,
`R_ℓ(E, C) ^ ((p² - 1) / 12) = 1`. -/
theorem veluRatio_pow_eq_one (hcited : CitedResults.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (P : Pair ℓ L)
    (hss : P.curve.IsSupersingularOver p) : P.veluRatio ^ ((p ^ 2 - 1) / 12) = 1 :=
  veluRatio_pow_eq_one_of_cited hcited.gonzalezDivisionPolynomial hcited.gonzalezMultiplicationByP
    hcited.supersingularJInvariant hcited.veluIsogeny hp hp5 hL hℓ hℓp P hss

end Gamma0.Pair
