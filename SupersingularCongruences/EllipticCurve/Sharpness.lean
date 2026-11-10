/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.EllipticCurve.DeuringModel

/-!
# Sharpness of the exponent `12` (Remark 4.1, first assertion)

For `p ≡ 1 (mod 4)`, Theorem 1.3 gives `κ(E) = -1` for a Deuring model `E`: its discriminant is
not a twelfth power of an element of `𝔽_{p²}`. (The second assertion of Remark 4.1, the numerical
example at `p = 11`, is `LevelTwo.remark_sharp_zmod_eleven`.)
-/

public section

universe u

namespace WeierstrassCurve

variable {L : Type u} [Field L] [IsAlgClosed L] [DecidableEq L] {p : ℕ} [CharP L p]

/-- **Remark 4.1** (first assertion): if `p ≥ 5`, `p ≡ 1 (mod 4)` and `W` is a Deuring model over
an algebraic closure `L` of `𝔽_p`, then `Δ(W)` is not the twelfth power of an element of
`𝔽_{p²}` (an element `b` with `b ^ (p ^ 2) = b`). -/
theorem not_exists_pow_twelve_of_isDeuringModelOver
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp4 : p % 4 = 1) (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (W : WeierstrassCurve L)
    [W.IsElliptic] [W.IsShortNF] (hD : W.IsDeuringModelOver p) :
    ¬ ∃ b : L, b ^ p ^ 2 = b ∧ W.Δ = b ^ 12 := by
  rintro ⟨b, hb, hΔ⟩
  have hκ := Δ_pow_of_isDeuringModelOver_of_cited hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hp hp5 hL W hD
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact W.isUnit_Δ.ne_zero (by rw [hΔ]; norm_num)
  have h12 : 12 * ((p ^ 2 - 1) / 12) = p ^ 2 - 1 := by
    have h2 : p % 2 = 1 := by omega
    have h3 : p % 3 ≠ 0 := fun h ↦ by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h)
      omega
    have hmod : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by omega
    have hsq : p ^ 2 % 12 = 1 := by
      rw [Nat.pow_mod]
      rcases hmod with h | h | h | h <;> rw [h]
    omega
  have hb1 : b ^ (p ^ 2 - 1) = 1 := by
    have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    refine mul_right_cancel₀ hb0 ?_
    rw [← pow_succ, Nat.sub_add_cancel hp1, hb, one_mul]
  have hodd : (p + 1) / 2 % 2 = 1 := by omega
  rw [hΔ, ← pow_mul, h12, hb1, ← Nat.div_add_mod ((p + 1) / 2) 2, hodd, pow_add, pow_mul] at hκ
  norm_num at hκ
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff L p 2).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd two_pos this
    omega
  exact h2 (by linear_combination hκ)

end WeierstrassCurve
