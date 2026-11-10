/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.EllipticCurve.DeuringModel
import all SupersingularCongruences.EllipticCurve.DiscriminantPower

/-!
# Corollary 4.7 via Deuring models

Let `L` be an algebraic closure of `𝔽_p`, `p ≥ 5`, and `m = (p² - 1) / 12`.

* `WeierstrassCurve.IsDeuringModelOver.exists_inv_pow_twelve_mul_Δ_eq_pow_three`,
  `WeierstrassCurve.IsDeuringModelOver.exists_inv_pow_twelve_mul_Δ_eq_sq`: **Corollary 4.7**
  (first assertion) over `L`: for a Deuring model `E` and an `𝔽_{p²}`-rational differential
  `ω = u · dx / (2y)`, `Δ(E, ω) = (u ^ 12)⁻¹ Δ(W)` is a cube and a square of elements of `𝔽_{p²}`.
* `WeierstrassCurve.exists_j_eq_pow_three_of_isSupersingularOver`,
  `WeierstrassCurve.exists_j_sub_1728_eq_sq_of_isSupersingularOver`: **Corollary 4.7**
  ("consequently" part): for every supersingular short Weierstrass curve over `L`, `j = c ^ 3` and
  `j - 1728 = s ^ 2` with `c, s ∈ 𝔽_{p²}`.

This follows the manuscript's route: by Theorem 1.3, `Δ ^ ((p² - 1) / 3) = κ ^ 4 = 1` and
`Δ ^ ((p² - 1) / 2) = κ ^ 6 = 1`, so the cube and square roots of `Δ` in `L` lie in `𝔽_{p²}`;
`j = c₄³ / Δ`, `j - 1728 = c₆² / Δ` with `c₄, c₆ ∈ 𝔽_{p²}`, and every supersingular `j` is the
`j`-invariant of a Deuring model by Lemma 4.3(a)
(`WeierstrassCurve.exists_isDeuringModelOver_scaling`).
(The variants `WeierstrassCurve.exists_j_eq_pow_three_of_supersingular` in
`SupersingularCongruences.EllipticCurve.DiscriminantPower` avoid Lemma 4.3.)
-/

public section

universe u

namespace WeierstrassCurve

variable {L : Type u} [Field L] [IsAlgClosed L] [DecidableEq L] {p : ℕ} [CharP L p]

/-- **Corollary 4.7** (cube, standard differential): the discriminant of a Deuring model over `L`
is the cube of an element of `𝔽_{p²}`. -/
theorem IsDeuringModelOver.exists_Δ_eq_pow_three
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) {W : WeierstrassCurve L} [W.IsElliptic]
    [W.IsShortNF] (hD : W.IsDeuringModelOver p) : ∃ t : L, t ^ p ^ 2 = t ∧ W.Δ = t ^ 3 := by
  obtain ⟨hm12, -⟩ := exists_twelve_mul hp hp5
  have hκ := Δ_pow_of_isDeuringModelOver_of_cited hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hp hp5 hL W hD
  set m := (p ^ 2 - 1) / 12
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq W.Δ (n := 3) (by norm_num)
  refine ⟨t, ?_, ht.symm⟩
  have he : p ^ 2 - 1 = 3 * (m * 4) := by omega
  have h1 : t ^ (p ^ 2 - 1) = 1 := by
    rw [he, pow_mul, ht, pow_mul, hκ, ← pow_mul, mul_comm, pow_mul,
      show ((-1 : L) ^ 4) = 1 by norm_num, one_pow]
  calc t ^ p ^ 2 = t ^ (p ^ 2 - 1) * t := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)]
    _ = t := by rw [h1, one_mul]

/-- **Corollary 4.7** (square, standard differential): the discriminant of a Deuring model over
`L` is the square of an element of `𝔽_{p²}`. -/
theorem IsDeuringModelOver.exists_Δ_eq_sq
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) {W : WeierstrassCurve L} [W.IsElliptic]
    [W.IsShortNF] (hD : W.IsDeuringModelOver p) : ∃ r : L, r ^ p ^ 2 = r ∧ W.Δ = r ^ 2 := by
  obtain ⟨hm12, -⟩ := exists_twelve_mul hp hp5
  have hκ := Δ_pow_of_isDeuringModelOver_of_cited hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hp hp5 hL W hD
  set m := (p ^ 2 - 1) / 12
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq W.Δ (n := 2) (by norm_num)
  refine ⟨r, ?_, hr.symm⟩
  have he : p ^ 2 - 1 = 2 * (m * 6) := by omega
  have h1 : r ^ (p ^ 2 - 1) = 1 := by
    rw [he, pow_mul, hr, pow_mul, hκ, ← pow_mul, mul_comm, pow_mul,
      show ((-1 : L) ^ 6) = 1 by norm_num, one_pow]
  calc r ^ p ^ 2 = r ^ (p ^ 2 - 1) * r := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)]
    _ = r := by rw [h1, one_mul]

/-- **Corollary 4.7** (first assertion, cube) over `L`: for a Deuring model and an
`𝔽_{p²}`-rational differential `ω = u · dx / (2y)`, `Δ(E, ω) = (u ^ 12)⁻¹ Δ(W)` is the cube of an
element of `𝔽_{p²}`. -/
theorem IsDeuringModelOver.exists_inv_pow_twelve_mul_Δ_eq_pow_three
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) {W : WeierstrassCurve L} [W.IsElliptic]
    [W.IsShortNF] (hD : W.IsDeuringModelOver p) (u : Lˣ) (hu : (u : L) ^ p ^ 2 = u) :
    ∃ t : L, t ^ p ^ 2 = t ∧ ((u : L) ^ 12)⁻¹ * W.Δ = t ^ 3 := by
  obtain ⟨t, htq, ht⟩ := hD.exists_Δ_eq_pow_three hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hp hp5 hL
  refine ⟨((u : L) ^ 4)⁻¹ * t, ?_, ?_⟩
  · rw [mul_pow, inv_pow, ← pow_mul, mul_comm 4 (p ^ 2), pow_mul, hu, htq]
  · rw [ht]; ring

/-- **Corollary 4.7** (first assertion, square) over `L`: for a Deuring model and an
`𝔽_{p²}`-rational differential `ω = u · dx / (2y)`, `Δ(E, ω) = (u ^ 12)⁻¹ Δ(W)` is the square of an
element of `𝔽_{p²}`. -/
theorem IsDeuringModelOver.exists_inv_pow_twelve_mul_Δ_eq_sq
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) {W : WeierstrassCurve L} [W.IsElliptic]
    [W.IsShortNF] (hD : W.IsDeuringModelOver p) (u : Lˣ) (hu : (u : L) ^ p ^ 2 = u) :
    ∃ r : L, r ^ p ^ 2 = r ∧ ((u : L) ^ 12)⁻¹ * W.Δ = r ^ 2 := by
  obtain ⟨r, hrq, hr⟩ := hD.exists_Δ_eq_sq hGonzalezDivisionPolynomial hGonzalezMultiplicationByP hp
    hp5 hL
  refine ⟨((u : L) ^ 6)⁻¹ * r, ?_, ?_⟩
  · rw [mul_pow, inv_pow, ← pow_mul, mul_comm 6 (p ^ 2), pow_mul, hu, hrq]
  · rw [hr]; ring

/-- **Corollary 4.7** (`j` is a cube in `𝔽_{p²}`) for a Deuring model over `L`. -/
theorem IsDeuringModelOver.exists_j_eq_pow_three
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) {W : WeierstrassCurve L} [W.IsElliptic]
    [W.IsShortNF] (hD : W.IsDeuringModelOver p) : ∃ c : L, c ^ p ^ 2 = c ∧ W.j = c ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, htq, ht⟩ := hD.exists_Δ_eq_pow_three hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hp hp5 hL
  refine ⟨W.c₄ / t, ?_, ?_⟩
  · have h48 : (-48 : L) ^ (p ^ 2) = -48 := by
      rw [← iterateFrobenius_def (R := L) (p := p) (n := 2), map_neg, map_ofNat]
    rw [div_pow, c₄_of_isShortNF, mul_pow, hD.a₄_pow, htq, h48]
  · rw [j, Units.val_inv_eq_inv_val, coe_Δ', ht, div_pow, div_eq_inv_mul]

/-- **Corollary 4.7** (`j - 1728` is a square in `𝔽_{p²}`) for a Deuring model over `L`. -/
theorem IsDeuringModelOver.exists_j_sub_1728_eq_sq
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) {W : WeierstrassCurve L} [W.IsElliptic]
    [W.IsShortNF] (hD : W.IsDeuringModelOver p) : ∃ s : L, s ^ p ^ 2 = s ∧ W.j - 1728 = s ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hrq, hr⟩ := hD.exists_Δ_eq_sq hGonzalezDivisionPolynomial hGonzalezMultiplicationByP hp
    hp5 hL
  have hΔ0 : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  have hr0 : r ≠ 0 := by rintro rfl; exact hΔ0 (by simpa using hr)
  refine ⟨W.c₆ / r, ?_, ?_⟩
  · have h864 : (-864 : L) ^ (p ^ 2) = -864 := by
      rw [← iterateFrobenius_def (R := L) (p := p) (n := 2), map_neg, map_ofNat]
    rw [div_pow, c₆_of_isShortNF, mul_pow, hD.a₆_pow, hrq, h864]
  · have hrel := W.c_relation
    rw [j, Units.val_inv_eq_inv_val, coe_Δ']
    field_simp
    linear_combination (-r ^ 2) * hrel - W.c₆ ^ 2 * hr

/-- **Corollary 4.7** ("consequently", cube; Morton's theorem), via Deuring models: for every
supersingular short Weierstrass elliptic curve `W` over an algebraic closure `L` of `𝔽_p`
(`p ≥ 5`), `j(W) = c ^ 3` for some `c ∈ 𝔽_{p²}`. -/
theorem exists_j_eq_pow_three_of_isSupersingularOver
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : SupersingularJInvariant.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (W : WeierstrassCurve L) [W.IsElliptic]
    [W.IsShortNF] (hW : W.IsSupersingularOver p) : ∃ c : L, c ^ p ^ 2 = c ∧ W.j = c ^ 3 := by
  obtain ⟨u, hu⟩ := exists_isDeuringModelOver_scaling hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hSupersingularJInvariant hp hp5 hL W hW
  rw [← scaling_j W u]
  exact hu.exists_j_eq_pow_three hGonzalezDivisionPolynomial hGonzalezMultiplicationByP hp hp5 hL

/-- **Corollary 4.7** ("consequently", square), via Deuring models: for every supersingular short
Weierstrass elliptic curve `W` over an algebraic closure `L` of `𝔽_p` (`p ≥ 5`),
`j(W) - 1728 = s ^ 2` for some `s ∈ 𝔽_{p²}`. -/
theorem exists_j_sub_1728_eq_sq_of_isSupersingularOver
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : SupersingularJInvariant.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (W : WeierstrassCurve L) [W.IsElliptic]
    [W.IsShortNF] (hW : W.IsSupersingularOver p) :
    ∃ s : L, s ^ p ^ 2 = s ∧ W.j - 1728 = s ^ 2 := by
  obtain ⟨u, hu⟩ := exists_isDeuringModelOver_scaling hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hSupersingularJInvariant hp hp5 hL W hW
  rw [← scaling_j W u]
  exact hu.exists_j_sub_1728_eq_sq hGonzalezDivisionPolynomial hGonzalezMultiplicationByP hp hp5 hL

end WeierstrassCurve
