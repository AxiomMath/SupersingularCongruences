/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.EllipticCurve.OverClosure
public import SupersingularCongruences.EllipticCurve.Scaling
public import SupersingularCongruences.EllipticCurve.DiscriminantPower
public import SupersingularCongruences.External
import all SupersingularCongruences.EllipticCurve.DiscriminantPower
import all SupersingularCongruences.EllipticCurve.OverClosure

/-!
# Deuring models over an algebraic closure of `𝔽_p`

Let `L` be an algebraic closure of `𝔽_p`, `p ≥ 5`.

* `WeierstrassCurve.Δ_pow_of_isDeuringModelOver`: **Theorem 1.3** over `L`: for a Deuring model
  `E` (coefficients in `𝔽_{p²}`, `π_E = [-p]`),
  `Δ(E, dx / (2y)) ^ ((p² - 1) / 12) = (-1)^((p+1)/2)`.
* `WeierstrassCurve.inv_pow_twelve_mul_Δ_pow_of_isDeuringModelOver`: **Theorem 1.3** over `L`
  for every `𝔽_{p²}`-rational differential `ω = u · dx / (2y)`, `u ^ (p ^ 2) = u`:
  `Δ(E, ω) ^ ((p² - 1) / 12) = ((u ^ 12)⁻¹ Δ(W)) ^ ((p² - 1) / 12) = (-1)^((p+1)/2)`.
* `WeierstrassCurve.IsDeuringModelOver.isSupersingularOver`: a Deuring model is supersingular.
* `WeierstrassCurve.exists_isDeuringModelOver_scaling`: **Lemma 4.3(a)**: every supersingular
  short Weierstrass curve over `L` is isomorphic (by a scaling) to a Deuring model.

## Proofs

Theorem 1.3 is the deduction from [gonzalez2022, Theorem 3.2 and Lemma 3.1] at the end of
Section 4.2 of the manuscript: on a Deuring model `[p] = [-1] ∘ π_E`, so González's automorphism
`u (x, y) = (ψ⁻² x, ψ⁻³ y)` is `[-1]` and `ψ_{E,p} = -1`; González's formula for `ψ_{E,p}` and
`Δ = -64 D`, `(-64) ^ m = 1` conclude.

Lemma 4.3(a): `j(E) ∈ 𝔽_{p²}` [silverman-aec, Theorem V.3.1(a)] gives a scaling `E₁` of `E` with
coefficients in `𝔽_{p²}`. The factorization `π_{E₁} = u ∘ [p]` with `u` an automorphism is taken
from [gonzalez2022, Lemma 3.1], which gives `p • (x, y) = (ψ⁻² x ^ (p²), ψ⁻³ y ^ (p²))`
(the manuscript derives the factorization from [silverman-aec, Corollary II.2.12], and cites
González's lemma for the same `u` at the end of Section 4.2). The twist is explicit: for `γ` with
`γ ^ (p² - 1) = -ψ⁻¹`, the scaling `E₁.scaling γ` satisfies `π = [-p]`: the scaling
`ψ_γ (x, y) = (γ² x, γ³ y)` satisfies `π (ψ_γ Q) = (c² γ² x_Q^{p²}, c³ γ³ y_Q^{p²})`,
`c = γ ^ (p² - 1)`, which is `ψ_γ (-(p • Q))` since `c = -ψ⁻¹`. The coefficients of `E₁.scaling γ`
are fixed by `x ↦ x ^ (p²)` because `ψ⁴ a₄ = a₄` and `ψ⁶ a₆ = a₆` (`u` is an automorphism of `E₁`).
-/

public section

open Polynomial WeierstrassCurve.Affine

universe u

namespace WeierstrassCurve

variable {L : Type u} [Field L] [IsAlgClosed L] [DecidableEq L] {p : ℕ} [CharP L p]

omit [IsAlgClosed L] [CharP L p] in
/-- Unfolding `IsSupersingularOver`: no nonzero `p`-torsion point over `L`. -/
theorem isSupersingularOver_iff {W : WeierstrassCurve L} :
    W.IsSupersingularOver p ↔ ∀ P : W.toAffine.Point, p • P = 0 → P = 0 :=
  Iff.rfl

omit [IsAlgClosed L] [CharP L p] in
/-- A Deuring model is supersingular: if `p • P = 0` then `π_E(P) = -(p • P) = 0`, so `P = 0`. -/
theorem IsDeuringModelOver.isSupersingularOver {W : WeierstrassCurve L}
    (hD : W.IsDeuringModelOver p) : W.IsSupersingularOver p := by
  rintro (_ | ⟨x, y, h⟩) hP
  · rfl
  · obtain ⟨h', e⟩ := hD.frobenius_eq x y h
    rw [hP, neg_zero] at e
    exact absurd e (Point.some_ne_zero _)

/-- **Theorem 1.3** over `L` (for the standard differential), from the cited results it uses,
[gonzalez2022, Theorem 3.2 and Lemma 3.1]: if `p ≥ 5` and the short Weierstrass curve `W` over `L`
is a Deuring model, then `Δ(W) ^ ((p² - 1) / 12) = (-1)^((p+1)/2)`. -/
theorem Δ_pow_of_isDeuringModelOver_of_cited
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (W : WeierstrassCurve L) [W.IsElliptic]
    [W.IsShortNF] (hD : W.IsDeuringModelOver p) :
    W.Δ ^ ((p ^ 2 - 1) / 12) = (-1) ^ ((p + 1) / 2) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, k, hmk, hk⟩ := exists_twelve_mul hp hp5
  set m := (p ^ 2 - 1) / 12
  have hW := hD.isSupersingularOver
  -- The Deuring condition: `p • (x, y) = -(x ^ (p ^ 2), y ^ (p ^ 2))`.
  have hfrob : ∀ (x y : L) (h : W.toAffine.Nonsingular x y),
      ∃ h' : W.toAffine.Nonsingular (x ^ (p ^ 2)) (-y ^ (p ^ 2)),
        p • Point.some x y h = Point.some _ _ h' := by
    intro x y h
    obtain ⟨h', e⟩ := hD.frobenius_eq x y h
    have hnegY : W.toAffine.negY (x ^ (p ^ 2)) (y ^ (p ^ 2)) = -y ^ (p ^ 2) := by
      simp [Affine.negY]
    have h'' : W.toAffine.Nonsingular (x ^ (p ^ 2)) (-y ^ (p ^ 2)) := by
      rw [← hnegY]; exact (Affine.nonsingular_neg ..).mpr h'
    refine ⟨h'', ?_⟩
    rw [← neg_neg (p • Point.some x y h), ← e, Point.neg_some]
    exact Point.some_eq_some rfl hnegY
  -- `ψ_{E,p} = -1` and González's formula give `(-1) ^ ((p - 1) / 2) D ^ m = -1`.
  have hψ := coeff_zero_preΨ_eq_neg_one hGonzalezMultiplicationByP hp hp5 W hL hD.a₄_pow
    hD.a₆_pow hW hfrob
  rw [hGonzalezDivisionPolynomial hp hp5 W hL hW, coeff_C_zero] at hψ
  -- `Δ = -64 D` and `(-64) ^ m = 1`.
  have h2 : (2 : L) ≠ 0 := fun h => by
    have := Nat.le_of_dvd two_pos ((CharP.cast_eq_zero_iff L p 2).mp (by exact_mod_cast h))
    omega
  have h4 : (4 : L) ≠ 0 := by
    have := mul_ne_zero h2 h2; norm_num at this; exact this
  have hΔ : W.Δ = -64 * (W.a₄ ^ 3 + 27 * W.a₆ ^ 2 / 4) := by
    rw [Δ_of_isShortNF]; field_simp; ring
  have h64 : (-64 : L) ^ m = 1 := by
    rw [hmk, pow_mul, show (-64 : L) ^ 2 = 2 ^ 12 by norm_num, ← pow_mul, hk, pow_mul,
      two_pow_sub_one (by omega), one_pow]
  have hodd : (p + 1) / 2 = (p - 1) / 2 + 1 := by
    have := hp.eq_one_or_self_of_dvd 2; omega
  have hsq : ((-1 : L) ^ ((p - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [hΔ, mul_pow, h64, one_mul, hodd, pow_succ]
  linear_combination (-1 : L) ^ ((p - 1) / 2) * hψ -
    (W.a₄ ^ 3 + 27 * W.a₆ ^ 2 / 4) ^ m * hsq

/-- **Theorem 1.3** over `L` (for the standard differential): if `p ≥ 5` and the short
Weierstrass curve `W` over `L` is a Deuring model, then `Δ(W) ^ ((p² - 1) / 12) = (-1)^((p+1)/2)`.
-/
theorem Δ_pow_of_isDeuringModelOver (hcited : CitedResults.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (W : WeierstrassCurve L) [W.IsElliptic]
    [W.IsShortNF] (hD : W.IsDeuringModelOver p) :
    W.Δ ^ ((p ^ 2 - 1) / 12) = (-1) ^ ((p + 1) / 2) :=
  Δ_pow_of_isDeuringModelOver_of_cited hcited.gonzalezDivisionPolynomial
    hcited.gonzalezMultiplicationByP hp hp5 hL W hD

omit [IsAlgClosed L] [DecidableEq L] [CharP L p] in
/-- For a prime `p ≥ 5` and `u ∈ 𝔽_{p²}ˣ` (i.e. `u ^ (p ^ 2) = u`),
`(u ^ 12) ^ ((p² - 1) / 12) = 1`. -/
lemma pow_twelve_pow_eq_one (hp : p.Prime) (hp5 : 5 ≤ p) (u : Lˣ) (hu : (u : L) ^ p ^ 2 = u) :
    ((u : L) ^ 12) ^ ((p ^ 2 - 1) / 12) = 1 := by
  rw [← pow_mul, (exists_twelve_mul hp hp5).1]
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  refine mul_left_cancel₀ u.ne_zero ?_
  rw [mul_one, ← pow_succ', Nat.sub_add_cancel h1, hu]

/-- **Theorem 1.3** over `L`, for every `𝔽_{p²}`-rational differential: if `p ≥ 5`, the short
Weierstrass curve `W` over `L` is a Deuring model and `ω = u · dx / (2y)` with `u ∈ 𝔽_{p²}ˣ`
(`u ^ (p ^ 2) = u`), then `Δ(E, ω) ^ ((p² - 1) / 12) = ((u ^ 12)⁻¹ Δ(W)) ^ ((p² - 1) / 12)`
equals `(-1)^((p+1)/2)`. -/
theorem inv_pow_twelve_mul_Δ_pow_of_isDeuringModelOver
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (W : WeierstrassCurve L) [W.IsElliptic]
    [W.IsShortNF] (hD : W.IsDeuringModelOver p) (u : Lˣ) (hu : (u : L) ^ p ^ 2 = u) :
    (((u : L) ^ 12)⁻¹ * W.Δ) ^ ((p ^ 2 - 1) / 12) = (-1) ^ ((p + 1) / 2) := by
  rw [mul_pow, inv_pow, pow_twelve_pow_eq_one hp hp5 u hu, inv_one, one_mul,
    Δ_pow_of_isDeuringModelOver_of_cited hGonzalezDivisionPolynomial hGonzalezMultiplicationByP hp
      hp5 hL W hD]

omit [IsAlgClosed L] [DecidableEq L] [CharP L p] in
/-- Scaling by `u * v` is scaling by `u` followed by scaling by `v`. -/
lemma scaling_mul (W : WeierstrassCurve L) (u v : Lˣ) :
    W.scaling (u * v) = (W.scaling u).scaling v := by
  ext <;> simp only [scaling_a₁, scaling_a₂, scaling_a₃, scaling_a₄, scaling_a₆, Units.val_mul] <;>
    ring

omit [IsAlgClosed L] [DecidableEq L] [CharP L p] in
private lemma exists_some_eq_some {W : Affine L} {X Y X' Y' : L} (hR : W.Nonsingular X' Y')
    (hX : X = X') (hY : Y = Y') :
    ∃ h' : W.Nonsingular X Y, Point.some X Y h' = Point.some X' Y' hR := by
  subst hX hY; exact ⟨hR, rfl⟩

/-- **Lemma 4.3(a)** (Deuring models): if `p ≥ 5` and `W` is a supersingular short Weierstrass
elliptic curve over `L`, then some scaling `W.scaling u`, isomorphic to `W` over `L`, is a Deuring
model: its coefficients lie in `𝔽_{p²}` and its `p²`-power Frobenius endomorphism is `[-p]`. -/
theorem exists_isDeuringModelOver_scaling
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : SupersingularJInvariant.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (W : WeierstrassCurve L) [W.IsElliptic]
    [W.IsShortNF] (hW : W.IsSupersingularOver p) :
    ∃ u : Lˣ, (W.scaling u).IsDeuringModelOver p := by
  have : Fact p.Prime := ⟨hp⟩
  -- A model `W₁` over `𝔽_{p²}` [silverman-aec, Theorem V.3.1(a)].
  obtain ⟨u, h4, h6⟩ := exists_scaling_pow_eq hp hp5 W (hSupersingularJInvariant hp W hW)
  set W₁ := W.scaling u with hW₁def
  have hW₁ : ∀ P : W₁.toAffine.Point, p • P = 0 → P = 0 :=
    Point.eq_zero_of_nsmul_eq_zero_scaling W u hW
  -- González's automorphism `(x, y) ↦ (ψ⁻² x, ψ⁻³ y)`: `ψ⁴ a₄ = a₄`, `ψ⁶ a₆ = a₆`.
  obtain ⟨hψ0, ha₄, ha₆, -, -⟩ := supersingular_aux hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hp hp5 W₁ hL h4 h6 hW₁
  set ψ := (W₁.preΨ p).coeff 0 with hψdef
  rw [h4] at ha₄
  rw [h6] at ha₆
  have e4 : ψ⁻¹ ^ 4 * W₁.a₄ = W₁.a₄ := by
    calc ψ⁻¹ ^ 4 * W₁.a₄ = ψ⁻¹ ^ 4 * (ψ ^ 4 * W₁.a₄) := by rw [← ha₄]
      _ = W₁.a₄ := by field_simp
  have e6 : ψ⁻¹ ^ 6 * W₁.a₆ = W₁.a₆ := by
    calc ψ⁻¹ ^ 6 * W₁.a₆ = ψ⁻¹ ^ 6 * (ψ ^ 6 * W₁.a₆) := by rw [← ha₆]
      _ = W₁.a₆ := by field_simp
  -- The twist: `γ ^ (p ^ 2 - 1) = -ψ⁻¹`.
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  have hpos : p ^ 2 - 1 ≠ 0 := by
    have : 2 ≤ p := hp.two_le
    have : 4 ≤ p ^ 2 := by nlinarith
    omega
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (-ψ⁻¹) (Nat.pos_of_ne_zero hpos)
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    exact neg_ne_zero.mpr (inv_ne_zero hψ0) (by rw [← hγ, zero_pow hpos])
  have hγq : γ ^ p ^ 2 = -ψ⁻¹ * γ := by
    rw [← hγ, ← pow_succ, Nat.sub_add_cancel h1]
  have hpow : ∀ n : ℕ, (γ ^ n) ^ p ^ 2 = (-ψ⁻¹) ^ n * γ ^ n := fun n => by
    rw [← pow_mul, mul_comm, pow_mul, hγq, mul_pow]
  refine ⟨u * Units.mk0 γ hγ0, ?_⟩
  rw [scaling_mul, ← hW₁def]
  refine
    { a₁_pow := by simp [zero_pow (pow_ne_zero 2 hp.ne_zero)]
      a₂_pow := by simp [zero_pow (pow_ne_zero 2 hp.ne_zero)]
      a₃_pow := by simp [zero_pow (pow_ne_zero 2 hp.ne_zero)]
      a₄_pow := ?_
      a₆_pow := ?_
      frobenius_eq := ?_ }
  · simp only [scaling_a₄, Units.val_mk0]
    rw [mul_pow, hpow, h4]
    linear_combination γ ^ 4 * e4
  · simp only [scaling_a₆, Units.val_mk0]
    rw [mul_pow, hpow, h6]
    linear_combination γ ^ 6 * e6
  · intro x y h
    set γu := Units.mk0 γ hγ0
    obtain ⟨Q, hQ⟩ := Point.scaling_surjective W₁ γu (Point.some x y h)
    rcases Q with _ | ⟨x₁, y₁, h₁⟩
    · exact absurd hQ.symm
        (by rw [← Point.zero_def, Point.scaling_zero]; exact Point.some_ne_zero _)
    rw [← hQ, ← map_nsmul]
    obtain ⟨h₂, e₂⟩ := hGonzalezMultiplicationByP hp hp5 W₁ hL h4 h6 hW₁ h₁
    rw [Point.scaling_some, Point.some.injEq] at hQ
    obtain ⟨rfl, rfl⟩ := hQ
    rw [e₂, Point.scaling_some, Point.neg_some]
    refine exists_some_eq_some _ ?_ ?_
    · simp only [γu, Units.val_mk0]
      rw [mul_pow, hpow]; ring
    · simp only [γu, Units.val_mk0, Affine.negY, a₁_of_isShortNF, a₃_of_isShortNF]
      rw [mul_pow, hpow]; ring

end WeierstrassCurve
