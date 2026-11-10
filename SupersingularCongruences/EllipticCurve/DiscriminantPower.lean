/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.EllipticCurve.Supersingular
public import SupersingularCongruences.External
public import SupersingularCongruences.EllipticCurve.Scaling

/-!
# Rationality of supersingular discriminants

Let `p ≥ 5` be prime, `K` a field with `p ^ 2` elements and `m = (p ^ 2 - 1) / 12`. For an elliptic
curve `E / K` and a nonzero `K`-rational invariant differential `ω`, the manuscript sets
`κ(E) = Δ(E, ω) ^ m`. For a short Weierstrass model `W` with its standard differential
`ω₀ = dx / (2y)` one has `Δ(E, ω₀) = W.Δ`, and the `K`-rational differentials are `ω = u⁻¹ ω₀` with
`u ∈ Kˣ`, for which `Δ(E, ω) = u ^ 12 * W.Δ`.

## Main results

* `WeierstrassCurve.unit_pow_twelve_mul_Δ_pow`: Lemma 4.4 (first assertion), `κ(E)` does not
  depend on `ω`.
* `WeierstrassCurve.unit_pow_twelve_mul_Δ_pow_of_isDeuringModel`: **Theorem 1.3**: if `E` is
  supersingular with `π_E = [-p]`, then `κ(E) = (-1) ^ ((p + 1) / 2)`.
* `WeierstrassCurve.isSquare_unit_pow_twelve_mul_Δ_of_isDeuringModel`,
  `WeierstrassCurve.exists_unit_pow_twelve_mul_Δ_eq_pow_three_of_isDeuringModel`,
  `WeierstrassCurve.exists_j_eq_pow_three_of_isDeuringModel`,
  `WeierstrassCurve.isSquare_j_sub_1728_of_isDeuringModel`: Corollary 4.7 for Deuring models:
  `Δ(E, ω)` is a square and a cube in `K`, `j(E)` is a cube and `j(E) - 1728` is a square.
* `WeierstrassCurve.exists_j_eq_pow_three_of_supersingular`,
  `WeierstrassCurve.exists_j_sub_1728_eq_sq_of_supersingular`: Corollary 4.7, "consequently" part:
  for every supersingular short Weierstrass curve over an algebraic closure `L` of `𝔽_p`
  (`p ≥ 5`), `j = c ^ 3` and `j - 1728 = s ^ 2` with `c, s ∈ F_{p²}` (i.e. `c ^ (p ^ 2) = c`,
  `s ^ (p ^ 2) = s`). The manuscript deduces this from the Deuring models of Lemma 4.3
  (formalized separately as `WeierstrassCurve.exists_isDeuringModelOver_scaling`). Here
  `j ∈ F_{p²}` [silverman-aec, Theorem V.3.1(a)] gives an `L`-isomorphic model
  `y² = x³ + u⁴ a₄ x + u⁶ a₆` over `F_{p²}` (`WeierstrassCurve.scaling`), to which
  [gonzalez2022, Lemma 3.1 and Theorem 3.2] apply.

The proof of Theorem 1.3 is the deduction from [gonzalez2022, Theorem 3.2 and Lemma 3.1] given at
the end of Section 4.2 of the manuscript (the cited results
`WeierstrassCurve.GonzalezDivisionPolynomial` and `WeierstrassCurve.GonzalezMultiplicationByP`,
taken as hypotheses and applied to the base change of the curve to the
algebraic closure, whose coefficients lie in `F_{p²}`). The manuscript's own proof via eta powers
(Proposition 4.5) is formalized separately as
`WeierstrassCurve.discriminant_pow_of_isDeuringModelOver_eta`.
-/

public section

open Polynomial WeierstrassCurve.Affine

universe u

/-- In a finite field `F` with `q` elements, if `n ∣ q - 1` and `a ≠ 0` satisfies
`a ^ ((q - 1) / n) = 1`, then `a` is an `n`-th power. -/
lemma FiniteField.exists_eq_pow_of_pow_card_sub_one_div_eq_one {F : Type*} [Field F] [Fintype F]
    {n : ℕ} (hn : n ∣ Fintype.card F - 1) {a : F} (ha : a ≠ 0)
    (h : a ^ ((Fintype.card F - 1) / n) = 1) : ∃ b : F, a = b ^ n := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨k, hk⟩ : Units.mk0 a ha ∈ Submonoid.powers g := by
    rw [mem_powers_iff_mem_zpowers]; exact hg _
  dsimp only at hk
  have hord : orderOf g = Fintype.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units]
  have hq : 0 < Fintype.card F - 1 := by have := Fintype.one_lt_card (α := F); omega
  obtain ⟨c, hc⟩ := hn
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hc; omega
  have hc0 : 0 < c := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hc; omega
  have hdiv : (Fintype.card F - 1) / n = c := by rw [hc, Nat.mul_div_cancel_left _ hn0]
  have hpow : g ^ (k * c) = 1 := by
    rw [pow_mul, hk]; ext; simpa [hdiv] using h
  have hdvd := orderOf_dvd_of_pow_eq_one hpow
  rw [hord, hc] at hdvd
  obtain ⟨d, rfl⟩ : n ∣ k := Nat.dvd_of_mul_dvd_mul_right hc0 hdvd
  refine ⟨((g ^ d : Fˣ) : F), ?_⟩
  rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm d n, hk, Units.val_mk0]

namespace WeierstrassCurve

section Arithmetic

/-- For a prime `p ≥ 5`, `p ^ 2 ≡ 1 [MOD 24]`. -/
private lemma sq_mod_twentyFour {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : p ^ 2 % 24 = 1 := by
  have h2 : p % 2 ≠ 0 := fun h => by
    have := hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h); omega
  have h3 : p % 3 ≠ 0 := fun h => by
    have := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h); omega
  have : p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 ∨ p % 24 = 13 ∨ p % 24 = 17 ∨
      p % 24 = 19 ∨ p % 24 = 23 := by omega
  rw [Nat.pow_mod]
  rcases this with h | h | h | h | h | h | h | h <;> rw [h]

/-- Arithmetic of `m = (p ^ 2 - 1) / 12` for a prime `p ≥ 5`: `12 * m = p ^ 2 - 1`, `m = 2 k` and
`12 k = (p - 1) * ((p + 1) / 2)`. -/
private lemma exists_twelve_mul {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    12 * ((p ^ 2 - 1) / 12) = p ^ 2 - 1 ∧
      ∃ k, (p ^ 2 - 1) / 12 = 2 * k ∧ 12 * k = (p - 1) * ((p + 1) / 2) := by
  have h24 := sq_mod_twentyFour hp hp5
  obtain ⟨a, ha⟩ := hp.odd_of_ne_two (by omega)
  have hd := Nat.div_add_mod (p ^ 2) 24
  rw [h24] at hd
  refine ⟨by omega, p ^ 2 / 24, by omega, ?_⟩
  have h1 : p - 1 = 2 * a := by omega
  have h2 : (p + 1) / 2 = a + 1 := by omega
  rw [h1, h2]
  subst ha
  nlinarith

end Arithmetic

variable {p : ℕ}

private lemma Point.some_eq_some {R : Type*} [CommRing R] {W : Affine R} {x y x' y' : R}
    {h : W.Nonsingular x y} {h' : W.Nonsingular x' y'} (hx : x = x') (hy : y = y') :
    Point.some x y h = Point.some x' y' h' := by
  subst hx hy; rfl

/-- In characteristic `p ≠ 2`, `2 ^ (p - 1) = 1` (Fermat). -/
private lemma two_pow_sub_one {R : Type*} [Field R] [Fact p.Prime] [CharP R p] (hp2 : p ≠ 2) :
    (2 : R) ^ (p - 1) = 1 := by
  have h2 : (2 : R) ≠ 0 := fun h => hp2 <|
    (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff R p 2).mp (by exact_mod_cast h))
  have hfrob : (2 : R) ^ p = 2 := by
    have := map_ofNat (frobenius R p) 2
    rwa [frobenius_def] at this
  refine mul_right_cancel₀ h2 ?_
  rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le, hfrob, one_mul]

/-- The deduction `ψ_{E,p} = -1` (manuscript, end of Section 4.2): over an algebraically closed
field of characteristic `p ≥ 5`, if a supersingular short Weierstrass curve satisfies
`p • (x, y) = -(x ^ (p ^ 2), y ^ (p ^ 2))` for every affine point and is defined over `F_{p²}`, then
the constant coefficient of its `p`-th division polynomial is `-1`. This combines
[gonzalez2022, Lemma 3.1] with the evaluation at a point with `x ≠ 0` and `y ≠ 0`. -/
private lemma coeff_zero_preΨ_eq_neg_one {L : Type u} [Field L] [IsAlgClosed L] [DecidableEq L]
    [CharP L p] (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime)
    (hp5 : 5 ≤ p) (W : WeierstrassCurve L) [W.IsElliptic]
    [W.IsShortNF] (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x)
    (ha₄ : W.a₄ ^ p ^ 2 = W.a₄) (ha₆ : W.a₆ ^ p ^ 2 = W.a₆)
    (hW : ∀ P : W.toAffine.Point, p • P = 0 → P = 0)
    (hfrob : ∀ (x y : L) (h : W.toAffine.Nonsingular x y),
      ∃ h' : W.toAffine.Nonsingular (x ^ (p ^ 2)) (-y ^ (p ^ 2)),
        p • Point.some x y h = Point.some _ _ h') :
    (W.preΨ p).coeff 0 = -1 := by
  obtain ⟨x, hx0, hfx⟩ : ∃ x : L, x ≠ 0 ∧ x ^ 3 + W.a₄ * x + W.a₆ ≠ 0 := by
    let q : L[X] := X * (X ^ 3 + C W.a₄ * X + C W.a₆)
    have hq : q ≠ 0 := by
      refine mul_ne_zero X_ne_zero (Monic.ne_zero ?_)
      monicity!
    obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset q.roots.toFinset
    refine ⟨x, ?_⟩
    have : q.eval x ≠ 0 := fun h0 => hx (by simpa [Multiset.mem_toFinset, mem_roots hq] using h0)
    simpa [q, not_or] using this
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ 3 + W.a₄ * x + W.a₆) two_pos
  have hy0 : y ≠ 0 := by rintro rfl; exact hfx (by simpa using hy.symm)
  have h : W.toAffine.Nonsingular x y := by
    rw [← Affine.equation_iff_nonsingular, Affine.equation_iff]
    simp [hy]
  obtain ⟨h3, h3eq⟩ := hGonzalezMultiplicationByP hp hp5 W hL ha₄ ha₆ hW h
  obtain ⟨h4, h4eq⟩ := hfrob x y h
  rw [h3eq, Point.some.injEq] at h4eq
  obtain ⟨e1, e2⟩ := h4eq
  set ψ := (W.preΨ p).coeff 0
  have i2 : ψ⁻¹ ^ 2 = 1 := mul_right_cancel₀ (pow_ne_zero (p ^ 2) hx0) (by rw [e1, one_mul])
  have i3 : ψ⁻¹ ^ 3 = -1 :=
    mul_right_cancel₀ (pow_ne_zero (p ^ 2) hy0) (by rw [e2, neg_one_mul])
  have i1 : ψ⁻¹ = -1 := by
    have : ψ⁻¹ ^ 3 = ψ⁻¹ * ψ⁻¹ ^ 2 := by ring
    rw [i2, mul_one, i3] at this
    exact this.symm
  rwa [inv_eq_iff_eq_inv, inv_neg_one] at i1

variable {K : Type u} [Field K] [Fintype K]

/-- The characteristic of a field with `p ^ 2` elements is `p`. -/
private lemma ringChar_eq_of_card (hp : p.Prime) (hK : Fintype.card K = p ^ 2) :
    ringChar K = p := by
  obtain ⟨n, hr, hcard⟩ := FiniteField.card K (ringChar K)
  have hdvd : p ∣ ringChar K ^ (n : ℕ) := by
    rw [← hcard, hK]; exact dvd_pow_self p two_ne_zero
  exact ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hdvd)).symm

/-- **Lemma 4.4** (first assertion). For a field `K` with `p ^ 2` elements (`p ≥ 5` prime), the
quantity `κ(E) = Δ(E, ω) ^ ((p ^ 2 - 1) / 12)` does not depend on the nonzero rational
differential `ω = u⁻¹ ω₀`, for which `Δ(E, ω) = u ^ 12 * W.Δ`. -/
theorem unit_pow_twelve_mul_Δ_pow (hp : p.Prime) (hp5 : 5 ≤ p) (hK : Fintype.card K = p ^ 2)
    (W : WeierstrassCurve K) (u : Kˣ) :
    ((u : K) ^ 12 * W.Δ) ^ ((p ^ 2 - 1) / 12) = W.Δ ^ ((p ^ 2 - 1) / 12) := by
  rw [mul_pow, ← pow_mul, (exists_twelve_mul hp hp5).1, ← hK,
    FiniteField.pow_card_sub_one_eq_one _ u.ne_zero, one_mul]

/-- **Theorem 1.3**, for the standard differential: if `p ≥ 5`, `#K = p ^ 2` and the short
Weierstrass elliptic curve `W` over `K` is supersingular with `π_E = [-p]`, then
`W.Δ ^ ((p ^ 2 - 1) / 12) = (-1) ^ ((p + 1) / 2)`. -/
theorem Δ_pow_of_isDeuringModel (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Fintype.card K = p ^ 2)
    (W : WeierstrassCurve K) [W.IsElliptic] [W.IsShortNF] (hss : W.IsSupersingular)
    (hD : W.IsDeuringModel) :
    W.Δ ^ ((p ^ 2 - 1) / 12) = (-1) ^ ((p + 1) / 2) := by
  classical
  have hchar : ringChar K = p := ringChar_eq_of_card hp hK
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := ringChar.of_eq hchar
  obtain ⟨-, k, hmk, hk⟩ := exists_twelve_mul hp hp5
  set m := (p ^ 2 - 1) / 12
  -- Base change to `L = AlgebraicClosure K`.
  set L := AlgebraicClosure K
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  let WL : WeierstrassCurve L := W.baseChange L
  have : WL.IsElliptic := inferInstanceAs (W.map (algebraMap K L)).IsElliptic
  have : WL.IsShortNF :=
    ⟨by simp [WL, baseChange], by simp [WL, baseChange], by simp [WL, baseChange]⟩
  have hWL : ∀ P : WL.toAffine.Point, p • P = 0 → P = 0 := fun P hP => hss.eq_zero (hchar ▸ hP)
  have hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x :=
    exists_pow_char_pow_eq_self_of_isAlgebraic (K := K) p
  -- The Deuring condition: `p • (x, y) = -(x ^ (p ^ 2), y ^ (p ^ 2))`.
  have hfrob : ∀ (x y : L) (h : WL.toAffine.Nonsingular x y),
      ∃ h' : WL.toAffine.Nonsingular (x ^ (p ^ 2)) (-y ^ (p ^ 2)),
        p • Point.some x y h = Point.some _ _ h' := by
    intro x y h
    obtain ⟨h', hF⟩ := W.frobeniusPoint_some h
    have hnegY : WL.toAffine.negY (x ^ (p ^ 2)) (y ^ (p ^ 2)) = -y ^ (p ^ 2) := by
      simp [Affine.negY]
    have h'' : WL.toAffine.Nonsingular (x ^ (p ^ 2)) (-y ^ (p ^ 2)) := by
      rw [← hnegY, ← hK]; exact (Affine.nonsingular_neg ..).mpr h'
    refine ⟨h'', ?_⟩
    have := hD.frobeniusPoint_eq (Point.some x y h)
    rw [hF, hchar] at this
    rw [← neg_neg (p • Point.some x y h), ← this, Point.neg_some]
    exact Point.some_eq_some (by rw [hK]) (by rw [hK, hnegY])
  -- `ψ_{E,p} = -1` and González's formula give `(-1) ^ ((p - 1) / 2) D ^ m = -1`.
  have hfix : ∀ a : K, (algebraMap K L a) ^ p ^ 2 = algebraMap K L a := fun a => by
    rw [← map_pow, ← hK, FiniteField.pow_card]
  have hψ := coeff_zero_preΨ_eq_neg_one hGonzalezMultiplicationByP hp hp5 WL hL
    (by simpa [WL, baseChange] using hfix W.a₄) (by simpa [WL, baseChange] using hfix W.a₆) hWL
    hfrob
  rw [hGonzalezDivisionPolynomial hp hp5 WL hL hWL, coeff_C_zero] at hψ
  have hDm : (-1 : K) ^ ((p - 1) / 2) * (W.a₄ ^ 3 + 27 * W.a₆ ^ 2 / 4) ^ m = -1 := by
    apply (algebraMap K L).injective
    simp only [map_mul, map_pow, map_neg, map_one, map_add, map_div₀, map_ofNat]
    simpa [WL, baseChange] using hψ
  -- `Δ = -64 D` and `(-64) ^ m = 1`.
  have h2 : (2 : K) ≠ 0 := fun h => by
    have := Nat.le_of_dvd two_pos ((CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h))
    omega
  have h4 : (4 : K) ≠ 0 := by
    have := mul_ne_zero h2 h2; norm_num at this; exact this
  have hΔ : W.Δ = -64 * (W.a₄ ^ 3 + 27 * W.a₆ ^ 2 / 4) := by
    rw [Δ_of_isShortNF]; field_simp; ring
  have h64 : (-64 : K) ^ m = 1 := by
    rw [hmk, pow_mul, show (-64 : K) ^ 2 = 2 ^ 12 by norm_num, ← pow_mul, hk, pow_mul,
      two_pow_sub_one (by omega), one_pow]
  have hodd : (p + 1) / 2 = (p - 1) / 2 + 1 := by
    have := hp.eq_one_or_self_of_dvd 2; omega
  have hsq : ((-1 : K) ^ ((p - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [hΔ, mul_pow, h64, one_mul, hodd, pow_succ]
  linear_combination (-1 : K) ^ ((p - 1) / 2) * hDm -
    (W.a₄ ^ 3 + 27 * W.a₆ ^ 2 / 4) ^ m * hsq

/-- **Theorem 1.3** (rationality of supersingular discriminants). Let `p ≥ 5` be prime, `K` a
field with `p ^ 2` elements and `W` a short Weierstrass elliptic curve over `K` which is
supersingular with `π_E = [-p]`. Then for every nonzero rational differential `ω = u⁻¹ ω₀`
(`u ∈ Kˣ`), `κ(E) = Δ(E, ω) ^ ((p ^ 2 - 1) / 12) = (-1) ^ ((p + 1) / 2)`. -/
theorem unit_pow_twelve_mul_Δ_pow_of_isDeuringModel
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Fintype.card K = p ^ 2) (W : WeierstrassCurve K) [W.IsElliptic] [W.IsShortNF]
    (hss : W.IsSupersingular) (hD : W.IsDeuringModel) (u : Kˣ) :
    ((u : K) ^ 12 * W.Δ) ^ ((p ^ 2 - 1) / 12) = (-1) ^ ((p + 1) / 2) := by
  rw [unit_pow_twelve_mul_Δ_pow hp hp5 hK, Δ_pow_of_isDeuringModel hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hp hp5 hK W hss hD]

/-- **Corollary 4.7** (first assertion, square). Under the hypotheses of Theorem 1.3, `Δ(E, ω)` is
a square in `K` for every nonzero rational differential `ω = u⁻¹ ω₀`. -/
theorem isSquare_unit_pow_twelve_mul_Δ_of_isDeuringModel
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Fintype.card K = p ^ 2) (W : WeierstrassCurve K) [W.IsElliptic] [W.IsShortNF]
    (hss : W.IsSupersingular) (hD : W.IsDeuringModel) (u : Kˣ) :
    IsSquare ((u : K) ^ 12 * W.Δ) := by
  obtain ⟨hm12, -⟩ := exists_twelve_mul hp hp5
  have hκ := unit_pow_twelve_mul_Δ_pow_of_isDeuringModel hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hp hp5 hK W hss hD u
  have hne : (u : K) ^ 12 * W.Δ ≠ 0 := mul_ne_zero (pow_ne_zero _ u.ne_zero) W.isUnit_Δ.ne_zero
  obtain ⟨b, hb⟩ := FiniteField.exists_eq_pow_of_pow_card_sub_one_div_eq_one
    (n := 2) (⟨6 * ((p ^ 2 - 1) / 12), by rw [hK]; omega⟩) hne (by
      rw [hK, show (p ^ 2 - 1) / 2 = (p ^ 2 - 1) / 12 * 6 by omega, pow_mul, hκ, ← pow_mul,
        mul_comm, pow_mul, show ((-1 : K) ^ 6) = 1 by norm_num, one_pow])
  exact ⟨b, by rw [hb, sq]⟩

/-- **Corollary 4.7** (first assertion, cube). Under the hypotheses of Theorem 1.3, `Δ(E, ω)` is
a cube in `K` for every nonzero rational differential `ω = u⁻¹ ω₀`. -/
theorem exists_unit_pow_twelve_mul_Δ_eq_pow_three_of_isDeuringModel
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Fintype.card K = p ^ 2) (W : WeierstrassCurve K) [W.IsElliptic]
    [W.IsShortNF] (hss : W.IsSupersingular) (hD : W.IsDeuringModel) (u : Kˣ) :
    ∃ c : K, (u : K) ^ 12 * W.Δ = c ^ 3 := by
  obtain ⟨hm12, -⟩ := exists_twelve_mul hp hp5
  have hκ := unit_pow_twelve_mul_Δ_pow_of_isDeuringModel hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hp hp5 hK W hss hD u
  have hne : (u : K) ^ 12 * W.Δ ≠ 0 := mul_ne_zero (pow_ne_zero _ u.ne_zero) W.isUnit_Δ.ne_zero
  exact FiniteField.exists_eq_pow_of_pow_card_sub_one_div_eq_one
    (n := 3) (⟨4 * ((p ^ 2 - 1) / 12), by rw [hK]; omega⟩) hne (by
      rw [hK, show (p ^ 2 - 1) / 3 = (p ^ 2 - 1) / 12 * 4 by omega, pow_mul, hκ, ← pow_mul,
        mul_comm, pow_mul, show ((-1 : K) ^ 4) = 1 by norm_num, one_pow])

/-- **Corollary 4.7** (`j` is a cube). If `p ≥ 5`, `#K = p ^ 2` and the short Weierstrass elliptic
curve `W` over `K` is supersingular with `π_E = [-p]`, then `j(W)` is a cube in `K`. -/
theorem exists_j_eq_pow_three_of_isDeuringModel
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Fintype.card K = p ^ 2) (W : WeierstrassCurve K) [W.IsElliptic] [W.IsShortNF]
    (hss : W.IsSupersingular) (hD : W.IsDeuringModel) :
    ∃ c : K, W.j = c ^ 3 := by
  obtain ⟨t, ht⟩ := exists_unit_pow_twelve_mul_Δ_eq_pow_three_of_isDeuringModel
    hGonzalezDivisionPolynomial hGonzalezMultiplicationByP hp hp5 hK W hss hD 1
  rw [Units.val_one, one_pow, one_mul] at ht
  have ht0 : t ≠ 0 := by
    rintro rfl; exact W.isUnit_Δ.ne_zero (by simpa using ht)
  refine ⟨W.c₄ / t, ?_⟩
  rw [j, Units.val_inv_eq_inv_val, coe_Δ', ht, div_pow, div_eq_inv_mul]

/-- **Corollary 4.7** (`j - 1728` is a square). If `p ≥ 5`, `#K = p ^ 2` and the short
Weierstrass elliptic curve `W` over `K` is supersingular with `π_E = [-p]`, then `j(W) - 1728` is
a square in `K`. -/
theorem isSquare_j_sub_1728_of_isDeuringModel
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Fintype.card K = p ^ 2) (W : WeierstrassCurve K) [W.IsElliptic] [W.IsShortNF]
    (hss : W.IsSupersingular) (hD : W.IsDeuringModel) :
    IsSquare (W.j - 1728) := by
  obtain ⟨s, hs⟩ := isSquare_unit_pow_twelve_mul_Δ_of_isDeuringModel hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hp hp5 hK W hss hD 1
  rw [Units.val_one, one_pow, one_mul] at hs
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  have hs0 : s ≠ 0 := by rintro rfl; exact hΔ (by simpa using hs)
  refine ⟨W.c₆ / s, ?_⟩
  have hrel := W.c_relation
  rw [j, Units.val_inv_eq_inv_val, coe_Δ']
  field_simp
  linear_combination (-s ^ 2) * hrel - W.c₆ ^ 2 * hs

section AlgClosed

/-! ### Supersingular `j`-invariants

Over an algebraically closed field `L` of characteristic `p ≥ 5`, the subfield `F_{p²}` of `L` is
the set of fixed points of `x ↦ x ^ (p ^ 2)`. -/

variable {L : Type u} [Field L] [IsAlgClosed L] [DecidableEq L] [CharP L p]

/-- For a supersingular short Weierstrass curve over `L` defined over `F_{p²}`, with `ψ` the
constant `p`-th division polynomial: `ψ ≠ 0`, `a₄ ^ (p ^ 2) = ψ ^ 4 a₄`, `a₆ ^ (p ^ 2) = ψ ^ 6 a₆`,
`Δ ^ ((p ^ 2 - 1) / 3) = ψ ^ 4` and `Δ ^ ((p ^ 2 - 1) / 2) = ψ ^ 6`. The coefficient identities
come from comparing the curve equation at `p • (x, y)` (given by [gonzalez2022, Lemma 3.1]) with its
`p ^ 2`-th power at `x = 0, 1`; the discriminant identities from [gonzalez2022, Theorem 3.2]. -/
private lemma supersingular_aux (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (W : WeierstrassCurve L)
    [W.IsElliptic] [W.IsShortNF] (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x)
    (ha₄' : W.a₄ ^ p ^ 2 = W.a₄) (ha₆' : W.a₆ ^ p ^ 2 = W.a₆)
    (hW : ∀ P : W.toAffine.Point, p • P = 0 → P = 0) :
    (W.preΨ p).coeff 0 ≠ 0 ∧
      W.a₄ ^ (p ^ 2) = ((W.preΨ p).coeff 0) ^ 4 * W.a₄ ∧
      W.a₆ ^ (p ^ 2) = ((W.preΨ p).coeff 0) ^ 6 * W.a₆ ∧
      W.Δ ^ ((p ^ 2 - 1) / 3) = ((W.preΨ p).coeff 0) ^ 4 ∧
      W.Δ ^ ((p ^ 2 - 1) / 2) = ((W.preΨ p).coeff 0) ^ 6 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hm12, k, hmk, hk⟩ := exists_twelve_mul hp hp5
  set m := (p ^ 2 - 1) / 12
  have hψeq := congrArg (coeff · 0) (hGonzalezDivisionPolynomial hp hp5 W hL hW)
  simp only [coeff_C_zero] at hψeq
  set ψ := (W.preΨ p).coeff 0
  set D := W.a₄ ^ 3 + 27 * W.a₆ ^ 2 / 4
  have h2 : (2 : L) ≠ 0 := fun h => by
    have := Nat.le_of_dvd two_pos ((CharP.cast_eq_zero_iff L p 2).mp (by exact_mod_cast h))
    omega
  have h4 : (4 : L) ≠ 0 := by
    have := mul_ne_zero h2 h2; norm_num at this; exact this
  have hΔ : W.Δ = -64 * D := by
    simp only [D]; rw [Δ_of_isShortNF]; field_simp; ring
  have hD0 : D ≠ 0 := fun h => W.isUnit_Δ.ne_zero (by rw [hΔ, h, mul_zero])
  have hψ0 : ψ ≠ 0 := by
    rw [hψeq]; exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ hD0)
  have h64 : (-64 : L) ^ m = 1 := by
    rw [hmk, pow_mul, show (-64 : L) ^ 2 = 2 ^ 12 by norm_num, ← pow_mul, hk, pow_mul,
      two_pow_sub_one (by omega), one_pow]
  have hsgn : ∀ n, ((-1 : L) ^ ((p - 1) / 2)) ^ (2 * n) = 1 := fun n => by
    rw [← pow_mul, mul_comm, pow_mul, pow_mul, neg_one_sq, one_pow, one_pow]
  -- Comparison of the curve equations.
  have key : ∀ x : L, ψ⁻¹ ^ 6 * (W.a₄ ^ (p ^ 2) * x ^ (p ^ 2) + W.a₆ ^ (p ^ 2)) =
      W.a₄ * ψ⁻¹ ^ 2 * x ^ (p ^ 2) + W.a₆ := by
    intro x
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ 3 + W.a₄ * x + W.a₆) two_pos
    have h : W.toAffine.Nonsingular x y := by
      rw [← Affine.equation_iff_nonsingular, Affine.equation_iff]
      simp [hy]
    obtain ⟨h', -⟩ := hGonzalezMultiplicationByP hp hp5 W hL ha₄' ha₆' hW h
    have he := h'.1
    rw [Affine.equation_iff, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF] at he
    have hyq := congrArg (iterateFrobenius L p 2) hy
    simp only [map_pow, map_add, map_mul, iterateFrobenius_def] at hyq
    linear_combination he - ψ⁻¹ ^ 6 * hyq
  have k0 := key 0
  have k1 := key 1
  rw [zero_pow (by positivity), mul_zero, zero_add, mul_zero, zero_add] at k0
  rw [one_pow, mul_one, mul_one] at k1
  have hψi : ψ⁻¹ ≠ 0 := inv_ne_zero hψ0
  have ha₆ : W.a₆ ^ (p ^ 2) = ψ ^ 6 * W.a₆ :=
    calc W.a₆ ^ (p ^ 2) = ψ ^ 6 * (ψ⁻¹ ^ 6 * W.a₆ ^ (p ^ 2)) := by field_simp
      _ = ψ ^ 6 * W.a₆ := by rw [k0]
  have ha₄ : W.a₄ ^ (p ^ 2) = ψ ^ 4 * W.a₄ := by
    have h : ψ⁻¹ ^ 6 * W.a₄ ^ (p ^ 2) = W.a₄ * ψ⁻¹ ^ 2 := by linear_combination k1 - k0
    calc W.a₄ ^ (p ^ 2) = ψ ^ 6 * (ψ⁻¹ ^ 6 * W.a₄ ^ (p ^ 2)) := by field_simp
      _ = ψ ^ 6 * (W.a₄ * ψ⁻¹ ^ 2) := by rw [h]
      _ = ψ ^ 4 * W.a₄ := by field_simp
  refine ⟨hψ0, ha₄, ha₆, ?_, ?_⟩
  · rw [show (p ^ 2 - 1) / 3 = m * 4 by omega, hΔ, mul_pow, pow_mul, h64, one_pow, one_mul,
      hψeq, mul_pow, show 4 = 2 * 2 by rfl, hsgn, one_mul, ← pow_mul]
  · rw [show (p ^ 2 - 1) / 2 = m * 6 by omega, hΔ, mul_pow, pow_mul, h64, one_pow, one_mul,
      hψeq, mul_pow, show 6 = 2 * 3 by rfl, hsgn, one_mul, ← pow_mul]

/-- For a supersingular short Weierstrass curve over `L` defined over `F_{p²}`, `j = c ^ 3` with
`c ∈ F_{p²}`; from [gonzalez2022, Theorem 3.2 and Lemma 3.1]. -/
private lemma exists_j_eq_pow_three_aux
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (W : WeierstrassCurve L) [W.IsElliptic] [W.IsShortNF]
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (ha₄' : W.a₄ ^ p ^ 2 = W.a₄)
    (ha₆' : W.a₆ ^ p ^ 2 = W.a₆) (hW : ∀ P : W.toAffine.Point, p • P = 0 → P = 0) :
    ∃ c : L, c ^ (p ^ 2) = c ∧ W.j = c ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hm12, -⟩ := exists_twelve_mul hp hp5
  obtain ⟨hψ0, ha₄, -, hΔ3, -⟩ := supersingular_aux hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hp hp5 W hL ha₄' ha₆' hW
  set ψ := (W.preΨ p).coeff 0
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq W.Δ (n := 3) (by norm_num)
  have ht0 : t ≠ 0 := by rintro rfl; exact W.isUnit_Δ.ne_zero (by simpa using ht.symm)
  have htq : t ^ (p ^ 2) = ψ ^ 4 * t := by
    rw [← hΔ3, ← ht, ← pow_mul, show 3 * ((p ^ 2 - 1) / 3) = p ^ 2 - 1 by omega, ← pow_succ,
      Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)]
  refine ⟨W.c₄ / t, ?_, ?_⟩
  · have h48 : (-48 : L) ^ (p ^ 2) = -48 := by
      rw [← iterateFrobenius_def (R := L) (p := p) (n := 2), map_neg, map_ofNat]
    rw [div_pow, c₄_of_isShortNF, mul_pow, ha₄, htq, h48]
    field_simp
  · rw [j, Units.val_inv_eq_inv_val, coe_Δ', ← ht, div_pow, div_eq_inv_mul]

/-- For a supersingular short Weierstrass curve over `L` defined over `F_{p²}`, `j - 1728 = s ^ 2`
with `s ∈ F_{p²}`; from [gonzalez2022, Theorem 3.2 and Lemma 3.1]. -/
private lemma exists_j_sub_1728_eq_sq_aux
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (W : WeierstrassCurve L) [W.IsElliptic] [W.IsShortNF]
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (ha₄' : W.a₄ ^ p ^ 2 = W.a₄)
    (ha₆' : W.a₆ ^ p ^ 2 = W.a₆) (hW : ∀ P : W.toAffine.Point, p • P = 0 → P = 0) :
    ∃ s : L, s ^ (p ^ 2) = s ∧ W.j - 1728 = s ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hm12, -⟩ := exists_twelve_mul hp hp5
  obtain ⟨hψ0, -, ha₆, -, hΔ2⟩ := supersingular_aux hGonzalezDivisionPolynomial
    hGonzalezMultiplicationByP hp hp5 W hL ha₄' ha₆' hW
  set ψ := (W.preΨ p).coeff 0
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq W.Δ (n := 2) (by norm_num)
  have hr0 : r ≠ 0 := by rintro rfl; exact W.isUnit_Δ.ne_zero (by simpa using hr.symm)
  have hrq : r ^ (p ^ 2) = ψ ^ 6 * r := by
    rw [← hΔ2, ← hr, ← pow_mul, show 2 * ((p ^ 2 - 1) / 2) = p ^ 2 - 1 by omega, ← pow_succ,
      Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)]
  refine ⟨W.c₆ / r, ?_, ?_⟩
  · have h864 : (-864 : L) ^ (p ^ 2) = -864 := by
      rw [← iterateFrobenius_def (R := L) (p := p) (n := 2), map_neg, map_ofNat]
    rw [div_pow, c₆_of_isShortNF, mul_pow, ha₆, hrq, h864]
    field_simp
  · have hrel := W.c_relation
    have hΔ0 : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
    rw [j, Units.val_inv_eq_inv_val, coe_Δ']
    field_simp
    linear_combination (-r ^ 2) * hrel + W.c₆ ^ 2 * hr

omit [DecidableEq L] in
/-- Every short Weierstrass elliptic curve over `L` with `j ∈ F_{p²}` has a model
`W.scaling u : y² = x³ + u⁴ a₄ x + u⁶ a₆`, isomorphic to it over `L`, with coefficients in
`F_{p²}`. (This is the reduction step after [gonzalez2022, Theorem 3.2]: if `a₄ a₆ ≠ 0` take
`u² = a₄ / a₆`, so that both new coefficients equal `a₄ ^ 3 / a₆ ^ 2`, which is a rational function
of `j`.) -/
private lemma exists_scaling_pow_eq (hp : p.Prime) (hp5 : 5 ≤ p) (W : WeierstrassCurve L)
    [W.IsElliptic] [W.IsShortNF] (hj : W.j ^ (p ^ 2) = W.j) :
    ∃ u : Lˣ, (W.scaling u).a₄ ^ p ^ 2 = (W.scaling u).a₄ ∧
      (W.scaling u).a₆ ^ p ^ 2 = (W.scaling u).a₆ := by
  have hp0 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  have hΔs : W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := by rw [Δ_of_isShortNF]
  have hcast : ∀ n : ℕ, (n : L) = 0 → p ∣ n := fun n h => (CharP.cast_eq_zero_iff L p n).mp h
  have hsmall : ∀ n : ℕ, 0 < n → n < p → (n : L) ≠ 0 := fun n hn hnp h =>
    absurd (Nat.le_of_dvd hn (hcast n h)) (by omega)
  by_cases h4 : W.a₄ = 0
  · have h6 : W.a₆ ≠ 0 := by rintro h6; exact hΔ (by simp [h4, h6])
    obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq W.a₆⁻¹ (n := 6) (by norm_num)
    have hv0 : v ≠ 0 := by rintro rfl; exact inv_ne_zero h6 (by simpa using hv.symm)
    refine ⟨Units.mk0 v hv0, ?_, ?_⟩
    · simp [h4, zero_pow hp0]
    · simp [hv, inv_mul_cancel₀ h6]
  by_cases h6 : W.a₆ = 0
  · obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq W.a₄⁻¹ (n := 4) (by norm_num)
    have hv0 : v ≠ 0 := by rintro rfl; exact inv_ne_zero h4 (by simpa using hv.symm)
    refine ⟨Units.mk0 v hv0, ?_, ?_⟩
    · simp [hv, inv_mul_cancel₀ h4]
    · simp [h6, zero_pow hp0]
  -- Generic case: `c = a₄ ^ 3 / a₆ ^ 2` satisfies `j (4 c + 27) = 6912 c`, hence `c ∈ F_{p²}`.
  set c := W.a₄ ^ 3 / W.a₆ ^ 2 with hc
  have h2 : (2 : L) ≠ 0 := by exact_mod_cast hsmall 2 (by norm_num) (by omega)
  have h16 : (16 : L) ≠ 0 := by
    have := pow_ne_zero 4 h2; norm_num at this; exact this
  have hjc : W.j * (4 * c + 27) = 6912 * c := by
    have hjΔ : W.j * W.Δ = W.c₄ ^ 3 := by
      rw [j, Units.val_inv_eq_inv_val, coe_Δ', mul_comm W.Δ⁻¹, mul_assoc, inv_mul_cancel₀ hΔ,
        mul_one]
    rw [c₄_of_isShortNF, hΔs] at hjΔ
    rw [hc]
    field_simp
    refine mul_left_cancel₀ h16 ?_
    linear_combination (-1 : L) * hjΔ
  have : Fact p.Prime := ⟨hp⟩
  have hjc' := congrArg (iterateFrobenius L p 2) hjc
  simp only [map_mul, map_add, map_ofNat, iterateFrobenius_def, hj] at hjc'
  have hc' : c ^ p ^ 2 = c := by
    have h1728 : 4 * W.j - 6912 ≠ 0 := by
      intro h
      have : ((186624 : ℕ) : L) = 0 := by
        push_cast; linear_combination 4 * hjc - (4 * c + 27) * h
      have hdvd := hcast _ this
      have : p ∣ 2 ^ 8 * 3 ^ 6 := by norm_num; exact hdvd
      rcases (Nat.Prime.dvd_mul hp).mp this with h2 | h3
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega
    have : (4 * W.j - 6912) * (c ^ p ^ 2 - c) = 0 := by linear_combination hjc' - hjc
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h1728)
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (W.a₄ / W.a₆) (n := 2) (by norm_num)
  have hv0 : v ≠ 0 := by
    rintro rfl; exact div_ne_zero h4 h6 (by simpa using hv.symm)
  have e4 : v ^ 4 * W.a₄ = c := by
    rw [hc, show v ^ 4 = (v ^ 2) ^ 2 by ring, hv]; field_simp
  have e6 : v ^ 6 * W.a₆ = c := by
    rw [hc, show v ^ 6 = (v ^ 2) ^ 3 by ring, hv]; field_simp
  refine ⟨Units.mk0 v hv0, ?_, ?_⟩
  · simp only [scaling_a₄, Units.val_mk0, e4, hc']
  · simp only [scaling_a₆, Units.val_mk0, e6, hc']

/-- **Corollary 4.7** (`j` is a cube in `F_{p²}`; Morton's theorem). Let `p ≥ 5` and let `W` be a
supersingular short Weierstrass elliptic curve over an algebraic closure `L` of `𝔽_p`
(hypothesis `hL`). Then `j(W) = c ^ 3` for some `c ∈ F_{p²}`, i.e. with `c ^ (p ^ 2) = c`.

This is derived from [silverman-aec, Theorem V.3.1(a)] (`j ∈ F_{p²}`, so that `W` has an
`L`-isomorphic model over `F_{p²}`) and [gonzalez2022, Theorem 3.2 and Lemma 3.1] applied to that
model, rather than via the Deuring models of Lemma 4.3. -/
theorem exists_j_eq_pow_three_of_supersingular
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : SupersingularJInvariant.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (W : WeierstrassCurve L) [W.IsElliptic] [W.IsShortNF]
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (hW : ∀ P : W.toAffine.Point, p • P = 0 → P = 0) :
    ∃ c : L, c ^ (p ^ 2) = c ∧ W.j = c ^ 3 := by
  obtain ⟨u, h4, h6⟩ := exists_scaling_pow_eq hp hp5 W (hSupersingularJInvariant hp W hW)
  rw [← scaling_j W u]
  exact exists_j_eq_pow_three_aux hGonzalezDivisionPolynomial hGonzalezMultiplicationByP hp hp5
    (W.scaling u) hL h4 h6 (Point.eq_zero_of_nsmul_eq_zero_scaling W u hW)

/-- **Corollary 4.7** (`j - 1728` is a square in `F_{p²}`). Let `p ≥ 5` and let `W` be a
supersingular short Weierstrass elliptic curve over an algebraic closure `L` of `𝔽_p`
(hypothesis `hL`). Then `j(W) - 1728 = s ^ 2` for some `s ∈ F_{p²}`, i.e. with `s ^ (p ^ 2) = s`.

This is derived from [silverman-aec, Theorem V.3.1(a)] (`j ∈ F_{p²}`, so that `W` has an
`L`-isomorphic model over `F_{p²}`) and [gonzalez2022, Theorem 3.2 and Lemma 3.1] applied to that
model, rather than via the Deuring models of Lemma 4.3. -/
theorem exists_j_sub_1728_eq_sq_of_supersingular
    (hGonzalezDivisionPolynomial : GonzalezDivisionPolynomial.{u})
    (hGonzalezMultiplicationByP : GonzalezMultiplicationByP.{u})
    (hSupersingularJInvariant : SupersingularJInvariant.{u}) (hp : p.Prime) (hp5 : 5 ≤ p)
    (W : WeierstrassCurve L) [W.IsElliptic] [W.IsShortNF]
    (hL : ∀ x : L, ∃ k, 0 < k ∧ x ^ p ^ k = x) (hW : ∀ P : W.toAffine.Point, p • P = 0 → P = 0) :
    ∃ s : L, s ^ (p ^ 2) = s ∧ W.j - 1728 = s ^ 2 := by
  obtain ⟨u, h4, h6⟩ := exists_scaling_pow_eq hp hp5 W (hSupersingularJInvariant hp W hW)
  rw [← scaling_j W u]
  exact exists_j_sub_1728_eq_sq_aux hGonzalezDivisionPolynomial hGonzalezMultiplicationByP hp hp5
    (W.scaling u) hL h4 h6 (Point.eq_zero_of_nsmul_eq_zero_scaling W u hW)

end AlgClosed

end WeierstrassCurve
