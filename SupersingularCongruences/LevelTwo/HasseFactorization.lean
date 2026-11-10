/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.LevelTwo.LarsonRing
public import SupersingularCongruences.EllipticCurve.HasseInvariant
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Data.Nat.Prime.Factorial
public import SupersingularCongruences.External

/-!
# Proposition 3.4: the algebraic core of the factorization of `A_p` at level two

In the manuscript's proof of Proposition 3.4, `A_p ∈ 𝔽_p[δ, ε]` (eq. (3.1)) is a weighted
homogeneous polynomial of weight `p - 1` (`δ` of weight `2`, `ε` of weight `4`), and on the Legendre
family `E_λ` the forms `δ, ε` take the values `h(λ) = c (λ + 1)`, `e(λ) = ζ λ` with `4c² = ζ`
(so that `x = μ / ε = (λ - 1)² / (4λ)`), while `A_p(E_λ) = ± H_p(λ)` (Lemma 2.1(c),(d)).
This file proves the purely algebraic statement that these data force the factorization
`A_p = c' δ^{α_p} ∏_{i=1}^s (μ - ξ_i ε)` with distinct `ξ_i ∉ {0, -1}` and identify the `ξ_i` as
the values of `x` at the roots of `H_p`.

## Main results

* `LevelTwo.eq_C_mul_prod_of_isWeightedHomogeneous`: over an algebraically closed field, a weighted
  homogeneous `P` of weight `2 (2m + α)` factors as `b δ^α ε^{m-d} ∏_r (δ² - r ε)` (first paragraph
  of the manuscript's proof: factoring a binary form in `(δ², ε)` into linear forms).
* `LevelTwo.exists_hasse_factorization_core`: the algebraic core of Proposition 3.4.

## Proof route

The manuscript compares orders of `A_p^{12} / Δ^{p-1}` and `H_p^{12} / (16 λ² (λ - 1)²)^{p-1}` at
points of `X₀(2)` and `X(2)`. Here the same comparison is carried out as a polynomial identity in
`λ`: substituting the factorization into `P(c (λ + 1), ζ λ) = κ H_p(λ)` gives
`κ H_p = K (λ + 1)^α λ^{m - d} ∏_r ((λ + 1)² - 4 r λ)`. Then `H_p(0) = 1` forces `d = m` (no factor
`ε`), `H_p(1) ≠ 0` excludes `r = 1` (`ξ = 0`), and squarefreeness of `H_p` (separability,
`Polynomial.DeuringPolynomialSeparable`) excludes `r = 0` (`ξ = -1`, factor `(λ + 1)²`) and
repeated `r` (a repeated quadratic factor has a double root). Here `r = 1 + ξ`.
-/

public section

open Polynomial

universe u

namespace LevelTwo

/-- `α_p = 1` if `p ≡ 3 (mod 4)` and `α_p = 0` otherwise (manuscript, Proposition 3.4). -/
def hasseAlpha (p : ℕ) : ℕ := if p % 4 = 3 then 1 else 0

/-- `s = (p - 1 - 2 α_p) / 4` (manuscript, Proposition 3.4). -/
def hasseS (p : ℕ) : ℕ := (p - 1 - 2 * hasseAlpha p) / 4

lemma hasseAlpha_def (p : ℕ) : hasseAlpha p = if p % 4 = 3 then 1 else 0 := (rfl)

lemma hasseS_def (p : ℕ) : hasseS p = (p - 1 - 2 * hasseAlpha p) / 4 := (rfl)

lemma hasseAlpha_le_one (p : ℕ) : hasseAlpha p ≤ 1 := by
  rw [hasseAlpha_def]; split_ifs <;> omega

/-- For odd `p`, `(p - 1) / 2 = 2 s + α_p`. -/
lemma half_eq_two_mul_hasseS_add (p : ℕ) (hp : Odd p) :
    (p - 1) / 2 = 2 * hasseS p + hasseAlpha p := by
  obtain ⟨k, rfl⟩ := hp
  rw [hasseS_def, hasseAlpha_def]
  split_ifs <;> omega

/-- `s ≥ 1` for `p ≥ 5` odd. -/
lemma one_le_hasseS (p : ℕ) (hp : Odd p) (hp5 : 5 ≤ p) : 1 ≤ hasseS p := by
  obtain ⟨k, rfl⟩ := hp
  rw [hasseS_def, hasseAlpha_def]
  split_ifs <;> omega

end LevelTwo

namespace LevelTwo

section Core

variable {L : Type*} [Field L]

lemma delta_eq_X [Infinite L] : delta L = MvPolynomial.X 0 :=
  MvPolynomial.funext fun x => by simp

lemma eps_eq_X [Infinite L] : eps L = MvPolynomial.X 1 :=
  MvPolynomial.funext fun x => by simp

lemma aeval_delta [Infinite L] {A : Type*} [CommRing A] [Algebra L A] (f : Fin 2 → A) :
    MvPolynomial.aeval f (delta L) = f 0 := by
  rw [delta_eq_X, MvPolynomial.aeval_X]

lemma aeval_eps [Infinite L] {A : Type*} [CommRing A] [Algebra L A] (f : Fin 2 → A) :
    MvPolynomial.aeval f (eps L) = f 1 := by
  rw [eps_eq_X, MvPolynomial.aeval_X]

/-- The weight of an exponent vector for the weights `(2, 4)` of `(δ, ε)`. -/
lemma weight_two_four_apply (d : Fin 2 →₀ ℕ) :
    Finsupp.weight ![2, 4] d = 2 * d 0 + 4 * d 1 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two]
  ring

/-- The dehomogenization `G(y) = ∑_d a_d y^{m - d₁}` of `P = ∑_d a_d δ^{d₀} ε^{d₁}`: if `P` has
weight `2 (2m + α)`, then `P = δ^α ε^m G(δ² / ε)`. -/
noncomputable def dehom (P : MvPolynomial (Fin 2) L) (m : ℕ) : L[X] :=
  ∑ d ∈ P.support, C (P.coeff d) * X ^ (m - d 1)

lemma natDegree_dehom_le (P : MvPolynomial (Fin 2) L) (m : ℕ) : (dehom P m).natDegree ≤ m := by
  refine natDegree_sum_le_of_forall_le _ _ fun d _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]
  omega

/-- `P(a, b) = a^α b^m G(a² / b)` for `b ≠ 0`. -/
lemma eval_eq_dehom {P : MvPolynomial (Fin 2) L} {m α : ℕ} (hα : α ≤ 1)
    (hP : P.IsWeightedHomogeneous ![2, 4] (2 * (2 * m + α))) {a b : L} (hb : b ≠ 0) :
    MvPolynomial.eval ![a, b] P = a ^ α * b ^ m * (dehom P m).eval (a ^ 2 / b) := by
  rw [MvPolynomial.eval_eq', dehom, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw := hP (MvPolynomial.mem_support_iff.mp hd)
  rw [weight_two_four_apply] at hw
  have h1 : d 1 ≤ m := by omega
  have h0 : d 0 = α + 2 * (m - d 1) := by omega
  have hbm : b ^ m = b ^ (m - d 1) * b ^ d 1 := by rw [← pow_add]; congr 1; omega
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    eval_mul, eval_C, eval_pow, eval_X, h0, hbm, div_pow, pow_add, pow_mul]
  field_simp

/-- Over an algebraically closed field, every `P` of weight `2 (2m + α)` (`α ≤ 1`) factors as
`P = b δ^α ε^{m - d} ∏_{r} (δ² - r ε)`, where `G = dehom P m` has leading coefficient `b`, degree
`d ≤ m` and roots `r` (manuscript, proof of Proposition 3.4, first paragraph). -/
lemma eq_C_mul_prod_of_isWeightedHomogeneous [IsAlgClosed L] {P : MvPolynomial (Fin 2) L}
    {m α : ℕ} (hα : α ≤ 1) (hP : P.IsWeightedHomogeneous ![2, 4] (2 * (2 * m + α))) :
    P = MvPolynomial.C (dehom P m).leadingCoeff * delta L ^ α *
      eps L ^ (m - (dehom P m).natDegree) *
      ((dehom P m).roots.map (fun r => delta L ^ 2 - MvPolynomial.C r * eps L)).prod := by
  set G := dehom P m with hG
  have hd : G.natDegree ≤ m := natDegree_dehom_le P m
  have hroots : G.roots.card = G.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hGfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  have hne : delta L * eps L ≠ 0 := mul_ne_zero delta_ne_zero eps_ne_zero
  refine mul_right_cancel₀ hne (MvPolynomial.funext fun x => ?_)
  simp only [map_mul, eval_delta, eval_eps]
  by_cases hx0 : x 0 = 0
  · simp [hx0]
  by_cases hx1 : x 1 = 0
  · simp [hx1]
  congr 1
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  have heval : G.eval (x 0 ^ 2 / x 1) =
      G.leadingCoeff * (G.roots.map fun r => x 0 ^ 2 / x 1 - r).prod := by
    conv_lhs => rw [← hGfac]
    simp [eval_multiset_prod, Multiset.map_map]
  rw [hx, eval_eq_dehom hα hP hx1, ← hG, heval]
  simp only [map_pow, map_multiset_prod, Multiset.map_map, Function.comp_def, map_sub, map_mul,
    MvPolynomial.eval_C, eval_delta, eval_eps, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  have hprod : (G.roots.map fun r => x 0 ^ 2 - r * x 1).prod =
      x 1 ^ G.natDegree * (G.roots.map fun r => x 0 ^ 2 / x 1 - r).prod := by
    have : (G.roots.map fun r => x 0 ^ 2 - r * x 1) =
        G.roots.map (fun r => x 1 * (x 0 ^ 2 / x 1 - r)) :=
      Multiset.map_congr rfl fun r _ => by field_simp
    rw [this, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hroots]
  rw [hprod, ← pow_sub_mul_pow (x 1) hd]
  ring

/-- On the Legendre family, `δ ↦ c (λ + 1)`, `ε ↦ ζ λ` with `4 c² = ζ` sends `δ² - r ε` to
`c² ((λ + 1)² - 4 r λ)`. -/
lemma aeval_delta_sq_sub_mul_eps [Infinite L] {c ζ : L} (hcζ : 4 * c ^ 2 = ζ) (r : L) :
    MvPolynomial.aeval ![C c * (X + 1), C ζ * X] (delta L ^ 2 - MvPolynomial.C r * eps L) =
      C (c ^ 2) * (X ^ 2 + C (2 - 4 * r) * X + 1) := by
  rw [map_sub, map_mul, map_pow, aeval_delta, aeval_eps, MvPolynomial.aeval_C, ← hcζ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, algebraMap_eq,
    map_mul, map_pow, map_sub, map_ofNat]
  ring

end Core

section Main

variable {L : Type u} [Field L] [IsAlgClosed L]

/-- **Proposition 3.4, algebraic core.** Let `p ≥ 5` be prime, `L` algebraically closed of
characteristic `p`, and let `P ∈ L[δ, ε]` be weighted homogeneous of weight `p - 1` (weights
`2, 4`). Suppose that on the Legendre family, where `δ ↦ c (λ + 1)` and `ε ↦ ζ λ` with
`4 c² = ζ` (so `μ = δ² - ε ↦ ζ (λ - 1)² / 4` and `x = μ / ε ↦ (λ - 1)² / (4λ)`), `P` becomes
`κ H_p(λ)` with `κ ≠ 0`. (The relation `4 c² = ζ` is the normalization `h² = e (x + 1)` of the
values `h = δ(E_λ)`, `e = ε(E_λ)`; nonvanishing of `c` and `ζ` follows from the hypotheses.)
Then `P = c' δ^{α_p} ∏_{i < s} (μ - ξ_i ε)` with `c' ≠ 0` and distinct `ξ_i ∉ {0, -1}`; the values
`x(λ₀)` at the roots `λ₀` of `H_p` are exactly the `ξ_i`, together with `-1` when `α_p = 1`; and
`s ≥ 1`. -/
theorem exists_hasse_factorization_core
    (hDeuringPolynomialSeparable : DeuringPolynomialSeparable.{u})
    {p : ℕ} [CharP L p] (hp : p.Prime) (hp5 : 5 ≤ p)
    {P : MvPolynomial (Fin 2) L} (hP : P.IsWeightedHomogeneous ![2, 4] (p - 1))
    {c ζ κ : L} (hκ : κ ≠ 0) (hcζ : 4 * c ^ 2 = ζ)
    (hPH : MvPolynomial.aeval ![C c * (X + 1), C ζ * X] P = C κ * deuringPolynomial L p) :
    ∃ (c' : L) (ξ : Fin (hasseS p) → L), c' ≠ 0 ∧ Function.Injective ξ ∧
      (∀ i, ξ i ≠ 0 ∧ ξ i ≠ -1) ∧
      P = MvPolynomial.C c' * delta L ^ hasseAlpha p *
        ∏ i, (mu L - MvPolynomial.C (ξ i) * eps L) ∧
      (∀ ρ : L, (∃ l₀, (deuringPolynomial L p).eval l₀ = 0 ∧ (l₀ - 1) ^ 2 / (4 * l₀) = ρ) ↔
        (ρ ∈ Set.range ξ ∨ (hasseAlpha p = 1 ∧ ρ = -1))) ∧ 1 ≤ hasseS p := by
  classical
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h4 : (4 : L) ≠ 0 := by
    have : ((4 : ℕ) : L) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff L p]
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega
    exact_mod_cast this
  set α := hasseAlpha p with hαdef
  set m := hasseS p with hmdef
  have hα1 : α ≤ 1 := hasseAlpha_le_one p
  have hn : (p - 1) / 2 = 2 * m + α := half_eq_two_mul_hasseS_add p hodd
  have hw : p - 1 = 2 * (2 * m + α) := by rw [← hn]; obtain ⟨k, rfl⟩ := hodd; omega
  rw [hw] at hP
  set G := dehom P m with hG
  set d := G.natDegree with hddef
  have hd : d ≤ m := natDegree_dehom_le P m
  have hroots : G.roots.card = d := IsAlgClosed.card_roots_eq_natDegree
  have hfac := eq_C_mul_prod_of_isWeightedHomogeneous hα1 hP
  rw [← hG, ← hddef] at hfac
  set H := deuringPolynomial L p with hH
  have hH0 : H.eval 0 = 1 := deuringPolynomial_eval_zero p
  have hH1 : H.eval 1 ≠ 0 := deuringPolynomial_eval_one_ne_zero hp (by omega)
  have hsqf : Squarefree H := (hDeuringPolynomialSeparable hp (by omega)).squarefree
  set q : L → L[X] := fun r => X ^ 2 + C (2 - 4 * r) * X + 1 with hq
  set K : L := G.leadingCoeff * c ^ α * ζ ^ (m - d) * (c ^ 2) ^ d with hK
  -- the factorization evaluated on the Legendre family
  have hid : C κ * H = C K * (X + 1) ^ α * X ^ (m - d) * (G.roots.map q).prod := by
    rw [← hPH]
    conv_lhs => rw [hfac]
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, MvPolynomial.aeval_C, aeval_delta, aeval_eps,
      map_multiset_prod, Multiset.map_map]
    have : (G.roots.map ((MvPolynomial.aeval ![C c * (X + 1), C ζ * X]) ∘
        fun r => delta L ^ 2 - MvPolynomial.C r * eps L)) =
        G.roots.map (fun r => C (c ^ 2) * q r) :=
      Multiset.map_congr rfl fun r _ => aeval_delta_sq_sub_mul_eps hcζ r
    rw [this, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hroots]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, algebraMap_eq,
      hK, map_mul, map_pow, mul_pow]
    ring
  have hevalid : ∀ t : L, κ * H.eval t = K * (t + 1) ^ α * t ^ (m - d) *
      (G.roots.map fun r => (q r).eval t).prod := by
    intro t
    have := congrArg (eval t) hid
    simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one, eval_multiset_prod,
      Multiset.map_map, Function.comp_def] at this
    exact this
  have hK0 : K ≠ 0 := by
    intro h0
    have := hevalid 0
    rw [hH0, h0] at this
    simp only [mul_one, zero_mul] at this
    exact hκ this
  have hmd : m - d = 0 := by
    by_contra h
    have := hevalid 0
    rw [hH0, zero_pow h] at this
    simp only [mul_one, mul_zero, zero_mul] at this
    exact hκ this
  have hdm : d = m := by omega
  have hdvdH : ∀ f : L[X], f ∣ (G.roots.map q).prod → f ∣ H := by
    intro f hf
    have h1 : f ∣ C κ * H := by rw [hid]; exact Dvd.dvd.mul_left hf _
    exact (isUnit_C.mpr hκ.isUnit).dvd_mul_left.mp h1
  have hnotsq : ∀ t : L, ¬ ((X - C t) * (X - C t) ∣ H) :=
    fun t h => not_isUnit_X_sub_C t (hsqf _ h)
  have hqdeg : ∀ r, (q r).degree ≠ 0 := by
    intro r
    have : (q r).degree = 2 := by simp only [hq]; compute_degree!
    rw [this]
    exact two_ne_zero
  have hqroot : ∀ r, ∃ t, (q r).IsRoot t := fun r => IsAlgClosed.exists_root _ (hqdeg r)
  have hqmem : ∀ r ∈ G.roots, q r ∣ (G.roots.map q).prod :=
    fun r hr => Multiset.dvd_prod (Multiset.mem_map_of_mem q hr)
  have hqH : ∀ r ∈ G.roots, ∀ t, (q r).IsRoot t → H.IsRoot t :=
    fun r hr t ht => ht.dvd (hdvdH _ (hqmem r hr))
  have hqeval : ∀ r t, (q r).eval t = t ^ 2 + (2 - 4 * r) * t + 1 := by
    intro r t
    simp only [hq, eval_add, eval_pow, eval_X, eval_mul, eval_C, eval_one]
  have hq0t : ∀ r t, (q r).IsRoot t → t ≠ 0 := by
    intro r t ht h0
    rw [IsRoot, hqeval, h0] at ht
    simp at ht
  have hnd : G.roots.Nodup := by
    rw [Multiset.nodup_iff_ne_cons_cons]
    intro r t ht
    obtain ⟨u, hu⟩ := hqroot r
    have h1 : q r * q r ∣ (G.roots.map q).prod := by
      rw [ht, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons,
        ← mul_assoc]
      exact Dvd.intro _ rfl
    have h2 : (X - C u) * (X - C u) ∣ q r * q r :=
      mul_dvd_mul (dvd_iff_isRoot.mpr hu) (dvd_iff_isRoot.mpr hu)
    exact hnotsq u (hdvdH _ (h2.trans h1))
  have hr0 : ∀ r ∈ G.roots, r ≠ 0 := by
    intro r hr h0
    have : q r = (X - C (-1)) * (X - C (-1)) := by
      rw [h0]
      simp only [hq, map_neg, map_one, mul_zero, sub_zero]
      rw [show (C 2 : L[X]) = 2 from map_ofNat C 2]
      ring
    exact hnotsq (-1) (hdvdH _ (this ▸ hqmem r hr))
  have hr1 : ∀ r ∈ G.roots, r ≠ 1 := by
    intro r hr h1
    have : (q r).IsRoot 1 := by
      rw [IsRoot, hqeval, h1]
      norm_num
    exact hH1 (hqH r hr 1 this)
  -- enumerate the roots
  set T := G.roots.toFinset with hT
  have hTcard : T.card = m := by rw [hT, Multiset.toFinset_card_of_nodup hnd, hroots, hdm]
  let E : Fin m ≃ T := (finCongr hTcard.symm).trans T.equivFin.symm
  let ξ : Fin m → L := fun i => (E i : L) - 1
  have hrange : ∀ ρ, ρ ∈ Set.range ξ ↔ ∃ r ∈ G.roots, ρ = r - 1 := by
    intro ρ
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨E i, Multiset.mem_toFinset.mp (E i).2, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨E.symm ⟨r, Multiset.mem_toFinset.mpr hr⟩, by simp [ξ]⟩
  refine ⟨G.leadingCoeff, ξ, ?_, ?_, ?_, ?_, ?_, one_le_hasseS p hodd hp5⟩
  · intro h
    apply hK0
    rw [hK, h]
    ring
  · intro i j hij
    exact E.injective (Subtype.val_injective (sub_left_injective hij))
  · intro i
    have hmem := Multiset.mem_toFinset.mp (E i).2
    exact ⟨fun h => hr1 _ hmem (by linear_combination h),
      fun h => hr0 _ hmem (by linear_combination h)⟩
  · rw [hfac, hmd, pow_zero, mul_one]
    congr 1
    have hterm : ∀ i, mu L - MvPolynomial.C (ξ i) * eps L =
        delta L ^ 2 - MvPolynomial.C (E i : L) * eps L := by
      intro i
      simp only [ξ, mu_def, map_sub, map_one]
      ring
    rw [Finset.prod_congr rfl fun i _ => hterm i,
      E.prod_comp (fun x : T => delta L ^ 2 - MvPolynomial.C (x : L) * eps L),
      Finset.prod_coe_sort T (fun r => delta L ^ 2 - MvPolynomial.C r * eps L),
      Finset.prod_eq_multiset_prod, hT, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
  · intro ρ
    rw [hrange]
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [hH0] at ht
        exact one_ne_zero ht
      have := hevalid t
      rw [ht, mul_zero, hmd, pow_zero, mul_one] at this
      rcases mul_eq_zero.mp this.symm with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h hK0
        · have hα0 : α ≠ 0 := by
            rintro h'
            rw [h', pow_zero] at h
            exact one_ne_zero h
          have hα' : α = 1 := by omega
          rw [hα', pow_one] at h
          have : t = -1 := by linear_combination h
          right
          refine ⟨hα', ?_⟩
          rw [this]
          field_simp
          norm_num
      · rw [Multiset.prod_eq_zero_iff, Multiset.mem_map] at h
        obtain ⟨r, hr, hrt⟩ := h
        left
        refine ⟨r, hr, ?_⟩
        rw [hqeval] at hrt
        field_simp
        linear_combination hrt
    · rintro (⟨r, hr, rfl⟩ | ⟨hα', rfl⟩)
      · obtain ⟨t, htr⟩ := hqroot r
        refine ⟨t, hqH r hr t htr, ?_⟩
        have ht0 := hq0t r t htr
        have h' := htr
        rw [IsRoot, hqeval] at h'
        field_simp
        linear_combination h'
      · refine ⟨-1, ?_, ?_⟩
        · have := hevalid (-1)
          rw [hα'] at this
          simp only [neg_add_cancel, pow_one, mul_zero, zero_mul] at this
          exact (mul_eq_zero.mp this).resolve_left hκ
        · field_simp
          norm_num

end Main

end LevelTwo
