/-
Assembled by AxiomProver.
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.FieldTheory.Perfect
public import SupersingularCongruences.KatzForms.LevelN
public import SupersingularCongruences.EllipticCurve.OverClosure
public import SupersingularCongruences.Algebra.ExpandSeries
import all SupersingularCongruences.KatzForms.LevelN

/-!
# Eta powers at levels `3` and `4` and the discriminant of a Deuring model

* `LevelNForms.algebraize_pow_eq_discriminantRule`, `LevelNForms.algebraize_apply_ne_zero`:
  **Proposition 4.5(b)**: if a classical form `h` on `Γ(N)` of weight `k` with `N k = 12` has an
  integral `q`-expansion in `q^{1/N}` and satisfies `h ^ N = Δ`, then its algebraization satisfies
  `h(E, φ, ω) ^ N = Δ(E, ω)` at every valid test object, hence `h(E, φ, ω) ≠ 0`.
* `WeierstrassCurve.Δ_pow_of_isDeuringModelOver_of_etaPowers`,
  `WeierstrassCurve.discriminant_pow_of_isDeuringModelOver_of_etaPowers`: **Theorem 1.3**
  (for `ω_E = dx / (2y)` and for every `𝔽_{p²}`-rational differential), by the manuscript's
  eta-power proof, from the algebraic forms `h₃ = η⁸` and `h₄ = η⁶`.

Auxiliary results: `LevelNForms.apply_map_of_qExp_eq` (Galois equivariance of forms with integral
`q`-expansion), `LevelNTest.scale_neg_one_eq` (`[-1]` is the scaling by `-1`),
`LevelNForms.apply_neg` (`f(E, -φ, ω) = (-1)^k f(E, φ, ω)`),
`WeierstrassCurve.Affine.Point.ofCurveEq_mapRingHom_of_isDeuringModelOver` (Frobenius on points
of a Deuring model is `[-p]`), `WeierstrassCurve.exists_pow_eq_Δ_of_etaPower` (the value
`v = h_N(E, φ, ω_E)` satisfies `v ^ N = Δ(E)` and `σ v = ±v`).
-/

public section

open UpperHalfPlane CongruenceSubgroup ModularForm WeierstrassCurve WeierstrassCurve.Affine
open scoped MatrixGroups

namespace LevelOne

lemma qParam_pow_eq (N : ℕ) (hN : N ≠ 0) (z : ℂ) :
    Function.Periodic.qParam N z ^ N = Function.Periodic.qParam 1 z := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- The `q`-expansion of `Δ` in `q^{1/N}` is `Δ(q) = Δ((q^{1/N})^N)`. -/
theorem qExpansion_discriminant_eq_expandSeries (N : ℕ) (hN : N ≠ 0) :
    qExpansion N ModularForm.discriminant =
      PowerSeries.map (Int.castRingHom ℂ) (Gamma0.expandSeries N integralDiscriminant) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hmem : (N : ℝ) ∈ (𝒮ℒ).strictPeriods := by
    have := (𝒮ℒ).strictPeriods.nsmul_mem one_mem_strictPeriods_SL N
    simpa using this
  have hc : (CuspForm.discriminant : ℍ → ℂ) = ModularForm.discriminant := rfl
  rw [← hc]
  ext m
  rw [PowerSeries.coeff_map]
  refine (ModularFormClass.qExpansion_coeff_unique (Γ := 𝒮ℒ) (k := 12) hN' hmem
    (c := fun m ↦ ((Gamma0.expandSeries N integralDiscriminant).coeff m : ℂ))
    (f := CuspForm.discriminant) (fun τ ↦ ?_) m).symm
  have h1 := ModularForm.hasSum_qExpansion (Γ := 𝒮ℒ) (h := 1) CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL τ
  have hinj : Function.Injective (fun n : ℕ ↦ N * n) := fun a b hab ↦ by
    simpa [hN] using hab
  rw [← hinj.hasSum_iff]
  · convert h1 using 1
    funext n
    simp only [Function.comp_apply, Gamma0.coeff_expandSeries, dvd_mul_right, ite_true,
      Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero hN), smul_eq_mul, pow_mul,
      qParam_pow_eq N hN]
    rw [hc, isIntegralQExpansion_discriminant.coeff]
  · intro x hx
    have hx' : ¬ N ∣ x := by
      rintro ⟨c, rfl⟩
      exact hx ⟨c, rfl⟩
    simp [Gamma0.coeff_expandSeries, hx']

end LevelOne

namespace WeierstrassCurve.Affine.Point

variable {L : Type*} [Field L]

/-- Transport of points along an equality of Weierstrass curves. -/
def ofCurveEq {W₁ W₂ : WeierstrassCurve L} (h : W₁ = W₂) (P : W₁.toAffine.Point) :
    W₂.toAffine.Point :=
  cast (congrArg (fun W : WeierstrassCurve L ↦ W.toAffine.Point) h) P

lemma ofCurveEq_zero {W₁ W₂ : WeierstrassCurve L} (h : W₁ = W₂) :
    ofCurveEq h (0 : W₁.toAffine.Point) = 0 := by
  subst h
  rfl

lemma ofCurveEq_some {W₁ W₂ : WeierstrassCurve L} (h : W₁ = W₂) {x y x' y' : L}
    (hxy : W₁.toAffine.Nonsingular x y) (hxy' : W₂.toAffine.Nonsingular x' y') (hx : x = x')
    (hy : y = y') : ofCurveEq h (some x y hxy) = some x' y' hxy' := by
  subst h hx hy
  rfl

variable [DecidableEq L]

/-- On a short Weierstrass curve the scaling by `-1` is `[-1]`. -/
lemma ofCurveEq_scaling_neg_one {W : WeierstrassCurve L} [W.IsShortNF]
    (hs : W.scaling (-1) = W) (P : W.toAffine.Point) :
    ofCurveEq hs (Point.scaling W (-1) P) = -P := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, Point.scaling_zero, ofCurveEq_zero, neg_zero]
  · rw [Point.scaling_some, neg_some]
    exact ofCurveEq_some _ _ _ (by simp) (by simp [negY]; norm_num)

/-- In a Deuring model, conjugating a point by `x ↦ x ^ (p ^ 2)` is `[-p]`. -/
lemma ofCurveEq_mapRingHom_of_isDeuringModelOver {p : ℕ} {W : WeierstrassCurve L}
    (hD : W.IsDeuringModelOver p) (σ : L →+* L) (hσ : ∀ x, σ x = x ^ p ^ 2) (hW : W.map σ = W)
    (P : W.toAffine.Point) : ofCurveEq hW (mapRingHom σ P) = -(p • P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, _root_.map_zero, ofCurveEq_zero, smul_zero, neg_zero]
  · obtain ⟨h', he⟩ := hD.frobenius_eq x y h
    rw [← he, mapRingHom_some]
    exact ofCurveEq_some _ _ _ (hσ x) (hσ y)

lemma nsmul_eq_mod_nsmul {W : WeierstrassCurve L} {N : ℕ} {P : W.toAffine.Point}
    (hP : N • P = 0) (m : ℕ) : m • P = (m % N) • P := by
  conv_lhs => rw [← Nat.div_add_mod m N]
  rw [add_nsmul, mul_nsmul, hP, nsmul_zero, zero_add]

lemma neg_nsmul_eq_of_mod_eq_one {W : WeierstrassCurve L} {N : ℕ} {P : W.toAffine.Point}
    (hP : N • P = 0) {m : ℕ} (hm : m % N = 1) : -(m • P) = -P := by
  rw [nsmul_eq_mod_nsmul hP, hm, one_nsmul]

lemma neg_nsmul_eq_of_mod_add_one_eq {W : WeierstrassCurve L} {N : ℕ} {P : W.toAffine.Point}
    (hP : N • P = 0) {m : ℕ} (hm : m % N + 1 = N) : -(m • P) = P := by
  rw [nsmul_eq_mod_nsmul hP, neg_eq_iff_add_eq_zero, ← succ_nsmul, hm, hP]

end WeierstrassCurve.Affine.Point

namespace LevelNTest

variable {L : Type*} [Field L] [DecidableEq L]

/-- Rewriting the curve of a test object along an equality of curves. -/
lemma eq_mk_of_curve_eq (T : LevelNTest L) {W : WeierstrassCurve L} [W.IsElliptic]
    [W.IsShortNF] (h : T.curve = W) :
    T = LevelNTest.mk W (Point.ofCurveEq h T.P₁) (Point.ofCurveEq h T.P₂) T.diff := by
  cases T
  subst h
  rfl

lemma map_eq_mk_of_curve_eq (T : LevelNTest L) (σ : L ≃+* L) {W : WeierstrassCurve L}
    [W.IsElliptic] [W.IsShortNF] (h : T.curve.map (σ : L →+* L) = W) :
    T.map σ = LevelNTest.mk W (Point.ofCurveEq h (Point.mapRingHom (σ : L →+* L) T.P₁))
      (Point.ofCurveEq h (Point.mapRingHom (σ : L →+* L) T.P₂))
      (Units.map (σ : L →* L) T.diff) := by
  unfold map
  exact eq_mk_of_curve_eq _ h

omit [DecidableEq L] in
lemma scaling_neg_one_eq (W : WeierstrassCurve L) [W.IsShortNF] : W.scaling (-1) = W := by
  ext <;> simp <;> norm_num

/-- The automorphism `[-1]` is the scaling by `u = -1`:
`(E, (P₁, P₂), -ω) ≅ (E, (-P₁, -P₂), ...)`, i.e. `T.scale (-1) = T.neg.smulDiff (-1)`. -/
lemma scale_neg_one_eq (T : LevelNTest L) : T.scale (-1) = T.neg.smulDiff (-1) := by
  have hs : (T.scale (-1)).curve = T.curve := by
    unfold scale
    exact scaling_neg_one_eq T.curve
  rw [eq_mk_of_curve_eq (T.scale (-1)) hs]
  unfold neg smulDiff
  congr 1
  · exact Point.ofCurveEq_scaling_neg_one hs T.P₁
  · exact Point.ofCurveEq_scaling_neg_one hs T.P₂
  · exact mul_comm _ _

lemma isValid_neg {N : ℕ} {e : WeilPairing N L} {ζ : L} {T : LevelNTest L} (hT : T.IsValid e ζ) :
    T.neg.IsValid e ζ := by
  obtain ⟨⟨h1, h2, h3⟩, hζ⟩ := hT
  refine ⟨⟨?_, ?_, fun a b hab ↦ h3 a b ?_⟩, ?_⟩
  · unfold neg; rw [smul_neg, h1, neg_zero]
  · unfold neg; rw [smul_neg, h2, neg_zero]
  · unfold neg at hab
    rw [smul_neg, smul_neg, ← neg_add, neg_eq_zero] at hab
    exact hab
  · unfold neg
    rw [e.pair_neg_neg _ h1 h2, hζ]

lemma discriminantRule_def (T : LevelNTest L) :
    T.discriminantRule = ((T.diff : L) ^ 12)⁻¹ * T.curve.Δ := by
  unfold discriminantRule
  rfl

/-- `Δ(E, ω) ≠ 0`. -/
lemma discriminantRule_ne_zero (T : LevelNTest L) : T.discriminantRule ≠ 0 := by
  rw [discriminantRule_def]
  exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ T.diff.ne_zero)) T.curve.isUnit_Δ.ne_zero

end LevelNTest

namespace LevelNForms

variable {N : ℕ} {L : Type*} [Field L] [DecidableEq L] {e : WeilPairing N L} {ζ : L}
  (F : LevelNForms N L e ζ)

/-- The `q`-expansion only depends on the underlying function (the weight may be rewritten). -/
lemma qExp_congr {a b : ℤ} (hab : a = b) (f : F.form a) (g : F.form b) (hfg : f.1 = g.1) :
    F.qExp a f = F.qExp b g := by
  subst hab
  rw [Subtype.ext hfg]

/-- Positive powers of forms are forms. -/
lemma pow_succ_mem {k : ℤ} {f : LevelNTest L → L} (hf : f ∈ F.form k) (n : ℕ) :
    f ^ (n + 1) ∈ F.form (((n + 1 : ℕ) : ℤ) * k) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    have := F.mul_mem hf ih
    rw [← pow_succ'] at this
    convert this using 2
    push_cast
    ring

/-- The `q`-expansion of a positive power. -/
lemma qExp_pow_succ {k : ℤ} (f : F.form k) (n : ℕ) :
    F.qExp (((n + 1 : ℕ) : ℤ) * k) ⟨f.1 ^ (n + 1), F.pow_succ_mem f.2 n⟩ =
      F.qExp k f ^ (n + 1) := by
  induction n with
  | zero => exact (F.qExp_congr (by simp) f _ (by simp)).symm.trans (pow_one _).symm
  | succ n ih =>
    rw [F.qExp_congr (b := k + ((n + 1 : ℕ) : ℤ) * k) (by push_cast; ring) _
      ⟨f.1 * f.1 ^ (n + 1), F.mul_mem f.2 (F.pow_succ_mem f.2 n)⟩ (pow_succ' _ _)]
    exact (F.qExp_mul f ⟨_, F.pow_succ_mem f.2 n⟩).trans (by rw [ih, ← pow_succ'])

/-- `Γ(N)` has the strict period `N`. -/
lemma natCast_mem_strictPeriods_Gamma (N : ℕ) :
    (N : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma N)).strictPeriods := by
  rw [strictPeriods_Gamma]
  exact AddSubgroup.mem_zmultiples _

/-- The classical identity `h ^ N = Δ` on `ℍ` gives `G ^ N = Δ(q^N)` for the integral
`q`-expansion `G` of `h` in `q^{1/N}`. -/
lemma pow_eq_expandSeries_of_pow_eq_discriminant (hN : N ≠ 0) {k : ℤ}
    (h : ModularForm (Gamma N) k) (G : PowerSeries ℤ)
    (hG : PowerSeries.map (Int.castRingHom ℂ) G = UpperHalfPlane.qExpansion N h)
    (hΔ : ∀ τ, h τ ^ N = ModularForm.discriminant τ) :
    G ^ N = Gamma0.expandSeries N LevelOne.integralDiscriminant := by
  apply LevelOne.map_intCast_injective
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hpow : (⇑(h.pow N) : ℍ → ℂ) = ModularForm.discriminant := by
    funext τ
    simp [hΔ]
  rw [map_pow, hG, ← ModularForm.qExpansion_pow hN' (natCast_mem_strictPeriods_Gamma N), hpow,
    LevelOne.qExpansion_discriminant_eq_expandSeries N hN]

/-- **Proposition 4.5(b)** (`h_N ^ N = Δ` as algebraic forms). Let `h` be a classical form of
weight `k` on `Γ(N)`, `N k = 12`, whose `q`-expansion in `q^{1/N}` has integer coefficients `G`,
with `h ^ N = Δ` on `ℍ`. Then its algebraization satisfies `h(E, φ, ω) ^ N = Δ(E, ω)` at every
valid test object `(E, φ, ω)`. -/
theorem algebraize_pow_eq_discriminantRule {k : ℤ} (h : ModularForm (Gamma N) k)
    (G : PowerSeries ℤ)
    (hG : PowerSeries.map (Int.castRingHom ℂ) G = UpperHalfPlane.qExpansion N h)
    (hNk : (N : ℤ) * k = 12) (hΔ : ∀ τ, h τ ^ N = ModularForm.discriminant τ)
    {T : LevelNTest L} (hT : T.IsValid e ζ) :
    (F.algebraize h G hG).1 T ^ N = T.discriminantRule := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hNk)
  set f := F.algebraize h G hG
  have hmem : f.1 ^ (n + 1) ∈ F.form 12 := hNk ▸ F.pow_succ_mem f.2 n
  have hq : F.qExp 12 ⟨f.1 ^ (n + 1), hmem⟩ =
      F.qExp 12 ⟨LevelNTest.discriminantRule, F.discriminant_mem⟩ := by
    rw [← F.qExp_congr hNk ⟨_, F.pow_succ_mem f.2 n⟩ _ rfl, F.qExp_pow_succ, F.qExp_algebraize,
      F.qExp_discriminant, ← map_pow,
      pow_eq_expandSeries_of_pow_eq_discriminant n.succ_ne_zero h G hG hΔ]
    ext m
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_map, Gamma0.coeff_expandSeries]
    split_ifs <;> simp
  simpa using F.eq_of_qExp_eq _ _ hq hT

/-- **Proposition 4.5(b)** (nonvanishing): `h(E, φ, ω) ≠ 0` at every valid test object. -/
theorem algebraize_apply_ne_zero {k : ℤ} (h : ModularForm (Gamma N) k) (G : PowerSeries ℤ)
    (hG : PowerSeries.map (Int.castRingHom ℂ) G = UpperHalfPlane.qExpansion N h)
    (hNk : (N : ℤ) * k = 12) (hΔ : ∀ τ, h τ ^ N = ModularForm.discriminant τ)
    {T : LevelNTest L} (hT : T.IsValid e ζ) :
    (F.algebraize h G hG).1 T ≠ 0 := by
  intro h0
  have := F.algebraize_pow_eq_discriminantRule h G hG hNk hΔ hT
  have hN : N ≠ 0 := by rintro rfl; simp at hNk
  rw [h0, zero_pow hN] at this
  exact LevelNTest.discriminantRule_ne_zero T this.symm

/-- Galois equivariance of a form with integral `q`-expansion: `f(T^σ) = σ(f(T))` for `σ` fixing
`ζ`. -/
theorem apply_map_of_qExp_eq {k : ℤ} (f : F.form k) (G : PowerSeries ℤ)
    (hf : F.qExp k f = PowerSeries.map (Int.castRingHom L) G) (σ : L ≃+* L) (hσ : σ ζ = ζ)
    {T : LevelNTest L} (hT : T.IsValid e ζ) : f.1 (T.map σ) = σ (f.1 T) := by
  have hσ' : σ.symm ζ = ζ := σ.symm_apply_eq.mpr hσ.symm
  have hq : F.qExp k ⟨fun T ↦ σ.symm (f.1 (T.map σ.symm.symm)), F.galois_mem f.2 σ.symm hσ'⟩ =
      F.qExp k f := by
    rw [F.qExp_galois f σ.symm hσ', hf]
    ext n
    simp
  have := F.eq_of_qExp_eq _ _ hq hT
  simp only [RingEquiv.symm_symm] at this
  rw [← this, RingEquiv.apply_symm_apply]

/-- `f(E, (-P₁, -P₂), ω) = (-1)^k f(E, (P₁, P₂), ω)`: the automorphism `[-1]` is the scaling by
`-1`, which pulls `ω` back to `-ω`. -/
theorem apply_neg {k : ℤ} {f : LevelNTest L → L} (hf : f ∈ F.form k) {T : LevelNTest L}
    (hT : T.IsValid e ζ) : f T.neg = (-1 : L) ^ k * f T := by
  have h1 := F.apply_scale hf hT (-1)
  rw [LevelNTest.scale_neg_one_eq, F.apply_smulDiff hf (LevelNTest.isValid_neg hT)] at h1
  rw [← h1, ← mul_assoc, Units.val_neg, Units.val_one, ← zpow_add₀ (by simp)]
  simp

end LevelNForms

namespace WeierstrassCurve

variable {L : Type*} [Field L] [IsAlgClosed L] [DecidableEq L] {p : ℕ} [CharP L p]

/-- The value `v = h_N(E, φ, ω_E)` of an eta power at a level-`N` structure `φ` on a Deuring model
`E`: `v ≠ 0`, `v ^ N = Δ(E)`, and the Frobenius `σ = (x ↦ x ^ (p ^ 2))` acts by `σ(v) = v` if
`-p ≡ 1 (mod N)` and by `σ(v) = (-1)^k v` if `-p ≡ -1 (mod N)`. -/
theorem exists_pow_eq_Δ_of_etaPower (hp : p.Prime) (W : WeierstrassCurve L) [W.IsElliptic]
    [W.IsShortNF] (hD : W.IsDeuringModelOver p) {N : ℕ} (e : WeilPairing N L) {ζ : L}
    (hζ : IsPrimitiveRoot ζ N) (F : LevelNForms N L e ζ) {k : ℤ} (h : ModularForm (Gamma N) k)
    (G : PowerSeries ℤ)
    (hG : PowerSeries.map (Int.castRingHom ℂ) G = UpperHalfPlane.qExpansion N h)
    (hNk : (N : ℤ) * k = 12) (hΔ : ∀ τ, h τ ^ N = ModularForm.discriminant τ)
    (hpN : p ^ 2 % N = 1) :
    ∃ v : L, v ≠ 0 ∧ v ^ N = W.Δ ∧ (p % N + 1 = N → v ^ p ^ 2 = v) ∧
      (p % N = 1 → v ^ p ^ 2 = (-1 : L) ^ k * v) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P₁, P₂, hB, hpair⟩ := e.exists_basis W hζ
  set T₀ : LevelNTest L := LevelNTest.mk W P₁ P₂ 1 with hT₀_def
  have hT₀ : T₀.IsValid e ζ := ⟨hB, hpair⟩
  set f := F.algebraize h G hG
  refine ⟨f.1 T₀, F.algebraize_apply_ne_zero h G hG hNk hΔ hT₀, ?_, ?_⟩
  · rw [F.algebraize_pow_eq_discriminantRule h G hG hNk hΔ hT₀, LevelNTest.discriminantRule_def]
    simp [T₀]
  set σ : L ≃+* L := iterateFrobeniusEquiv L p 2
  have hσ : ∀ x, σ x = x ^ p ^ 2 := fun x ↦ by
    simp [σ, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  have hσζ : σ ζ = ζ := by
    rw [hσ, ← pow_mod_orderOf, ← hζ.eq_orderOf, hpN, pow_one]
  have hW : W.map (σ : L →+* L) = W := by
    ext <;> simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, RingEquiv.coe_toRingHom, hσ,
      hD.a₁_pow, hD.a₂_pow, hD.a₃_pow, hD.a₄_pow, hD.a₆_pow]
  have hmap : T₀.map σ = LevelNTest.mk W (-(p • P₁)) (-(p • P₂)) 1 := by
    rw [LevelNTest.map_eq_mk_of_curve_eq T₀ σ hW]
    simp only [T₀]
    rw [Point.ofCurveEq_mapRingHom_of_isDeuringModelOver hD _ hσ,
      Point.ofCurveEq_mapRingHom_of_isDeuringModelOver hD _ hσ, _root_.map_one]
  have hgal := F.apply_map_of_qExp_eq f G (F.qExp_algebraize h G hG) σ hσζ hT₀
  rw [hmap, hσ] at hgal
  refine ⟨fun hm ↦ ?_, fun hm ↦ ?_⟩
  · rw [← hgal, Point.neg_nsmul_eq_of_mod_add_one_eq hB.1 hm,
      Point.neg_nsmul_eq_of_mod_add_one_eq hB.2.1 hm]
  · rw [← hgal, Point.neg_nsmul_eq_of_mod_eq_one hB.1 hm,
      Point.neg_nsmul_eq_of_mod_eq_one hB.2.1 hm, ← F.apply_neg f.2 hT₀]
    rfl

private lemma sq_mod_twelve (hp : p.Prime) (hp5 : 5 ≤ p) : p ^ 2 % 12 = 1 := by
  have h2 : p % 2 = 1 := by
    rcases Nat.even_or_odd p with h | h
    · exact absurd ((Nat.Prime.even_iff hp).mp h) (by omega)
    · exact Nat.odd_iff.mp h
  have h3 : p % 3 ≠ 0 := fun h ↦ by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by omega
  rw [Nat.pow_mod]
  rcases this with h | h | h | h <;> rw [h]

omit [IsAlgClosed L] [DecidableEq L] in
private lemma pow_sub_one_eq_of_pow_eq {v c : L} (hv : v ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (h : v ^ n = c * v) : v ^ (n - 1) = c := by
  refine mul_right_cancel₀ hv ?_
  rw [← pow_succ, Nat.sub_add_cancel hn, h]

/-- **Theorem 1.3** (rationality of supersingular discriminants), by the manuscript's eta-power
proof. Let `p ≥ 5` and let `W` be a Deuring model over `L` (coefficients in `𝔽_{p²}`,
`π_E = [-p]`). Suppose given, at levels `N = 3, 4`, the Weil pairing, a primitive `N`-th root of
unity `ζ_N`, the algebraic forms of level `N`, and the eta powers `h₃ = η⁸ ∈ M₄(Γ(3))`,
`h₄ = η⁶ ∈ M₃(Γ(4))` with integral `q`-expansions in `q^{1/N}` and `h_N ^ N = Δ`
(Proposition 4.5(a)). Then `Δ(E, ω_E) ^ ((p² - 1) / 12) = (-1)^((p+1)/2)`. -/
theorem Δ_pow_of_isDeuringModelOver_of_etaPowers (hp : p.Prime) (hp5 : 5 ≤ p)
    (W : WeierstrassCurve L) [W.IsElliptic] [W.IsShortNF] (hD : W.IsDeuringModelOver p)
    (e₃ : WeilPairing 3 L) {ζ₃ : L} (hζ₃ : IsPrimitiveRoot ζ₃ 3) (F₃ : LevelNForms 3 L e₃ ζ₃)
    (h₃ : ModularForm (Gamma 3) 4) (G₃ : PowerSeries ℤ)
    (hG₃ : PowerSeries.map (Int.castRingHom ℂ) G₃ = UpperHalfPlane.qExpansion 3 h₃)
    (hΔ₃ : ∀ τ, h₃ τ ^ 3 = ModularForm.discriminant τ)
    (e₄ : WeilPairing 4 L) {ζ₄ : L} (hζ₄ : IsPrimitiveRoot ζ₄ 4) (F₄ : LevelNForms 4 L e₄ ζ₄)
    (h₄ : ModularForm (Gamma 4) 3) (G₄ : PowerSeries ℤ)
    (hG₄ : PowerSeries.map (Int.castRingHom ℂ) G₄ = UpperHalfPlane.qExpansion 4 h₄)
    (hΔ₄ : ∀ τ, h₄ τ ^ 4 = ModularForm.discriminant τ) :
    W.Δ ^ ((p ^ 2 - 1) / 12) = (-1) ^ ((p + 1) / 2) := by
  have h12 := sq_mod_twelve hp hp5
  have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  have h3 : p % 3 = 1 ∨ p % 3 + 1 = 3 := by
    have := Nat.mod_lt p (show 0 < 3 by norm_num)
    have : p % 3 ≠ 0 := fun h ↦ by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h)
      omega
    omega
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by
    have := Nat.mod_lt p (show 0 < 4 by norm_num)
    have : p % 2 = 1 := by
      rcases Nat.even_or_odd p with h | h
      · exact absurd ((Nat.Prime.even_iff hp).mp h) (by omega)
      · exact Nat.odd_iff.mp h
    omega
  set m := (p ^ 2 - 1) / 12 with hm
  have h12m : 12 * m = p ^ 2 - 1 := by omega
  -- Level `3`: `κ⁴ = 1`.
  obtain ⟨v₃, hv₃0, hv₃, hA₃, hB₃⟩ := exists_pow_eq_Δ_of_etaPower hp W hD e₃ hζ₃ F₃ h₃ G₃ hG₃
    (by norm_num) hΔ₃ (by omega)
  have hσ₃ : v₃ ^ p ^ 2 = 1 * v₃ := by
    rcases h3 with h | h
    · rw [hB₃ h]; norm_num
    · rw [hA₃ h, one_mul]
  have hκ4 : (W.Δ ^ m) ^ 4 = 1 := by
    rw [← hv₃, ← pow_mul, ← pow_mul, show 3 * (m * 4) = 12 * m by ring, h12m,
      pow_sub_one_eq_of_pow_eq hv₃0 hp1 hσ₃]
  -- Level `4`: `κ³ = (-1)^((p+1)/2)`.
  obtain ⟨v₄, hv₄0, hv₄, hA₄, hB₄⟩ := exists_pow_eq_Δ_of_etaPower hp W hD e₄ hζ₄ F₄ h₄ G₄ hG₄
    (by norm_num) hΔ₄ (by omega)
  have hσ₄ : v₄ ^ p ^ 2 = (-1) ^ ((p + 1) / 2) * v₄ := by
    rcases h4 with h | h
    · rw [hB₄ h, Odd.neg_one_pow ⟨p / 4, by omega⟩]
      norm_num
    · rw [hA₄ (by omega), Even.neg_one_pow ⟨p / 4 + 1, by omega⟩, one_mul]
  have hκ3 : (W.Δ ^ m) ^ 3 = (-1) ^ ((p + 1) / 2) := by
    rw [← hv₄, ← pow_mul, ← pow_mul, show 4 * (m * 3) = 12 * m by ring, h12m,
      pow_sub_one_eq_of_pow_eq hv₄0 hp1 hσ₄]
  -- `κ = κ⁴ · κ³ · (-1)^((p+1)/2) = (-1)^((p+1)/2)`.
  have hsq : ((-1 : L) ^ ((p + 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    simp
  calc W.Δ ^ m = W.Δ ^ m * ((W.Δ ^ m) ^ 3 * (-1) ^ ((p + 1) / 2)) := by
        rw [hκ3, ← sq, hsq, mul_one]
    _ = (W.Δ ^ m) ^ 4 * (-1) ^ ((p + 1) / 2) := by ring
    _ = (-1) ^ ((p + 1) / 2) := by rw [hκ4, one_mul]

/-- **Theorem 1.3** for an arbitrary `𝔽_{p²}`-rational differential `ω = c · dx / (2y)`,
`c ^ (p ^ 2) = c`, by the eta-power proof: `Δ(E, ω) ^ ((p² - 1) / 12) = (-1)^((p+1)/2)`, where
`Δ(E, c ω_E) = c⁻¹² Δ(E)`. -/
theorem discriminant_pow_of_isDeuringModelOver_of_etaPowers (hp : p.Prime) (hp5 : 5 ≤ p)
    (W : WeierstrassCurve L) [W.IsElliptic] [W.IsShortNF] (hD : W.IsDeuringModelOver p)
    (e₃ : WeilPairing 3 L) {ζ₃ : L} (hζ₃ : IsPrimitiveRoot ζ₃ 3) (F₃ : LevelNForms 3 L e₃ ζ₃)
    (h₃ : ModularForm (Gamma 3) 4) (G₃ : PowerSeries ℤ)
    (hG₃ : PowerSeries.map (Int.castRingHom ℂ) G₃ = UpperHalfPlane.qExpansion 3 h₃)
    (hΔ₃ : ∀ τ, h₃ τ ^ 3 = ModularForm.discriminant τ)
    (e₄ : WeilPairing 4 L) {ζ₄ : L} (hζ₄ : IsPrimitiveRoot ζ₄ 4) (F₄ : LevelNForms 4 L e₄ ζ₄)
    (h₄ : ModularForm (Gamma 4) 3) (G₄ : PowerSeries ℤ)
    (hG₄ : PowerSeries.map (Int.castRingHom ℂ) G₄ = UpperHalfPlane.qExpansion 4 h₄)
    (hΔ₄ : ∀ τ, h₄ τ ^ 4 = ModularForm.discriminant τ) (c : Lˣ) (hc : (c : L) ^ p ^ 2 = c) :
    (((c : L) ^ 12)⁻¹ * W.Δ) ^ ((p ^ 2 - 1) / 12) = (-1) ^ ((p + 1) / 2) := by
  have h12 := sq_mod_twelve hp hp5
  have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  have hc1 : (c : L) ^ (p ^ 2 - 1) = 1 :=
    pow_sub_one_eq_of_pow_eq c.ne_zero hp1 (by rw [hc, one_mul])
  rw [mul_pow, inv_pow, ← pow_mul, show 12 * ((p ^ 2 - 1) / 12) = p ^ 2 - 1 by omega, hc1,
    inv_one, one_mul, Δ_pow_of_isDeuringModelOver_of_etaPowers hp hp5 W hD e₃ hζ₃ F₃ h₃ G₃ hG₃
      hΔ₃ e₄ hζ₄ F₄ h₄ G₄ hG₄ hΔ₄]

end WeierstrassCurve
