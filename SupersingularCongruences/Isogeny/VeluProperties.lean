/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.ModularCurve.Gamma0Pair
public import SupersingularCongruences.EllipticCurve.DeuringModel
import all SupersingularCongruences.ModularCurve.Gamma0Pair
import all SupersingularCongruences.Isogeny.Velu
import all SupersingularCongruences.EllipticCurve.Scaling

/-!
# Properties of Vélu's quotient: scaling, Deuring models, the value of `R_ℓ`

Let `W : y² = x³ + a₄ x + a₆` be a short Weierstrass curve and `C` a finite subgroup of its points.

## Main results

* `WeierstrassCurve.veluT_scaling`, `WeierstrassCurve.veluW_scaling`,
  `WeierstrassCurve.velu_scaling`: Vélu's sums for the scaled pair `(W.scaling u, ψ_u C)` are
  `u⁴ t`, `u⁶ w`, so Vélu's curve of the scaled pair is the scaling of Vélu's curve.
* `Gamma0.Pair.veluRatio_scale`: `R_ℓ` is well defined on isomorphism classes of pairs.
* `WeierstrassCurve.IsDeuringModelOver.frobenius_mem`,
  `WeierstrassCurve.IsDeuringModelOver.velu_a₄_pow`,
  `WeierstrassCurve.IsDeuringModelOver.velu_a₆_pow`:
  **Lemma 4.3(b)**: for a Deuring model `E` (over an algebraic closure `L` of `𝔽_p`) and a finite
  subgroup `C`, the subgroup `C` is stable under `π_E` and Vélu's curve `E / C` has coefficients
  in `𝔽_{p²}`. Since `π_E = [-p]` maps `C \ {0}` bijectively onto itself and acts on coordinates
  by `x ↦ x ^ (p²)`, Vélu's sums are fixed by `x ↦ x ^ (p²)`.
* `WeierstrassCurve.IsDeuringModelOver.velu`,
  `WeierstrassCurve.IsDeuringModelOver.velu_isSupersingularOver`:
  **Lemma 4.3(c)**: Vélu's curve of a Deuring model is a Deuring model (`π_{E'} = [-p]`), hence
  supersingular. By Vélu's coordinate formulas (reindexing `Q ↦ -(p • Q)` on `C \ {0}`),
  `φ ∘ [-p] = π_{E'} ∘ φ` on coordinates; since `φ` is surjective, `π_{E'} = [-p]`.
* `Gamma0.Pair.veluRatio_pow_eq`: **Lemma 4.4** (second assertion): for a pair `(E, C)` with
  `ℓ ≠ p` prime, `R_ℓ(E, C) ^ m = Δ(E / C) ^ m / Δ(E) ^ m`, `m = (p² - 1) / 12`. When `E` is a
  Deuring model, `E / C` is one as well and these are the values `κ(E') / κ(E)`.
-/

public section

open WeierstrassCurve.Affine

universe u

namespace WeierstrassCurve

section Scaling

variable {F : Type*} [Field F] [DecidableEq F]

lemma veluT_def (W : WeierstrassCurve F) (C : AddSubgroup W.toAffine.Point) :
    W.veluT C = ∑ᶠ Q ∈ (C : Set W.toAffine.Point) \ {0}, (3 * Q.xCoord ^ 2 + W.a₄) :=
  (rfl)

lemma veluW_def (W : WeierstrassCurve F) (C : AddSubgroup W.toAffine.Point) :
    W.veluW C = ∑ᶠ Q ∈ (C : Set W.toAffine.Point) \ {0},
      (5 * Q.xCoord ^ 3 + 3 * W.a₄ * Q.xCoord + 2 * W.a₆) :=
  (rfl)

lemma Affine.Point.xCoord_scaling (W : WeierstrassCurve F) (u : Fˣ) (Q : W.toAffine.Point) :
    (scaling W u Q).xCoord = u ^ 2 * Q.xCoord := by
  rcases Q with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, scaling_zero, xCoord_zero, xCoord_zero, mul_zero]
  · rw [scaling_some, xCoord_some, xCoord_some]

lemma Affine.Point.yCoord_scaling (W : WeierstrassCurve F) (u : Fˣ) (Q : W.toAffine.Point) :
    (scaling W u Q).yCoord = u ^ 3 * Q.yCoord := by
  rcases Q with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, scaling_zero, yCoord_zero, yCoord_zero, mul_zero]
  · rw [scaling_some, yCoord_some, yCoord_some]

omit [DecidableEq F] in
lemma Δ_scaling (W : WeierstrassCurve F) (u : Fˣ) : (W.scaling u).Δ = u ^ 12 * W.Δ := by
  rw [scaling, variableChange_Δ]
  simp [scalingChange]

private lemma coe_map_scaling_sdiff (W : WeierstrassCurve F) (u : Fˣ)
    (C : AddSubgroup W.toAffine.Point) :
    ((C.map (Point.scaling W u) : Set (W.scaling u).toAffine.Point) \ {0}) =
      Point.scaling W u '' ((C : Set W.toAffine.Point) \ {0}) := by
  rw [AddSubgroup.coe_map, Set.image_sdiff (Point.scaling_injective W u), Set.image_singleton,
    map_zero]

/-- Vélu's sum `t` of the scaled pair is `u⁴ t`. -/
lemma veluT_scaling (W : WeierstrassCurve F) (u : Fˣ) (C : AddSubgroup W.toAffine.Point) :
    (W.scaling u).veluT (C.map (Point.scaling W u)) = u ^ 4 * W.veluT C := by
  rw [veluT_def, veluT_def, coe_map_scaling_sdiff,
    finsum_mem_image (Point.scaling_injective W u).injOn, mul_finsum_mem]
  refine finsum_mem_congr rfl fun Q _ => ?_
  rw [Point.xCoord_scaling, scaling_a₄]
  ring

/-- Vélu's sum `w` of the scaled pair is `u⁶ w`. -/
lemma veluW_scaling (W : WeierstrassCurve F) (u : Fˣ) (C : AddSubgroup W.toAffine.Point) :
    (W.scaling u).veluW (C.map (Point.scaling W u)) = u ^ 6 * W.veluW C := by
  rw [veluW_def, veluW_def, coe_map_scaling_sdiff,
    finsum_mem_image (Point.scaling_injective W u).injOn, mul_finsum_mem]
  refine finsum_mem_congr rfl fun Q _ => ?_
  rw [Point.xCoord_scaling, scaling_a₄, scaling_a₆]
  ring

/-- Vélu's curve of the scaled pair `(W.scaling u, ψ_u C)` is the scaling by `u` of Vélu's curve
of `(W, C)`. -/
lemma velu_scaling (W : WeierstrassCurve F) (u : Fˣ) (C : AddSubgroup W.toAffine.Point) :
    (W.scaling u).velu (C.map (Point.scaling W u)) = (W.velu C).scaling u := by
  ext
  · simp
  · simp
  · simp
  · rw [velu_a₄, scaling_a₄, scaling_a₄, velu_a₄, veluT_scaling]; ring
  · rw [velu_a₆, scaling_a₆, scaling_a₆, velu_a₆, veluW_scaling]; ring

end Scaling

section Deuring

variable {L : Type u} [Field L] [DecidableEq L] {p : ℕ} [CharP L p]

omit [DecidableEq L] [CharP L p] in
private lemma map_finsum_mem_of_finite {α : Type*} (σ : L →+* L) {s : Set α} (hs : s.Finite)
    (f : α → L) : σ (∑ᶠ a ∈ s, f a) = ∑ᶠ a ∈ s, σ (f a) := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs, map_sum]

omit [DecidableEq L] [CharP L p] in
private lemma exists_some_eq_some {W : Affine L} {X Y X' Y' : L} (hR : W.Nonsingular X' Y')
    (hX : X = X') (hY : Y = Y') :
    ∃ h' : W.Nonsingular X Y, Point.some X Y h' = Point.some X' Y' hR := by
  subst hX hY; exact ⟨hR, rfl⟩

omit [CharP L p] in
/-- On a Deuring model, `π_E = [-p]` acts on coordinates by `x ↦ x ^ (p²)` (also at `0`). -/
lemma IsDeuringModelOver.coord_neg_nsmul (hp : p.Prime) {W : WeierstrassCurve L}
    (hD : W.IsDeuringModelOver p) (P : W.toAffine.Point) :
    (-(p • P)).xCoord = P.xCoord ^ p ^ 2 ∧ (-(p • P)).yCoord = P.yCoord ^ p ^ 2 := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, smul_zero, neg_zero, Point.xCoord_zero, Point.yCoord_zero,
      zero_pow (pow_ne_zero 2 hp.ne_zero)]
    exact ⟨rfl, rfl⟩
  · obtain ⟨h', e⟩ := hD.frobenius_eq x y h
    rw [← e, Point.xCoord_some, Point.yCoord_some, Point.xCoord_some, Point.yCoord_some]
    exact ⟨rfl, rfl⟩

omit [CharP L p] in
/-- On a Deuring model (supersingular), `[-p]` is injective on points. -/
lemma IsDeuringModelOver.neg_nsmul_injective {W : WeierstrassCurve L}
    (hD : W.IsDeuringModelOver p) :
    Function.Injective fun P : W.toAffine.Point => -(p • P) := by
  intro P Q h
  have h' : p • (P - Q) = 0 := by
    simp only [neg_inj] at h
    rw [smul_sub, h, sub_self]
  exact sub_eq_zero.mp (isSupersingularOver_iff.mp hD.isSupersingularOver _ h')

omit [CharP L p] in
/-- On a Deuring model, `[-p]` maps every finite subgroup `C` bijectively onto itself. -/
lemma IsDeuringModelOver.bijOn_neg_nsmul {W : WeierstrassCurve L}
    (hD : W.IsDeuringModelOver p) (C : AddSubgroup W.toAffine.Point)
    (hC : (C : Set W.toAffine.Point).Finite) :
    Set.BijOn (fun P : W.toAffine.Point => -(p • P)) C C :=
  (hC.injOn_iff_bijOn_of_mapsTo fun _ hQ => C.neg_mem (C.nsmul_mem hQ p)).mp
    hD.neg_nsmul_injective.injOn

omit [CharP L p] in
/-- On a Deuring model, `[-p]` maps `C \ {0}` bijectively onto itself, for a finite subgroup `C`.
-/
lemma IsDeuringModelOver.bijOn_neg_nsmul_sdiff {W : WeierstrassCurve L}
    (hD : W.IsDeuringModelOver p) (C : AddSubgroup W.toAffine.Point)
    (hC : (C : Set W.toAffine.Point).Finite) :
    Set.BijOn (fun P : W.toAffine.Point => -(p • P)) ((C : Set W.toAffine.Point) \ {0})
      ((C : Set W.toAffine.Point) \ {0}) := by
  refine ((hC.sdiff).injOn_iff_bijOn_of_mapsTo fun Q hQ => ⟨C.neg_mem (C.nsmul_mem hQ.1 p),
    fun h0 => hQ.2 ?_⟩).mp hD.neg_nsmul_injective.injOn
  refine hD.neg_nsmul_injective ?_
  simp only [Set.mem_singleton_iff] at h0 ⊢
  rw [h0, smul_zero, neg_zero]

omit [CharP L p] in
/-- **Lemma 4.3(b)** (the subgroup is defined over `𝔽_{p²}`): on a Deuring model, a subgroup `C`
is stable under the `p²`-power Frobenius `(x, y) ↦ (x ^ (p²), y ^ (p²))`. -/
theorem IsDeuringModelOver.frobenius_mem {W : WeierstrassCurve L} (hD : W.IsDeuringModelOver p)
    (C : AddSubgroup W.toAffine.Point) {x y : L} (h : W.toAffine.Nonsingular x y)
    (hC : Point.some x y h ∈ C) :
    ∃ h' : W.toAffine.Nonsingular (x ^ p ^ 2) (y ^ p ^ 2), Point.some _ _ h' ∈ C := by
  obtain ⟨h', e⟩ := hD.frobenius_eq x y h
  exact ⟨h', e ▸ C.neg_mem (C.nsmul_mem hC p)⟩

/-- Vélu's sum `t` of a finite subgroup of a Deuring model is fixed by `x ↦ x ^ (p²)`. -/
lemma IsDeuringModelOver.veluT_pow (hp : p.Prime) {W : WeierstrassCurve L}
    (hD : W.IsDeuringModelOver p) (C : AddSubgroup W.toAffine.Point)
    (hC : (C : Set W.toAffine.Point).Finite) : W.veluT C ^ p ^ 2 = W.veluT C := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← iterateFrobenius_def (R := L) p 2, veluT_def, map_finsum_mem_of_finite _ hC.sdiff]
  refine finsum_mem_eq_of_bijOn _ (hD.bijOn_neg_nsmul_sdiff C hC) fun Q _ => ?_
  simp only [map_add, map_mul, map_pow, map_ofNat, iterateFrobenius_def,
    (hD.coord_neg_nsmul hp Q).1, hD.a₄_pow]

/-- Vélu's sum `w` of a finite subgroup of a Deuring model is fixed by `x ↦ x ^ (p²)`. -/
lemma IsDeuringModelOver.veluW_pow (hp : p.Prime) {W : WeierstrassCurve L}
    (hD : W.IsDeuringModelOver p) (C : AddSubgroup W.toAffine.Point)
    (hC : (C : Set W.toAffine.Point).Finite) : W.veluW C ^ p ^ 2 = W.veluW C := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← iterateFrobenius_def (R := L) p 2, veluW_def, map_finsum_mem_of_finite _ hC.sdiff]
  refine finsum_mem_eq_of_bijOn _ (hD.bijOn_neg_nsmul_sdiff C hC) fun Q _ => ?_
  simp only [map_add, map_mul, map_pow, map_ofNat, iterateFrobenius_def,
    (hD.coord_neg_nsmul hp Q).1, hD.a₄_pow, hD.a₆_pow]

/-- **Lemma 4.3(b)** (the quotient is defined over `𝔽_{p²}`): for a Deuring model `W` and a
finite subgroup `C`, the coefficient `a₄` of Vélu's curve `W / C` lies in `𝔽_{p²}`. -/
theorem IsDeuringModelOver.velu_a₄_pow (hp : p.Prime) {W : WeierstrassCurve L}
    (hD : W.IsDeuringModelOver p) (C : AddSubgroup W.toAffine.Point)
    (hC : (C : Set W.toAffine.Point).Finite) : (W.velu C).a₄ ^ p ^ 2 = (W.velu C).a₄ := by
  have : Fact p.Prime := ⟨hp⟩
  rw [velu_a₄, ← iterateFrobenius_def (R := L) p 2, map_sub, map_mul, map_ofNat,
    iterateFrobenius_def, iterateFrobenius_def, hD.a₄_pow, hD.veluT_pow hp C hC]

/-- **Lemma 4.3(b)** (the quotient is defined over `𝔽_{p²}`): for a Deuring model `W` and a
finite subgroup `C`, the coefficient `a₆` of Vélu's curve `W / C` lies in `𝔽_{p²}`. -/
theorem IsDeuringModelOver.velu_a₆_pow (hp : p.Prime) {W : WeierstrassCurve L}
    (hD : W.IsDeuringModelOver p) (C : AddSubgroup W.toAffine.Point)
    (hC : (C : Set W.toAffine.Point).Finite) : (W.velu C).a₆ ^ p ^ 2 = (W.velu C).a₆ := by
  have : Fact p.Prime := ⟨hp⟩
  rw [velu_a₆, ← iterateFrobenius_def (R := L) p 2, map_sub, map_mul, map_ofNat,
    iterateFrobenius_def, iterateFrobenius_def, hD.a₆_pow, hD.veluW_pow hp C hC]

/-- **Lemma 4.3(c)**: if `W` is a Deuring model over an algebraically closed field `L` of
characteristic `p ≥ 5` and `C` is a finite subgroup, then Vélu's curve `W / C` is a Deuring model:
its coefficients lie in `𝔽_{p²}` (Lemma 4.3(b)) and `π_{E'} = [-p]`. -/
theorem IsDeuringModelOver.velu
    (hVeluIsogeny : VeluIsogeny.{u}) [IsAlgClosed L] (hp : p.Prime) (hp5 : 5 ≤ p)
    {W : WeierstrassCurve L} [W.IsElliptic] [W.IsShortNF] (hD : W.IsDeuringModelOver p)
    (C : AddSubgroup W.toAffine.Point) (hC : (C : Set W.toAffine.Point).Finite) :
    (W.velu C).IsDeuringModelOver p := by
  have : Fact p.Prime := ⟨hp⟩
  have hsmall : ∀ n : ℕ, 0 < n → n < p → (n : L) ≠ 0 := fun n hn hnp h =>
    absurd (Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff L p n).mp h)) (by omega)
  have h2 : (2 : L) ≠ 0 := by exact_mod_cast hsmall 2 (by norm_num) (by omega)
  have h3 : (3 : L) ≠ 0 := by exact_mod_cast hsmall 3 (by norm_num) (by omega)
  obtain ⟨-, φ, hker, hsurj, hφ⟩ := hVeluIsogeny W C h2 h3 hC
  set F : W.toAffine.Point → W.toAffine.Point := fun P => -(p • P) with hFdef
  set σ := iterateFrobenius L p 2
  have hσ : ∀ x : L, σ x = x ^ p ^ 2 := iterateFrobenius_def p 2
  have hFadd : ∀ P Q, F (P + Q) = F P + F Q := fun P Q => by
    simp only [hFdef, smul_add, neg_add]
  have hbij := hD.bijOn_neg_nsmul_sdiff C hC
  have hFC : ∀ P, F P ∈ C → P ∈ C := fun P hP => by
    obtain ⟨Q, hQ, hQe⟩ := (hD.bijOn_neg_nsmul C hC).surjOn hP
    exact hD.neg_nsmul_injective hQe ▸ hQ
  have hs : ((C : Set W.toAffine.Point) \ {0}).Finite := hC.sdiff
  -- Vélu's coordinate sums commute with `π = [-p]`.
  have hsum : ∀ c : W.toAffine.Point → L, (∀ P, c (F P) = σ (c P)) → ∀ P,
      c (F P) + ∑ᶠ Q ∈ (C : Set W.toAffine.Point) \ {0}, (c (F P + Q) - c Q) =
        σ (c P + ∑ᶠ Q ∈ (C : Set W.toAffine.Point) \ {0}, (c (P + Q) - c Q)) := by
    intro c hc P
    rw [map_add, map_finsum_mem_of_finite σ hs, hc]
    congr 1
    refine (finsum_mem_eq_of_bijOn F hbij fun Q _ => ?_).symm
    rw [map_sub, ← hc, ← hc, hFadd]
  have hx : ∀ P, (F P).xCoord = σ P.xCoord := fun P => by
    rw [hσ]; exact (hD.coord_neg_nsmul hp P).1
  have hy : ∀ P, (F P).yCoord = σ P.yCoord := fun P => by
    rw [hσ]; exact (hD.coord_neg_nsmul hp P).2
  refine
    { a₁_pow := by simp [zero_pow (pow_ne_zero 2 hp.ne_zero)]
      a₂_pow := by simp [zero_pow (pow_ne_zero 2 hp.ne_zero)]
      a₃_pow := by simp [zero_pow (pow_ne_zero 2 hp.ne_zero)]
      a₄_pow := hD.velu_a₄_pow hp C hC
      a₆_pow := hD.velu_a₆_pow hp C hC
      frobenius_eq := ?_ }
  intro x' y' h'
  obtain ⟨P, hP⟩ := hsurj (Point.some x' y' h')
  have hPC : P ∉ C := fun h => by
    rw [← hker, AddMonoidHom.mem_ker, hP] at h
    exact Point.some_ne_zero h' h
  have hFP : F P ∉ C := fun h => hPC (hFC P h)
  have hne : φ (F P) ≠ 0 := fun h => hFP (by rw [← hker, AddMonoidHom.mem_ker]; exact h)
  have heq : φ (F P) = -(p • Point.some x' y' h') := by
    rw [← hP, hFdef, map_neg, map_nsmul]
  have kx : (φ (F P)).xCoord = x' ^ p ^ 2 := by
    rw [(hφ (F P) hFP).1, hsum _ hx, ← (hφ P hPC).1, hP, Point.xCoord_some, hσ]
  have ky : (φ (F P)).yCoord = y' ^ p ^ 2 := by
    rw [(hφ (F P) hFP).2, hsum _ hy, ← (hφ P hPC).2, hP, Point.yCoord_some, hσ]
  rw [← heq]
  rcases hφFP : φ (F P) with _ | ⟨a, b, hab⟩
  · exact absurd hφFP hne
  rw [hφFP, Point.xCoord_some] at kx
  rw [hφFP, Point.yCoord_some] at ky
  exact exists_some_eq_some hab kx.symm ky.symm

/-- **Lemma 4.3(c)** (second part): Vélu's curve of a finite subgroup of a Deuring model is
supersingular. -/
theorem IsDeuringModelOver.velu_isSupersingularOver
    (hVeluIsogeny : VeluIsogeny.{u}) [IsAlgClosed L] (hp : p.Prime) (hp5 : 5 ≤ p)
    {W : WeierstrassCurve L} [W.IsElliptic] [W.IsShortNF] (hD : W.IsDeuringModelOver p)
    (C : AddSubgroup W.toAffine.Point) (hC : (C : Set W.toAffine.Point).Finite) :
    (W.velu C).IsSupersingularOver p :=
  (hD.velu hVeluIsogeny hp hp5 C hC).isSupersingularOver

end Deuring

end WeierstrassCurve

namespace Gamma0.Pair

open WeierstrassCurve

variable {ℓ : ℕ} {L : Type*} [Field L] [DecidableEq L]

/-- The finite subgroup of a pair is finite (as a set of points). -/
lemma finite_subgroup (P : Pair ℓ L) (hℓ : ℓ ≠ 0) :
    (P.subgroup : Set P.curve.toAffine.Point).Finite := by
  have : Finite P.subgroup := Nat.finite_of_card_ne_zero (by rw [P.card_subgroup]; exact hℓ)
  exact Set.toFinite _

/-- `R_ℓ` is invariant under isomorphisms of pairs: `R_ℓ(W.scaling u, ψ_u C) = R_ℓ(W, C)`. -/
theorem veluRatio_scale (P : Pair ℓ L) (u : Lˣ) : (P.scale u).veluRatio = P.veluRatio := by
  rw [veluRatio_def, veluRatio_def]
  change ((ℓ : L) ^ 12)⁻¹ *
      ((P.curve.scaling u).velu (P.subgroup.map (Point.scaling P.curve u))).Δ /
      (P.curve.scaling u).Δ = _
  rw [velu_scaling, Δ_scaling, Δ_scaling, mul_left_comm,
    mul_div_mul_left _ _ (pow_ne_zero 12 u.ne_zero)]

variable {p : ℕ} [CharP L p]

/-- **Lemma 4.4** (second assertion). For `p ≥ 5`, a prime `ℓ ≠ p` and a pair `(E, C)` over a
field of characteristic `p`, `R_ℓ(E, C) ^ m = Δ(E / C) ^ m / Δ(E) ^ m` with `m = (p² - 1) / 12`,
since `ℓ ^ (12 m) = ℓ ^ (p² - 1) = 1`. If `E` is a Deuring model, then so is `E / C`
(`WeierstrassCurve.IsDeuringModelOver.velu`), the differentials `dx / (2y)` are rational, and the
right-hand side is `κ(E') / κ(E)`. -/
theorem veluRatio_pow_eq (hp : p.Prime) (hp5 : 5 ≤ p) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (P : Pair ℓ L) :
    P.veluRatio ^ ((p ^ 2 - 1) / 12) =
      (P.curve.velu P.subgroup).Δ ^ ((p ^ 2 - 1) / 12) / P.curve.Δ ^ ((p ^ 2 - 1) / 12) := by
  have : Fact p.Prime := ⟨hp⟩
  have hℓ0 : (ℓ : L) ≠ 0 := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp
    ((CharP.cast_eq_zero_iff L p ℓ).mp h)).symm
  have hℓq : ((Units.mk0 (ℓ : L) hℓ0 : Lˣ) : L) ^ p ^ 2 = Units.mk0 (ℓ : L) hℓ0 := by
    have h1 : (ℓ : L) ^ p = ℓ := by
      have := map_natCast (frobenius L p) ℓ
      rwa [frobenius_def] at this
    rw [Units.val_mk0, pow_two, pow_mul, h1, h1]
  have h12 := pow_twelve_pow_eq_one hp hp5 _ hℓq
  rw [Units.val_mk0] at h12
  rw [veluRatio_def, div_pow, mul_pow, inv_pow, h12, inv_one, one_mul]

end Gamma0.Pair
