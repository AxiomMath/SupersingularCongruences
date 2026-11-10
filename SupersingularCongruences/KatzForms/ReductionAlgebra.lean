/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.KatzForms.BehrensC4
import all SupersingularCongruences.KatzForms.BehrensC4
import all SupersingularCongruences.ModularCurve.Gamma0Pair

/-!
# The algebra of reductions of classical forms as Katz forms

General lemmas on `p`-integral rational power series, their reductions `PowerSeries.reduceTo`,
the series `Gamma0.expandSeries` (`G(q) ↦ G(q^ℓ)`), and the Katz forms
`KatzForms.reduce f G hG hfG` obtained from classical forms:

* `PowerSeries.IsPIntegral` is closed under the ring operations, and `PowerSeries.reduceTo L` is
  additive and multiplicative on `p`-integral series (`L` of characteristic `p`);
* `Gamma0.expandSeries ℓ` is a ring homomorphism for `ℓ ≠ 0` and commutes with coefficient maps;
* the `q`-expansion map of a `KatzForms` structure is compatible with weight casts, powers and
  scalar multiples, and a form is determined by its `q`-expansion (`KatzForms.eq_of_qExp_eq`);
* `KatzForms.reduce_eq_of_qExp_eq`: the reduction of a classical form is the Katz form with the
  reduced `q`-expansion.
-/

public section

open PowerSeries Gamma0
open scoped MatrixGroups

namespace Rat

variable {p : ℕ} [hp : Fact p.Prime]

/-- Sums of `p`-integral rationals are `p`-integral. -/
lemma not_dvd_den_add {a b : ℚ} (ha : ¬ p ∣ a.den) (hb : ¬ p ∣ b.den) : ¬ p ∣ (a + b).den :=
  fun h ↦ (hp.out.dvd_mul.mp (h.trans (Rat.add_den_dvd a b))).elim ha hb

/-- Products of `p`-integral rationals are `p`-integral. -/
lemma not_dvd_den_mul {a b : ℚ} (ha : ¬ p ∣ a.den) (hb : ¬ p ∣ b.den) : ¬ p ∣ (a * b).den :=
  fun h ↦ (hp.out.dvd_mul.mp (h.trans (Rat.mul_den_dvd a b))).elim ha hb

omit hp in
lemma not_dvd_den_neg {a : ℚ} (ha : ¬ p ∣ a.den) : ¬ p ∣ (-a).den := by
  rwa [Rat.neg_den]

lemma not_dvd_den_sub {a b : ℚ} (ha : ¬ p ∣ a.den) (hb : ¬ p ∣ b.den) : ¬ p ∣ (a - b).den := by
  rw [sub_eq_add_neg]
  exact not_dvd_den_add ha (not_dvd_den_neg hb)

lemma not_dvd_den_intCast (n : ℤ) : ¬ p ∣ (n : ℚ).den := by
  rw [Rat.den_intCast, Nat.dvd_one]
  exact hp.out.one_lt.ne'

lemma not_dvd_den_natCast (n : ℕ) : ¬ p ∣ (n : ℚ).den := by
  exact_mod_cast not_dvd_den_intCast (p := p) n

lemma not_dvd_den_inv_natCast {n : ℕ} (hn : ¬ p ∣ n) : ¬ p ∣ ((n : ℚ)⁻¹).den := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [hp.out.one_lt.ne']
  · rwa [Rat.inv_natCast_den_of_pos hpos]

lemma not_dvd_den_sum {ι : Type*} (s : Finset ι) {f : ι → ℚ} (hf : ∀ i ∈ s, ¬ p ∣ (f i).den) :
    ¬ p ∣ (∑ i ∈ s, f i).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using not_dvd_den_intCast (p := p) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact not_dvd_den_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

variable {L : Type*} [Field L] [CharP L p]

omit hp in
lemma den_ne_zero_of_not_dvd {a : ℚ} (ha : ¬ p ∣ a.den) : (a.den : L) ≠ 0 :=
  fun h ↦ ha ((CharP.cast_eq_zero_iff L p _).mp h)

omit hp in
lemma cast_add_of_not_dvd {a b : ℚ} (ha : ¬ p ∣ a.den) (hb : ¬ p ∣ b.den) :
    ((a + b : ℚ) : L) = a + b :=
  Rat.cast_add_of_ne_zero (den_ne_zero_of_not_dvd ha) (den_ne_zero_of_not_dvd hb)

omit hp in
lemma cast_mul_of_not_dvd {a b : ℚ} (ha : ¬ p ∣ a.den) (hb : ¬ p ∣ b.den) :
    ((a * b : ℚ) : L) = a * b :=
  Rat.cast_mul_of_ne_zero (den_ne_zero_of_not_dvd ha) (den_ne_zero_of_not_dvd hb)

omit hp in
lemma cast_sub_of_not_dvd {a b : ℚ} (ha : ¬ p ∣ a.den) (hb : ¬ p ∣ b.den) :
    ((a - b : ℚ) : L) = a - b := by
  rw [sub_eq_add_neg, cast_add_of_not_dvd ha (not_dvd_den_neg hb), Rat.cast_neg, sub_eq_add_neg]

lemma cast_sum_of_not_dvd {ι : Type*} (s : Finset ι) {f : ι → ℚ}
    (hf : ∀ i ∈ s, ¬ p ∣ (f i).den) : ((∑ i ∈ s, f i : ℚ) : L) = ∑ i ∈ s, (f i : L) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      cast_add_of_not_dvd (hf a (Finset.mem_insert_self a s))
        (not_dvd_den_sum s fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

omit hp in
/-- A `p`-integral rational whose numerator is divisible by `p` reduces to `0`. -/
lemma cast_eq_zero_of_dvd_num {a : ℚ} (hn : (p : ℤ) ∣ a.num) : (a : L) = 0 := by
  rw [Rat.cast_def]
  obtain ⟨c, hc⟩ := hn
  rw [hc, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero, zero_mul, zero_div]

end Rat

namespace PowerSeries

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
lemma IsPIntegral.coeff {G : PowerSeries ℚ} (hG : G.IsPIntegral p) (n : ℕ) :
    ¬ p ∣ (G.coeff n).den :=
  isPIntegral_iff.mp hG n

lemma IsPIntegral.add {G H : PowerSeries ℚ} (hG : G.IsPIntegral p) (hH : H.IsPIntegral p) :
    (G + H).IsPIntegral p := isPIntegral_iff.mpr fun n ↦ by
  rw [map_add]; exact Rat.not_dvd_den_add (hG.coeff n) (hH.coeff n)

omit hp in
lemma IsPIntegral.neg {G : PowerSeries ℚ} (hG : G.IsPIntegral p) : (-G).IsPIntegral p :=
  isPIntegral_iff.mpr fun n ↦ by rw [map_neg]; exact Rat.not_dvd_den_neg (hG.coeff n)

lemma IsPIntegral.sub {G H : PowerSeries ℚ} (hG : G.IsPIntegral p) (hH : H.IsPIntegral p) :
    (G - H).IsPIntegral p := isPIntegral_iff.mpr fun n ↦ by
  rw [map_sub]; exact Rat.not_dvd_den_sub (hG.coeff n) (hH.coeff n)

lemma IsPIntegral.mul {G H : PowerSeries ℚ} (hG : G.IsPIntegral p) (hH : H.IsPIntegral p) :
    (G * H).IsPIntegral p := isPIntegral_iff.mpr fun n ↦ by
  rw [coeff_mul]
  exact Rat.not_dvd_den_sum _ fun x _ ↦ Rat.not_dvd_den_mul (hG.coeff _) (hH.coeff _)

lemma isPIntegral_C (a : ℚ) (ha : ¬ p ∣ a.den) : (C a).IsPIntegral p :=
    isPIntegral_iff.mpr fun n ↦ by
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact Rat.not_dvd_den_intCast 0

lemma isPIntegral_one : (1 : PowerSeries ℚ).IsPIntegral p := by
  simpa using isPIntegral_C (p := p) 1 (by simpa using Rat.not_dvd_den_intCast (p := p) 1)

lemma IsPIntegral.pow {G : PowerSeries ℚ} (hG : G.IsPIntegral p) (n : ℕ) :
    (G ^ n).IsPIntegral p := by
  induction n with
  | zero => simpa using isPIntegral_one
  | succ n ih => rw [pow_succ]; exact ih.mul hG

lemma IsPIntegral.const_mul {G : PowerSeries ℚ} (hG : G.IsPIntegral p) {a : ℚ}
    (ha : ¬ p ∣ a.den) : (C a * G).IsPIntegral p :=
  (isPIntegral_C a ha).mul hG

variable (L : Type*) [Field L]

lemma reduceTo_map_intCast (G : PowerSeries ℤ) :
    (PowerSeries.map (Int.castRingHom ℚ) G).reduceTo L = PowerSeries.map (Int.castRingHom L) G := by
  ext n
  simp [coeff_map]

variable [CharP L p] {L}

omit hp in
lemma reduceTo_add {G H : PowerSeries ℚ} (hG : G.IsPIntegral p) (hH : H.IsPIntegral p) :
    (G + H).reduceTo L = G.reduceTo L + H.reduceTo L := by
  ext n
  simp only [coeff_reduceTo, map_add]
  exact Rat.cast_add_of_not_dvd (hG.coeff n) (hH.coeff n)

omit hp in
lemma reduceTo_sub {G H : PowerSeries ℚ} (hG : G.IsPIntegral p) (hH : H.IsPIntegral p) :
    (G - H).reduceTo L = G.reduceTo L - H.reduceTo L := by
  ext n
  simp only [coeff_reduceTo, map_sub]
  exact Rat.cast_sub_of_not_dvd (hG.coeff n) (hH.coeff n)

lemma reduceTo_mul {G H : PowerSeries ℚ} (hG : G.IsPIntegral p) (hH : H.IsPIntegral p) :
    (G * H).reduceTo L = G.reduceTo L * H.reduceTo L := by
  ext n
  simp only [coeff_reduceTo, coeff_mul]
  rw [Rat.cast_sum_of_not_dvd _ fun x _ ↦ Rat.not_dvd_den_mul (hG.coeff _) (hH.coeff _)]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Rat.cast_mul_of_not_dvd (hG.coeff _) (hH.coeff _)]

lemma reduceTo_one : (1 : PowerSeries ℚ).reduceTo L = 1 := by
  ext n
  simp only [coeff_reduceTo, coeff_one]
  split_ifs <;> simp

lemma reduceTo_C (a : ℚ) : (C a).reduceTo L = C (a : L) := by
  ext n
  simp only [coeff_reduceTo, coeff_C]
  split_ifs <;> simp

lemma reduceTo_pow {G : PowerSeries ℚ} (hG : G.IsPIntegral p) (n : ℕ) :
    (G ^ n).reduceTo L = G.reduceTo L ^ n := by
  induction n with
  | zero => simpa using reduceTo_one
  | succ n ih => rw [pow_succ, reduceTo_mul (hG.pow n) hG, ih, pow_succ]

end PowerSeries

namespace Gamma0

variable {R S : Type*} [CommRing R] [CommRing S]

lemma reduceTo_expandSeries (L : Type*) [Field L] (ℓ : ℕ) (G : PowerSeries ℚ) :
    (expandSeries ℓ G).reduceTo L = expandSeries ℓ (G.reduceTo L) := by
  ext n
  simp only [coeff_reduceTo, coeff_expandSeries]
  split_ifs <;> simp

end Gamma0

namespace Gamma0.Pair

variable {ℓ : ℕ} {L : Type*} [Field L] [DecidableEq L]

lemma veluRatio_eq (P : Pair ℓ L) :
    P.veluRatio = ((ℓ : L) ^ 12)⁻¹ * (P.curve.velu P.subgroup).Δ / P.curve.Δ := by
  rw [veluRatio]

/-- The value of `R_ℓ` at a pair is the quotient of the values of the rules `ℓ⁻¹² Δ(E / C, ω')`
and `Δ(E, ω)` at any test object over it. -/
lemma veluRatio_eq_div (T : Test ℓ L) :
    T.toPair.veluRatio = ((ℓ : L) ^ 12)⁻¹ * veluDiscriminantRule T / discriminantRule T := by
  rw [veluRatio_eq, veluDiscriminantRule_apply, discriminantRule_apply]
  have h : ((T.diff : L) ^ 12)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ T.diff.ne_zero)
  rw [mul_left_comm, mul_div_mul_left _ _ h]

end Gamma0.Pair

namespace Gamma0.Test

variable {ℓ : ℕ} {L : Type*} [Field L] [DecidableEq L]

@[simp] lemma smulDiff_diff (T : Test ℓ L) (c : Lˣ) : (T.smulDiff c).diff = c * T.diff := by
  rw [smulDiff]

@[simp] lemma smulDiff_toPair (T : Test ℓ L) (c : Lˣ) : (T.smulDiff c).toPair = T.toPair := by
  rw [smulDiff]

end Gamma0.Test

namespace KatzForms

variable {p ℓ : ℕ} {L : Type*} [Field L] [DecidableEq L] (K : KatzForms p ℓ L)

lemma mem_form_of_eq {k k' : ℤ} (h : k = k') {f : Test ℓ L → L} (hf : f ∈ K.form k) :
    f ∈ K.form k' := h ▸ hf

/-- The `q`-expansion is compatible with casts of the weight. -/
lemma qExp_congr {k k' : ℤ} (h : k = k') {f f' : Test ℓ L → L} (hff : f = f')
    (hf : f ∈ K.form k) (hf' : f' ∈ K.form k') : K.qExp k ⟨f, hf⟩ = K.qExp k' ⟨f', hf'⟩ := by
  subst h hff
  rfl

/-- The `q`-expansion principle, for forms given as functions. -/
lemma eq_of_qExp_eq {k : ℤ} {f g : Test ℓ L → L} (hf : f ∈ K.form k) (hg : g ∈ K.form k)
    (h : K.qExp k ⟨f, hf⟩ = K.qExp k ⟨g, hg⟩) : f = g :=
  congrArg Subtype.val (K.qExp_injective k h)

/-- The `q`-expansion of a product, with a weight `c = a + b`. -/
lemma qExp_mul_of_eq {a b c : ℤ} (h : a + b = c) {f g : Test ℓ L → L} (hf : f ∈ K.form a)
    (hg : g ∈ K.form b) (hfg : f * g ∈ K.form c) :
    K.qExp c ⟨f * g, hfg⟩ = K.qExp a ⟨f, hf⟩ * K.qExp b ⟨g, hg⟩ := by
  rw [← K.qExp_mul ⟨f, hf⟩ ⟨g, hg⟩]
  exact K.qExp_congr h.symm rfl _ _

lemma mul_mem_of_eq {a b c : ℤ} (h : a + b = c) {f g : Test ℓ L → L} (hf : f ∈ K.form a)
    (hg : g ∈ K.form b) : f * g ∈ K.form c :=
  K.mem_form_of_eq h (K.mul_mem hf hg)

lemma pow_mem {k : ℤ} {f : Test ℓ L → L} (hf : f ∈ K.form k) (n : ℕ) :
    f ^ n ∈ K.form (n * k) := by
  induction n with
  | zero => simpa using K.one_mem
  | succ n ih =>
    rw [pow_succ]
    exact K.mul_mem_of_eq (by push_cast; ring) ih hf

lemma qExp_pow {k : ℤ} {f : Test ℓ L → L} (hf : f ∈ K.form k) (n : ℕ) :
    K.qExp (n * k) ⟨f ^ n, K.pow_mem hf n⟩ = K.qExp k ⟨f, hf⟩ ^ n := by
  induction n with
  | zero =>
    exact (K.qExp_congr (by simp) (pow_zero f) _ K.one_mem).trans (by rw [K.qExp_one, pow_zero])
  | succ n ih =>
    have hmem : f ^ n * f ∈ K.form (((n + 1 : ℕ) : ℤ) * k) := by
      rw [← pow_succ]; exact K.pow_mem hf (n + 1)
    refine (K.qExp_congr rfl (pow_succ f n) _ hmem).trans ?_
    rw [K.qExp_mul_of_eq (show (n : ℤ) * k + k = ((n + 1 : ℕ) : ℤ) * k by push_cast; ring)
      (K.pow_mem hf n) hf hmem, ih, pow_succ]

lemma qExp_smul {k : ℤ} (c : L) {f : Test ℓ L → L} (hf : f ∈ K.form k) :
    K.qExp k ⟨c • f, (K.form k).smul_mem c hf⟩ = c • K.qExp k ⟨f, hf⟩ := by
  rw [← map_smul]
  rfl

lemma qExp_add {k : ℤ} {f g : Test ℓ L → L} (hf : f ∈ K.form k) (hg : g ∈ K.form k) :
    K.qExp k ⟨f + g, (K.form k).add_mem hf hg⟩ = K.qExp k ⟨f, hf⟩ + K.qExp k ⟨g, hg⟩ := by
  rw [← map_add]
  rfl

lemma qExp_sub {k : ℤ} {f g : Test ℓ L → L} (hf : f ∈ K.form k) (hg : g ∈ K.form k) :
    K.qExp k ⟨f - g, (K.form k).sub_mem hf hg⟩ = K.qExp k ⟨f, hf⟩ - K.qExp k ⟨g, hg⟩ := by
  rw [← map_sub]
  rfl

lemma discriminant_pow_mem (t : ℕ) : discriminantRule ^ t ∈ K.form (12 * t) :=
  K.mem_form_of_eq (by ring) (K.pow_mem K.discriminant_mem t)

/-- The rule `Δ^{[ℓ]} = ℓ⁻¹² Δ(E / C, ω')` is a form of weight `12`. -/
lemma normalizedVeluDiscriminant_mem :
    (fun T ↦ ((ℓ : L) ^ 12)⁻¹ * veluDiscriminantRule T) ∈ K.form 12 :=
  (K.form 12).smul_mem ((ℓ : L) ^ 12)⁻¹ K.veluDiscriminant_mem

/-- The `q`-expansion of `Δ^{[ℓ]} = ℓ⁻¹² Δ(E / C, ω')` is `Δ(q^ℓ)`. -/
lemma qExp_normalizedVeluDiscriminant (hℓ : (ℓ : L) ≠ 0) :
    K.qExp 12 ⟨_, K.normalizedVeluDiscriminant_mem⟩ =
      expandSeries ℓ (PowerSeries.map (Int.castRingHom L) LevelOne.integralDiscriminant) := by
  rw [show (⟨_, K.normalizedVeluDiscriminant_mem⟩ : K.form 12) =
      ((ℓ : L) ^ 12)⁻¹ • ⟨_, K.veluDiscriminant_mem⟩ from rfl,
    map_smul, K.qExp_veluDiscriminant hℓ, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hℓ), one_smul]

/-- The reduction of a classical form is the Katz form with the reduced `q`-expansion. -/
lemma reduce_eq_of_qExp_eq {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 ℓ) k)
    (G : PowerSeries ℚ) (hG : G.IsPIntegral p)
    (hfG : PowerSeries.map (Rat.castHom ℂ) G = UpperHalfPlane.qExpansion 1 f)
    {g : Test ℓ L → L} (hg : g ∈ K.form k) (h : K.qExp k ⟨g, hg⟩ = G.reduceTo L) :
    (K.reduce f G hG hfG).1 = g := by
  have := K.qExp_reduce f G hG hfG
  exact K.eq_of_qExp_eq (K.reduce f G hG hfG).2 hg (this.trans h.symm)

end KatzForms

namespace LevelOne

open KatzForms

variable {p ℓ : ℕ} [Fact p.Prime] {L : Type*} [Field L] [DecidableEq L] (K : KatzForms p ℓ L)
  {k : ℤ}

lemma reductionAtLevel_eq (f : ModularForm 𝒮ℒ k) (G : PowerSeries ℤ)
    (hG : IsIntegralQExpansion G f) :
    reductionAtLevel K f G hG =
      K.reduce (LevelTwoForms.ofLevelOne ℓ f) (PowerSeries.map (Int.castRingHom ℚ) G)
        (PowerSeries.isPIntegral_map_intCast p G)
        (map_map_intCast_eq_qExpansion_ofLevelOne ℓ hG) := by
  rw [reductionAtLevel]

lemma levelRaiseReduction_eq [NeZero ℓ] (f : ModularForm 𝒮ℒ k) (G : PowerSeries ℤ)
    (hG : IsIntegralQExpansion G f) :
    levelRaiseReduction K f G hG =
      K.reduce (LevelTwoForms.levelRaise ℓ f)
        (PowerSeries.map (Int.castRingHom ℚ) (expandSeries ℓ G))
        (PowerSeries.isPIntegral_map_intCast p _)
        (map_map_intCast_eq_qExpansion_levelRaise ℓ hG) := by
  rw [levelRaiseReduction]

/-- The `q`-expansion of `ι f̄` is the reduction of the `q`-expansion of `f`. -/
lemma qExp_reductionAtLevel (f : ModularForm 𝒮ℒ k) (G : PowerSeries ℤ)
    (hG : IsIntegralQExpansion G f) :
    K.qExp k (reductionAtLevel K f G hG) = PowerSeries.map (Int.castRingHom L) G := by
  rw [reductionAtLevel_eq, K.qExp_reduce, PowerSeries.reduceTo_map_intCast]

/-- The `q`-expansion of `V_ℓ f̄` is `Ḡ(q^ℓ)`. -/
lemma qExp_levelRaiseReduction [NeZero ℓ] (f : ModularForm 𝒮ℒ k) (G : PowerSeries ℤ)
    (hG : IsIntegralQExpansion G f) :
    K.qExp k (levelRaiseReduction K f G hG) =
      expandSeries ℓ (PowerSeries.map (Int.castRingHom L) G) := by
  rw [levelRaiseReduction_eq, K.qExp_reduce, PowerSeries.reduceTo_map_intCast, map_expandSeries]

end LevelOne
