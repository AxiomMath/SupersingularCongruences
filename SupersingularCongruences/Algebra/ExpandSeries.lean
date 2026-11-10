/-
Assembled by AxiomProver.
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The substitution `q ↦ q^ℓ` on power series

`Gamma0.expandSeries ℓ G` is the series `G(q^ℓ) = ∑ₙ aₙ q^{ℓ n}` for `G = ∑ₙ aₙ qⁿ`. It is the
effect of the operator `V_ℓ` on `q`-expansions, and the base change `q ↦ q^ℓ` of the Tate
curve. For `ℓ ≠ 0` it is a ring homomorphism (`Gamma0.expandRingHom`).
-/

public section

open PowerSeries

namespace Gamma0

/-- The series `G(q^ℓ)`: `∑ₙ G.coeff n · X ^ (ℓ n)`. -/
noncomputable def expandSeries {R : Type*} [Semiring R] (ℓ : ℕ) (G : PowerSeries R) :
    PowerSeries R :=
  PowerSeries.mk fun n ↦ if ℓ ∣ n then G.coeff (n / ℓ) else 0

lemma coeff_expandSeries {R : Type*} [Semiring R] (ℓ : ℕ) (G : PowerSeries R) (n : ℕ) :
    (expandSeries ℓ G).coeff n = if ℓ ∣ n then G.coeff (n / ℓ) else 0 :=
  PowerSeries.coeff_mk _ _

variable {R S : Type*} [CommRing R] [CommRing S]

lemma map_expandSeries (f : R →+* S) (ℓ : ℕ) (G : PowerSeries R) :
    PowerSeries.map f (expandSeries ℓ G) = expandSeries ℓ (PowerSeries.map f G) := by
  ext n
  simp only [coeff_map, coeff_expandSeries]
  split_ifs <;> simp

lemma expandSeries_one {ℓ : ℕ} (hℓ : ℓ ≠ 0) : expandSeries ℓ (1 : PowerSeries R) = 1 := by
  ext n
  simp only [coeff_expandSeries, coeff_one]
  by_cases hn : n = 0
  · subst hn; simp
  · by_cases hd : ℓ ∣ n
    · have : n / ℓ ≠ 0 := by
        obtain ⟨m, rfl⟩ := hd
        rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ)]
        rintro rfl
        simp at hn
      simp [hd, this, hn]
    · simp [hd, hn]

lemma expandSeries_mul {ℓ : ℕ} (hℓ : ℓ ≠ 0) (A B : PowerSeries R) :
    expandSeries ℓ (A * B) = expandSeries ℓ A * expandSeries ℓ B := by
  ext n
  rw [coeff_mul, coeff_expandSeries]
  split_ifs with hd
  · obtain ⟨m, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ), coeff_mul]
    let e : ℕ × ℕ ↪ ℕ × ℕ :=
      ⟨fun x ↦ (ℓ * x.1, ℓ * x.2), fun x y h ↦ by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hℓ) h.1)
          (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hℓ) h.2)⟩
    have hsub : (Finset.antidiagonal m).map e ⊆ Finset.antidiagonal (ℓ * m) := by
      intro x hx
      simp only [Finset.mem_map, Finset.mem_antidiagonal] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      change ℓ * y.1 + ℓ * y.2 = ℓ * m
      rw [← mul_add, hy]
    rw [← Finset.sum_subset hsub, Finset.sum_map]
    · refine Finset.sum_congr rfl fun x _ ↦ ?_
      change _ = (expandSeries ℓ A).coeff (ℓ * x.1) * (expandSeries ℓ B).coeff (ℓ * x.2)
      simp [coeff_expandSeries, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ)]
    · intro x hx hxn
      simp only [coeff_expandSeries]
      split_ifs with h1 h2
      · exfalso
        apply hxn
        obtain ⟨a, ha⟩ := h1
        obtain ⟨b, hb⟩ := h2
        rw [Finset.mem_antidiagonal] at hx
        refine Finset.mem_map.mpr ⟨(a, b), ?_, ?_⟩
        · rw [Finset.mem_antidiagonal]
          apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hℓ)
          rw [mul_add, ← ha, ← hb, hx]
        · exact Prod.ext ha.symm hb.symm
      all_goals simp
  · symm
    refine Finset.sum_eq_zero fun x hx ↦ ?_
    rw [Finset.mem_antidiagonal] at hx
    simp only [coeff_expandSeries]
    split_ifs with h1 h2
    · exact absurd (hx ▸ dvd_add h1 h2) hd
    all_goals simp

lemma expandSeries_add (ℓ : ℕ) (A B : PowerSeries R) :
    expandSeries ℓ (A + B) = expandSeries ℓ A + expandSeries ℓ B := by
  ext n
  simp only [coeff_expandSeries, map_add]
  split_ifs <;> simp

lemma expandSeries_pow {ℓ : ℕ} (hℓ : ℓ ≠ 0) (A : PowerSeries R) (t : ℕ) :
    expandSeries ℓ (A ^ t) = expandSeries ℓ A ^ t := by
  induction t with
  | zero => simpa using expandSeries_one hℓ
  | succ t ih => rw [pow_succ, expandSeries_mul hℓ, ih, pow_succ]

lemma expandSeries_smul (ℓ : ℕ) (c : R) (A : PowerSeries R) :
    expandSeries ℓ (c • A) = c • expandSeries ℓ A := by
  ext n
  simp only [coeff_expandSeries, coeff_smul]
  split_ifs <;> simp

/-- The substitution `q ↦ q^ℓ`, `ℓ ≠ 0`, as a ring homomorphism of power series. -/
@[expose] noncomputable def expandRingHom {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    PowerSeries R →+* PowerSeries R where
  toFun := expandSeries ℓ
  map_one' := expandSeries_one hℓ
  map_mul' := expandSeries_mul hℓ
  map_zero' := by ext n; simp [coeff_expandSeries]
  map_add' := expandSeries_add ℓ

@[simp] lemma expandRingHom_apply {ℓ : ℕ} (hℓ : ℓ ≠ 0) (A : PowerSeries R) :
    expandRingHom hℓ A = expandSeries ℓ A := rfl

end Gamma0
