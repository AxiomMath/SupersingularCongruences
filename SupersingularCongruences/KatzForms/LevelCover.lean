/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.KatzForms.Basic
public import Mathlib.Data.ENat.Basic

/-!
# A rigid level-`N` cover of `X₀(ℓ)`

The proof of Proposition 5.4 of the manuscript divides by the Hasse invariant on the compactified
moduli curve `Ȳ` over `L` of elliptic curves with a `Γ₀(ℓ)`-structure and a full level-`N`
structure, `N ∈ {3, 4}` prime to `pℓ`. This moduli problem is representable and rigid, `Ȳ` is a
smooth proper curve over `L` [katz-mazur, Corollaries 4.7.1–4.7.2 and 10.9.2], and the finite group
`Q = GL₂(ℤ / N)`, of order prime to `p`, acts on `Ȳ` by changing the level-`N` structure; the
`Q`-invariant sections of `ω^{⊗k}` on `Ȳ` are the Katz forms of weight `k` on `Γ₀(ℓ)`
[katz1973, Section 1.2], [katz-mazur, Theorem 7.1.3].

`LevelCover K` bundles the facts about `Ȳ` used in the manuscript. A section of `ω^{⊗k}` is
represented by its values `s y λ` at the non-cuspidal points `y` and the differentials
`λ · ω_{E_y}`, where `(E_y, C_y) = pair y` is a representative of the image of `y` in `X₀(ℓ)`.
The order of vanishing `ord s z ∈ ℕ∞` is defined at non-cuspidal points and cusps `z`.
-/

public section

open Gamma0 CongruenceSubgroup
open scoped MatrixGroups

/-- **The level-`N` cover `Ȳ → X₀(ℓ)`** (cited facts); see the module docstring. -/
structure LevelCover {p ℓ : ℕ} {L : Type*} [Field L] [DecidableEq L] (K : KatzForms p ℓ L) where
  /-- An index type for the non-cuspidal points of `Ȳ` over `L`: each element stands for a
  rigidified representative (a pair `(E, C)` with a level-`N` structure), not for a point of the
  scheme `Ȳ` itself; `pair` forgets the level structure. The type lives in `Type` (universe `0`),
  which suffices for the uses here and keeps the interface satisfiable for any `L`. -/
  Pt : Type
  /-- A representative `(E, C)` of the image of a point in `X₀(ℓ)`. -/
  pair : Pt → Pair ℓ L
  /-- Every pair `(E, C)` admits a full level-`N` structure, since `E[N] ≅ (ℤ / N)²` for `p ∤ N`
  [silverman-aec, Corollary III.6.4(b)]. -/
  exists_pair_eq (P : Pair ℓ L) : ∃ y, pair y = P
  /-- An index type (in `Type`, universe `0`) for the cusps of `Ȳ`. -/
  Cusp : Type
  /-- The sections of `ω^{⊗k}` on `Ȳ`. -/
  sec : ℤ → Submodule L (Pt → Lˣ → L)
  /-- Pulling back a Katz form on `Γ₀(ℓ)` gives a section. -/
  pullback_mem {k : ℤ} {f : Test ℓ L → L} (hf : f ∈ K.form k) :
    (fun y c ↦ f ⟨pair y, c⟩) ∈ sec k
  /-- Products of sections are sections. -/
  mul_mem {a b : ℤ} {s t : Pt → Lˣ → L} : s ∈ sec a → t ∈ sec b → s * t ∈ sec (a + b)
  /-- The group `Q` of changes of level-`N` structure. -/
  Q : Type
  [group : Group Q]
  /-- The action of `Q` on the points of `Ȳ`, over `X₀(ℓ)`. -/
  act : Q → Pt → Pt
  pair_act (q : Q) (y : Pt) : pair (act q y) = pair y
  /-- `Q` acts on sections by pullback. -/
  act_mem {k : ℤ} {s : Pt → Lˣ → L} (hs : s ∈ sec k) (q : Q) :
    (fun y c ↦ s (act q y) c) ∈ sec k
  /-- `Q`-invariant sections of `ω^{⊗k}` descend to Katz forms of weight `k` on `Γ₀(ℓ)`
  [katz1973, Section 1.2], [katz-mazur, Theorem 7.1.3]. -/
  descend {k : ℤ} {s : Pt → Lˣ → L} (hs : s ∈ sec k) (hinv : ∀ q y c, s (act q y) c = s y c) :
    ∃ f ∈ K.form k, ∀ y c, s y c = f ⟨pair y, c⟩
  /-- The order of vanishing of a section at a point or cusp of `Ȳ` (`⊤` where it vanishes
  identically near the point). This field and those from `ord_mul` to `exists_eq_mul` are the
  properties of orders of vanishing on a smooth curve [hartshorne1977, Section II.6]. -/
  ord : (Pt → Lˣ → L) → Pt ⊕ Cusp → ℕ∞
  ord_mul {a b : ℤ} {s t : Pt → Lˣ → L} (hs : s ∈ sec a) (ht : t ∈ sec b) (z : Pt ⊕ Cusp) :
    ord (s * t) z = ord s z + ord t z
  /-- A section vanishes at a non-cuspidal point iff its order there is positive. -/
  ord_pos_iff {k : ℤ} {s : Pt → Lˣ → L} (hs : s ∈ sec k) (y : Pt) :
    0 < ord s (Sum.inl y) ↔ s y 1 = 0
  /-- The zero section has infinite order everywhere. -/
  ord_zero (z : Pt ⊕ Cusp) : ord 0 z = ⊤
  /-- A section with infinite order everywhere is zero. -/
  eq_zero_of_ord_eq_top {k : ℤ} {s : Pt → Lˣ → L} (hs : s ∈ sec k)
    (h : ∀ z, ord s z = ⊤) : s = 0
  /-- The pullback of a nonzero Katz form on `Γ₀(ℓ)` is nonzero on every component of `Ȳ`
  (`Q` permutes the components transitively). -/
  ord_pullback_ne_top {k : ℤ} {f : Test ℓ L → L} (hf : f ∈ K.form k) (hf0 : f ≠ 0)
    (z : Pt ⊕ Cusp) : ord (fun y c ↦ f ⟨pair y, c⟩) z ≠ ⊤
  /-- Division on a smooth curve: if `ord a ≤ ord g` everywhere and `a` has finite order
  everywhere, then `g / a` is a section. -/
  exists_eq_mul {a b : ℤ} {s g : Pt → Lˣ → L} (hs : s ∈ sec a) (hg : g ∈ sec b)
    (hfin : ∀ z, ord s z ≠ ⊤) (hle : ∀ z, ord s z ≤ ord g z) :
    ∃ h ∈ sec (b - a), g = s * h
  /-- **Igusa's theorem**: the zeros of the Hasse invariant on `Ȳ` are simple [igusa1958],
  [katz-mazur, Theorem 12.4.3]. -/
  ord_hasse_le_one (y : Pt) : ord (fun y c ↦ hasseRule p ⟨pair y, c⟩) (Sum.inl y) ≤ 1
  /-- At every cusp, the expansion of (the pullback of) the reduction of a level-one form is its
  `q`-expansion at `∞` (in a power of `q^{1/N}`): a level-one form whose reduced `q`-expansion has
  nonzero constant term does not vanish at any cusp [katz1973, Sections 1.2 and 1.4]. This is the
  cusp half of the manuscript's Lemma 2.1(b), which is therefore only partly formalized. -/
  ord_cusp_eq_zero {k : ℤ} (g : ModularForm 𝒮ℒ k) (G : PowerSeries ℚ) (hG : G.IsPIntegral p)
    (hgG : PowerSeries.map (Rat.castHom ℂ) G =
      UpperHalfPlane.qExpansion 1 (LevelTwoForms.ofLevelOne ℓ g))
    (hg : PowerSeries.constantCoeff (G.reduceTo L) ≠ 0) (c : Cusp) :
    ord (fun y c ↦ (K.reduce (LevelTwoForms.ofLevelOne ℓ g) G hG hgG).1 ⟨pair y, c⟩)
      (Sum.inr c) = 0
