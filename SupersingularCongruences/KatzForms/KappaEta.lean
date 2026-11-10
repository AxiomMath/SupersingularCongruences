/-
Assembled by AxiomProver.
-/
module

public import SupersingularCongruences.KatzForms.EtaKappa
public import SupersingularCongruences.ModularForms.EtaPower

/-!
# Theorem 1.3 by eta powers

The manuscript's eta-power proof of Theorem 1.3, with the eta powers `h₃ = η⁸ ∈ M₄(Γ(3))` and
`h₄ = η⁶ ∈ M₃(Γ(4))` of Proposition 4.5(a) (`EtaPower.etaPowerForm`) inserted into
`WeierstrassCurve.discriminant_pow_of_isDeuringModelOver_of_etaPowers`. The only remaining inputs
are the cited facts on the Weil pairing and on algebraic modular forms of levels `3` and `4`
(`WeilPairing`, `LevelNForms`).
-/

public section

namespace WeierstrassCurve

variable {L : Type*} [Field L] [IsAlgClosed L] [DecidableEq L] {p : ℕ} [CharP L p]

/-- **Theorem 1.3** (rationality of supersingular discriminants), eta-power proof
(manuscript, Section 4.4). Let `p ≥ 5`, let `L` be an algebraically closed field of
characteristic `p`, and let `E / 𝔽_{p²}` be a supersingular curve with `π_E = [-p]` (a Deuring
model, `W.IsDeuringModelOver p`). For every nonzero `𝔽_{p²}`-rational invariant differential
`ω = c · dx / (2y)` (`c ^ (p ^ 2) = c`),
`κ(E) = Δ(E, ω) ^ ((p² - 1) / 12) = (-1) ^ ((p + 1) / 2)`.

The cited inputs are the Weil pairings `e₃`, `e₄` and the theories `F₃`, `F₄` of algebraic modular
forms of levels `3` and `4` over `L` for primitive roots of unity `ζ₃`, `ζ₄`. -/
theorem discriminant_pow_of_isDeuringModelOver_eta (hp : p.Prime) (hp5 : 5 ≤ p)
    (W : WeierstrassCurve L) [W.IsElliptic] [W.IsShortNF] (hD : W.IsDeuringModelOver p)
    (e₃ : WeilPairing 3 L) {ζ₃ : L} (hζ₃ : IsPrimitiveRoot ζ₃ 3) (F₃ : LevelNForms 3 L e₃ ζ₃)
    (e₄ : WeilPairing 4 L) {ζ₄ : L} (hζ₄ : IsPrimitiveRoot ζ₄ 4) (F₄ : LevelNForms 4 L e₄ ζ₄)
    (c : Lˣ) (hc : (c : L) ^ p ^ 2 = c) :
    (((c : L) ^ 12)⁻¹ * W.Δ) ^ ((p ^ 2 - 1) / 12) = (-1) ^ ((p + 1) / 2) :=
  discriminant_pow_of_isDeuringModelOver_of_etaPowers hp hp5 W hD e₃ hζ₃ F₃
    (EtaPower.etaPowerForm 3 (Or.inl rfl)) (EtaPower.qSeries 3)
    (EtaPower.qExpansion_etaPowerForm 3 (Or.inl rfl))
    (EtaPower.etaPowerForm_pow_apply 3 (Or.inl rfl)) e₄ hζ₄ F₄
    (EtaPower.etaPowerForm 4 (Or.inr rfl)) (EtaPower.qSeries 4)
    (EtaPower.qExpansion_etaPowerForm 4 (Or.inr rfl))
    (EtaPower.etaPowerForm_pow_apply 4 (Or.inr rfl)) c hc

end WeierstrassCurve
