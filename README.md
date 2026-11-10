# Modular forms for chromatic homotopy: supersingular congruences

**Assembled by AxiomProver.**

Lean formalization of Ken Ono's *Modular forms for chromatic homotopy: supersingular congruences*.

The formalization covers the manuscript's three main theorems, for every prime `p ≥ 5`.
Theorem 1.1, Larson's conjecture, says that the pure power `Δ^t` satisfies Behrens' conditions
(C1)–(C4) for an admissible index `j ≤ p^n` and fails (C4) for `j > p^n`; condition (C4) is read in
the ring of Katz modular forms on `Γ₀(ℓ)` for every prime `ℓ ≠ p`. Its parts are
`LevelOne.discriminantPow_satisfiesBehrensConditions` and
`LevelOne.not_behrensC4_discriminantPow_of_isAdmissible`, and the conjecture itself is
`LevelOne.discriminantPow_satisfiesBehrensConditions_iff`. Theorem 1.2, supersingular containment,
is `Gamma0.Pair.veluRatio_pow_eq_one`, stated through Vélu's quotient of a supersingular curve,
and `KatzForms.containment`, stated for the modular function `R_ℓ = V_ℓ(Δ) / Δ`. Theorem 1.3, the rationality of supersingular
discriminants, is `WeierstrassCurve.discriminant_pow_of_isDeuringModelOver_eta`, by the
manuscript's eta-power proof, and `WeierstrassCurve.Δ_pow_of_isDeuringModelOver`, by its deduction
from González's theorem.

All of the manuscript's arguments for its main theorems are formalized, apart from one step of
Lemma 4.1 carried by an interface field. The proofs rely on two kinds of input, both taken as
explicit hypotheses rather than assumed. The first is the results the manuscript cites from the
literature, bundled as `CitedResults`. The second is interface structures for objects that
Mathlib does not yet have: Katz modular forms, modular curves and the Weil pairing. Both are
stated and documented in
[`SupersingularCongruences/External.lean`](SupersingularCongruences/External.lean). That file
also lists the few statements that Mathlib cannot yet express, none of which the main theorems
use: Lemma 4.2, the curve-level forms of Lemmas 3.2 and 3.3, parts of Remark 5.2, and the
homotopy-theoretic reading of the §2.1 example.

Using the pinned Lean and mathlib versions, build with:

```
lake exe cache get
lake build
```

Bibliographic references are collected in [references.bib](references.bib).
