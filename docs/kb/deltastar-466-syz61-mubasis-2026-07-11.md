# SYZ61 — syzygy kernel of a coprime triple is free of rank exactly 2 (2026-07-11)

Issue #466, rate-1/2 `SylvesterInjective` residual chain (SYZ38 → G172 → SYZ44 → SYZ57 → SYZ60).

## What landed

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ61MuBasisExistence.lean`, axiom-clean
(`propext, Classical.choice, Quot.sound` only; no `sorry`, no `native_decide`).

Fix a field `K` and the syzygy evaluation map of a triple `(f,g,h) : K[X]³`:

```
noncomputable def syzygyMap (f g h : K[X]) : (Fin 3 → K[X]) →ₗ[K[X]] K[X] where
  toFun r := f * r 0 + g * r 1 + h * r 2
```

Landed theorems (verbatim statements):

- `syzygyMap_surjective {f g h : K[X]} (hfg : IsCoprime f g) (hfh : IsCoprime f h) :`
  `Function.Surjective (syzygyMap f g h)` — from SYZ57's `exists_triple_repr` (Bézout seed).
- `finrank_syzygyKernel {f g h : K[X]} (hfg : IsCoprime f g) (hfh : IsCoprime f h) :`
  `Module.finrank K[X] (LinearMap.ker (syzygyMap f g h)) = 2`
- `rank_syzygyKernel {f g h : K[X]} (hfg : IsCoprime f g) (hfh : IsCoprime f h) :`
  `Module.rank K[X] (LinearMap.ker (syzygyMap f g h)) = 2`
- `syzygyKernel_free_rank_two {f g h : K[X]} (hfg : IsCoprime f g) (hfh : IsCoprime f h) :`
  `Module.Free K[X] (LinearMap.ker (syzygyMap f g h)) ∧`
  `Module.finrank K[X] (LinearMap.ker (syzygyMap f g h)) = 2`

## Proof route

Rank–nullity over the commutative **domain** `K[X]` (`IsDomain.hasRankNullity`,
`LinearMap.rank_eq_of_surjective`):
`rank (Fin 3 → K[X]) = rank K[X] + rank (ker φ)`, i.e. `3 = 1 + rank (ker φ)`
(`rank_fin_fun`, `rank_self`). Both summands are finite (`rank_lt_aleph0`), so applying
`Cardinal.toNat` (`toNat_add`, `toNat_natCast`) gives `3 = 1 + finrank (ker φ)`, hence
`finrank (ker φ) = 2`. Freeness is SYZ60's `kernel_free` (Smith normal form / PID structure).

## Honest status — MuBasisWindowIso / RankNullity / degree-sum law

This discharges part **(a) rank exactly 2** of the SYZ44/SYZ60 two-ramp decomposition,
UNCONDITIONALLY. It is the coprimality-driven rank drop that SYZ60 had folded into the
`MuBasisWindowIso` residual (SYZ60 only had *free ⇒ rank ≤ 3*).

- **`SYZ60.MuBasisWindowIso`: still OPEN**, but reduced from "(a)-rank-drop + (b)" to **(b) alone**
  — the *graded* μ-basis window count. Formalizing (b) needs product-degree grading on `K[X]³`,
  leading-coefficient vectors, and the CSC leading-vector exchange argument; Mathlib has no graded
  μ-basis for coprime triples. NOT attempted here (genuinely a large graded-module development).
- **`SYZ44.RankNullity`: still OPEN.** SYZ57 landed the ungraded Bézout core (image contains 1);
  SYZ61 landed the ungraded rank count (nullity = 2). The remaining gap is the *degree-controlled*
  balanced-window surjectivity onto `{deg ≤ D}` plus the windowed-finrank bookkeeping — not in
  Mathlib.
- **Degree-sum law `δ₁ + δ₂ = a+b+c` (`SYZ44.degree_sum_of_hilbert`): NOT yet unconditional.**
  It remains conditional on `RankNullity ∧ TwoRamp`. SYZ61 removes the rank-drop hypothesis from
  the (a) side but does not close the graded/degree-controlled halves.

No δ* closure. CORE remains OPEN / ON-BGK.

## Key Mathlib API used

`LinearMap.rank_eq_of_surjective`, `IsDomain.hasRankNullity`, `rank_fin_fun`, `rank_self`,
`rank_lt_aleph0`, `Cardinal.toNat_add`, `Cardinal.toNat_natCast`, `Module.finrank_eq_rank`,
`Submodule.smithNormalForm` (via SYZ60.kernel_free).
