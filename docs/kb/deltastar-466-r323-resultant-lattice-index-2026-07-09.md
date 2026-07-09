# #466 R323 (Fable): the determinant identification — recurrence-lattice index = |resultant|

Date: 2026-07-09 · Lane file: `Frontier/_R323ResultantRecurrenceLatticeIndex.lean`

## What was open

R321 (`_R321DyadicSaturationBridge.lean` + kb r321–r322 note) proved the abstract dyadic
saturation theorem conditional on "the standard determinant/resultant identification": that
for a relation polynomial `f` in `ℤ[x]/(x^m+1)` (`m = 2^k`), the recurrence lattice
`f·ℤ[x]/(x^m+1)` has index `|Res(x^m+1, f)|`. R315 built the resultant annihilator but only
its nonvanishing/divisibility/height faces, never the lattice-index reading. Mathlib has no
norm↔resultant bridge, and `Ideal.absNorm` demands `IsDedekindDomain`, which it cannot see
for `ℤ[x]/(x^m+1)` without the cyclotomic ring-of-integers transfer.

## What landed (all axiom-clean, `lake build` verified)

1. `nat_card_quot_span_singleton` — **Dedekind-free `absNorm_span_singleton`**: for any
   domain `S` free and finite over `ℤ` and `r ≠ 0`,
   `#(S ⧸ (r)) = |Norm_ℤ(r)|`, routed through `Submodule.natAbs_det_equiv` and
   `Ideal.basisSpanSingleton` only.
2. `norm_toQ` — the ℤ-norm on `AdjoinRoot (x^m+1 : ℤ[X])` casts to the ℚ-norm along the
   root-preserving hom `toQ` (matching power bases; `modByMonic` commutes with `map`;
   `Basis.reindex` across the degree cast).
3. `normQ_aeval_eq_prod` — `Norm_ℚ(P(θ)) = ∏ P(ζ)` over the roots of `x^m+1` in
   `AlgebraicClosure ℚ` (embeddings ↔ roots via `PowerBasis.liftEquiv'`; separability from
   char 0; nodup roots).
4. `patternResultant_cast_eq_prod` — `Res(x^m+1, P)` casts to the same product
   (`resultant_map_map` + `resultant_eq_prod_eval`, monic so no leading-coefficient factor).
5. `norm_mk_eq_patternResultant` — **the exact identity, no sign**:
   `Norm_ℤ(P mod x^m+1) = Res_{m, deg P}(x^m+1, P)` (both sides cast injectively to the same
   product in char 0).
6. `nat_card_quot_span_mk_eq_patternResultant` — **the target**: for `¬(x^m+1) ∣ P`,
   `#(ℤ[x]/(x^m+1) ⧸ (P)) = |Res(x^m+1, P)|.natAbs`.

## Consequence for the prize route (weld R315 × R321)

Every realized kernel relation `d` (R314/R315: height ≤ 2r, `evalVec(g,d) = 0`, `p ∣ N(d)`)
now has a machine-checked lattice meaning: the recurrence lattice `P_d·ℤ[x]/(x^m+1)` has
index exactly `|N(d)|`. The R321/R322 census fact `|N(d)|/p ∈ {2,4,8}` on all 92 in-window
`n=32` K-bad primes therefore says — with no "standard identification" hypothesis left —
that the evaluation kernel sits above one short recurrence lattice with dyadic quotient
(`8·kernel ⊆ recurrenceLattice`, R321's unconditional bridge, now fully fed).

**Remaining open input for the R321 `PrimitiveSaturationDichotomy`:** only the uniform
principal-lattice return-probability bound (genuinely open; after Fourier duality it can
collapse back to the Paley spectrum — any proof must use the short/banded structure of `f`).

## Validation

`lake env lean` clean (0 errors, 0 warnings); real `lake build` of the module passed;
axiom audit `[propext, Classical.choice, Quot.sound]` on all six theorems.
