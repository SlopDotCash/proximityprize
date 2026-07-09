# #407 — Gauss-phase-flatness-algebra: the index-parity separation (the algebraic reason the 2-power escape fails)

> Session 2026-06-13. Angle: **gauss-phase-flatness-algebra** (attack the Gauss-phase DFT flatness
> directly via the explicit algebra of `a_j = τ(ψ^j)/√q`). Honesty contract in force: **no closure**.
> All numerics from real probes (`/tmp/gpf*.py`, machine-exact to 1e-13); one axiom-clean Lean brick.

## 0. The object (corrected prize regime)

`F_p`, `n = 2^a` the **maximal** dyadic subgroup (`n` = full 2-part of `p−1`), `m = (p−1)/n`,
`ψ` a mult char of order `m`. House `B = max_{b≠0}‖∑_{x∈μ_n} e_p(bx)‖`. Phase sequence
`a_j = τ(ψ^j)/√p` (unimodular for `m ∤ j`; `|τ_j| = √p` by Weil, proven). The prize floor
`δ* = average ⟺` flatness of the **m-DFT of `(a_j)`**: `max_b‖∑_j w_b^{-j} a_j‖ ≤ C√(m log m)`.

## 1. What is rigorously established this session

**(R1) The DFT self-duality is exact and involutive (verified 1e-15).** The m-DFT of the Gauss-sum
sequence `(τ_j)` equals `m·(η_b)` (the coset/period sequence), and vice versa: `(τ_j) ↔ (η_b)` are a
DFT pair. So `B = (√p/m)·max_b‖∑_{j≠0} w_b^{-j} a_j‖` up to the `j=0` correction. Iterating the DFT
just toggles `τ↔η`; it yields no *extra* structure for the sup-norm (only Parseval/L² transfers).
This is the precise "Gauss-sum-of-Gauss-sums" — but it is a self-inverse, not a self-improvement.

**(R2) Parseval two-sided pin (provable lower bound).** `∑_b|η_b|² = (1/m)∑_j|τ_j|² = ((m−1)p+1)/m`
⟹ `L²(η) = √n·(1−o(1))`, so **`B ≥ √n` rigorously**. Empirically `B/L² ∈ [1.27, 2.77]` over 36
prize-shaped primes (n=8,16,32): this ratio IS the log-factor gap. `B/√(n ln m) ∈ [0.78, 1.54]`,
median 1.20 — the random-model constant, consistent across n.

**(R3) The Jacobi cocycle (exact, 0 violations).** `a_i a_j = (J(ψ^i,ψ^j)/√p)·a_{i+j}` with
`|J/√p| = 1`: `(a_j)` is a **projective representation of ℤ/m** with unimodular structure constants
`b_{i,j} = J_{i,j}/√p ∈ H²(ℤ/m, U(1))`. Flatness of the DFT would follow if `[b]` were a *coboundary*
(then `a_j` = genuine character × chirp ⟹ Gauss-sum DFT = √m, no log). It is **not** a coboundary.

**(R4) The chirp dichotomy (the quantitative obstruction).** `(a_j)` is provably **not a quadratic
chirp**: the 2nd-order phase ratio has circular variance ≈ 0.49–0.81 (chirp = 0). Hence the DFT
**cannot** reach the perfect `√m` (no-log) bound; `√(m log m)` (random model) is the right target, and
`B ≈ √(n log m)` (not `√n`) is forced from below. This *explains* the measured `C ≈ 1` law.

**(R5) THE NEW STRUCTURAL FINDING — the index-parity separation (Lean, axiom-clean).** The Hasse–
Davenport order-2 **duplication** `a_j·a_{j+m/2} = (unit)·a_{2j}·a_{m/2}` (verified 1e-13) — the only
algebraic lever by which the *dyadic* structure of `μ_n` could special-case the phase DFT toward
flatness — requires an **order-2 character inside the index group ℤ/m**, i.e. `m` even. But in the
prize regime `n = 2^a` absorbs the **entire** 2-part of `p−1`, so **`m = (p−1)/n` is ODD**. Therefore:
- the doubling map `x ↦ 2x` on ℤ/m is a **bijection** (not 2-to-1), so H–D *permutes* `(a_j)` rather
  than folding it — **no dyadic self-reduction on the index side**;
- the 2-power lives entirely on the *subgroup* side `μ_n`; the index group ℤ/m (odd) where the
  DFT/flatness question lives sees **no dyadic structure at all** (`F_p^* ≅ μ_n × ℤ/m`, coprime orders).

This is the **algebraic explanation** of the previously only-numerically-refuted "2-power escape"
(`RESEARCH_SYNTHESIS_407_TANGENT.md §5`): there is no extra 2-power cancellation because the 2-power
and the DFT live on coprime-order sides. The H–D fold *is* active in the non-prize near-Fermat case
(`m` even, the #400 trap with `C > √2`) and *inactive* in every prize-valid prime.

**Lean brick:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_GaussPhaseFlatnessAlgebra.lean`
(axiom-clean `[propext, Classical.choice, Quot.sound]`, `lake env lean` RC=0):
- `prizeIndex_odd` : `padicValNat 2 (p−1) = a ⟹ Odd ((p−1)/2^a)`.
- `doubling_bijective_of_odd` : `Odd |G| ⟹ Bijective (x ↦ x+x)` on a finite add-group.
- `dyadic_invisible_to_index` : packaged separation (prize ⟹ ℤ/m odd ∧ doubling bijective).

## 2. The wall, located precisely

Flatness of the m-DFT of `(a_j)` over the **odd** group ℤ/m ⟺ `√m`-cancellation in the Jacobi-sum
average `T_h = (1/m)∑_i J(ψ^i,ψ^h)` (the tangent sum, I4) ⟺ **effective Jacobi-sum equidistribution
at constant index** `q = nm`, `m ≈ 2^128`. This is the SAME √-cancellation core as every face
(additive energy, Gauss-period house, Paley eigenvalue, tangent sum). The cohomology class `[b]` being
non-trivial is *necessary* for non-flatness but does not by itself bound the sup-norm in either
direction — the bound is the open analytic input. KU (2505.22059) is vacuous here (`KowalskiUntrauBarrier.lean`).

## 3. Honest scorecard

| axis | score | why |
|---|---|---|
| Novelty | 7 | the index-parity separation (R5) is a new, clean, *algebraic* explanation of the 2-power-escape refutation, and the cocycle/chirp framing (R3,R4) packages the obstruction sharply; the self-duality (R1) and Parseval pin (R2) are known-type. |
| Insight | 8 | pinpoints *why* the dyadic structure cannot help: 2-power and DFT on coprime-order sides of `F_p^* ≅ μ_n × ℤ/m`. Converts a numeric refutation into a theorem. |
| Proximity | 8 | dead-on prize regime; the separation is exactly a property of the maximal-dyadic setup. |
| Feasibility | 2 | the residual flatness over odd ℤ/m is the open √-cancellation wall; this angle clarifies, does not ease it. |

**Verdict:** PARTIAL — a new axiom-clean structural theorem (the index-parity separation) that
*proves* the dyadic structure is invisible to the Gauss-phase DFT, plus the precise cocycle/chirp
location of the obstruction. **No flatness bound, no δ* pin, is claimed.** Reconfirms the wall from a
new (algebraic, not numeric) direction.

## Cross-path lever

The Parseval pin (R2) `B ≥ √n` is a clean, transferable **lower** bound usable by any path needing a
two-sided bracket on `B`. The index-parity separation (R5) is a *reusable structural pre-fact* for any
2-power-tower / dyadic-descent attempt (it tells them the descent must act on the subgroup side, never
the index side) — directly relevant to the additive-combinatorics / Lam–Leung-tower face and the
cumulant-tower-martingale route.

## References
- [ABF26] eprint 2026/680, #407.  Berndt–Evans–Williams, *Gauss and Jacobi Sums* §11.4 (H–D product).
- In-tree: `GaussPeriodCosetReduction.lean`, `TangentSumJacobiAverage.lean` (I4),
  `KowalskiUntrauBarrier.lean`, `CharSumMomentDeepWall.lean`, `RESEARCH_SYNTHESIS_407*.md`.
