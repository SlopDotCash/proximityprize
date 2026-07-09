# δ* sweep A12 — tower-recursive phase alignment as a named structural lemma (2026-06-14)

**Actionable:** A12 (merged 389-T03). Numerical-probe + Lean-brick.
**Status:** PARTIAL — structural backbone re-landed axiom-clean; the descent it once promised stays
REFUTED. This is a precise statement of the worst-vs-average mechanism, **not** a closure.

## Object

`η_b(G) = Σ_{y∈G} ψ(b·y)` (incomplete Gauss period). For `n = 2^μ`, `μ_n ≤ Fˣ` the order-`n`
subgroup, `z` a generator, split `μ_n = μ_{n/2} ⊔ z·μ_{n/2}` and put
`A := η_b(μ_{n/2})`, `B := η_{b·z}(μ_{n/2})` (`= Σ_{x∈z·μ_{n/2}} ψ(b·x)`).

## The exact structural facts (the lemma)

```
[SPLIT]          η_b(μ_n)       = A + B               (untwisted half-coset sum)
[TWIST]          η^χ_b          = A − B               (order-2 multiplicative twist)
[PARALLELOGRAM]  ‖A+B‖² + ‖A−B‖² = 2(‖A‖² + ‖B‖²)      (EXACT — the 2-adic energy recursion)
[ALIGN]          ‖A−B‖² ≤ ‖A+B‖²  ⟺  Re(A·conj B) ≥ 0   (untwisted branch dominates iff coherent)
```

All four are PROVEN axiom-clean in
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A12_PhaseAlignmentTower.lean`
(`eta_split_coset`, `etaTwist`/`eta_twist_split`, `gaussPeriod_tower_parallelogram`,
`untwisted_ge_twisted_iff_align`, plus `eta_untwisted_norm_ge_twist_of_align`).
Axiom audit: `[propext, Classical.choice, Quot.sound]` only — no `sorryAx`.

## What the probe shows (`scripts/probes/sweep_A12_phase_align.py`)

n = 8,16,32,64; `p ~ n²` and prize-shaped `p ~ n⁴`; coset-rep scan (η constant on cosets):

| n | p | cos(A,B)@b* | untw>twist | parallelo res | persist 1-lvl | proxy |
|---|---|---|---|---|---|---|
| 8 | 73 | +1.00000 | T | 0 | **−1.00000** | 0.283 |
| 8 | 4129 | +1.00000 | T | 7e-15 | +1.00000 | 0.925 |
| 16 | 257 | +1.00000 | T | 1e-14 | +1.00000 | 0.959 |
| 16 | 65537 | +1.00000 | T | 0 | +1.00000 | 0.999 |
| 32 | 1153 | +1.00000 | T | 3e-14 | +1.00000 | 0.873 |
| 32 | 1048609 | +1.00000 | T | 0 | +1.00000 | 0.985 |
| 64 | 4289 | +1.00000 | T | 6e-14 | +1.00000 | 0.470 |
| 64 | 16777601 | +1.00000 | T | 5e-13 | +1.00000 | 0.630 |

- **cos = +1.00000 EXACTLY** at the worst frequency `b*` in all 8 cases — the untwisted branch
  `A+B` realizes `B(μ_n)`. (`untwist_bigger = True` everywhere.)
- A, B are REAL (`max|Im| ≤ 5e-15`): negation symmetry `−1 = z^{n/2} ∈ μ_n`. So "cos = 1" reduces
  to "A, B have the SAME SIGN at b*". The alignment is **forced** — at the maximizing frequency the
  cross term is `≥ 0` (it has to be, or `A−B` would beat the claimed max). It carries **no** extra
  information beyond "the max picks the coherent branch".

## The two honest negatives this sharpens

1. **Persistence is NOT robust.** The top-level alignment is forced, but one 2-adic level down it
   **flips to anti-alignment** at `n=8, p=73` (cos = −1.00000) while holding at +1 in 7/8 cases.
   So the alignment does not propagate as a clean recursion — a fresh, independent confirmation of
   why the descent fails.
2. **Proxy faithfulness is only approximate.** `|S_{b*}(μ_{n/2})| / B(μ_{n/2})` rises toward 1 as
   `p` grows (0.92–0.999 at `p ~ n⁴`) but dips to 0.47/0.63 at the smallest primes — the worst
   `μ_n` frequency only *approximately* maximizes `μ_{n/2}`.

## Why this is NOT a closure

The parallelogram is an **EQUALITY**. The naive descent `M(n)² ≤ 2·M(n/2)²` (taking `‖A−B‖² ≥ 0`
and `‖A‖,‖B‖ ≤ M(n/2)`) is **FALSE at finite n** — worst-case ratios spike to **2.68 > 2** (#407
ledger; the single-level `LocalAlignedChildSubmaximality` was refuted axiom-clean). There is no
inequality direction here that crosses the floor.

The value is exactly as the actionable framed it: **a precise statement of the one mechanism the
symmetric moment hierarchy cannot see.** `Σ_b ‖η_b‖^{2r}` is symmetric in `b` — it averages over
all frequencies and is blind to *which* frequency aligns coherently. The parallelogram split tracks
the per-`b*` coherent addition of the two children — the worst-vs-average gap that the moment
method (capped at Johnson, `_MomentMethodNoGo.lean`) provably cannot resolve. The floor
`B(μ_n) ≲ √(n·log(q/n))` (BGK / Paley-graph wall) remains OPEN.

## Files

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A12_PhaseAlignmentTower.lean` (axiom-clean)
- `scripts/probes/sweep_A12_phase_align.py`
- in-tree predecessor (coset count): `GaussPeriodCosetReduction.lean` (the `(q−1)/n`-period count)
