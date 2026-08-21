# Attack #09 — Bootstrap the proven small-n / norm-regime BGK to large n via the 2-adic tower

**Issue #464/#444/#407 · 2026-06-27 · angle: norm-regime bootstrap / tensor / induction**

## Target theorem (what would close the prize from this angle)

> For `n = 2^μ`, prove by induction on `μ` that `M(2^μ) = max_{b≠0}‖η_b^{(μ)}‖ ≤ C·√(n log m)`,
> using the proven unconditional base case (norm regime `p>2^n`: `μ_n_additiveEnergy_eq = 3n²−3n`,
> `eta_quartic_le_uncond`) and an inductive step that propagates the bound up the dyadic tower
> `μ_2 ⊂ μ_4 ⊂ … ⊂ μ_{2^μ}` with a sub-`2×` per-level factor.

If the per-level factor were `√2` (the L²-heuristic factor for a sum of two decorrelated unit-scale
periods), induction would give `M(2^μ) ≤ √n · M(2)/√2 = Θ(√n)`, hitting the prize order.

## The recursion (proven, exact)

The smooth domain splits dyadically: `μ_{2^μ} = μ_{2^{μ-1}} ⊔ ω·μ_{2^{μ-1}}` for `ω` a primitive
`2^μ`-th root. Instantiating `sum_tower_split` at `f = ψ(b·•)` gives the EXACT period recursion

```
η_b^{(μ)} = η_b^{(μ-1)} + η_{bω}^{(μ-1)}.
```

This is landed axiom-clean as `eta_tower_recursion` in
`Frontier/_Attack09NormRegimeBootstrap.lean` (char-free, no Weil, no BGK).

## Proof attempt

**Lever (a) — TowerMonotonicity + base case.** `TowerMonotonicity`/`TowerMonotonicityRS` prove
`ε_mca` is monotone up the 2-adic tower. But monotonicity is for `ε_mca`, NOT for `M`. There is no
proven `M`-monotonicity, and `ε_mca` monotonicity gives only an inequality in the WRONG direction
for an upper bound on `M` (it says the protocol gets worse, not that the spectrum is controlled).
Dead.

**Lever (b) — multiplicative/tensor propagation.** The recursion is ADDITIVE (`a + bω`), not
multiplicative/tensor. `μ_{2^{μ+1}}` is not `μ_{2^μ} ⊗ μ_2` as a character object; the natural map
is the additive split. Apply the triangle inequality to the additive split:
`‖η_b^{(μ)}‖ ≤ ‖η_b^{(μ-1)}‖ + ‖η_{bω}^{(μ-1)}‖ ≤ 2·M(2^{μ-1})` (landed: `eta_tower_triangle`,
`M_doubling`). Iterated from the base `M(2)≈√2`, this gives `M(2^μ) ≤ 2^{μ-1}·M(2) = Θ(n)` —
TRIVIAL, far above `√n`.

**Lever (c) — the crossing pin / parallelogram.** The parallelogram law (landed:
`period_parallelogram`) conserves the second moment: `‖η‖²+‖η̃‖² = 2(‖a‖²+‖b‖²)`, where `η̃ = a−b`
is the χ-twisted period. This is exact and beautiful but useless for `M`: `η̃` is a DIFFERENT
frequency's period (the twist by the order-2 character of the level), so bounding `‖η‖²` requires
knowing `‖η̃‖²` is large — i.e. that the second moment is unevenly split — which is itself the
worst-case cancellation question.

## Refutation (the wall, made numerically exact)

The whole lift hinges on whether the two sub-period halves `a = η_{b}^{(μ-1)}` and `bω =
η_{bω}^{(μ-1)}`
DECORRELATE in phase, giving `√2` instead of `2`. Probe `probe_attack09` (p=257, computing the exact
maximizer `b*` at each level):

| μ | n | M(2^μ) | \|a\| | \|bω\| | \|a\|+\|bω\| | ratio_to_tri |
|---|----|--------|-------|--------|-------------|--------------|
| 2 | 4  | 3.923  | 1.957 | 1.966  | 3.923       | **1.000**    |
| 3 | 8  | 6.101  | 2.772 | 3.329  | 6.101       | **1.000**    |
| 4 | 16 | 9.229  | 5.851 | 3.378  | 9.229       | **1.000**    |
| 5 | 32 | 11.860 | 9.229 | 2.631  | 11.860      | **1.000**    |
| 6 | 64 | 10.100 | 3.713 | 6.386  | 10.100      | **1.000**    |

**At the worst-case frequency the two halves align in phase EXACTLY** (`ratio_to_tri = 1.000`). The
triangle inequality is TIGHT at the maximizer through μ=6. There is no decorrelation to harvest: any
sub-`2×` per-level factor would require an unconditional statement that the level-`(μ−1)` periods at
`b*` and `b*ω` are NOT phase-aligned — which is precisely the worst-case phase-cancellation
statement BGK/Paley controls and which ~60 prior sessions have shown is the wall.

Note the structural signature at μ=5: `M(32) = 11.86 = 9.229 (= M(16), the prior maximizer) +
2.631`.
The new level's worst case is built by ALIGNING a fresh half onto the previous level's maximizer.
The bad frequency persists and accretes; it does not average down. (This matches
`SpurPrimePersistTower`/`spur prime persistence`.)

## Why the norm-regime base case cannot be propagated

The base case `eta_quartic_le_uncond` / `μ_n_additiveEnergy_eq = 3n²−3n` is unconditional ONLY in
the
norm regime `p > 2^n` (no wraparound mod p: the `±1` combinations of roots never collide mod p, so
the additive energy is the char-0 Wick value). Going UP the tower at FIXED prime p, the wraparound
re-appears as soon as `2^μ` grows past `log₂ p`. The base case holds at small μ precisely because
there is no wraparound; the inductive step must CREATE wraparound control at each new level, and
that
is exactly the open content (`DCEnergyEssential`: the full-energy hypothesis is FALSE past the DC
crossover). The norm regime and the prize regime are on opposite sides of the wraparound onset; the
tower walks from one into the other, and the unconditional input expires at the crossing.

## Lever analysis — what would crack it

The single missing input is: **an unconditional sub-`2×` per-level phase-decorrelation bound** of
the
form `‖η_{b*}^{(μ-1)} + η_{b*ω}^{(μ-1)}‖ ≤ √2 · max(‖·‖)` at the maximizer. The numerics REFUTE this
as stated (alignment is exact). The honest equivalent is the worst-case cancellation = BGK/Paley
spectrum bound itself; the tower gives no independent leverage on it.

## Honest verdict

**Reduces to the wall.** The 2-adic tower recursion is exact and axiom-clean, but its only
unconditional consequence is trivial doubling `M(2^μ) ≤ 2·M(2^{μ-1}) ⟹ M ≤ n`. The lift needs a
per-level phase-decorrelation factor that the numerics show is exactly tight (no decorrelation at
the
maximizer), and that factor IS the worst-case Paley/BGK cancellation. The norm-regime base case
expires at the wraparound onset, which the tower necessarily crosses. Bricks landed (axiom-clean,
`[propext, Classical.choice, Quot.sound]`):
`eta_tower_recursion`, `eta_tower_triangle`, `M_doubling`, `period_parallelogram` in
`Frontier/_Attack09NormRegimeBootstrap.lean`.

This is the ~61st independent confirmation of the same wall; the value-add here is the EXACT
phase-alignment refutation of the decorrelation hope (ratio_to_tri = 1.000), which closes lever (b)
cleanly rather than leaving it "untested".
