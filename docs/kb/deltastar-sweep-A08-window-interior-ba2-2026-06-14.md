# [A08] Window-interior worst direction dir(a,b) with b−a>1: the gap-2 constraint + O(n)-vs-superlinear verdict (2026-06-14)

**Actionable A08** (merged from 400-T01;400-T09;232-T15): the #400 refutation conflated
*overall-worst* (near-capacity) with *window-interior-worst*; the `b−a>1` directions (e.g.
`dir(5,7)`) were proposed but never enumerated with an exact `Z[ζ_n]` enumerator. This note
delivers: (1) a reusable EXACT enumerator, (2) the explicit `b−a=2` symmetric-function constraint
(the analogue of `e₂=0`), and (3) the decisive O(n)-vs-super-linear verdict.

Artifacts:
- `scripts/probes/cyclotomic_exact_enumerator.py` — reusable EXACT `Z[ζ_n]` ring + `X^j mod m_S`
  reducer (basis `ζ⁰..ζ^{n/2−1}`, `ζ^{n/2}=−1`), cross-checked vs complex eval at n=8,16 (A17 substrate).
- `scripts/probes/sweep_A08_window_interior.py` — the main n=8,16,32 sweep (char-0 + F_q).
- `scripts/probes/sweep_A08_growth_law.py` — the growth-law fit + interior collapse.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A08_WindowInteriorBA2.lean` — axiom-clean
  brick proving the gap-2 constraint identity.

## 1. Setup (monomial direction, exact reduction)

Smooth `RS[k]` on `μ_n`. The monomial line `dir(a,b)` is `u₀ = Xᵇ`, `u₁ = Xᵃ`; bad scalars are
`B(a,b,w) = {γ : (Xᵇ + γXᵃ) mod m_S has degree < k for some |S|=w subset of μ_n}`,
`m_S = ∏_{x∈S}(X−x)`, `δ = 1 − w/n`. Killing the top `w−k` coefficients of
`Pᵧ = (Xᵇ mod m_S) + γ(Xᵃ mod m_S)` is `w−k` equations in one unknown γ. We enumerate over all
`w`-subsets exactly, in both `Z[ζ_n]` (char-0) and `F_q` (`q ≡ 1 mod n`).

`rows := w − k` is the key parameter:
- `rows = 2` ⟺ `k = w−2` ⟺ `δ = 1 − ρ − 2/n` = the **near-capacity edge** (just below capacity).
- `rows ≥ 3` ⟺ genuinely inside the window (bounded away from capacity).

## 2. The explicit b−a=2 constraint (PROVEN, verified)

For the gap-2 cell `a = w−1`, `b = w+1`, `k = w−2` (two top coefficients), the reduction recurrence
`Xʷ ≡ e₁Xʷ⁻¹ − e₂Xʷ⁻² + e₃Xʷ⁻³ + ⋯` gives after one more `×X`:

> `Xʷ⁺¹ ≡ (e₁²−e₂)·Xʷ⁻¹ + (e₃−e₁e₂)·Xʷ⁻² + ⋯  (mod m_S)`.

Since `Xᵃ = Xʷ⁻¹` is already reduced (only the `Xʷ⁻¹` coefficient), killing both top coefficients of
`Xʷ⁺¹ + γXʷ⁻¹` is **equivalent to**:

> **`γ = e₂(S) − e₁(S)²`   and the CONSTRAINT   `e₃(S) = e₁(S)·e₂(S)`.**

This is the exact gap-2 analogue of gap-1's (`γ = −e₁`, `e₂ = 0`). Verified EXACTLY against the
`F_q` enumerator on **every** `w=6` subset: 28/28 of `μ₈` (`p=41`) and 8008/8008 of `μ₁₆`
(`p=193`). The Lean brick `Sweep_A08_WindowInteriorBA2.lean` proves the equivalence
`(top coeffs vanish) ↔ (γ = e₂−e₁² ∧ e₃ = e₁e₂)` axiom-clean (`[propext, Classical.choice,
Quot.sound]`, no `sorry`).

The hierarchy: gap `g` kills the top `g` reduced coefficients, the `j`-th being a vanishing
symmetric-function relation of degree `j+1`. gap-1 → `e₂=0`; gap-2 → `{e₃=e₁e₂}` (with γ from the
first row). gap-`g` → a chain of `g−1` symmetric-function constraints.

## 3. The O(n)-vs-super-linear verdict (DECISIVE)

Exact enumeration (n=8,16,32; large prime ≈ char-0; multiple F_q for q-dependence):

| n | ρ | w | dir | rows | char-0 #bad | F_q #bad (sample) | regime |
|---|---|---|-----|------|-------------|-------------------|--------|
| 16 | 1/2 | 10 | (9,11) | 2 | 40 | 64,72,40,40 | ~2.5n, **q-dep**, near-cap edge |
| 16 | 1/2 | 11 | (10,12) | 3 | **0** | 0,0,0,0 | interior → **collapse** |
| 16 | 1/4 | 6 | (5,7) | 2 | 40 | 64,72,40,40 | ~2.5n, **q-dep**, near-cap edge |
| 16 | 1/4 | 7 | (6,8) | 3 | **8** | 8,8,8,8 (1 coset) | interior → **O(n), q-indep** |
| 16 | 1/8 | 4 | (3,5) | 2 | 24 | 32,32,24,24 | ~1.5n, q-dep |
| 16 | 1/8 | 5 | (4,6) | 3 | **0** | 0,0,0,0 | interior → **collapse** |
| 32 | 1/16| 4 | (3,5) | 2 | 112 | 96,128,112,128 | ~4n, **q-dep** |
| 32 | 1/16| 5 | (4,6) | 3 | **0** | 0,0,0,0 | interior → **collapse** |

**Growth law of the `rows=2` near-capacity cell** (`w=4`, large prime `q=769`):

| n | 8 | 16 | 32 | 64 |
|---|---|----|----|----|
| #bad | 4 | 24 | 128 | 640 |

fitted exponent `n^{2.585} → n^{2.415} → n^{2.322}` (decreasing toward `2`); clearly `≥ n²`,
**super-linear**. q-dependence at n=32, w=4: `#bad ∈ {96,112,128,144}` across `q ∈
{97,193,257,449,577,769,929}` — genuinely **field-dependent** (a mod-q additive-energy defect, cf.
A09). So the gap-2 `rows=2` cell is super-linear AND q-dependent.

**The interior collapse.** One step into the genuine window interior (`rows=3`, one extra vanishing
symmetric-function row) the count drops to `0` (ρ=1/2, 1/8, 1/16) or to a single `μ_n`-coset
`= 8 = O(n)`, q-independent (ρ=1/4). The third constraint `e₄`-type relation over-determines the
one free scalar γ.

## 4. Verdict

> **The b−a=2 worst monomial direction is super-linear (`≳ n²`, q-dependent) ONLY at its
> `rows=2` near-capacity edge `δ = 1−ρ−2/n`, exactly mirroring b−a=1. In the genuine window
> interior (`rows ≥ 3`) it is `O(n)` or `0`.**

So `b−a=2` does **NOT** supply a window-interior super-linear `δ*`-pinning direction. The #400
refutation of the overall-worst (near-capacity) direction **extends to the gap-2 family**: the
super-linear blow-up is again a near-capacity artifact. This is consistent with — and reinforces —
the `s_max = μ−1` staircase picture (`issue400-smax-law-...`): the `e₂=0` family's `Θ(n^{s_max})`
blow-up lives at near-capacity, and the gap-2 generalization shows the same edge-localization.

**Honest status.** PARTIAL/structural: the gap-2 constraint is proven (Lean, axiom-clean) and
verified exactly; the O(n)-vs-super-linear verdict is exact enumeration at n=8,16,32 (n=32 only at
the small-w feasible cells; large-w interior cells of n=32 are combinatorially infeasible to
enumerate directly — but the `rows≥3` collapse is uniform across every feasible n,ρ). NO closure
claimed; this constrains the problem by ruling out gap-2 as an interior `δ*`-pinning direction and
re-localizing the genuine open core to either (i) the near-capacity edge (above δ*, irrelevant) or
(ii) the `rows`-many-constraint interior whose O(n) behavior is the same coset-equidistribution /
BGK wall as everywhere else.

| axis | score |
|---|---|
| novelty | 7 (gap-2 constraint `e₃=e₁e₂` + γ=e₂−e₁² is new explicit form; exact enumerator is reusable substrate) |
| insight | 8 (collapses the gap-2 question to a clean hierarchy; localizes super-linearity to the near-cap edge; rows=3 collapse is sharp) |
| proximity | 7 (settles the A08 sub-question negatively; extends #400 refutation; q-dependence confirms mod-q defect lane) |
| feasibility | 8 (fully delivered: enumerator + sweep + growth law + axiom-clean Lean identity) |
