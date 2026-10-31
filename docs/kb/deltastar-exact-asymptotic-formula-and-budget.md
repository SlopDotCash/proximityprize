# δ* exact asymptotic formula (over-det far-line incidence) + the budget reconciliation — #407

Computed exactly with the validated parallel Rust engine (`scripts/rust-pg/`, matches the canonical in-tree
probe δ*(μ_16,k=4)=9/16). Resolves the long-open ">2^12 crossover" asymptotic of the far-line incidence δ*.

## The exact closed form (validated, 5+ points, 2 rates)

For the over-determined **monomial** far-line incidence threshold with the in-tree **windowed budget = n**:

> **δ* = ½ + (1/(2ρ) − 1)/n**,  equivalently **s* = n/2 − 1/(2ρ) + 1**  (binding witness size).

Verified exactly: ρ=1/4 → δ*=½+1/n (0.5625, 0.5500, 0.5417 at n=16,20,24); ρ=1/8 → δ*=½+3/n (0.6875, 0.625 at
n=16,24). The binding `s*−k = (1/(2ρ)−1)(k−1)`.

**Consequence: δ* → ½ as n→∞, for every ρ** (with budget=n). This is BELOW the conjectured floor `1−ρ−Θ(1/log n)`
(→ 1−ρ), and below Johnson `1−√ρ` for ρ<1/4. So with budget=n the far-line incidence δ* is NOT the floor — it
converges to the ½-agreement (Plotkin-type) threshold.

## The reconciliation: it is ALL in the budget normalization

The over-determined incidence `I(s)` trends down (not necessarily monotonically; see "The decay law" below) from
`I(k+2) ~ cubic ~ n³` (s near k) to a small plateau (s near n/2). δ* = (n−s*)/n where `s*` is the first `s` with
`I(s) ≤` budget `B`. So the budget SLIDES δ*:

| budget B | binding s* | δ* |
|---|---|---|
| `~ n`   | `~ n/2`     | → ½ (Plotkin) |
| `~ n^{3−ε}` | `~ k + Θ(n/log n)` | → **1−ρ−Θ(1/log n)** = the FLOOR |
| `~ n³` (= I(k+2)) | `~ k+2` | → 1−ρ (capacity, impossible) |

So **whether δ* tracks the floor is exactly the question of the prize budget `B = ε*·q`** and the decay rate of
`I(s)`:
- The prize sets `ε* = 2^{-128}` (fixed) and `q` = field size. In the prize regime `q ~ n^β` (β≈4), `B = ε*·q
  = 2^{-128}·n^β` — which **grows with n** (not the fixed `n` the windowed probe used). The correct asymptotic
  budget is super-linear, sliding δ* UP from ½ toward the floor.
- The floor `δ* = 1−ρ−Θ(1/log n)` corresponds to `s*−k ~ Θ(n/log n)`, i.e. `B = I(k + Θ(n/log n))`. Whether
  the prize budget `ε*·q` lands exactly there (giving the floor) is the precise, now-combinatorial open question.

## What is established vs open

- **Established (exact, validated):** the budget=n far-line incidence δ* = ½ + (1/(2ρ)−1)/n → ½; the
  over-det incidence is cubic `~n³` at s=k+2 and trends down (not monotonically; see the decay-law section) to a
  small plateau near s~n/2; p-independent in the thin/prize regime.
- **Open (the floor reconciliation):** derive `I(s)` for general s (the decay law), and determine where the
  prize budget `ε*·q` crosses it — i.e. whether `s*−k ~ Θ(n/log n)` (floor) for the prize-regime budget. This is
  now a pure combinatorial decay-vs-budget question (no char-p, no BGK).

## Honest correction to an earlier over-statement

Earlier I suggested δ* "decouples from BGK and might track the floor." The decoupling (p-independence) is real,
but the floor-tracking is NOT automatic — with the literal budget=n it gives ½, not the floor. The floor requires
the correct super-linear budget `ε*·q`, and matching it to the incidence decay is the genuine remaining problem.
The engine + the exact δ*=½+(1/(2ρ)−1)/n formula are solid; the floor claim is downgraded to "depends on the
budget normalization, precisely stated above."

## The decay law I(s) (full curves, validated)

The over-determined incidence `I(s)` decays overall from `~n³` (s=k+2) to a small plateau, crossing budget=n at
`s* ≈ n/2`.

**What each row is a maximum over (threshold-dependent family).** `I(s)` is the maximum, over the far monomial
directions admissible at threshold `s`, of the number of bad scalars `γ` whose line point agrees with some
degree-`<k` codeword on at least `s` points of `μ_n`. Both the admissible family (which directions count as far /
over-determined at agreement `s`) and the per-direction maximizer depend on `s`, so `I` is a maximum over a
**different family at each `s`**, not one fixed family evaluated at nested thresholds. Consequently `I(s)` need
**not** be monotone in `s`: the `n=24, k=3` row below increases from `I(9)=16` to `I(10)=19`. The word "decays"
describes the overall trend only. The binding size is defined by the **first-crossing convention**
`s* = min { s ≥ k+2 : I(s) ≤ B }`; because the rows are not monotone, a crossing need not be unique in general
(a later rise above `B` is not excluded by any proof), and every `s*` quoted here uses the first-crossing
convention. (The engine source, `scripts/rust-pg/`, is not in this tree, so the exact admissibility rule for far
directions at each `s` could not be re-read here; any reuse of these rows must restate it.)

```
n=24,k=2:  s= 4   5   6   7   8   9  10  11  12  13
           I=361  71  40  24  18  15  15   5   5   5      (budget 24 crossed at s*=7)
n=24,k=3:  s= 5   6   7   8   9  10  11  12  13
           I=143 133  37  37  16  19  12  12   9          (budget 24 crossed at s*=9)
```

- `I(k+2) ~ cubic ~ n³` (top of the curve), trending down (non-monotonically) to a small plateau near `s~n/2`
  (`5 = 2k+1` for `k=2`; the `k=3` row is still at `9` at the last listed `s`).
- **The budget slides s\* through this decay region:** `δ* = 1−ρ` (floor/capacity) needs `s*~k+2` ⟹ budget
  `~ I(k+2) ~ n³`; `δ* → ½` needs `s*~n/2` ⟹ budget `~ n`.

So the **floor `δ*=1−ρ−Θ(1/log n)` corresponds to the prize budget `ε*·q ~ n^{3−ε}`**. The precise open
question is now purely: *what is `ε*·q` in the asymptotic prize regime, and does it cross `I(s)` at `s*−k ~
Θ(n/log n)`?* With `ε*=2^{-128}` fixed and `q` the field size, this is a normalization/parameterization
question about the prize — fully combinatorial, no char-p, no BGK.
