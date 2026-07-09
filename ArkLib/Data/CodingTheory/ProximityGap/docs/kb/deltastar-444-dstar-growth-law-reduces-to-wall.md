# D\*-growth-law: the p-independent distinct-γ count is super-budget ⟹ reduces to the wall (#444)

*Status: PROVEN (axiom-clean Lean) — a **reduces-to-wall** outcome on the off-BGK over-determined
route. Not a prize closure; a clean negative that re-confirms the char-sum wall is the binding object
in the window interior. Honesty contract: no fabricated closure.*

## The attack target

The off-BGK (`p`-independent) route to `δ*` replaces the analytic char-sum wall
`M(n) = max_{b≠0} |Σ_{x∈μ_n} e_p(bx)| ≤ C·√(n·log m)` by the **distinct-bad-scalar count**
`D*(n,r) = max over witness lines of #{distinct γ}`, where a far-line bad scalar
`γ = −h_{e−r}(S)/h_{f−r}(S)` is pinned by an alignable `(r+1)`-subset `S ⊆ μ_n` on the depth-`r`
bilinear Schur-ratio variety `h_{e−r}h_{f−r+1} = h_{f−r}h_{e−r+1}`. The closure hope (line 4338): the
`p`-independent `D*` governs `δ*` through the window and stays `≤` the prize **budget**
`q·ε* = n`, so the combinatorial union of bad scalars fits the budget and closes the prize *without*
the wall.

**The attack question:** does `D*(n,r)` stay `≤ n` through the window interior, or cross `n` earlier?

## The proven growth law (Frontier/_DstarGrowthLaw.lean, axiom-clean, real lake build 8313 jobs)

By the proven orbit identity `D*(n,r) = (n/d)·O_P + [γ=0]` (`d = gcd(e−f,n)`; reproduced exactly here,
`scripts/probes/_probe_444_dstar_growth.py`), where `O_P` = #distinct dilation invariants `J = γ^{n/d}`,
the worst case `d = 1` gives `D* = n·O_P + [γ=0]`. For the over-determined deep band (deficit 2, `r = 3`,
worst-case order-2 line) the in-tree closed form `DeepBandR3Bound.deepBandBadCount` gives

> `D*(n,3) = n·C(n/4,2) + 1`, hence `O_P(n,3) = C(n/4,2) = Θ(n²)` and `D*(n,3) = Θ(n³)`.

`_DstarGrowthLaw.lean` lands (all four `[propext, Classical.choice, Quot.sound]`, no `sorryAx`):

- `dStar3_eq_n_mul_orbit`: `D*(n,3) = n·C(n/4,2) + 1` (= the orbit identity in the `n=4g` chart).
- `dStar3_gt_budget`: **`budget n = n < D*(n,3)` for every `n = 4g ≥ 16`** — the budget is crossed at the
  bottom of the band.
- `orbit_count_unbounded`: `O_P(n,3) = C(n/4,2) → ∞` — the budget-excess factor is **unbounded,
  polynomially-growing**, NOT a constant.
- `offBGK_overdet_caps_below_window`: the packaged verdict (both of the above).

Numerics (`decide`-checked rungs + probes, matching `DeepBandR3Bound`): `n=16` `D*=97`, `O_P=6`;
`n=32` `D*=897`, `O_P=28`; `n=64` `D*=7681`, `O_P=120`. Log-log slope of `O_P(n,3)` in `n` → 2.000
(`_probe_444_dstar_polestructure.py`). At the prize `n = 2³⁰`: `O_P ≈ 3.6·10¹⁶`, so `D*` exceeds the
budget `n` by ~`3.6·10¹⁶×`.

## Generating-function / pole reading

`Z(t) = exp(∑_r I_r t^r / r)`, `I_r` = #length-`r` alignable moment patterns. `O_P(n,r) = [t^r] Z`
counts the distinct values of a fixed-degree rational symmetric invariant `J` on the
`(e_1,…,e_{r−1})` moment variety; the number of free moment coordinates is `r−1`, so
`I_r = Θ(n^{r−1})`, `O_P = Θ(n^{r−1})`, `D* = Θ(n^r)`. There is **no finite-radius pole** capping `O_P`
at a constant — the radius of convergence in the `n`-scaled variable `→ 0`. The growth is genuinely
polynomial in `n`; there is no constant cap that would let the off-BGK union fit the budget.

## Verdict: REDUCES TO WALL (confirms "line 451")

The `p`-independent over-determined distinct-γ count is `Θ(n³)` ≫ budget `n` for all `n ≥ 16` and grows
without bound. So the off-BGK over-determined route **caps below the window** — the combinatorial union
of bad scalars does NOT fit the budget. Therefore the binding window-interior `δ*` is forced onto the
**under-determined (`s−k ≤ 1`) BGK char-sum contribution**: `M(n) ≤ C·√(n·log m)` is the real wall on
the over-determined side, and this route does not breach it. This is fully consistent with the campaign
DECISIVE-PHASE VERDICT (`m* = s−k` linear, over-det count super-poly inside the window) and with the
in-tree `moment_ladder_exceeds_prize` (no moment method reaches the target).

**What this is NOT:** a prize closure, and not a claim that the over-det count is the binding `δ*`
object. It is the precise refutation of the "`D* ≤ budget` through the window" hope, with an explicit
super-budget growth law, isolating the under-determined char sum as the binding wall.

## Pointers

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_DstarGrowthLaw.lean` (this result);
  `…/DeepBandR3Bound.lean` (the `r=3` closed form it wires to);
  `…/Frontier/DemandFloorReduction.lean` (the `O_P ≤ C(n/2,r−1)` reduction it sits beside).
- Probes: `scripts/probes/_probe_444_dstar_growth.py` (orbit identity + `O_P` census, full line sweep,
  anchor `97,145,89,113,225,104` reproduced); `scripts/probes/_probe_444_dstar_polestructure.py`
  (growth law `O_P=Θ(n²)`, slope→2.000, budget decision).
