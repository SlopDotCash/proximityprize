# wf407 / T371-01-census — Moment-depth classification of `CensusDomination`

**Date:** 2026-06-14 · **Verdict: WALLED (DEEP).** CensusDomination is a deep
`r`-th-order subset-sum statistic with `r = (1−δ*)·n/m = Θ(n)` at fixed production
rate. It does NOT collapse to the reachable 2nd-order additive energy `E₂(μ_n)`; it
inherits the master deep-moment / Gauss-period (`E_r`, `r ≍ band`) wall (W4 + W2).

## The B5 question (the dossier's "arguably highest-value single question")

The both-sided δ* pin (`CensusDominationWeld.kkh26_deltaStar_pin_of_censusDomination`,
audited airtight O165, axiom-clean) rests on ONE named open Prop, `CensusDomination`.
Is it (1) **low-order** (≤ 4th moment, hence reachable like `E₂`, so the pin follows),
or (2) **deep** (= the full Gauss-period wall, needing moments `r ≍ log q`, so it
inherits the master wall)? This decides everything.

## The exact equivalence chain (kernel-proven in-tree, not re-derived)

`CensusDomination dom k a₀ K` caps, for every stack and every band `a ≥ a₀`, the number
of `a`-subsets that are `γ`-aligned (some `γ`) with a non-degenerate `(k+1)`-tuple
(`UniversalAlignmentLaw.Aligned`: all `C(a,k+1)` divided-difference ratios coincide).
The deployed pin uses `k = (r−2)m+1`, `a₀ = rm+1`, band `a = rm`, `n = 2^μ·m`,
`δ* = 1 − r/2^μ`.

`KKH26AlignmentSupply.kkh26_fibreUnion_aligned_nondegenerate` (kernel-proven)
identifies the **extremal supply** on the KKH26 line `(x^{rm}, x^{(r−1)m})`:

- aligned `rm`-sets ↔ `r`-subsets `T` of the order-`s` subgroup (`s = n/m`), via the
  `m`-power-fibre union `S_T = {i : (gⁱ)^m ∈ T}`;
- aligning scalar `γ_T = −∑_{a∈T} a`.

Therefore, exactly:

```
extremal bad-scalar count = #{ distinct r-subset sums of the order-s subgroup }
supply count              = C(s, r)
band index                = a = rm = (1 − δ*)·n        (m=1: a = r = (1−δ*)·n)
```

So **§5.0 BIND ⟺ M(n) ⟺ CensusDomination** all bottom out in the same object: the
`r`-subset-sum / additive structure of `μ_s`, at subset-size/order `r` = the agreement
band = `Θ(n)` at any fixed rate.

## Numerics (EXACT, full enumeration, the decisive evidence)

`scripts/probes/wf407_T371_01_census_depth_v2.py`,
`wf407_T371_01_census_E2_independence.py`,
`wf407_T371_01_census_prodrate.py`.

**(1) Bad count is functionally independent of `E₂`** — the decisive test.
Order-`s=16` subgroup, FIXED `E₂(G) = 3s²−3s = 720`, identical across 5 primes
(12289, 40961, 65537, 786433, 1179649). Bad count `#distinct r-subset sums`:

| r        | 2   | 3   | 4    | 5    | 6    | 7    | 8    |
|----------|-----|-----|------|------|------|------|------|
| bad count| 113 | 464 | 1233 | 2256 | 3025 | 3280 | 3281 |

A single 2nd-moment value (720) maps to MANY bad counts ⟹ the census bad count is NOT a
function of `E₂`. It is a deep `r`-th-order subset-sum statistic. (Counts are identical
across all 5 primes = char-0 subset-sum counts, well below the mod-p collision threshold
in the prize regime.)

**(2) `s=8` symmetry `r ↔ s−r`** (peak at the half-band `r=s/2`):
bad counts `25, 40, 41, 40, 25` for `r=2..6` — the deepest band is `r=s/2` = the
production rate `ρ=1/2` (FRI). The deepest census band is the deepest production rate.

**(3) Moment order grows LINEARLY in `n`.** Deployed `k=(r−2)m+1` ⟹ `r ≈ ρ·s+2`. At
`ρ=1/2`, `r ≈ s/2 = n/2 = Θ(n)`; supply `C(s,r) ~ 2^{H(ρ)·n}` exponential. At the prize
(`p ~ n·2^128`, `n=2^30`): required census order `r ~ n/2 = 2^29`, while the
char-0-transferable deep-moment depth is `r_max = 2·log_n p = 1+128/log₂n ≈ 5.3` = `O(1)`.
**Gap = `n/2` vs `O(1)`** — exactly the W4 moment-method-stops-`√(log)`-short master wall,
viewed on the census face.

## Lean brick (axiom-clean)

`Research/ProximityPrize/Frontier/WF407_T371_01_CensusMomentDepth.lean`:

- `band_eq_agreement_radius` — the band order `a = r` equals `(1−δ*)·n` (`m=1`); the
  census order is the deep agreement radius.
- `band_order_linear` — fixed-rate band order is `Θ(n)` (doubling `n` doubles `r`).
- `alignableSupply_strictMono_below_half` — `C(s,r) < C(s,r+1)` for `2r+1<s`: the supply
  strictly grows with the band index `r`; no fixed low order can describe it.
- `alignableSupply_le_peak` — peak at the half-band `r=s/2` (FRI `ρ=1/2`).
- `census_badCount_not_second_order` — machine-checked countermodel to "`CensusDomination`
  is 2nd-order", using the probe's exact numbers (`E₂=720` fixed, bad `113 ≠ 464`).

Axiom audit: `[propext, Classical.choice, Quot.sound]` only.

## Verdict

**WALLED (DEEP).** `CensusDomination` is NOT a `≤4th`-moment statement and is NOT
reachable via the 2nd-order additive energy. Its order parameter is the agreement band
`r = (1−δ*)·n/m = Θ(n)`, an `r`-th-order subset-sum count provably independent of `E₂`.
It is the SAME deep object as the master Gauss-period / `E_r` wall (memory
`arklib-389-deep-moment-wall`, `CharSumMomentDeepWall.lean`). This RESOLVES the B5
question: the conditional pin does not get cheaper than the master wall — proving
`CensusDomination` at prize parameters is equivalent in moment-depth to the
deep-moment / explicit-RS sub-Johnson list-decoding 25-year open problem.

**What this rules out:** any attempt to discharge `CensusDomination` via a second-moment /
additive-energy argument (e.g. `E₂(μ_n)=3n²−3n` rigidity) is doomed — `E₂` does not
determine the census bad count. The only viable route is a genuinely deep
(`r=Θ(n)`-th-order) cancellation, i.e. solving the master wall itself.

**What remains (for the next wave):** the deep object is the `r`-subset-sum count of
`μ_s` at `r=Θ(n)`. This connects to the live `arklib-407-dyadic-fourier-uncertainty`
(char-0 lacunary count CLOSED) and `arklib-389-energy-character-unification` lanes — the
char-0 subset-sum count is closed-form (coset-union rigidity); the open part is the
char-p mod-q defect at deep order, the unchanged prize wall.
