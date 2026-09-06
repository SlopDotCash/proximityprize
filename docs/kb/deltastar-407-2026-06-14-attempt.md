# #407 attempt — closed-conjecture hunt, literature pass, and honest survivor

Date: 2026-06-14.

## Current issue state read

Issue #407 corrects several tempting routes. The current reliable synthesis is:

- The prize regime is thin-subgroup: `n = 2^μ`, `q ≈ n·2^128`, so `n ≈ q^(1/4..1/5)` and `n ≪ √q`.
- The analytic core remains the incomplete Gauss-period bound
  `max_b |Σ_{x∈μ_n} exp(2πibx/q)| ≤ C √(n log(q/n))`.
- Uniform one-step phase descent and constant-index/effective-Katz escapes were refuted or retracted.
- The R4 saturated-incidence route is a useful alternate finite/counting face, but its remaining profile-equality claim is still open.

## Five papers added / confirmed on disk

Stored in `~/papers/arklib/issue407-effective-eq/`:

1. `arxiv-2505.22059.pdf` — quantitative/effective equidistribution. Useful for checking whether Deligne/Katz-style discrepancy can be made effective; currently vacuous in the thin prize scale.
2. `arxiv-2207.12439.pdf` — Rojas-Leon, equidistribution and independence of Gauss sums. Gives qualitative non-conspiracy of Gauss phases; the missing prize input is uniform effectiveness over `m ≈ 2^128` phases.
3. `arxiv-2310.09992.pdf` — uncertainty principle / nonvanishing minors for subgroup Fourier matrices. Clarifies the specific-subgroup NVM face; index `> 3` remains open, so it does not bypass the Gauss-sum wall.
4. `arxiv-1712.00761.pdf` — improved Gauss-sum bounds in arbitrary finite fields. Confirms prime-power/subfield issues; insufficient for square-root cancellation in the deployed scale.
5. `arxiv-2302.13670.pdf` — ultra-short sums of trace functions. Relevant to large-value tails and effective trace-function methods; current bounds do not reach the `√n` target.

## Conjecture candidate

**Saturated-Incidence Inverse Profile (SIIP).** For fixed prize rate `ρ` and dyadic smooth domain `μ_n`, let `I_actual(n,w)` be the worst far-line incidence at agreement size `w`, and let `I∞(w)` be the characteristic-zero saturated cyclotomic incidence profile. In the non-saturated prize regime,

`I_actual(n,w) = I∞(w)` for all `w` up to the threshold band, and

`w* = max { w : I∞(w) ≤ n }`, `δ* = 1 - w*/n`.

This is closed as a finite profile statement and does not use Johnson or per-witness ownership. It is not yet a proof: the equality `I_actual = I∞` in the full threshold band is the open content.

Scores:

- Novelty: 8/10
- Insight: 9/10
- Proximity to prize regime: 9/10
- Feasibility: 6/10

Verdict: keep as a survivor and formal interface, not a claimed prize solution. The deterministic threshold plumbing is in `Research/ProximityPrize/Frontier/Issue407SaturatedIncidence.lean`.
The file also records the radius bridge

`agreementRadius n w = 1 - w/n`

with `agreementRadius_mem_unit`, `agreementRadius_strictAnti`, `agreementRadius_antitone`, and
`actualRadiusThreshold_of_saturatedRadiusThreshold`. These only translate a finite profile
certificate into the `δ*` language; the profile equality is still the open content.

## Refutation pressure applied

- Uniform `O(1)` coset rigidity is already refuted above the threshold band.
- Full-group or small-field validations are invalid for #407; the candidate is explicitly non-saturated/proper-subgroup.
- If any `w ≤ W` has `I∞(w) ≤ n < I_actual(n,w)`, the candidate fails immediately. This is formalized as `not_saturatedThrough_of_false_good`.

## Honest bottom line

No 9/10-feasibility closed conjecture was found. The best survivor is a sharper finite inverse-profile formulation of the R4 route, with an axiom-clean Lean consumer and explicit refutation hooks. The prize core remains open unless the saturated-profile equality or the equivalent Gauss-period sup-norm bound is proved.
