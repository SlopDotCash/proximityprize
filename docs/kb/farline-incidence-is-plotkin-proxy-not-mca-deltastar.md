# DECISIVE: the far-line incidence δ* → 1/2 (below Johnson) — it is a Plotkin proxy, NOT the MCA δ* — #407

> **Scope correction (2026-10-28 audit, T48; see the banner in
> `deltastar-RESOLUTION-tracks-floor-not-half.md`).** The formula `δ* = ½ + (1/(2ρ) − 1)/n → ½` is
> fitted to rows with `n ≤ 24`, so "exact" and "→ ½" are extrapolations. The later RESOLUTION note
> reports that the fitted formula breaks at `n = 32`, and that note's own opposite extrapolation is
> not established either. Both rest on a handful of finite rows, and the RESOLUTION rows (fixed
> `k = 2`) also change the rate with `n`.
> The conclusion that the far-line incidence is a proxy rather than the MCA `δ*` is consistent with
> the later guard: `δ*` remains an interval, and no incidence count for one stack family gives the
> MCA threshold without an extremality theorem.

Exact computation (validated Rust engine, matches the canonical probe δ*(μ₁₆,k=4)=9/16) of the in-tree far-line
incidence threshold, with the in-tree budget `= q·ε* = (n·2^128)·2^-128 = n`:

> **δ* = ½ + (1/(2ρ) − 1)/n  →  ½**  (exact, validated at ρ=1/4 and 1/8, n=16..24)

## The decisive tension (rigorous)

`epsMCA_ge_far_incidence` (in-tree, axiom-clean): `epsMCA(δ) ≥ far_incidence(δ)/q`. So far-line incidence is a
rigorous LOWER bound on `epsMCA` ⟹ a rigorous UPPER bound on the MCA threshold: `δ*_MCA ≤ δ*_far-line`.
But also `δ*_MCA ≥ Johnson = 1−√ρ` (Johnson radius is list-decodable / achievable). So:

> `1−√ρ = Johnson ≤ δ*_MCA ≤ δ*_far-line → ½`.

For **ρ < 1/4**, `1−√ρ > ½`, so this chain is `Johnson ≤ δ*_MCA ≤ ½ < Johnson` — a **contradiction**. Concretely
ρ=1/8: Johnson=0.646, but δ*_far-line = ½+3/n = 0.625 at n=24 and → ½. So far-line δ* drops *below* Johnson.

## What it means (one of these MUST hold)

1. **The far-line incidence is a Plotkin-type proxy, NOT the MCA δ\*.** The whole #357/#389/#407 identification
   "far-line incidence = δ*" is an approximation valid only at small n (where ½+(1/(2ρ)−1)/n happens to exceed
   Johnson); it **fails asymptotically**. The true MCA δ* (≥ Johnson, the prize target) is a *different, harder*
   object that this computable incidence does not capture — and the BGK/char-sum difficulty lives in *that*
   object, not the (now-shown-easy, → ½) far-line incidence.
2. OR Johnson is not a lower bound for the MCA threshold (MCA is strictly stronger than list-decoding, so δ*
   could be below Johnson), in which case **δ* → ½ REFUTES the floor conjecture** `δ*=1−ρ−Θ(1/log n)` (½ < 1−ρ).
3. OR there is a budget/far-condition normalization subtlety vs the exact ABF26 MCA definition.

## Net (honest, and a course-correction)

My earlier "δ* decouples from BGK / is a computable p-independent quantity" results are real **about the
far-line incidence object** — but this computation now shows that object **→ ½**, which is below Johnson and
therefore **cannot be the prize MCA δ*** (resolution 1, most likely). So the decoupling/p-independence applies
to a *proxy*, and **the prize δ* (≥ Johnson, the floor) is a genuinely different object** that the far-line
incidence does not pin. This re-opens (correctly) what the right computable object for the MCA δ* is — and
re-localizes the prize difficulty to the gap between the far-line proxy (→½, easy) and the true MCA threshold
(≥ Johnson, BGK-hard). The exact formula and the engine are solid; the over-identification of far-line incidence
with δ* is the error this surfaces.

**Concrete next step:** read the exact ABF26 MCA δ* definition (§4.5 `mcaConjecture`) and determine whether the
far-line incidence is (a) a loose upper bound, (b) the LD-side of a bracket, or (c) genuinely δ* (refuting the
floor). The Rust engine can now compute any incidence variant fast to test the correct object.
