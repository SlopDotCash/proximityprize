# Issue #466/#505 G89: all-depth Wick assembly under per-depth budget caps

Date: 2026-07-10

Every prior corrected-padding absorption result (G79S, G81, G82, and the reported G86/G88
counted-decoder chain) spends the full production Wick budget `(2r-1)!! * n^r` on ONE primitive
depth at a time. A δ*-facing energy statement must control the sum over all depths
`s = 0, …, r` at once. G89 closes that assembly gap.

## Results (`Frontier/_G89AllDepthWickAssembly.lean`, all axiom-clean)

- `depthBudgetCap n r J s`: the even-split per-depth budget cap
  `(r+1) * (J * (r.descFactorial s)^2 * (r-s)!) ≤ (2r-1)!! * n^s`, with monotonicity in `J`.
- `allDepth_correctedSectors_le_fullWick` (**headline, general**): if for every `s ≤ r` the
  depth-`s` sector mass fits `correctedPadEnvelope n r (J s) s` and `depthBudgetCap n r (J s) s`
  holds, then `∑_{s=0}^{r} W s ≤ (2r-1)!! * n^r`. ℕ-clean proof by the `(r+1)`-multiplication
  trick (no division).
- `depthBudgetCap_of_shallow`: for `2s ≤ r+1`, the G79S/G81-style normalized condition
  `(r+1)*J*r^s ≤ n^s` implies the cap.
- Production kernel checks at `(n, r) = (2^30, 110)` (budget split 111 ways):
  - `production_cap_zero/one/two`: the caps hold with the CRUDE universe counts `J = n^(2s)` at
    depths 0, 1, 2 (sharpens G82's unsplit depth-two calibration);
  - `production_cap_three`: the cap holds with the elementary equal-sum fiber count `J = n^5`;
  - `production_cap_four_equalSum_fails`: the equal-sum fiber count `n^7` FAILS the depth-4 cap;
  - `production_cap_four_freeOrbit`: G83's free-orbit quotient count `J = n^6` PASSES the
    depth-4 cap even after the 111-fold split — the depth-4 rescue survives the all-depth
    assembly (concurrent-swarm sharpening, verified in the same landing).
- `production_allDepth_absorbed_of_deep_caps` (**headline, production**): given the envelope
  bounds at all 111 depths, shallow counts bounded by their elementary values (crude universe at
  depths ≤ 2, equal-sum fiber at depth 3, free-orbit equal-sum at depth 4), and the deep caps
  for `5 ≤ s ≤ 110` as a named hypothesis, the TOTAL mass over all depths fits the single
  production Wick budget `219!! * (2^30)^110`.

## What this changes

The combinatorial superstructure (decoder, padding, orbit bookkeeping, per-depth absorptions)
now composes into ONE production statement whose only open input is the family of deep caps
`5 ≤ s ≤ 110`. Depths 0–4 are fed unconditionally by elementary counting; depth five is the
first depth where genuinely new cancellation is mandatory (matching the reported G86 depth-five
constant-gap frontier). The open analytic wall is unchanged but is now consumed through a single
named interface.

## Honest scope

- The deep caps for growing `s` ARE the square-root-scale cancellation wall; no claim they hold.
- Important semantic caveat for consumers: at deep depths the caps are provably UNSATISFIABLE by
  raw sector cardinality (pigeonhole gives ≥ n^(2s)/p equal-sum pairs, which exceeds the cap for
  large `s`), so `J`/`W` must be instantiated with normalized/weighted masses (the 1/p-scale
  relation weighting), exactly as in the DC-subtracted moment. The theorem is agnostic (`J`, `W`
  are abstract ℕ); the instantiation choice is the consumer's obligation.
- The per-depth envelope hypothesis is the counted-decoder bound (reported G88), consumed as an
  interface; CORE remains OPEN / ON-BGK.

## Verification

`scripts/pg-iterate.sh` passes (13 s). Axiom audit: only `propext`, `Classical.choice`,
`Quot.sound` across all nine audited declarations.

Also repaired in the same landing: `ArkLib.lean` was stale — tracked files
`_G86CoreOccurrenceEmbedding.lean` and `_G87CorrectedPaddingDecoder.lean` were missing from the
generated import list (the untracked-file guard had blocked regeneration for every agent).
