# Issue #464: Jacobi finite-prefix turnover gate

Date: 2026-06-25.

Status: **form-D guardrail**, not a delta-star proof.

## Inputs Checked

- Live issue #464, where the Jacobi-turnover face is listed as equivalent to the same BGK/Paley
  wall.
- `docs/kb/deltastar-DOSSIER-v2-2026-06-22.md`, especially the form-D notes saying the edge is
  controlled by recurrence-coefficient turnover depth.
- Existing Jacobi frontier files around edge bounds and the Hermite-turnover model.

## Verdict

The form-D Jacobi/Toda route needs a global recurrence-coefficient turnover theorem, not just
low-depth evidence.  The finite gate is:

```text
global coefficient ceiling = prefix ceiling + tail ceiling.
```

The Lean file proves the exact countermodel.  For any checked prefix `k <= K` and any larger height
`H > B`, the sequence

```text
b_k = 0 for k <= K,
b_{K+1} = H
```

satisfies the prefix bound but violates the global bound at the next coefficient.

## Lean Result

The frontier file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_JacobiFinitePrefixTurnoverGate.lean
```

defines:

```lean
PrefixBound
TailBound
GlobalBound
```

and proves:

- `globalBound_iff_prefix_and_tail`: a global ceiling is exactly a prefix ceiling plus a tail
  ceiling.
- `prefixBound_not_force_global`: prefix-only evidence does not imply the global ceiling.
- `tailBound_fails_for_prefixSpike`: the spike countermodel pinpoints the missing tail theorem.
- `finitePrefixTurnoverGate`: the bundled consumer/refutation package.

## Consequence for #464

Jacobi coefficients are a useful sharper diagnostic for the Paley spectrum, but a proof of the
floor cannot stop at "the first several coefficients follow the Hermite law" or "the observed
turnover happens near log p."  It must prove that no coefficient beyond the checked prefix re-enters
above the prize-scale ceiling.

This is the same wall in form-D language: the missing input is a genuine tail/turnover theorem for
the char-p Hankel ratios, equivalent to controlling moments at the relevant depth.

## What New Math Would Look Like

The useful theorem is not another finite prefix computation.  It must have the form:

```text
for every k > K_prize, b_k <= B_prize,
```

where `K_prize = O(log p)` and `B_prize` is the recurrence-coefficient ceiling that implies
`M <= C * sqrt(n * log(p/n))`.

Equivalently, the proof must show that after the observed Hermite-like rise, the char-p Jacobi
coefficients cannot re-enter above the prize edge.  That is a global tail/turnover theorem for the
actual Gauss-period measure, not a consequence of finite low-depth Hankel arithmetic.
