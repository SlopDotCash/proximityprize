# Critique Of The SDP Loop: Degree 2 Needs Logarithmic Autocorrelation

**Date:** 2026-06-27
**Issue:** #464
**Loop:** criticize the previous autocorrelation-SDP essay and prove the exact quantitative gap.
**Verdict:** the degree-2 SDP is a real partial power saving, but it cannot prove the prize from
ordinary Weil/Jacobi off-diagonal autocorrelation. A prize proof needs logarithmic off-diagonal
control or genuinely high-order phase structure.

## What The Previous Essay Got Right

`deltastar-464-sdp-container-critical-loop-2026-06-27.md` identified a useful change of basis:
Gaussian periods are a DFT of the normalized Gauss-sum phase vector. This makes the house problem
look like a deterministic flat-polynomial problem. The degree-2 SDP/autocorrelation envelope

```text
||DFT(a)||_infty^2 <= m + (m - 1) * B
```

is not phase-blind in the same way as degree-1 Delsarte/Parseval. If a Weil/Jacobi input gives
`B = C * sqrt(m)`, the resulting house bound beats the classical completion scale `sqrt(p)`.
That is a genuine partial improvement.

## What It Overstated

The essay still left room for a misleading interpretation: maybe the degree-2 envelope is close
enough, and maybe constants or a sharper Jacobi estimate push it to the prize. That is false. The
missing factor is not a constant. It is the gap

```text
sqrt(m)  versus  log(m).
```

At the deployed index `m = 2^128`, that is `2^64` versus about `88.7`.

## New Lean Socket

The new file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_AvSDPPrizeGap.lean
```

proves the exact arithmetic obstruction.

Definitions:

```text
degreeTwoEnvelope(m,B) = m + (m - 1) * B
prizeEnvelope(m,C)     = C * m * log(m)
```

Theorems:

- `offdiag_le_log_of_degreeTwo_le_prize`: if the degree-2 envelope is at prize scale, then
  `B <= C * (m/(m-1)) * log(m)`.
- `sqrt_le_log_of_weil_scale_degreeTwo_prize`: if `B = Cweil * sqrt(m)`, then any degree-2-SDP
  proof of the prize forces

```text
sqrt(m) <= (Cprize/Cweil) * (m/(m-1)) * log(m).
```

So the degree-2 route can reach the prize only after replacing the natural `sqrt(m)` off-diagonal
bound with a logarithmic bound. That replacement is exactly the flat-polynomial/Paley problem.

## Consequence

The degree-2 SDP is not the solution. It is a useful intermediate bracket:

```text
sqrt(n log p)  <<  degree-2 SDP scale  <<  sqrt(p).
```

But it has the wrong terminal exponent. It moves the problem from "bound one additive character
sum over `mu_n`" to "prove the explicit Gauss-sum phase vector has random-flat DFT sup." That is
the same core in a sharper coordinate system.

## What New Math Would Have To Look Like

The next viable tool cannot merely improve the constant in a Weil-scale autocorrelation theorem.
It must reduce the effective off-diagonal budget from `sqrt(m)` to `log(m)` or bypass the L1
autocorrelation envelope entirely.

Three possible shapes remain:

1. **High-order autocorrelation entropy.** Use Hasse-Davenport and Jacobi cocycle identities to show
   that many autocorrelation lags cannot be simultaneously large. This is stronger than bounding
   each lag by `sqrt(m)`.
2. **A deterministic flat-polynomial theorem for Gauss phases.** Prove directly that the normalized
   Gauss-sum phase vector has `||DFT||_infty^2 = O(m log m)`, using arithmetic cocycles rather than
   probabilistic Salem-Zygmund typicality.
3. **Worst-case incidence structure.** Avoid the DFT entirely by proving the `OpenCoreConditionalPin`
   incidence bound over every far stack. The container attempt shows this cannot be a generic
   hypergraph-container theorem; it must use RS algebra beyond scalar codegree.

## Verification

```bash
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_AvSDPPrizeGap.lean
```

Result: `OK (18s)`, with the expected small axiom audit and no `sorryAx`.

## Net

This loop refutes the optimistic degree-2-SDP reading while preserving its genuine contribution.
It gives a precise threshold for any future SDP/autocorrelation proof: either prove logarithmic
aggregate off-diagonal control, or leave degree 2 behind.
