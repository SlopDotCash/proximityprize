# δ* #466 — R168 dyadic tail-envelope consumer (2026-07-08)

## Purpose

R66/R67 found strong empirical support for the dyadic coset tail envelope

```text
N(T) ≤ M exp(-T/4).
```

The existing S11 lane already proves the analytic bridge

```text
MGFBound ⟹ MomentEnvelope ⟹ CharPEnergyTransferWithSlack ⟹ prize-square bound.
```

R168 adds the concrete Lean-facing target for the new route:

```text
DyadicTailMGFBound(s,t) := MGFBound s t 2 (1/8)
```

This is the conservative MGF consequence one expects from a survival tail of
rate `1/4`: evaluate the exponential moment at half the survival rate.

## Lean Artifact

File:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R168DyadicTailEnvelopeConsumer.lean
```

Theorems:

```text
DyadicClosedFormGridTail
dyadicTailMGF_of_survival_count_ceiling
dyadicTailMGF_of_closedFormGridTail
dyadicTailMGF_of_bin_budget
dyadicTailMGF_of_tower_product_budget
dyadicTailMGF_of_tower_amgm_mgf
momentEnvelope_of_dyadicTailMGF
slack_of_dyadicTailMGF
prize_sq_of_dyadicTailMGF
```

The concrete slack constant is `16`, from `A/c = 2 / (1/8)`.

## Verdict

This does not prove the dyadic tail theorem.  It fixes the downstream contract:

```text
Prove (1 / |s|) * Σ_b exp((1/8) * t_b) ≤ 2
```

for the normalized dyadic period spectrum.

The new count-ceiling theorem makes the residual even more explicit: it is
enough to supply a finite threshold grid, staircase increments `δ`, survival
count ceilings `B`, and the numerical weighted-sum inequality

```text
Σ_θ δ(θ) B(θ) ≤ 2 |s|.
```

Once that residual is landed, the existing S11 machinery delivers the moment
envelope, energy-transfer slack, and prize-square shape without a new analytic
bridge.

R170 is now reflected directly in Lean by `DyadicClosedFormGridTail`: on a
chosen threshold grid, prove

```text
#{b : θ ≤ t_b} ≤ (3/4) |s| exp(-θ/4).
```

Together with the pure weighted-sum inequality for that grid, this implies
`DyadicTailMGFBound`.

R176 is reflected by `dyadicTailMGF_of_bin_budget`: assign each spectrum point
to a bin, bound `exp(t_b/8)` by the bin ceiling, and prove the resulting
pointwise bin-budget sum is at most `2 |s|`.  This is the compensation-law
consumer: high-tail bins are permitted if low bins keep the total exponential
budget under control.

R181 is reflected by `dyadicTailMGF_of_tower_product_budget`: if a parent tower
value is bounded by the sum of its two child values, and the paired child
product budget is at most `2 |s|`, then the parent satisfies the R168 MGF
residual.

R184 is reflected by `dyadicTailMGF_of_tower_amgm_mgf`: the paired product
budget follows from two one-sided child MGF bounds at rate `1/4`, each with
constant `2`, using the pointwise AM-GM inequality `uv ≤ (u²+v²)/2`.

Verified:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R168DyadicTailEnvelopeConsumer.lean
```
