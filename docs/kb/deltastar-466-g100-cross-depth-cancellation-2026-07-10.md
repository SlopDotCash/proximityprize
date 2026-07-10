# G100: nonnegative per-depth caps lose cross-depth cancellation

Lean artifact:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G100PerDepthCenteringCancellation.lean`.

G96 correctly proves that centered bounds at every maximal-cancellation depth imply
`DCEnergyBound`. G100 red-teams the stronger description of that interface as “exact.”

For one depth define the signed integer anomaly

```text
A_s = q * equalSumFiber_s - populationFiber_s.
```

G100 proves the lossless identity

```text
sum_s A_s = q * sum_s equalSumFiber_s - sum_s populationFiber_s
```

and the corresponding exact global inequality. Negative anomalies are meaningful: an
under-populated depth cancels an over-populated depth in the global DC-subtracted moment.

The G96 localized hypothesis instead asks for natural caps satisfying

```text
q * equalSumFiber_s <= q * cap_s + populationFiber_s
```

at every depth. This charges the positive part of each anomaly separately. G100 gives a
kernel-checked two-bin countermodel:

- anomalies are `+2` and `-2`;
- the aggregate anomaly and global Wick allowance are zero;
- every nonnegative per-bin cap family satisfying the binwise bounds has positive total cap.

Therefore G96 remains a valid sufficient consumer, but its nonnegative per-depth caps are not
necessary and are not equivalent to the global wall. A lossless depth method must retain signed
cross-depth cancellation or prove independently that negative-depth compensation is unnecessary.

`scripts/pg-iterate.sh` passes. All five declarations use only accepted foundational axioms; no
`sorryAx`.
