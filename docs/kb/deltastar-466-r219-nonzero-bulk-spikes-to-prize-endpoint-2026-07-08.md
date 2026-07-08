# δ* #466 — R219 nonzero bulk-plus-spikes to prize endpoint

R219 specializes the R218 survival-grid endpoint to the half-rate
bulk-plus-spikes tail envelope:

```text
#{b ≠ 0 : θ ≤ ‖η_G(b)‖² / σ²}
  ≤ Cbulk * #(b ≠ 0) * exp(-θ/2) + Kspike.
```

Together with a staircase dominance certificate and the weighted budget

```text
Σ_θ δ(θ) * (Cbulk * #(b ≠ 0) * exp(-θ/2) + Kspike)
  ≤ 2 * #(b ≠ 0),
```

the theorem lands the concrete nonprincipal R168/S11 squared prize bound for
the normalized dilation parent.

It also records the literal `(3/5, 2)` specialization.  As noted in R216, raw
frequency carriers may need a spike budget scaled by coset multiplicity; the
literal specialization is appropriate when spikes are counted as individual
carrier elements.

Verified command:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R219NonzeroBulkSpikesToPrizeEndpoint.lean
```

Output:

```text
'ArkLib.ProximityGap.Frontier.R219NonzeroBulkSpikesToPrizeEndpoint.prize_sq_of_nonzero_normalizedSq_halfRate_bulkPlusSpikes_tail' depends on axioms: [propext,
'ArkLib.ProximityGap.Frontier.R219NonzeroBulkSpikesToPrizeEndpoint.prize_sq_of_nonzero_normalizedSq_threeFifths_plus_two_tail' depends on axioms: [propext,
OK (31s) — ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R219NonzeroBulkSpikesToPrizeEndpoint.lean
```

Readout: the dyadic concentration route is now reduced to proving the actual
half-rate nonprincipal normalized-square survival envelope and its weighted
grid budget.
