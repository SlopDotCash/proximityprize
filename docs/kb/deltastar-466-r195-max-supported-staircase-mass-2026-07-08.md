# δ* #466 — max-supported staircase mass consumer (2026-07-08)

## Hypothesis

R194 suggests controlling the R193 spike mass through a logarithmic max bound.
R195 supplies the finite-grid bookkeeping:

```text
δ(θ) = 0 for θ > Tmax
Σ_{θ≤Tmax} δ(θ) ≤ M
--------------------------------
StaircaseMass Θ δ ≤ M
```

## Lean artifact

File:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R195MaxSupportedStaircaseMass.lean`.

New predicate:

```lean
def MaxSupportedStaircase (Θ : Finset ℝ) (δ : ℝ → ℝ) (Tmax : ℝ) : Prop :=
  ∀ θ ∈ Θ, Tmax < θ → δ θ = 0
```

Main theorem:

```text
MaxSupportedStaircase Θ δ Tmax
prefix mass below Tmax ≤ M
--------------------------------
StaircaseMass Θ δ ≤ M
```

## Verification

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R195MaxSupportedStaircaseMass.lean
```

R195 passed the fast Lean check in 6 seconds.

## Verdict

The spike route now has a clear Lean chain:

```text
logarithmic max bound
  -> max-supported/prefix staircase mass
  -> R193 spike mass certificate
  -> R192 split budget
  -> R190 quarter-MGF
```

The remaining concrete work is to instantiate the R189 half-grid increments
and prove the prefix telescoping bound from the logarithmic max estimate.
