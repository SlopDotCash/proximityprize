# R229 parameterized quotient-envelope endpoint

Date: 2026-07-08
Issue: #466 / Proximity Prize

## Purpose

R228 refuted the universal quotient envelope with constants `(3/5, 2)`.
R229 removes that hardcoding from the formal bridge.  It proves that any true
quotient envelope

```text
#{quotient cosets with X >= theta}
  <= Cbulk * ((# nonzero frequencies) / |G|) * exp(-theta/2) + Kquot
```

lifts to the raw nonzero-frequency envelope

```text
Cbulk * (# nonzero frequencies) * exp(-theta/2) + Kquot * |G|
```

and then feeds the existing generic R219 prize endpoint.

## Lean artifact

File:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R229ParamQuotientEnvelopePrizeEndpoint.lean
```

Main definitions/theorems:

```text
ParamQuotientEnvelope
paramQuotientEnvelope_scale_le_raw
nonzeroNormalizedSqGridTail_param_scaled_of_quotient
prize_sq_of_quotient_param_tail
prize_sq_of_natural_quotient_param_tail
```

Verification:

```bash
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R229ParamQuotientEnvelopePrizeEndpoint.lean
```

Result:

```text
✅ OK (73s)
axioms: [propext]
```

## Empirical repair targets

The R228 medium-plus-large stress command

```bash
python3 scripts/probes/probe_r228_natural_quotient_tail_sweep.py \
  --medium-max-a 10 --medium-max-index 256 \
  --large-max-n 256 --large-max-p 120000000 --large-primes-per-start 1 \
  --chunk 32768 --top 12 --step 0.5 --c-bulk 0.61 --spike-budget 3.0
```

survived:

```text
tested=479
violations=0
max_excess=-0.078631
```

The alternative `(Cbulk, Kquot) = (0.6, 4)` also survived the same sweep:

```text
tested=479
violations=0
max_excess=-0.569145
```

Earlier medium-only sweeps showed `(0.6, 3)` fails and `(0.61, 3)` survives
on `a <= 11, M <= 512`.

## Interpretation

R229 is not a proof of the analytic tail law.  It is the formal endpoint needed
after R228: the prize bridge can now consume repaired quotient laws without
new Lean plumbing.  The next analytic target should optimize between:

- `(0.61, 3)`, which perturbs the bulk constant but keeps the spike budget near
  the original shape;
- `(0.6, 4)`, which preserves the half-rate bulk coefficient but increases
  the additive quotient spike allowance.

The weighted-grid budget remains the decisive downstream constraint.
