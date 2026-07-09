# R259 joint fine-budget refutation

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Question

R258 gave a promising marginal socket for the fine layer

```text
X_64 = lift(X_32) + R_fine.
```

After deleting one fine residual spike, the fine-layer tail constant falls to
about `0.382`.  R259 asks whether this composes into a useful full quarter-MGF
budget when weighted by the actual lifted `X_32` values.

## Probe

New script:

```text
scripts/probes/probe_r259_n64_joint_fine_budget.py
```

It pays the top `trim` fine residual rows exactly and then uses the actual
coarse weight average `mean exp(lift(X_32)/4)` times a fine-layer envelope for
the remaining rows.

## Command

```bash
python3 -m py_compile scripts/probes/probe_r259_n64_joint_fine_budget.py
for trim in 1 2 4; do
  python3 scripts/probes/probe_r259_n64_joint_fine_budget.py \
    --min-index 512 --max-index 12000 --chunk 8192 \
    --trim "$trim" --tau 0.5 --step 0.03125 --top 12
done
```

## Result

The naive joint budget does not close.  It overpays known direct-MGF failure
rows and the Fermat row.

Best among the tested trims:

```text
trim=1:
  worst budget = 2.88684626
  witness M=3193 p=204353
  exact MGF = 2.63206669

trim=2:
  worst budget = 3.67632947
  witness M=1024 p=65537
  exact MGF = 3.26239583

trim=4:
  worst budget = 3.67556366
  witness M=1024 p=65537
  exact MGF = 3.26239583
```

Increasing `trim` makes the Fermat row worse because direct payment of several
large fine residual rows dominates the budget.

## Interpretation

The fine-layer tail socket from R258 is real, but it does not by itself imply
a full MGF bound through this envelope composition.  The obstruction is not an
artifact: several rows have exact full quarter-MGF already above `2`, so they
must be treated by a finite/direct-failure branch or excluded from the
asymptotic lane.

The surviving use of the fine-layer split is therefore conditional:

```text
finite branch:
  classify/directly discharge known MGF-failure rows;

asymptotic branch:
  use X_64 = lift(X_32) + R_fine,
  pay one fine residual spike,
  prove the trimmed fine tail,
  and combine with a cancellation inequality sharper than
  mean(exp(lift(X_32)/4)) * envelope(R_fine).
```

The next proof attempt should search for that cancellation inequality, not a
plain product/envelope composition.
