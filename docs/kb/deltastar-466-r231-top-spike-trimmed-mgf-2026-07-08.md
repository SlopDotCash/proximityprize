# R231: top-spike trimmed quotient MGF feasibility

Issue: #466. Date: 2026-07-08.

## Question

R230 showed that a simple low-band exponential quotient survival envelope is
too expensive.  The natural repair is to remove the rare top quotient spikes:

```text
pay the top L quotient orbits exactly,
then prove N_res(theta) <= Cbulk * M * exp(-theta/2) + K
only for the residual spectrum.
```

The R231 probe tests whether this shape can recover the quarter-MGF budget
`<= 2`.

## Probe

```text
python3 -m py_compile scripts/probes/probe_r231_top_spike_trimmed_mgf.py
python3 scripts/probes/probe_r231_top_spike_trimmed_mgf.py \
  --medium-max-a 8 --medium-max-index 2048 --min-index 512 --chunk 8192 \
  --trims 1 2 4 8 16 32 64 --taus 0.5 1.0 2.0 4.0 \
  --spike-budgets 0 1 2 --top 24
```

Summary:

```text
cases=1684
feasible_rows=0
best_budget=3.863974
slack=-1.863974
C_req=0.64611544
trim=16
tau=0.5
K=0
```

Best row:

```text
budget=3.8640
C_req=0.64612
trim=16
tau=0.50
K=0
C-witness: n=256, p=202753, M=792, theta=0.502665, count=398
budget-witness: n=64, p=65537, M=1024
```

## Interpretation

Top-spike trimming alone does not rescue the low-band quotient-tail route in
the tested regime.  Paying finitely many top quotient orbits exactly lowers the
required residual bulk constant, but the Fermat-style budget witness remains
too expensive.

This sharpens the residual:

- a finite top-spike reserve is not enough by itself;
- the structured Fermat/generalized-Fermat family must be isolated or treated
  with a different budget;
- any surviving quotient-tail route likely needs a structure-sensitive
  exceptional-family theorem, not just a uniform trimmed survival envelope.

No prize closure is claimed.  This is a negative feasibility result that
prevents the next Lean socket from encoding an insufficient analytic shape.
