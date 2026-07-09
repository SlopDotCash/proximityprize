# δ* #466 — finite moments do not certify the dyadic MGF target (2026-07-08)

## Hypothesis

R185 found strong low mixed-moment evidence for independent real-Gaussian child
periods.  Could finitely many such moments prove the R186 target

```text
avg exp(X/4) ≤ 2 ?
```

R187 tests the generic obstruction: with only finitely many polynomial moment
budgets, a tiny far-tail spike can satisfy all moment constraints while making
the exponential moment enormous.

Probe: `scripts/probes/probe_r187_finite_moments_do_not_certify_mgf.py`.

## Result

For each `K`, allow a one-spike distribution with mass

```text
ε ≤ min_{1≤j≤K} (2j−1)!! / S^j,
```

so that all moments through order `K` are below the `χ²_1`/real-Gaussian
values.  Its exponential contribution is `ε exp(S/4)`.

```text
K  best_spike_mgf_contribution  score
2  1.027e+211 1999.9
3  2.567e+208 1999.9
4  8.985e+205 1999.9
5  4.044e+203 1999.9
6  2.224e+201 1999.9
8  1.084e+197 1999.9
10 8.757e+192 1999.9
12 1.058e+189 1999.9
16 4.012e+181 1999.9
20 4.180e+174 1999.9
```

The optimum runs to the artificial search cap; the phenomenon is unbounded.

## Verdict

Low mixed moments are excellent structural evidence, but they cannot by
themselves prove `MGF(1/4)≤2`.  Any successful proof must include one of:

* a direct exponential/tail inequality;
* a deterministic support cap at the right scale;
* a structural theorem forbidding isolated far-tail spikes, not merely bounding
  finitely many moments.

So the dyadic tower route has split into two honest tasks:

```text
1. Prove the low mixed-moment / angle-equidistribution structure.
2. Prove a genuine exponential tail or no-far-spike theorem.
```

Without (2), the argument loops back to the deep-r Paley/BGK wall.
