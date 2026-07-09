# δ* #466 — multiplicative-order test for normalized monotonicity (2026-07-08)

## Hypothesis

R58/R59 exposed a promising theorem shape for the prize family:

```text
R_{r+1}(μ_n) ≤ R_r(μ_n),
R_r = Σ_{b≠0}|η_b|^(2r) / ((p-1)(2r-1)!!σ^(2r)).
```

R60 asks whether this is a generic multiplicative-subgroup phenomenon or genuinely tied to the
2-power subgroup structure.

Probe: `scripts/probes/probe_r60_multiplicative_order_monotonicity.py`.

## Result

Exact coset-spectrum sweep at `p ≈ order^4`:

| order | type | monotone? | notable ratios |
|---:|---|---|---|
| 9 | odd | yes | `R2=0.6271, R3=0.3503` |
| 12 | even non-2pow | yes | `R2=0.9154, R3=0.8894` |
| 15 | odd | yes | `R2=0.6433, R3=0.3713` |
| 18 | even non-2pow | **no** | `R3=0.9433 < R4=0.9807 < R5=0.9910` |
| 20 | even non-2pow | yes | `R2=0.9494, R3=0.8536` |
| 24 | even non-2pow | **no** | `R3=0.9639 < R4=1.0253 < R5=1.0964` |
| 27 | odd | yes | `R2=0.6539, R3=0.3845` |
| 30 | even non-2pow | **no** | `R2=0.9664 < R3=1.0275 < R4=1.2469` |
| 32 | 2-power | yes | `R2=0.9685, R3=0.9069` |
| 36 | even non-2pow | **no** | `R3=0.9802 < R4=1.0465 < R5=1.1545` |
| 40 | even non-2pow | yes | `R2=0.9748, R3=0.9250` |
| 48 | even non-2pow | **no** | `R3=0.9868 < R4=1.0447 < R5=1.1430` |

Several even non-2-power subgroups violate monotonicity, and some become genuinely super-Wick
(`R_r > 1`).  The 2-power row remains monotone.

## Verdict

The R58/R59 monotonicity survivor is **not** a theorem about all multiplicative subgroups.  It is
at least strongly shaped by the 2-power/cyclotomic structure of the prize family.

This is good news for targeting: a proof of normalized monotonicity cannot be generic subgroup
harmonic analysis.  It should exploit one of the dyadic-specific features:

* antipodal pairing and exact arcsine moments,
* the tower `μ_{2^{a+1}} → μ_{2^a}`,
* 2-power cyclotomic binomials `Φ_{2^m}(X) = X^{2^{m-1}} + 1`,
* or a sign/phase cancellation absent from even non-2-power orders.

The first counterexamples also give a useful adversarial test suite for any proposed proof: it must
explain why orders `24, 30, 36, 48` fail while order `32` succeeds.
