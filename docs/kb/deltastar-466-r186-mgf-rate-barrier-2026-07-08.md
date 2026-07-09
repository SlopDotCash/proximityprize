# δ* #466 — MGF rate barrier for the dyadic tower route (2026-07-08)

## Hypothesis

R184 showed that the R182 paired child product budget can be bounded by a
one-level child MGF at rate `1/4`:

```text
avg exp(left/8) exp(right/8)
  ≤ sqrt(avg exp(left/4) · avg exp(right/4)).
```

R186 checks whether one can demand a stronger one-level MGF invariant, or
whether `1/4` is already near the natural edge.

Probe: `scripts/probes/probe_r186_mgf_rate_barrier.py`.

## Result

```text
n p kind maxX mgf0.125 mgf0.167 mgf0.25 mgf0.333 mgf0.5
32 32993 spike 17.636 1.165 1.249 1.523 2.162 10.76
64 16778497 spike 27.584 1.154 1.224 1.414 1.766 9.304
128 268437889 control 23.688 1.154 1.224 1.410 1.713 3.809
256 16777729 control 16.587 1.154 1.224 1.409 1.701 3.291
512 262657 high 16.168 1.157 1.233 1.467 1.992 8.642
```

## Verdict

The rate `1/4` is robustly below the target budget `2`, with measured values
around `1.4..1.5`.  But `1/3` is already close to `2` and can exceed it in a
spike cell; `1/2` is completely false.

So the proof target should be:

```text
Dyadic MGF(1/4) bound:
  avg_C exp((1/4) |η_C|²/σ²) ≤ 2.
```

This single-level theorem would imply the tower product budget by Cauchy/AM-GM
and then feed the R168 consumer.  Stronger exponential-rate claims are not the
right target.

Honest scope: `MGF(1/4)≤2` is still a tail theorem, but it is now a sharply
calibrated finite-rate statement rather than an overstrong global
sub-Gaussian claim.
