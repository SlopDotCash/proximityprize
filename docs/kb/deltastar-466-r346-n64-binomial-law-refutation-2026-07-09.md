# #466 R346 — the single-binomial saturation law fails at the first n=64 endpoint

Date: 2026-07-09

## Result

The proposed universal `BinomialBadPrimeLaw` cannot be used as stated.  In the
prize window for `n = 64`,

```text
p = 16,778,497 = 64^4 + 385
```

is prime, `p ≡ 1 (mod 64)`, and the exact depth-four subgroup-energy census gives

```text
E4^0 = 1,602,260,800
W4  = 13,547,520
A4/E4^0 = 1.0591...
```

so it is K-bad for the `K = 1.05` threshold.  The simple norm family
`p | (c^32 + 1)` does not explain this instance: direct modular tests find no
such witness for `2 ≤ c < 20`.

This does not refute the existence of a short *multi-generator* recurrence web.
It does refute the stronger route claim that every bad endpoint is saturated by
one dominant binomial recurrence.  The R325 max-coordinate lemma remains valid,
but its saturation hypothesis must be replaced by a web/ideal statement, or the
proof must charge the non-binomial residual separately.

## Verification

The exact energy was computed by the same finite convolution used in
`scripts/probes/probe_466_d4_structure.py`; the R322 and R324 Lean files still
validate with `scripts/pg-iterate.sh`.
