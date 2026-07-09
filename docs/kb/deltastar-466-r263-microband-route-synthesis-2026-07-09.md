# #466 R263: micro-band route synthesis

Date: 2026-07-09

## Current target

After R249-R262, the live main-lane residual route is:

```text
top-five exact contribution
+ trim-five micro-band cap:
    S(0.75) <= 612 / 1485
+ trim-five high-tail cap:
    sup_{theta >= 0.755} S(theta) exp(theta/2) <= 0.6012
```

The micro-band cap is the hard part.

## Refuted explanations

The cap is not explained by:

- low moments up to degree four, even with exact residual maximum (R243);
- threshold-set Fourier structure in quotient index (R244);
- exact scaled-survival monotonicity (R247);
- independent q60 plus thin-band caps (R258);
- coupled linear q60/thin-band tradeoffs (R259);
- simple arithmetic features of `M` or `p = Mn+1` (R260);
- dyadic-level monotonicity (R261);
- low Fourier modes of the unsorted value sequence (R262).

## Surviving interpretation

`S(0.75)` depends only on the vertical value distribution of the normalized
Gauss-period squares after deleting the top five. Index structure can be useful
only insofar as it proves a value-distribution theorem.

The plausible theorem is now direct:

```text
TrimFiveMicroBand:
  for dyadic n >= 256 in the main lane,
  #{x in R_5 : x >= 0.75} <= (612 / 1485) M.
```

The best conceptual reading remains R255's lower-bulk phenomenon: the residual
distribution is more zero-heavy than `Exp(1)` in the middle, while the upper
tail compensates the mean. A proof likely needs an analytic vertical
distribution theorem for Gauss periods, not a combinatorial classification of
bad quotient indices.
