# #466 R245: trim-five vertical distribution socket

Date: 2026-07-09

## Surviving hypothesis

The R231-R244 funnel leaves one concrete analytic socket for the main
`n >= 256` lane.

Let `X_j = |eta_j|^2 / sigma^2` be the quotient Gauss-period normalized-square
spectrum, sorted as `X_(1) >= ... >= X_(M)`. Delete the five largest values and
write the residual multiset as `R_5`.

The needed vertical distribution theorem is:

```text
TrimFiveResidualCDF:
  for dyadic n >= 256 and quotient index M >= 512 in the prize lane,
  #{x in R_5 : x >= theta} / M <= 0.6012 * exp(-theta/2)
  for every theta >= 0.75.
```

The live endpoint is equivalent, up to tiny slack, to the first-band cap

```text
#{x in R_5 : x >= 0.75} / M <= 0.4122.
```

## Why this socket

Evidence chain:

- R231: paying exact top quotient values plus a residual tail is feasible.
- R237: top-five mass has stable scaling on the cached main lane.
- R238: residual half-rate tail with `tau=0.75`, `C=0.6012` gives total MGF
  budget `1.995028 < 2`.
- R239/R240: the worst residual tail constant sits at the first band and is
  stable by dyadic level.
- R241: rate `1/2` is forced by the tradeoff; faster rates are killed by rare
  post-trim spikes, slower rates lose MGF budget.
- R242: the endpoint is a middle-bulk percentile theorem, especially the
  residual 60th percentile.
- R243: low moments up to degree four plus the exact residual max cannot prove
  the cap.
- R244: the threshold survivor set is Fourier-uniform in quotient index; there
  is no obvious interval/subgroup bad-set structure.

## Discharge if proven

Together with the existing top-five exact budget socket and the finite
`n=128` exception certificates from R234/R235, `TrimFiveResidualCDF` would close
the current quotient-MGF route to the prize-facing quarter-MGF endpoint.

This is not yet a proof. It is the narrowed analytic theorem that survived the
latest refutation funnel.
