# G139 accident quantization consumer, 2026-07-11

Issue: #466. Branch: `research/proximity-prize` only.

Fresh G56 analysis sharpened the G136 rung-2 accident target.  G136 had already proved the
production anchor equivalent to `#accidents <= 3`.  G139 observes that, once normalized by
`t = y/x` and quotienting by the inversion symmetry `t ~ t^-1`, each non-lawful fiber excess is
quantized in multiples of four:

- a regular fiber with `c` inversion-pairs contributes `4c(c-1)`;
- the distinguished fiber containing the singleton `{1}` and `c` inversion-pairs contributes
  `4c^2`.

The formal consumer is
`ArkLib.ProximityGap.Frontier.G139AccidentQuantizationConsumer.production_rung2_anchor_iff_no_accidents_of_four_dvd`:
if `4 | #accidents(mu_(2^30))`, then the production rung-2 anchor is equivalent to
`#accidents(mu_(2^30)) = 0`, not merely `<= 3`.

This is not a closure of the prime-specific wall.  The remaining exact target is to prove the
modulus-four/inversion-fiber theorem for the concrete map `t -> (1+t)^(2^30)` and then certify the
zero-accident/squarefree-discriminant condition at the first prize prime.
