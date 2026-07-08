# #466 R191: tower product-MGF fixed point

Status: exploratory hypothesis.

R190 suggests that the correct dyadic tower target is not a threshold recursion but the paired
product MGF itself:

```text
(1 / M) * sum_i exp(left_i / 8) * exp(right_i / 8) <= 2.
```

The Lean consumer `_R168DyadicTailEnvelopeConsumer.lean` already proves this implies the R168
parent MGF residual. Numerically the product budget appears much sharper:

```text
(1 / M) * sum_i exp((left_i + right_i) / 8) ~= 4/3.
```

For independent real-Gaussian periods, `left` and `right` are independent `chi^2_1`, and therefore
`E exp((X+Y)/8) = (1 - 2*(1/8))^-1 = 4/3`.

Probe:

```bash
python3 scripts/probes/probe_r191_tower_product_mgf_fixed_point.py
```

Potential prize route: prove a finite-field paired-product MGF bound at rate `1/8` with any
constant `< 2`, ideally by a finite-harmonic equidistribution theorem for adjacent child cosets.
This would bypass the false global MGF domination and the awkward inherited/balanced threshold
recursion.

## Run result

```text
independent chi-square product targets:
  rate=0.062500 target=1.14286
  rate=0.125000 target=1.33333
  rate=0.166667 target=1.5
  rate=0.250000 target=2

n p prod1/16 prod1/8 prod1/6 prod1/4 parent1/8 ratio_to_4/3
16  1048609    1.140763 1.320899 1.470488 1.87188 1.151858 0.990674
32  16777601   1.141788 1.326782 1.484013 1.92493 1.153238 0.995087
64  16778497   1.142336 1.330273 1.492847 1.9712  1.154140 0.997705
128 268437889  1.142585 1.331620 1.495712 1.97813 1.154323 0.998715
256 16777729   1.142702 1.332294 1.497253 1.98389 1.154376 0.999220
```

The product MGF approaches the independent `chi^2_1 + chi^2_1` fixed point from below at all
tested rates. This turns the open target into a concrete local equidistribution/MGF statement:
prove enough adjacent-child joint Gaussianity at rate `1/8` to get any uniform constant below `2`.
