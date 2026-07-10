# R400: support-locator rational fibers (2026-07-10)

Status: scalable rational-fiber theorem axiom-clean; support-three closure template isolated but
its six-rich-line cap is not yet formalized.

## Normalized sparse direction

For a direction supported on `s` evaluation coordinates, let `H` be the monic locator of that
support.  Interpolate the nonzero direction values there by a polynomial `r` of degree `<s`.
Every degree-`<k` codeword fitting one scalar on all support coordinates has the form

```text
c = r0 + gamma*r + H*q.
```

On a zero-direction coordinate `x`, divide by `H(x)` and write

```text
A(x)=r(x)/H(x),   B(x)=(u0(x)-r0(x))/H(x).
```

The zero agreements of `c` are exactly the weighted coordinate points `(A(x),B(x))` lying on
the affine parameter line `B=a+gamma*A`.

## Lean theorem

`Frontier/_R400SupportLocatorRationalFiberBound.lean` proves for every injected field-valued
domain:

```text
deg H = s, r != 0, deg r < s
  => #{x : r(x)=a H(x)} <= s.
```

The proof observes that `r-aH` is nonzero and has degree at most `s`, then injects the fiber into
its polynomial roots.  The axiom audit contains only the standard `propext`, `Classical.choice`,
and `Quot.sound` axioms.

Thus every geometric coordinate point `(A,B)` has multiplicity at most the direction support
size `s`.  This is the scalable algebraic input missing from a purely constant-weight Plotkin
argument.

## Exact support-three campaign

For `[16,4]`, threshold nine, and support three:

* random exact scans found at most two bad scalars;
* adversarial hill climbing over all `17^4=83,521` codewords reached seven bad scalars;
* the exact rational-map census over every support triple and degree-`<3` nonzero numerator has
  maximum fiber profile `(3,3,3,3,1)`;
* this realizes the abstract four-triple configuration and six `t=6` secants exactly.

The probes are:

```text
scripts/probes/probe_rate_quarter_support3_hillclimb.py
scripts/probes/probe_rate_quarter_support3_rational_fibers.py
```

The existing constant-weight Plotkin theorem gives stratum caps

```text
t=7: at most 5 codewords, scalar weight 1;
t=8: at most 2 codewords, scalar weight 3.
```

The remaining `t=6` geometry is a weighted line arrangement of total coordinate weight thirteen,
point multiplicity at most three, and line weight at least six.  The observed sharp candidate is
six lines, attained by the six secants of four triple points.  If this six-line cap is proved, a
mixed weighted-incidence inequality excludes the only scalar-weight endpoint above sixteen,
`(x6,x7,x8)=(6,5,2)`, because

```text
(6*x6+7*x7+24*x8)^2
  <= 13 * (3*(x6+x7+3*x8)^2 + 3*x6+4*x7+45*x8)
```

fails at that endpoint (`14161 > 12935`).  This would close every zero-safe support-three line.

This is not yet the full rate-quarter or delta-star proof.
