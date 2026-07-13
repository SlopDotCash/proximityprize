# G260: the quotient origin is a gauge, so no W-intrinsic origin anchor pins the covariance

Date: 2026-07-13
Issue: #466
Status: axiom-clean route no-go, not prize closure

## Question

After G258 (complete Fourier-value multiset + positivity + support cardinality cannot pin the
fixed-row covariance, because quotient units relabel the physical profile) and G259 (Fable: the full
bispectrum and every translation-invariant higher moment cannot pin it either, because the target
covariance is not translation invariant while those moments are), the single named open repair was:

Does a W-intrinsic, sponsor-uniform ORIGIN ANCHOR exist that recovers the absolute quotient origin
from `W` alone, independent of the rank rows `R_r`?

## Structural answer

No. The choice of "zero coset" in the sponsor quotient is a gauge. Let the cyclic shift group
`Z/mZ` act on physical profiles by `(shift c W) x = W (x - c)`. Then:

- Total mass is preserved: `sum_x (shift c W) x = sum_x W x` (`shift_sum_eq`).
- The correlation depends only on relative placement:
  `sum_x (shift c W)(x) R(x) = sum_x W(x) (shift (-c) R)(x)` (`shift_corr_eq`).
  There is no distinguished origin in the pairing; only the offset of `W` against `R` matters.
- The fixed-row centered covariance

  ```text
  centeredCov m W R = m * sum_x W(x) R(x) - (sum_x W(x)) (sum_x R(x))
  ```

  is therefore genuinely shift-NON-invariant.

Every origin marker computable from `W` alone is translation-covariant and falls into one of two
classes, neither of which can select the physical origin `R_r` uses:

- INVARIANT markers (autocorrelation values, `|DFT|`, the value multiset, any degree-`k` moment):
  `M(shift c W) = M(W)`. The identity and a sign-reversing shift receive the SAME value.
- EQUIVARIANT markers (the argmax of a unique extremum, any "distinguished residue" rule, `DFT`
  phases): `M(shift c W) = M(W) + c`. "Align `M` to `0`" is a GAUGE FIXING that maps the whole shift
  orbit to ONE canonical profile, so it cannot tell the covariance which physical origin is real.

## Exact witness (Z/7, decide-checked)

`W = ![2,0,1,1,1,1,0]`, row `R = ![0,0,0,1,1,1,0]`, shift `c = 2`:

```text
centeredCov 7 W R           = 7*3 - 6*3 =  3  > 0   (base_cov_pos)
centeredCov 7 (shift 2 W) R = 7*2 - 6*3 = -4  < 0   (shifted_cov_neg)
```

The SAME fixed row is sign-reversed by a single origin shift. `W` has its unique maximum at `0`,
`shift 2 W` at `2 = 0 + 2` (argmax equivariance, `argmax_base` / `argmax_shifted`), and the two
argmax-gauge canonical forms coincide exactly (`gauge_canonical_forms_coincide`): both equal
`![2,0,1,1,1,1,0]`. Two profiles with the same argmax-gauge canonical form, opposite covariance sign
against the same row. Any decision procedure factoring through that canonical form is blind to the
sign. Packaged as `origin_anchor_gauge_nogo`.

The probe `scripts/probes/g260_origin_anchor_gauge_nogo.py` verifies the argmax-gauge collapse over
the WHOLE shift orbit universally (random profiles, all shifts) and shows simultaneous `r=5,6`
sign-reversing shifts persist at `~25%` of all nontrivial shifts as the support fraction thins to
`0.03` (prize scale). Exact integer arithmetic, no FFT, no `/tmp` dependency.

## Honest scope

Route no-go, not a Jacobi covariance estimate and not a prize closure. It closes the origin-anchor
repair G259 left open. The rank weight is the standard structural surrogate used across G245-G259 (not
the literal G245 Newton coefficient); the tested result is structural (gauge covariance of every
`W`-marker versus shift-non-invariance of the target), stable across the surrogate, not a numerical
covariance estimate.

The missing datum is absolute row placement itself, equivalently the original joint sponsor-prime
BGK/Paley covariance

```text
Re sum_{chi != 1} What(chi) * conjugate(Rhat_r(chi)),  r=5,6,
```

proved directly against the row label rather than through any marginal, higher-moment, or
origin-marker shortcut. CORE remains OPEN / ON-BGK.

## Artifacts

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G260OriginAnchorGaugeNoGo.lean`
- `scripts/probes/g260_origin_anchor_gauge_nogo.py`
- DISPROOF entry `[466-G260-origin-anchor-gauge-nogo]`
