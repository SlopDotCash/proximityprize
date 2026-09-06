# #444 DC-subtracted cosh-MGF consumer

## Result

Landed `Research/ProximityPrize/Frontier/DCSubtractedCoshMGF.lean`.

The raw cosh-MGF identity is not the prize object at the saddle because the `b = 0` term contributes
`|G|^(2r)`.  The live #444 mandatory form is DC-subtracted.  The new Lean brick proves the exact
nonzero-frequency identity

```text
sum_{b != 0} cosh(||eta_b|| y)
  = sum'_r ((q E_r(G) - |G|^(2r)) y^(2r) / (2r)!)
```

and the root-free consumer:

```text
DC-MGF(y) <= B, B > 0, y > 0, b0 != 0
  => ||eta_b0|| <= log(2B) / y.
```

## Status

This is a proven consumer, not a proof of the open inequality.  It aligns the cosh/Laplace route
with the DC-subtracted `A_r <= Wick` core instead of the false raw `E_r <= Wick` form.

Validation:

```text
scripts/pg-iterate.sh Research/ProximityPrize/Frontier/DCSubtractedCoshMGF.lean
```

passed axiom-clean modulo the standard foundation axioms reported by Lean (`propext`, etc.).
