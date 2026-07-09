# Prize entropy pin: degree parameter refutation

Date: 2026-07-09

## Result

`PrizePinConjecture` in `PrizeEntropyDeltaStar.lean` is false as stated.  Its parameter
`k` is the polynomial degree bound used by `evalCode g n k`, so the code has dimension
`k + 1`.  The entropy expression instead receives `k / n` as its rate.

`PrizeEntropyPinRefuted.lean` gives a machine-checked counterexample at

```text
p = 12289, n = 8, g = 4043, k = 0, epsilon* = 14/12289.
```

The existing unconditional theorem `KKH26DimOne.deltaStar_pin_F12289` proves

```text
mcaDeltaStar (evalCode 4043 8 0) (14/12289) = 3/4.
```

But the historical conjecture supplies rate `0/8 = 0`, and

```text
prizeDeltaStar 0 B = 1
```

for every budget `B`, because binary entropy vanishes at zero.  Thus the claimed equality
would identify `3/4` with `1`.

## Scope

This refutes the Lean definition exactly as written.  It does not refute a corrected
entropy conjecture using the actual rate `(k + 1) / n`, and it does not close or refute any
of the four production prize instances.  Their worst-case list upper bound remains open.

## Related finite pins

`DeltaStarPinsF17N8.lean` adds two independent unconditional operational pins on the
eight-point smooth domain over `F_17`:

```text
degree <= 2, epsilon* in [2/17, 4/17): delta* = 1/4;
degree <= 1, epsilon* in [3/17, 8/17): delta* = 3/8.
```

They combine the five-thirds ratio-pigeonhole good side with explicit pencil bad sides.
They are finite exact pins, not proofs of the entropy formula.

## Validation

The two new modules typecheck, and their `#print axioms` audits contain only `propext`,
`Classical.choice`, and `Quot.sound`.
