# Two literal-threshold exact pins at rate 3/16

Date: 2026-07-09

## New adjacent pin

`LiteralBudgetRateThreeSixteenths.lean` applies the existing KKH26 ceiling-march engine to the
certified order-32 literal-budget field from `LiteralBudgetPin.lean`, now in its adjacent
`r = 7` band.  The exact natural-number band arithmetic is

```text
floor(choose(32, 7) / 7) = 480836,
floor(P / 2^128) = (P - 1) / 2^128 = 1314883,
2^7 * choose(16, 7) = 1464320,
480836 <= 1314883 < 1464320.
```

It proves the unconditional operational pin

```text
mcaDeltaStar (evalCode g 32 5) 2^-128 = 25/32.
```

The code has dimension six and standard RS rate `6/32 = 3/16`.

## Two-scale comparison

`Mu6DeepRung.lean` already proves, over a different certified prime field,

```text
mcaDeltaStar (evalCode g' 64 11) 2^-128 = 51/64.
```

That code has dimension twelve and the same standard RS rate `12/64 = 3/16`.  Hence at the
same normalized error threshold `epsilon* = 2^-128`,

```text
51/64 - 25/32 = 1/64.
```

The module packages both pins, their equal rates, the exact drift, and a named concrete
counterexample.

## Scope

This comparison rules out a universal finite-instance exact identity depending only on
`(rate, epsilon*)`.  It does not isolate length as the cause.  The two fields differ, and so do
their integer bad-scalar budgets:

```text
(P32 - 1) / 2^128 = 1314883,
(P64 - 1) / 2^128 = 1010527601191.
```

It therefore does not refute formulas retaining `n`, `q`, `floor(q * epsilon*)`, finer code
data, or a fixed field-scaling regime.  It also does not address the four asymptotic production
instances.

## Validation

The module typechecks in the stable Lean overlay.  Its four `#print axioms` audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
