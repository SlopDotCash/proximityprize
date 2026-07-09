# #466 R355 — the explicit six-web is a fixed resultant obstruction

For the non-pairable six-term relation at `p = 16,778,497`, take

```text
f(X) = X^5 + X^6 + X^28 + X^29 − X^3 − X^25.
```

Using `Φ₆₄(X) = X^32 + 1`, exact integer resultant arithmetic gives

```text
Res(Φ₆₄, f) = 134,227,976 = 2^3 · 16,778,497.
```

Thus the observed bad prime is not an unstructured numerical accident: it is
exactly the odd prime divisor of a fixed small-height cyclotomic resultant.
This validates the intended arithmetic architecture:

* enumerate normalized six-web templates;
* attach each template its fixed resultant;
* charge every bad prime to a prime divisor of one resultant;
* compare the resulting distinct-prime count with the prize-window supply.

The local resultant calculation is exact; the remaining global issue is the
number and height of normalized six-web templates at general dyadic order.
