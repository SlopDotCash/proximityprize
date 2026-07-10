# Issue #466 R390: characteristic-zero nonzero four-fiber bound

Date: 2026-07-09

R390 assembles Lam--Leung, pairing lifting, the 105 perfect matchings, and R387--R389 to prove

```text
c != 0  =>  rep4_G(c) <= 105 * card(G)
```

for a finite set of `2^k`-th roots in any characteristic-zero field. This is the first rigorous
`O(n)` nonzero block-fiber theorem behind the switching route. The probe-sharp value is
`12n-24`; R390 deliberately proves the coarser constant needed to establish the exponent.

The remaining prize-facing question is finite-field transfer: extra characteristic-`p` relations
must either preserve an `O(n)` fiber bound in the prize regime or be isolated in a signed remainder
whose DC contribution cancels exactly.
