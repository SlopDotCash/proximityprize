# #466 R362 — exact two-shell census at the n=64 bad endpoint

For the folded evaluation lattice at `p = 16,778,497`, exact unordered
multiset enumeration gives (with all positive/negative mass splits included):

```text
reduced L1-6 vectors : 32 unoriented (64 oriented)
  of which 20 arise from the 3+3 split and 12 from 4+2 / 2+4
reduced L1-8 vectors : 528 unoriented across all splits
  (20+96+236+176 from 1+7, 2+6, 3+5, 4+4)
```

The neighboring controls show the distinction:

```text
p=16,777,601 : L1-6 = 0,  L1-8 = 47
p=16,777,729 : L1-6 = 0,  L1-8 = 39
p=16,778,497 : L1-6 = 32, L1-8 = 528 (complete split census)
p=16,778,561 : L1-6 = 0,  L1-8 = 62
```

Thus the R349 reduction isolates a genuinely sparse arithmetic signal: the
bad endpoint is marked by the appearance of the L1-six shell, while L1-eight
relations are present even at nearby good primes and carry only the lower
`s=0` weight. A uniform proof should bound the L1-six shell separately and
charge the generic L1-eight shell to the lower-weight budget.
