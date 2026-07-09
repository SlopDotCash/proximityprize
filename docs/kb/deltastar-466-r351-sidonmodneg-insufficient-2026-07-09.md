# #466 R351 — Sidon-mod-negation does not eliminate the L1-six shell

The natural attempt to discharge R350 using `SidonModNeg` fails. An exact
sample at `p = 16,778,497` produces the nontrivial endpoint relation

```text
  e_3 + e_5 + e_6 + e_25 + e_28 + e_29 = 0
```

with signs grouped as three positive and three negative subgroup terms (the
displayed indices are folded after antipodal reduction). Its coefficient
pattern is `(+1,+1,+1,-1,-1,-1)`, not the doubled pattern `(+2,-1,-1)`.

`SidonModNeg` controls four-term coincidences and the doubled `2a=b+c`
configuration, but it says nothing about genuine three-sum collisions. Thus
the correct shell input is a `B₃`/three-sum uniqueness or weighted 3-sum
incidence theorem. This explains why the subgroup can be Sidon-mod-negation
while its depth-four energy is already K-bad.
