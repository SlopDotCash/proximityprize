# #466 R315: kernel relation to resultant weld

## Result

`Frontier/_R315KernelRelationResultantWeld.lean` converts every realized R314 relation
`d : Fin(2^k) -> Z` into

```text
P_d(X) = sum_j d_j X^j.
```

It proves:

```text
coeff(P_d,j) = d_j,
d != 0  =>  P_d != 0,
deg(P_d) < 2^k,
aeval(g,P_d) = evalVec(g,d).
```

Combining R314's `|d_j| <= 2r` with FS3 gives the following unconditional package.  If
`2r <= 2^b`, `g^(2^k) = -1`, and `d` is a realized collision relation in characteristic
`p`, then there is an integer annihilator `N` such that

```text
N != 0,
N <= 2^((k+1+b) * 2^(k+1)),
p divides N.
```

The annihilator is the absolute value of the resultant of `X^(2^k)+1` and `P_d`.

## Consequence for the prize route

The exact collision surplus now has the chain

```text
rEnergy - shadowEnergy
  = sum over realized d of relationMass(d),

realized d
  => d != 0, height(d) <= 2r, evalVec(g,d)=0
  => p divides a nonzero explicitly bounded cyclotomic resultant N(d).
```

No named arithmetic hypothesis remains in this conversion.  What remains is the genuinely
hard fixed-prime counting statement: bound the total `relationMass(d)` among bounded
relations whose resultants are divisible by the selected prize prime.  The existing FS1--FS6
ledger controls this after averaging over primes; the prize requires a strong bound at one
specified splitting prime.

## Validation

```text
./scripts/pg-iterate.sh \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R315KernelRelationResultantWeld.lean
```

passed on 2026-07-09 with no `sorryAx`.
