# G173: the `p > n^4` primitive-relation transfer threshold is false

Date: 2026-07-11
Issue: #466
Status: axiom-clean exact counterexample, CORE remains open

## Question

The G105 suppression probe found no primitive disjoint equal-sum 4-subset pairs for `mu_12`, `mu_16`, and `mu_20` at three primes just above `n^4`. It then suggested that, modulo a characteristic-p Lam-Leung transfer, all primitive packet masses vanish and the padded-collision ladder collapses to Wick.

The decisive question is whether field size `p > n^4` can supply that transfer at a dyadic subgroup, independently of the deployed prime.

## Exact answer: no

Take

```text
n = 64
p = 17318209 > 64^4
omega = 7937154 in ZMod p, order(omega) = 64.
```

Exact modular evaluation gives

```text
omega^52 = 5663213
omega^57 = 17079628
omega^58 = 5424631
5663213 + 17079628 = 5424631 + 1 mod p.
```

The normalized triple `(a,b,c) = (omega^52,omega^57,omega^58)` solves `a+b=c+1`, and it is outside all three characteristic-zero Mann families:

```text
a != 1,  b != 1,  not (c = -1 and b = -a).
```

Therefore it belongs to G136's literal `accidents(mu_64)` set. `_G173PrimitiveTransferThresholdRefuted.lean` kernel-checks the primality, exact order, power evaluations, relation, subgroup membership, and non-lawfulness. This is a genuine primitive signed four-term characteristic-p relation above `n^4`.

It is not a new isolated numerical phenomenon. The existing wf-S7 resultant probe identifies the underlying signed polynomial

```text
X^8 + X^13 - X^14 - X^20
```

whose cyclotomic norm is divisible by `p`; its Galois closure has 1024 signed configurations in 32 full orbits of size `phi(64)=32`. The existing `_AvW3G_GateClosesQuadraticExcess.lean` records the same prime's depth-three wraparound excess `W_3=1658880`.

## Why the small G105 zero cells are nonbinding

The new exact audit `probe_g173_primitive_depth4_production_scaling.py` reproduces a real structural signal at the production exponent `beta=158/30`:

```text
n=16: subgroup primitive depth-4 = 0
n=32: subgroup primitive depth-4 = 0, random control = 7
n=64: subgroup primitive depth-4 = 0, random control = 51
```

The subgroup's many depth-4 collisions are all reducible through depth two. That is useful evidence about one rung, but it cannot establish a uniform transfer across primitive lengths. G173's depth-two accident already falsifies the proposed size threshold.

There is also a basic scale mismatch. There are `C(n,4)` four-subsets, so a random birthday model for equal 4-subset sums has scale

```text
C(n,4)^2 / (2p) = Theta(n^8/p).
```

At the deployed exponent `p=n^(158/30)=n^5.266...`, that ambient scale grows as `n^2.733...`; `p>n^4` is not an unsaturated threshold for pair collisions. The observed depth-4 suppression is special subgroup reducibility, not a counting consequence of field size.

## FS15-FS18 and literature integration

Lam-Leung and Mann classify vanishing sums of roots of unity in characteristic zero. Passing a signed relation to characteristic `p` requires proving that `p` does not divide the corresponding nonzero cyclotomic norm/resultant.

FS16 proves the sharp generic envelope

```text
|Res(X^(n/2)+1,g)| <= coeffMass(g)^(n/2).
```

For fixed signed weight `L`, this only excludes a prime when `p > L^(n/2)`, an exponential threshold in `n`. The production prime is polynomial in `n`, `p=n^(~5.27)`, exponentially below `L^(n/2)` for every fixed `L>=2` once `n` is large. FS15/FS17 then show that almost-all-prime Wick ladders are useful only outside the resultant bad set, while G64 proves the deployed deep ladder is forced exceptional. FS18's odd/even characteristic-zero taxonomy does not change this divisibility obstruction.

Thus a production transfer must be prime-specific nondivisibility, not a theorem from `p>n^4` or from three small zero cells.

## Binding conclusion

G105's literal zero-triple/resultant interface remains valid, and its three depth-4 zero samples remain reproducible. The extrapolation to total primitive suppression is refuted. The correct frontier is exactly G136's statement: at rung two, each certified production prime must be checked for accidents, and the production anchor is equivalent to `#accidents <= 3`. At higher rungs, primitive finite-characteristic packet mass remains the weighted kernel-relation/BGK wall.

No δ* closure is claimed.
