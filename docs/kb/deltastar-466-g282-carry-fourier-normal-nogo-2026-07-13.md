---
id: deltastar-466-g282-carry-fourier-normal-nogo-2026-07-13
title: "G282: primitive carry-Fourier normals do not carry the CORE sign"
issue: 466
date: 2026-07-13
tags: [proximity-gap, deltastar, carry, wraparound, Fourier, weighted-kernel, no-go]
status: landed
---

# G282: primitive carry-Fourier normals do not carry the CORE sign

## Result

For the canonical adjacent-rank relation

```text
2y + sum(B) - z - sum(A) = k p,
J_r = sum_k J_{r,k},
A_r = p J_r - n^2 C(n,r) C(n,r-1),
```

G278 proved `J_{r,k}=J_{r,-k}` and showed that neither `k=0` nor all `k!=0` carries certifies the
gate. G281 proved that even perfect Eulerian carry shape plus the complete lawful floor misses the
production gate by factors from `271` to more than `2*10^10`. G282 tests arithmetic normals that
those two-block and shape statements do not directly cover: exact primitive-character aggregates of
the carry histogram, represented by integer Ramanujan sums at every conductor.

```text
T2 = sum_k (-1)^k J_k,
T3 = sum_k 2 cos(2 pi k/3) J_k,
T4 = sum_k   cos(  pi k/2) J_k,
T6 = sum_k 2 cos(  pi k/3) J_k.
```

All four weight systems are integer-valued.

## Abstract theorem

`Frontier/_G282CarryFourierNormalNoGo.lean` proves:

1. `symmetric_carry_kills_odd`: if negation permutes the finite carry bins, `J(-k)=J(k)`, and
   `a(-k)=-a(k)`, then `sum_k J(k)a(k)=0` exactly. Every odd carry moment and every odd arithmetic
   normal lies in the kernel.
2. `carryPairing_eq_evenized`: for every rational linear weight `a`, pairing against a symmetric
   carry histogram equals pairing against `(a(k)+a(-k))/2`. The carry statistic sees only the
   negation-even component.

These are genuine finite algebraic theorems, not recorded-cell decisions.

The file also proves `dominant_zero_bin_forces_positive`. If a distinguished histogram weight is
positive, every other weight is at least minus one eighth of it, all multiplicities are
nonnegative, and the distinguished bin contains more than one ninth of the mass, then the pairing
is strictly positive. The division-free hypothesis is `-a(0) <= 8*a(k)`, so no hidden divisibility
assumption enters the Ramanujan application.

## Exact probe

`scripts/probes/g282_carry_fourier_normal_probe.py` reuses G278's exact integer subset-sum DP and
integer dot products. It scans the complete 42-prime `n=16,p<2600` window at both live ranks and four
exact `n=32` late cells, 88 cells total. No FFT or floating-point value enters a sign decision.

```text
T2: agreement with sign(A_r) = 47/88, all four sign quadrants occur
T_d = sum_k c_d(k)J_k: positive in 88/88 for every 3 <= d <= 4096,
                        while A_r has both signs
maximal carry support radius: 6
minimum of 9*J0-J: 2,838,100 > 0 at (n,p,r)=(16,2593,5)
```

Here `c_d(k)` is the exact integer Ramanujan sum. The displayed `T3,T4,T6` are the first instances
(up to the harmless factor `c_4=2*T4`). The finite scan through `d=128` combines with an unbounded
argument. For `d>=129`, `0<|k|<=6` implies `q=d/gcd(d,k)>=22`. The elementary inverse-totient
classification gives `phi(q)>=8`, so the exact formula
`c_d(k)=mu(q)*phi(d)/phi(q)` yields `c_d(k)>=-phi(d)/8`, while `c_d(0)=phi(d)`. Therefore

```text
T_d >= phi(d)/8 * (9*J0-J) > 0.
```

The scan through 4096 checks both the coefficient inequality and the conclusion in every cell. For
prime `d>6` the aggregate simplifies further to `T_d=d*J0-J`, exactly the already-dead
zero-versus-nonzero split from G278.

Exact kernel-recorded discriminators:

```text
(n,p,r)=(16,193,5):  (A,T2)=(+3,843,136, -163,896)
          (16,257,5):         (-1,051,408,  -88,764)
          (16,433,5):         (+3,425,440, +474,180)
         (16,1553,5):        (-16,213,712, +383,316)
```

At the last negative-gate cell, `T3=809194`, `T4=516342`, and `T6=1581282` are all positive. The probe
also verifies exact vanishing of carry moments of degrees `1,3,5,7,9` in every cell.

## Literature and asymptotic interpretation

The identity `c_d(k)=mu(d/gcd(d,k))*phi(d)/phi(d/gcd(d,k))` is the classical Ramanujan-sum
formula for the aggregate of primitive additive characters modulo `d`. The only inverse-totient
input needed here is elementary: `phi(q)<8` has solutions only
`q in {1,2,3,4,5,6,7,8,9,10,12,14,18}`, hence `q>=22` implies `phi(q)>=8`.
For prime `d>6`, the formula collapses exactly to `T_d=d*J0-J`. Increasing conductor therefore
amplifies the already-known zero-bin magnitude instead of revealing a new sign. Quantitatively,
`T_d/phi(d) >= (9J0-J)/8`, so the lower bound grows at the same totient scale as the trivial
zero-bin coefficient while remaining independent of the CORE polarity.

This also explains why subgroup-interval literature does not repair the route. The power-saving
range in Di Benedetto, Garaev, Garcia, Gonzalez-Sanchez, Shparlinski, and Trujillo,
*New estimates for exponential sums over multiplicative subgroups and intervals in prime fields*
(arXiv:2003.06165), starts at `|G|>p^(1/4)`, whereas the sponsors have approximately
`|G|=p^(1/5.27)`. More importantly, such interval-distribution input controls carry magnitude or
shape, while G280 shows the survivor needs an odd row-labelled sign. FS15-FS18 likewise provide
fixed-depth almost-all-prime magnitude ladders; G64 proves the sponsor is exceptional by depth six.

## Binding inequality and asymptotics

The tested normals are scale-sensitive, unlike G281's normalized Eulerian proportions, so this is not
a restatement of G281. Their failure is sign-theoretic:

- every negation-odd carry weight is annihilated exactly by `J_k=J_{-k}`;
- the parity normal `T2`, the only fluctuating primitive Ramanujan member in the census, is
  deterministically decoupled from the gate, with all four exact sign quadrants;
- every primitive Ramanujan aggregate `T_d` at every conductor `d>=3` is positive and therefore
  carries zero-bin magnitude, not gate polarity.

A carry-based repair must use a genuinely different non-Ramanujan weight or explicit row-labelled
information. Merely increasing the conductor cannot help. The unbounded tail statement is specific
to the recorded support and dominance inequalities, not a sponsor-prime asymptotic estimate.

FS15-FS18 fit this conclusion exactly. They give fixed-depth, almost-all-prime magnitude ladders and
the sharp `(2r)^(n/2)` resultant envelope, but G64 forces the deployed sponsor exceptional already at
depth six. They do not select either sponsor prime and do not create the row-labelled sign absent from
these carry normals.

## Honest scope

This is an axiom-clean route no-go, not a sponsor-prime estimate and not prize closure. It closes
odd carry moments abstractly and the entire primitive Ramanujan carry-normal family on the exact
88-cell census. It does not prove that arbitrary non-Ramanujan or row-labelled carry weights fail.
The surviving object remains an absolute, sponsor-specific, row-labelled signed Jacobi/Gross-Koblitz
or equivalent weighted-kernel estimate at ranks 5 and 6.
CORE OPEN / ON-BGK.
