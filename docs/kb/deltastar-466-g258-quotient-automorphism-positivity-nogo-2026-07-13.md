# G258: quotient automorphisms defeat the positivity/support repair

Date: 2026-07-13
Issue: #466
Status: axiom-clean route no-go, not prize closure

## Question

G257 preserved the complete complex Fourier-value multiset and conjugation pairing while permuting
Fourier pairs against the rank profiles. Its unconstrained optimum reversed the covariance, but Fable's
G258 audit found that 7/8 tested optima inverted to signed physical profiles. At sparse cells, the
identity was isolated under every single pair transposition/orientation move. This suggested that
positivity plus sparse support might be the first independently checkable invariant capable of pinning
the covariance.

The decisive question was whether the exact positivity-constrained assignment minimum at
`(n,p,r,m)=(16,1297,5,81)` remained nonnegative.

## Structural answer

No. The local search omitted the global automorphism components of the feasible set.

For a unit `a` of `Z/mZ`, define

```text
w_a(x) = w(a^{-1}x).
```

This is an exact physical relabeling:

- if `w` is integer and nonnegative, so is `w_a`;
- total mass and support cardinality are unchanged;
- `DFT(w_a)(k)=DFT(w)(a k)`;
- because multiplication by `a` commutes with negation, inverse-character/conjugate pairs remain
  paired;
- hence the complete complex DFT-value multiset is preserved exactly, not only magnitudes or a phase
  histogram.

The DFT statement is already Mathlib's `dft_comp_unitMul`; G258 packages it as
`dft_unitRelabel` and proves a test-function multiset identity

```text
sum_k h(DFT(w_a)(k)) = sum_k h(DFT(w)(k))
```

for every `h : C -> C`.

### Harmonic-analysis interpretation

This is the standard naturality of finite-abelian Fourier transform under a group automorphism:
the primal automorphism acts by the inverse dual automorphism on characters. In phase-retrieval
language, it is stronger than ordinary homometry. Homometric sets preserve only Fourier magnitudes;
here the complete complex coefficient multiset is preserved, with its conjugate pairing, but its
labels are permuted. Consequently Lu--Zheng--Zheng-style unlabelled Jacobi phase discrepancy and every
other symmetric phase statistic are exactly invariant under the move. Only a labelled observable can
distinguish the two profiles.

## Exact characteristic-p certificate

At `(n,p,m)=(16,1297,81)`, the weighted-relation quotient profile is the indicator of

```text
S = {0,6,8,12,18,21,31,35,41,42,47,57,60,65,72,78}.
```

It has mass 16, support 16, and values only 0 or 1. Take `a=26`, with inverse `53 mod 81`. The physical
relabeling has support

```text
S' = {0,3,7,9,13,19,21,24,39,46,60,63,69,70,75,77},
```

again a 0/1 profile of mass/support 16.

With centered quotient covariance

```text
C_m(w,R) = m * sum_x w(x)R(x) - (sum_x w(x))(sum_x R(x)),
```

the exact totals are:

```text
rank 5:
  sum R5 = 496733
  sum w R5 = 113689       => C_81(w,R5)   = +1261081
  sum w_a R5 = 93845      => C_81(w_a,R5) = -346283

rank 6:
  sum R6 = 2185369
  sum w R6 = 477249       => C_81(w,R6)   = +3691265
  sum w_a R6 = 417335     => C_81(w_a,R6) = -1161769
```

The same unit therefore reverses both ranks simultaneously. Four units do so:
`a in {14,26,44,56}`. All certificate values are computed with Python integers in physical space,
with no numerical FFT. Control sweeps show the phenomenon is not tautological: at `(8,1801,m=225)`
no unit reverses either rank, while `(64,3329,m=52)` has eleven simultaneous reversing units.

### Sponsor-scale asymptotics

The automorphism ambiguity is not a bounded-size toy family. Exact integer factorization gives

```text
m1 = 2^128+192
   = 2^6 * 7^3 * 26407 * 279991 * 4533259 * 462478642316479903
phi(m1) = 145829224502780318494720788756410680320 > 2^126

m2 = 2^129+13
   = 3 * 5^2 * 7 * 71 * 202172094073993 * 90308905535905320959
phi(m2) = 306733401168168365365525363013448844800 > 2^127.
```

So the label-free Fourier/positivity data leave more than `2^126` or `2^127` exact cyclic
relabelings at the two sponsors before quotienting by the stabilizer of the particular profile.
This does not prove that a sponsor relabeling reverses the covariance, but it shows why a bounded
local-move rigidity argument has the wrong asymptotic shape. The surviving theorem must control the
actual labels across a production-scale automorphism orbit.

## Why the local search looked rigid

At the `m=81` cell the original profile vanishes on 65 of 81 quotient positions. Every single
transposition or orientation flip moved the inverse DFT negative on that zero set, so the identity
was isolated at graph distance one in the local move graph. But a unit automorphism changes many
Fourier-pair assignments coherently and lands exactly on another 0/1 support. Local isolation is not
global support rigidity.

## Consequence

The following label-free inputs do not determine the covariance sign, even jointly:

- complete complex Fourier-value multiset;
- inverse-character pairing;
- physical nonnegativity and integrality;
- total mass;
- 0/1 structure and support cardinality;
- both adjacent ranks considered simultaneously.

This closes the positivity/sparse-support repair to G257. It does not preserve the exact labelled
support set. A theorem using that labelled placement could still distinguish the two profiles, but
that input is precisely the joint row-labelled shifted-subgroup/Jacobi object

```text
Re sum_{chi != 1} What(chi) * conjugate(Rhat_r(chi)),  r=5,6,
```

rather than a marginal shortcut. The production sponsor-prime covariance remains open and on the
BGK/Paley wall.

## Artifacts

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G258QuotientAutomorphismPositivityNoGo.lean`
- `scripts/probes/g258_quotient_automorphism_positivity_nogo.py`
- DISPROOF entry `[466-G258-quotient-automorphism-positivity-nogo]`
