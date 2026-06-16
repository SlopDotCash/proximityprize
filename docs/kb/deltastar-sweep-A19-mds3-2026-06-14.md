# delta* sweep A19 — Higher-order MDS(3) genericity of the explicit 2-power smooth domain mu_{2^k}

Date: 2026-06-14
Type: numerical-probe (A19; merged from 232-T18 / 389-T05)
Status: PARTIAL — order-3 failure CONFIRMED, but it does NOT seed a beyond-Johnson list lower bound.
Artifact: `scripts/probes/sweep_A19_mds3.py` (exact arithmetic over Q and F_q)
In-tree substrate: `ArkLib/Data/CodingTheory/HigherOrderMDSOrderThreeFail.lean`
(`reedSolomonFrame_not_isHigherMDS_three_of_sumZeroPairs`, axiom-clean, = the proven 389-T05),
`HigherOrderMDSListGenPos.lean` (`mds_genpos_list_bound`), `HigherOrderMDSReedSolomon.lean`.

## What was asked (A19)

Exact-arithmetic MDS(3) test of `mu_{2^k}` vs random vs adversarial domains at n = 8,16,32 with a
known-failure gate. The order-3 failure for negation-closed `mu_n` via antipodal sum-zero pairs is
PROVEN in-tree (389-T05). Confirm it numerically, then **decide whether it seeds a beyond-Johnson
list lower bound, or whether the affinely-dependent (GM-MDS dual zero-pattern) case is live.**

## Setup

RS frame columns `v_i = (1, D_i, ..., D_i^{k-1})` in the k-dim message space. For a triple of
pairwise-disjoint 2-element index sets, MDS(3) **holds** iff the three pair-spans intersect in {0}
(`inter_dim = 0`, = the generic value `max(0, 6 - (3-1)*3) = 0`); it **fails** iff `inter_dim >= 1`
(a common vector exists). A pair `{a,b}` spans the plane orthogonal to the interpolation normal
`(X-a)(X-b) <-> (ab, -(a+b), 1)`; three pairs with a common SUM `sigma` have collinear normals, so
they share the common vector `w = (0, 1, sigma)`. For `mu_n` (negation-closed, even n), antipodal
pairs `{x, -x}` all have sum 0, so `w = (0,1,0)` lies in every antipodal pair-span -> MDS(3) fails
unconditionally.

## Numerical results (all exact: Q via Fraction, F_q via prime-field Gaussian elimination)

1. **GATE** `{+-1,+-2,+-3}` over Q: `inter_dim = 1`, MDS(3) **FAILS**, `w = (0,1,0)` verified in all
   three pair-spans. Matches the in-tree proof.
2. **mu_{2^k} over F_q**, n = 8, 16, 32, two primes each incl. prize-scale `~ n^4`
   (q = 41/4129, 97/65537, 97/1048609): antipodal pair sums all `= 0 (mod q)`, `inter_dim = 1`,
   MDS(3) **FAILS** in every case. (CONFIRMS 389-T05 numerically, char-p, prize-shaped.)
3. **Random (antipodal-free) domains** over F_q, 200 trials each at n = 8,16,32: **0/200** failures
   — MDS(3) holds generically (control passes).
4. **Adversarial non-antipodal** common-sum domain `{0,10},{1,9},{2,8}` (sigma = 10, the in-tree
   `Dfail`): `inter_dim = 1`, MDS(3) **FAILS**. So the failure mechanism is "common pair-sum", not
   specifically antipodal — antipodal is the sigma=0 instance Sidon does not forbid.

## The decisive question — does MDS(3) failure SEED a beyond-Johnson list lower bound?

**NO.** Three independent checks, all negative:

- **Primal codeword count at the failure radius = 1.** The 6 pair-points have RS-column rank `= k = 3`
  (full). Any deg-<3 polynomial is pinned by any 3 of the 6 points, so 6 shared agreements force a
  UNIQUE codeword. The MDS(3) failure is a statement about the DUAL (pair-span intersection / the
  common vector `w`); it does NOT produce >= 3 distinct PRIMAL codewords agreeing on the 6 points.
- **Affinely-dependent branch caps at k-1.** The proven genpos bound `(L+1)a <= Ln + (k-L)` is for
  affinely-INDEPENDENT messages and caps the common-agreement set S at `k-L = 1` (L=2). The MDS(3)
  failure lives in the affinely-DEPENDENT branch, where one nonzero difference functional can vanish
  on at most `k-1 = 2` columns (a deg-<k poly has <= k-1 roots). Measured max |S| = 2 for both the
  antipodal and the sigma=10 domains — an MDS-region count, NOT beyond-Johnson.
- **Direct list-decoding realization over F_q.** The affinely-dependent pair-difference
  `d(X) = X^2 - a^2` (the only quadratic vanishing on an antipodal pair) vanishes on exactly **2**
  points of `mu_n`. The induced 2-codeword cluster has mutual agreement 2, vs Johnson agreement
  `~ sqrt((k-1)n)` (4.0/5.66/8.0 at n=8/16/32) and UD agreement `(n+k)/2` (5.5/9.5/17.5). Cluster
  agreement `2 << both` => the cluster lives WELL INSIDE the unique-decoding radius. Not beyond
  Johnson, not even beyond UD.

## Is the higher-order GM-MDS dual-zero-pattern case live? (does it compound?)

**The antipodal failure is a k=3-only phenomenon; it does not compound at higher order via the same
mechanism.** `w = (0,1,0,...,0)` is in an antipodal pair-span `span{(D_a^j),((-D_a)^j)}` iff
`v_b - v_a` aligns with `w` coordinate-by-coordinate. The X^2 coordinate `D_b^2 - D_a^2 = 0`
(antipodal), but the X^3 coordinate `D_b^3 - D_a^3 = (D_b - D_a)(D_b^2 + D_aD_b + D_a^2) != 0`. So
once `k >= 4` the cubic Newton coordinate breaks the shared vector: verified `rank([v_a, v_{-a}, w])`
= 2 (in-plane) at k=3 but = 3 (NOT in-plane) at k=4,5. A higher-order beyond-Johnson lower bound for
`mu_{2^k}` would therefore require a DIFFERENT, genuinely multi-term symmetric-function coincidence
(not the antipodal sum-zero one).

## Verdict

- Order-3 higher-MDS **fails** for `mu_{2^k}` unconditionally (antipodal sum-zero), confirmed exactly
  over Q and over F_q at n=8,16,32 incl. prize-scale primes. The mechanism is "common pair-sum",
  matching the in-tree proof and its `commonPairSum` generalization.
- This failure is REAL and structural but **BENIGN for list size**: it does not seed a beyond-Johnson
  (or even a beyond-unique-decoding) list lower bound. The common vector `w` is a dual/genericity
  artifact; the primal codeword agreement list at the failure radius is 1, and the
  affinely-dependent agreement set is capped at `k-1` = an ordinary MDS-region count.
- The order-3 antipodal lane for the derandomization route is therefore **closed (benign)**. The
  genuine list-size threat, if any, must come from genuinely higher-order symmetric-function fiber
  geometry — the object probed by A21 (esymm fibre count) and A08 (window-interior worst direction
  with b-a>1), NOT from the order-3 antipodal failure.

## Honesty

PARTIAL. What's proven/established: MDS(3) failure is confirmed numerically (matching the in-tree
proof) and is shown NOT to seed a beyond-Johnson list lower bound, via three independent exact
checks. What's left: whether some genuinely-higher-order (multi-term, non-antipodal)
symmetric-function coincidence on `mu_{2^k}` produces a beyond-Johnson cluster remains open — that is
the A21/A08 lane, not this one. No closure claimed for the prize.
