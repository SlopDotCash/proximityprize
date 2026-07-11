# #466/#505 CXI01: convex/information assault — the positive-moment cone has one exact null ray

Date: 2026-07-10.  Lane 8 of the 10×10 assault.  Status: exact probe plus axiom-audited Lean
method-class no-go; **no bound on the Paley maximum and no proximity-prize closure**.

## Starting point

G121→G127 already gives exact matching-moment identities, the triangular moment LP, its Farkas
dual, and the disjoint-sector gate.  The live object is the fully-disjoint equal-sum census
`depthFiber G r r`, at production `(n,r)=(2^30,110)`.  All positive matching moments use the
coefficient matrix

```text
  W[m,s] = (r-s)_m,       m=1,...,r,  s=0,...,r.
```

The decisive convex question is whether enriching the *optimization language* (LP, SOS, SDP,
entropy, transport, minimax) creates information at `s=r`, or merely repackages these rows.

## Exact cone computation

`scripts/probes/probe_cxi01_positive_moment_cone.py` uses integer arithmetic only.  For every tested
`r=1,2,3,4,5,8,16,32,110`:

* the `s=r` column is identically zero;
* after writing `t=r-s` and restricting to `t=1,...,r`, the matrix is triangular:
  `W[m,t]=(t)_m`, zero for `m>t`, diagonal `m!`;
* hence the matrix has exact rank `r`, nullity one, and its common nonnegative recession cone is
  precisely the full-depth ray `R_{≥0} e_r`.

The production `r=110` check has rank `110`, nullity `1`; the shallow determinant
`∏_{m=1}^{110}m!` has 28,672 bits.  This is not a numerical near-kernel.

The same probe tests the truncated-moment measure
`μ_T = T δ_0 + δ_1`.  All positive falling-factorial moments are independent of `T`, while the
normalized atom at zero tends to one and its entropy tends to zero.  Thus maximum-entropy completion
or transport based only on positive moments cannot upper-bound the zero-match atom.

## The ten subangles, falsify-first

1. **Thin-aware Delsarte LP — REDUCES.**  Domain-blind Krawtchouk rows were already fenced.  Adding
   the G124 subgroup-aware matching rows constrains every shallow coordinate but has the exact
   recession ray `e_r`.  A surviving LP must add an arithmetic-labeled row nonzero at full depth.

2. **Terwilliger/flag SDP — CONDITIONAL NO-GO.**  Any flag matrix whose entries count at least one
   shared coordinate has zero Gram column on a fully-disjoint pair.  PSD closure and Schur
   complements do not remove a common null vector.  A viable flag must encode a genuinely disjoint
   additive relation, not only richer overlap labels.

3. **Moment-SOS — EXACT NO-GO FOR ZERO-CONSTANT TESTS.**  A nonnegative polynomial expressed in the
   falling-factorial basis with no zeroth coefficient vanishes at match count zero.  Every conic
   combination remains blind.  Introducing the constant coefficient is exactly row `m=0`.

4. **Entropy duality — EXACT ATOM OBSTRUCTION.**  The family `μ_T` keeps all positive moments fixed
   while changing the zero atom without bound.  Any dual polynomial positive at zero needs a
   positive constant coefficient, i.e. must pay total mass at the open rung.

5. **Optimal transport — REDUCES.**  An integral probability metric using tests `f(0)=0` is
   unchanged under the unnormalized zero-atom spike.  Normalization does not rescue a tail theorem:
   `μ_T/|μ_T| → δ_0`.  A useful transport-entropy inequality must independently control the atom
   or total mass, which is the disjoint census.

6. **Vector discrepancy — STILL ADMISSIBLE, BUT NOT AN LP CONSEQUENCE.**  Choosing good signs is
   irrelevant because the arithmetic signs are fixed.  A survivor must prove that the fixed dyadic
   signing has nonzero correlation with the full-depth relation class; matching-moment balance alone
   has payoff zero against `e_r`.

7. **Noncommutative Khintchine — RESIDUAL IDENTIFIED.**  Variance/overlap blocks lie in the positive
   moment cone and miss `e_r`.  The deterministic correction block must therefore carry the full
   disjoint census.  Bounding its operator norm is a valid new target, but it is not supplied by the
   Khintchine variance term.

8. **Maximum-entropy completion — REFUTED FROM TRUNCATED POSITIVE MOMENTS.**  `μ_T` is an explicit
   one-parameter family with identical positive factorial moments and arbitrary zero mass.  Moment
   determinacy needs the zeroth moment/normalization plus a statistic that separates the zero atom;
   the former alone is the unknown total energy.

9. **Invariant flag algebra — SAME NULL-RAY TEST.**  Flags requiring any cross-endpoint match vanish
   at full depth.  An SDP extrapolation from `r≤10` is relevant only if at least one invariant flag is
   supported on fully-disjoint additive accidents and its production coefficient is controlled.

10. **Rational dual certificates — EXACT FARKAS FENCE.**  Every dual combination of rows `m≥1` has
    full-depth coefficient zero.  To dominate a target with `c_r>0`, a certificate must use
    `λ_0>0`; row zero is `E_r`, the very open quantity.  This gives a mechanical rejection rule for
    generated certificates.

## Lean result

`Frontier/_CXI01PositiveMomentConeRecession.lean` proves, without importing the in-flight G127 file:

* `blindConstraints_have_unbounded_fullDepth_ray` — arbitrary blind nonnegative constraint
  families admit unbounded full-depth feasible spikes;
* `positiveDescentConstraints_have_unbounded_fullDepth_ray` — specialization to every positive
  falling-factorial row;
* `zero_firstDescentMoment_forces_shallow_zero` — the first row kills every shallow nonnegative
  recession direction, so the ray above is the exact common nonnegative recession cone;
* `no_positiveDescentDual_dominates_fullDepth` — exact conic-dual obstruction;
* `descentDual_fullDepth_eq_rowZero` and `fullDepth_domination_requires_rowZero` — the full-depth
  dual column is exactly `λ_0`, so a positive target necessarily pays row zero.

## Literature cross-check

This verdict is consistent with, but does not rely on, SOS lower-bound phenomena for graph
problems.  Kunisky–Yu's degree-4 Paley-clique analysis proves a substantial low-degree SOS gap and
shows that richer Paley arithmetic can change the relaxation value
(https://arxiv.org/abs/2211.02713); it does **not** furnish the generalized-Paley period bound here.
The truncated moment literature likewise requires positivity plus rank/variety consistency for
extremal determinacy (Curto–Fialkow–Moeller, https://arxiv.org/abs/math/0610882).  CXI01 is more
elementary and problem-specific: its missing atom is visible directly as a literal zero column.

## Verdict and survivor

**Strong no-go:** the entire positive matching-moment LP/SOS/SDP/entropy-dual cone has exactly one
missing nonnegative direction, the fully-disjoint census, and no optimizer can manufacture a bound
along a zero column.  This strengthens the G127 prose observation into a reusable theorem family.

**Strongest survivor:** search for one arithmetic-labeled statistic with *provably nonzero
full-depth coefficient* and a production-scale bound.  Concrete candidates are a signed disjoint
relation character, the G133 punctured correction, or a disjoint-core operator block.  Before any
large SDP/SOS run, print its coefficient on `e_r`; zero means immediate retirement.

The CORE remains open and on the fully-disjoint Paley/BGK wall.
