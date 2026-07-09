# Delta-star tight-budget packing / master-gap audit (2026-07-09)

## Verdict

The overlap-packing obstruction is a genuine obstruction for the faithful operational
`mcaDeltaStar`.  It is not restricted to far directions, monomial pencils, a proxy incidence,
or a catalogue conjecture.

The axiom-clean theorem
`PackingBudgetFirstJump.mcaDeltaStar_le_half_of_floor_eq_length` has the exact form:

```text
[Fact p.Prime], [NeZero n], orderOf g = n,
0 < Q, 2 <= k, n % 2 = 0,
p / Q = n, k <= n / 4, 4 <= p - n

  ==> mcaDeltaStar (evalCode g n (k - 1)) Q^{-1} <= 1/2.
```

Consequently, with `n = 2^30`, `Q = 2^128`, and dimensions
`k = 2^28, 2^27, 2^26` (rates `1/4, 1/8, 1/16`), every smooth prime-field instance in the
branch `floor(p / 2^128) = 2^30` has operational MCA threshold at most `1/2`.

At rate `1/4`, this is the Johnson radius.  At rates `1/8` and `1/16`, it is strictly below
the Johnson radii `1 - 1/sqrt(8)` and `3/4`.  Thus a field-uniform claim that all
`p approximately n * 2^128` instances have threshold in the advertised beyond-Johnson window is
false.  The field regime must be split by the exact integer budget
`B = floor(p / 2^128)`.

## Definition trace

1. `Errors.lean` defines `mcaEvent` using one witness set of size at least `(1-delta)n`, exact
   line agreement with a codeword, and failure of joint pair agreement.  It defines `epsMCA` as
   the supremum over **all** two-row stacks.
2. `MCAThresholdLedger.lean` defines `mcaDeltaStar` as the supremum of radii with
   `epsMCA <= epsilonStar`; `mcaDeltaStar_le_of_bad` turns any strict bad point into an
   operational upper bound.
3. `PackingEnvelope.overlap_packing_epsMCA_lower_bound` explicitly constructs a two-row stack and
   a set of `n+c` scalars, proves `mcaEvent` for every scalar, and feeds that set directly into
   `epsMCA_ge_card_div_of_mcaEvent_set`.  Its consumer
   `mcaDeltaStar_le_overlap_packing` calls `mcaDeltaStar_le_of_bad` directly.
4. `KKH26RegimeSplit.evalCode_eq_reedSolomon` proves
   `evalCode g n d = ReedSolomon.code (powDomain g) (d+1)`.  Hence `d=k-1` is exactly the
   dimension-`k` prize code convention; there is no degree off-by-one escape.

## The half-radius specialization

Set

```text
t = n/2,       s = n/2 + 1,       c = 2,       d = k - 1.
```

Then the overlap construction supplies `n+2` bad scalars at
`delta = 1 - t/n = 1/2`.  Its arithmetic hypotheses reduce to

```text
2 <= k,       k <= n/2 - 1,       n even,
```

and the landed prize-facing theorem uses the stronger convenient assumption `k <= n/4`.
The six tuned-scalar separation hypotheses are discharged by
`exists_overlapFreshScalars`: four field elements outside the negated evaluation domain suffice,
i.e. `4 <= p-n`.  This is automatic at `n=2^30`, `Q=2^128` from `p/Q=n`.

The strict budget comparison is exact:

```text
p / Q = n  ==>  p < (n+1)Q < (n+2)Q
              ==>  1/Q < (n+2)/p.
```

Thus the bad mass is strictly above `epsilonStar = 2^-128`, not merely equal to it.  The same
raw packing witness also crosses at radius `1/2` whenever `p < (n+2)Q` (in particular when
`floor(p/Q)` is `n` or `n+1`); the currently packaged headline theorem states the `floor=n`
branch.

## Concrete non-vacuity

`Frontier/_PrizeShapePrimeP30.lean` already kernel-certifies

```text
P = 365375409332725729550921208179070755120141565953
  = 2^30 * (2^128 + 192) + 1
```

as prime (`prime_P`), proves `P / 2^128 = 2^30` (`P_div_two_pow_128`), and supplies an explicit
`g : ZMod P` of order `2^30` (`orderOf_g`).  Therefore the tight-budget branch contains a fully
certified smooth prize-shaped field; it is not a hypothetical compatibility corner.

## Audit of the window reductions

The conditional reduction files remain logically valid, but their hypotheses do not bypass the
packing stack:

* `OpenCoreConditionalPin.WorstCaseIncidenceBounded C delta B` quantifies over every stack.
  At `B=n`, it is false already at `delta=1/2`, because the packing stack has `n+2` bad scalars.
  By monotonicity it is false at every larger radius, including the proposed windows for all
  three rates.
* `_PrizeFloorOfBGK.prizeFloor_window_of_BGK_and_incidence` explicitly assumes that open incidence
  bound.  On the tight-budget branch the assumption is refuted by packing; the issue is not a
  remaining BGK estimate there.
* `SumsetExtremalityReduction` explicitly assumes `SumsetExtremal`, and separately assumes a
  monomial-family bound.  Neither assumption excludes arbitrary stacks from the operational
  definition.  At budget `n`, their conjunction cannot yield an all-stack bound at or above
  `1/2`.
* `LineListMCAWeld.mcaDeltaStar_ge_of_farLineListBudgeted` does cover all stacks, but only under
  the far-list, arithmetic-fit, large-zero-branch, and normalized-budget hypotheses
  `hfarL`, `hfit`, `hlow`, and `hBudget`.  Packing proves that these hypotheses cannot jointly
  close with numerator at most `n` at radius `1/2`.
* `_BridgeB01.deltaStar_master_gap_identity` is an algebra lemma from an assumed binding-radius
  identification.  `_CoreReductionComplete.prize_reduces_to_BCHKS` explicitly receives `hE1`,
  `hident`, and `hmstar_real`.  These files do not prove that a monomial/subset-sum binder equals
  the faithful operational binder in this low-budget branch.

If one expresses the true operational capacity gap as a master-gap depth, the ceiling
`deltaStar <= 1/2` forces a **linear** gap of at least

```text
rate 1/4:   (1/2 - 1/4)n = n/4,
rate 1/8:   (1/2 - 1/8)n = 3n/8,
rate 1/16:  (1/2 - 1/16)n = 7n/16.
```

Hence an `O(log n)` monomial binding depth cannot be identified with the operational depth on
this branch without contradicting the explicit stack.

## Corrected regime statement and remaining work

The honest regime map is at least two-branched:

* **Tight normalized budget** (`floor(p/2^128)=n`, and in fact the same half-radius witness while
  `p<(n+2)2^128`): rates `1/4`, `1/8`, and `1/16` satisfy `mcaDeltaStar <= 1/2`.
* **Larger normalized budget**: the first overlap-packing crossing moves with
  `B=floor(p/2^128)`; only after accounting for that crossing can a beyond-Johnson window be a
  possible target.

This audit proves only the bad side.  It does **not** prove that every radius below `1/2` is good,
so it does not yet establish `mcaDeltaStar = 1/2`.  It also does not cover the exact rate-`1/2`
code: at `k=n/2` the packing degree/window inequality fails by one.  A matching all-stack bound
below `1/2`, plus a separate rate-`1/2` analysis, remain necessary for a complete prize solution.

## Validation

`scripts/pg-iterate.sh` passes on
`Frontier/_PackingBudgetFirstJump.lean`; the new theorems report only the standard
`propext`, `Classical.choice`, and `Quot.sound` axioms and contain no `sorry`.
