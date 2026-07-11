# δ* #466 — Pair-cloud second moment: the jaws do NOT close (kernel no-go rungs) — but Cauchy–Schwarz caps near-full pencils at FIVE, unconditionally (2026-07-11)

**Lane:** P1 rate-quarter — pair-cloud round following
`deltastar-466-rate-quarter-pencil-cover-theorem-2026-07-11.md` (seventh round of
the 2026-07-11 arc).
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterPairCloudSecondMoment.lean`
(pg-iterate OK 10s; 7 theorems; full axiom lists read manually via `lake env lean`:
6 exactly `[propext, Classical.choice, Quot.sound]`, 1 `[propext, Quot.sound]`;
no sorryAx, no warnings).
**Calculation:** done exactly in Python first (constants kernel-pinned); W-lane
check: `LineList*` files are incidence/dimension-lift machinery, no below-Johnson
second-moment lemma in-tree — built from scratch.

## The decisive answer: the jaws do NOT close

* **Second-moment jaw at the pair-pencil floor `a = 2T−N = 111848108` is OPEN by a
  factor 23.04**: `23·a² ≤ N(k−1) < 24·a²` (`secondMoment_floor_slack`).  The
  `(2T−N)`-aligned pair-pencil cloud sits far below the Johnson threshold where
  Cauchy–Schwarz packing would bind.
* **The packing jaw NEVER binds**: `2·P(T−1) ≤ 2N + P(P−1)(k−1)` for EVERY `P`
  (`packing_jaw_never_binds`, universal; minimum margin at `P = 3`; quadratic
  pairwise budget beats linear coverage demand).
* Consequence (kernel no-go): pair-counting + second moment cannot squeeze
  `B ≤ N` in the many-pencil regime.  No future campaign should re-attempt this
  route; the constants are pinned.

## The round's positive gem: at most FIVE near-full pencils, unconditionally

At sizes `≥ T − 5` the Cauchy–Schwarz second moment DOES bind at `P = 6`:
`S₀(S₀−N) = 8831558712238801572 > 30N(k−1) = 8646911252339097600` (~2% margin,
exact).  Kernel-checked IN FULL — not just the arithmetic:

* `six_near_full_sets_impossible` — six subsets of `Fin N` of size `≥ T−5` with
  pairwise intersections `≤ k−1` cannot coexist.  Proof: exact incidence double
  count (`∑ d = Σ|A_π|`, `∑ d² = Σ_{π,π'}|A_π ∩ A_π'|`), diagonal split, Mathlib
  `sq_sum_le_card_mul_sum_sq` (Chebyshev/Cauchy–Schwarz, applies to ℕ directly),
  and the `S(S−N)` monotone finale in pure ℕ arithmetic.
* `six_near_full_pencils_impossible` — **any stack admits at most five
  pairwise-distinct pencils with aligned sets `≥ T−5`** (via
  `alignedSet_inter_card_lt_k`).
* `sixPencil_margin_forced` — among any six pairwise-distinct pencils, at least
  one satisfies the margin-5 hypothesis of the harvest-cap budget theorems.
* `five_full_pencils_feasible` — five full pencils remain counting-feasible: the
  gap between the unconditional `≤ 5` and the generic-rank `≤ 2`
  (dimension-deficit round) is exactly the Bezout-escape content.

This unconditionally shrinks the round-3 residual: clusters of SIX or more
near-full pencils are now theorem-level impossible; `FullyAlignedTripleFree`-type
content is needed only for 3-to-5 clusters.

## Residual map after seven rounds (P1 counting branch, literal domain)

1. 3-to-5 near-full pencil clusters (Bezout/generic-rank; all known escape
   constructors dyadically blocked, round 5).
2. The sub-Johnson pair-cloud swarm (counting-immune by this round's no-go rungs;
   needs beyond-Johnson list input — the campaign's global wall).
3. Margin growth for ≥ 5 under-aligned pencils in scalar covers.

Budget theorems now cover: 1–2 pencils (no hypotheses), ≤ 4 pencils at pair level
(no hypotheses), 3–4 pencils at scalar level (margins, forced generically and
partially forced by this round's `≤ 5` cap).

## Honesty

`StallResidual(μ_{2^30})` remains OPEN.  The no-go rungs are as load-bearing as
the positive results: they prove where the wall is NOT.  No δ* movement; bracket
`3/8 ≤ δ* ≤ 43/96 + 1/(3·2^30)` untouched.

## Next targets

1. Exploit `≤ 5` structurally: a bad family's near-full pencils number ≤ 5 and
   carry ≤ 5c riders; the REST of the family rides margin-5 pencils at
   `≤ 96189372` each — an over-budget family needs `≥ (N − 5c)/96189372`… note
   `5c > N`, so this alone does not close; the right combination is `≤ 5`
   near-full + the PAIR-level partition across the near-full/margined boundary
   (pairs between two margined-pencil riders live on pair-pencils with their own
   `2T−N` floor — a two-level ledger).
2. The 3-to-5 cluster dimension count (extend the triple deficit to quadruples/
   quintuples: parameter budget `(P−1)·2k` vs overlap mass `P(T−1) − N + …`).
