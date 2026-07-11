# δ* #466 — Junk-slice ledger: vote decomposition + junk-forced rider count landed; the fiber-Chebyshev composition does NOT improve the five-pencil master (calibrated no-improvement) — SESSION CLOSE with 11-round arc retrospective (2026-07-11)

**Lane:** P1 rate-quarter — eleventh and final round of the 2026-07-11 session.
**Probe:** `scripts/probes/probe_rate_quarter_p1_junk_slice.py` (exact).
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterJunkSliceLedger.lean`
(pg-iterate OK 10s; 5 theorems; full axiom lists read manually via `lake env lean`:
all exactly `[propext, Classical.choice, Quot.sound]`; no sorryAx, no warnings).
Build note: `_P1RateQuarterFiberChebyshevRefinement` olean built once via lake-locked.

## The composition audit (exact) — verdict: NO improvement

The fiber constraint forces a lower rider cap only when the vote demand exceeds
the total foreign fiber capacity:

* five-cover geometry (4 foreign regions): capacity `4(k−1) = 1073741820 ≥ T` —
  never forcing (`fiveCover_fiber_capacity`);
* two-capacity-region geometry: forcing needs margin `> 2(k−1)`, i.e. alignment
  `A < T − 2(k−1) = 55924056` — BELOW the pair-pencil floor `2T−N = 111848108`:
  empty range for pair-pencil families (`two_region_crossover_empty`);
* the master's margin demand `13` is seven orders below the fiber cap
  (`master_margin_no_improvement`).

Probe: the extremal dual family's 230 riders each take exactly ONE foreign vote
and ZERO junk votes — nowhere near binding.  **The five-pencil master ledger is
unchanged; no margin hypothesis weakens.**

## Kernel-landed anyway (the real content)

* `vote_decomposition_two_regions` — the exact own/foreign/junk decomposition:
  a non-exceptional rider has `#votes ≤ 2(k−1) + #(junk votes)`.
* `junk_forced_riders` — the conditional high-demand count:
  `#riders · (b − 2(k−1)) ≤ #(complement of the capacity regions)` — stated for
  completeness; its binding range is empty for pair-pencil families.
* The three calibration rungs above.

## Honesty

Nothing about `SwarmResidual`, the stall band, the master ledger, or δ* changes;
bracket `3/8 ≤ δ* ≤ 43/96 + 1/(3·2^30)` untouched.

---

## ARC RETROSPECTIVE — eleven rounds, 2026-07-11 (the lane closes)

**Rounds and headline results** (all axiom-clean, all probes exact):

1. **Stall-band census** (`_StallBandCensus`, 16 thms): extremal stall families
   = two-pencil covers at capacity `2(N−T+1) ≈ 0.898N`; 1/2-pencil budgets
   unconditional; μ_16 budget TIGHT (zero slack) ⇒ proofs must use `2(T−1)>N`.
2. **Pencil harvest cap** (`_PencilHarvestCap`, 11 thms): margin harvest bound;
   3/4-pencil budgets under margins (5 sharp); mechanism = dimension count.
3. **Dimension deficit** (`_DimensionDeficit`, 7 thms): pure degree argument
   REFUTED as universal (toy Bezout escape); forced-coincidence theorem
   (`≥ 167772161` per overlap); symmetric escape excluded;
   `FullyAlignedTripleFree` + conditional composition.
4. **Stepanov weld** (`_StepanovWeld`, 9 thms): the escape EXISTS at the prize
   modulus (`7·2²⁵ | P−1`, exact fit) — **`StallResidual` REFUTED on
   adversarial domains** (end-to-end synthetic census `614 > 613`); shared-
   factor pinning caps the overshoot at `N + O(1)`.
5. **Dyadic obstruction** (`_DyadicDomainEscape`, 7 thms): the refutation does
   NOT transport to `μ_{2^30}` — no 2-power in any escape window; two-level
   variants blocked; the prize-domain route restored.
6. **Pencil-cover theorem** (`_PencilCoverTheorem`, 6 thms): pair-pencil cover
   existence with the `2T−N` alignment floor; margin-free 4-pencil pair-cover
   budget (`B ≤ 2c ≤ N`); route caps at four.
7. **Pair-cloud second moment** (`_PairCloudSecondMoment`, 7 thms): counting
   jaws provably CANNOT close the swarm (no-go rungs); **at most FIVE
   near-full pencils per stack, unconditionally** (full kernel Cauchy–Schwarz).
8. **Cluster confinement** (`_ClusterConfinement`, 11 thms): compounded
   rank-drop floors `X₃/X₄/X₅`; dyadic blocking at every confined size;
   five-pencil master budget; **final residual form
   `StallResidual ⟸ SwarmResidual`**.
9. **Cross-cone bridge** (`_CrossConeBridge`, 6 thms): the P1 swarm's moment
   layer IS the B-side lag machinery (formal identity bridge, first
   cross-cone import); calibrated non-bridge at the open layers
   (sub-Burgess `N⁴ < P < N⁶` vs complete sums; list-level vs `r = 4`).
10. **Fiber-Chebyshev refinement** (`_FiberChebyshevRefinement`, 8 thms): the
    `(k−1)` foreign-vote cap real and tight; u-relative boundary-moving hope
    REFUTED (`F₀` unchanged); no-fully-foreign-rider.
11. **Junk-slice ledger** (this file, 5 thms): vote decomposition + junk-forced
    count; the composition's no-improvement calibrated exactly.

**Totals**: 11 new lane files + 93 kernel theorems (all
`[propext, Classical.choice, Quot.sound]` or better; every axiom list read
manually in full), 9 exact probes, 2 refutations (adversarial-domain
StallResidual; u-relative fiber cap), 3 no-go theorems (packing jaw, second-
moment jaw, junk-slice composition), 1 cross-cone identity bridge.

**Final residual map** (P1 counting branch, literal prize domain `μ_{2^30}`):
`StallResidual ⟸ SwarmResidual` = (i) 3-to-5 near-full clusters (compounding
rank-drop floors `X_m`, every known constructor dyadically blocked) + (ii) the
sub-Johnson pair-cloud swarm (counting-immune, sub-Burgess incomplete-sum list
problem — the campaign's global wall, now with its structural distinction from
the B-side wall kernel-pinned).  The operational bracket
`3/8 ≤ δ* ≤ 43/96 + 1/(3·2^30)` is exactly where the session found it.
