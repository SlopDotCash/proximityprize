# δ* #466 — Stall-band census: extremal families are two-pencil covers at capacity `2(N−T+1)`; single- and double-pencil `StallResidual` instances become theorems (2026-07-11)

**Lane:** P1 rate-quarter predecessor pin, charge arc — empirical calibration of the
pin's sole open content, `StallResidual` (`_P1RateQuarterDChargeDerecursion.lean`:
bad families all of whose base scalars carry pools `F ∈ [75018134, 480946858]`).
**Probe:** `scripts/probes/probe_rate_quarter_p1_stall_band_census.py` (deterministic,
exact integer arithmetic; scaled shapes with the exact P1 ratios
`T = ⌈N·592794966/2^30⌉`, `k = N/4`).
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterStallBandCensus.lean`
(pg-iterate OK 14s; 16 theorems; full axiom lists ALSO read manually via
`lake env lean`: 15 exactly `[propext, Classical.choice, Quot.sound]`, 1 `[propext]`;
no sorryAx, no new axioms/hypotheses).

## Census findings (part a: do maximal stall families exist, and how big?)

Scaled boundaries (all kernel-pinned in the new file): μ_128 `F₀=10`, band `[11,57]`;
μ_256 `F₀=20`, band `[21,114]`; μ_512 `F₀=37`, band `[38,229]`.

| scale | q | max #stall-bad found | vs N | structure |
|---|---|---|---|---|
| μ_16 (exhaustive per pair, all 17⁴ codewords) | 17 | **16 = N** | **TIGHT, zero slack** | two-pencil cover at capacity (2(T−1)=N) |
| μ_128 | 131 / 521 | 116 = 2(N−T+1) | 0.906·N | dual two-pencil construction |
| μ_256 | 257 / 1031 | 230 = 2(N−T+1) | 0.898·N | dual two-pencil construction |
| μ_512 | 521 / 1031 | 460 = 2(N−T+1) | 0.898·N | dual two-pencil construction |

* Maximal stall-band families **exist at every scale**; every realized pool sits at
  the TOP of the band (`F = N − T`), agreement exactly `T`.
* **The μ_16 surprise (exhaustive):** the designed weight-`N−T+1` single-pencil error
  pattern spawned an *emergent second pencil* aligned on the error support — 8 of the
  16 bad scalars are served by codewords OFF the designed pencil.  The extremal
  family is exactly a **two-pencil cover at capacity `2(N−T+1)`**, which equals `N`
  at μ_16 (`2(T−1) = 16`).  So the `≤ N` budget has NO slack at the degenerate scale
  — the residual is not generically slack.
* **Dual construction at real ratios** (`2(T−1) > N`): aligned regions
  `A₁, A₂` of size `T−1` overlapping in `2T−2−N ≤ k−1` coords (fits — at prize scale
  `111848106 ≤ 268435455`); second pencil `v² = v¹ + (x·d, d)` with `d = z·c`, `z`
  vanishing on the overlap.  The cancellation-ratio map is `γ = −x` — **injective** —
  so each pencil harvests one bad scalar per coordinate of the other's private
  region: exactly `2(N−T+1)`, verified exactly at μ_128/μ_256/μ_512 with every
  BadFamilyData clause checked (threshold, codewordness, line agreement,
  non-jointness).
* **Nothing beat two pencils.**  Hill-climbed 3-pencil composites produced FEWER bad
  scalars: a third pencil's cancellation ratios are values of a deg `< k` rational
  function on the other pencils' aligned regions and collide instead of spreading.
  The pairwise-fit arithmetic `m(T−1) − C(m,2)(k−1) ≤ N` admits `m = 3`, but the
  ratio-collision mechanism eats the harvest.

## Part (b): direction structure on `Z`

For the best μ_256 single-pencil family (base pool `F = 114 = N−T`, `|Z| = 142`,
stall window on `Z` `[28, 94]`): all 114 rider directions sit at agreement
`> J_Z` (the "counted" bucket) — census families are top-of-band witnesses whose
directions are Johnson-visible; the *uncounted* sub-window population was never
realized by any construction tried.  (The wall is that nothing rules it out.)

## Part (c): the gap, and what was formalized

Realized maximum = `2(N−T+1) ≈ 0.898·N` at real ratios; remaining room to the budget
is exactly `2T − N − 2 = 111848106 ≈ 0.104·N` at prize scale.  Kernel-checked (new
file, PRIZE shape unless noted):

* `pool_card_le_N_sub_T'` — local re-proof of the universal pool bound (keeps the
  import at the derecursion layer, whose olean exists).
* `singlePencil_card_le`, `singlePencil_cap_le_N`, `stall_budget_of_single_pencil` —
  **any bad family riding a single pencil has `#bad ≤ N − T + 1 = 480946859 ≤ N`**:
  the `StallResidual` obligation holds unconditionally on the single-pencil subclass
  (stall-pool hypothesis not even needed).  First evidence-grade brick on the wall.
* `twoPencil_cap_le_N`, `stall_budget_of_two_pencil_cover`,
  `stallResidual_of_pencil_pair_cover` — the census's EXTREMAL class (two-pencil
  covers) also obeys the budget: `2(N−T+1) = 961893718 ≤ N`; the last theorem carries
  the literal `StallResidual` stall-pool hypothesis shape.
* `threePencil_cap_overflows` (`N < 3(N−T+1)`) — the counting route ends at two
  pencils; `twoPencil_slack` (`= 111848106`), `dual_construction_fits`
  (`2(T−1) − N ≤ k − 1`) — the extremal construction scales to the prize shape.
* Scaled rungs: `mu128_boundary`, `mu256_boundary`, `mu512_boundary`,
  `mu_thresholds_exact`, `mu_singlePencil_caps`, `mu_twoPencil_caps` (incl. μ_16
  tightness `2(16−9+1) = 16`).

## Honesty

* `StallResidual` is NOT discharged.  Open content after this round: bad families
  whose witnesses ride **three or more distinct pencils** (or none — scalars whose
  codewords lie on no shared pencil).  The census never realized such a family
  beating even one pencil's harvest, but only constructions within designed pencil
  pools were searched at μ ≥ 128 (lower-bound census; the μ_16 exhaustive layer is
  the only completeness check, and it is degenerate: `T = 9` is barely
  above Johnson `⌊√(N(k−1))⌋ = 8`, and `q = N + 1`).
* The μ_16 zero-slack data point means any discharge of `StallResidual` must use the
  real-ratio inequality `2(T−1) > N` (equivalently `T > N/2 + 1`) — a scale-free
  argument valid at all shapes would be FALSE at μ_16-style shapes where `2(T−1)=N`
  and the budget is exactly attained.
* No δ* movement; bracket `3/8 ≤ δ* ≤ 43/96 + 1/(3·2^30)` untouched.  Probe census at
  μ ≥ 128 is a lower-bound census by design (soundness of the designed-pencil
  detector validated exhaustively at μ_16: zero false positives).

## Next target

Close the `0.104·N` corridor: prove that a bad family's witnesses are covered by at
most TWO pencils *up to a `2T−N−2`-sized remainder* — e.g. a third-pencil harvest
bound via the ratio-collision mechanism (`γ = −a/b` with `a, b` codeword differences:
each value has multiplicity ≤ k−1, but on another pencil's aligned region `a, b` are
CONSTRAINED codeword differences — the collision observed empirically wants a
degree/injectivity argument).  If the per-extra-pencil harvest can be capped by
`(2T−N−2)/1` in total, `StallResidual` follows.
