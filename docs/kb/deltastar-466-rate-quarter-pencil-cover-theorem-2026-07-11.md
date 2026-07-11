# δ* #466 — Pencil-cover round (residual c): pair-pencil existence with a `2T−N` alignment floor + the margin-free four-pencil pair-cover budget; open content = the many-pencil regime (2026-07-11)

**Lane:** P1 rate-quarter — residual (c) round (cover-by-few-pencils), sixth round
of the 2026-07-11 arc.
**Probe:** `scripts/probes/probe_rate_quarter_p1_pencil_cover.py` (exact).
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterPencilCoverTheorem.lean`
(pg-iterate OK 12s; 6 theorems; full axiom lists read manually via `lake env lean`:
5 exactly `[propext, Classical.choice, Quot.sound]`, 1 `[propext]`; no sorryAx, no
warnings).

## The math

* **Cover existence is a theorem.**  Every pair of bad scalars rides its
  divided-difference pencil (in-tree `pencil_reproduces_first/second`), and the
  pencil's aligned set contains the pairwise witness intersection
  (`pencil_agrees_on_inter`), of size `≥ 2T − N = 111848108` — kernel:
  `pair_pencil_aligned_floor` + `pairPencil_floor_constant`.  Residual (c)'s
  existence half is closed; only FEWNESS was ever at stake.
* **Pencils partition pairs.**  Distinct pencils share ≤ 1 rider, so
  `B(B−1) = Σ_π m_π(m_π−1)` with the unconditional cap `m_π ≤ c = N−T+1 =
  480946859`.  Pigeonhole: a pair-cover by `P` pencils forces `B² ≤ P·c²`; at
  `P = 4`: `B ≤ 2c = 961893718 ≤ N`.
* **Kernel: `stall_budget_of_four_pair_pencil_cover`** — bad families whose PAIRS
  are covered by four pencils obey the `StallResidual` budget, with NO margin,
  alignment, or pool hypotheses (proof: the ordered square `G ×ˢ G` is covered by
  the four rider squares — diagonal handled by pairing with any second element —
  then `B² ≤ 4c²` and `(2c+1)² > 4c²`).  Contrapositive
  (`overBudget_no_four_pencil_pair_cover`): over-budget families admit no
  four-pencil pair-cover.
* **The route caps at four**: `(N+1)² ≤ 5c²` (`five_cover_insufficient`) — five
  pencils no longer pin the budget.

## Probe (exact)

The census's extremal dual family (`B = 230 = 2c'` at μ_256/q=1031): pair-pencil
distribution `{m=115: 2 pencils, m=2: 13225 pencils}`, 13227 distinct pencils, and
the partition identity `Σ m(m−1) = B(B−1) = 52670` holds exactly.  Extremal
families are MANY-pencil objects: two capacity pencils plus a quadratic cloud of
pair-only pencils (each `(2T−N)`-aligned).  De Bruijn–Erdős-type facts force
over-budget families to have `≥ B` distinct pencils — the open content is this
many-pencil regime, i.e. the sub-Johnson direction swarm of the derecursion file,
unchanged (the second-moment packing test `a² vs N(k−1)` stays on the feasible
side since `2T−N < √(N(k−1))` — everything funnels to the same wall).

## Cover-class budget map after this round (all kernel, prize shape)

| cover class | hypothesis | budget theorem |
|---|---|---|
| 1 pencil (scalar) | none | `≤ 480946859` (`riders_card_le_uniform`) |
| 2 pencils (scalar) | none | `≤ 961893718` (`stall_budget_of_two_pencil_cover`) |
| 3 pencils (scalar) | third margin ≥ 5 (probe-forced `T−k`) | `≤ 1058083090 ≤ N` |
| 4 pencils (scalar) | two margins ≥ 9 | `≤ 1068770798 ≤ N` |
| ≤ 4 pencils (PAIR level) | none | `≤ 961893718 ≤ N` (this round) |
| ≥ 5 pencils (pair level) | — | OPEN (the wall) |

## Honesty

`StallResidual(μ_{2^30})` remains OPEN: the many-pencil regime is untouched (and
must be — it contains the extremal `2(N−T+1)` families; any closure must exploit
that their pair-pencil clouds are value-collision-limited, which at prize scale is
the same beyond-Johnson content as ever).  No δ* movement; bracket
`3/8 ≤ δ* ≤ 43/96 + 1/(3·2^30)` untouched.

## Next targets

1. The pair-pencil cloud second moment: the 13k pair-only pencils of an extremal
   family are `(2T−N)`-aligned with pairwise aligned-intersections ≤ k−1; an
   over-budget family's cloud has `≥ N+1` such pencils — quantify what the cloud's
   incidence structure forces on `u₁`'s direction list (connects to the W-lane
   list-size machinery).
2. De Bruijn–Erdős formalization (lines = pencils with ≥ 2 riders) to make the
   `≥ B` distinct-pencil floor kernel-checked.
