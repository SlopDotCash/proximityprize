# δ* #466 — Stall→badCount bridge: `StallResidual` implies the P1 counting branch in full prize vocabulary (2026-07-11)

**Lane:** P1 rate-quarter predecessor pin, charge arc — referee follow-up to
`deltastar-466-rate-quarter-dcharge-referee-2026-07-11.md` (which flagged the
mcaEvent ↔ BadFamilyData vocabulary gap as the audit's only real finding).
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterStallBadCountBridge.lean`
(pg-iterate OK 16s; full axiom lists ALSO read manually via `lake env lean` given the
known pg-iterate first-line truncation: all 5 theorems exactly
`[propext, Classical.choice, Quot.sound]`, no sorryAx).

## Result

The referee-named glue theorem is landed, closing the audit's finding:

* `badFamilyData_of_mcaEvents` — **the Skolemization bridge**: for any finite
  `G : Finset F` with `∀ γ ∈ G, mcaEvent (predecessorCode dom) predecessorDelta u₀ u₁ γ`,
  there exist witness functions `(Sf, pf)` with `BadFamilyData dom u₀ u₁ G Sf pf`.
  Per-γ choice on the subtype `{γ // γ ∈ G}`, `dite`-extended off `G` by `(∅, 0)`;
  mass→threshold conversion via `agreement_mass_eq_predecessorThreshold`
  (`rw [Fintype.card_fin, …]` + `exact_mod_cast`), `smul_eq_mul` for the line agreement.
  This promotes the inline pattern of `badFamily_card_le_N_of_sharedFreshTripleFree`
  (`_P1RateQuarterSharedFreshCoordinate.lean:468–512`) to a reusable lemma.
* `badCount_le_N_of_stall : StallResidual dom → badCount (predecessorCode dom)
  predecessorDelta u₀ u₁ ≤ N` — composed with `predecessor_budget_of_stall`;
  the `badCount` unfolding is `simpa [badCount]` (decidability instances align under
  `Classical.propDecidable`).
* `all_badCount_le_N_of_stall` — uniform per-`WordStack` form (`change` to `badCount`).
* `epsMCA_predecessor_le_prizeEpsilon_of_stall : StallResidual dom →
  epsMCA (predecessorCode dom) predecessorDelta ≤ 2⁻¹²⁸` — via in-tree
  `epsMCA_le_of_badCount_le` and `N_div_P_le_prizeEpsilon` (mirroring
  `_P1RateQuarterPredecessorGenericSplit.lean:167–176`).
* `predecessorDelta_le_mcaDeltaStar_of_stall : StallResidual dom →
  predecessorDelta ≤ mcaDeltaStar (predecessorCode dom) 2⁻¹²⁸` — **the strongest honest
  in-tree corollary**: the P1 predecessor pin's counting-branch open content is now
  EXACTLY `StallResidual`, literally in the `mcaDeltaStar` currency, per evaluation
  domain.

## What is NOT claimed

* No discharge of `StallResidual` (bad families all of whose base scalars carry pools
  `F ≥ F₀ + 1 = 75018134`; `_P1RateQuarterDChargeDerecursion.lean`) — still OPEN,
  still the beyond-Johnson prize wall.
* No δ* movement — the corollary is conditional on the open residual; the operational
  bracket `3/8 ≤ δ* ≤ 43/96 + ε` is untouched.

## Build notes

* The closure file's olean did not exist (frontier files are iterated with
  `pg-iterate`, which produces no oleans); built it once with
  `./scripts/lake-locked.sh build ArkLib.….Frontier._P1RateQuarterSmallPoolClosureDischarged`
  (8434 jobs, OK) so the bridge could import it.
* `ℝ≥0∞` needs `open scoped ENNReal` in frontier files (only `NNReal` is opened by the
  lane template); missing it surfaces as a bare `expected token` at the `⁻¹`.
* Cross-namespace abbrev mixing (`predecessorCode`/`predecessorDelta` from
  `SharedFreshCoordinate` vs `PredecessorGenericSplit`) unifies fine — they are
  definitionally equal `abbrev`s; open only ONE namespace and fully qualify the other's
  lemmas (`…PredecessorGenericSplit.N_div_P_le_prizeEpsilon`) to avoid ambiguity.

## Consumers / next

Any future discharge of `StallResidual dom` (stall band `F ∈ [75018134, 480946859]`,
sub-regimes split at `F = k = 2²⁸`) now yields `predecessorDelta ≤ mcaDeltaStar` for the
predecessor code with NO further glue.
