# δ* #466 — Referee audit of the P1 D-charge chain / SmallPoolClosure discharge (2026-07-11)

**Role:** adversarial skeptic/referee, tag `[rate-quarter-dcharge-referee-audit]`.
**Claim audited:** "the P1 rate-quarter predecessor pin's open content is exactly
`StallResidual` (`predecessor_budget_of_stall`), with `SmallPoolClosure` discharged
unconditionally."

## Verdict

**The chain SURVIVES in its own vocabulary.**  Independent re-verification
(`lake env lean`, full message output, not just `pg-iterate` first-lines): all
audited theorems in `_P1RateQuarterSmallPoolAssembly.lean` (7) and
`_P1RateQuarterSmallPoolClosureDischarged.lean` (9) — including
`smallPoolClosure_holds` and `predecessor_budget_of_stall` — depend on exactly
`[propext, Classical.choice, Quot.sound]`.  No `sorryAx`, no custom axioms.

One real finding (LOW/MEDIUM severity, vocabulary gap, not a math hole) — see §3.

## 1. What was attacked and held

1. **Dichotomy coverage** (`predecessor_budget_of_smallPool_and_stall`,
   `_P1RateQuarterSmallPoolAssembly.lean:217`): `by_cases` on
   `∀ γ₀ ∈ G, 75018134 ≤ pool` + `push_neg` is exhaustive; the two Props use exact
   complementary bounds (`≤ 75018133` vs `75018134 ≤`); the empty family falls
   vacuously into the stall branch (`0 ≤ N`).  Quantifier pattern is right: base
   scalar EXISTENTIAL in `SmallPoolClosure`, UNIVERSAL stall in `StallResidual`.
2. **Quantifier order**: both Props and all consumers are
   `∀ u₀ u₁ G Sf pf …` with `dom` the outer parameter; nothing fixes the stack;
   `smallPoolClosure_holds` is `∀ dom`.
3. **Marginal partition** (`smallPool_budget`): fiber partition exact
   (`card_eq_sum_card_fiberwise`); pool cap and vote charge used strictly
   PER-FIBER (no cross-fiber vote-disjointness is claimed or needed); layer cake
   is a generic identity; `m·(T−A) ≤ F ⇒ A ≥ T − ⌊F/m⌋` is nat-division-correct;
   `johnson_core_rel` transports in-tree `R15Bracket.johnson_core` to the
   `{x // x ∈ Z}` subtype with cards preserved (`card_attach_filter`); pairwise
   `< k` overlaps come from `predecessor_sep` (RS separation on `k` points);
   the `m = 2, 3` monotonisations move both sides in the correct direction
   (`Z = N − F ≤ N − m·⌊F/m⌋`).
4. **Constants recomputed independently** (exact integer arithmetic):
   - `T = 592794966 = 8m + r + d + 2` with `m = 2²⁶`, `r = (m−1)/3 = 22369621`,
     `d = (m−2)/2 = 33554431` — matches `predecessorThreshold_eq`;
   - `N = 2³⁰ = 1073741824`, `k = 2²⁸`, `F = ZMod P`, `P` the 2^30-shaped prime;
   - Johnson boundary: `(T−F)² > (N−F)(k−1)` TRUE at `F₀ = 75018133`, FALSE at
     `F₀+1` — the derecursion boundary is exact;
   - caps: `m=1` division = `657668325` at `F₀` (attained); `m=2` cap `7`;
     `m≥3` cap `5` (Lean proves the uniform sweep coefficientwise; endpoint
     spot-checks agree);
   - pinned products `657668326·378645484 = 249023141609739784 >
     249023141355186198 = 998723691·249341378` — both exact;
   - ledger `1 + 657668325 + 7 + 5·(75018133 − 2) = 1032758988 ≤ N`.
5. **Honesty labels**: `SmallPoolClosure` correctly labelled OPEN in the assembly
   file and discharged only in the (read-only) successor; `StallResidual`
   correctly OPEN; probes are cross-checks only; kb notes match formal content.

## 2. Verification note on `pg-iterate.sh`

`pg-iterate` prints only the FIRST LINE of each `#print axioms` message
(`grep "depends on axioms"`), which at default pretty-printer width truncates the
list to `[propext,`.  Its `sorryAx` gate still catches sorries, but a referee
should re-run `lake env lean <file>` and read the full multi-line lists (done
here; all clean).

## 3. The one real finding: mcaEvent ↔ BadFamilyData vocabulary gap

The chain's endpoint currency is the Skolemized `BadFamilyData`
(`_P1RateQuarterPencilCountCharge.lean:359` — explicit `Sf`, `pf` witness
functions).  The pin's prize-facing currency is `badCount`/`mcaEvent`
(`_P1RateQuarterPredecessorGenericSplit.lean:115-190`:
`badCount ≤ N ⇒ epsMCA ≤ 2⁻¹²⁸ ⇒ predecessorDelta ≤ mcaDeltaStar`).

**There is no landed lemma**
`StallResidual dom → badCount (predecessorCode dom) predecessorDelta u₀ u₁ ≤ N`.
The needed bridge (per-γ Skolemization of the `mcaEvent` existentials into
`Sf`/`pf`, plus the mass-to-threshold conversion
`agreement_mass_eq_predecessorThreshold`) is routine classical choice and is
already demonstrated inline in `badFamily_card_le_N_of_sharedFreshTripleFree`
(`_P1RateQuarterSharedFreshCoordinate.lean:468-512`), but it is not formalized
for this chain.

**Precise form of the claim that is actually proved:** "the P1 predecessor pin's
open content *through the counting branch, in `BadFamilyData` vocabulary*, is
exactly `StallResidual`."  Before the swarm quotes the single-residual form
against `mcaDeltaStar`, land a ~30-line `badCount_le_N_of_stall` glue theorem.

## 4. Files audited (read-only)

- `_P1RateQuarterGlobalConsistencyCharge.lean` (D-pool/sink partition, vote
  source, heavy-window closure, `GlobalConsistencySwarmResidual`)
- `_P1RateQuarterDChargeDerecursion.lean` (`StallResidual`,
  `derecursion_boundary`, `johnson_condition_of_le_boundary`)
- `_P1RateQuarterMDSPoolSecondCharge.lean` (analysis theorems only; nothing in
  the closure chain depends on it logically)
- `_P1RateQuarterSmallPoolAssembly.lean`, `_P1RateQuarterSmallPoolClosureDischarged.lean`
  (re-built, axiom lists verified in full)
- upstream: `_P1RateQuarterPencilCountCharge.lean`,
  `_P1RateQuarterSharedFreshCoordinate.lean`, `_P1RateQuarterScaleArithmetic.lean`,
  `_P1RateQuarterCommonFactorArithmetic.lean`, `ScaleBracketFull.lean`
  (`R15Bracket.johnson_core`), `_P1RateQuarterLayerCakeBudget.lean`
  (`johnson_core_to_subtracted`).
