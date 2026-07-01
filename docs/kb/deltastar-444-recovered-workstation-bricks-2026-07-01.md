# #444 phantom-brick recovery — the unpushed workstation branch (2026-07-01)

**Verdict in one line:** the five "phantom bricks" flagged in dossier v2 §12 (`_DstarGrowthLaw`,
`_OPSingleOrbit`, `_DyadicRecursionDstar`, `PrizeEquivalencePin`, `FloorResonanceEnergyBridge`)
were never fabricated — they were written and verified on a workstation whose #444 session ended
without pushing; the files have been recovered, re-verified axiom-clean against 2026-07-01 main,
and landed. **No conclusion changes**; the honesty flag is resolved from "phantom" to
"recovered + verified."

## What happened

The #444 campaign checkout `claude/444-charzero-dyadic-rigidity` on this workstation accumulated
76 unabsorbed commits and ~150 uncommitted files (2026-06-13 → 06-17) that never reached `main`
(the session's push loop was never run to completion). Issue comments cited the brick names as
landed; the dossier v2 honesty audit (2026-06-22) correctly flagged them as absent on every branch
and re-founded the affected conclusions on independently-verified bricks
(`_MomentLadderExceedsPrize`, `_EnergyRatioMonotoneReduction`, `KambireDeepBandFloor`,
`OverdetIncidenceMaxClosedForm`).

## What is recovered and landed (all `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`)

| File (`Frontier/`) | Headline theorem(s) | Verdict it records |
|---|---|---|
| `_DstarGrowthLaw.lean` | `dStar3_gt_budget`, `orbit_count_unbounded`, `offBGK_overdet_caps_below_window` | p-independent distinct-γ count `D* = Θ(n³) ≫ budget`; off-BGK far-line route caps below the window |
| `_OPSingleOrbit.lean` | `OP_single_orbit_refuted` | `O_P = 1` persistence REFUTED — `O_P = n/8 − 1` exactly (`= 1` only at n = 16) |
| `_DyadicRecursionDstar.lean` | `symmetric_dyadic_halving` | the dyadic halving recursion for the binding count is REFUTED (exact only for the symmetric stratum); binding `m*` is LINEAR, not log |
| `PrizeEquivalencePin.lean` | `prizeFloor_eq_value_iff_bindingCount_brackets`, `no_second_order_route`, `prizeFloor_from_growthLaw` | the airtight prize ⟺ binding-count equivalence + method-necessity companion |
| `FloorResonanceEnergyBridge.lean` | `worst_period_sq_ge_of_energyRatioGrowth`, `energyRatioGrowth_fails_of_no_floor` | floor lower bound wired to the energy-ratio wall via reverse-Markov |
| `_S2NonSymTower.lean` | `singletonCount_le_curve_degree` etc. | non-symmetric squaring-tower singleton-fiber decomposition (CRACK D reduces to the wall) |
| `SymmetricTowerBracket.lean` | (dependency of `_DyadicRecursionDstar`) | the symmetric-stratum tower bracket engine |

Also landed from the same branch: the #444 KB notes that cited these bricks (verbatim, they are
honest no-go/retraction records) and the non-underscore `probe_444_*` / `angleB_*` probe scripts
that generated their numerics.

## Where the rest lives

The complete branch (83 committed Frontier files missing from main + all scratch `_`-files and
probes) is preserved at **`archive/444-charzero-dyadic-rigidity`** on the fork. Nothing else from
it is landed on main; consult the archive before re-deriving any #444-era object.

## The operational lesson

A cited brick must be verifiable on `main` at cite time. Push before the session ends; when a
result is posted to an issue, the push loop is part of the claim.
