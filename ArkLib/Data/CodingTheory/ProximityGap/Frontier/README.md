# Proximity Gap — Frontier scratch lanes (#334 → #444 → #464 → #466)

Drop-in starting points for the actionable open targets. Each file:
- imports ONLY its minimal substrate (fast `lake env lean`, ~30s, no build lock),
- states the precise target as an honest named `Prop`/hypothesis (no `sorry`, no fake `axiom`),
- documents the reference + the in-tree substrate API to consume.

**Iterate:** `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/<File>.lean`
**Land:** one real `lake build <Module>` (autoImplicit=false) + axiom audit, then the push loop.
**Lane hygiene:** files starting `_` are scratch/lane files (most are git-tracked — treat them as
lane state, not throwaway); copy `_TEMPLATE.lean` to start a new lane.
Read the parent `CLAUDE.md` (build/concurrency/honesty rules) before touching anything.

## Live targets (2026-07-01)

**The current campaign is #466.** The ranked live frontier is
`docs/kb/deltastar-DOSSIER-v3-2026-07-01.md` §6 (as re-ranked by the §14/§15 round logs) and
`../PROXIMITY_PRIZE_WORKBENCH.lean` §5 — go there for what to attack; this README only records
the status of the original #334-era lane files below.

## Status of the original #334 lane files

| file | target | status (2026-07-01) |
|------|--------|---------------------|
| `ThornerZamanS128.lean` + `ThornerZamanInstance.lean` | discharge `TZPrimeSupply` (window `[n^β, 2n^β]` has ≥ supply primes `≡ 1 mod n`) | **Concrete ladder LANDED** (axiom-clean, explicit-prime certificates): β=2 through `n = 32768` (`tzPrimeSupply_{8,16,…,32768}_two`), β=3 through `n = 64`, β=4 through `n = 64`, β=5 at `n = 8` — all in `ThornerZamanInstance.lean` (+ `CanonicalWidthFourConcreteTZ.lean`). The *general/asymptotic* Thorner–Zaman PNT-in-APs form remains a named open hypothesis (dossier v3 §6 Tier 3, "largely dischargeable"). |
| `CurveDecodability.lean` | [GG25] Def 3.1 curve decodability → [Jo26] half | OPEN, multi-brick (dossier v3 §6 Tier 3; folded-RS capacity pin via `curveDecodable_of_structured_close_set_budget` is the live adjacent lane). **RE-PLAN TARGET (2026-07-10):** GGSW arXiv:2607.08516 (Jul 9) casts curve-decodability directly as a row-span-constrained LCL property with black-box transference from subspace designs — formalize against THAT formulation, not the [Jo26] proxy; see `docs/kb/deltastar-466-litsweep-2026-07-10.md`. ([JLR 2601.10047] is withdrawn, subsumed by GG25 — update stale citations.) |
| `EquivariancePin.lean` | Lean equivariance pin for the n=12 orbit reduction | LANDED → `../MCAEquivariance.lean` (engine) + `../MCAEigenstackOrbitLaw.lean` (orbit law, counting) |

Historical note: predecessors #334/#357/#444/#464 are CLOSED, each distilled into its
successor; the `_`-prefixed files in this directory are the accumulated lane record of those
campaigns plus the live #466 lanes. Check `../DISPROOF_LOG.md` (`466-r*` round tags, still
accumulating) before re-attempting anything.
