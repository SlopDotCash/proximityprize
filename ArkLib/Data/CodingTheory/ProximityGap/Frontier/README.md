# Proximity Gap — Frontier scratch lanes (#334)

Drop-in starting points for the actionable open targets. Each file:
- imports ONLY its minimal substrate (fast `lake env lean`, ~30s, no build lock),
- states the precise target as an honest named `Prop`/hypothesis (no `sorry`, no fake `axiom`),
- documents the reference + the in-tree substrate API to consume.

**Iterate:** `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/<File>.lean`
**Land:** one real `lake build <Module>` (autoImplicit=false) + axiom audit, then the push loop.
**Lane hygiene:** files starting `_` are throwaway; copy `_TEMPLATE.lean` to start a new lane.
Read the parent `CLAUDE.md` (build/concurrency/honesty rules) before touching anything.

| file | target | status | blocker |
|------|--------|--------|---------|
| `ThornerZamanS128.lean` + `ThornerZamanInstance.lean` | discharge `TZPrimeSupply` (PNT-in-APs) → s=128 prize rows; concrete finite rows live in `ThornerZamanInstance.lean` | OPEN, concrete | analytic NT only |
| `CurveDecodability.lean` | [GG25] Def 3.1 curve decodability → [Jo26] half | OPEN, multi-brick | from scratch |
| `EquivariancePin.lean` | Lean equivariance pin for the n=12 orbit reduction | LANDED → `../MCAEquivariance.lean` (engine) + `../MCAEigenstackOrbitLaw.lean` (orbit law, counting) | — |
