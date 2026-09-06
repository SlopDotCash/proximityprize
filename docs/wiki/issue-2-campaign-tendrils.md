# Issue 2: campaign dependencies beyond Frontier

This slice follows the reusable algebra move in PR #189. It relocates 210
campaign modules into `Research/ProximityPrize`, preserving declaration names,
theorem statements, and proof bodies. The recorded path substitutions and the
MCAPlateauWindow import adjustment are the only changes in those moved modules.

The set is the reverse-import closure of Lattice2 (including its four children),
CapacityBounds, Hab25ConjectureGlue, and the three explicitly named Whir campaign
modules, after separating reusable GS algebra. This includes Hab25/threshold
assembly files placed under BCIKS20 and campaign adapters under Connections,
GuruswamiSudan, Stir, Whir, and ToMathlib. It is a dependency slice, not a claim
that the remaining ProximityGap modules have all been classified as library math.

Three boundaries need different treatment:

- The ProximityGap umbrella stays in ArkLib and drops the moved imports.
- `Whir/ProtocolSoundness.lean` stays in ArkLib and replaces its campaign
  `MCAJohnsonBound` import with the direct library dependency
  `BCIKS20.LocalSeriesProducer`. Its theorem declarations and proofs remain intact.
- `ToMathlib/RestrictedSumsetGeneral.lean` retains the general restricted-sumset
  theorem. Its three MCA-specific corollaries move to
  `Research/ProximityPrize/Connections/RestrictedSumsetMCA.lean`, consumed by the
  relocated `MCAPlateauWindow` module.

The generated library roots contain 1,711 ArkLib imports and 3,295 Research
imports. The Research-to-ArkLib direction gate passes after the move. Source
comparison confirms that all 210 moved files match their original contents
under the recorded path changes. Documentation, whitespace, and zero-hole checks also pass. The citation map
has been regenerated for the moved paths, and the final generated-record check
passes. The full strict-token scan passes with the nine documented residual
axioms. The complete WHIR ProtocolSoundness module passes with the direct library
import; its ten printed theorem audits use only standard Lean axioms. See the
[WHIR audit](../kb/audits/whir-library-boundary-2026-09-06.json). The restricted-sumset split and its eight-module dependency chain also pass;
the general theorem and three moved corollaries use only standard Lean axioms
([audit](../kb/audits/restricted-sumset-boundary-2026-09-06.json)). Full-library Lean
validation and hosted acceptance remain pending.

The hypotheses and obstruction surfaces move with the code; none are discharged
by relocation. This work does not close issue #2 or the proof gate in #164.

The [migration manifest](../kb/audits/campaign-tendrils-migration-2026-09-06.json)
records all old/new paths and source hashes against the parent commit.
