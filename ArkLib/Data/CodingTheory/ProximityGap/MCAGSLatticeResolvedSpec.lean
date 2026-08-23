/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.MCAGSLatticeSpec

/-!
# Exact GS MCA prize resolution specification re-exports

`MCAGSLatticePrizeSpec.lean` now owns the adjacent-upper-witness front doors that resolve the
four-rate faithful MCA prize at the concrete lower-frontier lattice indices and expose the
satisfy/maximality specification supplied by `mcaPrizeLatticeResolved_iff`.

This file remains as the lightweight compatibility/audit module for those public declarations.
-/

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators NNReal ENNReal

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace GrandChallengesLattice

open GrandChallenges

set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_of_GSMassFrontiers_and_adjacent_upperWitnesses
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_of_GSPivotFrontiers_and_adjacent_upperWitnesses

end GrandChallengesLattice

end ProximityGap
