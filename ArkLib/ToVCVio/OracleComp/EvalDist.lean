/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToVCVio.ToMathlib.Data.Vector.Basic
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.Constructions.Replicate

/-!
# Compatibility import for VCV-io's `OracleComp.EvalDist`

The pinned dependency now proves `OracleComp.support_ofFn_mapM_index` in
`VCVio.OracleComp.Constructions.Replicate`. Keep this import path for existing
clients without redeclaring that theorem.
-/
