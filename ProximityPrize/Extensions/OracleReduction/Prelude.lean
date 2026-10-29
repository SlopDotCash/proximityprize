/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.OracleReduction.Prelude

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Batteries.Data.Vector.Lemmas
import VCVio.OracleComp.Constructions.SampleableType

/-!
  # Prelude for Interactive (Oracle) Reductions

  This file contains preliminary definitions and instances that is used in defining I(O)Rs.
-/

open OracleComp

-- -- Notation for sums (maybe not needed?)
-- @[inherit_doc] postfix:max "↪ₗ" => Sum.inl
-- @[inherit_doc] postfix:max "↪ᵣ" => Sum.inr

namespace Direction

end Direction

section Relation

-- This can use mathlib's `Rel` once it becomes `Set`-based upstream.

end Relation
