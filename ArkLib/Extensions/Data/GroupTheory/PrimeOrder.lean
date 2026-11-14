/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.GroupTheory.PrimeOrder

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Prime Order Groups

This file defines the `PrimeOrder` type class, which asserts that a group has some prime order `p`.

We also define the unbundled version, `PrimeOrderWith`, which has the prime order `p` as an explicit
output parameter. -/

namespace PrimeOrder

variable {G : Type*} [Group G] [PrimeOrder G]

end PrimeOrder

namespace PrimeOrderWith

variable {G : Type*} [Group G] {p : outParam ℕ} [Fact (Nat.Prime p)] [PrimeOrderWith G p]

end PrimeOrderWith
