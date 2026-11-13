/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Classes.FunEquiv

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Logic.Equiv.Defs

/-!
# FunEquiv

This file defines the `(D)FunEquiv` type class, which expresses that a given type `F` has an
equivalence to a dependent function type.

This is stronger than `(D)FunLike` since we get an equivalence and not just an injection into the
dependent function type.
-/

namespace DFunEquiv

variable {F : Sort*} {α : Sort*} {β : α → Sort*} [inst : DFunEquiv F α β]

-- The canonical module already provides the DFunLike coercion from this equivalence.

end DFunEquiv
