/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Fin.Sigma

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.BigOperators.Fin
import ProximityPrize.Extensions.Data.Fin.Basic
import ArkLib.Data.Fin.Fold
import ProximityPrize.Extensions.Data.Fin.Tuple.Lemmas

/-!
# Fin Sigma Equivalences

We re-define big-operators sum and product over `Fin` to have good definitional equalities.
-/

universe u v w

open Finset

namespace Fin

section BigOperators

variable {α : Type*}

variable {n : ℕ}

end BigOperators

end Fin

namespace Fin

section Sigma

variable {m : ℕ} {n : Fin m → ℕ}

@[simp]
theorem splitSum_embedSum_fst {m : ℕ} {n : Fin m → ℕ} (i : Fin m) (j : Fin (n i)) :
    (splitSum (embedSum i j)).1 = i :=
  congrArg Sigma.fst (splitSum_embedSum i j)

end Sigma

end Fin

namespace Fin

variable {α : Sort*}

section FinSigmaFinEquiv

variable {n : ℕ}

end FinSigmaFinEquiv

end Fin
