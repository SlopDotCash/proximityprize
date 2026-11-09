/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Fin.BigOperators

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import CompPoly.Data.Fin.BigOperators

/-!
# Compatibility exports for Fin big-operator helpers

Most Fin arithmetic and big-operator helpers in this file moved to
`CompPoly.Data.Fin.BigOperators`. This module keeps the historical ArkLib import path and the
legacy theorem name still used by older ArkLib modules.
-/

theorem Fin.sum_univ_odd_even {n : ℕ} {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ i : Fin (2 ^ n), f (2 * i)) + (∑ i : Fin (2 ^ n), f (2 * i + 1))
    = ∑ i : Fin (2 ^ (n + 1)), f i :=
  Fin.sum_univ_pow_two_even_add_odd f
