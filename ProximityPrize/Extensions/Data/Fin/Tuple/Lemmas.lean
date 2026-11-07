/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Fin.Tuple.Lemmas

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ProximityPrize.Extensions.Data.Fin.Tuple.Notation

/-!
  # Lemmas for new operations on `Fin`-indexed (heterogeneous) vectors
-/

universe u v w

private lemma cast_eq_cast_same_type {α β : Sort u} (h1 h2 : α = β) {x y : α}
    (h : cast h1 x = cast h2 y) : x = y := by
  subst_vars
  rfl

namespace Fin

variable {m n : ℕ} {α : Sort u}

section FunctorialBinary

variable {A : Sort u} {B : Sort v} {F₂ : A → B → Sort w} {m n : ℕ}

end FunctorialBinary

section FunctorialUnary

variable {A : Sort u} {F : A → Sort v} {m n : ℕ} {α : A}

end FunctorialUnary

/-! ### Lemmas for heterogeneous vectors -/

variable {m n : ℕ} {α : Sort u}

-- @[simp, grind =]
-- theorem concat_eq_append {α : Sort u} {n : ℕ} (v : FinVec α n) (a : α) :
--     concat v a = append v (FinVec.cons a FinVec.empty) := by
--   ext i; fin_cases i <;> rfl

section padding

end padding

end Fin
