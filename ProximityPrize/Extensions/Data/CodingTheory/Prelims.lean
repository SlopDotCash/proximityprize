/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.Prelims

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Chung Thai Nguyen
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.RingTheory.Henselian

/-! # Coding-Theory Preliminaries -/

section TensorCombination
variable {F : Type*} [CommRing F] [Fintype F] [DecidableEq F]
         {A : Type*} [AddCommMonoid A] [Module F A]

end TensorCombination
noncomputable section

variable {F : Type*}
         {ι : Type*} [Fintype ι]
         {ι' : Type*} [Fintype ι']
         {m n k : ℕ}

namespace Matrix

section

variable [Semiring F] (U : Matrix ι ι' F)

end

section

variable [CommRing F] [Nontrivial F]
         {U : Matrix (Fin m) (Fin n) F}

end

section

variable [Field F]
         {U : Matrix (Fin m) (Fin n) F}

end

end Matrix

namespace LinearCombination

end LinearCombination

end

namespace Affine
section
variable {ι : Type*} [Fintype ι]
         {F A : Type*}
         {k : ℕ}

variable [DecidableEq F] [Ring F] [Fintype F]

-- The canonical `AffSpanSet.instFinite` is a Set.Finite theorem, not a typeclass instance.

end
end Affine

namespace Curve

section

variable {ι : Type*}
         {F A : Type*} [Semiring F]
         [AddCommMonoid A] [Module F A]

end

section

open Finset
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         -- For usage with linear code, we set A = F
         {F A : Type*} [Semiring F] [Fintype F]
         [AddCommMonoid A] [Module F A] [Fintype A] [DecidableEq A]

open Finset
end
end Curve

namespace sInf

end sInf

namespace Finset

section

variable {α : Type*} [DecidableEq α] {s : Finset α}

variable [Fintype α]

end

end Finset
