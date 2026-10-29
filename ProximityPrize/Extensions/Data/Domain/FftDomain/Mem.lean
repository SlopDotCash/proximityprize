/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Domain.FftDomain.Mem

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Field

import ProximityPrize.Extensions.Data.Domain.CosetFftDomain.Mem
import ProximityPrize.Extensions.Data.Domain.FftDomain.Defs
import ArkLib.ToMathlib.Finset.ToListWithProof

/-!
# Membership for FFT domains

We specialize the coset membership theory to FFT domains: `one_mem`, the existence
characterizations `mem_iff_exists` and `mem_iff_mem_toCosetFftDomain`, and their `toFinset`
counterparts (`mem_toFinset_iff_exists`, `mem_toFinset_iff_mem`). A `Decidable (x ∈ ω)` instance
is also provided.
-/

namespace Domain

variable {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

namespace FftDomainClass

variable {D : Type} [FunLike D ι F] [FftDomainClass D ι F]
variable {ω : D}

end FftDomainClass

namespace FftDomain

open CosetFftDomain

variable {ω : FftDomain ι F} {x : F}

end FftDomain

instance {x : F} {ω : FftDomain ι F} : Decidable (x ∈ ω) :=
  decidable_of_iff _ FftDomain.mem_toFinset_iff_mem

end Domain
