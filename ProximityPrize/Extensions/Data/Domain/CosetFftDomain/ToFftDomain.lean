/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Domain.CosetFftDomain.ToFftDomain

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Field

import ProximityPrize.Extensions.Data.Domain.CosetFftDomain.Mem
import ProximityPrize.Extensions.Data.Domain.FftDomain.Mem

/-!
# Converting a coset FFT domain to an FFT domain

We define `toFftDomain`, normalizing a coset FFT domain `ω` into an `FftDomain` (coset generator
set to one). The evaluation bridge `eval_toFftDomain` and the membership characterization
`mem_toFftDomain_iff_mul_mem` relate the two domains, with `mul_mem` corollaries and the
finset-image / cardinality lemmas (`toFinset_image_toFftDomain_eq_toFinset`,
`card_toFinset_eq_card_toFftDomain_toFinset`) describing the image set.
-/

namespace Domain

variable {ι : Type} [AddCommGroup ι]
variable {F : Type} [Field F]

namespace CosetFftDomainClass

variable {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]

end CosetFftDomainClass

namespace CosetFftDomain

variable {ω : CosetFftDomain ι F} {x : F}

end CosetFftDomain

namespace FftDomain

lemma toFffDomain_eq_self {ω : FftDomain ι F} :
    ω.toFftDomain = ω := by
  exact toFftDomain_eq_self

end FftDomain

end Domain
