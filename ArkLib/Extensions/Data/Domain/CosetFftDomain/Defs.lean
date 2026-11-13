/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Domain.CosetFftDomain.Defs

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

/-!
# Coset FFT domains

This file defines coset FFT domains: evaluation domains of the form `x · G` for an FFT
subgroup domain `G`.  The data is packaged as a structure `CosetFftDomain` (an injective
group embedding `Multiplicative ι →* Fˣ` together with a coset generator) and an
abstract interface `CosetFftDomainClass` characterizing such maps via `map_zero_unit`,
`map_add`, and `map_neg`.  It provides the `FunLike` instance, the evaluation identity
`eval_coset_fft_domain_eq_eval_generator_mul_domain`, conversions between the structure and
the class (`mkSubgroupUnit`, `toCosetFftDomain`), injectivity lemmas, the `SmoothCosetFftDomain`
abbreviation, and the underlying `Finset` of evaluation points (`toFinset`, `card_toFinset`).
-/

/-! The canonical module supplies the concrete coercion, class instance and embedding coercion.
The former copies imposed additional finite-domain assumptions and introduced no extra API. -/
