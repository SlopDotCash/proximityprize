/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Domain.FftDomain.Defs

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

import ProximityPrize.Extensions.Data.Domain.CosetFftDomain.Defs

/-!
# FFT domains

We define the `FftDomain` structure: a coset FFT domain whose coset generator is `1`. We provide
its `FunLike` instance and the `CosetFftDomainClass` instance, plus the `FftDomainClass` typeclass
abstracting FFT domains and its canonical instance on `FftDomain`.

Evaluation bridges (`eval_fft_domain_eq_eval_domain`,
`eval_fft_domain_eq_eval_coset_fft_domain`) and injectivity lemmas (`injective`, `injOn`) round
out the file.
-/

/-! The canonical module supplies the concrete coercion and both domain class instances.
The former copies imposed additional finite-domain assumptions and introduced no extra API. -/
