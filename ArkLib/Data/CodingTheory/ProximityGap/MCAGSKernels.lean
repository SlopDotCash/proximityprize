/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.MCAGSWitness
import ArkLib.Data.CodingTheory.GuruswamiSudan.ListSizeBound

/-!
# Grand Challenge 1 prize kernels: MCA error bounded by the *proven* GS list size (Issue #141)

This file proves the genuine research kernel for the Grand Challenge 1 prize that is reachable
with the in-tree machinery: in the Guruswami–Sudan / Johnson window the MCA error is bounded by
a `poly/q` quantity in which the list-size factor is **discharged by the proven GS list-size
theorem** (`GSListSizeBound.gs_list_size_window_div`) rather than assumed.

The full prize (the `epsMCAgs`/`ε_mca` bound *up to capacity* `1 - ρ - η`) needs a list-size
bound *beyond* the Johnson radius `1 - √ρ`; that beyond-Johnson list-size estimate is the
irreducible open core (no in-tree or mathlib proof exists — see the #141 disposition note). What
is genuinely provable, and proved here sorry-free and axiom-clean, is the **Johnson-window**
kernel:

* `gsWindow_msg_card_le` — a thin codeword-facing re-export of the proved GS output-list bound:
  the number of degree-`<k` candidate messages agreeing to order `m` on agreement sets of size
  `≥ a` is `≤ (m·a-1)/(k-1)` (q-independent — the prize's `poly` numerator, *proved*).

* `epsMCAgs_le_gsWindow_div` — composing that proved list size with the proved pivot-covering
  bound `epsMCAgs ≤ ℓ/q` (`MCAGSWitness.epsMCAgs_le_listSize_div_of_pivotCovering`), the GS-exposed
  MCA error satisfies `epsMCAgs ≤ ((m·a-1)/(k-1)) / q` — the `poly/q` prize shape with the hard
  list-size factor proved, not assumed.


Nothing here proves the open prize (the *uniform* beyond-Johnson bound). It pushes the frontier
to exactly the boundary of what Guruswami–Sudan supplies, with the list-size kernel proved.

## References

- [ABF26] §1 Grand MCA Challenge; §4.3. Guruswami–Sudan list decoding (in-tree
  `GSListSizeBound.gs_list_size_window_div`). Tracking: Issue #141.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code Polynomial
open scoped ProbabilityTheory BigOperators

namespace MCAGS

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Per-stack message-list bound (proved GS window list size).** A thin codeword-facing
re-export of `GSListSizeBound.gs_list_size_window_div`: given a nonzero `(1,k-1)`-weighted-degree
`≤ m·a-1` interpolant `Qu` and degree-`<k` candidate messages `Pu` each agreeing to order `m` on
an agreement set of size `≥ a`, the candidate count is `≤ (m·a-1)/(k-1)` — q-independent.

Keeping the (elaboration-heavy) GS application behind this named lemma is what makes the MCA
composition below cheap to elaborate. Tracking: Issue #141. -/
theorem gsWindow_msg_card_le
    {k m a : ℕ} (hm : 0 < m) (ha : 0 < a) (hk : 0 < k - 1)
    (xs : ι → F) (Qu : (F[X])[X]) (Pu : Finset F[X]) (S : F[X] → Finset ι)
    (hQu : Qu ≠ 0)
    (hwdu : Polynomial.Bivariate.natWeightedDegree Qu 1 (k - 1) ≤ m * a - 1)
    (hpdegu : ∀ p ∈ Pu, p.natDegree ≤ k - 1)
    (hvanu : ∀ p ∈ Pu, ∀ i ∈ S p, ArkLib.GS.vanishesToOrder m Qu (xs i) (p.eval (xs i)))
    (hxinju : ∀ p ∈ Pu, ∀ i ∈ S p, ∀ j ∈ S p, xs i = xs j → i = j)
    (hcardu : ∀ p ∈ Pu, a ≤ (S p).card) :
    Pu.card ≤ (m * a - 1) / (k - 1) :=
  GSListSizeBound.gs_list_size_window_div (k := k) (m := m) (a := a)
    Qu hQu hm ha xs Pu S hk hwdu hpdegu hvanu hxinju hcardu

set_option maxHeartbeats 400000 in
/-- **Grand Challenge 1 Johnson-window kernel.** With per-stack Guruswami–Sudan interpolation
data and pivot covering, the GS-exposed MCA error is bounded by the **proved** GS output-list
size over `q`:
`epsMCAgs C δ L ≤ ((m·a-1)/(k-1)) / q`.

The numerator is `gsWindow_msg_card_le` (proved, axiom-clean), q-independent — the `poly/q` prize
shape with the list-size factor proved, not assumed. The remaining open inputs (the GS data per
stack, the codeword↔message bridge `hbridge`, pivot covering, and the in-window radius) are
explicit hypotheses. Tracking: Issue #141. -/
theorem epsMCAgs_le_gsWindow_div
    (C : Set (ι → F)) (δ : ℝ≥0)
    (L : WordStack F (Fin 2) ι → Finset (ι → F))
    {k m a : ℕ} (hm : 0 < m) (ha : 0 < a) (hk : 0 < k - 1)
    (xs : ι → F)
    (Q : WordStack F (Fin 2) ι → (F[X])[X])
    (P : WordStack F (Fin 2) ι → Finset F[X])
    (S : F[X] → Finset ι)
    (hQ : ∀ u, Q u ≠ 0)
    (hwd : ∀ u, Polynomial.Bivariate.natWeightedDegree (Q u) 1 (k - 1) ≤ m * a - 1)
    (hpdeg : ∀ u, ∀ p ∈ P u, p.natDegree ≤ k - 1)
    (hvan : ∀ u, ∀ p ∈ P u, ∀ i ∈ S p,
      ArkLib.GS.vanishesToOrder m (Q u) (xs i) (p.eval (xs i)))
    (hxinj : ∀ u, ∀ p ∈ P u, ∀ i ∈ S p, ∀ j ∈ S p, xs i = xs j → i = j)
    (hcard : ∀ u, ∀ p ∈ P u, a ≤ (S p).card)
    (hbridge : ∀ u, (L u).card ≤ (P u).card)
    (hcov : ∀ u, PivotCovering (F := F) C δ L u) :
    epsMCAgs (F := F) C δ L
      ≤ (((m * a - 1) / (k - 1) : ℕ) : ENNReal) / (Fintype.card F : ENNReal) :=
  epsMCAgs_le_listSize_div_of_pivotCovering (F := F) C δ L ((m * a - 1) / (k - 1)) hcov
    (fun u => le_trans (hbridge u)
      (gsWindow_msg_card_le hm ha hk xs (Q u) (P u) S (hQ u) (hwd u) (hpdeg u)
        (hvan u) (hxinj u) (hcard u)))

/-! ## Source audit -/

#print axioms gsWindow_msg_card_le
#print axioms epsMCAgs_le_gsWindow_div

end MCAGS

end ProximityGap
