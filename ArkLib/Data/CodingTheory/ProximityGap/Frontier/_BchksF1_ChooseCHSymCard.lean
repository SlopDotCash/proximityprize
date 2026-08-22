/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BchksF1b_ChooseCHMultisetGrounding
import Mathlib.Data.Sym.Card

/-!
# Bchks F1c — the IMAGE-CARD reduction: `#bad ≤ chooseCH s r` via a monomial-direction injection

`_BchksF1b_ChooseCHMultisetGrounding` GROUNDED the floor multiplier as the monomial count
(`chooseCH s r = Fintype.card (Sym (Fin s) r)` — there are exactly `chooseCH s r` degree-`r`
monomial multisets over an `s`-node alphabet). That grounding is a *cardinality of the index set*.
This file turns it into the floor's actual *bounding mechanism*: the `poly = 1` leading-order
ceiling `#bad ≤ chooseCH s r`, discharged by a genuine cardinality argument
(`Fintype.card_le_of_injective` / `Finset.card_image_of_injOn`) when the bad set injects into
`Sym (Fin s) r`.

## The mechanism (ABF26 §4 + SchurLagrangeBridge)

At the minimal witness `|R| = k+1`, the forced bad scalar of the far pencil `(x^a, x^b)` is
`γ = −h_{a−k}(R)/h_{b−k}(R)`, with `h_d` the degree-`d` complete-homogeneous symmetric polynomial —
i.e. a SUM over degree-`d` monomials, each indexed by an element of `Sym (Fin s) d`. If distinct bad
scalars arise from distinct monomial directions (the injection hypothesis `hφ`), the bad count is
cut by the number of directions `= chooseCH s r` (the grounded `Sym` cardinality). This is the
`poly = 1` leading order of the F1 floor with a real combinatorial witness — NOT a free `≤`.

⚠️ **The injection is exactly where `poly = 1` can FAIL.** The distinct-`h`-VALUE count over
`(k+1)`-subsets is empirically NOT bounded by `chooseCH n r` at small `r` (`poly = 1` FALSE,
`poly = n` verified — F1 `poly(n)=n` fix; constraint lemma in `DISPROOF_LOG.md` O237). So this file
supplies the leading-order mechanism (`poly = 1` GIVEN injectivity) while the empirical `poly = n`
excess lives precisely in the non-injective small-`r` value-collision region (the genuine open
core).

## Honest scope (rules 1,3,6)

This is the F1 ceiling's reduction MECHANISM, not the open core. It says only "an injection into the
`chooseCH s r` monomial directions caps the bad count" — pure char-free cardinality, NO field
arithmetic / thinness. It does NOT prove the open `CompleteHomogeneousSpectrumBound` (which needs
`poly = n`). Field-universal, so by rule 3 it CANNOT prove CORE. NO moment/census/orbit/spectrum
re-derivation; a `Fintype.card`/`Sym` object, NOT a `δ*`/incidence object — asymptotic-guard
cliff-at-`n/2` UNTOUCHED, no capacity/beyond-Johnson/growth-law claim.
CORE `M(μ_n) ≤ C√(n log(p/n))` OPEN.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.BchksF1

open Finset

/-- **The IMAGE-CARD reduction (the `poly = 1` leading-order floor, with a combinatorial witness).**
If the bad-scalar index `B` injects into the degree-`r` monomial multisets `Sym (Fin s) r` (the
ABF26 §4 worst-direction structure: each forced bad scalar `−h_{a−k}/h_{b−k}` pinned by a distinct
monomial direction), then `|B| ≤ chooseCH s r`. The `poly = 1` floor, discharged by genuine
cardinality (`Fintype.card_le_of_injective`) through the F1b grounding `chooseCH = card (Sym _)`. -/
theorem card_le_chooseCH_of_inj {B : Type*} [Fintype B] (s r : ℕ)
    (φ : B → Sym (Fin s) r) (hφ : Function.Injective φ) :
    Fintype.card B ≤ chooseCH s r := by
  rw [chooseCH_eq_card_sym]
  exact Fintype.card_le_of_injective φ hφ

/-- **Finset form of the image-card reduction.** A bad-scalar `Finset B` with an injection (on `B`)
into the monomial directions `Sym (Fin s) r` has `B.card ≤ chooseCH s r`. -/
theorem finset_card_le_chooseCH_of_injOn {β : Type*} (B : Finset β) (s r : ℕ)
    (φ : β → Sym (Fin s) r) (hφ : Set.InjOn φ B) :
    B.card ≤ chooseCH s r := by
  rw [chooseCH_eq_card_sym]
  calc B.card = (B.image φ).card := (Finset.card_image_of_injOn hφ).symm
    _ ≤ Fintype.card (Sym (Fin s) r) := by simpa using Finset.card_le_univ (B.image φ)

/-- **The reduction composed with the bad ≤ spectrum step.** If `bad ≤ |B|` and `B` injects into the
monomial directions `Sym (Fin s) r`, then `bad ≤ chooseCH s r` — the full `poly = 1` floor chain
(`bad ≤ #directions = chooseCH`), GIVEN the (small-`r`-failing) injection. -/
theorem bad_le_chooseCH_of_inj {B : Type*} [Fintype B] (bad s r : ℕ)
    (hbad : bad ≤ Fintype.card B)
    (φ : B → Sym (Fin s) r) (hφ : Function.Injective φ) :
    bad ≤ chooseCH s r :=
  le_trans hbad (card_le_chooseCH_of_inj s r φ hφ)

/-- **Sanity (the reduction lands the F1b grounded count).** Any `B` injecting into `Sym (Fin 8) 3`
has `|B| ≤ chooseCH 8 3 = 120` — the 120 degree-`3` monomial directions over 8 nodes cap the bad
count, matching the F1/F1b machine-checked number. -/
theorem card_le_chooseCH_concrete {B : Type*} [Fintype B]
    (φ : B → Sym (Fin 8) 3) (hφ : Function.Injective φ) :
    Fintype.card B ≤ 120 := by
  have h := card_le_chooseCH_of_inj 8 3 φ hφ
  rwa [show chooseCH 8 3 = 120 from by decide] at h

end ArkLib.ProximityGap.BchksF1

/-! ## Axiom audit (expected: ⊆ `{propext, Classical.choice, Quot.sound}`) -/
#print axioms ArkLib.ProximityGap.BchksF1.card_le_chooseCH_of_inj
#print axioms ArkLib.ProximityGap.BchksF1.finset_card_le_chooseCH_of_injOn
#print axioms ArkLib.ProximityGap.BchksF1.bad_le_chooseCH_of_inj
#print axioms ArkLib.ProximityGap.BchksF1.card_le_chooseCH_concrete
