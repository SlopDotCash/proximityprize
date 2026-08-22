/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.UncertaintyTwoPowerBounds
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZModDonohoStark

/-!
# Discharging the `DonohoStarkHolds` hypothesis from the proven `donoho_stark` (#407, #444)

`UncertaintyTwoPowerBounds.lean` derives the near-capacity `s*` ceiling
`sStar_le_of_donohoStark : n ≤ (k+2)·(n − s*)` from a NAMED HYPOTHESIS
`DonohoStarkHolds d : n ≤ d.minSupport · d.T.card`, recorded there as a `Prop` "since its Lean proof
is not the point of that angle".  But that hypothesis IS a fully-proven, axiom-clean theorem in
`_ZModDonohoStark.lean`:

> `donoho_stark : Φ ≠ 0  ⟹  (N:ℝ) ≤ |supp Φ| · |supp 𝓕Φ|`.

This file BRIDGES the two: it builds the abstract `SparseZeroData` from a *real* nonzero function
`Φ : ZMod n → ℂ` (`minSupport := |supp Φ|`, `T := supp 𝓕Φ`) and **discharges `DonohoStarkHolds`
unconditionally** via `donoho_stark`, turning the conditional ceiling into an *unconditional*
theorem about real DFT-sparse functions:

> for any nonzero `Φ` with `|supp 𝓕Φ| ≤ k+2`,  `n ≤ (k+2)·(n − sStar (ofFun Φ))`,
> i.e. its zero count on `Z_n` is `≤ n·(k+1)/(k+2)` (near capacity, the honest DFT-uncertainty
> ceiling, far above Johnson `√(kn)`; the gap below is the prize).

**Frontier-movement, NON-MOMENT, EXTEND-proven.**  This is pure DFT-support algebra (no
additive-energy / moment route).  It consumes the proven `donoho_stark` + `farSupport_card_le`; it
proves NO new analytic content and makes NO capacity/beyond-Johnson/cliff-at-n/2 claim. It
UNCONDITIONALIZES the existing near-capacity ceiling and re-confirms (rule 4) that DFT-uncertainty
alone yields nothing below Johnson for the `2`-power group.  The bridge cast is ℝ→ℕ on the card
product (`donoho_stark` is stated over ℝ; the supports are finite so the bound transfers to ℕ).
Axiom-clean.  Issues #407, #444.
-/

set_option autoImplicit false

open Finset ZMod
open scoped ZMod
open ProximityGap.UncertaintyTwoPower
open ProximityGap.Frontier.ZModDonohoStark

namespace ProximityGap.UncertaintyTwoPower.DonohoStarkBridge

variable {n : ℕ} [NeZero n]

/-- **The bridge constructor.**  Package a function `Φ : ZMod n → ℂ` as the abstract
`SparseZeroData`: the Fourier support `T := supp 𝓕Φ`, the physical support
`minSupport := |supp Φ|` (`≤ n` since `supp Φ ⊆ univ`). -/
noncomputable def ofFun (Φ : ZMod n → ℂ) : SparseZeroData n where
  T := supp ((𝓕) Φ)
  minSupport := (supp Φ).card
  minSupport_le := by
    have : supp Φ ⊆ (univ : Finset (ZMod n)) := Finset.subset_univ _
    simpa using (Finset.card_le_card this).trans_eq (by simp [ZMod.card])

@[simp] theorem ofFun_T (Φ : ZMod n → ℂ) : (ofFun Φ).T = supp ((𝓕) Φ) := rfl

@[simp] theorem ofFun_minSupport (Φ : ZMod n → ℂ) :
    (ofFun Φ).minSupport = (supp Φ).card := rfl

/-- **Discharge of `DonohoStarkHolds` (the headline).**  For any nonzero `Φ`, the abstract named
hypothesis `DonohoStarkHolds (ofFun Φ)` is a THEOREM. It is exactly the proven `donoho_stark`,
cast from ℝ to ℕ on the (finite) support-card product. -/
theorem donohoStarkHolds_ofFun (Φ : ZMod n → ℂ) (hΦ : Φ ≠ 0) :
    DonohoStarkHolds (ofFun Φ) := by
  unfold DonohoStarkHolds
  simp only [ofFun_T, ofFun_minSupport]
  -- `donoho_stark` over ℝ: `(n:ℝ) ≤ |supp Φ| · |supp 𝓕Φ|`.
  have hR : (n : ℝ) ≤ ((supp Φ).card : ℝ) * ((supp ((𝓕) Φ)).card : ℝ) := donoho_stark Φ hΦ
  have hcast : (n : ℝ) ≤ (((supp Φ).card * (supp ((𝓕) Φ)).card : ℕ) : ℝ) := by
    rw [Nat.cast_mul]; exact hR
  exact_mod_cast hcast

/-- **The UNCONDITIONAL near-capacity ceiling on real DFT-sparse functions.**  Combining the
discharge with the proven `sStar_le_of_donohoStark`: for any nonzero `Φ` whose Fourier support has
`≤ k+2` frequencies, `n ≤ (k+2)·(n − sStar (ofFun Φ))`.  Equivalently the zero count on `Z_n`
satisfies `sStar (ofFun Φ) ≤ n·(k+1)/(k+2)`, the honest DFT-uncertainty ceiling, with NO named
hypothesis remaining. -/
theorem sStar_ofFun_le (Φ : ZMod n → ℂ) (hΦ : Φ ≠ 0) (k : ℕ)
    (hT : (supp ((𝓕) Φ)).card ≤ k + 2) :
    n ≤ (k + 2) * (n - sStar (ofFun Φ)) := by
  refine sStar_le_of_donohoStark (ofFun Φ) k ?_ (donohoStarkHolds_ofFun Φ hΦ)
  simpa using hT

/-- **Specialization to the far-line support (the real prize object).**  If `Φ`'s Fourier support
is the structured far support `farSupport n k a b = {0,…,k-1} ∪ {a,b}`, then `|T| ≤ k+2` is
automatic (`farSupport_card_le`), so the unconditional ceiling holds with no support hypothesis at
all. -/
theorem sStar_ofFun_le_of_farSupport (Φ : ZMod n → ℂ) (hΦ : Φ ≠ 0)
    (k : ℕ) (a b : ZMod n) (hsupp : supp ((𝓕) Φ) = farSupport n k a b) :
    n ≤ (k + 2) * (n - sStar (ofFun Φ)) :=
  sStar_ofFun_le Φ hΦ k (by rw [hsupp]; exact farSupport_card_le n k a b)

/-- **Rule-4 cartography (re-confirmation, NOT a closure).**  The unconditional ceiling is
near-CAPACITY: it does NOT (and cannot) reach the Johnson floor `s* ≤ √(kn)`.  Concretely, the
ceiling only forces `sStar (ofFun Φ) ≤ n`, i.e. `n - sStar ≥ ⌈n/(k+2)⌉ ≥ 1`, which is the trivial
physical-support lower bound `|supp Φ| ≥ 1` sharpened to `≥ n/(k+2)`.  The `√(kn)` gap below is the
`μ_n`-specific character-sum content (the prize), untouched by DFT-uncertainty. -/
theorem ofFun_minSupport_ge_one (Φ : ZMod n → ℂ) (hΦ : Φ ≠ 0) :
    1 ≤ (ofFun Φ).minSupport := by
  simp only [ofFun_minSupport]
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
  intro hempty
  apply hΦ
  funext j
  by_contra hj
  have hmem : j ∈ supp Φ := by
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hj
  rw [hempty] at hmem
  simp at hmem

end ProximityGap.UncertaintyTwoPower.DonohoStarkBridge

/-! ## Axiom audit (expected: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`). -/
#print axioms ProximityGap.UncertaintyTwoPower.DonohoStarkBridge.donohoStarkHolds_ofFun
#print axioms ProximityGap.UncertaintyTwoPower.DonohoStarkBridge.sStar_ofFun_le
#print axioms ProximityGap.UncertaintyTwoPower.DonohoStarkBridge.sStar_ofFun_le_of_farSupport
#print axioms ProximityGap.UncertaintyTwoPower.DonohoStarkBridge.ofFun_minSupport_ge_one
