/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.REnergyGeneralCharPLowerBound

/-!
# The diagonal (antipodal-pairing) FLOOR on `negSymCount` and `rEnergy` (#444)

`Frontier/REnergyGeneralCharPLowerBound.lean` (this campaign) landed the char-free general-`r`
energy LOWER bound `negSymCount G (2r) ≤ rEnergy G r` — but only **relatively** (the relation energy
is at least the count-balanced census). It supplies the sign `0 ≤ W_r`, NOT a *quantitative* value.
This file lands the missing **absolute** floor on the census itself, and hence on the energy:

> **`|G|^r ≤ negSymCount G (2r)`**  for any negation-closed `G` (`0 ∉ G`, char `≠ 2`), char-free.

and, chaining with the landed relative bound,

> **`|G|^r ≤ rEnergy G r`**  (the diagonal/DC main-term floor on the depth-`r` relation energy).

## Why this is a real brick (frontier-movement, NON-moment, extend-proven)

The dossier (#444 §6.0/§6.1) repeatedly flags as *mildly favourable to the prize floor being TRUE*
that the char-0 energy ratio `E_r/Wick → 1` **from below** (gap `Θ(1/n)`), with `n^r` the diagonal
main term. The char-0 cushion bracket landed the UPPER edge (`E_r ≤ Wick`). The matching **LOWER
edge** `n^r ≤ E_r`, the diagonal main term as a *proven* floor, was absent in any characteristic.
This is it: a single char-free theorem, uniform in `r`, holding in **every** field (no char-0, no
Lam–Leung needed). It is **NON-MOMENT** (a perfect-matching tuple injection, not a moment
cancellation), **EXTEND-proven** (it composes the landed `negSymCount_le_rEnergy`), and makes **no
capacity / beyond-Johnson / cliff-at-`n/2`** claim (rule 4/6 + asymptotic guard): a clean lower
bound that RAISES the floor, untouched is the open `b ≠ 0` √-cancellation ceiling.

## The mechanism (char-free involution)

For `z : Fin r → F`, `padDiag z : Fin (2r) → F` places `z i` in even slot `2i` and `−z i` in odd
slot `2i+1`. Count-balance of `padDiag z` (for every `v`, the `v`- and `(−v)`-fibers have equal
card) is witnessed by the parity-toggle involution `toggle : Fin (2r) → Fin (2r)` (`2i ↔ 2i+1`),
which flips the contributed sign, hence swaps the `v`- and `(−v)`-fibers. The map `z ↦ padDiag z` is
injective and lands in `G^{2r}` when `z ∈ G^r` and `G` is negation-closed, giving
`|G|^r = |G^r| ≤ negSymCount G (2r)`.

Probe (`scripts/probes/probe_negsym_floor_sweep.py`, 24/24): PROPER thin `μ_n = 2^a` (`a=2,3`),
primes `p ∈ {17,41,97,113}`, `p ≡ 1 mod n`, NEVER `n = q-1`, `r=1,2,3`; `|G|^r ≤ negSymCount(G,2r)`
in every case (p-independent, as a char-0 census).

Issue #444. Axiom target `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.Frontier.E3StrataCount (negSymCount)
open ArkLib.ProximityGap.Frontier.REnergyGeneralCharPLowerBound (negSymCount_le_rEnergy)

namespace ArkLib.ProximityGap.Frontier.NegSymCountDiagonalFloor

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- The half-index `⟨k/2, _⟩ : Fin r` of a `2r`-slot. -/
def half {r : ℕ} (k : Fin (2 * r)) : Fin r := ⟨k.val / 2, by omega⟩

/-- The canonical antipodal padding: even slot `2i ↦ z i`, odd slot `2i+1 ↦ −z i`. -/
def padDiag {r : ℕ} (z : Fin r → F) : Fin (2 * r) → F :=
  fun k => if k.val % 2 = 0 then z (half k) else - z (half k)

/-- The parity-toggle involution `2i ↔ 2i+1` on `Fin (2r)`. -/
def toggle {r : ℕ} (k : Fin (2 * r)) : Fin (2 * r) :=
  if h : k.val % 2 = 0 then ⟨k.val + 1, by have := k.isLt; omega⟩
  else ⟨k.val - 1, by have := k.isLt; omega⟩

/-- The underlying value of `toggle k`. -/
theorem toggle_val {r : ℕ} (k : Fin (2 * r)) :
    (toggle k).val = if k.val % 2 = 0 then k.val + 1 else k.val - 1 := by
  unfold toggle
  by_cases h : k.val % 2 = 0
  · rw [dif_pos h, if_pos h]
  · rw [dif_neg h, if_neg h]

theorem toggle_toggle {r : ℕ} (k : Fin (2 * r)) : toggle (toggle k) = k := by
  apply Fin.ext
  rw [toggle_val, toggle_val]
  by_cases h : k.val % 2 = 0
  · have h1 : (k.val + 1) % 2 ≠ 0 := by omega
    rw [if_pos h, if_neg h1]; omega
  · have h1 : (k.val - 1) % 2 = 0 := by omega
    rw [if_neg h, if_pos h1]; omega

theorem toggle_injective {r : ℕ} : Function.Injective (toggle (r := r)) :=
  Function.LeftInverse.injective toggle_toggle

theorem half_val {r : ℕ} (k : Fin (2 * r)) : (half k).val = k.val / 2 := rfl

theorem half_toggle {r : ℕ} (k : Fin (2 * r)) : half (toggle k) = half k := by
  apply Fin.ext
  rw [half_val, half_val, toggle_val]
  by_cases h : k.val % 2 = 0
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

theorem padDiag_toggle {r : ℕ} (z : Fin r → F) (k : Fin (2 * r)) :
    padDiag z (toggle k) = - padDiag z k := by
  unfold padDiag
  rw [half_toggle]
  by_cases h : k.val % 2 = 0
  · have h1 : (toggle k).val % 2 ≠ 0 := by rw [toggle_val, if_pos h]; omega
    rw [if_pos h, if_neg h1]
  · have h1 : (toggle k).val % 2 = 0 := by rw [toggle_val, if_neg h]; omega
    rw [if_neg h, if_pos h1, neg_neg]

private theorem padDiag_apply {r : ℕ} (z : Fin r → F) (k : Fin (2 * r)) :
    padDiag z k = if k.val % 2 = 0 then z (half k) else - z (half k) := rfl

/-- `padDiag z` lands in `G` slot-wise when `z` does and `G` is negation-closed. -/
theorem padDiag_mem_piFinset {r : ℕ} {G : Finset F} (hneg : ∀ x ∈ G, -x ∈ G)
    {z : Fin r → F} (hz : z ∈ Fintype.piFinset (fun _ : Fin r => G)) :
    padDiag z ∈ Fintype.piFinset (fun _ : Fin (2 * r) => G) := by
  rw [Fintype.mem_piFinset] at hz ⊢
  intro k
  rw [padDiag_apply]
  split
  · exact hz (half k)
  · exact hneg _ (hz (half k))

/-- **Count-balance of `padDiag z`.** For every value `v`, the `v`-fiber and the `−v`-fiber of
`padDiag z` have equal cardinality. Witnessed by the sign-flipping involution `toggle`. -/
theorem padDiag_balanced {r : ℕ} (z : Fin r → F) (v : F) :
    (Finset.univ.filter (fun k => padDiag z k = v)).card
      = (Finset.univ.filter (fun k => padDiag z k = -v)).card := by
  refine Finset.card_bij (fun k _ => toggle k) ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [padDiag_toggle, hk.2]
  · intro a _ b _ hab
    exact toggle_injective hab
  · intro k hk
    rw [Finset.mem_filter] at hk
    refine ⟨toggle k, ?_, toggle_toggle k⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [padDiag_toggle, hk.2, neg_neg]

/-- `padDiag` is injective: `z i` is read back from the even slot `2i`. -/
theorem padDiag_injective {r : ℕ} : Function.Injective (padDiag (F := F) (r := r)) := by
  intro a b hab
  funext i
  have hi : (2 * i.val) % 2 = 0 := by omega
  have key : padDiag a ⟨2 * i.val, by have := i.isLt; omega⟩
           = padDiag b ⟨2 * i.val, by have := i.isLt; omega⟩ := by rw [hab]
  rw [padDiag_apply, padDiag_apply] at key
  simp only [hi, if_true] at key
  have hhalf : half (⟨2 * i.val, by have := i.isLt; omega⟩ : Fin (2 * r)) = i := by
    apply Fin.ext
    show (2 * i.val) / 2 = i.val
    omega
  rw [hhalf] at key
  exact key

/-- **The diagonal floor on the count-balanced census (char-free, all characteristics).**
For any negation-closed `G` (`0 ∉ G` not even needed here; `char ≠ 2` not needed) in a finite field,
`|G|^r ≤ negSymCount G (2r)`. The diagonal `2r`-tuples `padDiag z` (`z ∈ G^r`) are `|G|^r` distinct
count-balanced tuples. -/
theorem pow_card_le_negSymCount {r : ℕ} (G : Finset F) (hneg : ∀ x ∈ G, -x ∈ G) :
    G.card ^ r ≤ negSymCount G (2 * r) := by
  classical
  -- |G^r| = |G|^r, and z ↦ padDiag z injects G^r into the count-balanced filter set.
  have hcard : (Fintype.piFinset (fun _ : Fin r => G)).card = G.card ^ r := by
    simp [Fintype.card_piFinset]
  have hinj : (Fintype.piFinset (fun _ : Fin r => G)).card ≤ negSymCount G (2 * r) := by
    unfold negSymCount
    apply Finset.card_le_card_of_injOn padDiag
    · intro z hz
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨padDiag_mem_piFinset hneg hz, ?_⟩
      intro v
      exact padDiag_balanced z v
    · intro a _ b _ hab
      exact padDiag_injective hab
  rw [hcard] at hinj
  exact hinj

/-- **The diagonal main-term FLOOR on the depth-`r` relation energy (char-free, all char).**
`|G|^r ≤ rEnergy G r` for any negation-closed `G` (`0 ∉ G`, `char ≠ 2`). Chains the count floor
`|G|^r ≤ negSymCount G (2r)` with the landed relative bound `negSymCount G (2r) ≤ rEnergy G r`.
This is the matching LOWER edge of the char-0 cushion bracket, now in EVERY characteristic — the
"energy ratio → 1 from below" anchor (#444 §6.0/§6.1) as a proven floor. No capacity / cliff claim. -/
theorem pow_card_le_rEnergy {r : ℕ} (G : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ x ∈ G, -x ∈ G) :
    G.card ^ r ≤ rEnergy G r :=
  le_trans (pow_card_le_negSymCount G hneg) (negSymCount_le_rEnergy G r h2 h0 hneg)

end ArkLib.ProximityGap.Frontier.NegSymCountDiagonalFloor

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.NegSymCountDiagonalFloor.padDiag_balanced
#print axioms ArkLib.ProximityGap.Frontier.NegSymCountDiagonalFloor.pow_card_le_negSymCount
#print axioms ArkLib.ProximityGap.Frontier.NegSymCountDiagonalFloor.pow_card_le_rEnergy
