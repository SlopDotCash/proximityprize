/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.E3StrataCharZero
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._E3NegSymConverse
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import ArkLib.Data.CodingTheory.ProximityGap.SidonModNegEnergyEquality
import ArkLib.Data.CodingTheory.ProximityGap.MonomialRowFullSupport

/-!
# The char-`p` lower bound `rEnergy G 3 >= 15n^3 - 45n^2 + 40n` (#444)

`Frontier/REnergyThreeCharZero.lean` identifies `rEnergy G 3` (the depth-3 relation energy, the
`r = 2` cross-step rung input) with the antipodal count-balanced 6-tuple census of `G`, but ONLY
in characteristic 0 (its forward direction is the char-0 Lam-Leung theorem, which is `false at
depth` in char `p` -- the BGK/Burgess `sqrt`-cancellation wall). `Frontier/CrossStepRungTwoMuN.lean`
(the `census4` worktree) reduced the whole `r = 2` rung for `mu_n` to ONE open producer input: the
EXACT closed form `rEnergy (mu_n) 3 = 15n^3 - 45n^2 + 40n`, left open because the char-`p` forward
direction is the wall.

This file lands the **unconditional `>=` half** of that closed form, char-`p`-universal:

> **`rEnergy G 3 >= 15|G|^3 - 45|G|^2 + 40|G|`** for any negation-closed `G` (`0 ∉ G`, char ≠ 2)
> in ANY finite field.

The mechanism is the CHAR-FREE direction of the census identity (no Lam-Leung, no `[CharZero]`):

* every antipodally count-balanced 6-tuple over `G` IS a genuine zero-sum 6-tuple
  (`E3NegSymConverse.sum_eq_zero_of_fiber_balanced`, char-free, needs only `0 ∉ G`, `2 ≠ 0`);
* `rEnergy G 3` counts zero-sum 6-tuples (`rEnergy_three_eq_zeroSumCount`, a pure bijection, here
  reproved char-free); so the count-balanced tuples INJECT into the zero-sum tuples;
* hence `rEnergy G 3 >= negSymCount G 6`, and `negSymCount G 6 = 15|G|^3 - 45|G|^2 + 40|G|` is the
  proven char-0 strata producer (`E3StrataCharZero.negSymCount_six_closed`, char-free in `|G|`).

## Why this is a real brick (not the wall, not a re-map)

The char-0 EQUALITY `rEnergy (mu_n) 3 = 15n^3 - 45n^2 + 40n` is FALSE in char `p` when `p` is small
relative to `n` (extra low-degree collisions add zero-sum 6-tuples that are NOT count-balanced).
The probe `probe_renergy3_charp.py` (PROPER thin `mu_n = 2^a`, `p = 1 mod n`, NEVER `n = q-1`,
multi-prime incl. Fermat 17/257/65537) confirms: at `p > n^3` the equality HOLDS exactly, but at
`p = 17` (`n = 8`: `15560 ≠ 5120`) and `p = 257` (`n = 16`: `109840 ≠ 50560`) the energy is
STRICTLY GREATER -- the extra-collision surplus. In EVERY case the energy is `>= 15n^3-45n^2+40n`
(the count-balanced tuples are always present), so the `>=` direction is UNCONDITIONAL. This brick
proves exactly that unconditional half: it DISCHARGES the lower-bound side of the `census4` open
input, leaving the open part as precisely the extra-collision exclusion `p > n^3` (= the wall).
NON-MOMENT (a tuple-count injection, not an additive-moment cancellation bound). EXTEND-proven on
the landed char-0 strata producer + the char-free converse. NOT a CORE closure: the worst-case sup
`M(mu_n) <= C sqrt(n log(p/n))` stays OPEN.

Issue #444. Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.Frontier.E3StrataCount (negSymCount)
open ArkLib.ProximityGap.Frontier.E3NegSymConverse (sum_eq_zero_of_fiber_balanced)

namespace ArkLib.ProximityGap.Frontier.REnergyThreeCharPLowerBound

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- The `Fin 6 -> F` glue of two `Fin 3 -> F` tuples (tail negated). Identical to the
`_REnergyThreeScratch` glue, reproduced here so the zero-sum bijection is available char-free
(the scratch version carries an unused `[CharZero L]` section variable). -/
private def glue (v w : Fin 3 → F) : Fin 6 → F :=
  ![v 0, v 1, v 2, -(w 0), -(w 1), -(w 2)]

private theorem glue_sum (v w : Fin 3 → F) : ∑ i, glue v w i = (∑ i, v i) - ∑ i, w i := by
  simp only [glue, Fin.sum_univ_six, Fin.sum_univ_three]
  simp [Matrix.cons_val]
  ring

/-- **`rEnergy G 3` counts zero-sum 6-tuples, char-free.** The relation energy
`#{(v,w) : Σv = Σw}` bijects with `#{c : Σc = 0}` via `(v,w) ↦ glue v w`. A pure combinatorial
bijection -- no characteristic hypothesis (the `_REnergyThreeScratch` analogue is gated behind an
unused `[CharZero]`; this one is usable at `F_p`). -/
theorem rEnergy_three_eq_zeroSumCount (G : Finset F) (hneg : ∀ z ∈ G, -z ∈ G) :
    rEnergy G 3
      = ((Fintype.piFinset (fun _ : Fin 6 => G)).filter (fun c => ∑ i, c i = 0)).card := by
  classical
  have hre : rEnergy G 3
      = (((Fintype.piFinset (fun _ : Fin 3 => G)) ×ˢ (Fintype.piFinset (fun _ : Fin 3 => G))).filter
          (fun p => ∑ i, p.1 i = ∑ i, p.2 i)).card := by
    rw [rEnergy, ← Finset.sum_product', ← Finset.card_filter]
  rw [hre]
  refine Finset.card_nbij'
    (fun p => glue p.1 p.2)
    (fun c => (![c 0, c 1, c 2], ![-(c 3), -(c 4), -(c 5)]))
    ?_ ?_ ?_ ?_
  · rintro ⟨v, w⟩ hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset] at hp
    obtain ⟨⟨hv, hw⟩, hsum⟩ := hp
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp only [glue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val] <;>
        first
          | exact hv _
          | exact hneg _ (hw _)
    · rw [glue_sum, hsum]; ring
  · intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hc
    obtain ⟨hcG, hcsum⟩ := hc
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset]
    refine ⟨⟨fun i => ?_, fun j => ?_⟩, ?_⟩
    · fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val] <;> exact hcG _
    · fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val] <;> exact hneg _ (hcG _)
    · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val]
      have h6 : ∑ i, c i = c 0 + c 1 + c 2 + c 3 + c 4 + c 5 := Fin.sum_univ_six c
      rw [h6] at hcsum; linear_combination hcsum
  · rintro ⟨v, w⟩ _
    ext i
    · fin_cases i <;> simp [glue]
    · fin_cases i <;> simp [glue]
  · intro c _
    funext i
    fin_cases i <;> simp [glue]

/-- **Count-balanced 6-tuples inject into zero-sum 6-tuples (char-free).** The
`negSymCount`-filter (fiber-balanced) is a SUBSET of the zero-sum filter, because every
count-balanced tuple of nonzero values is a genuine zero-sum tuple
(`sum_eq_zero_of_fiber_balanced`, char-free). Hence `negSymCount G 6 <= rEnergy G 3`. -/
theorem negSymCount_le_rEnergy_three (G : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ z ∈ G, -z ∈ G) :
    negSymCount G 6 ≤ rEnergy G 3 := by
  classical
  rw [rEnergy_three_eq_zeroSumCount G hneg]
  unfold negSymCount
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter, Fintype.mem_piFinset] at hc ⊢
  obtain ⟨hcG, hbal⟩ := hc
  refine ⟨hcG, ?_⟩
  -- fiber-balanced + nonzero values ⟹ zero-sum (char-free converse)
  exact sum_eq_zero_of_fiber_balanced h2 c (fun i => fun h => h0 (h ▸ hcG i)) hbal

/-- **The char-`p` lower bound (HEADLINE).** For any negation-closed `G` (`0 ∉ G`, char ≠ 2) in a
finite field, the depth-3 relation energy is at least the char-0 closed form:
`rEnergy G 3 >= 15|G|^3 - 45|G|^2 + 40|G|` (over `ℤ`). UNCONDITIONAL in the characteristic: the
extra char-`p` collisions only ADD zero-sum 6-tuples, never remove the count-balanced ones. With
`G = mu_n` (`n = 2^a`, always negation-closed, `0 ∉ mu_n`, char `p` odd) this is the `>=` half of
the `census4` open input `rEnergy (mu_n) 3 = 15n^3 - 45n^2 + 40n`. -/
theorem rEnergy_three_ge_closed (G : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ z ∈ G, -z ∈ G) :
    15 * (G.card : ℤ) ^ 3 - 45 * (G.card : ℤ) ^ 2 + 40 * (G.card : ℤ) ≤ (rEnergy G 3 : ℤ) := by
  have hcount : (negSymCount G 6 : ℤ)
      = 15 * (G.card : ℤ) ^ 3 - 45 * (G.card : ℤ) ^ 2 + 40 * (G.card : ℤ) :=
    E3StrataCharZero.negSymCount_six_closed G h2 h0 hneg
  have hle : (negSymCount G 6 : ℤ) ≤ (rEnergy G 3 : ℤ) := by
    exact_mod_cast negSymCount_le_rEnergy_three G h2 h0 hneg
  rw [hcount] at hle
  exact hle

/-! ### The `mu_n` specialization (hypotheses discharged for the actual prize object) -/

open ArkLib.ProximityGap.EnergyEqualitySidonModNeg (muN mem_muN mu_n_card_eq)
open ArkLib.ProximityGap.WF5SidonFullSupport (zero_notMem_muN)

/-- **The `mu_n` lower bound (prize object, hypotheses discharged).** For `n = 2^m` (`m >= 1`) and
a primitive `n`-th root `omega in ZMod p` (`p` an odd prime, so char != 2), the depth-3 relation
energy of the thin subgroup `mu_n = {z : z^n = 1}` is at least the char-0 closed form:
`rEnergy (mu_n) 3 >= 15n^3 - 45n^2 + 40n`. This is `rEnergy_three_ge_closed` with `G = muN p n`,
discharging negation-closure (`-1 in mu_n` since `n` even), `0 not in mu_n`, `2 != 0` (`p` odd), and
`|mu_n| = n`. The directly-consumable `>=` half of the `census4` open r=2-rung input. -/
theorem muN_rEnergy_three_ge_closed {p : ℕ} [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) {n m : ℕ}
    (hn2 : n = 2 ^ m) (hm : 1 ≤ m) {ω : ZMod p} (hω : IsPrimitiveRoot ω n) :
    15 * (n : ℤ) ^ 3 - 45 * (n : ℤ) ^ 2 + 40 * (n : ℤ) ≤ (rEnergy (muN p n) 3 : ℤ) := by
  have hnpos : 0 < n := by rw [hn2]; positivity
  have hmem : ∀ z : ZMod p, z ∈ muN p n ↔ z ^ n = 1 := fun z => mem_muN hnpos z
  have hneg : ∀ z ∈ muN p n, -z ∈ muN p n := by
    intro z hz
    rw [hmem] at hz ⊢
    have he : Even n := by rw [hn2]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
    rw [neg_pow, he.neg_one_pow, one_mul]; exact hz
  have h0 : (0 : ZMod p) ∉ muN p n := zero_notMem_muN hnpos
  have hcard : (muN p n).card = n := mu_n_card_eq hω
  have hge := rEnergy_three_ge_closed (muN p n) hp2 h0 hneg
  rw [hcard] at hge
  exact hge

end ArkLib.ProximityGap.Frontier.REnergyThreeCharPLowerBound

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.REnergyThreeCharPLowerBound.rEnergy_three_eq_zeroSumCount
#print axioms ArkLib.ProximityGap.Frontier.REnergyThreeCharPLowerBound.negSymCount_le_rEnergy_three
#print axioms ArkLib.ProximityGap.Frontier.REnergyThreeCharPLowerBound.rEnergy_three_ge_closed
#print axioms ArkLib.ProximityGap.Frontier.REnergyThreeCharPLowerBound.muN_rEnergy_three_ge_closed
