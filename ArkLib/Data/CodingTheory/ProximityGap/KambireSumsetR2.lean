/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg
import Mathlib.Tactic

/-!
# The distinct 2-subset-sum count of a Sidon-mod-negation set — the Kambiré bad-count `|H^{(+2)}|` (#407)

A **W4-free, q-independent, cyclotomic** exact count on the prize's lower-bracket optimality (piece 4 —
the Kambiré sumset-max). For the dyadic domain `μ_{2^μ}`, the bad-scalar count at the deep-band edge is
`|H^{(+r)}| = #{distinct r-subset-sums}`; this file pins the `r=2` base case in closed form.

> `two_mul_card_offDiag_sum_image` :  for a negation-closed, no-self-antipodal, Sidon-mod-negation set
> `G` (the in-tree `sidonModNeg_rootsOfUnity` gives `SidonModNeg(μ_n)` for even `n`, large prime),
> `2·#{a+b : a,b∈G, a≠b} = |G|² − 2|G| + 2`,  i.e.  `|H^{(+2)}| = (|G|²−2|G|+2)/2`.

The mechanism is purely combinatorial (no character sums, q-independent): under `SidonModNeg` every
**non-antipodal** 2-subset has a unique sum (`filter_eq_pair`), while all `|G|/2` **antipodal** pairs
`{ζ,−ζ}` collapse to the single value `0` (`fiber_zero_eq`). Numerically confirmed: `μ_8 → 25`,
`μ_16 → 113`, `μ_32 → 481` `= (s²−2s+2)/2`. This is the energy/AVERAGE-side, deep-band-edge base case;
the prize window needs the extremal `r ≈ |G|/2`, where `|H^{(+r)}|` has no closed form (open core).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/
set_option linter.style.longLine false
open Finset
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

namespace ArkLib.ProximityGap.AdditiveEnergySidonModNeg
variable {F : Type*} [Field F] [DecidableEq F]

private theorem fiber_zero_eq {G : Finset F} (hneg : ∀ x ∈ G, -x ∈ G) (hself : ∀ x ∈ G, x ≠ -x) :
    G.offDiag.filter (fun p => p.1 + p.2 = 0) = G.image (fun a => (a, -a)) := by
  ext ⟨c, e⟩
  simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hc, _he, _hce⟩, hsum⟩
    exact ⟨c, hc, rfl, by linear_combination -hsum⟩
  · rintro ⟨a, ha, rfl, rfl⟩
    exact ⟨⟨ha, hneg a ha, hself a ha⟩, by ring⟩

private theorem fiber_zero_card {G : Finset F} (hneg : ∀ x ∈ G, -x ∈ G) (hself : ∀ x ∈ G, x ≠ -x) :
    (G.offDiag.filter (fun p => p.1 + p.2 = 0)).card = G.card := by
  rw [fiber_zero_eq hneg hself,
    Finset.card_image_of_injective G (fun a b h => (Prod.ext_iff.mp h).1)]

private theorem fiber_nz_card {G : Finset F} (hS : SidonModNeg G) {v : F} (hv : v ≠ 0)
    (hvI : v ∈ G.offDiag.image (fun p => p.1 + p.2)) :
    (G.offDiag.filter (fun p => p.1 + p.2 = v)).card = 2 := by
  obtain ⟨⟨a, b⟩, hab, hsum⟩ := Finset.mem_image.mp hvI
  rw [Finset.mem_offDiag] at hab
  obtain ⟨haG, hbG, hne⟩ := hab
  simp only at hsum
  have hpair : G.offDiag.filter (fun p => p.1 + p.2 = v) = {(a, b), (b, a)} := by
    ext ⟨c, e⟩
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hc, he, _hce⟩, hsce⟩
      have hc_mem : c ∈ G.filter (fun x => (a + b) - x ∈ G) := by
        rw [Finset.mem_filter]
        refine ⟨hc, ?_⟩
        have hvc : (a + b) - c = e := by linear_combination hsum - hsce
        rw [hvc]; exact he
      rw [filter_eq_pair hS haG hbG (by rw [hsum]; exact hv), Finset.mem_insert,
        Finset.mem_singleton] at hc_mem
      rcases hc_mem with rfl | rfl
      · left; exact ⟨rfl, by have h := hsce.trans hsum.symm; linear_combination h⟩
      · right; exact ⟨rfl, by have h := hsce.trans hsum.symm; linear_combination h⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨⟨haG, hbG, hne⟩, hsum⟩
      · exact ⟨⟨hbG, haG, hne.symm⟩, by rw [add_comm]; exact hsum⟩
  rw [hpair, Finset.card_insert_of_notMem
      (by simp only [Finset.mem_singleton, Prod.mk.injEq, not_and]; exact fun h => absurd h hne),
    Finset.card_singleton]

/-- **The distinct 2-subset-sum count under Sidon-mod-negation.** For a negation-closed,
no-self-antipodal, Sidon-mod-negation set `G` (e.g. the dyadic roots `μ_{2^μ}`), the number of
distinct off-diagonal sums `{a+b : a,b∈G, a≠b}` is `(|G|²−2|G|+2)/2`: every non-antipodal pair has a
unique sum and all `|G|/2` antipodal pairs collapse to the single value `0`. q-independent, cyclotomic,
no character sums (the Kambiré bad-count `|H^{(+2)}|`, piece-4 base case). -/
theorem two_mul_card_offDiag_sum_image {G : Finset F}
    (hneg : ∀ x ∈ G, -x ∈ G) (hself : ∀ x ∈ G, x ≠ -x) (hS : SidonModNeg G) (hG2 : 2 ≤ G.card) :
    2 * (G.offDiag.image (fun p => p.1 + p.2)).card = G.card * G.card - 2 * G.card + 2 := by
  classical
  set I := G.offDiag.image (fun p => p.1 + p.2) with hI
  set fib : F → ℕ := fun v => (G.offDiag.filter (fun p => p.1 + p.2 = v)).card with hfib
  have hmaps : ∀ p ∈ G.offDiag, p.1 + p.2 ∈ I := fun p hp => Finset.mem_image_of_mem _ hp
  have hcardsum : G.offDiag.card = ∑ v ∈ I, fib v := Finset.card_eq_sum_card_fiberwise hmaps
  have hoff : G.offDiag.card = G.card * G.card - G.card := Finset.offDiag_card G
  have h0I : (0 : F) ∈ I := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < G.card)
    exact Finset.mem_image.mpr ⟨(a, -a),
      by rw [Finset.mem_offDiag]; exact ⟨ha, hneg a ha, hself a ha⟩, by ring⟩
  have hfib0 : fib 0 = G.card := fiber_zero_card hneg hself
  rw [← Finset.add_sum_erase I fib h0I, hfib0] at hcardsum
  have herase : ∑ v ∈ I.erase 0, fib v = 2 * (I.erase 0).card := by
    rw [Finset.sum_congr rfl (fun v hv =>
      fiber_nz_card hS (Finset.ne_of_mem_erase hv) (Finset.mem_of_mem_erase hv)),
      Finset.sum_const, smul_eq_mul, mul_comm]
  rw [herase, Finset.card_erase_of_mem h0I, hoff] at hcardsum
  have hmm : 2 * G.card ≤ G.card * G.card := by nlinarith [hG2]
  have hI1 : 1 ≤ I.card := Finset.card_pos.mpr ⟨0, h0I⟩
  omega

end ArkLib.ProximityGap.AdditiveEnergySidonModNeg
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.two_mul_card_offDiag_sum_image
