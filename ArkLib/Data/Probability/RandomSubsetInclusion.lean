/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic

/-!
# Inclusion count for uniformly random size-`n` subsets (hypergeometric first-moment brick)

For a finite set `s` and a fixed element `x ∈ s`, the number of `n`-element subsets of `s` that
contain `x`, scaled by `|s|`, equals `n` times the total number of `n`-element subsets:

  `|{L ⊆ s : |L| = n ∧ x ∈ L}| · |s| = n · C(|s|, n)`.

Equivalently, a uniformly random size-`n` subset of `s` contains a fixed `x ∈ s` with probability
`n / |s|`. This is the **first-moment linchpin** for random-domain (random Reed–Solomon) list
decoding / MCA bounds: the expected number of bad evaluation points in a random size-`n` domain is
`|Bad| · n / |F|`. It is the size-`n`-subset analogue of the random-linear-code uniform marginal
in `RandomLinearCodeEquidistribution.lean`, and supplies the marginal that the now-closed #71
uniform size-`n` subset PMF (`Probability.uniformSizedSubset`) needs for ABF26 T3.6 / T4.15.

`card_filter_mem_powersetCard_mul` is `sorry`-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

namespace ArkLib.RandomSubset

open Finset

variable {α : Type*} [DecidableEq α]

/-- **Hypergeometric inclusion count.** For `x ∈ s` and any `n`,
`|{L ∈ s.powersetCard n : x ∈ L}| · |s| = n · |s.powersetCard n|`. Division-free `ℕ` form of the
marginal `Pr[x ∈ L] = n / |s|` for a uniformly random `n`-element subset `L` of `s`. -/
theorem card_filter_mem_powersetCard_mul {s : Finset α} {x : α} (hx : x ∈ s) (n : ℕ) :
    ((s.powersetCard n).filter (fun L => x ∈ L)).card * s.card
      = n * (s.powersetCard n).card := by
  cases n with
  | zero =>
    simp [Finset.powersetCard_zero, Finset.filter_singleton]
  | succ m =>
    have hxni : x ∉ s.erase x := Finset.notMem_erase x s
    -- decompose the (m+1)-subsets of `s = insert x (s.erase x)`
    have hdecomp : s.powersetCard (m + 1)
        = (s.erase x).powersetCard (m + 1)
            ∪ ((s.erase x).powersetCard m).image (insert x) := by
      conv_lhs => rw [← Finset.insert_erase hx]
      exact Finset.powersetCard_succ_insert hxni m
    -- the `x`-containing subsets are exactly the `insert x`-images
    have hfilter : (s.powersetCard (m + 1)).filter (fun L => x ∈ L)
        = ((s.erase x).powersetCard m).image (insert x) := by
      rw [hdecomp, Finset.filter_union]
      rw [Finset.filter_false_of_mem (s := (s.erase x).powersetCard (m + 1))
            (fun L hL hxL => hxni ((Finset.mem_powersetCard.1 hL).1 hxL))]
      rw [Finset.empty_union, Finset.filter_true_of_mem]
      intro L hL
      obtain ⟨T, -, rfl⟩ := Finset.mem_image.1 hL
      exact Finset.mem_insert_self x T
    have hinj : Set.InjOn (insert x) ((s.erase x).powersetCard m : Set (Finset α)) := by
      intro T₁ hT₁ T₂ hT₂ h
      have hx₁ : x ∉ T₁ := fun hxm => hxni ((Finset.mem_powersetCard.1 hT₁).1 hxm)
      have hx₂ : x ∉ T₂ := fun hxm => hxni ((Finset.mem_powersetCard.1 hT₂).1 hxm)
      rw [← Finset.erase_insert hx₁, ← Finset.erase_insert hx₂, h]
    rw [hfilter, Finset.card_image_of_injOn hinj, Finset.card_powersetCard,
      Finset.card_powersetCard, Finset.card_erase_of_mem hx]
    -- goal: (|s| - 1).choose m * |s| = (m + 1) * |s|.choose (m + 1), via succ_mul_choose_eq
    have hpos : 0 < s.card := Finset.card_pos.2 ⟨x, hx⟩
    have key := Nat.succ_mul_choose_eq (s.card - 1) m
    simp only [Nat.succ_eq_add_one, Nat.sub_add_cancel hpos] at key
    -- key : s.card * (s.card - 1).choose m = s.card.choose (m + 1) * (m + 1)
    rw [mul_comm ((s.card - 1).choose m) s.card, key, mul_comm]

/-- **Hypergeometric pairwise-inclusion count.** For distinct `x, y ∈ s`,
`|{L ∈ s.powersetCard n : x ∈ L ∧ y ∈ L}| · (|s| · (|s| − 1)) = n · (n − 1) · |s.powersetCard n|`.
Division-free `ℕ` form of `Pr[x ∈ L ∧ y ∈ L] = n(n−1) / (|s|(|s|−1))` for a uniformly random
size-`n` subset — the second-moment / pairwise ingredient for random-domain (random RS)
concentration. Reduces to the single-inclusion count on `s.erase x`. -/
theorem card_filter_mem_mem_powersetCard_mul {s : Finset α} {x y : α}
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) (n : ℕ) :
    ((s.powersetCard n).filter (fun L => x ∈ L ∧ y ∈ L)).card * (s.card * (s.card - 1))
      = n * (n - 1) * (s.powersetCard n).card := by
  cases n with
  | zero =>
    rw [Finset.powersetCard_zero, Finset.filter_singleton]
    simp
  | succ m =>
    have hyex : y ∈ s.erase x := Finset.mem_erase.2 ⟨hxy.symm, hy⟩
    -- bijection L ↦ L.erase x : {L ∋ x,y} ≃ {T ∋ y, T ⊆ s.erase x}
    have hbij : ((s.powersetCard (m + 1)).filter (fun L => x ∈ L ∧ y ∈ L)).card
        = (((s.erase x).powersetCard m).filter (fun L => y ∈ L)).card := by
      refine Finset.card_bij' (fun L _ => L.erase x) (fun T _ => insert x T) ?hi ?hj ?linv ?rinv
      case hi =>
        intro L hL
        rw [Finset.mem_filter, Finset.mem_powersetCard] at hL
        obtain ⟨⟨hLs, hLc⟩, hxL, hyL⟩ := hL
        rw [Finset.mem_filter, Finset.mem_powersetCard]
        exact ⟨⟨Finset.erase_subset_erase x hLs,
            by rw [Finset.card_erase_of_mem hxL, hLc, Nat.add_sub_cancel]⟩,
          Finset.mem_erase.2 ⟨hxy.symm, hyL⟩⟩
      case hj =>
        intro T hT
        rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
        obtain ⟨⟨hTs, hTc⟩, hyT⟩ := hT
        have hxT : x ∉ T := fun h => (Finset.mem_erase.1 (hTs h)).1 rfl
        rw [Finset.mem_filter, Finset.mem_powersetCard]
        exact ⟨⟨Finset.insert_subset hx (hTs.trans (Finset.erase_subset x s)),
          by rw [Finset.card_insert_of_notMem hxT, hTc]⟩,
          Finset.mem_insert_self x T, Finset.mem_insert_of_mem hyT⟩
      case linv =>
        intro L hL
        rw [Finset.mem_filter] at hL
        exact Finset.insert_erase hL.2.1
      case rinv =>
        intro T hT
        rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
        exact Finset.erase_insert (fun h => (Finset.mem_erase.1 (hT.1.1 h)).1 rfl)
    rw [hbij]
    have hsingle := card_filter_mem_powersetCard_mul (s := s.erase x) hyex m
    rw [Finset.card_powersetCard, Finset.card_erase_of_mem hx] at hsingle
    rw [Finset.card_powersetCard]
    have hpos : 0 < s.card := Finset.card_pos.2 ⟨x, hx⟩
    have hchoose := Nat.succ_mul_choose_eq (s.card - 1) m
    simp only [Nat.succ_eq_add_one, Nat.sub_add_cancel hpos] at hchoose
    set c := (((s.erase x).powersetCard m).filter (fun L => y ∈ L)).card with hc
    -- hsingle : c * (s.card - 1) = m * (s.card - 1).choose m ;  goal uses c
    have hkey : c * (s.card * (s.card - 1)) = (m + 1) * m * (s.card).choose (m + 1) := by
      rw [mul_left_comm c s.card (s.card - 1), hsingle,
        mul_left_comm s.card m ((s.card - 1).choose m), hchoose,
        mul_comm ((s.card).choose (m + 1)) (m + 1), ← mul_assoc, mul_comm m (m + 1)]
    simpa using hkey

end ArkLib.RandomSubset

#print axioms ArkLib.RandomSubset.card_filter_mem_powersetCard_mul
#print axioms ArkLib.RandomSubset.card_filter_mem_mem_powersetCard_mul
