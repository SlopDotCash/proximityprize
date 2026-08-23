/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The `(∑x, ∑x²)` statistic is injective at agreement `a=2` (Issue #232)

The `k=0` boundary of the list-decoding interior grid. For the `t=2` statistic `(∑x, ∑x²)` over
**2**-element subsets of the smooth domain, the map is INJECTIVE (`two_set_inj`,
`statistic_injOn_two`): each 2-subset `{x,y}` is recovered from `(s,q)=(x+y, x²+y²)` via
`xy=(s²−q)/2` (needs char ≠ 2, which the smooth domain has). Consequently the second moment /
collision count at `a=2` is exactly `C(n,2)` — the statistic is **maximally anti-concentrated**, the
prize-survival regime. With the `a=h` (coset, `n/h`) exact count and the `h∤n` vanishing, this pins
the boundary of the open `2 ≤ a < h` interior. Axiom-clean.
-/

open Finset

namespace ArkLib.ProximityGap.A2Injective

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The `(∑x, ∑x²)` statistic is injective on 2-element sets (char ≠ 2).** If `{x,y}` and
`{x',y'}` (each two distinct elements) have equal sum and equal sum-of-squares, they are equal as
sets. Hence on the smooth domain the `t=2` statistic is injective at agreement `a=2` — the `k=0`
boundary is fully anti-concentrated (`collisionCount = C(n,2)`), the prize-survival regime. -/
theorem two_set_inj (h2 : (2 : F) ≠ 0) {x y x' y' : F}
    (hxy : x ≠ y) (hxy' : x' ≠ y')
    (hsum : x + y = x' + y') (hsq : x ^ 2 + y ^ 2 = x' ^ 2 + y' ^ 2) :
    ({x, y} : Finset F) = {x', y'} := by
  have h2xy : 2 * (x * y) = 2 * (x' * y') := by linear_combination (x + y + x' + y') * hsum - hsq
  have hprod : x * y = x' * y' := mul_left_cancel₀ h2 h2xy
  have hx'_root : (x' - x) * (x' - y) = 0 := by
    have e : (x' - x) * (x' - y) = x' ^ 2 - (x + y) * x' + x * y := by ring
    rw [e, hsum, hprod]; ring
  have hy'_root : (y' - x) * (y' - y) = 0 := by
    have e : (y' - x) * (y' - y) = y' ^ 2 - (x + y) * y' + x * y := by ring
    rw [e, hsum, hprod]; ring
  have hx'mem : x' = x ∨ x' = y := by
    rcases mul_eq_zero.mp hx'_root with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hy'mem : y' = x ∨ y' = y := by
    rcases mul_eq_zero.mp hy'_root with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hsub : ({x', y'} : Finset F) ⊆ {x, y} := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    rcases hz with rfl | rfl
    · exact hx'mem
    · exact hy'mem
  exact (Finset.eq_of_subset_of_card_le hsub
    (by rw [Finset.card_pair hxy, Finset.card_pair hxy'])).symm

/-- **Injectivity of the `(∑x, ∑x²)` statistic on 2-element subsets.** Over a field with `2 ≠ 0`,
the map `S ↦ (∑_{z∈S} z, ∑_{z∈S} z²)` is injective on the 2-element subsets of any `G`. Hence the
second-moment collision count at `a=2` is exactly `C(|G|,2)` (each 2-subset collides only with
itself) — the maximally anti-concentrated `k=0` boundary. -/
theorem statistic_injOn_two (h2 : (2 : F) ≠ 0) (G : Finset F) :
    Set.InjOn (fun S => (∑ z ∈ S, z, ∑ z ∈ S, z ^ 2)) (↑(G.powersetCard 2) : Set (Finset F)) := by
  intro S hS S' hS' h
  rw [Finset.mem_coe, Finset.mem_powersetCard] at hS hS'
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hS.2
  obtain ⟨x', y', hxy', rfl⟩ := Finset.card_eq_two.mp hS'.2
  simp only [Finset.sum_pair hxy, Finset.sum_pair hxy', Prod.mk.injEq] at h
  exact two_set_inj h2 hxy hxy' h.1 h.2

private lemma sum_split (g : F → F) (S S' : Finset F) :
    ∑ x ∈ S, g x = ∑ x ∈ S \ S', g x + ∑ x ∈ S ∩ S', g x := by
  rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S S'), Finset.sdiff_union_inter]

/-- **No low-order collisions.** Two equal-size subsets `S, S'` (`2 ≠ 0`) with the same sum AND same
sum-of-squares that differ in at most 2 elements must be EQUAL. Hence two *distinct* equal-statistic
equal-size subsets satisfy `|S \ S'| ≥ 3` (so `|S △ S'| ≥ 6`): the `(∑x, ∑x²)` statistic has no
collisions of small symmetric difference — `m=1` is impossible, `m=2` is killed by `two_set_inj`.
This structurally confines the collision-count off-diagonal to symmetric difference `≥ 6`. -/
theorem no_low_order_collision (h2 : (2 : F) ≠ 0) {S S' : Finset F}
    (hcard : S.card = S'.card)
    (hsum : ∑ x ∈ S, x = ∑ x ∈ S', x)
    (hsq : ∑ x ∈ S, x ^ 2 = ∑ x ∈ S', x ^ 2)
    (hsmall : (S \ S').card ≤ 2) : S = S' := by
  classical
  have hcardD : (S \ S').card = (S' \ S).card := Finset.card_sdiff_eq_card_sdiff_iff.mpr hcard
  have hsumD : ∑ x ∈ S \ S', x = ∑ x ∈ S' \ S, x := by
    have e1 := sum_split (fun x => x) S S'
    have e2 := sum_split (fun x => x) S' S
    rw [Finset.inter_comm S' S] at e2
    rw [e1, e2] at hsum; simpa using hsum
  have hsqD : ∑ x ∈ S \ S', x ^ 2 = ∑ x ∈ S' \ S, x ^ 2 := by
    have e1 := sum_split (fun x => x ^ 2) S S'
    have e2 := sum_split (fun x => x ^ 2) S' S
    rw [Finset.inter_comm S' S] at e2
    rw [e1, e2] at hsq; simpa using hsq
  have hdisj : Disjoint (S \ S') (S' \ S) := by
    rw [Finset.disjoint_left]; intro a ha hb
    rw [Finset.mem_sdiff] at ha hb; exact ha.2 hb.1
  have hzero : (S \ S').card = 0 := by
    rcases Nat.lt_or_ge (S \ S').card 1 with h0 | h1
    · omega
    rcases Nat.lt_or_ge (S \ S').card 2 with h1' | h2'
    · exfalso
      have hD1 : (S \ S').card = 1 := by omega
      have hD'1 : (S' \ S).card = 1 := by rw [← hcardD]; exact hD1
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hD1
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hD'1
      rw [hu, hv] at hsumD; simp only [Finset.sum_singleton] at hsumD
      subst hsumD
      have hmemu : u ∈ S \ S' := by rw [hu]; simp
      have hmemu' : u ∈ S' \ S := by rw [hv]; simp
      exact (Finset.disjoint_left.mp hdisj hmemu) hmemu'
    · exfalso
      have hD2 : (S \ S').card = 2 := by omega
      have hD'2 : (S' \ S).card = 2 := by rw [← hcardD]; exact hD2
      obtain ⟨u1, u2, hu12, hu⟩ := Finset.card_eq_two.mp hD2
      obtain ⟨v1, v2, hv12, hv⟩ := Finset.card_eq_two.mp hD'2
      rw [hu, hv] at hsumD hsqD
      rw [Finset.sum_pair hu12, Finset.sum_pair hv12] at hsumD
      rw [Finset.sum_pair hu12, Finset.sum_pair hv12] at hsqD
      have heq := two_set_inj h2 hu12 hv12 hsumD hsqD
      rw [← hu, ← hv] at heq
      have hne : (S \ S').Nonempty := by rw [hu]; exact ⟨u1, by simp⟩
      obtain ⟨w, hw⟩ := hne
      have hw' : w ∈ S' \ S := heq ▸ hw
      exact (Finset.disjoint_left.mp hdisj hw) hw'
  rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hzero
  exact Finset.eq_of_subset_of_card_le hzero (by rw [hcard])

end ArkLib.ProximityGap.A2Injective

#print axioms ArkLib.ProximityGap.A2Injective.statistic_injOn_two
#print axioms ArkLib.ProximityGap.A2Injective.no_low_order_collision
