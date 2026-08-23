/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.InterleavedListMCACollapse

/-!
# The incidence route to `epsMCA`: bounding the interleaved list of an MDS code (#389)

The δ\* chain in this cone is: MCA bad-scalar count `≤` interleaved-list cardinality at the
doubled radius (`mcaBad_card_le_interleavedList`), then `→ epsMCA` (`epsMCA_le_of_badCount_le`).
The remaining open input is bounding `interleavedList C f₁ f₂ a` — the number of codeword pairs
`(g₁,g₂) ∈ C × C` jointly agreeing with `(f₁,f₂)` on `≥ a` positions.

This file bounds that list by the same **incidence / charging** argument used for the higher-order
MDS list bounds (`MDSIncidenceBound.lean`): for an MDS code (two codewords agreeing on `≥ k`
positions are equal), each interleaved pair is determined by *any* `k` points of its joint-agreement
set, so distinct pairs charge to disjoint `k`-subsets and `|interleavedList(a)| · C(a,k) ≤ C(n,k)`.

* `interleavedList_card_le` — the interleaved-list bound, `|interleavedList(a)| · C(a,k) ≤ C(n,k)`.
* `mcaBadSet_card_le_binom` — chaining with the repo collapse gives an explicit binomial bound on
  the MCA bad-scalar count, `|mcaBadSet| · C(2t−n,k) ≤ C(2t−n,k) + (n−(2t−n)) · C(n,k)`, feeding
  `epsMCA` via `epsMCA_le_of_badCount_le`.

This makes the incidence route to `epsMCA` unconditional given PairClosed + MDS.  Note the bound is
non-vacuous only for `2t−n ≥ k` (i.e. `δ ≤ (1−ρ)/2`, *below* the prize window): the crude factor
`C(n,k)/C(a,k)` is exponential in the window, so pinning δ\* in the window interior still requires a
*sub*-`C(n,k)/C(a,k)` (higher-order-MDS) list bound — exactly the open GM-MDS certificate.
Axiom-clean.
-/

open Finset Round17CAPair InterleavedMCACollapse

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [DecidableEq F] [Fintype F]

omit [DecidableEq ι] [Field F] [Fintype F] in
/-- **The interleaved-list cardinality bound for an MDS code.**  If any two codewords of `C`
agreeing on `≥ k` positions are equal (the MDS / unique-`k`-interpolation property), then the
`2`-interleaved list at joint-agreement floor `a` has at most `C(n,k) / C(a,k)` pairs:
each pair `(g₁,g₂)` is determined by any `k` points of its joint-agreement set, so distinct pairs
charge to disjoint `k`-subsets and `|interleavedList(a)| · C(a,k) ≤ C(n,k)`. -/
theorem interleavedList_card_le (C : Finset (ι → F)) (f₁ f₂ : ι → F) {a k : ℕ}
    (huniq : ∀ g ∈ C, ∀ g' ∈ C,
      k ≤ (univ.filter (fun x => g x = g' x)).card → g = g') :
    (interleavedList C f₁ f₂ a).card * a.choose k ≤ (Fintype.card ι).choose k := by
  classical
  have hLdef : ∀ p : (ι → F) × (ι → F), p ∈ interleavedList C f₁ f₂ a ↔
      p.1 ∈ C ∧ p.2 ∈ C ∧ a ≤ (jointAgreeSet f₁ f₂ p.1 p.2).card := by
    intro p
    unfold interleavedList
    rw [Finset.mem_filter, Finset.mem_product]
    tauto
  have htarget : (univ.powersetCard k : Finset (Finset ι)).card = (Fintype.card ι).choose k := by
    rw [Finset.card_powersetCard, Finset.card_univ]
  have hsig : ((interleavedList C f₁ f₂ a).sigma
        (fun p => (jointAgreeSet f₁ f₂ p.1 p.2).powersetCard k)).card
      = ∑ p ∈ interleavedList C f₁ f₂ a, (jointAgreeSet f₁ f₂ p.1 p.2).card.choose k := by
    rw [Finset.card_sigma]
    exact Finset.sum_congr rfl (fun p _ => Finset.card_powersetCard k _)
  have hcard_le : (∑ p ∈ interleavedList C f₁ f₂ a,
      (jointAgreeSet f₁ f₂ p.1 p.2).card.choose k) ≤ (Fintype.card ι).choose k := by
    rw [← hsig, ← htarget]
    apply Finset.card_le_card_of_injOn (fun x => x.2)
    · rintro ⟨p, s⟩ hps
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powersetCard, Finset.subset_univ,
        true_and] at hps ⊢
      exact hps.2.2
    · rintro ⟨p, s⟩ hps ⟨p', s'⟩ hps' heq
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powersetCard] at hps hps'
      have hss : s = s' := heq
      subst hss
      obtain ⟨hp1, hp2, -⟩ := (hLdef p).mp hps.1
      obtain ⟨hp'1, hp'2, -⟩ := (hLdef p').mp hps'.1
      have hk1 : k ≤ (univ.filter (fun x => p.1 x = p'.1 x)).card := by
        rw [← hps.2.2]
        apply Finset.card_le_card
        intro x hx
        have h1 := hps.2.1 hx
        have h2 := hps'.2.1 hx
        rw [jointAgreeSet, Finset.mem_filter] at h1 h2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, h1.2.1.symm.trans h2.2.1⟩
      have hk2 : k ≤ (univ.filter (fun x => p.2 x = p'.2 x)).card := by
        rw [← hps.2.2]
        apply Finset.card_le_card
        intro x hx
        have h1 := hps.2.1 hx
        have h2 := hps'.2.1 hx
        rw [jointAgreeSet, Finset.mem_filter] at h1 h2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, h1.2.2.symm.trans h2.2.2⟩
      have hpp : p = p' :=
        Prod.ext (huniq p.1 hp1 p'.1 hp'1 hk1) (huniq p.2 hp2 p'.2 hp'2 hk2)
      subst hpp; rfl
  have hlb : (interleavedList C f₁ f₂ a).card * a.choose k
      ≤ ∑ p ∈ interleavedList C f₁ f₂ a, (jointAgreeSet f₁ f₂ p.1 p.2).card.choose k := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    exact Nat.choose_le_choose k ((hLdef p).mp hp).2.2
  exact le_trans hlb hcard_le

/-- **End-to-end: the MCA bad-scalar count for an MDS, PairClosed code is binomial-bounded.**
Chaining the repo collapse `mcaBad_card_le_interleavedList` with `interleavedList_card_le`: at
witness floor `t` and code dimension `k`, the bad-scalar count satisfies
`|mcaBadSet| · C(2t−n, k) ≤ C(2t−n, k) + (n − (2t−n)) · C(n, k)`.  Unconditional given PairClosed
and the MDS unique-`k`-interpolation property; this is the incidence route to `epsMCA`. -/
theorem mcaBadSet_card_le_binom (C : Finset (ι → F)) (hC : PairClosed C) (f₁ f₂ : ι → F)
    (t k : ℕ) (huniq : ∀ g ∈ C, ∀ g' ∈ C,
      k ≤ (univ.filter (fun x => g x = g' x)).card → g = g') :
    (mcaBadSet C f₁ f₂ t).card * (2 * t - Fintype.card ι).choose k
      ≤ (2 * t - Fintype.card ι).choose k
        + (Fintype.card ι - (2 * t - Fintype.card ι)) * (Fintype.card ι).choose k := by
  set n := Fintype.card ι with hn
  set a := 2 * t - n with ha
  have h1 : (mcaBadSet C f₁ f₂ t).card ≤ 1 + (n - a) * (interleavedList C f₁ f₂ a).card :=
    mcaBad_card_le_interleavedList C hC f₁ f₂ t
  have h2 : (interleavedList C f₁ f₂ a).card * a.choose k ≤ n.choose k :=
    interleavedList_card_le C f₁ f₂ huniq
  calc (mcaBadSet C f₁ f₂ t).card * a.choose k
      ≤ (1 + (n - a) * (interleavedList C f₁ f₂ a).card) * a.choose k :=
        Nat.mul_le_mul_right _ h1
    _ = a.choose k + (n - a) * ((interleavedList C f₁ f₂ a).card * a.choose k) := by ring
    _ ≤ a.choose k + (n - a) * n.choose k :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ h2) _
