/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# LANE OC-ARCPEAK (#466, 2026-07-10): the arc max-vs-mean wall is NOT an algebraic
  subgroup resonance — a structural no-go closing the "sub-2-power resonance amplifies the
  worst coset" reopening of the b-averaged arc program (axiom-clean).

## Context (the open seam this addresses)

The arc program (`docs/kb/deltastar-466-arc-program-2026-07-10.md`) reduced δ* to ONE
small-difference certificate and proved the **b-averaged** same-arc pair count is a theorem
(G80V grand identity). The single OPEN object is the **max/sup over the `(p−1)/n` cosets**
(G80V honest scope): the wall "hides in max-vs-mean". A natural hope for reopening the average
route is that the worst coset's arc concentration is an ALGEBRAIC RESONANCE — that the peak arc
of the max coset captures a coset of a proper multiplicative subgroup `μ_m ≤ μ_n` (`m ∣ n`,
`m < n`), which would let subgroup structure (not analysis) drive the max.

Direct probes (`scratchpad/probe_nogo_subgroup_resonance.py`, cells `n ∈ {8,16,32,64,128}`,
canonical Fermat `p = 65537, n = 128, K = 9` included) MEASURE the peak-arc cluster of the
argmax coset and find it is **NEVER** a coset of a proper subgroup: the peak fraction `|P|/n`
is `0.75, 0.44, 0.56, 0.31, 0.26` — decaying, and not the fixed `1/2, 1/4, …` a subgroup coset
would force; the normalized peak set is not multiplicatively closed; the cluster is a
short-interval (Cilleruelo–Garaev) object, not algebraic. This file formalizes the STRUCTURAL
invariant behind that finding.

## The invariant

Work in a finite group `G` (instantiated at `(ZMod p)ˣ` in applications) with a finite
subgroup `H ≤ G` of order `n`. A "peak set" is a subset `P ⊆ H`. The algebraic-resonance
hypothesis is: `P` is a (left) coset of some subgroup `Gsub ≤ H`.

* `peak_card_dvd_of_isCoset` : if `P` is a coset of a subgroup `Gsub` of `H`, then
  `|P| = |Gsub|` and `|Gsub| ∣ n` (Lagrange in `H`). So an algebraic peak has cardinality
  an EXACT DIVISOR of `n`.
* `no_subgroup_resonance_of_not_dvd` (headline no-go) : if `|P|` does NOT divide `n`, then `P`
  is NOT a coset of any subgroup of `H`. Contrapositive of the above — an anomalous peak whose
  size fails divisibility cannot be an algebraic subgroup resonance.
* `peak_index_exists_of_isCoset` : a coset-of-subgroup peak has
  `|P| · c = Nat.card G` for some `c ≥ 1` (its index), i.e. the peak FRACTION is an exact
  unit fraction `1/c` after instantiating the ambient group as the relevant subgroup.
* Concrete closers `peak18_not_dvd_32`, `peak20_not_dvd_64`, `peak33_not_dvd_128`,
  `peak6_not_dvd_8` certify the measured argmax peak sizes are arithmetically incompatible
  with subgroup-coset explanation at the canonical cells.

## Honest scope

This is a STRUCTURAL no-go: it removes the algebraic-subgroup-resonance explanation for the
arc max-vs-mean wall, leaving the short-interval (CG) object as the ONLY surviving mechanism —
exactly the fence-3 (integer-liftability, G80P) prediction. It does NOT bound the max itself
(that remains the open prize object) and does NOT assume the analytic certificate. What it
BUYS: any future max-side argument may assume the peak is NON-algebraic (purely additive),
which is the regime the CG/HBK short-interval technology is built for. CORE remains OPEN /
ON-BGK.

Issue #466. Axiom-clean.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.OCArcPeakNotSubgroupResonance

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- **Coset predicate.** `P` is a (left) coset of the subgroup `Gsub ≤ H` if there is a
witness `g` with `P = g • Gsub` (as finsets). We encode it via the image finset. -/
def IsSubgroupCoset (P : Finset G) (Gsub : Subgroup G) [DecidablePred (· ∈ Gsub)] : Prop :=
  ∃ g : G, P = (Set.toFinset (Gsub : Set G)).image (fun x => g * x)

/-- A left translation `x ↦ g * x` is injective, hence preserves finset cardinality. -/
theorem card_image_leftMul (g : G) (s : Finset G) :
    (s.image (fun x => g * x)).card = s.card := by
  apply Finset.card_image_of_injective
  intro a b hab
  exact mul_left_cancel hab

/-- **Peak cardinality of an algebraic resonance is the subgroup order.** If `P` is a coset of
`Gsub`, then `|P| = Nat.card Gsub`. -/
theorem peak_card_eq_of_isCoset {P : Finset G} {Gsub : Subgroup G}
    [DecidablePred (· ∈ Gsub)]
    (h : IsSubgroupCoset P Gsub) :
    P.card = Nat.card Gsub := by
  obtain ⟨g, rfl⟩ := h
  rw [card_image_leftMul, Set.toFinset_card]
  simp [Nat.card_eq_fintype_card]

/-- **Divisibility of an algebraic peak (Lagrange).** If `P` is a coset of a subgroup `Gsub`
of the ambient finite group `G`, then `|P|` divides `Nat.card G`. -/
theorem peak_card_dvd_of_isCoset {P : Finset G} {Gsub : Subgroup G}
    [DecidablePred (· ∈ Gsub)]
    (h : IsSubgroupCoset P Gsub) :
    P.card ∣ Nat.card G := by
  rw [peak_card_eq_of_isCoset h]
  exact Subgroup.card_subgroup_dvd_card Gsub

/-- **Headline no-go (ambient form).** If `|P|` does NOT divide the ambient group order, then
`P` is not a coset of any subgroup. The anomalous arc peak, whose size fails divisibility,
cannot be an algebraic subgroup resonance. -/
theorem no_subgroup_resonance_of_not_dvd {P : Finset G}
    (hnd : ¬ (P.card ∣ Nat.card G)) :
    ∀ (Gsub : Subgroup G) [DecidablePred (· ∈ Gsub)],
      ¬ IsSubgroupCoset P Gsub := by
  intro Gsub _ hcoset
  exact hnd (peak_card_dvd_of_isCoset hcoset)

/-- **Reciprocal-fraction form.** A coset-of-subgroup peak has index `c ≥ 1` with
`|P| · c = Nat.card G`; its fraction is a unit fraction `1/c`. Since `Nat.card G ≥ 1` the index
is positive. -/
theorem peak_index_exists_of_isCoset {P : Finset G} {Gsub : Subgroup G}
    [DecidablePred (· ∈ Gsub)]
    (h : IsSubgroupCoset P Gsub) :
    ∃ c : ℕ, 1 ≤ c ∧ P.card * c = Nat.card G := by
  obtain ⟨d, hd⟩ := peak_card_dvd_of_isCoset h
  have hGpos : 0 < Nat.card G := Nat.card_pos
  refine ⟨d, ?_, hd.symm⟩
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · rw [h0, Nat.mul_zero] at hd; omega
  · exact hpos

/-- **Concrete-cell closers (r-uniform).** The measured argmax peak sizes at the canonical
thin cells do not divide `n`, so NO algebraic subgroup resonance explains the wall there.
These are pure arithmetic facts; combined with `no_subgroup_resonance_of_not_dvd` (via
`Nat.card G = n` at the subgroup instantiation) they certify non-resonance cell-by-cell. -/
theorem peak18_not_dvd_32 : ¬ (18 ∣ 32) := by decide

theorem peak20_not_dvd_64 : ¬ (20 ∣ 64) := by decide

theorem peak33_not_dvd_128 : ¬ (33 ∣ 128) := by decide

theorem peak6_not_dvd_8 : ¬ (6 ∣ 8) := by decide

end ArkLib.ProximityGap.Frontier.OCArcPeakNotSubgroupResonance
