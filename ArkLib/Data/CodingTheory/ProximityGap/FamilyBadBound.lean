/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# The per-family bad-scalar bound (#371, explainer geometry, brick R1)

**For ANY pair of codewords `(cs, d)`, the number of nonzero scalars `γ` whose
`mcaEvent`-badness is witnessed by the affine family member `cs + γ•d` is at most
`w + 1`** — for every code `C` (no linearity, distance, or rationality hypotheses),
over any coefficient field and any `NoZeroSMulDivisors` module of alphabets.

Mechanism (the E-disjointness count): on a family witness `S` the stack rows satisfy
`u₀ - cs = -γ•(u₁ - d)` pointwise, so `S ⊆ J ⊔ E_γ` where
`J := {i : u₀ i = cs i ∧ u₁ i = d i}` is the γ-independent joint-agreement set and
`E_γ := {i : u₁ i ≠ d i ∧ line equation}`.  The sets `E_γ` are pairwise disjoint in
the complement of `J` (the ratio `(u₀-cs)/(u₁-d)` determines `γ`), and the no-joint
clause of `mcaEvent` forces `E_γ ≠ ∅` (else `(cs, d)` itself jointly explains).
Counting disjoint sets of size `≥ n - w - |J|` inside the `≤ n - |J|`-point complement
gives `≤ w + 1` in every case.

This is the "in-family" half of the window classification: below UDR every
`mcaEvent`-bad scalar has a unique explainer, every PAIR of bad scalars generates such
a family through its secant, and the window extremals decompose into family/triangle
configurations.  Downstream (with the secant generation and the slope-capacity count)
this drives `WindowRationalBounded`.
-/

open Finset
open scoped NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- `γ` is *family-bad* for the codeword pair `(cs, d)`: some witness set of size
`≥ (1-δ)·n` carries exact agreement of the line `u₀ + γ•u₁` with the family member
`cs + γ•d`, yet admits no joint explanation of the stack.  Every `mcaEvent` whose
(below-UDR unique) explainer lies in the family is of this form. -/
def FamilyBad (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ cs d : ι → A) (γ : F) : Prop :=
  ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
    (∀ i ∈ S, cs i + γ • d i = u₀ i + γ • u₁ i) ∧
    ¬ pairJointAgreesOn C S u₀ u₁

namespace FamilyBad

variable [NoZeroSMulDivisors F A]

open Classical in
/-- **The per-family bound**: at radius `δ` with `δ·n ≤ w` and `δ ≤ 1`, at most
`w + 1` nonzero scalars are family-bad for any single codeword pair `(cs, d)`. -/
theorem card_le (C : Set (ι → A)) {δ : ℝ≥0} {w : ℕ} (hδ1 : δ ≤ 1)
    (hδn : δ * (Fintype.card ι : ℝ≥0) ≤ w)
    {u₀ u₁ cs d : ι → A} (hc : cs ∈ C) (hd : d ∈ C) :
    (Finset.univ.filter (fun γ : F => γ ≠ 0 ∧ FamilyBad C δ u₀ u₁ cs d γ)).card
      ≤ w + 1 := by
  set n := Fintype.card ι with hn
  -- the γ-independent joint-agreement set and the per-γ exclusive sets
  set J : Finset ι := Finset.univ.filter (fun i => u₀ i = cs i ∧ u₁ i = d i) with hJ
  set E : F → Finset ι := fun γ =>
    Finset.univ.filter (fun i => u₁ i ≠ d i ∧ cs i + γ • d i = u₀ i + γ • u₁ i)
    with hE
  set Γ : Finset F :=
    Finset.univ.filter (fun γ : F => γ ≠ 0 ∧ FamilyBad C δ u₀ u₁ cs d γ) with hΓ
  -- per-γ facts
  have key : ∀ γ ∈ Γ, (E γ).Nonempty ∧ n ≤ J.card + (E γ).card + w := by
    intro γ hγ
    rw [hΓ, Finset.mem_filter] at hγ
    obtain ⟨-, hγ0, S, hScard, hSline, hSnj⟩ := hγ
    -- witness size: n ≤ S.card + w
    have hsize : n ≤ S.card + w := by
      have h1 : ((1 : ℝ≥0) - δ) + δ = 1 := tsub_add_cancel_of_le hδ1
      have h2 : (n : ℝ≥0) ≤ (S.card : ℝ≥0) + w := by
        calc (n : ℝ≥0) = ((1 - δ) + δ) * n := by rw [h1, one_mul]
          _ = (1 - δ) * n + δ * n := by ring
          _ ≤ (S.card : ℝ≥0) + w := add_le_add hScard hδn
      exact_mod_cast h2
    -- S splits into J and E γ
    have hsplit : S ⊆ J ∪ E γ := by
      intro i hi
      have hline := hSline i hi
      by_cases hu1 : u₁ i = d i
      · -- then u₀ i = cs i, so i ∈ J
        have : cs i = u₀ i := by
          have := hline
          rw [hu1] at this
          exact add_right_cancel this
        exact Finset.mem_union_left _ (by
          rw [hJ, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, this.symm, hu1⟩)
      · exact Finset.mem_union_right _ (by
          rw [hE, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hu1, hline⟩)
    -- nonemptiness: the no-joint clause rules out (cs, d) on S
    have hne : (E γ).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      apply hSnj
      refine ⟨cs, hc, d, hd, fun i hi => ?_⟩
      have hiJ : i ∈ J := by
        have := hsplit hi
        rw [hempty, Finset.union_empty] at this
        exact this
      rw [hJ, Finset.mem_filter] at hiJ
      exact ⟨hiJ.2.1.symm, hiJ.2.2.symm⟩
    refine ⟨hne, ?_⟩
    calc n ≤ S.card + w := hsize
      _ ≤ (J ∪ E γ).card + w := by
          exact Nat.add_le_add_right (Finset.card_le_card hsplit) w
      _ ≤ J.card + (E γ).card + w := by
          exact Nat.add_le_add_right (Finset.card_union_le _ _) w
  -- disjointness of the E γ across distinct scalars
  have hdisj : ∀ γ ∈ Γ, ∀ γ' ∈ Γ, γ ≠ γ' → Disjoint (E γ) (E γ') := by
    intro γ _ γ' _ hne
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [hE, Finset.mem_filter] at hi hi'
    obtain ⟨-, hu1, heq⟩ := hi
    obtain ⟨-, -, heq'⟩ := hi'
    -- subtract the two line equations: (γ - γ') • (d i - u₁ i) = 0
    have h1 : γ • d i - γ • u₁ i = u₀ i - cs i := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm (γ • d i) (cs i)]
      exact heq
    have h2 : γ' • d i - γ' • u₁ i = u₀ i - cs i := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm (γ' • d i) (cs i)]
      exact heq'
    have hsub : (γ - γ') • (d i - u₁ i) = 0 := by
      have hexp : (γ - γ') • (d i - u₁ i)
          = (γ • d i - γ • u₁ i) - (γ' • d i - γ' • u₁ i) := by
        rw [sub_smul, smul_sub, smul_sub]
      rw [hexp, h1, h2, sub_self]
    rcases smul_eq_zero.mp hsub with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact hu1 (sub_eq_zero.mp h).symm
  -- the disjoint union of the E γ lives in the complement of J
  have hsubU : ∀ γ ∈ Γ, E γ ⊆ Finset.univ \ J := by
    intro γ _ i hi
    rw [hE, Finset.mem_filter] at hi
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, fun hiJ => ?_⟩
    rw [hJ, Finset.mem_filter] at hiJ
    exact hi.2.1 hiJ.2.2
  have hbiU : (Γ.biUnion E).card = ∑ γ ∈ Γ, (E γ).card :=
    Finset.card_biUnion hdisj
  have hUcard : (Γ.biUnion E).card ≤ n - J.card := by
    have h1 : (Γ.biUnion E).card ≤ (Finset.univ \ J).card :=
      Finset.card_le_card (Finset.biUnion_subset.mpr hsubU)
    have h2 : (Finset.univ \ J).card = n - J.card := by
      rw [Finset.card_sdiff, Finset.card_univ, Finset.inter_univ, ← hn]
    exact h2 ▸ h1
  -- case split on r := n - w - J.card
  by_cases hr : n ≤ J.card + w
  · -- complement is small: count nonempty disjoint sets
    have : Γ.card ≤ ∑ γ ∈ Γ, (E γ).card := by
      calc Γ.card = ∑ _γ ∈ Γ, 1 := by simp
        _ ≤ ∑ γ ∈ Γ, (E γ).card := by
            refine Finset.sum_le_sum fun γ hγ => ?_
            exact Nat.one_le_iff_ne_zero.mpr
              (Finset.card_ne_zero_of_mem ((key γ hγ).1.choose_spec))
    have hle : Γ.card ≤ n - J.card := le_trans this (hbiU ▸ hUcard)
    omega
  · -- complement is large: every E γ has size ≥ r ≥ 1
    push_neg at hr
    set r := n - (J.card + w) with hrdef
    have hr1 : 1 ≤ r := by omega
    have hEr : ∀ γ ∈ Γ, r ≤ (E γ).card := by
      intro γ hγ
      have := (key γ hγ).2
      omega
    have hsum : Γ.card * r ≤ ∑ γ ∈ Γ, (E γ).card := by
      calc Γ.card * r = ∑ _γ ∈ Γ, r := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ γ ∈ Γ, (E γ).card := Finset.sum_le_sum hEr
    have hcap : Γ.card * r ≤ n - J.card := le_trans hsum (hbiU ▸ hUcard)
    -- n - J.card = w + r, so Γ.card * r ≤ w + r with r ≥ 1 gives Γ.card ≤ w + 1
    have hwr : n - J.card ≤ w + r := by omega
    have hfin : Γ.card * r ≤ w + r := le_trans hcap hwr
    by_contra hbig
    push_neg at hbig
    have h1 : (w + 2) * r ≤ Γ.card * r :=
      Nat.mul_le_mul (by omega) (le_refl r)
    have h4 : (w + 2) * r ≤ w + r := le_trans h1 hfin
    have h2 : w ≤ w * r := by
      simpa using Nat.mul_le_mul (le_refl w) hr1
    have h3 : (w + 2) * r = w * r + 2 * r := by ring
    have h5 : w + 2 * r ≤ w * r + 2 * r := Nat.add_le_add_right h2 (2 * r)
    have h6 : w * r + 2 * r ≤ w + r := h3 ▸ h4
    have h7 : w + 2 * r ≤ w + r := le_trans h5 h6
    omega

end FamilyBad

end ProximityGap

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.FamilyBad.card_le
