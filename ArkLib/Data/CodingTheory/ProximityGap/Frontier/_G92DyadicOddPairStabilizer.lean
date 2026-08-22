/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CliqueOrbitFreeness

/-!
# G92: stabilizers of unordered odd-cardinality pairs in a dyadic translation torsor

G91's exact depth-five census found one possible short orbit after quotienting ordered cores by
coordinate permutations and side swap: a translation may exchange the two five-sets.  The
existing `CliqueOrbitFreeness` theorem already says that a translation fixing one odd-cardinality
set is trivial.  This file supplies the missing pair-level bridge.

If translation by `j` stabilizes an unordered pair `{A,B}`, then either it fixes both sides or
exchanges them.  In the first case `j=0`.  In the second case translation by `j+j` fixes each
side, hence `j+j=0`.  Thus every nontrivial pair stabilizer is the unique order-two translation
whenever the ambient dyadic group has a unique involution.  There are no other short orbits.

The theorem is stated for any finite additive group satisfying the two exact structural inputs
used by the proof: every nonzero element has positive even additive order, and the order-two
element is unique.  `ZMod (2^a)` supplies the first input via `zmod_two_pow_even_order`; the
second is isolated explicitly so downstream arithmetic can instantiate it with the half-turn.

Issue #505.  This classifies stabilizers; it does not prove the remaining generic depth-five
tenfold incidence estimate or close CORE.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.G92DyadicOddPairStabilizer

open ProximityGap.CliqueOrbitFreeness

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Translation by `j` fixes both ordered sides. -/
def FixesBoth (j : G) (A B : Finset G) : Prop :=
  (∀ x ∈ A, x + j ∈ A) ∧ (∀ x ∈ B, x + j ∈ B)

/-- Translation by `j` exchanges the two ordered sides. -/
def SwapsSides (j : G) (A B : Finset G) : Prop :=
  (∀ x ∈ A, x + j ∈ B) ∧ (∀ x ∈ B, x + j ∈ A)

/-- The setwise stabilizer predicate for an unordered pair, already split into its only two
permutations of the sides. -/
def StabilizesUnorderedPair (j : G) (A B : Finset G) : Prop :=
  FixesBoth j A B ∨ SwapsSides j A B

/-- A side-swapping translation squares to a translation fixing the first side. -/
theorem fixes_left_by_double_of_swapsSides
    {j : G} {A B : Finset G} (h : SwapsSides j A B) :
    ∀ x ∈ A, x + (j + j) ∈ A := by
  intro x hx
  have hxB := h.1 x hx
  have hxA := h.2 (x + j) hxB
  simpa [add_assoc] using hxA

/-- A side-swapping translation also squares to a translation fixing the second side. -/
theorem fixes_right_by_double_of_swapsSides
    {j : G} {A B : Finset G} (h : SwapsSides j A B) :
    ∀ x ∈ B, x + (j + j) ∈ B := by
  intro x hx
  have hxA := h.2 x hx
  have hxB := h.1 (x + j) hxA
  simpa [add_assoc] using hxB

/-- **Pair-stabilizer dichotomy.** In a group whose nonzero elements all have positive even
additive order, an unordered pair of odd-cardinality sets has only two possible stabilizers:
the identity, or an order-two side swap. -/
theorem stabilizer_eq_zero_or_orderTwo_swap
    (hevenOrder : ∀ j : G, j ≠ 0 → Even (addOrderOf j) ∧ 0 < addOrderOf j)
    {A B : Finset G} (hoddA : Odd A.card) (hoddB : Odd B.card)
    {j : G} (hstab : StabilizesUnorderedPair j A B) :
    j = 0 ∨ (j + j = 0 ∧ SwapsSides j A B) := by
  rcases hstab with hfix | hswap
  · exact Or.inl (fixed_eq_zero_of_odd_card hevenOrder hoddA hfix.1)
  · have hdouble : j + j = 0 :=
      fixed_eq_zero_of_odd_card hevenOrder hoddA
        (fixes_left_by_double_of_swapsSides hswap)
    by_cases hj : j = 0
    · exact Or.inl hj
    · exact Or.inr ⟨hdouble, hswap⟩

/-- A nontrivial stabilizer must exchange the sides and have additive order exactly two. -/
theorem nonzero_stabilizer_is_orderTwo_swap
    (hevenOrder : ∀ j : G, j ≠ 0 → Even (addOrderOf j) ∧ 0 < addOrderOf j)
    {A B : Finset G} (hoddA : Odd A.card) (hoddB : Odd B.card)
    {j : G} (hj : j ≠ 0) (hstab : StabilizesUnorderedPair j A B) :
    addOrderOf j = 2 ∧ SwapsSides j A B := by
  obtain hzero | ⟨hdouble, hswap⟩ :=
    stabilizer_eq_zero_or_orderTwo_swap hevenOrder hoddA hoddB hstab
  · exact absurd hzero hj
  · constructor
    · exact addOrderOf_eq_prime_iff.mpr ⟨by simpa [two_nsmul] using hdouble, hj⟩
    · exact hswap

/-- With a specified unique involution `h`, every nontrivial unordered-pair stabilizer is exactly
that half-turn and exchanges the two sides. -/
theorem nonzero_stabilizer_eq_uniqueInvolution
    (hevenOrder : ∀ j : G, j ≠ 0 → Even (addOrderOf j) ∧ 0 < addOrderOf j)
    (h : G) (hunique : ∀ j : G, j ≠ 0 → j + j = 0 → j = h)
    {A B : Finset G} (hoddA : Odd A.card) (hoddB : Odd B.card)
    {j : G} (hj : j ≠ 0) (hstab : StabilizesUnorderedPair j A B) :
    j = h ∧ SwapsSides j A B := by
  obtain hzero | ⟨hdouble, hswap⟩ :=
    stabilizer_eq_zero_or_orderTwo_swap hevenOrder hoddA hoddB hstab
  · exact absurd hzero hj
  · exact ⟨hunique j hj hdouble, hswap⟩

/-- **Uniqueness needs no ambient classification.** For one fixed unordered pair of odd sets,
there is at most one nonzero stabilizing translation.  Two such translations both swap the sides;
their sum fixes a side and is therefore zero, while each is its own inverse. -/
theorem nonzero_pair_stabilizer_unique
    (hevenOrder : ∀ j : G, j ≠ 0 → Even (addOrderOf j) ∧ 0 < addOrderOf j)
    {A B : Finset G} (hoddA : Odd A.card) (hoddB : Odd B.card)
    {j k : G} (hj : j ≠ 0) (hk : k ≠ 0)
    (hjstab : StabilizesUnorderedPair j A B)
    (hkstab : StabilizesUnorderedPair k A B) : j = k := by
  obtain ⟨hjtwo, hjswap⟩ :=
    nonzero_stabilizer_is_orderTwo_swap hevenOrder hoddA hoddB hj hjstab
  obtain ⟨hktwo, hkswap⟩ :=
    nonzero_stabilizer_is_orderTwo_swap hevenOrder hoddA hoddB hk hkstab
  have hsumFix : ∀ x ∈ A, x + (j + k) ∈ A := by
    intro x hx
    have hxB := hjswap.1 x hx
    have hxA := hkswap.2 (x + j) hxB
    simpa [add_assoc] using hxA
  have hsum : j + k = 0 :=
    fixed_eq_zero_of_odd_card hevenOrder hoddA hsumFix
  have hjneg : j = -k := eq_neg_of_add_eq_zero_left hsum
  have hkself : -k = k := by
    have hkdouble : k + k = 0 := by
      have hz := addOrderOf_nsmul_eq_zero k
      rw [hktwo] at hz
      simpa [two_nsmul] using hz
    have : k = -k := eq_neg_of_add_eq_zero_left hkdouble
    exact this.symm
  exact hjneg.trans hkself

/-- Prize-regime specialization: an unordered pair of odd-cardinality subsets of
`ZMod (2^a)` is stabilized only by zero or by an order-two side swap. -/
theorem zmod_two_pow_stabilizer_eq_zero_or_orderTwo_swap
    (a : ℕ) {A B : Finset (ZMod (2 ^ a))} (hoddA : Odd A.card) (hoddB : Odd B.card)
    {j : ZMod (2 ^ a)} (hstab : StabilizesUnorderedPair j A B) :
    j = 0 ∨ (j + j = 0 ∧ SwapsSides j A B) :=
  stabilizer_eq_zero_or_orderTwo_swap
    (fun j hj => zmod_two_pow_even_order a j hj) hoddA hoddB hstab

#print axioms fixes_left_by_double_of_swapsSides
#print axioms fixes_right_by_double_of_swapsSides
#print axioms stabilizer_eq_zero_or_orderTwo_swap
#print axioms nonzero_stabilizer_is_orderTwo_swap
#print axioms nonzero_stabilizer_eq_uniqueInvolution
#print axioms nonzero_pair_stabilizer_unique
#print axioms zmod_two_pow_stabilizer_eq_zero_or_orderTwo_swap

end ArkLib.ProximityGap.Frontier.G92DyadicOddPairStabilizer
