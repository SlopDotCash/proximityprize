/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

/-!
# LANE G80O (#466, 2026-07-10): the PRODUCT–DIVISOR interval route — subgroup-interval counts
  obey `T(W)² ≤ D·n` below √p, where `D` is a PURE Nat divisor-count bound: the first
  Cilleruelo–Garaev-type mechanism in-tree, with the wall shifted to a textbook lemma
  (axiom-clean skeleton; divisor input named).

## The mechanism (CG product trick, formalized)

For multiplicatively closed `H` (`|H| = n`) and `T(W) := #{s ∈ [1,W] : s mod p ∈ H}` with
`W² < p`:

* products of two counted elements satisfy `s·t < p` — NO wraparound — so the integer product
  `y = s·t ∈ [1, W²]` determines the residue, and `y mod p ∈ H` (multiplicativity);
* the fiber of the product map over `y` injects into `y`'s divisors
  (`fiber_card_le_divisorCount`);
* distinct integers in `[1, W²] ⊆ [1, p−1]` have distinct residues, so the image injects
  into `H` (`image_card_le_card`);
* hence `T(W)² ≤ D·n` whenever every `y ≤ W²` has at most `D` divisors
  (`intervalCount_sq_le_of_divisorBound`).

## Quantitative reading (honest)

With the ELEMENTARY divisor bound `d(y) ≤ 2√y` the result is vacuous (`√(2W·n)` is the
geometric mean, never below `min(n, W)`). The route becomes NONTRIVIAL with the classical
constant-exponent divisor bound `d(y) ≤ C_δ·y^δ` (elementary via multiplicativity —
`d(2^a) = a+1 ≤ C·2^{aδ}` etc., a PURE Nat lemma with no subgroup content): at `δ = 1/4`,
`T(W) ≤ √(C·n)·W^{1/4}`, strictly below `min(n, W)` throughout `n^{2/3} < W < n²` — e.g.
`T(n) = O(n^{3/4})`, the first CG-type saving expressible in-tree. At `δ = o(1)` (the true
divisor rate) it reaches `T(W) ≤ √n·W^{o(1)}` for ALL `W < √p` — the full CG interval bound.

The regime cap `W < √p` is the G80P rigidity window: this route CANNOT reach the prize saddle
(`W = p/K ≫ √p`, regime-disjoint — G80P). Its value: (i) the missing analytic input for a
genuine machine-checked CG bound is now a NAT-ONLY divisor lemma (`DivisorBound` below);
(ii) it is the k = 2 rung of the k-fold product ladder `T(W)^k ≤ D_k·n` (`W^k < p`), whose
`k → log p / log W` limit is the BGK bootstrap — the formal skeleton all deeper rungs share.

## Honest scope

The subgroup/rigidity/counting skeleton is UNCONDITIONAL and axiom-clean. The divisor input
is a named hypothesis (`DivisorBound`), elementary-known, not yet formalized — pure Nat
plumbing, no wall content. No prize progress claimed: the route is fenced away from the
saddle by G80P regime disjointness. CORE remains OPEN / ON-BGK.

Issue #466. Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false


open Finset

namespace ArkLib.ProximityGap.Frontier.G80OProductDivisorInterval

variable {p : ℕ} [Fact p.Prime] [NeZero p]

/-- Interval count of `H`-residues: `#{s ∈ [1, W] : (s : ZMod p) ∈ H}`. -/
def intervalCount (p : ℕ) [NeZero p] (H : Finset (ZMod p)) (W : ℕ) : ℕ :=
  ((Finset.Icc 1 W).filter (fun s => ((s : ℕ) : ZMod p) ∈ H)).card

/-- The named divisor input (PURE Nat, no subgroup content): every `y ∈ [1, M]` has at most
`D` divisors. Elementary-known at `D = C_δ·M^δ` for every fixed `δ > 0`. -/
def DivisorBound (M D : ℕ) : Prop :=
  ∀ y ∈ Finset.Icc 1 M, y.divisors.card ≤ D

/-- **Fiber ↪ divisors**: pairs `(s, t) ∈ [1, W]²` with `s·t = y` inject into the divisors
of `y` via first projection. -/
theorem fiber_card_le_divisorCount (W y : ℕ) (hy : y ≠ 0) :
    (((Finset.Icc 1 W) ×ˢ (Finset.Icc 1 W)).filter
      (fun st => st.1 * st.2 = y)).card ≤ y.divisors.card := by
  refine Finset.card_le_card_of_injOn (fun st => st.1) ?_ ?_
  · rintro ⟨s, t⟩ hst
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hst
    obtain ⟨⟨hs, _⟩, hmul⟩ := hst
    show s ∈ y.divisors
    rw [Nat.mem_divisors]
    exact ⟨⟨t, hmul.symm⟩, hy⟩
  · rintro ⟨s, t⟩ hst ⟨s', t'⟩ hst' heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hst hst'
    obtain ⟨⟨hs, ht⟩, hmul⟩ := hst
    obtain ⟨⟨hs', ht'⟩, hmul'⟩ := hst'
    simp only at heq
    subst heq
    have hs0 : s ≠ 0 := by
      have := (Finset.mem_Icc.mp hs).1; omega
    have : t = t' := by
      have h1 : s * t = s * t' := by rw [hmul, hmul']
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hs0) h1
    simp [this]

/-- **CAPSTONE — the product–divisor square bound**: for multiplicatively closed `H` and
`W² < p`, `T(W)² ≤ D·|H|` under the Nat-only divisor input `DivisorBound W² D`. -/
theorem intervalCount_sq_le_of_divisorBound
    (H : Finset (ZMod p)) (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    {W D : ℕ} (hW : W * W < p) (hD : DivisorBound (W * W) D) :
    intervalCount p H W * intervalCount p H W ≤ D * H.card := by
  classical
  set S : Finset ℕ := (Finset.Icc 1 W).filter (fun s => ((s : ℕ) : ZMod p) ∈ H) with hS
  have hcard : intervalCount p H W = S.card := rfl
  -- the product map on S × S
  have hsq : intervalCount p H W * intervalCount p H W = (S ×ˢ S).card := by
    rw [hcard, Finset.card_product]
  rw [hsq]
  -- fibers of (s,t) ↦ s*t are ≤ D; image ≤ |H|
  calc (S ×ˢ S).card
      ≤ D * ((S ×ˢ S).image (fun st => st.1 * st.2)).card := by
        refine Finset.card_le_mul_card_image _ D ?_
        intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨⟨s, t⟩, hst, rfl⟩ := hy
        rw [Finset.mem_product, hS] at hst
        obtain ⟨hs, ht⟩ := hst
        rw [Finset.mem_filter, Finset.mem_Icc] at hs ht
        have hy1 : 1 ≤ s * t := Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by omega) (by omega))
        have hyW : s * t ≤ W * W := Nat.mul_le_mul hs.1.2 ht.1.2
        have hyne : s * t ≠ 0 := by omega
        calc ((S ×ˢ S).filter (fun st => st.1 * st.2 = s * t)).card
            ≤ (((Finset.Icc 1 W) ×ˢ (Finset.Icc 1 W)).filter
                (fun st => st.1 * st.2 = s * t)).card := by
              refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
              refine Finset.product_subset_product ?_ ?_ <;>
                exact fun a ha => (Finset.mem_filter.mp ha).1
          _ ≤ (s * t).divisors.card := fiber_card_le_divisorCount W (s * t) hyne
          _ ≤ D := hD (s * t) (Finset.mem_Icc.mpr ⟨hy1, hyW⟩)
    _ ≤ D * H.card := by
        refine Nat.mul_le_mul_left D ?_
        -- image ↪ H : y ↦ (y : ZMod p), injective on [1, W²] ⊆ [1, p−1]
        refine Finset.card_le_card_of_injOn (fun y => ((y : ℕ) : ZMod p)) ?_ ?_
        · intro y hy
          simp only [Finset.mem_coe, Finset.mem_image] at hy
          obtain ⟨⟨s, t⟩, hst, rfl⟩ := hy
          simp only [hS, Finset.mem_product, Finset.mem_filter] at hst
          obtain ⟨hs, ht⟩ := hst
          push_cast
          exact hmul _ hs.2 _ ht.2
        · intro y hy y' hy' heq
          simp only [Finset.mem_coe, Finset.mem_image] at hy hy'
          obtain ⟨⟨s, t⟩, hst, rfl⟩ := hy
          obtain ⟨⟨s', t'⟩, hst', rfl⟩ := hy'
          simp only [hS, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc]
            at hst hst'
          obtain ⟨hs, ht⟩ := hst
          obtain ⟨hs', ht'⟩ := hst'
          have h1 : s * t < p := lt_of_le_of_lt (Nat.mul_le_mul hs.1.2 ht.1.2) hW
          have h2 : s' * t' < p := lt_of_le_of_lt (Nat.mul_le_mul hs'.1.2 ht'.1.2) hW
          have := (ZMod.natCast_eq_natCast_iff' (s * t) (s' * t') p).mp heq
          rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this

end ArkLib.ProximityGap.Frontier.G80OProductDivisorInterval

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80OProductDivisorInterval.fiber_card_le_divisorCount
#print axioms
  ArkLib.ProximityGap.Frontier.G80OProductDivisorInterval.intervalCount_sq_le_of_divisorBound
