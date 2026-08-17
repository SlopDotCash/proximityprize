/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80OProductDivisorInterval
import Mathlib.Algebra.Order.Chebyshev

/-!
# LANE G80L (#466, 2026-07-10): the ENERGY-REFINED consumer — `T(W)⁴ ≤ n·E×(A)` by
  Cauchy–Schwarz on product-map fibers: interval counts are controlled by the INTEGER
  multiplicative energy of the interval piece (axiom-clean).

## Why this rung

The crude k-fold ladder (fiber ≤ `d(y)^{k−1}`) worsens with k; the genuine CG/BGK bootstrap
refines the FIBER SECOND MOMENT — the multiplicative energy. This lane lands the exact
consumer for that refinement:

* `sq_card_le_card_mul_energy` (Cauchy–Schwarz over fibers): for ANY finite `A ⊆ ℕ` and the
  product map on `A × A`, `|A|⁴ = (Σ_y r(y))² ≤ #(products)·Σ_y r(y)² = #(products)·E×(A)`,
  where `E×(A) = #{(a,b,c,d) ∈ A⁴ : a·b = c·d}` (INTEGER multiplicative energy).
* `intervalCount_pow_four_le_energy` (capstone): for multiplicatively closed `H`, `W² < p`,
  with `A = {s ∈ [1,W] : s mod p ∈ H}`:  `T(W)⁴ ≤ |H| · E×(A)` — the product SET collapses
  into `H` by rigidity (≤ n distinct products), so the interval count is controlled by the
  integer multiplicative energy of the interval piece.

## What this opens (honest)

`E×(A)` for `A ⊆ [1,W]` is the central object of the integer sum-product literature
(Bourgain–Chang, Konyagin–Shkredov): the known `E×(A) ≤ |A|²·W^{o(1)}` (divisor-moment
methods) would give `T⁴ ≤ n·T²·W^{o(1)}` — i.e. `T(W) ≤ √n·W^{o(1)}` for ALL `W < √p`, the
FULL CG bound, strictly better than G80M's `√n·W^{1/4}` — from a PURE-integer energy input
with no subgroup content (the subgroup enters only through the `≤ n` product-set cap, proven
here). Formalizing `E×(A) ≤ |A|²·W^{o(1)}` (Σ_{y≤M} d(y)² ≈ M·log³M partial-summation
machinery) is the next Nat-plumbing target. Still fenced from the prize saddle (G80P);
advances the interval face. CORE remains OPEN / ON-BGK.

Issue #466. Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false


open Finset

namespace ArkLib.ProximityGap.Frontier.G80LEnergyRefinedConsumer

open ArkLib.ProximityGap.Frontier.G80OProductDivisorInterval

/-- Integer multiplicative energy of a finite set of naturals:
`#{(a,b,c,d) ∈ A⁴ : a·b = c·d}`. -/
def mulEnergy (A : Finset ℕ) : ℕ :=
  (((A ×ˢ A) ×ˢ (A ×ˢ A)).filter
    (fun q => q.1.1 * q.1.2 = q.2.1 * q.2.2)).card

/-- **Cauchy–Schwarz over product fibers**: `|A|⁴ ≤ #(A·A) · E×(A)`, where `A·A` is the
product set `(A ×ˢ A).image (·*·)`. -/
theorem sq_card_le_card_mul_energy (A : Finset ℕ) :
    A.card ^ 4 ≤ ((A ×ˢ A).image (fun st => st.1 * st.2)).card * mulEnergy A := by
  classical
  set P : Finset ℕ := (A ×ˢ A).image (fun st => st.1 * st.2) with hP
  set r : ℕ → ℕ := fun y => ((A ×ˢ A).filter (fun st => st.1 * st.2 = y)).card with hr
  -- |A|² = Σ_{y ∈ P} r(y)
  have hsum : A.card ^ 2 = ∑ y ∈ P, r y := by
    rw [sq, ← Finset.card_product]
    rw [hP, hr]
    exact Finset.card_eq_sum_card_image (fun st => st.1 * st.2) (A ×ˢ A)
  -- E×(A) = Σ_{y ∈ P} r(y)²
  have henergy : mulEnergy A = ∑ y ∈ P, r y ^ 2 := by
    rw [mulEnergy]
    have hsplit : ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter
        (fun q => q.1.1 * q.1.2 = q.2.1 * q.2.2)
        = P.biUnion (fun y =>
            ((A ×ˢ A).filter (fun st => st.1 * st.2 = y)) ×ˢ
            ((A ×ˢ A).filter (fun st => st.1 * st.2 = y))) := by
      ext ⟨⟨a, b⟩, ⟨c, d⟩⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, hP,
        Finset.mem_image]
      constructor
      · rintro ⟨⟨hab, hcd⟩, heq⟩
        exact ⟨a * b, ⟨(a, b), hab, rfl⟩, ⟨⟨hab, rfl⟩, ⟨hcd, heq.symm⟩⟩⟩
      · rintro ⟨y, _, ⟨⟨hab, hy1⟩, ⟨hcd, hy2⟩⟩⟩
        exact ⟨⟨hab, hcd⟩, hy1.trans hy2.symm⟩
    rw [hsplit, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.card_product, sq, hr]
    · intro y _ y' _ hyy'
      refine Finset.disjoint_left.mpr ?_
      rintro ⟨st, uv⟩ hm hm'
      simp only [Finset.mem_product, Finset.mem_filter] at hm hm'
      exact hyy' (hm.1.2.symm.trans hm'.1.2)
  -- Cauchy–Schwarz: (Σ r)² ≤ |P|·Σ r²
  have hcs : (∑ y ∈ P, r y) ^ 2 ≤ P.card * ∑ y ∈ P, r y ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc A.card ^ 4 = (A.card ^ 2) ^ 2 := by ring
    _ = (∑ y ∈ P, r y) ^ 2 := by rw [hsum]
    _ ≤ P.card * ∑ y ∈ P, r y ^ 2 := hcs
    _ = P.card * mulEnergy A := by rw [henergy]

variable {p : ℕ} [Fact p.Prime] [NeZero p]

/-- **CAPSTONE — the energy-refined interval consumer**: for multiplicatively closed `H`,
`W² < p`, with `A` the interval piece: `T(W)⁴ ≤ |H| · E×(A)`. The product set collapses into
`H` by no-wraparound rigidity, so the subgroup enters ONLY through the `≤ |H|` cap; the open
input is the pure-integer energy `E×(A)` — the sum-product literature's central object. -/
theorem intervalCount_pow_four_le_energy
    (H : Finset (ZMod p)) (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    {W : ℕ} (hW : W * W < p) :
    intervalCount p H W ^ 4 ≤
      H.card * mulEnergy ((Finset.Icc 1 W).filter (fun s => ((s : ℕ) : ZMod p) ∈ H)) := by
  classical
  set A : Finset ℕ := (Finset.Icc 1 W).filter (fun s => ((s : ℕ) : ZMod p) ∈ H) with hA
  have hT : intervalCount p H W = A.card := rfl
  -- product set ≤ |H| by rigidity (from G80O's image argument)
  have hprodset : ((A ×ˢ A).image (fun st => st.1 * st.2)).card ≤ H.card := by
    refine Finset.card_le_card_of_injOn (fun y => ((y : ℕ) : ZMod p)) ?_ ?_
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_image] at hy
      obtain ⟨⟨s, t⟩, hst, rfl⟩ := hy
      simp only [hA, Finset.mem_product, Finset.mem_filter] at hst
      obtain ⟨hs, ht⟩ := hst
      push_cast
      exact hmul _ hs.2 _ ht.2
    · intro y hy y' hy' heq
      simp only [Finset.mem_coe, Finset.mem_image] at hy hy'
      obtain ⟨⟨s, t⟩, hst, rfl⟩ := hy
      obtain ⟨⟨s', t'⟩, hst', rfl⟩ := hy'
      simp only [hA, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hst hst'
      obtain ⟨hs, ht⟩ := hst
      obtain ⟨hs', ht'⟩ := hst'
      have h1 : s * t < p := lt_of_le_of_lt (Nat.mul_le_mul hs.1.2 ht.1.2) hW
      have h2 : s' * t' < p := lt_of_le_of_lt (Nat.mul_le_mul hs'.1.2 ht'.1.2) hW
      have := (ZMod.natCast_eq_natCast_iff' (s * t) (s' * t') p).mp heq
      rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
  calc intervalCount p H W ^ 4 = A.card ^ 4 := by rw [hT]
    _ ≤ ((A ×ˢ A).image (fun st => st.1 * st.2)).card * mulEnergy A :=
        sq_card_le_card_mul_energy A
    _ ≤ H.card * mulEnergy A := Nat.mul_le_mul_right _ hprodset

end ArkLib.ProximityGap.Frontier.G80LEnergyRefinedConsumer

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80LEnergyRefinedConsumer.sq_card_le_card_mul_energy
#print axioms
  ArkLib.ProximityGap.Frontier.G80LEnergyRefinedConsumer.intervalCount_pow_four_le_energy
