/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80LEnergyRefinedConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80JDivisorSecondMoment

/-!
# LANE G80I (#466, 2026-07-10): the ENERGY-ROUTE ASSEMBLY — the unconditional theorem
  `T(W)⁴ ≤ n·W²·(log₂(W²)+1)³` below √p (axiom-clean, zero hypotheses; G80L × G80J joined).

## Content

* `mulEnergy_le_sum_sq_divisors` : for `A ⊆ [1,W]` (vals in `[1,W]`),
  `E×(A) ≤ Σ_{y ∈ [1,W²]} d(y)²` — each energy quadruple `(a,b,c,d)` with `ab = cd = y`
  contributes to `r(y)²` with `r(y) ≤ d(y)` (fibers inject into divisors, G80O) and the
  products lie in `[1, W²]`.
* `intervalCount_pow_four_le` (CAPSTONE) : for any prime `p`, multiplicatively closed
  `H ⊆ ZMod p`, `W² < p`:
  `T(W)⁴ ≤ |H| · (W² · (log₂(W²)+1)³)` — the energy consumer (G80L) fired by the divisor
  second moment (G80J). Equivalently `T(W) = O(n^{1/4}·√W·log^{3/4}W)` — NONTRIVIAL below
  the `n^{2/3}` threshold where G80M dies; together G80M + G80I give the best-of-both
  unconditional envelope `T(W) ≤ min(√n·W^{1/4}·C, n^{1/4}·√W·log^{3/4}·C')` on all
  `W < √p`.

## Honest scope

Fenced from the prize saddle by G80P regime disjointness. The next rung — the energy
RECURSION (Konyagin–Shkredov self-improvement of `E×`) — is where the open BGK content
begins. CORE remains OPEN / ON-BGK.

Issue #466. Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false


open Finset

namespace ArkLib.ProximityGap.Frontier.G80IEnergyRouteAssembly

open ArkLib.ProximityGap.Frontier.G80OProductDivisorInterval
open ArkLib.ProximityGap.Frontier.G80LEnergyRefinedConsumer
open ArkLib.ProximityGap.Frontier.G80JDivisorSecondMoment

/-- **Energy ≤ divisor second moment**: for a set of naturals inside `[1, W]`,
`E×(A) ≤ Σ_{y ∈ [1, W²]} d(y)²`. -/
theorem mulEnergy_le_sum_sq_divisors (A : Finset ℕ) {W : ℕ}
    (hA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ W) :
    mulEnergy A ≤ ∑ y ∈ Finset.Icc 1 (W * W), y.divisors.card ^ 2 := by
  classical
  set P : Finset ℕ := (A ×ˢ A).image (fun st => st.1 * st.2) with hP
  set r : ℕ → ℕ := fun y => ((A ×ˢ A).filter (fun st => st.1 * st.2 = y)).card with hr
  -- E = Σ_{y ∈ P} r(y)² (fiber partition, as in G80L)
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
  rw [henergy]
  -- P ⊆ [1, W²] and r(y) ≤ d(y)
  have hPsub : P ⊆ Finset.Icc 1 (W * W) := by
    intro y hy
    rw [hP, Finset.mem_image] at hy
    obtain ⟨⟨s, t⟩, hst, rfl⟩ := hy
    rw [Finset.mem_product] at hst
    obtain ⟨hs, ht⟩ := hst
    obtain ⟨hs1, hsW⟩ := hA s hs
    obtain ⟨ht1, htW⟩ := hA t ht
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
      Nat.mul_le_mul hsW htW⟩
  have hrd : ∀ y ∈ P, r y ^ 2 ≤ y.divisors.card ^ 2 := by
    intro y hy
    have hy0 : y ≠ 0 := by
      have := hPsub hy
      rw [Finset.mem_Icc] at this
      omega
    refine Nat.pow_le_pow_left ?_ 2
    -- fiber over A×A ⊆ fiber over [1,W]² ≤ divisors
    calc r y ≤ (((Finset.Icc 1 W) ×ˢ (Finset.Icc 1 W)).filter
        (fun st => st.1 * st.2 = y)).card := by
          rw [hr]
          refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
          refine Finset.product_subset_product ?_ ?_ <;>
            (intro a ha; rw [Finset.mem_Icc]; exact hA a ha)
      _ ≤ y.divisors.card := fiber_card_le_divisorCount W y hy0
  calc ∑ y ∈ P, r y ^ 2 ≤ ∑ y ∈ P, y.divisors.card ^ 2 := Finset.sum_le_sum hrd
    _ ≤ ∑ y ∈ Finset.Icc 1 (W * W), y.divisors.card ^ 2 :=
        Finset.sum_le_sum_of_subset hPsub

variable {p : ℕ} [Fact p.Prime] [NeZero p]

/-- **CAPSTONE — the assembled unconditional energy-route theorem**: for any prime `p`,
multiplicatively closed `H`, `W² < p`:
`T(W)⁴ ≤ |H| · W² · (log₂(W²)+1)³` — zero named hypotheses. -/
theorem intervalCount_pow_four_le
    (H : Finset (ZMod p)) (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    {W : ℕ} (hW : W * W < p) :
    intervalCount p H W ^ 4 ≤
      H.card * ((W * W) * (Nat.log 2 (W * W) + 1) ^ 3) := by
  classical
  set A : Finset ℕ := (Finset.Icc 1 W).filter (fun s => ((s : ℕ) : ZMod p) ∈ H) with hA
  have hAW : ∀ a ∈ A, 1 ≤ a ∧ a ≤ W := by
    intro a ha
    rw [hA, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ha.1
  calc intervalCount p H W ^ 4
      ≤ H.card * mulEnergy A := intervalCount_pow_four_le_energy H hmul hW
    _ ≤ H.card * ∑ y ∈ Finset.Icc 1 (W * W), y.divisors.card ^ 2 :=
        Nat.mul_le_mul_left _ (mulEnergy_le_sum_sq_divisors A hAW)
    _ ≤ H.card * ((W * W) * (Nat.log 2 (W * W) + 1) ^ 3) :=
        Nat.mul_le_mul_left _ (sum_sq_card_divisors_le (W * W))

end ArkLib.ProximityGap.Frontier.G80IEnergyRouteAssembly

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80IEnergyRouteAssembly.mulEnergy_le_sum_sq_divisors
#print axioms
  ArkLib.ProximityGap.Frontier.G80IEnergyRouteAssembly.intervalCount_pow_four_le
