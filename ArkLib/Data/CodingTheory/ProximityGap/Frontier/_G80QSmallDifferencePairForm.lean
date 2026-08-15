/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80SDirectionalStripReduction

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# LANE G80Q (#466, 2026-07-10): the SMALL-DIFFERENCE PAIR form — the arc certificate in its
  final classical shape: `pairCount(b·H) ≤ |H| + #{(u,z) ∈ (b·H)² : u ≠ z, u − z ∈ Strip}`
  (axiom-clean; the terminal simplification of the strip reduction).

## The simplification

G80S's capstone bounds the pair certificate by `Σ_{d ∈ H, d≠1} #{z ∈ b·H : (d−1)z ∈ Strip}`.
This lane collapses that ratio-indexed sum via the exact bijection `(d, z) ↦ (d·z, z)`:
since `z ∈ b·H` and `d ∈ H` give `d·z ∈ b·H`, and conversely any pair `(u, z) ∈ (b·H)²` has
`u/z ∈ H`, the sum EQUALS the off-diagonal small-difference pair count of the coset itself:

* `strip_sum_eq_smallDiffPairs` :
  `Σ_{d ∈ H.erase 1} #{z ∈ b·H : (d−1)z ∈ Strip} = #{(u,z) ∈ (b·H)², u ≠ z, u − z ∈ Strip}`.
* `pairCount_le_smallDiffPairs` (CAPSTONE) :
  `pairCount(b·H) ≤ |H| + #{(u,z) ∈ (b·H)² : u ≠ z, u − z ∈ Strip(p/K)}`.

## The pair certificate, final form

The exact pair-form input is a bound, for every coset `C = b·μ_n` and window `W = p/K`, on

  `#{(u, z) ∈ C² : u ≠ z, |u − z| < W (signed)} ≤ n²·(2W/p)·O(1) + n·polylog(q)`.

This is the Cilleruelo–Garaev small-difference object verbatim. It feeds G80W's pair-excess
consumer, but that consumer loses `√K`; therefore a generic `n·polylog(q)` error, or a constant
factor above the uniform main term, is not by itself sufficient for the prize scale. A closure
through this route needs the quantitatively stronger pair-excess budget already calibrated in
G80W, or a signed/correlated consumer avoiding the `√K` loss. Known CG/BGK technology reaches
strong estimates only in substantially denser regimes; the prize regime remains the wall.

## Honest scope

Exact combinatorial collapse only. No small-difference estimate is proved, and the displayed
classical-shaped estimate is not asserted to overcome G80W's `√K` loss. CORE remains OPEN /
ON-BGK.

Issue #466. Axiom-clean.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G80QSmallDifferencePairForm

open ArkLib.ProximityGap.Frontier.G80ZArcArithmeticInstantiation
open ArkLib.ProximityGap.Frontier.G80VArcDilationCoincidenceReduction
open ArkLib.ProximityGap.Frontier.G80SDirectionalStripReduction

variable {p : ℕ} [Fact p.Prime] [NeZero p]

variable (H : Finset (ZMod p)) (h0 : (0 : ZMod p) ∉ H)
  (hdiv : ∀ x ∈ H, ∀ y ∈ H, x * y⁻¹ ∈ H)
  (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)

include h0 hdiv hmul in
/-- **The ratio-sum collapse**: summing per-ratio strip counts over `d ∈ H \ {1}` equals the
off-diagonal small-difference pair count of the coset `b·H`. Bijection `(d, z) ↦ (d·z, z)`. -/
theorem strip_sum_eq_smallDiffPairs (W : ℕ) (b : ZMod p) (hb : b ≠ 0) :
    ∑ d ∈ H.erase 1,
        ((H.image (fun y => b * y)).filter
          (fun z => (d - 1) * z ∈ strip p W)).card
      = (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
          (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card := by
  classical
  set C : Finset (ZMod p) := H.image (fun y => b * y) with hC
  have hC0 : (0 : ZMod p) ∉ C := by
    rw [hC]
    intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨y, hy, hzero⟩ := hmem
    have hy0 : y ≠ 0 := fun h => h0 (h ▸ hy)
    exact (mul_ne_zero hb hy0) hzero
  -- partition the RHS by the ratio d = u/z ∈ H \ {1}
  have hpart : (C ×ˢ C).filter (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)
      = (H.erase 1).biUnion (fun d =>
          (C.filter (fun z => (d - 1) * z ∈ strip p W)).image (fun z => (d * z, z))) := by
    ext ⟨u, z⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_erase]
    constructor
    · rintro ⟨⟨hu, hz⟩, hne, hstrip⟩
      have hz0 : z ≠ 0 := fun h => hC0 (h ▸ hz)
      -- d = u/z ∈ H: u = b·y_u, z = b·y_z, u/z = y_u/y_z ∈ H
      rw [hC, Finset.mem_image] at hu hz
      obtain ⟨yu, hyu, rfl⟩ := hu
      obtain ⟨yz, hyz, rfl⟩ := hz
      have hyz0 : yz ≠ 0 := fun h => h0 (h ▸ hyz)
      refine ⟨(b * yu) * (b * yz)⁻¹, ⟨?_, ?_⟩, b * yz, ⟨?_, ?_⟩, ?_⟩
      · -- ratio ≠ 1
        intro h1
        apply hne
        have := congrArg (· * (b * yz)) h1
        simp only [one_mul] at this
        rw [mul_assoc, inv_mul_cancel₀ (fun h => hz0 h)] at this
        · rw [← this, mul_one]
      · -- ratio ∈ H
        have hrw : (b * yu) * (b * yz)⁻¹ = yu * yz⁻¹ := by
          field_simp
        rw [hrw]
        exact hdiv yu hyu yz hyz
      · rw [hC]
        exact Finset.mem_image_of_mem _ hyz
      · -- strip condition transfers
        have hrw : ((b * yu) * (b * yz)⁻¹ - 1) * (b * yz) = b * yu - b * yz := by
          field_simp
        rw [hrw]
        exact hstrip
      · -- (d·z, z) = (u, z)
        have hrw : (b * yu) * (b * yz)⁻¹ * (b * yz) = b * yu := by
          field_simp
        rw [hrw]
    · rintro ⟨d, ⟨hd1, hdH⟩, z, ⟨hzC, hstrip⟩, heq⟩
      have hz0 : z ≠ 0 := fun h => hC0 (h ▸ hzC)
      injection heq with hu hz'
      subst hz'
      constructor
      · constructor
        · -- d·z ∈ C
          rw [← hu]
          rw [hC, Finset.mem_image] at hzC ⊢
          obtain ⟨y, hy, rfl⟩ := hzC
          exact ⟨d * y, hmul d hdH y hy, by ring⟩
        · exact hzC
      · constructor
        · -- d·z ≠ z
          rw [← hu]
          intro hdz
          apply hd1
          have := mul_right_cancel₀ hz0 (hdz.trans (one_mul z).symm)
          exact this
        · rw [← hu, show d * z - z = (d - 1) * z by ring]
          exact hstrip
  rw [hpart, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.card_image_of_injective _ fun a c hac => by injection hac]
  · -- disjointness: the ratio determines d
    intro d hd d' hd' hne
    refine Finset.disjoint_left.mpr ?_
    rintro ⟨u, z⟩ hm hm'
    simp only [Finset.mem_image, Finset.mem_filter] at hm hm'
    obtain ⟨z1, ⟨hz1, _⟩, heq1⟩ := hm
    obtain ⟨z2, ⟨hz2, _⟩, heq2⟩ := hm'
    injection heq1 with hu1 hv1
    injection heq2 with hu2 hv2
    subst hv1
    have hz0 : z1 ≠ 0 := fun h => by
      rw [hC, Finset.mem_image] at hz1
      obtain ⟨y, hy, hby⟩ := hz1
      have hy0 : y ≠ 0 := fun h' => h0 (h' ▸ hy)
      exact (mul_ne_zero hb hy0) (h ▸ hby)
    rw [hv2] at hu2
    exact hne (mul_right_cancel₀ hz0 (hu1.trans hu2.symm))

include h0 hdiv hmul in
/-- **CAPSTONE — the certificate in final classical form.** For every dilation `b ≠ 0`:
`pairCount(b·H) ≤ |H| + #{(u,z) ∈ (b·H)² : u ≠ z, u − z ∈ Strip(p/K)}` — the arc/pair
certificate is the SMALL-DIFFERENCE pair count of the coset. -/
theorem pairCount_le_smallDiffPairs (K : ℕ) (hK : 0 < K) (h1 : (1 : ZMod p) ∈ H)
    (b : ZMod p) (hb : b ≠ 0) :
    ((H ×ˢ H).filter
        (fun q => arcIndex K (b * q.1) = arcIndex K (b * q.2))).card
      ≤ H.card +
        (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
          (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p (p / K))).card := by
  calc ((H ×ˢ H).filter
        (fun q => arcIndex K (b * q.1) = arcIndex K (b * q.2))).card
      ≤ H.card + ∑ d ∈ H.erase 1,
          ((H.image (fun y => b * y)).filter
            (fun z => (d - 1) * z ∈ strip p (p / K))).card :=
        pairCount_le_strip_sum H h0 hdiv hmul K hK h1 b hb
    _ = _ := by rw [strip_sum_eq_smallDiffPairs H h0 hdiv hmul (p / K) b hb]

end ArkLib.ProximityGap.Frontier.G80QSmallDifferencePairForm

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80QSmallDifferencePairForm.strip_sum_eq_smallDiffPairs
#print axioms
  ArkLib.ProximityGap.Frontier.G80QSmallDifferencePairForm.pairCount_le_smallDiffPairs
