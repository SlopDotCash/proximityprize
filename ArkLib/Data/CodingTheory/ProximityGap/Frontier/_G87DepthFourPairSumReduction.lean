/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# G87: depth four reduces to factor-5 pair-sum concentration

With the G86 sharp envelope, the production depth-four overshoot of the unrestricted equal-sum
core universe drops from `2^11.26` (coarse envelope; G82 pinned the cutoff there) to `2^2.09`.
This file closes that remaining gap by an elementary convolution split.  Writing
`pairCount S c = #{(h,h') ∈ S^2 : h+h' = c}` and `quadCount` for quadruples,

```text
quadCount a  =  sum_c pairCount c * pairCount (a-c)  <=  (M+1) * n^2,
J_4          =  sum_a (quadCount a)^2                <=  (M+1) * n^6,
```

where `M = max_{c ≠ 0} pairCount c` is the **pair-sum concentration** of `S` (the `c = 0` term
pays `pairCount 0 <= n`).  The production consumer kernel-checks that `M <= n/5` puts the whole
depth-four sharp envelope inside one full Wick budget at `(n, r) = (2^30, 110)`.

Consequence: the depth-four sector — the first honest cutoff of the padded collision lane —
no longer needs square-root cancellation, an additive-energy estimate, or any Fourier input.
It needs only `max_{c≠0} |S ∩ (c-S)| <= n/5`, a factor-5 anti-concentration statement.  For a
multiplicative subgroup of size `n <= p^{2/3}` the classical Stepanov-method bound of
Garcia–Voloch (1988) / Heath-Brown–Konyagin (2000) gives `~4 n^{2/3}` (`~2^22` versus the
required `2^27.7` at production), so the recorded hypothesis `PairSumConcentration5` is far
inside known territory; it is an explicit named assumption here, not proved in Lean.  Depth
five remains genuinely open: even `M ~ n^{2/3}` leaves the analogous chain about `2^26` over
budget.  Probe: `scripts/probes/probe_466_g87_depth_four_feasibility.py`.  Issue #466.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace ArkLib.ProximityGap.Frontier.G87DepthFourPairSumReduction

open Finset
open scoped Nat

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Number of ordered pairs from `S` with sum `c`. -/
def pairCount (S : Finset G) (c : G) : ℕ :=
  ((S ×ˢ S).filter fun p => p.1 + p.2 = c).card

/-- Number of ordered quadruples from `S` with total sum `a`. -/
def quadCount (S : Finset G) (a : G) : ℕ :=
  (((S ×ˢ S) ×ˢ (S ×ˢ S)).filter fun p => p.1.1 + p.1.2 + (p.2.1 + p.2.2) = a).card

/-- The ordered equal-sum core universe at depth four: pairs of quadruples with equal sums. -/
def equalSumQuadPairs (S : Finset G) : ℕ :=
  ∑ a : G, quadCount S a ^ 2

/-- **Factor-5 pair-sum concentration** — the named external input.  For a multiplicative
subgroup `S = H` of `F_p^*` with `|H| <= p^{2/3}` this holds with enormous room by the
Stepanov-method bound `max_{c≠0} |H ∩ (c-H)| <= ~4|H|^{2/3}` (Garcia–Voloch 1988;
Heath-Brown–Konyagin 2000).  Recorded as an assumption, not proved here. -/
def PairSumConcentration5 (S : Finset G) : Prop :=
  ∀ c : G, c ≠ 0 → pairCount S c ≤ S.card / 5

/-- A summand pair is determined by its first coordinate once the sum is fixed. -/
theorem pairCount_le_card (S : Finset G) (c : G) : pairCount S c ≤ S.card := by
  classical
  unfold pairCount
  calc
    ((S ×ˢ S).filter fun p => p.1 + p.2 = c).card
        ≤ (S.image fun h => (h, c - h)).card := by
      apply Finset.card_le_card
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      rcases hp with ⟨⟨h1, _⟩, hsum⟩
      have h2 : p.2 = c - p.1 := by
        rw [← hsum]
        abel
      exact Finset.mem_image.mpr ⟨p.1, h1, by rw [← h2]⟩
    _ ≤ S.card := Finset.card_image_le

/-- Total pair mass: `sum_c pairCount c = n^2`. -/
theorem sum_pairCount (S : Finset G) : ∑ c : G, pairCount S c = S.card ^ 2 := by
  classical
  have h : (S ×ˢ S).card =
      ∑ c ∈ Finset.univ, ((S ×ˢ S).filter fun p : G × G => p.1 + p.2 = c).card :=
    Finset.card_eq_sum_card_fiberwise fun p _ => Finset.mem_univ _
  unfold pairCount
  rw [← h, Finset.card_product]
  ring

/-- Total quadruple mass: `sum_a quadCount a = n^4`. -/
theorem sum_quadCount (S : Finset G) : ∑ a : G, quadCount S a = S.card ^ 4 := by
  classical
  have h : (((S ×ˢ S) ×ˢ (S ×ˢ S)).card) =
      ∑ a ∈ Finset.univ, ((((S ×ˢ S) ×ˢ (S ×ˢ S))).filter
        fun p : (G × G) × (G × G) => p.1.1 + p.1.2 + (p.2.1 + p.2.2) = a).card :=
    Finset.card_eq_sum_card_fiberwise fun p _ => Finset.mem_univ _
  unfold quadCount
  rw [← h, Finset.card_product, Finset.card_product]
  ring

/-- The depth-four fiber over a fixed first-pair sum `c` is a product of two pair fibers. -/
theorem quad_fiber_eq_product (S : Finset G) (a c : G) :
    ((((S ×ˢ S) ×ˢ (S ×ˢ S)).filter
        fun p : (G × G) × (G × G) => p.1.1 + p.1.2 + (p.2.1 + p.2.2) = a).filter
      fun p => p.1.1 + p.1.2 = c) =
    ((S ×ˢ S).filter fun p : G × G => p.1 + p.2 = c) ×ˢ
      ((S ×ˢ S).filter fun p : G × G => p.1 + p.2 = a - c) := by
  classical
  ext p
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, htot⟩, hfst⟩
    refine ⟨⟨h1, hfst⟩, h2, ?_⟩
    rw [← htot, hfst]
    abel
  · rintro ⟨⟨h1, hfst⟩, h2, hsnd⟩
    refine ⟨⟨⟨h1, h2⟩, ?_⟩, hfst⟩
    rw [hfst, hsnd]
    abel

/-- **Convolution identity**: `quadCount a = sum_c pairCount c * pairCount (a - c)`. -/
theorem quadCount_eq_conv (S : Finset G) (a : G) :
    quadCount S a = ∑ c : G, pairCount S c * pairCount S (a - c) := by
  classical
  unfold quadCount
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p : (G × G) × (G × G) => p.1.1 + p.1.2) (t := Finset.univ)
    (fun p _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [quad_fiber_eq_product S a c, Finset.card_product]
  rfl

/-- Reindexing: shifted pair mass equals total pair mass. -/
theorem sum_pairCount_shift (S : Finset G) (a : G) :
    ∑ c : G, pairCount S (a - c) = S.card ^ 2 := by
  classical
  rw [← sum_pairCount S]
  exact Fintype.sum_bijective (fun c => a - c)
    ⟨fun u v huv => by simpa using sub_right_injective huv,
     fun u => ⟨a - u, by abel⟩⟩
    (fun c => pairCount S (a - c)) (pairCount S) (fun c => rfl)

/-- **Fiber bound from pair-sum concentration.**  Every quadruple fiber obeys
`quadCount a <= (M+1) * n^2`: the `c = 0` convolution term pays `n * n` and every
other term is `<= M * pairCount (a-c)`. -/
theorem quadCount_le (S : Finset G) {M : ℕ}
    (hM : ∀ c : G, c ≠ 0 → pairCount S c ≤ M) (a : G) :
    quadCount S a ≤ (M + 1) * S.card ^ 2 := by
  classical
  rw [quadCount_eq_conv]
  have hzero : pairCount S 0 * pairCount S (a - 0) ≤ S.card ^ 2 := by
    calc
      pairCount S 0 * pairCount S (a - 0)
          ≤ S.card * S.card := Nat.mul_le_mul (pairCount_le_card S 0) (pairCount_le_card S _)
      _ = S.card ^ 2 := (sq S.card).symm
  have hrest : ∑ c ∈ Finset.univ.erase (0 : G), pairCount S c * pairCount S (a - c)
      ≤ M * S.card ^ 2 := by
    calc
      ∑ c ∈ Finset.univ.erase (0 : G), pairCount S c * pairCount S (a - c)
          ≤ ∑ c ∈ Finset.univ.erase (0 : G), M * pairCount S (a - c) := by
        refine Finset.sum_le_sum fun c hc => ?_
        exact Nat.mul_le_mul_right _ (hM c (Finset.ne_of_mem_erase hc))
      _ ≤ ∑ c : G, M * pairCount S (a - c) :=
        Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
      _ = M * ∑ c : G, pairCount S (a - c) := by rw [Finset.mul_sum]
      _ = M * S.card ^ 2 := by rw [sum_pairCount_shift]
  calc
    ∑ c : G, pairCount S c * pairCount S (a - c)
        = pairCount S 0 * pairCount S (a - 0) +
          ∑ c ∈ Finset.univ.erase (0 : G), pairCount S c * pairCount S (a - c) :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
    _ ≤ S.card ^ 2 + M * S.card ^ 2 := Nat.add_le_add hzero hrest
    _ = (M + 1) * S.card ^ 2 := by ring

/-- **Depth-four equal-sum universe bound**: `J_4 <= (M+1) * n^6`. -/
theorem equalSumQuadPairs_le (S : Finset G) {M : ℕ}
    (hM : ∀ c : G, c ≠ 0 → pairCount S c ≤ M) :
    equalSumQuadPairs S ≤ (M + 1) * S.card ^ 6 := by
  unfold equalSumQuadPairs
  calc
    ∑ a : G, quadCount S a ^ 2
        ≤ ∑ a : G, ((M + 1) * S.card ^ 2) * quadCount S a := by
      refine Finset.sum_le_sum fun a _ => ?_
      calc
        quadCount S a ^ 2 = quadCount S a * quadCount S a := sq _
        _ ≤ ((M + 1) * S.card ^ 2) * quadCount S a :=
          Nat.mul_le_mul_right _ (quadCount_le S hM a)
    _ = ((M + 1) * S.card ^ 2) * ∑ a : G, quadCount S a := by rw [Finset.mul_sum]
    _ = ((M + 1) * S.card ^ 2) * S.card ^ 4 := by rw [sum_quadCount]
    _ = (M + 1) * S.card ^ 6 := by ring

/-- Factor-5 concentration bounds the depth-four universe at production scale. -/
theorem equalSumQuadPairs_le_of_concentration (S : Finset G)
    (hPSC : PairSumConcentration5 S) (hcard : S.card = 2 ^ 30) :
    equalSumQuadPairs S ≤ (2 ^ 30 / 5 + 1) * (2 ^ 30) ^ 6 := by
  have h := equalSumQuadPairs_le S (M := 2 ^ 30 / 5)
    (fun c hc => by simpa [hcard] using hPSC c hc)
  rwa [hcard] at h

/-- **Production depth-four kernel inequality**: the sharp envelope with
`J = (n/5 + 1) * n^6` fits inside one full Wick budget at `(n, r, s) = (2^30, 110, 4)`. -/
theorem production_depth_four_kernel :
    ((2 ^ 30 / 5 + 1) * (2 ^ 30) ^ 6) * ((4 + 106).choose 4 ^ 2 * ((106)! * (2 ^ 30) ^ 106))
      ≤ Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  decide +kernel

/-
DEFERRED CONSUMER (G86 sharp-envelope weld).  The headline
`production_depth_four_sector_absorbed`, composing `equalSumQuadPairs_le_of_concentration`
and `production_depth_four_kernel` through G86's `sectorMass_le_sharpEnvelope`, was drafted
against `_G86SharpReconstructionIdentity`, which was never landed on this branch.  Importing
that nonexistent module broke the umbrella `ArkLib` build for every lane.  The self-contained
convolution machinery above (fiber count, `quadCount_le`, `equalSumQuadPairs_le`, the
concentration specialization, and the kernel inequality) is axiom-clean and retained.  The
final `sectorMass ≤ Wick budget` weld and G87W's bridge consumer are held out of the build
until the G86 `sectorMass_le_sharpEnvelope` identity is genuinely proved and landed; see the
DISPROOF_LOG entry `[466-G87P-G87W-g86-deferral]`.
-/

end ArkLib.ProximityGap.Frontier.G87DepthFourPairSumReduction

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G87DepthFourPairSumReduction.quadCount_eq_conv
#print axioms
  ArkLib.ProximityGap.Frontier.G87DepthFourPairSumReduction.quadCount_le
#print axioms
  ArkLib.ProximityGap.Frontier.G87DepthFourPairSumReduction.equalSumQuadPairs_le
#print axioms
  ArkLib.ProximityGap.Frontier.G87DepthFourPairSumReduction.equalSumQuadPairs_le_of_concentration
#print axioms
  ArkLib.ProximityGap.Frontier.G87DepthFourPairSumReduction.production_depth_four_kernel
