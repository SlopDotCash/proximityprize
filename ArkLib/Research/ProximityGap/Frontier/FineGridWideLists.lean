/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FineGridFirstOrderSecurity

/-! # List sizes at the four wider interpolation radii -/

namespace ProximityGap.FineGridFirstOrderSecurity

open ReedSolomon ReedSolomon.HiddenDerivative CoreDefinitions

/-- A single reference slot count bounds every finite-width list on an injective
prime-field domain of any positive integral multiple of the reference length. -/
theorem interleaved_list_of_slots {p N b k A m M μ h C : ℕ} [Fact p.Prime] (hb : 0 < b)
    (hk : 2 ≤ k) (hkA : k < A) (hAN : A ≤ N) (hμ : μ < N)
    (hcost : firstOrderListWeight k μ M ≤ C*(A-k))
    (hslots : rowSlots N m M μ h < columnSlots k A m M μ h)
    (dom : Fin (b*N) ↪ ZMod p) (width : ℕ) :
    Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
      (code dom (b*k) : Set (Fin (b*N) → ZMod p))) (1-(A:ℝ)/N) ≤ ((C*(b*N):ℕ):ℕ∞) := by
  let φ := algebraMap (ZMod p) (RatFunc (ZMod p))
  have hsize : b*N ≤ p := by simpa using Fintype.card_le_of_injective dom dom.injective
  have hchar : ringChar (RatFunc (ZMod p)) = p := ringChar.eq _ p
  apply (Lambda_interleaved_le_ratFunc dom _ width _).trans
  exact list_of_slots hb hk hkA hAN hμ (Or.inr (hsize.trans_eq hchar.symm))
    hcost hslots (dom.trans ⟨φ,φ.injective⟩)

/-- At the radii certified by the wider line-MCA interpolation, each worst-center
interleaved list is bounded by the stated constant times the block length. -/
theorem wide_interleaved_list_bounds {p b : ℕ} [Fact p.Prime] (hb : 0 < b)
    (dom : Fin (b*4096) ↪ ZMod p) (width : ℕ) :
    let bounded := fun (k : ℕ) (r : ℝ) (C : ℕ) =>
      Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
        (code dom (b*k) : Set (Fin (b*4096) → ZMod p))) r ≤ ((C*(b*4096):ℕ):ℕ∞)
    bounded 2048 (1265/4096) 96741451 ∧ bounded 1024 (2170/4096) 138925816 ∧
      bounded 512 (2783/4096) 25849285 ∧ bounded 256 (3197/4096) 25632097 := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := wide_slot_certificates
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [Nat.cast_ofNat, show (1-(2831:ℝ)/4096) = 1265/4096 by norm_num] using
      interleaved_list_of_slots (C:=96741451) hb (by decide) (by decide) (by decide)
        (by decide) (by decide +kernel) h₁ dom width
  · simpa only [Nat.cast_ofNat, show (1-(1926:ℝ)/4096) = 2170/4096 by norm_num] using
      interleaved_list_of_slots (C:=138925816) hb (by decide) (by decide) (by decide)
        (by decide) (by decide +kernel) h₂ dom width
  · simpa only [Nat.cast_ofNat, show (1-(1313:ℝ)/4096) = 2783/4096 by norm_num] using
      interleaved_list_of_slots (C:=25849285) hb (by decide) (by decide) (by decide)
        (by decide) (by decide +kernel) h₃ dom width
  · simpa only [Nat.cast_ofNat, show (1-(899:ℝ)/4096) = 3197/4096 by norm_num] using
      interleaved_list_of_slots (C:=25632097) hb (by decide) (by decide) (by decide)
        (by decide) (by decide +kernel) h₄ dom width

end ProximityGap.FineGridFirstOrderSecurity

#print axioms ProximityGap.FineGridFirstOrderSecurity.interleaved_list_of_slots
#print axioms ProximityGap.FineGridFirstOrderSecurity.wide_interleaved_list_bounds
