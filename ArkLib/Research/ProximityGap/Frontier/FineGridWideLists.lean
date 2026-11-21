/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FineGridFirstOrderSecurity

/-! # List sizes at the four wider interpolation radii

The slot certificates behind `FineGridFirstOrderSecurity.four_rates_wide` also bound
lists. No field-size hypothesis is needed beyond the existence of the domain, so the
bounds hold at radii `1269/4096`, `2174/4096`, `2788/4096` and `3201/4096` on every
injective prime-field domain of length `4096 b`.
-/

namespace ProximityGap.FineGridFirstOrderSecurity

open ReedSolomon ReedSolomon.HiddenDerivative CoreDefinitions

/-- A single reference slot count bounds every scalar list on an injective prime-field
domain of any positive integral multiple of the reference length. -/
theorem prime_list_of_slots {p N b k A m M μ h C : ℕ} [Fact p.Prime] (hb : 0 < b)
    (hk : 2 ≤ k) (hkA : k < A) (hAN : A ≤ N) (hμ : μ < N)
    (hcost : firstOrderListWeight k μ M ≤ C*(A-k))
    (hslots : rowSlots N m M μ h < columnSlots k A m M μ h)
    (dom : Fin (b*N) ↪ ZMod p) :
    Code.Lambda (code dom (b*k) : Set (Fin (b*N) → ZMod p)) (1-(A:ℝ)/N) ≤
      ((C*(b*N):ℕ):ℕ∞) := by
  refine list_of_slots hb hk hkA hAN hμ (Or.inr ?_) hcost hslots dom
  simpa [ZMod.ringChar_zmod_n] using Fintype.card_le_of_injective dom dom.injective

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

/-- At the radii certified by the wider line-MCA interpolation, each worst-center scalar
list is bounded by the stated constant times the block length. -/
theorem wide_list_bounds {p b : ℕ} [Fact p.Prime] (hb : 0 < b)
    (dom : Fin (b*4096) ↪ ZMod p) :
    let bounded := fun (k : ℕ) (r : ℝ) (C : ℕ) =>
      Code.Lambda (code dom (b*k) : Set (Fin (b*4096) → ZMod p)) r ≤ ((C*(b*4096):ℕ):ℕ∞)
    bounded 2048 (1269/4096) 1369562863 ∧ bounded 1024 (2174/4096) 649560740 ∧
      bounded 512 (2788/4096) 2486297660 ∧ bounded 256 (3201/4096) 615760719 := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := wide_slot_certificates
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [Nat.cast_ofNat, show (1-(2827:ℝ)/4096) = 1269/4096 by norm_num] using
      prime_list_of_slots (C:=1369562863) hb (by decide) (by decide) (by decide)
        (by decide) (by decide +kernel) h₁ dom
  · simpa only [Nat.cast_ofNat, show (1-(1922:ℝ)/4096) = 2174/4096 by norm_num] using
      prime_list_of_slots (C:=649560740) hb (by decide) (by decide) (by decide)
        (by decide) (by decide +kernel) h₂ dom
  · simpa only [Nat.cast_ofNat, show (1-(1308:ℝ)/4096) = 2788/4096 by norm_num] using
      prime_list_of_slots (C:=2486297660) hb (by decide) (by decide) (by decide)
        (by decide) (by decide +kernel) h₃ dom
  · simpa only [Nat.cast_ofNat, show (1-(895:ℝ)/4096) = 3201/4096 by norm_num] using
      prime_list_of_slots (C:=615760719) hb (by decide) (by decide) (by decide)
        (by decide) (by decide +kernel) h₄ dom

/-- At the radii certified by the wider line-MCA interpolation, each worst-center
interleaved list is bounded by the stated constant times the block length. -/
theorem wide_interleaved_list_bounds {p b : ℕ} [Fact p.Prime] (hb : 0 < b)
    (dom : Fin (b*4096) ↪ ZMod p) (width : ℕ) :
    let bounded := fun (k : ℕ) (r : ℝ) (C : ℕ) =>
      Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
        (code dom (b*k) : Set (Fin (b*4096) → ZMod p))) r ≤ ((C*(b*4096):ℕ):ℕ∞)
    bounded 2048 (1269/4096) 1369562863 ∧ bounded 1024 (2174/4096) 649560740 ∧
      bounded 512 (2788/4096) 2486297660 ∧ bounded 256 (3201/4096) 615760719 := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := wide_slot_certificates
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [Nat.cast_ofNat, show (1-(2827:ℝ)/4096) = 1269/4096 by norm_num] using
      interleaved_list_of_slots (C:=1369562863) hb (by decide) (by decide) (by decide)
        (by decide) (by decide +kernel) h₁ dom width
  · simpa only [Nat.cast_ofNat, show (1-(1922:ℝ)/4096) = 2174/4096 by norm_num] using
      interleaved_list_of_slots (C:=649560740) hb (by decide) (by decide) (by decide)
        (by decide) (by decide +kernel) h₂ dom width
  · simpa only [Nat.cast_ofNat, show (1-(1308:ℝ)/4096) = 2788/4096 by norm_num] using
      interleaved_list_of_slots (C:=2486297660) hb (by decide) (by decide) (by decide)
        (by decide) (by decide +kernel) h₃ dom width
  · simpa only [Nat.cast_ofNat, show (1-(895:ℝ)/4096) = 3201/4096 by norm_num] using
      interleaved_list_of_slots (C:=615760719) hb (by decide) (by decide) (by decide)
        (by decide) (by decide +kernel) h₄ dom width

end ProximityGap.FineGridFirstOrderSecurity

#print axioms ProximityGap.FineGridFirstOrderSecurity.interleaved_list_of_slots
#print axioms ProximityGap.FineGridFirstOrderSecurity.wide_list_bounds
#print axioms ProximityGap.FineGridFirstOrderSecurity.wide_interleaved_list_bounds
