/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyRepBound
import Mathlib.FieldTheory.Perfect

/-!
# RepCountFrobeniusInvariance

Module docstring for `RepCountFrobeniusInvariance.lean`.
-/


open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Frobenius-invariance of the Garcia–Voloch representation count.** For a root-of-unity
subgroup `G = μ_n` of a finite field of characteristic `p`, the additive representation
count is invariant under Frobenius `c ↦ c^p`: `r(c^p) = r(c)`.  Complements the
μ_n-coset-invariance; over an extension field `F_{p^e}` it reduces the GV obligation
`∀ c ≠ 0, r(c) ≤ M` further to one representative per ⟨Frobenius, dilation⟩-orbit. -/
theorem repCount_frobenius_eq {n : ℕ} (G : Finset F)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (p : ℕ) [ExpChar F p] (c : F) :
    repCount G (frobenius F p c) = repCount G c := by
  classical
  have hclosed : ∀ {z : F}, z ∈ G → frobenius F p z ∈ G := by
    intro z hz; rw [hGmem] at hz ⊢; rw [← map_pow, hz, map_one]
  have hclosed' : ∀ {z : F}, z ∈ G → (frobeniusEquiv F p).symm z ∈ G := by
    intro z hz; rw [hGmem] at hz ⊢; rw [← map_pow, hz, map_one]
  have hsc : (frobeniusEquiv F p).symm (frobenius F p c) = c :=
    (frobeniusEquiv F p).symm_apply_apply c
  unfold repCount
  refine Finset.card_nbij' (fun y => (frobeniusEquiv F p).symm y) (fun y => frobenius F p y)
    ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    obtain ⟨hyG, hcy⟩ := hy
    refine ⟨hclosed' hyG, ?_⟩
    have : c - (frobeniusEquiv F p).symm y
        = (frobeniusEquiv F p).symm (frobenius F p c - y) := by rw [map_sub, hsc]
    rw [this]; exact hclosed' hcy
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    obtain ⟨hyG, hcy⟩ := hy
    refine ⟨hclosed hyG, ?_⟩
    have : frobenius F p c - frobenius F p y = frobenius F p (c - y) := (map_sub _ _ _).symm
    rw [this]; exact hclosed hcy
  · intro y _; exact (frobeniusEquiv F p).apply_symm_apply y
  · intro y _; exact (frobeniusEquiv F p).symm_apply_apply y

end ArkLib.ProximityGap.AdditiveEnergyRepBound
