/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneralKMultiplicity

/-!
# The boundary-slice EXACT law (#371): the bad set as a residual-ratio image

At the boundary radius (`k < (1−δ)·n ≤ k+1`: witnesses are exactly the
`(k+1)`-point sets) and for **strongly far** directions (max codeword agreement
≤ `k` — the probe-measured threshold extremizers), the bad-scalar set is computed
EXACTLY:

  **`badSet = { −e_t(u₀)/e_t(u₁) : t an injective (k+1)-tuple }`**

— both inclusions.  `⊇`: each tuple's ratio makes the line-residual vanish, the
extension explains the line on the tuple (a valid witness at this radius), and
strong farness kills every joint.  `⊆`: every bad witness contains an injective
`(k+1)`-tuple, whose direction-residual is nonzero (strong farness again), pinning
the scalar to that tuple's ratio.

This is the first exact `ε_mca` formula above Johnson for a full stack class —
covering the measured `C(8,3) = 56 > 40 = spectrum` threshold instance: the count
is the number of DISTINCT residual ratios, a Vandermonde-determinant image-size
question over the smooth domain, where the census/quartet machinery operates.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **THE BOUNDARY-SLICE EXACT LAW**: at the boundary radius and for strongly far
directions, the bad set IS the residual-ratio image. -/
theorem boundary_slice_badSet_eq (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    {u₀ u₁ : Fin n → F}
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ k) :
    Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)
      = (Finset.univ.filter
          (fun t : Fin (k+1) → Fin n => Function.Injective t)).image
        (fun t => -(residual dom k t u₀) / residual dom k t u₁) := by
  -- strong farness: every injective tuple has nonzero direction residual
  have hallres : ∀ t : Fin (k+1) → Fin n, Function.Injective t →
      residual dom k t u₁ ≠ 0 := by
    intro t htinj hres
    obtain ⟨c, hcC, hcag⟩ := extension_of_residual_eq_zero dom t htinj hres
    have hsub : Finset.univ.image t ⊆ agreeSet c u₁ := by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hcag a⟩
    have hcard : k + 1 ≤ (agreeSet c u₁).card := by
      calc k + 1 = (Finset.univ.image t).card := by
            rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
              Fintype.card_fin]
        _ ≤ _ := Finset.card_le_card hsub
    have := hμ c hcC
    omega
  ext γ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · -- ⊆ : a bad witness contains an injective tuple pinning the scalar
    rintro ⟨S, hsz, ⟨c, hcC, hag⟩, -⟩
    have hScard : k + 1 ≤ S.card := by
      have h1 : ((k : ℝ≥0)) < (S.card : ℝ≥0) := lt_of_lt_of_le hlo hsz
      have h2 : k < S.card := by exact_mod_cast h1
      omega
    obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq hScard
    -- enumerate S' as an injective tuple
    set t : Fin (k+1) → Fin n :=
      fun a => (S'.equivFin.symm (Fin.cast hS'card.symm a) : Fin n) with ht
    have htinj : Function.Injective t := by
      intro a b hab
      have h1 : (S'.equivFin.symm (Fin.cast hS'card.symm a))
          = S'.equivFin.symm (Fin.cast hS'card.symm b) := Subtype.ext hab
      have h2 := S'.equivFin.symm.injective h1
      exact Fin.cast_injective _ h2
    have htmem : ∀ a, t a ∈ S := fun a =>
      hS'sub (S'.equivFin.symm (Fin.cast hS'card.symm a)).2
    -- the line residual vanishes on t
    obtain ⟨P, hPdeg, rfl⟩ := hcC
    have hPdeg' : P.natDegree < k := by
      by_cases hP0 : P = 0
      · subst hP0
        simpa using hk
      · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
    have hlinezero : residual dom k t (fun i => u₀ i + γ * u₁ i) = 0 := by
      refine residual_eq_zero_of_extends dom k t hPdeg' fun a => ?_
      have := hag (t a) (htmem a)
      simpa [smul_eq_mul] using this.symm
    rw [residual_line] at hlinezero
    refine ⟨t, htinj, ?_⟩
    exact (gamma_eq_of_owned dom k t (hallres t htinj) hlinezero).symm
  · -- ⊇ : every tuple's ratio is bad
    rintro ⟨t, htinj, rfl⟩
    have hres1 := hallres t htinj
    set γ := -(residual dom k t u₀) / residual dom k t u₁ with hγ
    -- the line residual vanishes at γ
    have hlinezero : residual dom k t (fun i => u₀ i + γ * u₁ i) = 0 := by
      rw [residual_line, hγ]
      field_simp
      ring
    -- hence the line extends on the tuple
    obtain ⟨c, hcC, hcag⟩ := extension_of_residual_eq_zero dom t htinj hlinezero
    refine ⟨Finset.univ.image t, ?_, ⟨c, hcC, ?_⟩, ?_⟩
    · -- witness size
      have hcard : (Finset.univ.image t).card = k + 1 := by
        rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
          Fintype.card_fin]
      rw [hcard]
      exact_mod_cast hhi
    · -- the line agreement
      intro i hi
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hi
      have h := hcag a
      show c (t a) = u₀ (t a) + γ • u₁ (t a)
      rw [smul_eq_mul]
      exact h
    · -- no joint: v₁ would agree with u₁ on k+1 points
      rintro ⟨v₀, hv₀, v₁, hv₁, hagj⟩
      have hsub : Finset.univ.image t ⊆ agreeSet v₁ u₁ := by
        intro x hx
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
        rw [agreeSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (hagj (t a) (Finset.mem_image_of_mem t
          (Finset.mem_univ a))).2⟩
      have hcard : k + 1 ≤ (agreeSet v₁ u₁).card := by
        calc k + 1 = (Finset.univ.image t).card := by
              rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
                Fintype.card_fin]
          _ ≤ _ := Finset.card_le_card hsub
      have := hμ v₁ hv₁
      omega

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.boundary_slice_badSet_eq
