/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PopularCodewords

/-!
# The general-k sparse-direction bound (#371)

The `k = 1` sparse bound lifted through the proven packing: for a direction
supported on ≤ `e` positions, at every radius `δ ≤ w/n` and every rate,

  **`#bad · (m+1−k)^k ≤ n^k · e`**,  `m := n − w − e`.

The argument is the `k = 1` template verbatim with the popularity fiber count
replaced by the packing bound: a bad witness must hit the support (else the joint
pair `(P, 0)` explains); off the support the explaining codeword agrees with `u₀`
on ≥ `m` positions — a *popular* codeword, of which there are at most
`n^k/(m+1−k)^k`; and at a hit point the scalar is determined.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The general-k sparse-direction bound**: `#bad · (n−w−e+1−k)^k ≤ n^k · e`. -/
theorem sparse_direction_badScalars_card_le_generalK (dom : Fin n ↪ F) {k : ℕ}
    {w e : ℕ} {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hmk : k ≤ n - w - e)
    {u₀ ε : Fin n → F}
    (hsupp : (Finset.univ.filter (fun i => ε i ≠ 0)).card ≤ e) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ ε γ)).card
      * ((n - w - e) + 1 - k) ^ k ≤ n ^ k * e := by
  set supp := Finset.univ.filter (fun i => ε i ≠ 0) with hsuppdef
  set m := n - w - e with hm
  set pop := Finset.univ.filter (fun c : Fin n → F =>
    c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧ m ≤ (agreeSet c u₀).card)
    with hpop
  set f : (Fin n → F) × Fin n → F := fun p => (p.1 p.2 - u₀ p.2) / ε p.2 with hf
  -- every bad scalar maps to a (popular codeword, support point) pair
  have hsub : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ ε γ))
      ⊆ (pop ×ˢ supp).image f := by
    intro γ hγ
    obtain ⟨S, hsz, ⟨c, hcC, hag⟩, hno⟩ := (Finset.mem_filter.mp hγ).2
    -- witness size: n − w ≤ |S|
    have hS : n - w ≤ S.card := by
      have h2 : ((n - w : ℕ) : ℝ≥0) ≤ (S.card : ℝ≥0) := by
        have hcardn : (Fintype.card (Fin n) : ℝ≥0) = (n : ℝ≥0) := by
          rw [Fintype.card_fin]
        calc ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := by rw [Nat.cast_tsub]
          _ ≤ (n : ℝ≥0) - δ * (Fintype.card (Fin n) : ℝ≥0) := by
              exact tsub_le_tsub_left (by rw [hcardn] at hδn ⊢; exact hδn) _
          _ = (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) := by
              rw [tsub_mul, one_mul, hcardn]
          _ ≤ (S.card : ℝ≥0) := hsz
      exact_mod_cast h2
    -- the witness hits the support
    have hhit : ∃ i ∈ S, ε i ≠ 0 := by
      by_contra hmiss
      push Not at hmiss
      refine hno ⟨c, hcC,
        0, (rsCode dom k : Submodule F (Fin n → F)).zero_mem, fun i hi => ?_⟩
      have hεi := hmiss i hi
      have hline := hag i hi
      simp only [smul_eq_mul] at hline
      rw [hεi, mul_zero, add_zero] at hline
      exact ⟨hline, by simp [hεi]⟩
    obtain ⟨i₀, hi₀S, hεi₀⟩ := hhit
    -- the codeword is popular: c = u₀ on S off the support
    have hcpop : c ∈ pop := by
      rw [hpop, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hcC, ?_⟩
      have hsub2 : S \ supp ⊆ agreeSet c u₀ := by
        intro i hi
        obtain ⟨hiS, hins⟩ := Finset.mem_sdiff.mp hi
        rw [hsuppdef, Finset.mem_filter] at hins
        have hεz : ε i = 0 := by
          by_contra hne
          exact hins ⟨Finset.mem_univ _, hne⟩
        have hline := hag i hiS
        simp only [smul_eq_mul] at hline
        rw [hεz, mul_zero, add_zero] at hline
        rw [agreeSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hline⟩
      calc m = n - w - e := hm
        _ ≤ S.card - supp.card := by
            have := hsupp
            omega
        _ ≤ (S \ supp).card := Finset.le_card_sdiff _ _
        _ ≤ _ := Finset.card_le_card hsub2
    -- the scalar is determined at the hit
    refine Finset.mem_image.mpr ⟨(c, i₀), ?_, ?_⟩
    · rw [Finset.mem_product]
      refine ⟨hcpop, ?_⟩
      rw [hsuppdef, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hεi₀⟩
    · have hline : c i₀ = u₀ i₀ + γ * ε i₀ := by
        have := hag i₀ hi₀S
        simpa [smul_eq_mul] using this
      rw [hf]
      show (c i₀ - u₀ i₀) / ε i₀ = γ
      rw [div_eq_iff hεi₀]
      linear_combination hline
  -- the count
  calc (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ ε γ)).card
        * ((n - w - e) + 1 - k) ^ k
      ≤ ((pop ×ˢ supp).image f).card * ((n - w - e) + 1 - k) ^ k :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ (pop.card * supp.card) * (m + 1 - k) ^ k := by
        rw [hm]
        refine Nat.mul_le_mul_right _ ?_
        calc ((pop ×ˢ supp).image f).card ≤ (pop ×ˢ supp).card :=
              Finset.card_image_le
          _ = pop.card * supp.card := Finset.card_product _ _
    _ = (pop.card * (m + 1 - k) ^ k) * supp.card := by ring
    _ ≤ n ^ k * supp.card := by
        refine Nat.mul_le_mul_right _ ?_
        exact popular_codewords_card_mul_le dom k u₀ m (by omega)
    _ ≤ n ^ k * e := Nat.mul_le_mul_left _ hsupp

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.sparse_direction_badScalars_card_le_generalK
