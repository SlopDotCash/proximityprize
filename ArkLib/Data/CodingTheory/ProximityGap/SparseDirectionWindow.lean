/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS

/-!
# The sparse-direction window bound (#371): the last k = 1 class

The window decomposition's remaining class: directions that ARE sparse error
patterns (`|supp ε| ≤ e`).  At `k = 1` (constant codewords) the analysis closes by
the popularity argument:

* a bad witness must HIT the support (else the joint pair `(c, 0)` explains);
* off the support the explaining constant equals `u₀`, so it is an
  `(n−w−e)`-**popular** value of `u₀` — and there are at most `n/(n−w−e)` of those;
* at a hit point the scalar is DETERMINED: `γ = (c − u₀ i)/ε i`.

Hence  **`#bad · (n−w−e) ≤ n·e`** — unconditional, valid at every radius with
`n − w − e > 0`, in particular throughout the window.  Combined with the
multiplicity theorem (genuine rational directions) and WB-3b (polynomial
directions), the `k = 1` window now carries an unconditional `O(n²/(n−2w))/q`
mass bound across ALL direction classes.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- Constant words are the `k = 1` codewords. -/
theorem const_mem_rsCode_one (dom : Fin n ↪ F) (a : F) :
    (fun _ : Fin n => a) ∈ (rsCode dom 1 : Submodule F (Fin n → F)) := by
  refine ⟨C a, ?_, ?_⟩
  · calc (C a).degree ≤ 0 := degree_C_le
      _ < 1 := by norm_num
  · funext i
    rw [eval_C]

/-- `k = 1` codewords are constant. -/
theorem rsCode_one_const (dom : Fin n ↪ F) {c : Fin n → F}
    (hc : c ∈ (rsCode dom 1 : Submodule F (Fin n → F))) :
    ∃ a : F, c = fun _ => a := by
  obtain ⟨P, hPdeg, rfl⟩ := hc
  refine ⟨P.coeff 0, ?_⟩
  funext i
  rw [Polynomial.eval_eq_sum_range' (n := 1) ?_, Finset.sum_range_one, pow_zero,
    mul_one]
  by_cases hP0 : P = 0
  · subst hP0
    simp
  · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg

open Classical in
/-- **THE SPARSE-DIRECTION WINDOW BOUND** (`k = 1`): for a direction supported on
`≤ e` positions, at every radius `δ ≤ w/n`:

  `#bad · (n − w − e) ≤ n · e`. -/
theorem sparse_direction_badScalars_card_le (dom : Fin n ↪ F)
    {w e : ℕ} {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {u₀ ε : Fin n → F}
    (hsupp : (Finset.univ.filter (fun i => ε i ≠ 0)).card ≤ e) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ ε γ)).card
      * (n - w - e) ≤ n * e := by
  set supp := Finset.univ.filter (fun i => ε i ≠ 0) with hsuppdef
  set m := n - w - e with hm
  -- the popular values of u₀
  set popular := Finset.univ.filter
    (fun v : F => m ≤ (Finset.univ.filter (fun i => u₀ i = v)).card) with hpop
  -- popularity count: #popular · m ≤ n
  have hpopcount : popular.card * m ≤ n := by
    have hfib : ∑ v ∈ popular, (Finset.univ.filter (fun i => u₀ i = v)).card
        ≤ n := by
      calc ∑ v ∈ popular, (Finset.univ.filter (fun i => u₀ i = v)).card
          ≤ ∑ v : F, (Finset.univ.filter (fun i => u₀ i = v)).card :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = (Finset.univ : Finset (Fin n)).card :=
            (Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (u₀ i))).symm
        _ = n := by rw [Finset.card_univ, Fintype.card_fin]
    calc popular.card * m = ∑ _v ∈ popular, m := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ v ∈ popular, (Finset.univ.filter (fun i => u₀ i = v)).card :=
          Finset.sum_le_sum fun v hv => (Finset.mem_filter.mp hv).2
      _ ≤ n := hfib
  -- every bad scalar maps to a (popular value, support point) pair
  set f : F × Fin n → F := fun p => (p.1 - u₀ p.2) / ε p.2 with hf
  have hsub : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ ε γ))
      ⊆ (popular ×ˢ supp).image f := by
    intro γ hγ
    obtain ⟨S, hsz, ⟨c, hcC, hag⟩, hno⟩ := (Finset.mem_filter.mp hγ).2
    obtain ⟨a, rfl⟩ := rsCode_one_const dom hcC
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
    -- the witness hits the support (else the joint pair (a, 0) explains)
    have hhit : ∃ i ∈ S, ε i ≠ 0 := by
      by_contra hmiss
      push Not at hmiss
      refine hno ⟨(fun _ => a), const_mem_rsCode_one dom a,
        0, (rsCode dom 1 : Submodule F (Fin n → F)).zero_mem, fun i hi => ?_⟩
      have hεi := hmiss i hi
      have hline := hag i hi
      simp only [smul_eq_mul] at hline
      rw [hεi, mul_zero, add_zero] at hline
      exact ⟨hline.symm ▸ rfl, by simp [hεi]⟩
    obtain ⟨i₀, hi₀S, hεi₀⟩ := hhit
    -- the constant is popular: a = u₀ on S off the support
    have hapop : a ∈ popular := by
      rw [hpop, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hsub2 : S \ supp ⊆ Finset.univ.filter (fun i => u₀ i = a) := by
        intro i hi
        obtain ⟨hiS, hins⟩ := Finset.mem_sdiff.mp hi
        rw [hsuppdef, Finset.mem_filter] at hins
        have hεz : ε i = 0 := by
          by_contra hne
          exact hins ⟨Finset.mem_univ _, hne⟩
        have hline := hag i hiS
        simp only [smul_eq_mul] at hline
        rw [hεz, mul_zero, add_zero] at hline
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hline.symm⟩
      calc m = n - w - e := hm
        _ ≤ S.card - supp.card := by
            have := hsupp
            omega
        _ ≤ (S \ supp).card := Finset.le_card_sdiff _ _
        _ ≤ _ := Finset.card_le_card hsub2
    -- the scalar is determined at the hit
    refine Finset.mem_image.mpr ⟨(a, i₀), ?_, ?_⟩
    · rw [Finset.mem_product]
      exact ⟨hapop, by rw [hsuppdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hεi₀⟩⟩
    · have hline : a = u₀ i₀ + γ * ε i₀ := by
        have := hag i₀ hi₀S
        simpa [smul_eq_mul] using this
      rw [hf]
      show (a - u₀ i₀) / ε i₀ = γ
      rw [div_eq_iff hεi₀]
      linear_combination hline
  calc (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ ε γ)).card
        * (n - w - e)
      ≤ ((popular ×ˢ supp).image f).card * (n - w - e) :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ (popular.card * supp.card) * (n - w - e) := by
        refine Nat.mul_le_mul_right _ ?_
        calc ((popular ×ˢ supp).image f).card ≤ (popular ×ˢ supp).card :=
              Finset.card_image_le
          _ = popular.card * supp.card := Finset.card_product _ _
    _ ≤ (popular.card * e) * m := by
        rw [hm]
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hsupp) (le_refl _)
    _ = (popular.card * m) * e := by ring
    _ ≤ n * e := Nat.mul_le_mul_right _ hpopcount

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.const_mem_rsCode_one
#print axioms ProximityGap.Ownership.rsCode_one_const
#print axioms ProximityGap.Ownership.sparse_direction_badScalars_card_le
