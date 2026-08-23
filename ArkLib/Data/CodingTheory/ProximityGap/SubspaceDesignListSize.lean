/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.SubspaceDesignListDim
import ArkLib.Data.CodingTheory.ProximityGap.AffineSubspaceCardBound


/-!
# The subspace-design list-size bound (B2 list decoding) (#389, #334)

The explicit list-size theorem from a subspace design — the Guruswami–Xing list-decoding bound,
assembling the producer ingredients landed in this session.

`subspaceDesign_list_card_le`: for a `τ`-subspace design `C`, the list `L` of codewords agreeing
with a word `y` on `≥ a` coordinates has `|L| ≤ |F|^{r−1}` whenever `τ(r)·n + r·n < (r+1)·a`.

Proof: confine and count.  `subspaceDesign_list_dim_bound` shows no `r+1` of the list have
linearly independent differences, so a basis extraction (`exists_linearIndependent`) caps the
dimension of the span `W` of the differences at `r−1` (an independent `r`-subset would rebuild
`r+1` codewords with independent differences, contradiction).  Then `L ⊆ c₀ + W` and
`card_le_pow_finrank_of_sub_mem` give `|L| ≤ |F|^{dim W} ≤ |F|^{r−1}`.

This is the list-size half of the curve-decodability producer: it bounds the number of close
codewords for the explicit subspace-design code.  The remaining producer step is the
interpolation/`CurveDecodable` assembly (GG25 §4.3) and the explicit FRS τ-parameters at window `δ`.
Axiom-clean.
-/
open Finset CodingTheory

namespace ProximityGap

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The subspace-design list-size bound.**  For a `τ`-subspace design `C`, the list of codewords
agreeing with a word `y` on `≥ a` coordinates has size `≤ |F|^{r−1}` whenever
`τ(r)·n + r·n < (r+1)·a`.  The list-dimension bound (`subspaceDesign_list_dim_bound`) confines the
list to a subspace of dimension `< r`; the cardinality bound (`card_le_pow_finrank_of_sub_mem`)
counts it.  Combining via a basis extraction (`exists_linearIndependent`): if the span of the
differences had dimension `≥ r`, an independent `r`-subset would give `r+1` codewords with
independent differences, contradicting the dimension bound. -/
theorem subspaceDesign_list_card_le {s : ℕ} {τ : ℕ → ℝ}
    {C : Submodule F (ι → Fin s → F)} (h : IsSubspaceDesign s τ C)
    {r : ℕ} (hr : 1 ≤ r) (y : ι → Fin s → F) {a : ℕ}
    (L : Finset (ι → Fin s → F)) (hLC : ∀ c ∈ L, c ∈ C)
    (hLa : ∀ c ∈ L, a ≤ (univ.filter (fun i => c i = y i)).card)
    (hbig : τ r * Fintype.card ι + r * Fintype.card ι < (r + 1) * a) :
    L.card ≤ Fintype.card F ^ (r - 1) := by
  classical
  rcases L.eq_empty_or_nonempty with rfl | ⟨c0, hc0⟩
  · simp
  set imgSet : Set (ι → Fin s → F) := (fun c => c - c0) '' (L : Set (ι → Fin s → F)) with himg
  set W := Submodule.span F imgSet with hW
  have hsub : ∀ c ∈ L, c - c0 ∈ W := fun c hc => Submodule.subset_span ⟨c, hc, rfl⟩
  have hfin : Module.finrank F W ≤ r - 1 := by
    by_contra hcon
    rw [not_le] at hcon
    have hge : r ≤ Module.finrank F W := by omega
    obtain ⟨b, hbsub, hbspan, hbind⟩ := exists_linearIndependent F imgSet
    haveI : Fintype ↥imgSet := (Set.toFinite imgSet).fintype
    haveI : Fintype ↥b := (Set.Finite.subset (Set.toFinite imgSet) hbsub).fintype
    have hWb : W = Submodule.span F b := by rw [hW, ← hbspan]
    have hbcard : Module.finrank F W = b.toFinset.card := by
      rw [hWb, finrank_span_set_eq_card hbind]
    rw [hbcard] at hge
    obtain ⟨t', ht'sub, ht'card⟩ := Finset.exists_subset_card_eq hge
    -- `t'` : `r` independent differences
    have ht'subb : (↑t' : Set (ι → Fin s → F)) ⊆ b := fun x hx => by
      have := ht'sub (Finset.mem_coe.mp hx); rwa [Set.mem_toFinset] at this
    have ht'ind : LinearIndependent F ((↑) : ↥t' → (ι → Fin s → F)) := by
      have hbind' : LinearIndepOn F id b := hbind
      exact hbind'.mono ht'subb
    -- each element of `t'` is `c − c0` for a codeword `c ∈ L`
    have hpre : ∀ x ∈ t', ∃ c ∈ L, c - c0 = x := by
      intro x hx
      have : x ∈ imgSet := hbsub (ht'subb (Finset.mem_coe.mpr hx))
      rwa [himg, Set.mem_image] at this
    choose cw hcwL hcwdiff using hpre
    set e : Fin r ≃ ↥t' := (t'.equivFinOfCardEq ht'card).symm with he
    set cf : Fin (r + 1) → (ι → Fin s → F) :=
      Fin.cons c0 (fun j : Fin r => cw (e j) (e j).2) with hcf
    have hcf0 : cf 0 = c0 := by rw [hcf, Fin.cons_zero]
    have hcfsucc : ∀ i : Fin r, cf i.succ = cw (e i) (e i).2 := by
      intro i; rw [hcf, Fin.cons_succ]
    have hcfC : ∀ j, cf j ∈ C := by
      intro j
      refine Fin.cases ?_ ?_ j
      · rw [hcf0]; exact hLC c0 hc0
      · intro i; rw [hcfsucc]; exact hLC _ (hcwL _ _)
    have hcfa : ∀ j, a ≤ (univ.filter (fun i => cf j i = y i)).card := by
      intro j
      refine Fin.cases ?_ ?_ j
      · rw [hcf0]; exact hLa c0 hc0
      · intro i; rw [hcfsucc]; exact hLa _ (hcwL _ _)
    refine subspaceDesign_list_dim_bound h hr cf hcfC y hcfa hbig ?_
    have heq : (fun j : Fin r => cf j.succ - cf 0) = fun j => ((e j : (ι → Fin s → F))) := by
      funext j
      rw [hcf0, hcfsucc, hcwdiff]
    rw [heq]
    exact ht'ind.comp e e.injective
  calc L.card ≤ Fintype.card F ^ Module.finrank F W :=
        card_le_pow_finrank_of_sub_mem W c0 L hsub
    _ ≤ Fintype.card F ^ (r - 1) :=
        Nat.pow_le_pow_right Fintype.card_pos hfin

end ProximityGap
