/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.GG25ExactPreservation
import ArkLib.Data.CodingTheory.ProximityGap.SubspaceAvoidance

/-!
# The field-size-weighted curve-decodability transfer (issue #334, K5, brick 6)

[Jo26] (ePrint 2026/891) **Theorem 5.8**: if `C` is marked `(ℓ, δ, a, b₀)`-curve-decodable
(`1 ≤ b ≤ b₀ ≤ a ≤ q`) and

  `C(a,b) · (q^{s−1} − 1) < C(b₀,b) · (q^s − 1)`

(the paper's `C(b₀,b)/C(a,b) > (q^{s−1}−1)/(q^s−1)` cleared of denominators), then `C^{≡s}` is
marked `(ℓ, δ, a, b)`-curve-decodable. The mechanism shares everything with Theorem 5.7
(`GG25ExactPreservation.lean`) except the final counting: instead of the covering lemma, an
**incidence double count** — each nonzero `λ` is incident to at least `C(b₀, b)` of the `V_T`
(every `b`-subset of its `b₀`-sized explained set works), while under failure every proper
`V_T` holds at most `q^{s−1} − 1` nonzero vectors (`SubspaceAvoidance`'s cardinality bound).
-/

open Finset
open scoped NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

set_option maxHeartbeats 1000000 in
/-- **[Jo26] Theorem 5.8 (field-size-weighted curve-decodability transfer).** If `C` is
**marked** `(ℓ, δ, a, b₀)`-curve-decodable, `1 ≤ b ≤ b₀`, and

  `C(a,b) · (q^{s−1} − 1) < C(b₀,b) · (q^s − 1)`,

then `C^{≡s}` is marked `(ℓ, δ, a, b)`-curve-decodable (over `rowwiseCode`; convert with
`rowwiseCode_eq_interleave`). -/
theorem markedCurveDecodable_interleaved_weighted
    (C : Submodule F (ι → A)) {ℓ s : ℕ} {δ : ℝ≥0} {a b b₀ : ℕ}
    (hb : 1 ≤ b) (hbb : b ≤ b₀)
    (hmarked : MarkedCurveDecodable (F := F) (C : Set (ι → A)) ℓ δ a b₀)
    (hweight : a.choose b * (Fintype.card F ^ (s - 1) - 1)
      < b₀.choose b * (Fintype.card F ^ s - 1)) :
    MarkedCurveDecodable (F := F) (rowwiseCode (C : Set (ι → A)) s) ℓ δ a b := by
  classical
  intro U f hf A₀ hcard hδ
  by_contra hfail
  push Not at hfail
  -- Every V_T is proper under failure.
  have hproper : ∀ {B : Finset F}, B ∈ A₀.powersetCard b →
      (curveExplainSubmodule C (ℓ := ℓ) f B) ≠ ⊤ := fun {B} hB =>
    curveExplainSubmodule_ne_top_of_no_witness (a := a) (U := U) C hfail (B := B) hB
  -- Per-λ incidence: every nonzero λ lies in V_T for at least C(b₀, b) of the T's.
  have hincLB : ∀ lam : Fin s → F,
      b₀.choose b ≤ ((A₀.powersetCard b).filter
        (fun B => lam ∈ curveExplainSubmodule C (ℓ := ℓ) f B)).card := by
    intro lam
    -- The marked base property at the projected instance.
    have hδ' : ∀ α ∈ A₀,
        (δᵣ( (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) •
            rowCombine (A := A) lam (U j) i),
          rowCombine (A := A) lam (f α) ) : ℝ≥0) ≤ δ := by
      intro α hα
      refine le_trans ?_ (hδ α hα)
      have hpt : (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) •
            rowCombine (A := A) lam (U j) i)
          = rowCombine (A := A) lam
            (fun i k => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • U j i k) := by
        funext i
        unfold rowCombine
        calc ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • ∑ k, lam k • U j i k
            = ∑ j : Fin (ℓ + 1), ∑ k, α ^ (j : ℕ) • (lam k • U j i k) :=
              Finset.sum_congr rfl fun j _ => Finset.smul_sum
          _ = ∑ k, ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • (lam k • U j i k) := Finset.sum_comm
          _ = ∑ k, lam k • ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • U j i k := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.smul_sum]
              exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
      have hcurve : (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • U j i)
          = (fun i k => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • U j i k) := by
        funext i k
        rw [Finset.sum_apply]
        exact Finset.sum_congr rfl fun j _ => rfl
      rw [hpt, hcurve]
      exact_mod_cast relHammingDist_rowCombine_le lam _ _
    have hfC' : ∀ α, rowCombine (A := A) lam (f α) ∈ (C : Set (ι → A)) := by
      intro α
      rw [rowCombine_eq_sum_rows]
      exact Submodule.sum_mem _ fun k _ => C.smul_mem _ (hf α k)
    obtain ⟨h, hhC, hcount⟩ := hmarked
      (fun j => rowCombine (A := A) lam (U j))
      (fun α => rowCombine (A := A) lam (f α)) hfC' A₀ hcard hδ'
    set S := A₀.filter (fun α => rowCombine (A := A) lam (f α)
      = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • h j i) with hS
    -- Every b-subset of S certifies λ ∈ V_T.
    have hmono : S.powersetCard b ⊆ (A₀.powersetCard b).filter
        (fun B => lam ∈ curveExplainSubmodule C (ℓ := ℓ) f B) := by
      intro T hT
      rw [Finset.mem_powersetCard] at hT
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨hT.1.trans (Finset.filter_subset _ _), hT.2⟩, h, hhC, fun α hα => ?_⟩
      have := hT.1 hα
      rw [hS, Finset.mem_filter] at this
      exact this.2
    calc b₀.choose b ≤ S.card.choose b := Nat.choose_le_choose b hcount
    _ = (S.powersetCard b).card := (Finset.card_powersetCard b S).symm
    _ ≤ _ := Finset.card_le_card hmono
  -- Per-T incidence: a proper V_T holds at most q^{s−1} − 1 nonzero vectors.
  have hincUB : ∀ B ∈ A₀.powersetCard b,
      ((Finset.univ.filter (fun lam : Fin s → F => lam ≠ 0)).filter
        (fun lam => lam ∈ curveExplainSubmodule C (ℓ := ℓ) f B)).card
      ≤ Fintype.card F ^ (s - 1) - 1 := by
    intro B hB
    have hssub : (Finset.univ.filter (fun lam : Fin s → F => lam ≠ 0)).filter
        (fun lam => lam ∈ curveExplainSubmodule C (ℓ := ℓ) f B)
        ⊂ Finset.univ.filter
          (fun lam : Fin s → F => lam ∈ curveExplainSubmodule C (ℓ := ℓ) f B) := by
      constructor
      · intro x hx
        rw [Finset.mem_filter] at hx ⊢
        rw [Finset.mem_filter] at hx
        exact ⟨Finset.mem_univ _, hx.2⟩
      · intro hsub
        have h0 : (0 : Fin s → F) ∈ Finset.univ.filter
            (fun lam : Fin s → F => lam ∈ curveExplainSubmodule C (ℓ := ℓ) f B) := by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, (curveExplainSubmodule C f B).zero_mem⟩
        have := hsub h0
        rw [Finset.mem_filter, Finset.mem_filter] at this
        exact this.1.2 rfl
    have hlt := Finset.card_lt_card hssub
    have hKcard : (Finset.univ.filter
        (fun lam : Fin s → F => lam ∈ curveExplainSubmodule C (ℓ := ℓ) f B)).card
        ≤ Fintype.card F ^ (s - 1) := by
      have := SubspaceAvoidance.card_le_pow_finrank_pred_of_ne_top
        (curveExplainSubmodule C (ℓ := ℓ) f B) (hproper hB)
      rw [Nat.card_eq_fintype_card] at this
      calc _ = Fintype.card ↥(curveExplainSubmodule C (ℓ := ℓ) f B) :=
            (Fintype.card_subtype _).symm
      _ ≤ _ := this
    omega
  -- The incidence double count.
  set NZ := Finset.univ.filter (fun lam : Fin s → F => lam ≠ 0) with hNZ
  have hNZcard : NZ.card = Fintype.card F ^ s - 1 := by
    rw [hNZ, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    congr 1
    rw [Fintype.card_fun, Fintype.card_fin]
  have hdouble : ∑ lam ∈ NZ, ((A₀.powersetCard b).filter
        (fun B => lam ∈ curveExplainSubmodule C (ℓ := ℓ) f B)).card
      = ∑ B ∈ A₀.powersetCard b, (NZ.filter
        (fun lam => lam ∈ curveExplainSubmodule C (ℓ := ℓ) f B)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have hLB : NZ.card * b₀.choose b ≤ ∑ lam ∈ NZ, ((A₀.powersetCard b).filter
      (fun B => lam ∈ curveExplainSubmodule C (ℓ := ℓ) f B)).card := by
    calc NZ.card * b₀.choose b = ∑ _lam ∈ NZ, b₀.choose b := by
          rw [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum fun lam _ => hincLB lam
  have hUB : ∑ B ∈ A₀.powersetCard b, (NZ.filter
      (fun lam => lam ∈ curveExplainSubmodule C (ℓ := ℓ) f B)).card
      ≤ a.choose b * (Fintype.card F ^ (s - 1) - 1) := by
    calc _ ≤ ∑ _B ∈ A₀.powersetCard b, (Fintype.card F ^ (s - 1) - 1) :=
          Finset.sum_le_sum fun B hB => hincUB B hB
    _ = (A₀.powersetCard b).card * (Fintype.card F ^ (s - 1) - 1) := by
          rw [Finset.sum_const, smul_eq_mul]
    _ = a.choose b * (Fintype.card F ^ (s - 1) - 1) := by
          rw [Finset.card_powersetCard, hcard]
  -- Assemble the contradiction with the weight hypothesis.
  have : (Fintype.card F ^ s - 1) * b₀.choose b
      ≤ a.choose b * (Fintype.card F ^ (s - 1) - 1) := by
    calc (Fintype.card F ^ s - 1) * b₀.choose b = NZ.card * b₀.choose b := by rw [hNZcard]
    _ ≤ _ := hLB
    _ = _ := hdouble
    _ ≤ _ := hUB
  have hcontra : b₀.choose b * (Fintype.card F ^ s - 1)
      ≤ a.choose b * (Fintype.card F ^ (s - 1) - 1) := by
    rw [mul_comm] at this ⊢
    omega
  omega

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.curveExplainSubmodule_ne_top_of_no_witness
#print axioms ProximityGap.markedCurveDecodable_interleaved_weighted
