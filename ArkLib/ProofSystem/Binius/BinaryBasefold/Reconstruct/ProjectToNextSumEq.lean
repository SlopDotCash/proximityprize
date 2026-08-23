/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Structured.SingleRound
import ArkLib.ProofSystem.RingSwitching.Prelude

/-!
# Round-poly marginal at the verifier challenge (`projectToNextSumcheckPoly_sum_eq`)

This file supplies the single missing lemma `projectToNextSumcheckPoly_sum_eq` consumed by
`Binius.BinaryBasefold.ReductionLogic` (the `foldStep_is_logic_complete` output-relation step) and
by `Binius.RingSwitching.SumcheckPhase` / `Binius.BinaryBasefold.Steps.Fold`.

It is the *challenge-evaluation* analogue of the proven verifier-check identity
`Sumcheck.Structured.getSumcheckRoundPoly_sum_eq`: instead of summing the round univariate over the
two Boolean points `𝓑 0, 𝓑 1`, we evaluate it at the verifier's challenge `rᵢ`, and the survivor
sum is taken of the *projected next-round* polynomial `projectToNextSumcheckPoly i Hᵢ rᵢ` over the
smaller Boolean cube `(univ.map 𝓑) ^ᶠ (ℓ - i.succ)`.

The proof bridges the two `getSumcheckRoundPoly` conventions:

* the round univariate keeps the **last** surviving variable as the indeterminate
  (`getSumcheckRoundPoly_eval_eq_sum_snoc`, `Fin.snoc … rᵢ`), and
* `projectToNextSumcheckPoly = fixFirstVariablesOfMQP (v := 1)` also fixes the **last** surviving
  variable (`fixFirstVariablesOfMQP_eval`),

so both sides are the same survivor-cube sum of `Hᵢ` with its last variable fixed to `rᵢ`, up to a
canonical `Fin.cast` reindex of the survivor coordinates.
-/

namespace Sumcheck.Structured

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial

noncomputable section

variable {L : Type} [CommRing L] {ℓ : ℕ} [NeZero ℓ]

/-- Renaming a polynomial along the canonical index `finCongr` of a dimension equality is
heterogeneously equal to the original polynomial. -/
private lemma rename_finCongr_heq' {a b : ℕ} (h : a = b) (p : MvPolynomial (Fin a) L) :
    HEq (rename (finCongr h) p) p := by
  subst h
  simp [finCongr_refl]

/- **Round-poly marginal at the challenge** (`D = uniform 𝓑`): evaluating the prover's round
univariate `getSumcheckRoundPoly ℓ (uniform 𝓑 ℓ) i Hᵢ` at the verifier challenge `rᵢ`
equals the sum,
over the next round's Boolean cube `(univ.map 𝓑) ^ᶠ (ℓ - i.succ)`, of the projected next-round
polynomial `projectToNextSumcheckPoly i Hᵢ rᵢ`. Consumed by `BinaryBasefold.ReductionLogic`,
`BinaryBasefold.Steps.Fold`, and `RingSwitching.SumcheckPhase`. -/
set_option maxHeartbeats 800000 in
-- Needed for the dependent survivor-cube reindexing and `Fin.cast` normalization proof below.
theorem projectToNextSumcheckPoly_sum_eq {𝓑 : Fin 2 ↪ L} (i : Fin ℓ)
    (Hᵢ : MultiquadraticPoly L (ℓ - i)) (rᵢ : L) :
    (getSumcheckRoundPoly ℓ (SumcheckDomain.uniform 𝓑 ℓ) (i := i) Hᵢ).val.eval rᵢ =
      ∑ x ∈ (Finset.univ.map 𝓑) ^ᶠ (ℓ - i.succ),
        (projectToNextSumcheckPoly (L := L) (ℓ := ℓ) (i := i) (Hᵢ := Hᵢ)
          (rᵢ := rᵢ)).val.eval x := by
  have hn : ℓ - ↑i.castSucc = (ℓ - ↑i.castSucc - 1) + 1 := by
    have := i.2
    simp only [Fin.val_castSucc]
    omega
  set curH : L[X Fin ((ℓ - ↑i.castSucc - 1) + 1)] := rename (finCongr hn) Hᵢ.val
    with hcurH_def
  have hHEq : HEq curH Hᵢ.val := by
    rw [hcurH_def]
    exact rename_finCongr_heq' (L := L) (h := hn) (p := Hᵢ.val)
  rw [getSumcheckRoundPoly_eval_eq_sum_snoc ℓ (SumcheckDomain.uniform 𝓑 ℓ)
    (i := i) (h := Hᵢ) (r := rᵢ) (curH := curH) (hcurH := hHEq)]
  have hpos : 0 < ℓ - ↑i.castSucc := by
    have := i.2
    simp only [Fin.val_castSucc]
    omega
  set v1 : Fin (ℓ - ↑i.castSucc + 1) := ⟨1, by omega⟩ with hv1
  have hfix : ∀ x : Fin (ℓ - (↑i.castSucc + 1)) → L,
      MvPolynomial.eval
          (Fin.snoc (Fin.append x (fun j => j.elim0) ∘ Fin.cast (by omega)) rᵢ) curH
        = MvPolynomial.eval
            (fun k : Fin ((ℓ - ↑i.castSucc) - ↑v1) =>
              (Fin.append x (fun j => j.elim0) ∘ Fin.cast (by simp only [hv1]; omega)) k)
            (fixFirstVariablesOfMQP (ℓ - ↑i.castSucc) v1 Hᵢ.val (fun _ => rᵢ)) := by
    intro x
    rw [RingSwitching.fixFirstVariablesOfMQP_eval (L := L) (ℓ := ℓ - ↑i.castSucc)
      v1 Hᵢ.val (fun _ => rᵢ)
      (fun k : Fin ((ℓ - ↑i.castSucc) - ↑v1) =>
        (Fin.append x (fun j => j.elim0) ∘ Fin.cast (by simp only [hv1]; omega)) k)]
    rw [hcurH_def, eval_rename]
    refine congrArg (fun pt => MvPolynomial.eval pt Hᵢ.val) ?_
    funext j
    simp only [Function.comp_apply, Equiv.trans_apply, finCongr_apply,
      RingSwitching.finSumFinEquiv_symm_dite, Fin.val_cast]
    by_cases hj : (j : ℕ) < ℓ - ↑i.castSucc - 1
    · rw [dif_pos (show (j : ℕ) < (ℓ - ↑i.castSucc) - ↑v1 by
          simp only [hv1]; omega), Sum.elim_inl]
      simp only [show (Fin.cast hn j) = Fin.castSucc ⟨(j : ℕ), by omega⟩ from Fin.ext rfl,
        Fin.snoc_castSucc, Function.comp_apply]
    · have hjlast : (j : ℕ) = ℓ - ↑i.castSucc - 1 := by
        have := j.2
        omega
      rw [dif_neg (show ¬ (j : ℕ) < (ℓ - ↑i.castSucc) - ↑v1 by
          simp only [hv1]; omega), Sum.elim_inr]
      simp only [show (Fin.cast hn j) = Fin.last (ℓ - ↑i.castSucc - 1) from
          Fin.ext (by simp [hjlast]),
        Fin.snoc_last]
  rw [Finset.sum_congr rfl (fun x _ => hfix x)]
  simp only [projectToNextSumcheckPoly]
  change
    ∑ x ∈ ((SumcheckDomain.uniform 𝓑 ℓ).drop (↑i.castSucc + 1)).cube,
        MvPolynomial.eval
          (fun k : Fin ((ℓ - ↑i.castSucc) - 1) =>
            (Fin.append x (fun j => j.elim0) ∘ Fin.cast (by omega)) k)
          (fixFirstVariablesOfMQP (ℓ - ↑i.castSucc)
            ⟨1, by have := i.2; simp only [Fin.val_castSucc]; omega⟩ Hᵢ.val
            (fun _ => rᵢ))
      =
    ∑ x ∈ (Finset.univ.map 𝓑) ^ᶠ (ℓ - ↑i.succ),
        MvPolynomial.eval x
          (fixFirstVariablesOfMQP (ℓ - ↑i.castSucc)
            ⟨1, by have := i.2; simp only [Fin.val_castSucc]; omega⟩ Hᵢ.val
            (fun _ => rᵢ))
  simp only [SumcheckDomain.drop_uniform]
  rw [show (Finset.univ.map 𝓑) ^ᶠ (ℓ - ↑i.succ)
      = (SumcheckDomain.uniform 𝓑 (ℓ - ↑i.succ)).cube from rfl]
  symm
  have hdim : ℓ - (↑i.succ : ℕ) = ℓ - (↑i.castSucc + 1) := by
    have := i.2
    simp only [Fin.val_succ, Fin.val_castSucc]
  apply Finset.sum_nbij' (fun z => z ∘ Fin.cast hdim) (fun y => y ∘ Fin.cast hdim.symm)
  · intro z hz
    apply SumcheckDomain.mem_cube.2
    have hzmem := Fintype.mem_piFinset.mp hz
    intro j
    simpa [Function.comp_apply, SumcheckDomain.points_uniform] using hzmem (Fin.cast hdim j)
  · intro y hy
    apply Fintype.mem_piFinset.mpr
    intro j
    simpa [Function.comp_apply, SumcheckDomain.points_uniform] using
      SumcheckDomain.mem_cube.1 hy (Fin.cast hdim.symm j)
  · intro z _
    funext j
    simp
  · intro y _
    funext j
    simp
  · intro z _
    refine congrArg
      (fun pt => MvPolynomial.eval pt
        (fixFirstVariablesOfMQP (ℓ - ↑i.castSucc)
          ⟨1, by have := i.2; simp only [Fin.val_castSucc]; omega⟩ Hᵢ.val (fun _ => rᵢ))) ?_
    funext j
    simp only [Function.comp_apply]
    change z j =
      Fin.append (z ∘ Fin.cast hdim) (fun j => j.elim0) (Fin.castAdd 0 (Fin.cast hdim.symm j))
    rw [Fin.append_left, Function.comp_apply]
    exact (congrArg z (Fin.ext (by simp only [Fin.val_cast]))).symm

end

end Sumcheck.Structured

#print axioms Sumcheck.Structured.projectToNextSumcheckPoly_sum_eq
