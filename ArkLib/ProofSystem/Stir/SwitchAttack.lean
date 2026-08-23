/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Stir.SubUnitRbr

/-!
# Issue #335 (K4) — the switch-prover tightness attack, decision level

The anti-fabrication fence for the genuine budget of `Stir/SubUnitRbr.lean`:

* `stirChecking_switch_decision` — with the constant codeword message family `constMsgs u`,
  the checking decision reduces EXACTLY to the single input-link check (every
  pair-consistency check compares two reads of the same constant vector; the final
  full-read check sees `u` itself, a codeword).
* `stirChecking_switch_attack` — acceptance probability ≥ `|{x | f x = u x}|/|F|` over a
  uniformly drawn round-2 challenge value.  With `u` a nearest codeword to a δ-far `f`,
  no rbr budget family summing below `(|ι| − Δ(f, code))/|F|` can be sound for this
  verifier: `stirEpsStar` is essentially tight, and the L5.4 `2^{-secpar}` budgets are
  unachievable in the single-query wire model (the t-repetition model — #335 A1 — is the
  honest path).  The bound counts only in-image challenge values; out-of-image values map
  to the fixed `Function.invFun` fallback point and can only increase acceptance.
-/


open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal WhirIOP.Construction VectorIOP
open OracleInterface
open scoped ENNReal

noncomputable section

namespace StirIOP

namespace MultiRound

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [Nonempty ι]
variable (M : ℕ) (φ : ι ↪ F) (deg : ℕ)

/-- The switch prover's constant message family: every message is the packed codeword `u`. -/
def constMsgs (u : ι → F) :
    ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j :=
  fun j => Vector.cast (stirMultiVSpec_length_msg j) (packFiniteFunction ι u)

/-- Reading any constant message at the position of `x` returns `u x`. -/
theorem msgAns_constMsgs (u : ι → F)
    (j : ((stirMultiVSpec M ι).toProtocolSpec F).MessageIdx) (x : ι) :
    msgAns (constMsgs M u) j (msgPos M j x) = u x := by
  have h1 : msgAns (constMsgs M u) j (msgPos M j x)
      = (constMsgs M u j).get (msgPos M j x) := rfl
  rw [h1]
  simp [constMsgs, msgPos, packFiniteFunction, Vector.get_eq_getElem,
    Equiv.symm_apply_apply]

/-- The final-check unpacked function of the constant messages is `u` itself. -/
theorem finalRead_constMsgs (u : ι → F) :
    (fun x : ι =>
      (((List.finRange (Fintype.card ι)).map (fun k =>
        msgAns (constMsgs M u) (msgIdx M (Fin.last M))
          (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M))) k))).getD
        ((Fintype.equivFin ι x : Fin (Fintype.card ι)) : ℕ) 0)) = u := by
  funext x
  rw [listGetD_finRange_map
    (fun k => msgAns (constMsgs M u) (msgIdx M (Fin.last M))
      (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M))) k))
    ((Fintype.equivFin ι x : Fin (Fintype.card ι)) : ℕ) (Fin.isLt _)]
  have h1 : msgAns (constMsgs M u) (msgIdx M (Fin.last M))
      (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M)))
        (Fintype.equivFin ι x))
      = (constMsgs M u (msgIdx M (Fin.last M))).get
        (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M)))
          (Fintype.equivFin ι x)) := rfl
  rw [h1]
  simp [constMsgs, packFiniteFunction, Vector.get_eq_getElem, Equiv.symm_apply_apply]

/-- **The switch-prover decision characterization**: with the constant codeword messages, the
checking verifier's decision reduces to the single input-link check — acceptance holds iff
the input agrees with `u` at the challenge-derived point.  Every pair-consistency check
compares two reads of the same constant vector, and the final full-read check sees `u` itself. -/
theorem stirChecking_switch_decision (f u : ι → F) (hu : u ∈ ReedSolomon.code φ deg)
    (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges) :
    checkingBool M φ deg (fun _ => f) (constMsgs M u) chals = true ↔
      f (queryPoint φ (chalFE chals (outChalIdx M 0)))
        = u (queryPoint φ (chalFE chals (outChalIdx M 0))) := by
  rw [checkingBool_eq_true_iff]
  constructor
  · rintro ⟨h0, -, -⟩
    rw [msgAns_constMsgs] at h0
    exact h0
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rw [msgAns_constMsgs]
      exact h
    · intro j
      rw [msgAns_constMsgs, msgAns_constMsgs, msgAns_constMsgs, msgAns_constMsgs]
      exact ⟨rfl, rfl⟩
    · rw [finalRead_constMsgs]
      exact hu

/-- **The switch-prover acceptance lower bound (K4, decision level)**: against the constant
codeword strategy, the checking decision accepts with probability at least
`|{x | f x = u x}| / |F|` over a uniformly drawn round-2 challenge value (other challenges
arbitrary).  With `u` a nearest codeword to a δ-far `f`, the agreement set has
`≥ |ι| − (⌊δ|ι|⌋ + …)`-size, so no rbr budget family summing below `|A|/|F|` can be sound for
this verifier — the genuine-budget theorem `stirCheckingRbrSoundness_genuine` is essentially
tight.  (The bound counts only in-image challenge values; out-of-image values map to the
fixed `Function.invFun` fallback point and can only increase acceptance.) -/
theorem stirChecking_switch_attack (f u : ι → F) (hu : u ∈ ReedSolomon.code φ deg)
    (chals₀ : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges) :
    ((Finset.univ.filter (fun x : ι => f x = u x)).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ Pr[fun r : F =>
          checkingBool M φ deg (fun _ => f) (constMsgs M u)
            (Function.update chals₀ (outChalIdx M 0)
              (Vector.cast (by
                rw [stirMulti_length_chal (M := M) (ι := ι) (outChalIdx M 0).1 (by
                  show ((outChalIdx M 0).1 : ℕ) % 3 ≠ 1
                  simp [outChalIdx])]
                ) (Vector.replicate 1 r))) = true
        | $ᵗ F] := by
  classical
  set A : Finset ι := Finset.univ.filter (fun x : ι => f x = u x) with hA
  -- the event contains the φ-image of the agreement set
  have hsub : A.image φ ⊆ Finset.univ.filter (fun r : F =>
      checkingBool M φ deg (fun _ => f) (constMsgs M u)
        (Function.update chals₀ (outChalIdx M 0)
          (Vector.cast (by
            rw [stirMulti_length_chal (M := M) (ι := ι) (outChalIdx M 0).1 (by
              show ((outChalIdx M 0).1 : ℕ) % 3 ≠ 1
              simp [outChalIdx])]
            ) (Vector.replicate 1 r))) = true) := by
    intro r hr
    obtain ⟨x, hxA, rfl⟩ := Finset.mem_image.mp hr
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [stirChecking_switch_decision M φ deg f u hu]
    have hread : chalFE (Function.update chals₀ (outChalIdx M 0)
        (Vector.cast (by
          rw [stirMulti_length_chal (M := M) (ι := ι) (outChalIdx M 0).1 (by
            show ((outChalIdx M 0).1 : ℕ) % 3 ≠ 1
            simp [outChalIdx])]
          ) (Vector.replicate 1 (φ x)))) (outChalIdx M 0) = φ x := by
      rw [chalFE, Function.update_self]
      simp [Vector.get_eq_getElem]
    rw [hread]
    have hqp : queryPoint φ (φ x) = x := Function.leftInverse_invFun φ.injective x
    rw [hqp]
    simpa [hA] using hxA
  -- count: Pr over the uniform draw is the filter density
  have hcount : ((A.image φ).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ Pr[fun r : F =>
          checkingBool M φ deg (fun _ => f) (constMsgs M u)
            (Function.update chals₀ (outChalIdx M 0)
              (Vector.cast (by
                rw [stirMulti_length_chal (M := M) (ι := ι) (outChalIdx M 0).1 (by
                  show ((outChalIdx M 0).1 : ℕ) % 3 ≠ 1
                  simp [outChalIdx])]
                ) (Vector.replicate 1 r))) = true
        | $ᵗ F] := by
    rw [probEvent_uniformSample]
    exact ENNReal.div_le_div_right (by exact_mod_cast Finset.card_le_card hsub) _
  rw [Finset.card_image_of_injective _ φ.injective] at hcount
  exact hcount

end MultiRound

end StirIOP

end

#print axioms StirIOP.MultiRound.stirChecking_switch_decision
#print axioms StirIOP.MultiRound.stirChecking_switch_attack
