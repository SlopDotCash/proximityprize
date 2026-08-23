/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.ComposedRbrKnowledgeSoundness

/-!
# Shared direction facts for the composed Spartan chains (DRY-audit item 8)

The seam-direction facts and round-count positivity lemmas for `composedPSpec` and its `sfx*`
suffixes, extracted from their three per-file `private` clones (`ComposedCompleteness.lean` —
the original, left untouched as sibling-shared — plus the two campaign clones). Public so the
KS fold (`TightComposedFull.lean`), the completeness fold (`TightComposedCompleteness.lean`),
and any future chain consume ONE copy.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

/-! ### Direction facts -/

/-- Positivity of two-step round counts. -/
theorem vsum_two_pos {ℓ : ℕ} (h : 0 < ℓ) : 0 < Fin.vsum (fun _ : Fin ℓ => 2) := by
  rcases ℓ with - | k
  · omega
  · rw [Fin.vsum_succ]; omega

/-- The multi-round sum-check protocol opens with the prover's `P_to_V` polynomial message. -/
theorem sumcheckPSpec_dir_zero (deg n : ℕ)
    (h : 0 < Fin.vsum (fun _ : Fin n => 2)) :
    (Sumcheck.Spec.pSpec R deg n).dir ⟨0, h⟩ = .P_to_V := by
  rcases ProtocolSpec.seqCompose_appendValid
      (pSpec := fun _ : Fin n => Sumcheck.Spec.SingleRound.pSpec R deg)
      (fun _ => ⟨by norm_num, rfl⟩) with hzero | ⟨h', hdir⟩
  · omega
  · exact hdir

/-- `sfx6 = sumcheck₂ ++ₚ !p[]` opens `P_to_V` (second sum-check's leading message). -/
theorem sfx6_dir_zero (hn : 0 < pp.ℓ_n)
    (h : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0) :
    (sfx6 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_pos hn
  rw [show (⟨0, h⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))
      = Fin.castLE (by omega) (⟨0, hv⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2))) from by
    ext; simp]
  rw [Prover.append_dir_castLE]
  exact sumcheckPSpec_dir_zero 2 pp.ℓ_n hv

/-- `sfx5 = !p[] ++ₚ sfx6` opens `P_to_V`. (Also the seam-direction fact for the
`prependRLCTarget ▷ …` append, whose combined spec is literally `sfx5` at seam index `0`.) -/
theorem sfx5_dir_zero (hn : 0 < pp.ℓ_n)
    (h : 0 < 0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)) :
    (sfx5 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  have h6 : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0 := by omega
  rw [show (⟨0, h⟩ : Fin (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))
      = Fin.natAdd 0 (⟨0, h6⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx6_dir_zero pp hn h6

/-- `sfx4 = ⟨V_to_P, LinComb⟩ ++ₚ sfx5` opens `V_to_P` (the linear-combination challenge). -/
theorem sfx4_dir_zero
    (h : 0 < 1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) :
    (sfx4 (R := R) pp).dir ⟨0, h⟩ = .V_to_P := by
  rw [show (⟨0, h⟩ : Fin (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

/-- Seam-direction fact for `linearCombination ▷ sfx5`: the combined spec (= `sfx4`) at the
seam index `1` is `P_to_V`. -/
theorem sfx4_dir_seam (hn : 0 < pp.ℓ_n)
    (h : 1 < 1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) :
    (sfx4 (R := R) pp).dir ⟨1, h⟩ = .P_to_V := by
  have h5 : 0 < 0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))
      = Fin.natAdd 1 (⟨0, h5⟩ : Fin (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx5_dir_zero pp hn h5

/-- `sfx3 = ⟨P_to_V, EvalClaim⟩ ++ₚ sfx4` opens `P_to_V` (the bundled eval-claim message). -/
theorem sfx3_dir_zero
    (h : 0 < 1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) :
    (sfx3 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  rw [show (⟨0, h⟩ : Fin (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

/-- Seam-direction fact for `sendEvalClaim ▷ sfx4`: the combined spec (= `sfx3`) at the seam
index `1` is `V_to_P` (the linear-combination challenge). -/
theorem sfx3_dir_seam
    (h : 1 < 1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) :
    (sfx3 (R := R) pp).dir ⟨1, h⟩ = .V_to_P := by
  have h4 : 0 < 1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))
      = Fin.natAdd 1 (⟨0, h4⟩ : Fin (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx4_dir_zero pp h4

/-- `sfx2 = sumcheck₃ ++ₚ sfx3` opens `P_to_V` (first sum-check's leading message). -/
theorem sfx2_dir_zero (hm : 0 < pp.ℓ_m)
    (h : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) :
    (sfx2 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2) := vsum_two_pos hm
  rw [show (⟨0, h⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))
      = Fin.castLE (by omega) (⟨0, hv⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2))) from by
    ext; simp]
  rw [Prover.append_dir_castLE]
  exact sumcheckPSpec_dir_zero 3 pp.ℓ_m hv

/-- Seam-direction fact for `firstSumcheck ▷ sfx3`: the combined spec (= `sfx2`) at the seam
index `vsum 2` is `P_to_V` (the bundled eval-claim message). -/
theorem sfx2_dir_seam
    (h : Fin.vsum (fun _ : Fin pp.ℓ_m => 2) < Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) :
    (sfx2 (R := R) pp).dir ⟨Fin.vsum (fun _ : Fin pp.ℓ_m => 2), h⟩ = .P_to_V := by
  have h3 : 0 < 1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) := by omega
  rw [show (⟨Fin.vsum (fun _ : Fin pp.ℓ_m => 2), h⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))
      = Fin.natAdd (Fin.vsum (fun _ : Fin pp.ℓ_m => 2))
          (⟨0, h3⟩ : Fin (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx3_dir_zero pp h3

/-- `sfx1 = ⟨V_to_P, FirstChallenge⟩ ++ₚ sfx2` opens `V_to_P`. -/
theorem sfx1_dir_zero
    (h : 0 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))) :
    (sfx1 (R := R) pp).dir ⟨0, h⟩ = .V_to_P := by
  rw [show (⟨0, h⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

/-- Seam-direction fact for `firstChallenge ▷ sfx2`: the combined spec (= `sfx1`) at the seam
index `1` is `P_to_V` (the first sum-check's leading message). -/
theorem sfx1_dir_seam (hm : 0 < pp.ℓ_m)
    (h : 1 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))) :
    (sfx1 (R := R) pp).dir ⟨1, h⟩ = .P_to_V := by
  have h2 : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))))
      = Fin.natAdd 1 (⟨0, h2⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx2_dir_zero pp hm h2

/-- Seam-direction fact for `firstMessage ▷ sfx1`: the combined spec (= `composedPSpec`) at the
seam index `1` is `V_to_P` (the first challenge). -/
theorem composedPSpec_dir_seam
    (h : 1 < 1 + (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))) :
    (composedPSpec (R := R) pp).dir ⟨1, h⟩ = .V_to_P := by
  have h1 : 0 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))))
      = Fin.natAdd 1 (⟨0, h1⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx1_dir_zero pp h1

/-! ### Challenge-family `Fintype`/`Inhabited` instances, bottom-up -/


end

end Spartan.Spec.Bricks
