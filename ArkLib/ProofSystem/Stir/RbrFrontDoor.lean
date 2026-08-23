/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.MainThm
import ArkLib.ProofSystem.Stir.MultiRoundSpec

/-!
# The stir_rbr_soundness front door (#301)

The front-door wiring — `stir_rbr_soundness` reduces to supplying a
`VectorIOP` over the landed `stirVSpec` together with its `IsSecureWithGap` proof and the
per-round error bounds (the STIR analogue of WHIR's
`whir_rbr_soundness_of_whirVectorSpec_secure_gap`). -/

open BigOperators Finset ListDecodable NNReal ReedSolomon VectorIOP OracleComp LinearCode STIR

namespace StirIOP

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {M : ℕ} (ι : Fin (M + 1) → Type) [∀ i : Fin (M + 1), Fintype (ι i)]

open LinearCode in
/-- **Front door for Lemma 5.4**: `stir_rbr_soundness` holds as soon as one supplies a
`VectorIOP` over the canonical `stirVSpec` wire format (whose `2M+2` challenge count is the
landed `stirVSpec_card_challengeIdx`), its `IsSecureWithGap` proof at the max'd round-error
function, and the per-round error bounds. This isolates the remaining work on Lemma 5.4 to
exactly: the protocol object, its security proof, and the budget inequalities — all wire-format
independent of the `∃`-packaging. -/
theorem stir_rbr_soundness_of_stirVSpec_secure_gap
    [SampleableType F] {s : ℕ}
    {P : Params ι F}
    [h_nonempty : ∀ i : Fin (M + 1), Nonempty (ι i)]
    {hParams : ParamConditions ι P} {Dist : Distances M}
    {Codes : CodeParams ι P Dist}
    (hδ₀ : Dist.δ 0 < (1 - Bstar (rate (code (P.φ 0) P.deg))))
    (hδᵢ : ∀ {j : Fin (M + 1)}, j ≠ 0 →
        Dist.δ j < (1 - rate (code (P.φ j) (degree ι P j))
          - 1 / Fintype.card (ι j) : ℝ) ∧
        Dist.δ j < (1 - Bstar (rate (code (P.φ j) (degree ι P j)))))
    (ε_fold : ℝ≥0) (ε_out : Fin M → ℝ≥0) (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    (msgLen : Fin (M + 1) → ℕ) (chalLen : ℕ)
    (π : VectorIOP Unit (OracleStatement (ι 0) F) Unit (stirVSpec M msgLen chalLen) F)
    (hSecure : VectorIOP.IsSecureWithGap
        (stirRelation (degree ι P 0) (P.φ 0) 0)
        (stirRelation (degree ι P 0) (P.φ 0) (Dist.δ 0))
        (fun _ => ({ε_fold} ∪ {ε_fin} ∪ univ.image ε_out ∪ univ.image ε_shift).max' (by simp))
        π)
    (h_fold : ε_fold ≤ proximityError F (P.deg / P.foldingParam 0)
        (rate (code (P.φ 0) P.deg)) (Dist.δ 0) (P.repeatParam 0))
    (h_tail : ∀ j : Fin M,
        ε_out j ≤ ((Dist.l j.succ : ℝ) ^ 2 / 2) *
          ((degree ι P j.succ : ℝ) / (Fintype.card F - Fintype.card (ι j.succ))) ^ s
        ∧
        ε_shift j ≤
          (1 - Dist.δ j.castSucc) ^ (P.repeatParam j.castSucc)  +
           proximityError F (degree ι P j.succ) (rate (code (P.φ j.succ) (degree ι P j.succ)))
            (Dist.δ j.succ) (P.repeatParam j.castSucc) + s +
           proximityError F ((degree ι P j.succ) / P.foldingParam j.succ)
            (rate (code (P.φ j.succ) (degree ι P j.succ)))
            (Dist.δ j.succ) (P.repeatParam j.succ)
        ∧
        ε_fin ≤ (1 - Dist.δ (Fin.last M)) ^ (P.repeatParam (Fin.last M))) :
    stir_rbr_soundness (F := F) ι (s := s) (P := P)
      (hParams := hParams) (Dist := Dist) (Codes := Codes)
      hδ₀ @hδᵢ ε_fold ε_out ε_shift ε_fin :=
  ⟨3 * M + 3, stirVSpec M msgLen chalLen, stirVSpec_card_challengeIdx,
    π, hSecure, h_fold, h_tail⟩

end StirIOP

#print axioms StirIOP.stir_rbr_soundness_of_stirVSpec_secure_gap
