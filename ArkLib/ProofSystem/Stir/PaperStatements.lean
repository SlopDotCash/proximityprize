/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.MainThm
import ArkLib.Extensions.OracleReduction.VectorIOR

/-!
# Historical STIR paper specifications

These proposition definitions come from #216 at `e36fe8a908`, adapting ArkLib PR #1291
at `df916f59068e0829ea1da1d1c16af8d3e2167b66`. They use the original prover-averaged
security game and the canonical strict soundness relation.

The main specification chooses uniform constants before the protocol parameters and measures
the vector protocol's actual total message length. The round-by-round specification chooses
one protocol before the distances and list sizes and then quantifies its error budget.

These definitions leave the existence claims open. They admit arbitrary vector protocols,
including an exhaustive membership verifier, and carry no verifier-query count or construction
requirement. The concrete STIR prover, verifier, transcript and per-challenge analysis remain
separate obligations, as described in `ArkLib.ProofSystem.Stir.MainThm`.
-/

open BigOperators Finset NNReal ReedSolomon VectorIOP OracleComp LinearCode STIR

namespace StirIOP

namespace Paper

/-- Historical uniform existence and message-length specification. -/
def mainStatement : Prop :=
    ∃ c_F : ℝ, 0 < c_F ∧ ∃ c_M : ℝ, 0 < c_M ∧ ∃ c_len : ℕ → ℝ,
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
      (secpar : ℕ) (ι : Type) [Fintype ι] [Nonempty ι] (φ : ι ↪ F) [Smooth φ]
      (degree : ℕ) (hdeg : ∃ p : ℕ, degree = 2 ^ p)
      (k : ℕ) (hk : ∃ p : ℕ, k = 2 ^ p) (hkGe : 4 ≤ k)
      (δ : ℝ≥0) (hδPos : 0 < δ) (hδub : δ < 1 - 1.05 * Real.sqrt (degree / Fintype.card ι))
      (hF : c_F * (secpar * 2 ^ secpar * degree ^ 2 * (Fintype.card ι : ℝ) ^ ((7 : ℝ) / 2) /
            Real.log (1 / rate (code φ degree))) ≤ Fintype.card F),
    ∃ (M n : ℕ) (vPSpec : ProtocolSpec.VectorSpec n),
      Fintype.card vPSpec.ChallengeIdx = 2 * M + 2 ∧
      ∃ (ε_rbr : vPSpec.ChallengeIdx → ℝ≥0)
        (π : VectorIOP Unit (OracleStatement ι F) Unit vPSpec F),
        IsSecureWithGapAveraged (stirRelation degree φ 0) (stirOpenRelation degree φ δ) ε_rbr π ∧
        (∀ i, ε_rbr i ≤ 1 / 2 ^ secpar) ∧
        (M : ℝ) ≤ c_M * (Real.log degree / Real.log k) ∧
        (vPSpec.totalMessageLength : ℝ) ≤ Fintype.card ι + c_len k * Real.log degree


variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {M : ℕ} (ι : Fin (M + 1) → Type) [∀ i, Fintype (ι i)]

/-- Historical uniform-protocol round-by-round specification. -/
def roundByRoundStatement
    [SampleableType F] {s : ℕ}
    {P : Params ι F}
    [h_nonempty : ∀ i : Fin (M + 1), Nonempty (ι i)]
    (hParams : ParamConditions ι P) : Prop :=
    ∃ n : ℕ,
    -- There exists an `n`-message vector IOPP,
    ∃ vPSpec : ProtocolSpec.VectorSpec n,
    -- such that there are `2 * M + 2` challenges from the verifier to the prover,
    Fintype.card (vPSpec.ChallengeIdx) = 2 * M + 2 ∧
    -- ∃ vector IOPP π with the aforementioned `vPSpec`, and for
    -- `Statement = Unit, Witness = Unit, OracleStatement(ι₀, F)` such that, for all distances and
    -- list sizes `Dist` of the lemma,
    ∃ π : VectorIOP Unit (OracleStatement (ι 0) F) Unit vPSpec F,
    ∀ {Dist : Distances M} (Codes : CodeParams ι P Dist)
      (hδ₀Pos : 0 < Dist.δ 0)
      (hδ₀ : Dist.δ 0 < (1 - Bstar (rate (code (P.φ 0) (degree ι P 0)))))
      (hδᵢ : ∀ {j : Fin (M + 1)}, j ≠ 0 →
        0 < Dist.δ j ∧
        Dist.δ j < (1 - rate (code (P.φ j) (degree ι P j))
          - 1 / Fintype.card (ι j) : ℝ) ∧
        Dist.δ j < (1 - Bstar (rate (code (P.φ j) (degree ι P j))))),
    -- there are round-by-round errors `ε_fold`, `ε_out`, `ε_shift`, `ε_fin` of `π`, whose maximum
    -- is the error of every challenge, such that
    ∃ (ε_fold : ℝ≥0) (ε_out ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0),
    (IsSecureWithGapAveraged (stirRelation (degree ι P 0) (P.φ 0) 0)
                    (stirOpenRelation (degree ι P 0) (P.φ 0) (Dist.δ 0))
                    (fun _ => ε_fold ⊔ ε_fin ⊔ univ.sup ε_out ⊔ univ.sup ε_shift) π) ∧
    -- `ε_fold ≤ errStar(degree₀/foldingParam₀, ρ₀, δ₀, foldingParam₀)`
      ε_fold ≤ proximityError F (degree ι P 0 / P.foldingParam 0)
                 (rate (code (P.φ 0) (degree ι P 0))) (Dist.δ 0) (P.foldingParam 0)
      ∧
      -- Note here that `j : Fin M`, so we need to cast into `Fin (M + 1)` for indexing of
      -- `Dist.δ` and `P.repeatParam`. To get `j`, we use `.castSucc`, whereas to get `j + 1`,
      -- we use `.succ`.
      -- Because of the difference in indexing between the paper and the code, we essentially have
      -- `j = i - 1` compared to the paper.
      -- `ε_out_{j+1} ≤ l_{j+1}²/2 * (degree_{j+1} / (|F| - |ι_{j+1}|))^s`
      (∀ j : Fin M,
        ε_out j ≤ ((Dist.l j.succ : ℝ) ^ 2 / 2) *
          ((degree ι P j.succ : ℝ) / (Fintype.card F - Fintype.card (ι j.succ))) ^ s
        ∧
        -- `ε_shift_{j+1} ≤ (1 - δ_j)^repeatParam_j`
        -- `+ errStar(degree_{j+1}, ρ_{j+1}, δ_{j+1}, repeatParam_j + s)`
        -- `+ errStar(degree_{j+1}/foldingParam_{j+1}, ρ_{j+1}, δ_{j+1}, foldingParam_{j+1})`
        ε_shift j ≤
          (1 - Dist.δ j.castSucc) ^ (P.repeatParam j.castSucc)  +
          -- proximityError(degree_{j+1}, ρ(code_{j+1}), δ_{j+1}, repeatParam_j + s),
          -- where code_{j+1} = code φ_{j+1} degree_{j+1}
           proximityError F (degree ι P j.succ) (rate (code (P.φ j.succ) (degree ι P j.succ)))
            (Dist.δ j.succ) (P.repeatParam j.castSucc + s) +
          -- proximityError(degree_{j+1} / foldingParam_{j+1}, ρ(code_{j+1}), δ_{j+1},
          -- foldingParam_{j+1})
           proximityError F ((degree ι P j.succ) / P.foldingParam j.succ)
            (rate (code (P.φ j.succ) (degree ι P j.succ)))
            (Dist.δ j.succ) (P.foldingParam j.succ)) ∧
      -- `ε_fin ≤ (1 - δ_M)^repeatParam_M`
      ε_fin ≤ (1 - Dist.δ (Fin.last M)) ^ (P.repeatParam (Fin.last M))


end Paper
end StirIOP
