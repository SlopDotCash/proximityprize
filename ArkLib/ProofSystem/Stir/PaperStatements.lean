/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.MainThm

/-!
# Corrected STIR paper statements

Adapted from upstream PR #1291 at `df916f59068e0829ea1da1d1c16af8d3e2167b66`.
These are proposition definitions, not security theorems. The donor theorem bodies are admitted
and are intentionally not imported. The existing native `stir_main` and `stir_rbr_soundness`
remain legacy conditional interfaces; their proofs do not establish these stronger contracts.

The main statement quantifies uniform constants before all protocol parameters, uses a lower
bound on field size with real exponent 7/2, measures the actual protocol message length, and
requires strict proximity for soundness. Query complexity is not asserted: the current vector
IOP interface has no implemented verifier-query counter. The round statement chooses one
protocol before distances and list bounds, then obtains its error bounds for those choices.
-/

open BigOperators Finset ListDecodable NNReal ReedSolomon VectorIOP OracleComp LinearCode STIR

namespace StirIOP

/-- Strict version of `stirRelation`: the oracle's output is *strictly* closer than `err` to a
  Reed-Solomon codeword of degree less than `degree` over domain `φ`.

  This is the soundness relation of an IOPP of proximity: its complement is "at least `err`-far",
  which is the case the soundness statements of [ACFY24stir] cover (`δ₀ ≤ Δ(f, RS)` in Lemma 5.4).
  Completeness is stated with `stirRelation degree φ 0`, the codewords. -/
def stirOpenRelation
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} [Fintype ι] [Nonempty ι]
    (degree : ℕ) (φ : ι ↪ F) (err : ℝ≥0) : Set ((Unit × ∀ i, (OracleStatement ι F i)) × Unit) :=
  fun ⟨⟨_, oracle⟩, _⟩ => δᵣ(oracle (), ReedSolomon.code φ degree) < err

namespace Paper

/-- Corrected existence and complexity contract; no proof is asserted. -/
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
        IsSecureWithGap (stirRelation degree φ 0) (stirOpenRelation degree φ δ) ε_rbr π ∧
        (∀ i, ε_rbr i ≤ 1 / 2 ^ secpar) ∧
        (M : ℝ) ≤ c_M * (Real.log degree / Real.log k) ∧
        (vPSpec.totalMessageLength : ℝ) ≤ Fintype.card ι + c_len k * Real.log degree


variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {M : ℕ} (ι : Fin (M + 1) → Type) [∀ i, Fintype (ι i)]

/-- Corrected uniform-protocol round-by-round contract; no proof is asserted. -/
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
    (IsSecureWithGap (stirRelation (degree ι P 0) (P.φ 0) 0)
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
