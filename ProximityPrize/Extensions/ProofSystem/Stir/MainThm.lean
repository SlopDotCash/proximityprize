/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Stir.MainThm

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das (Least Authority)
-/

import ProximityPrize.Extensions.Data.CodingTheory.ListDecodability
import ProximityPrize.Extensions.Data.CodingTheory.ReedSolomon
import ProximityPrize.Extensions.OracleReduction.VectorIOR
import ArkLib.ProofSystem.Stir.ProximityBound

/-!
# STIR Main Theorem

Section 5 of [ACFY24stir]: Theorem 5.1 and Lemma 5.4.

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing
    with fewer queries*][ACFY24stir]
-/

open BigOperators Finset ListDecodable NNReal ReedSolomon VectorIOP OracleComp LinearCode STIR

namespace StirIOP

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {M : ℕ} (ι : Fin (M + 1) → Type) [∀ i : Fin (M + 1), Fintype (ι i)]

section MainTheorem

/-- Provides a default OracleInterface instance that leverages
  the oracle statement defined above. The oracle simply applies
  the function `f : ι → F` to the query input `i : ι`,
  producing the response. -/
instance {ι : Type} : OracleInterface (OracleStatement ι F ()) := OracleInterface.instFunction

/-- Theorem 5.1 : STIR main theorem
  Consider the following ingrediants,
  a security parameter `secpar`
  a ReedSolomon code `RS[F, ι, degree]` with rate `ρ = degree/ |ι|`, where ι is a smooth domain
  a proximity parameter `δ ∈ (0, 1 - 1.05 * √ρ)`
  a folding parameter `k ≥ 4`, being a power of 2
  if `|F| ≤ secpar * 2^{secpar * degree² * |ι|^3.5 / log(1/ρ)}`, then
  there exists a `vector IOPP π` for `RS` with
  - `round by round soundness error ≤ 2 ^ (- secpar)`,
  - `M = O(logₖdegree)`
  - `proof length = |ι| + Oₖ(log degree)`
  - `query complexity to input = secpar / (- log(1-δ))`
  - `query complexity to proof strings = Oₖ(log degree + secpar * log(log degree / log(1/ρ)))`
-/
def stir_main
    (secpar : ℕ) [SampleableType F]
  {ι : Type} [Fintype ι] [Nonempty ι]
  {φ : ι ↪ F} {degree : ℕ} [hsmooth : Smooth φ]
  {k proofLen qNumtoInput qNumtoProofstr : ℕ}
  (hk : ∃ p, k = 2 ^ p) (hkGe : k ≥ 4)
  (δ : ℝ≥0) (hδub : δ < 1 - 1.05 * Real.sqrt (degree / Fintype.card ι))
  (hF : Fintype.card F ≤
        secpar * 2 ^ secpar * degree ^ 2 * (Fintype.card ι) ^ (7 / 2) /
          Real.log (1 / rate (code φ degree))) : Prop :=
  ∃ n : ℕ,
  ∃ vPSpec : ProtocolSpec.VectorSpec n,
  ∃ ε_rbr : vPSpec.ChallengeIdx → ℝ≥0,
  ∃ π : VectorIOP Unit (OracleStatement ι F) Unit vPSpec F,
  IsSecureWithGap (stirRelation degree φ 0)
                  (stirRelation degree φ δ)
                  ε_rbr π
  ∧ ∀ i, ε_rbr i ≤ (1 : ℚ≥0) / (2 ^ secpar)
  ∧ ∃ c > 0, M ≤ c * (Real.log degree / Real.log k)
  ∧ ∃ cₖ : ℕ → ℝ, proofLen ≤ (Fintype.card ι) + (cₖ k) * (Real.log degree)
  ∧ (qNumtoInput : ℝ) ≥ secpar / (-Real.log (1 - δ))
  ∧ ∃ cₖ : ℕ → ℝ, qNumtoProofstr ≤
    (cₖ k) * ((Real.log degree) +
      secpar * (Real.log ((Real.log degree) / Real.log (1/rate (code φ degree)))))
  -- STATUS (audit 2026-06-10): front-door statement. The mechanical protocol shape now exists:
  -- `MultiRoundAssembly.lean` constructs `stirMultiRoundIOP`, proves perfect completeness for
  -- its shell verifier, and exposes `stir_main_of_secure_vectorIOP` / `stir_main_of_residuals`.
  -- `CheckingVerifier.lean` adds a non-shell verifier, proves its perfect completeness, and
  -- routes this theorem through checking-IOP front doors. What remains open is the checking
  -- verifier's RBR soundness bridge (`stirCheckingCABridge`) plus the numeric complexity legs.
  -- The soundness argument also still consumes the BCIKS/STIR proximity-gap machinery in the
  -- Johnson / sqrt-rho regime, through explicit residuals rather than hidden proof holes.

end MainTheorem

section RBRSoundness

open LinearCode

/-- Lemma 5.4: Round-by-round soundness of the STIR IOPP
  Consider parameters:
  `ι = {ιᵢ}_{i = 0, ..., M}` be smooth evaluation domains
  `P : Params ι F` containing required protocol parameters -
    initial degree, folding parameters `foldingParamᵢ`, embedding `φᵢ`,
    repetition parameters `repeatParamᵢ`
  `hParams : ParamConditions ι P`, stating conditions that parameters of P must satisfy
  `degreeᵢ = deg / ∏ j<i foldingParamⱼ`, where `deg = degree₀`
  `rateᵢ = degreeᵢ / |ιᵢ|`
  `Codes : CodeParams ι degree P Dist`, containing smooth ReedSolomon codes `RS[F, ιᵢ, degreeᵢ]`
    where `RS[F, ιᵢ, degreeᵢ]` is `(δᵢ,lᵢ)`-list decodable for all `i ∈ {1, ..., M}`
  `δ₀ < (1 - BStar(ρ₀))`
  `∀ i ∈ {1, ..., M}, δᵢ < (1 - ρᵢ - 1/|ιᵢ|)` and `δᵢ < (1 - BStar(ρᵢ))`
  then there exists a `vector IOPP π` with parameters as above such that
  `ε_fold ≤ errStar(degree₀/foldingParam₀, ρ₀, δ₀, repeatParam₀)`
  `ε_outᵢ ≤ lᵢ²/2 * (degreeᵢ/ |F| - |ιᵢ|)^s`
  `ε_shiftᵢ ≤ (1 - δ_{i-1})^repeatParam_{i-1} + errStar(degreeᵢ, ρᵢ, δᵢ, t_{i-1} + s)`
    `+ errStar(degreeᵢ/foldingParamᵢ, ρᵢ, δᵢ, repeatParamᵢ)`
  `ε_fin ≤ (1 - δ_M)^repeatParam_M`
-/
def stir_rbr_soundness
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
    (ε_fold : ℝ≥0) (ε_out : Fin M → ℝ≥0) (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) : Prop :=
    ∃ n : ℕ,
    -- There exists an `n`-message vector IOPP,
    ∃ vPSpec : ProtocolSpec.VectorSpec n,
    -- such that there are `2 * M + 2` challenges from the verifier to the prover,
    Fintype.card (vPSpec.ChallengeIdx) = 2 * M + 2 ∧
    -- ∃ vector IOPP π with the aforementioned `vPSpec`, and for
    -- `Statement = Unit, Witness = Unit, OracleStatement(ι₀, F)` such that
    ∃ π : VectorIOP Unit (OracleStatement (ι 0) F) Unit vPSpec F,
    let ε_rbr : vPSpec.ChallengeIdx → ℝ≥0 :=
      fun _ => ({ε_fold} ∪ {ε_fin} ∪ univ.image ε_out ∪ univ.image ε_shift).max' (by simp)
    (IsSecureWithGap (stirRelation (degree ι P 0) (P.φ 0) 0)
                    (stirRelation (degree ι P 0) (P.φ 0) (Dist.δ 0))
                    ε_rbr π) ∧
    -- `ε_fold ≤ errStar(degree₀/foldingParam₀, ρ₀, δ₀, repeatParam₀)`
      ε_fold ≤ proximityError F (P.deg / P.foldingParam 0) (rate (code (P.φ 0) P.deg))
                 (Dist.δ 0) (P.repeatParam 0)
      ∧
      -- Note here that `j : Fin M`, so we need to cast into `Fin (M + 1)` for indexing of
      -- `Dist.δ` and `P.repeatParam`. To get `j`, we use `.castSucc`, whereas to get `j + 1`,
      -- we use `.succ`.
      -- Because of the difference in indexing between the paper and the code, we essentially have
      -- `j = i - 1` compared to the paper.
      -- `ε_out_{j+1} ≤ l_{j+1}²/2 * (degree_{j+1}/ |F| - |ι_{j+1}|)^s`
      ∀ j : Fin M,
        ε_out j ≤ ((Dist.l j.succ : ℝ) ^ 2 / 2) *
          ((degree ι P j.succ : ℝ) / (Fintype.card F - Fintype.card (ι j.succ))) ^ s
        ∧
        -- `ε_shift_{j+1} ≤ (1 - δ_j)^repeatParam_j`
        -- `+ errStar(degree_{j+1}, ρ_{j+1}, δ_{j+1}, repeatParam_j + s)`
        -- `+ errStar(degree_{j+1}/foldingParam_{j+1}, ρ_{j+1}, δ_{j+1}, repeatParam_{j+1})`
        ε_shift j ≤
          (1 - Dist.δ j.castSucc) ^ (P.repeatParam j.castSucc)  +
          -- proximityError(degreeⱼ, ρ(codeⱼ), δⱼ, repeatParam_j + s), where codeⱼ = code φⱼ degreeⱼ
           proximityError F (degree ι P j.succ) (rate (code (P.φ j.succ) (degree ι P j.succ)))
            (Dist.δ j.succ) (P.repeatParam j.castSucc) + s +
          -- proximityError(degreeⱼ / foldingParamⱼ, ρ(codeⱼ), δⱼ, repeatParamⱼ)
           proximityError F ((degree ι P j.succ) / P.foldingParam j.succ)
            (rate (code (P.φ j.succ) (degree ι P j.succ)))
            (Dist.δ j.succ) (P.repeatParam j.succ)
        ∧
        -- `ε_fin ≤ (1 - δ_M)^repeatParam_M`
        ε_fin ≤ (1 - Dist.δ (Fin.last M)) ^ (P.repeatParam (Fin.last M))
  -- STATUS (audit 2026-06-10): front-door statement. `MultiRoundSpec.lean`, `FullChain.lean`,
  -- and `MultiRoundAssembly.lean` now realize the `2 * M + 2` challenge shape and provide
  -- conditional witnesses for this existential. `CheckingVerifier.lean` instantiates those
  -- witnesses with a real verifier and proven completeness; the remaining unconditional Lemma
  -- 5.4 content is the round-by-round knowledge-soundness bridge. The per-round `proximityError`
  -- obligations remain tied to the explicit BCIKS/STIR proximity-gap residuals in the Johnson /
  -- sqrt-rho list-decoding regime.

end RBRSoundness

end StirIOP

/- Axiom audit for the STIR main theorem residual front doors (#24). -/
#print axioms StirIOP.stir_main
#print axioms StirIOP.stir_rbr_soundness
