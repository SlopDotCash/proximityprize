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

section ParamRegime

/-! ### Nonvacuity of the parameter regime (audit 2026-10-28, L36)

An older form of `ParamConditions` required `|ιᵢ| ≤ degreeᵢ`, which on a nonempty domain forces
rate `1` and so contradicts the radius hypothesis `δ₀ < 1 - B⋆(ρ₀)` of `stir_rbr_soundness`
(`not_lt_one_sub_Bstar_rate_of_card_le`). The canonical `ParamConditions` uses
`h_smooth_lt : degreeᵢ < |ιᵢ|`; the lemmas below record that the radius windows are then
nonempty. -/

omit [Fintype F] [DecidableEq F] in
/-- If the evaluation domain is no larger than the degree bound, the Reed–Solomon code has rate
`1`, and then no radius satisfies `δ < 1 - B⋆(ρ)`. -/
theorem not_lt_one_sub_Bstar_rate_of_card_le {ι : Type} [Fintype ι] [Nonempty ι]
    (φ : ι ↪ F) {d : ℕ} (hd : Fintype.card ι ≤ d) (δ : ℝ≥0) :
    ¬ δ < 1 - Bstar (rate (code φ d)) := by
  have hcard : (Fintype.card ι : ℚ≥0) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  have hrate : rate (code φ d) = 1 := by
    rw [ReedSolomon.rateOfLinearCode_eq_min_div, min_eq_right hd, div_self hcard]
  simp [hrate, Bstar]

omit [Fintype F] in
variable {ι} in
/-- Under `ParamConditions`, every round's Reed–Solomon code has rate `< 1`. -/
theorem ParamConditions.rate_lt_one {P : Params ι F} (hP : ParamConditions ι P)
    (i : Fin (M + 1)) : rate (code (P.φ i) (degree ι P i)) < 1 := by
  have hd := hP.h_smooth_lt i
  have hpos : (0 : ℚ≥0) < Fintype.card (ι i) := by exact_mod_cast (Nat.zero_le _).trans_lt hd
  rw [ReedSolomon.rateOfLinearCode_eq_min_div, min_eq_left hd.le, div_lt_one hpos]
  exact_mod_cast hd

omit [Fintype F] in
variable {ι} in
/-- Under `ParamConditions`, every round's radius window `δᵢ < 1 - B⋆(ρᵢ)` is nonempty. -/
theorem ParamConditions.zero_lt_one_sub_Bstar_rate {P : Params ι F} (hP : ParamConditions ι P)
    (i : Fin (M + 1)) : 0 < 1 - Bstar (rate (code (P.φ i) (degree ι P i))) := by
  have h : ((rate (code (P.φ i) (degree ι P i)) : ℚ≥0) : ℝ≥0) < 1 := by
    exact_mod_cast hP.rate_lt_one i
  have hs : Bstar (rate (code (P.φ i) (degree ι P i))) < 1 := by
    unfold Bstar
    simpa using NNReal.sqrt_lt_sqrt.mpr h
  exact tsub_pos_of_lt hs

omit [Fintype F] in
variable {ι} in
/-- **Nonvacuity of the round-`0` radius hypothesis**: under `ParamConditions`, the bound
`δ₀ < 1 - B⋆(ρ₀)` assumed by `stir_rbr_soundness` is satisfiable, for instance by `δ₀ = 0`. -/
theorem ParamConditions.zero_lt_one_sub_Bstar_rate_zero {P : Params ι F}
    (hP : ParamConditions ι P) : 0 < 1 - Bstar (rate (code (P.φ 0) P.deg)) := by
  simpa only [degree_zero] using hP.zero_lt_one_sub_Bstar_rate 0

end ParamRegime

section MainTheorem

/-- Provides a default OracleInterface instance that leverages
  the oracle statement defined above. The oracle simply applies
  the function `f : ι → F` to the query input `i : ι`,
  producing the response. -/
instance {ι : Type} : OracleInterface (OracleStatement ι F ()) := OracleInterface.instFunction

omit [DecidableEq F] in
/-- **The field-size condition of Theorem 5.1** (the `hF` hypothesis of `stir_main`):
`secpar · 2^secpar · degree² · |ι|^(7/2) / log(1/ρ) ≤ |F|`, where `ρ` is the rate of
`RS[F, ι, degree]` and `7/2` is a real exponent (`Real.rpow`).

This is a *lower* bound on the field size, matching the canonical target
`|F| = Ω(λ · 2^λ · d² · |L|^(7/2) / log(1/ρ))` recorded in `ArkLib.ProofSystem.Stir.MainThm`,
specialised to the constant `1`. A soundness theorem can only need such a lower bound. The
exponent and constant have not been re-checked against the text of [ACFY24stir].

Audit note (2026-10-28, L36): the hypothesis used to be the *upper* bound
`|F| ≤ secpar * 2 ^ secpar * degree ^ 2 * |ι| ^ (7 / 2) / log(1/ρ)`, in which `7 / 2` is
natural-number division (`= 3`), while the docstring of `stir_main` put the degree/length/log
expression into the exponent of `2`. As an upper bound it excluded the large-field regime of
the theorem, and at `secpar = 0` it forced `|F| ≤ 0`, so every front door that also assumed
`secpar = 0` had no instances (`NumericLegs.lean`). Front doors that also cap `|F|` from
above (the small-field routes) are inhabited only when the cap is compatible with this lower
bound, for instance at `secpar = 0` (`fieldSizeCondition_zero`). -/
def FieldSizeCondition (secpar : ℕ) {ι : Type} [Fintype ι] (φ : ι ↪ F) (degree : ℕ) : Prop :=
  (secpar : ℝ) * 2 ^ secpar * (degree : ℝ) ^ 2 * (Fintype.card ι : ℝ) ^ ((7 : ℝ) / 2) /
      Real.log (1 / (rate (code φ degree) : ℝ)) ≤ Fintype.card F

omit [DecidableEq F] in
/-- At `secpar = 0` the field-size condition holds for every field: its left side is `0`. -/
theorem fieldSizeCondition_zero {ι : Type} [Fintype ι] (φ : ι ↪ F) (degree : ℕ) :
    FieldSizeCondition 0 φ degree := by
  simp [FieldSizeCondition]

/-- Theorem 5.1 : STIR main theorem (front-door statement).
  Consider the following ingredients,
  a security parameter `secpar`
  a ReedSolomon code `RS[F, ι, degree]` with rate `ρ = degree/ |ι|`, where ι is a smooth domain
  a proximity parameter `δ ∈ (0, 1 - 1.05 * √ρ)`
  a folding parameter `k ≥ 4`, being a power of 2
  if `|F| ≥ secpar * 2^secpar * degree² * |ι|^(7/2) / log(1/ρ)` (`FieldSizeCondition`), then
  there exists a `vector IOPP π` for `RS` with
  - `round by round soundness error ≤ 2 ^ (- secpar)`,
  - `M = O(logₖdegree)`
  - `proof length = |ι| + Oₖ(log degree)`
  - `query complexity to input = secpar / (- log(1-δ))`
  - `query complexity to proof strings = Oₖ(log degree + secpar * log(log degree / log(1/ρ)))`

  What the Lean statement does and does not say (audit 2026-10-28, L36):
  - The body never uses `hF`; it only restricts where the front door can be stated. See
    `FieldSizeCondition` for its direction and exponent, both corrected on 2026-10-28.
  - `π` and its spec `vPSpec` are existentially quantified. Any secure-with-gap vector IOP for
    the two `stirRelation`s witnesses the statement; nothing pins `π` to the STIR verifier.
  - The complexity conjuncts constrain the free parameters `M`, `proofLen`, `qNumtoInput` and
    `qNumtoProofstr`, which are not linked to the cost of `π`. The constants `c` and `cₖ` are
    chosen after the whole instance, so the round-count, proof-length and proof-query
    conjuncts hold for arbitrary counts once the relevant logarithmic brackets are positive
    (`ComplexityLegs.lean`). They are per-instance constraints, not the uniform `O(·)` bounds
    of the paper; only the input-query conjunct constrains its count (from below).
  - The complexity conjuncts sit outside the quantifier `∀ i` of the rbr-error bound. Before
    2026-10-28 they were nested under it, so a protocol with no challenges satisfied all of
    them vacuously.
-/
def stir_main
    (secpar : ℕ) [SampleableType F]
  {ι : Type} [Fintype ι] [Nonempty ι]
  {φ : ι ↪ F} {degree : ℕ} [hsmooth : Smooth φ]
  {k proofLen qNumtoInput qNumtoProofstr : ℕ}
  (hk : ∃ p, k = 2 ^ p) (hkGe : k ≥ 4)
  (δ : ℝ≥0) (hδub : δ < 1 - 1.05 * Real.sqrt (degree / Fintype.card ι))
  (hF : FieldSizeCondition secpar φ degree) : Prop :=
  ∃ n : ℕ,
  ∃ vPSpec : ProtocolSpec.VectorSpec n,
  ∃ ε_rbr : vPSpec.ChallengeIdx → ℝ≥0,
  ∃ π : VectorIOP Unit (OracleStatement ι F) Unit vPSpec F,
  IsSecureWithGap (stirRelation degree φ 0)
                  (stirRelation degree φ δ)
                  ε_rbr π
  ∧ (∀ i, ε_rbr i ≤ (1 : ℚ≥0) / (2 ^ secpar))
  ∧ (∃ c > 0, M ≤ c * (Real.log degree / Real.log k))
  ∧ (∃ cₖ : ℕ → ℝ, proofLen ≤ (Fintype.card ι) + (cₖ k) * (Real.log degree))
  ∧ (qNumtoInput : ℝ) ≥ secpar / (-Real.log (1 - δ))
  ∧ ∃ cₖ : ℕ → ℝ, qNumtoProofstr ≤
    (cₖ k) * ((Real.log degree) +
      secpar * (Real.log ((Real.log degree) / Real.log (1/rate (code φ degree)))))
  -- STATUS (updated 2026-10-28): front-door statement with the limitations listed in the
  -- docstring. `MultiRoundAssembly.lean` constructs `stirMultiRoundIOP` (shell verifier) and the
  -- general wiring `stir_main_of_secure_vectorIOP`; `CheckingVerifier.lean` adds the checking
  -- verifier and its conditional CA/bridge routes. Within the single-domain identity-fold
  -- checking model the soundness leg is proved outright (`stir_main_of_checkingIOP_genuine`,
  -- `SubUnitRbr.lean`; `stir_main_of_checkingIOP_rep`, `RepWire.lean`). Paper-STIR folding
  -- (degree reduction) and its Johnson-regime correlated-agreement inputs are carried only by
  -- the conditional routes, and the complexity conjuncts remain per-instance constraints.

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
  `ε_fold ≤ errStar(degree₀/foldingParam₀, ρ₀, δ₀, foldingParam₀)`
  `ε_outᵢ ≤ lᵢ²/2 * (degreeᵢ/ |F| - |ιᵢ|)^s`
  `ε_shiftᵢ ≤ (1 - δ_{i-1})^repeatParam_{i-1} + errStar(degreeᵢ, ρᵢ, δᵢ, t_{i-1} + s)`
    `+ errStar(degreeᵢ/foldingParamᵢ, ρᵢ, δᵢ, foldingParamᵢ)`
  `ε_fin ≤ (1 - δ_M)^repeatParam_M`

  What the Lean statement does and does not say (audit 2026-10-28, L36):
  - `ParamConditions` requires `degreeᵢ < |ιᵢ|` (`h_smooth_lt`), so the radius windows are
    nonempty (`ParamConditions.zero_lt_one_sub_Bstar_rate_zero`); the reversed condition would
    force rate `1` and contradict `hδ₀` (`not_lt_one_sub_Bstar_rate_of_card_le`).
  - In the shift bound the repetition count `t_{i-1} + s` is the fourth argument of `errStar`,
    as in the formula above; it used to be `errStar(…, t_{i-1}) + s`.
  - The fourth argument of the fold term `errStar(d₀/k₀, ρ₀, δ₀, ·)` and of the last shift term
    `errStar(dᵢ/kᵢ, ρᵢ, δᵢ, ·)` is the folding parameter `kᵢ` (the number of functions combined
    by the fold), as in the canonical `ArkLib.ProofSystem.Stir.MainThm` target and the blueprint
    lemma `lemma:rnd_by_rnd_soundness`; it used to be the repetition parameter `tᵢ`.
  - The final-round bound on `ε_fin` is a separate conjunct. It used to sit under
    `∀ j : Fin M`, so at `M = 0` there was no final bound at all.
  - The budget shapes are transcriptions that have not been re-checked against the text of
    [ACFY24stir]; the per-round bounds constrain the free error parameters
    `ε_fold`, `ε_out`, `ε_shift`, `ε_fin` from above.
  - Budget direction (as for WHIR, audit L04): `π` must be secure at the maximum of those
    parameters. A security bound justifies every larger budget, not every smaller one, so the
    front doors that conclude this statement for arbitrary admissible `ε`s assume that security
    as a hypothesis rather than deriving it from the paper's error bounds.
  - `π` is existentially quantified: any vector IOP with `2M + 2` challenges that is
    secure-with-gap for the two `stirRelation`s at the max of these errors witnesses the
    statement; nothing pins `π` to the STIR verifier.
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
    -- `ε_fold ≤ errStar(degree₀/foldingParam₀, ρ₀, δ₀, foldingParam₀)`
      ε_fold ≤ proximityError F (P.deg / P.foldingParam 0) (rate (code (P.φ 0) P.deg))
                 (Dist.δ 0) (P.foldingParam 0)
      ∧
      -- Note here that `j : Fin M`, so we need to cast into `Fin (M + 1)` for indexing of
      -- `Dist.δ` and `P.repeatParam`. To get `j`, we use `.castSucc`, whereas to get `j + 1`,
      -- we use `.succ`.
      -- Because of the difference in indexing between the paper and the code, we essentially have
      -- `j = i - 1` compared to the paper.
      -- `ε_out_{j+1} ≤ l_{j+1}²/2 * (degree_{j+1}/ |F| - |ι_{j+1}|)^s`
      (∀ j : Fin M,
        ε_out j ≤ ((Dist.l j.succ : ℝ) ^ 2 / 2) *
          ((degree ι P j.succ : ℝ) / (Fintype.card F - Fintype.card (ι j.succ))) ^ s
        ∧
        -- `ε_shift_{j+1} ≤ (1 - δ_j)^repeatParam_j`
        -- `+ errStar(degree_{j+1}, ρ_{j+1}, δ_{j+1}, repeatParam_j + s)`
        -- `+ errStar(degree_{j+1}/foldingParam_{j+1}, ρ_{j+1}, δ_{j+1}, foldingParam_{j+1})`
        ε_shift j ≤
          (1 - Dist.δ j.castSucc) ^ (P.repeatParam j.castSucc)  +
          -- proximityError(degreeⱼ, ρ(codeⱼ), δⱼ, repeatParam_j + s), where codeⱼ = code φⱼ degreeⱼ
           proximityError F (degree ι P j.succ) (rate (code (P.φ j.succ) (degree ι P j.succ)))
            (Dist.δ j.succ) (P.repeatParam j.castSucc + s) +
          -- proximityError(degreeⱼ / foldingParamⱼ, ρ(codeⱼ), δⱼ, foldingParamⱼ)
           proximityError F ((degree ι P j.succ) / P.foldingParam j.succ)
            (rate (code (P.φ j.succ) (degree ι P j.succ)))
            (Dist.δ j.succ) (P.foldingParam j.succ))
      ∧
      -- `ε_fin ≤ (1 - δ_M)^repeatParam_M`, outside the tail quantifier so it also binds at `M = 0`
      ε_fin ≤ (1 - Dist.δ (Fin.last M)) ^ (P.repeatParam (Fin.last M))
  -- STATUS (updated 2026-10-28): front-door statement with the limitations listed in the
  -- docstring. `MultiRoundSpec.lean`, `FullChain.lean` and `MultiRoundAssembly.lean` realize the
  -- `2 * M + 2` challenge shape and the general wiring `stir_rbr_soundness_of_secure_vectorIOP`;
  -- `CheckingVerifier.lean` instantiates it with the checking verifier, conditionally on the
  -- named CA/bridge residuals (or the small-field vacuous-budget route). The per-round
  -- `proximityError` obligations remain tied to the BCIKS/STIR proximity-gap residuals in the
  -- Johnson / sqrt-rho list-decoding regime.

end RBRSoundness

end StirIOP

/- Axiom audit for the STIR main theorem residual front doors (#24). -/
#print axioms StirIOP.stir_main
#print axioms StirIOP.stir_rbr_soundness
/- Parameter-regime checks added by the 2026-10-28 audit repair (L36). -/
#print axioms StirIOP.not_lt_one_sub_Bstar_rate_of_card_le
#print axioms StirIOP.ParamConditions.rate_lt_one
#print axioms StirIOP.ParamConditions.zero_lt_one_sub_Bstar_rate
#print axioms StirIOP.ParamConditions.zero_lt_one_sub_Bstar_rate_zero
#print axioms StirIOP.fieldSizeCondition_zero
