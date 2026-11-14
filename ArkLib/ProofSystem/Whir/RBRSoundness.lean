/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das (Least Authority), Alexander Hicks
-/

import ArkLib.Extensions.Data.CodingTheory.ReedSolomon
import ArkLib.Extensions.Data.CodingTheory.ListDecodability
import ArkLib.Extensions.OracleReduction.VectorIOR
import ArkLib.ProofSystem.Whir.BlockRelDistance
import ArkLib.ProofSystem.Whir.MutualCorrAgreement
import ArkLib.ProofSystem.Whir.ProximityGen
import ArkLib.ProofSystem.Whir.RbrBudgetAccounting

/-!
# Round by round soundness theorem

This file states the round by round soundness theorem of the WHIR IOPP (Theorem 5.2 of
Section 5 of [ACFY24]) as a `Prop`, `whir_rbr_soundness`, about an explicitly supplied
protocol. Nothing here proves it, and ArkLib does not yet contain a protocol that implements
Construction 5.1 (see the docstring of `whir_rbr_soundness`).

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24]

## Implementation notes (corrections from paper)

- Theorem 5.2:
-- `(δᵢ, l_{i,s})`-list decodable in place of `(l_{i,s}, δᵢ)`-list decodable
-- proximity generators should be defined for `C^(0),...,C^(k)` in place of `C^(1),...,C^(k)`

- Theorem 5.2 holds for `l = 2` as can be seen with `BStar(..,2)` and `errStar(..,2,..)`
  and so `Gen(l,alpha) = {1, alpha,...., alpha^{l-1}}` also corresponds to `l = 2`
  and not for a generic l.

- In Construction 5.1 and Theorem 5.2,
  we use M + 1 iterations instead of M, for ease of representation in Lean:
  rounds are indexed by `Fin (M + 1)`, round `0` is the initial sumcheck and round `i.succ`
  (`i : Fin M`) is the paper's main-loop iteration `i + 1`.

## Statement shape

`whir_rbr_soundness` takes each per-round error as a budget that must dominate the analytic
Theorem 5.2 bound (`bound ≤ ε`), constrains the out-of-domain and main-round folding errors only
on the main rounds, uses the shift term `ℓ_{i+1,0} · (t_i + 1) / |F|`, and takes the protocol
`π` as an explicit argument instead of quantifying over it existentially.

## Tags
Open question: should we aim to add tags?
-/
namespace WhirIOP

open BigOperators BlockRelDistance.Generic MutualCorrAgreement Generator Finset
     ListDecodable NNReal ReedSolomon

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {M : ℕ} (ι : Fin (M + 1) → Type) [∀ i : Fin (M + 1), Fintype (ι i)]

/-- ** Per‑round protocol parameters. **
For a fixed depth `M`, the reduction runs `M + 1` rounds.
In round `i ∈ {0,…,M}` we fold by a factor `foldingParamᵢ`,
evaluate on the point set `ιᵢ` through the embedding `φᵢ : ιᵢ ↪ F`,
and repeat certain proximity checks `repeatParamᵢ` times. -/
structure Params (F : Type) where
  foldingParam : Fin (M + 1) → ℕ
  varCount : Fin (M + 1) → ℕ
  φ : (i : Fin (M + 1)) → (ι i) ↪ F
  repeatParam : Fin (M + 1) → ℕ

/-- ** Conditions that protocol parameters must satisfy. **
  h_m : m = varCount₀
  h_sumkLt : ∑ i : Fin (M + 1), foldingParamᵢ ≤ m
  h_varCount_i : ∀ i : Fin (M + 1), i ≠ 0, varCountᵢ = m - ∑ j < i foldingParamⱼ
  h_smooth : each φᵢ must embed a smooth evaluation domain
  h_repeatPLt : ∀ i : Fin (M + 1), repeatParamᵢ ≤ |ιᵢ| -/
structure ParamConditions (P : Params ι F) where
  m : ℕ -- m = P.varCount 0
  h_m : m = P.varCount 0
  h_sumkLt : ∑ i : Fin (M + 1), P.foldingParam i ≤ m
  h_varCount_i : ∀ i : Fin (M + 1),
    P.varCount i = m - ∑ j : Fin i, P.foldingParam (Fin.castLT j (Nat.lt_trans j.isLt i.isLt))
  h_smooth : ∀ i : Fin (M + 1), Smooth (P.φ i)
  h_repeatPLt : ∀ i : Fin (M + 1), P.repeatParam i ≤ Fintype.card (ι i)

/-- `GenMutualCorrParams` binds together a set of smooth ReedSolomon codes
  `C_{i : M + 1, j : foldingParamᵢ + 1} = RS[F, ιᵢ^(2ʲ), (varCountᵢ - j)]` with
  `Gen_α_ij` which is a proximity generator with mutual correlated agreement
  for `C_ij` with proximity parameters `BStar_ij` and `errStar_ij`.

  Additionally, it includes the condition that
    C_ij is `(δᵢ, dist_ij)`-list decodeable,
  where `δᵢ = 1 - max_{j : foldingParamᵢ + 1} BStar(C_ij,2)`
-/
-- NOTE: fix this after fixing folding
class GenMutualCorrParams (P : Params ι F) (S : ∀ i : Fin (M + 1), Finset (ι i)) where

  δ : Fin (M + 1) → ℝ≥0
  dist : (i : Fin (M + 1)) → Fin ((P.foldingParam i) + 1) → ℝ≥0

-- φ i j : ιᵢ^(2ʲ) ↪ F
  φ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1), (indexPowT (S i) (P.φ i) j) ↪ F

  inst1 : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1), Fintype (indexPowT (S i) (P.φ i) j)
  inst2 : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
    Nonempty (indexPowT (S i) (P.φ i) j)
  inst3 : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
    DecidableEq (indexPowT (S i) (P.φ i) j)
  inst4 : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1), Smooth (φ i j)

  parℓ_type : ∀ i : Fin (M + 1), ∀ _ : Fin ((P.foldingParam i) + 1), Type
  inst5 : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1), Fintype (parℓ_type i j)

  exp : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1), (parℓ_type i j) ↪ ℕ

-- this ensures that Gen_α_ij is a proxmity generator for C_ij = RS[F, ιᵢ^(2^j), (varCountᵢ - j)]
-- wrt proximity function Gen_α (α,l) = {1,α²,...,α^{parℓ-1}}
  Gen_α : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
    ProximityGenerator (indexPowT (S i) (P.φ i) j) F :=
      fun i j => RSGenerator.genRSC (parℓ_type i j) (φ i j) (P.varCount i - j) (exp i j)

  inst6 : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1), Fintype (Gen_α i j).parℓ

  BStar : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
    (Set ((indexPowT (S i) (P.φ i) j) → F)) → Type → ℝ≥0
  errStar : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
    (Set ((indexPowT (S i) (P.φ i) j) → F)) → Type → ℝ → ENNReal

  C : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1), Set ((indexPowT (S i) (P.φ i) j) → F)
  hcode : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1), (C i j) = (Gen_α i j).C

  h : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
    hasMutualCorrAgreement (Gen_α i j)
      (BStar i j (C i j) (Gen_α i j).parℓ)
      (errStar i j (C i j) (Gen_α i j).parℓ)

  hℓ_bound : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
    Fintype.card (Gen_α i j).parℓ = 2
  hℓ_bound' : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
    Fintype.card (parℓ_type i j) = 2

  hδLe : ∀ i : Fin (M + 1),
    (δ i) ≤ 1 - Finset.univ.sup (fun j => BStar i j (C i j) (Gen_α i j).parℓ)

  hlistDecode : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
    listDecodable (C i j) (δ i) (dist i j)

section RBR

open NNRat OracleComp OracleSpec ProtocolSpec VectorIOP

/-- `OracleStatement` defines the oracle message type for a multi-indexed setting:
  given base input type `ι`, and field `F`, the output type at each index
  is a function `ι → F` representing an evaluation over `ι`.
-/
@[reducible]
def OracleStatement (ι F : Type) : Unit → Type :=
    fun _ => ι → F

/-- Provides a default OracleInterface instance that leverages
  the oracle statement defined above. The oracle simply applies
  the function `f : ι → F` to the query input `i : ι`,
  producing the response. -/
instance {ι : Type} : OracleInterface (OracleStatement ι F ()) := OracleInterface.instFunction

/-- WHIR relation: the oracle's output is δᵣ-close to a codeword of a smooth ReedSolomon code
with number of variables at most `varCount` over domain `φ`, within error `err`.
-/
def whirRelation
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} [Fintype ι] [Nonempty ι]
    (varCount : ℕ) (φ : ι ↪ F) [Smooth φ] (err : ℝ≥0)
    : Set ((Unit × ∀ i, (OracleStatement ι F i)) × Unit) :=
  { ⟨⟨_, oracle⟩, _⟩ | δᵣ(oracle (), smoothCode φ varCount) ≤ err }

/-- Shared WHIR statement with the same challenge pin and numerical bounds for both RBR games. -/
def whirRbrSoundnessWith (fixedPrefix : Bool)
    [SampleableType F] {d dstar : ℕ}
  -- P : set of M + 1 parameters including foldingParamᵢ, varCountᵢ, φᵢ, repeatParamᵢ,
  -- where foldingParamᵢ > 0
    {P : Params ι F} {S : ∀ i : Fin (M + 1), Finset (ι i)}
  -- hParams : a set of conditions that parameters in P must satisfy
  -- h : a set of smooth ReedSolomon codes C_ij bundled with its proximity generators
  -- and condition for list decodeability
    {hParams : ParamConditions ι P} {h : GenMutualCorrParams ι P S}
    {m_0 : ℕ} (hm_0 : m_0 = P.varCount 0) {σ₀ : F}
    {wPoly₀ : MvPolynomial (Fin (m_0 + 1)) F} {δ : ℝ≥0}
    [Smooth (P.φ 0)] [Nonempty (ι 0)]
    [∀ i : Fin (M + 1), Fact (0 < P.foldingParam i)]
    (ε_fold : (i : Fin (M + 1)) → Fin (P.foldingParam i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    (h_fold_0 :
        let maxDeg := (Finset.univ : Finset (Fin m_0)).sup (fun i => wPoly₀.degreeOf (Fin.succ i))
        let dstar := 1 + (wPoly₀.degreeOf 0) + maxDeg
        let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
          Fintype (indexPowT (S 0) (P.φ 0) j) := h.inst1 0
        let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
          Nonempty (indexPowT (S 0) (P.φ 0) j) := h.inst2 0
        let errStar_0 j := h.errStar 0 j (h.C 0 j) (h.Gen_α 0 j).parℓ (h.δ 0)
        ∀ j : Fin (P.foldingParam 0),
          ((dstar * (h.dist 0 j.castSucc)) / Fintype.card F) + (errStar_0 j.succ) ≤ ε_fold 0 j)
    (h_out :
        ∀ i : Fin M,
          2^(P.varCount i.succ) * (h.dist i.succ 0)^2 / (2 * Fintype.card F) ≤ ε_out i.succ)
    (h_shift :
        ∀ i : Fin M,
          (1 - (h.δ i.castSucc))^(P.repeatParam i.castSucc)
            + (h.dist i.succ 0) * (P.repeatParam i.castSucc + 1) / Fintype.card F ≤ ε_shift i)
    (h_fold_i :
        let maxDeg := (Finset.univ : Finset (Fin m_0)).sup (fun i => wPoly₀.degreeOf (Fin.succ i))
        let dstar := 1 + (wPoly₀.degreeOf 0) + maxDeg
        let d := max dstar 3
        let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
          Fintype (indexPowT (S i) (P.φ i) j) := h.inst1
        let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
          Nonempty (indexPowT (S i) (P.φ i) j) := h.inst2
        let errStar i j := h.errStar i j (h.C i j) (h.Gen_α i j).parℓ (h.δ i)
        ∀ i : Fin M, ∀ j : Fin (P.foldingParam i.succ),
          d * (h.dist i.succ j.castSucc) / Fintype.card F + errStar i.succ j.succ
            ≤ ε_fold i.succ j)
    (h_fin :
        (1 - h.δ (Fin.last M))^(P.repeatParam (Fin.last M)) ≤ ε_fin)
    {n : ℕ} (vPSpec : ProtocolSpec.VectorSpec n)
    (π : VectorIOP Unit (OracleStatement (ι 0) F) Unit vPSpec F) : Prop :=
    Fintype.card (vPSpec.ChallengeIdx) = 2 * M + 2 ∧
      (let ε_rbr : vPSpec.ChallengeIdx → ℝ≥0 := fun _ =>
          Issue113WHIR.epsRbr (fp := P.foldingParam) ε_fold ε_out ε_shift ε_fin
        let completeRelation := whirRelation m_0 (P.φ 0) 0
        let soundRelation := whirRelation m_0 (P.φ 0) (h.δ 0)
        if fixedPrefix then
          VectorIOP.IsSecureWithGap completeRelation soundRelation ε_rbr π
        else
          VectorIOP.IsSecureWithGapAveraged completeRelation soundRelation ε_rbr π)

/-- Theorem 5.2: **round-by-round soundness of the WHIR Vector IOPP**, stated for an explicitly
  supplied protocol `π`. This is a `Prop`-valued statement, not a proved theorem.

  `whir_rbr_soundness … h_fold_0 h_out h_shift h_fold_i h_fin vPSpec π` says that `vPSpec` has
  `2 * M + 2` challenge slots and that `π` is `IsSecureWithGapAveraged` (perfectly complete for exact
  codewords, round-by-round knowledge sound for `whirRelation m_0 (P.φ 0) (h.δ 0)`) at the
  constant per-challenge budget `max (ε_fold, ε_out, ε_shift, ε_fin)`.

  **Budget direction.** Each hypothesis requires the chosen error to *dominate* the analytic
  Theorem 5.2 bound (`bound ≤ ε`): an upper bound on a failure probability justifies every larger
  budget and no smaller one. Round-by-round knowledge soundness is monotone in the budget, so
  asking for every dominating budget is the same as asking for the analytic bounds themselves
  when they are finite. An earlier revision required `ε ≤ bound`, which demanded security at
  every smaller budget, including zero.

  **Per-round bounds.** Round `0` is the initial sumcheck and round `i.succ` (`i : Fin M`) is the
  paper's main-loop iteration `i + 1`; `ℓ` is `h.dist`, `t` is `P.repeatParam`, `δ` is `h.δ`,
  `m` is `P.varCount` and `err*` is `h.errStar` (with `parℓ` of size `2`).
  * `h_fold_0`: `d* · ℓ_{0,j} / |F| + err*(C_{0,j+1}, δ_0) ≤ ε_fold 0 j`.
  * `h_out`: `2^{m_{i+1}} · ℓ_{i+1,0}² / (2|F|) ≤ ε_out i.succ`, on main rounds only. Round `0`
    has no out-of-domain sample (the transcript scaffold `PaperTranscriptSlot` also has
    out-of-domain slots only for the main rounds), so `ε_out 0` is unconstrained; it can only
    enlarge the budget.
  * `h_shift`: `(1 - δ_i)^{t_i} + ℓ_{i+1,0} · (t_i + 1) / |F| ≤ ε_shift i`.
  * `h_fold_i`: `d · ℓ_{i+1,j} / |F| + err*(C_{i+1,j+1}, δ_{i+1}) ≤ ε_fold i.succ j`, on main
    rounds only, so round `0` keeps the `d*` bound of `h_fold_0` rather than `d = max d* 3`.
  * `h_fin`: `(1 - δ_M)^{t_M} ≤ ε_fin`.
  These were re-derived from the per-round arguments, not re-checked line by line against the
  ePrint text: a cheating sumcheck message of degree below `d` (`d*` in round `0`) agrees with
  the honest message of a fixed list codeword at a random point with probability at most
  `d / |F|` (union over the `ℓ` list codewords, plus the folding error `err*`); two distinct
  list codewords agree at a random out-of-domain point with probability at most `2^m / |F|`
  (union over the `ℓ² / 2` pairs); in the shift round all `t` queries avoid the disagreement set
  with probability at most `(1 - δ)^t`, and the `γ`-combination of the `t + 1` new constraints
  (a polynomial of degree at most `t + 1` in `γ`) fails for a fixed list codeword with
  probability at most `(t + 1) / |F|`. An earlier revision wrote the shift term as
  `(ℓ · t + 1) / |F|`.

  **Protocol identification.** An earlier revision quantified existentially over `π` and pinned
  only the challenge count. That does not exclude a verifier that reads the whole input oracle,
  checks exact code membership and ignores its challenges, so even a proof would not have
  certified WHIR. Here `π` is an explicit argument: the statement certifies WHIR only when `π`
  is a protocol that implements Construction 5.1. None exists in ArkLib yet. `whirVectorIOP`
  (`Whir/Protocol.lean`) accepts every transcript, and the checked verifier
  `Whir302Checked.whirVerifyChecked` never queries the input oracle, so all-zero prover messages
  pass all of its checks (`Whir302Checked.whirCheckingBool_allZero`). The `2 * M + 2` count is
  only a cardinality constraint, inherited from an aggregated-challenge reading of
  Construction 5.1: the unbundled paper transcript `whirPaperTranscriptVectorSpec` has
  `(∑ i, P.foldingParam i) + 2 * M + 1` challenges (`Whir/ChallengeCardPin.lean`), so that
  conjunct holds there only when the folding parameters sum to `1`.

  **Status: open.** A proof for a protocol implementing Construction 5.1 needs that construction,
  the folding list-decoding lemmas (`Whir/Folding.lean`, L4.20–4.23) and the MCA `errStar` bounds
  (Corollary 4.11, open in the `√ρ` regime). In ABF26 terms, `errStar` corresponds to `epsMCA`
  (Def 4.3) and the folding lemmas to ABF26 T3.4 specialized to FRS. -/
def whir_rbr_soundness :=
  @whirRbrSoundnessWith F _ _ _ M ι _ false

/-- The same WHIR challenge pin and numerical bounds, with a fixed-prefix security package. -/
def whir_rbr_soundness_fixedPrefix :=
  @whirRbrSoundnessWith F _ _ _ M ι _ true


end RBR

end WhirIOP
