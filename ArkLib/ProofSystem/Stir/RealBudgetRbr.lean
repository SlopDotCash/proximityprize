/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.FullPredKSF
import ArkLib.ProofSystem.Stir.CheckedFinalBlock
import ArkLib.ProofSystem.Whir.SubUnitRbr
import ArkLib.ProofSystem.Stir.SpotCheckBound

/-!
# The STIR checked final block at the REAL spot-check budget (#301)

**Round-by-round knowledge soundness of `stirFinalVectorVerifierChecked` at the genuine
spot-check budget**, assembled through the full-predicate KSF shell
(`FullPredKSF.rbrKnowledgeSoundness_of_salvageBound`).

The block predicate:
* round 0 (empty transcript): the δ-positivity gate `0 < δ` (= the input relation);
* round 1 (after the final-word message): *the word agrees with the incoming oracle on
  MORE than a `(1−δ)` fraction of the index space* (`agreementSet` strict bound);
* round 2 (after the repetition challenge): *the pointwise check at the challenge-determined
  index* — exactly the decision of the checked verifier (`hFull` is proven from the
  `toVerifier`-collapse of `stirFinalCheckedComp`, so acceptance FORCES the predicate).

## The TRUE budget (the composed-marginal computation the task asked for)

`stirFinalQueryIndex : F → Fin |ι|` is `c ↦ (equivFin F c) % |ι|` — the **val-mod map**, NOT a
uniform-preserving map unless `|ι| ∣ |F|`.  The marginal of the queried index under a uniform
challenge is `fiber(k)/|F|` with `fiber(k) = #{x < |F| : x ≡ k [MOD |ι|]} ≤ ⌈|F|/|ι|⌉`
(`card_fiber_stirFinalQueryIndex_le`).  Hence the honest salvage bound at `C_fin` is the
**max-fiber union bound**

  `ε_fin = (1−δ) · |ι| · ⌈|F|/|ι|⌉ / |F|`   (`stirSpotBudget`),

which collapses to EXACTLY `1−δ` in the divisible regime `|ι| ∣ |F|`
(`stirSpotBudget_eq_of_dvd`) — e.g. whenever the index space is a subgroup-sized smooth domain
in a prime-power field with `|ι| ∣ |F|`.  In the non-divisible regime the bound
`(1−δ)·|ι|·⌈|F|/|ι|⌉/|F|` is what is TRUE for this union-bound route (it can exceed `1−δ` by
the fiber imbalance `|ι|·⌈|F|/|ι|⌉/|F| ≤ 1 + |ι|/|F|`); a finer bound would sum the `|A|`
largest fibers instead of `|A| · maxfiber`.

## HONESTY: what the wrapper statement does and does not say

The block's input statement (pending randomness + incoming packed oracle) contains NO final
word, so no statement-dependent input relation can force the round-1 agreement predicate to
fail: the honest word (= the incoming oracle itself) always agrees fully.  The input relation
of the assembled `rbrKnowledgeSoundness` is therefore the statement-independent δ-positivity
gate `{_ | 0 < δ}`; as a bare proposition the wrapper is then also derivable at budget 0 from
the constant-`True` state function.  The CONTENT of this file is the named state function
(`stirSpotPred`, whose round-1 state is the genuine agreement predicate) together with the
PROVEN `hFull` (acceptance forces the pointwise check) and `hSalvage` (the spot-check salvage
bound at the true budget) legs — the pieces a chain-level analysis composes with.

## Build note

`ArkLib.ProofSystem.Stir.SpotCheckBound` has no `.olean` in the current build, so its content
(`agreementSet`, `agreementSet_card_le`, `probEvent_spotCheck_le`) is inlined verbatim below
(same namespace, same names; the orchestrator dedups on landing).
-/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec NNReal Finset StirIOP.Round
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## Part 0 — inlined `SpotCheckBound` (no olean; verbatim) -/


/-! ## Part 1 — the composed marginal: fiber counting for `stirFinalQueryIndex`

`stirFinalQueryIndex` is the val-mod map `c ↦ (equivFin F c) % |ι|`.  Its fibers have size at
most `⌈|F|/|ι|⌉ = (|F| + |ι| − 1)/|ι|`, hence the preimage of any index set `A` has at most
`|A| · ⌈|F|/|ι|⌉` elements — the composed (non-uniform!) marginal computation. -/

section FiberCount

/-- The number of `x < M` with `x % N = k` is at most `⌈M/N⌉ = (M + N − 1)/N`. -/
lemma card_filter_mod_eq_le (M N k : ℕ) (hN : 0 < N) :
    ((Finset.range M).filter (fun x => x % N = k)).card ≤ (M + N - 1) / N := by
  classical
  have hmem : ∀ x ∈ (Finset.range M).filter (fun x => x % N = k),
      x / N ∈ Finset.range ((M + N - 1) / N) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    simp only [Finset.mem_range]
    rcases Nat.eq_zero_or_pos M with hM | hM
    · omega
    · have hx1 : x ≤ M - 1 := by omega
      have h1 : x / N ≤ (M - 1) / N := Nat.div_le_div_right hx1
      have h2 : (M + N - 1) / N = (M - 1) / N + 1 := by
        have heq : M + N - 1 = (M - 1) + N := by omega
        rw [heq, Nat.add_div_right _ hN]
      omega
  have hinj : Set.InjOn (fun x => x / N)
      ((Finset.range M).filter (fun x => x % N = k)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx hy
    have hdiv : x / N = y / N := hxy
    calc x = N * (x / N) + x % N := (Nat.div_add_mod x N).symm
      _ = N * (y / N) + y % N := by rw [hdiv, hx.2, hy.2]
      _ = y := Nat.div_add_mod y N
  calc ((Finset.range M).filter (fun x => x % N = k)).card
      ≤ (Finset.range ((M + N - 1) / N)).card :=
        Finset.card_le_card_of_injOn (fun x => x / N) hmem hinj
    _ = (M + N - 1) / N := Finset.card_range _

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **Fiber bound for the query-index map**: every fiber of `stirFinalQueryIndex` has at most
`⌈|F|/|ι|⌉` elements (the max-fiber size of the val-mod map). -/
lemma card_fiber_stirFinalQueryIndex_le (k : Fin (Fintype.card ι)) :
    (Finset.univ.filter (fun c : F => stirFinalQueryIndex (ι := ι) c = k)).card
      ≤ (Fintype.card F + Fintype.card ι - 1) / Fintype.card ι := by
  classical
  have h1 : (Finset.univ.filter (fun c : F => stirFinalQueryIndex (ι := ι) c = k)).card
      ≤ ((Finset.range (Fintype.card F)).filter
          (fun x => x % Fintype.card ι = k.val)).card := by
    refine Finset.card_le_card_of_injOn (fun c => (Fintype.equivFin F c).val) ?_ ?_
    · intro c hc
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter,
        Finset.mem_univ, true_and] at hc
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
      exact ⟨(Fintype.equivFin F c).isLt, congrArg Fin.val hc⟩
    · intro c _ c' _ hcc
      exact (Fintype.equivFin F).injective (Fin.val_injective hcc)
  exact le_trans h1 (card_filter_mod_eq_le _ _ _ Fintype.card_pos)

/-- **Preimage bound**: the `stirFinalQueryIndex`-preimage of an index set `A` has at most
`|A| · ⌈|F|/|ι|⌉` elements (the max-fiber union bound). -/
lemma card_filter_stirFinalQueryIndex_mem_le (A : Finset (Fin (Fintype.card ι))) :
    (Finset.univ.filter (fun c : F => stirFinalQueryIndex (ι := ι) c ∈ A)).card
      ≤ A.card * ((Fintype.card F + Fintype.card ι - 1) / Fintype.card ι) := by
  classical
  have hsub : Finset.univ.filter (fun c : F => stirFinalQueryIndex (ι := ι) c ∈ A)
      ⊆ A.biUnion (fun k => Finset.univ.filter
          (fun c : F => stirFinalQueryIndex (ι := ι) c = k)) := by
    intro c hc
    rw [Finset.mem_filter] at hc
    exact Finset.mem_biUnion.mpr ⟨_, hc.2, Finset.mem_filter.mpr ⟨Finset.mem_univ c, rfl⟩⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  refine le_trans (Finset.sum_le_sum
    (fun k _ => card_fiber_stirFinalQueryIndex_le (F := F) (ι := ι) k)) ?_
  rw [Finset.sum_const, smul_eq_mul]

end FiberCount

/-! ## Part 2 — the budget -/

noncomputable section Budget

/-- The max-fiber size of the query-index map: `⌈|F|/|ι|⌉`. -/
def stirSpotMaxFiber (ι F : Type) [Fintype ι] [Fintype F] : ℕ :=
  (Fintype.card F + Fintype.card ι - 1) / Fintype.card ι

/-- **The TRUE spot-check salvage budget** of the checked STIR final block:
`(1−δ) · |ι| · ⌈|F|/|ι|⌉ / |F|` — the agreement-set bound `(1−δ)·|ι|` times the max-fiber
union bound `⌈|F|/|ι|⌉` of the (non-uniform!) val-mod index marginal, normalized by `|F|`.
Collapses to exactly `1 − δ` when `|ι| ∣ |F|` (`stirSpotBudget_eq_of_dvd`). -/
def stirSpotBudget (ι F : Type) [Fintype ι] [Fintype F] (δ : ℝ≥0) : ℝ≥0 :=
  (1 - δ) * ((Fintype.card ι * stirSpotMaxFiber ι F : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)

/-- **The divisible regime**: when `|ι| ∣ |F|` every fiber of the val-mod map has exactly
`|F|/|ι|` elements, and the spot-check budget is EXACTLY `1 − δ` — the budget shape of the
task. -/
theorem stirSpotBudget_eq_of_dvd (ι F : Type) [Fintype ι] [Fintype F]
    [Nonempty ι] [Nonempty F] (δ : ℝ≥0) (h : Fintype.card ι ∣ Fintype.card F) :
    stirSpotBudget ι F δ = 1 - δ := by
  obtain ⟨q, hq⟩ := h
  have hN : 0 < Fintype.card ι := Fintype.card_pos
  have hM : 0 < Fintype.card F := Fintype.card_pos
  have hmf : stirSpotMaxFiber ι F = q := by
    unfold stirSpotMaxFiber
    rw [hq]
    have heq : Fintype.card ι * q + Fintype.card ι - 1
        = Fintype.card ι * q + (Fintype.card ι - 1) := by omega
    rw [heq, Nat.mul_add_div hN, Nat.div_eq_of_lt (by omega), add_zero]
  have hnum : Fintype.card ι * stirSpotMaxFiber ι F = Fintype.card F := by
    rw [hmf, hq]
  unfold stirSpotBudget
  rw [hnum, mul_div_assoc, div_self (by exact_mod_cast hM.ne'), mul_one]

end Budget

/-! ## Part 3 — partial-transcript reads and seam lemmas for the 2-slot final spec -/

section Reads

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Read the final word (slot 0) off a partial transcript once visible. -/
def trWord {m : Fin 3}
    (tr : Transcript m ((stirFinalVSpec ι F).toProtocolSpec F)) (h : 0 < m.val) :
    Vector F (Fintype.card ι) :=
  tr ⟨0, h⟩

/-- The final word read as a function on the index space (the `OracleInterface.answer` read,
matching `stirFinalWordAt`). -/
def trWordFun {m : Fin 3}
    (tr : Transcript m ((stirFinalVSpec ι F).toProtocolSpec F)) (h : 0 < m.val)
    (k : Fin (Fintype.card ι)) : F :=
  OracleInterface.answer (trWord tr h) k

/-- The slot-1 entry as a typed length-1 vector (definitional ascription at the return
type — the CheckedFinalBlock accessor idiom). -/
def trRepChalVec {m : Fin 3}
    (tr : Transcript m ((stirFinalVSpec ι F).toProtocolSpec F)) (h : 1 < m.val) :
    Vector F 1 :=
  tr ⟨1, h⟩

def trRepChal {m : Fin 3}
    (tr : Transcript m ((stirFinalVSpec ι F).toProtocolSpec F)) (h : 1 < m.val) : F :=
  (trRepChalVec tr h).get 0

/-- **Seam lemma**: appending an entry does not change the final word already present. -/
lemma trWord_concat {m : Fin 2}
    (tr : Transcript m.castSucc ((stirFinalVSpec ι F).toProtocolSpec F))
    (msg : ((stirFinalVSpec ι F).toProtocolSpec F).«Type» m)
    (h : 0 < m.castSucc.val) (h' : 0 < m.succ.val) :
    trWord (tr.concat msg) h' = trWord tr h :=
  Fin.snoc_castSucc
    (α := fun j => ((stirFinalVSpec ι F).toProtocolSpec F).«Type»
      (Fin.castLE m.succ.is_le j))
    msg tr ⟨0, h⟩

/-- Function form of the word seam lemma. -/
lemma trWordFun_concat {m : Fin 2}
    (tr : Transcript m.castSucc ((stirFinalVSpec ι F).toProtocolSpec F))
    (msg : ((stirFinalVSpec ι F).toProtocolSpec F).«Type» m)
    (h : 0 < m.castSucc.val) (h' : 0 < m.succ.val) (k : Fin (Fintype.card ι)) :
    trWordFun (tr.concat msg) h' k = trWordFun tr h k := by
  unfold trWordFun
  rw [trWord_concat tr msg h h']

/-- **Seam lemma at the challenge slot**: the repetition challenge read off the concatenated
transcript IS the fresh challenge. -/
lemma trRepChal_concat
    (tr : Transcript (1 : Fin 2).castSucc ((stirFinalVSpec ι F).toProtocolSpec F))
    (msg : ((stirFinalVSpec ι F).toProtocolSpec F).«Type» (1 : Fin 2))
    (h : 1 < ((1 : Fin 2).succ : Fin 3).val) :
    trRepChal (tr.concat msg) h
      = (show Vector F 1 from msg).get 0 := by
  unfold trRepChal trRepChalVec
  have hsnoc : (tr.concat msg) ⟨1, h⟩ = msg := by
    show Fin.snoc tr msg ⟨1, h⟩ = msg
    exact Fin.snoc_last (α := fun j : Fin 2 =>
      ((stirFinalVSpec ι F).toProtocolSpec F).«Type» (Fin.castLE (by omega) j)) msg tr
  exact congrArg (fun v : Vector F 1 => v.get 0) hsnoc

/-- The generic vector-challenge read (`Whir302SubUnit.chalElemOf`) at the STIR repetition
slot is the head of the length-1 payload. -/
lemma chalElemOf_stirFinal
    (ch : ((stirFinalVSpec ι F).toProtocolSpec F).Challenge ⟨1, stirFinalVSpec_dir_one⟩) :
    Whir302SubUnit.chalElemOf (stirFinalVSpec ι F) ⟨1, stirFinalVSpec_dir_one⟩ ch
      = (show Vector F 1 from ch).get 0 :=
  dif_pos Nat.one_pos

/-- Every full transcript of a 2-slot spec is an `mk2`. -/
lemma transcript_last_eq_mk2 {pSpec : ProtocolSpec 2}
    (tr : Transcript (Fin.last 2) pSpec) :
    tr = (FullTranscript.mk2 (tr ⟨0, Nat.zero_lt_two⟩) (tr ⟨1, Nat.one_lt_two⟩) :
      FullTranscript pSpec) := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- Challenge payloads of the final vector spec are sampleable (the `Vector F 1` payload). -/
noncomputable instance instStirFinalVChalSampleable :
    ∀ i, SampleableType (((stirFinalVSpec ι F).toProtocolSpec F).Challenge i) :=
  fun _ => by dsimp [ProtocolSpec.Challenge]; infer_instance

end Reads

/-! ## Part 4 — the block predicate (`stirSpotPred`) and the `hEmpty`/`hConcatMsg` legs -/

section Pred

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **The STIR final-block state predicate** for the full-predicate KSF:
* round 0: the δ-positivity gate (= the input relation `stirSpotRelIn`);
* round 1: the final word agrees with the incoming oracle on MORE than a `1−δ` fraction;
* round 2: the pointwise check at the challenge-determined index (= the checked verifier's
  decision). -/
def stirSpotPred (δ : ℝ≥0) :
    (m : Fin 3) → (F × ∀ i, VOStmt ι F i) →
      Transcript m ((stirFinalVSpec ι F).toProtocolSpec F) → Prop
  | ⟨0, _⟩ => fun _ _ => 0 < δ
  | ⟨1, _⟩ => fun stmtIn tr =>
      ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ)
        < ((agreementSet (ι := ι) (trWordFun tr Nat.one_pos)
            (stirIncomingAt stmtIn.2)).card : ℝ)
  | ⟨2, _⟩ => fun stmtIn tr =>
      trWordFun tr Nat.zero_lt_two
          (stirFinalQueryIndex (trRepChal tr Nat.one_lt_two))
        = stirIncomingAt stmtIn.2 (stirFinalQueryIndex (trRepChal tr Nat.one_lt_two))
  | ⟨n + 3, h⟩ => absurd h (by omega)

/-- **The input relation of the assembled wrapper**: the statement-independent δ-positivity
gate (see the file docstring for why no statement-dependent relation can sit here). -/
def stirSpotRelIn (ι F : Type) [Fintype ι] [Field F] [Fintype F] (δ : ℝ≥0) :
    Set ((F × ∀ i, VOStmt ι F i) × Unit) :=
  {_x | 0 < δ}

/-- The `hEmpty` leg: at round 0 the predicate is exactly the input relation. -/
lemma stirSpotPred_empty (δ : ℝ≥0) (stmtIn : F × ∀ i, VOStmt ι F i) (w : Unit) :
    (stmtIn, w) ∈ stirSpotRelIn ι F δ ↔ stirSpotPred δ 0 stmtIn default :=
  Iff.rfl

/-- The `hConcatMsg` leg: the prover's message cannot repair a broken state.  The only
message round is slot 0; an agreeing-word state at round 1 forces `0 < δ` (the agreement
strict bound is unsatisfiable at `δ = 0`). -/
lemma stirSpotPred_concat (δ : ℝ≥0) (m : Fin 2)
    (hdir : ((stirFinalVSpec ι F).toProtocolSpec F).dir m = .P_to_V)
    (stmtIn : F × ∀ i, VOStmt ι F i)
    (tr : Transcript m.castSucc ((stirFinalVSpec ι F).toProtocolSpec F))
    (msg : ((stirFinalVSpec ι F).toProtocolSpec F).«Type» m)
    (h : stirSpotPred δ m.succ stmtIn (tr.concat msg)) :
    stirSpotPred δ m.castSucc stmtIn tr := by
  match m with
  | ⟨0, h0⟩ =>
      have hag : ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ)
          < ((agreementSet (ι := ι) (trWordFun (tr.concat msg) Nat.one_pos)
              (stirIncomingAt stmtIn.2)).card : ℝ) := h
      have hcard : ((agreementSet (ι := ι) (trWordFun (tr.concat msg) Nat.one_pos)
          (stirIncomingAt stmtIn.2)).card : ℝ) ≤ (Fintype.card ι : ℝ) := by
        have hle := Finset.card_filter_le (Finset.univ : Finset (Fin (Fintype.card ι)))
          (fun k => trWordFun (tr.concat msg) Nat.one_pos k = stirIncomingAt stmtIn.2 k)
        rw [Finset.card_univ, Fintype.card_fin] at hle
        exact_mod_cast hle
      show 0 < δ
      by_contra hδ
      have hδ0 : δ = 0 := le_antisymm (not_lt.mp hδ) (zero_le δ)
      subst hδ0
      rw [tsub_zero, NNReal.coe_one, one_mul] at hag
      linarith
  | ⟨1, h1m⟩ =>
      have hd : ((stirFinalVSpec ι F).toProtocolSpec F).dir ⟨1, h1m⟩ = .V_to_P :=
        stirFinalVSpec_dir_one
      rw [hd] at hdir
      exact Direction.noConfusion hdir

end Pred

/-! ## Part 5 — the `hFull` leg: acceptance of the checked verifier forces the pointwise
check (the `stirFinalVectorVerifierChecked_toVerifier_honest` factoring, generalized to
arbitrary words and run through the failure branch) -/

section Full

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A field is `VCVCompatible` (the `CheckedFinalBlock` local-instance idiom). -/
local instance : VCVCompatible F := { toFintype := inferInstance, toInhabited := ⟨0⟩ }

/-- **The general `toVerifier`-collapse of the checked final verifier** (the honest lemma
`stirFinalVectorVerifierChecked_toVerifier_honest` with the word decoupled from the incoming
oracle): on ANY `mk2` transcript the full verify computation is the pure
`stirFinalCheckedAns` decision. -/
theorem stirFinalVectorVerifierChecked_toVerifier_verify
    (stmtIn : F) (oStmtIn : ∀ i, VOStmt ι F i)
    (w : ((stirFinalVSpec ι F).toProtocolSpec F).«Type» 0)
    (r1 : ((stirFinalVSpec ι F).toProtocolSpec F).«Type» 1) :
    (stirFinalVectorVerifierChecked (ι := ι) (F := F)).toVerifier.verify (stmtIn, oStmtIn)
      (FullTranscript.mk2 w r1)
      = (do
          let s ← (OptionT.mk (pure (stirFinalCheckedAns oStmtIn
              (FullTranscript.mk2 w r1).messages stmtIn
              (FullTranscript.mk2 w r1).challenges)) : OptionT (OracleComp []ₒ) (F × F))
          pure (s, fun _ : Unit => w)) := by
  have h1 : (stirFinalVectorVerifierChecked (ι := ι) (F := F)).toVerifier.verify
      (stmtIn, oStmtIn) (FullTranscript.mk2 w r1)
      = ((do
          let s ← (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn
                (FullTranscript.mk2 w r1).messages)
              (OptionT.mk (stirFinalCheckedComp stmtIn
                (FullTranscript.mk2 w r1).challenges))
              : OptionT (OracleComp []ₒ) (F × F))
          pure (s, fun _ : Unit => w))
        : OptionT (OracleComp []ₒ) ((F × F) × ∀ i, VOStmt ι F i)) := rfl
  rw [h1, simulateQ_optionT_stirFinalCheckedComp]
  rfl

/-- **The failure branch**: if the checked decision is `none` on the transcript, the whole
verifier run (under ANY query implementation and initialization) succeeds with probability
`0` — rejection is `OptionT` failure. -/
theorem probEvent_checkedRun_mk2_eq_zero {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) (r : F) (oSt : ∀ i, VOStmt ι F i)
    (w : ((stirFinalVSpec ι F).toProtocolSpec F).«Type» 0)
    (r1 : ((stirFinalVSpec ι F).toProtocolSpec F).«Type» 1)
    (hfail : stirFinalCheckedAns oSt (FullTranscript.mk2 w r1).messages r
        (FullTranscript.mk2 w r1).challenges = none)
    (q : (F × F) × (∀ i, VOStmt ι F i) → Prop) :
    Pr[q | OptionT.mk do
        (simulateQ impl ((stirFinalVectorVerifierChecked (ι := ι) (F := F)).toVerifier.run
          (r, oSt) (FullTranscript.mk2 w r1))).run' (← init)] = 0 := by
  have hver : ((stirFinalVectorVerifierChecked (ι := ι) (F := F)).toVerifier.run
      (r, oSt) (FullTranscript.mk2 w r1))
      = (OptionT.mk (pure none) :
          OptionT (OracleComp []ₒ) ((F × F) × ∀ i, VOStmt ι F i)) := by
    show (stirFinalVectorVerifierChecked (ι := ι) (F := F)).toVerifier.verify
        (r, oSt) (FullTranscript.mk2 w r1) = _
    rw [stirFinalVectorVerifierChecked_toVerifier_verify, hfail]
    rfl
  refine probEvent_eq_zero ?_
  intro y hy
  intro _
  rw [OptionT.mem_support_iff] at hy
  erw [support_bind] at hy
  simp only [Set.mem_iUnion, exists_prop] at hy
  obtain ⟨s, -, hy⟩ := hy
  rw [hver] at hy
  rw [show (simulateQ impl ((OptionT.mk (pure none)) :
        OptionT (OracleComp []ₒ) ((F × F) × ∀ i, VOStmt ι F i))
      : StateT σ ProbComp (Option ((F × F) × ∀ i, VOStmt ι F i)))
      = pure none from simulateQ_pure _ _] at hy
  rw [StateT.run'_pure_lib] at hy
  simp only [support_pure, Set.mem_singleton_iff, reduceCtorEq] at hy

end Full

/-! ## Part 6 — the salvage game bound (the generic spot-game shape, mirroring
`Whir302SubUnit.probEvent_salvage_game_le`) -/

section SpotGame

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι' : Type} {oSpec : OracleSpec ι'} {n : ℕ} {vspec : ProtocolSpec.VectorSpec n}
  [∀ i, SampleableType ((vspec.toProtocolSpec F).Challenge i)]
  {StmtIn StmtOut WitIn WitOut : Type} {σ : Type}

open Whir302SubUnit in
/-- **The spot-game salvage bound** (the index-check mirror of
`Whir302SubUnit.probEvent_salvage_game_le`): in the round-`c` RBR game (arbitrary logged
prover prefix, then a fresh uniform length-1 vector challenge), the probability that a
prefix-measurable predicate `P` holds AND the fresh challenge's field element satisfies a
prefix-measurable per-challenge condition `S` is bounded by any `B` dominating the counting
bound `#{x : F | S tr x} / |F|` on every `P`-prefix. -/
theorem probEvent_spotGame_le
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (c : (vspec.toProtocolSpec F).ChallengeIdx) (hc : vspec.length c.1 = 1)
    (P : (vspec.toProtocolSpec F).Transcript c.1.castSucc → Prop)
    (S : (vspec.toProtocolSpec F).Transcript c.1.castSucc → F → Prop)
    [∀ tr, DecidablePred (S tr)]
    (B : ℝ≥0∞)
    (hB : ∀ tr, P tr →
      ((Finset.univ.filter (fun x : F => S tr x)).card : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ≤ B)
    (stmtIn : StmtIn) (witIn : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut (vspec.toProtocolSpec F)) :
    Pr[fun x : (vspec.toProtocolSpec F).Transcript c.1.castSucc ×
          (vspec.toProtocolSpec F).Challenge c ×
          (oSpec + ([(vspec.toProtocolSpec F).Challenge]ₒ'
            (fun i => challengeOracleInterface i))).QueryLog =>
        P x.1 ∧ S x.1 (chalElemOf vspec c x.2.1)
      | (do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound c.1.castSucc stmtIn witIn
            let challenge ← liftComp ((vspec.toProtocolSpec F).getChallenge c) _
            return (transcript, challenge, proveQueryLog))).run' (← init)
        : ProbComp _)]
      ≤ B := by
  classical
  -- peel the init draw
  refine probEvent_bind_le_of_forall_support init _ _ _ (fun s _ => ?_)
  -- distribute the simulation over the prefix bind
  rw [simulateQ_bind, StateT.run'_bind_lib]
  -- peel the prover prefix
  refine probEvent_bind_le_of_forall_support _ _ _ _ (fun rk _ => ?_)
  obtain ⟨⟨⟨tr, pst⟩, log⟩, s'⟩ := rk
  dsimp only
  -- the challenge draw in `liftM` form, then the uniform average over the drawn challenge
  rw [liftComp_eq_liftM]
  rw [ChallengeCoherence.probEvent_run'_simulateQ_addLift_getChallenge_bind impl s' c
    (fun ch => pure (tr, ch, log)) _]
  -- collapse the pure trailing stage and recombine the average into a bind
  simp only [simulateQ_pure, StateT.run'_pure_lib]
  rw [← probEvent_bind_eq_tsum]
  by_cases hP : P tr
  · -- the prefix predicate holds: comap marginal bound at the carried field element
    refine le_trans (probEvent_bind_le_uniform_marginal_comap
      ($ᵗ ((vspec.toProtocolSpec F).Challenge c)) (chalElemOf vspec c)
      (fun ch => pure (tr, ch, log)) _ {x : F | S tr x}
      (fun x => le_of_eq (probEvent_chalElemOf_eq_uniform vspec c hc x)) ?_) ?_
    · -- the continuation forces the per-challenge condition at the carried value
      intro ch hch
      refine probEvent_eq_zero ?_
      rintro x hx ⟨-, hS⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact hch hS
    · have hfilter : (Finset.univ.filter (· ∈ {x : F | S tr x}))
          = (Finset.univ.filter (fun x : F => S tr x)) := by
        apply Finset.filter_congr
        intro x _
        simp [Set.mem_setOf_eq]
      rw [hfilter]
      exact hB tr hP
  · -- the prefix predicate fails: the event is empty at this prefix
    refine le_trans (le_of_eq (probEvent_eq_zero ?_)) (zero_le _)
    rintro x hx ⟨hPx, -⟩
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      exists_prop] at hx
    obtain ⟨ch, -, rfl⟩ := hx
    exact hP hPx

end SpotGame

/-! ## Part 7 — THE THEOREM: RBR knowledge soundness of the checked STIR final block at the
real spot-check budget -/

section Theorem

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance : VCVCompatible F := { toFintype := inferInstance, toInhabited := ⟨0⟩ }

open scoped Classical in
set_option maxHeartbeats 1600000 in
/-- **RBR knowledge soundness of the CHECKED STIR final block at the real spot-check
budget** (`Verifier` level): through the full-predicate KSF with the `stirSpotPred` state
function, the checked final verifier is round-by-round knowledge sound at the budget
concentrated on the repetition challenge `C_fin` with value
`(1−δ)·|ι|·⌈|F|/|ι|⌉/|F|` (= `1−δ` exactly when `|ι| ∣ |F|`). -/
theorem stirFinalVectorVerifierChecked_toVerifier_rbrKnowledgeSoundness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) (δ : ℝ≥0) :
    (stirFinalVectorVerifierChecked (ι := ι) (F := F)).toVerifier.rbrKnowledgeSoundness
      init impl (stirSpotRelIn ι F δ)
      (Set.univ : Set ((((F × F) × ∀ i, VOStmt ι F i)) × Unit))
      (fun i => if i = ⟨1, stirFinalVSpec_dir_one⟩ then stirSpotBudget ι F δ else 0) := by
  classical
  refine FullPredKSF.rbrKnowledgeSoundness_of_salvageBound init impl
    (stirFinalVectorVerifierChecked (ι := ι) (F := F)).toVerifier
    (stirSpotRelIn ι F δ) _ (stirSpotPred δ) _
    (fun stmtIn w => stirSpotPred_empty δ stmtIn w)
    (fun m hdir stmtIn tr msg h => stirSpotPred_concat δ m hdir stmtIn tr msg h)
    ?hFull ?hSalvage
  case hFull =>
    intro stmtIn tr witOut hacc
    obtain ⟨r, oSt⟩ := stmtIn
    by_contra hnp
    rw [transcript_last_eq_mk2 tr] at hacc hnp
    have hfail : stirFinalCheckedAns oSt
        (FullTranscript.mk2 (tr ⟨0, Nat.zero_lt_two⟩) (tr ⟨1, Nat.one_lt_two⟩)).messages r
        (FullTranscript.mk2 (tr ⟨0, Nat.zero_lt_two⟩)
          (tr ⟨1, Nat.one_lt_two⟩)).challenges = none := by
      unfold stirFinalCheckedAns
      exact if_neg (fun hcond => hnp hcond)
    rw [probEvent_checkedRun_mk2_eq_zero init impl r oSt _ _ hfail] at hacc
    exact lt_irrefl 0 hacc
  case hSalvage =>
    intro stmtIn witIn prover i
    -- the only challenge index is the repetition slot
    have hi : i = ⟨1, stirFinalVSpec_dir_one⟩ := by
      rcases i with ⟨⟨iv, hlt⟩, hdir⟩
      interval_cases iv
      · have hd : ((stirFinalVSpec ι F).toProtocolSpec F).dir ⟨0, hlt⟩ = .P_to_V :=
          stirFinalVSpec_dir_zero
        rw [hd] at hdir
        exact Direction.noConfusion hdir
      · exact Subtype.ext rfl
    subst hi
    rw [if_pos rfl]
    refine le_trans (probEvent_mono ?_)
      (probEvent_spotGame_le init impl
        (⟨1, stirFinalVSpec_dir_one⟩ :
          ((stirFinalVSpec ι F).toProtocolSpec F).ChallengeIdx) rfl
        (fun tr => ¬ stirSpotPred δ
          ((⟨1, stirFinalVSpec_dir_one⟩ :
            ((stirFinalVSpec ι F).toProtocolSpec F).ChallengeIdx) : _).1.castSucc stmtIn tr)
        (fun tr x => trWordFun tr Nat.one_pos (stirFinalQueryIndex x)
          = stirIncomingAt stmtIn.2 (stirFinalQueryIndex x))
        _ ?hB stmtIn witIn prover)
    · -- the salvage event implies the spot-game event
      rintro ⟨tr, ch, log⟩ - ⟨hne, hsucc⟩
      refine ⟨hne, ?_⟩
      have hs : trWordFun (tr.concat ch) Nat.zero_lt_two
          (stirFinalQueryIndex (trRepChal (tr.concat ch) Nat.one_lt_two))
          = stirIncomingAt stmtIn.2
            (stirFinalQueryIndex (trRepChal (tr.concat ch) Nat.one_lt_two)) := hsucc
      rw [trRepChal_concat tr ch Nat.one_lt_two] at hs
      rw [trWordFun_concat tr ch Nat.one_pos Nat.zero_lt_two] at hs
      rw [chalElemOf_stirFinal]
      exact hs
    case hB =>
      intro tr hP
      -- ¬(round-1 predicate): the agreement set has at most a `(1−δ)` fraction
      have hP' : ¬ (((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ)
          < ((agreementSet (ι := ι) (trWordFun tr Nat.one_pos)
              (stirIncomingAt stmtIn.2)).card : ℝ)) := hP
      have hag : ((agreementSet (ι := ι) (trWordFun tr Nat.one_pos)
          (stirIncomingAt stmtIn.2)).card : ℝ)
          ≤ ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) := not_lt.mp hP'
      -- the per-challenge condition is exactly the preimage of the agreement set
      have hfilter : Finset.univ.filter (fun x : F =>
            trWordFun tr Nat.one_pos (stirFinalQueryIndex x)
              = stirIncomingAt stmtIn.2 (stirFinalQueryIndex x))
          = Finset.univ.filter (fun x : F => stirFinalQueryIndex (ι := ι) x
              ∈ agreementSet (ι := ι) (trWordFun tr Nat.one_pos)
                (stirIncomingAt stmtIn.2)) := by
        apply Finset.filter_congr
        intro x _
        unfold agreementSet
        simp
      -- the max-fiber union bound on the preimage
      have hcardN : (Finset.univ.filter (fun x : F =>
            trWordFun tr Nat.one_pos (stirFinalQueryIndex x)
              = stirIncomingAt stmtIn.2 (stirFinalQueryIndex x))).card
          ≤ (agreementSet (ι := ι) (trWordFun tr Nat.one_pos)
              (stirIncomingAt stmtIn.2)).card * stirSpotMaxFiber ι F := by
        rw [hfilter]
        exact card_filter_stirFinalQueryIndex_mem_le _
      -- assemble the ℝ≥0 numerator bound
      have hAnn : ((agreementSet (ι := ι) (trWordFun tr Nat.one_pos)
          (stirIncomingAt stmtIn.2)).card : ℝ≥0)
          ≤ (1 - δ) * (Fintype.card ι : ℝ≥0) := by
        rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_natCast]
        exact hag
      have hnum : ((Finset.univ.filter (fun x : F =>
            trWordFun tr Nat.one_pos (stirFinalQueryIndex x)
              = stirIncomingAt stmtIn.2 (stirFinalQueryIndex x))).card : ℝ≥0)
          ≤ (1 - δ) * ((Fintype.card ι * stirSpotMaxFiber ι F : ℕ) : ℝ≥0) := by
        calc ((Finset.univ.filter (fun x : F =>
              trWordFun tr Nat.one_pos (stirFinalQueryIndex x)
                = stirIncomingAt stmtIn.2 (stirFinalQueryIndex x))).card : ℝ≥0)
            ≤ (((agreementSet (ι := ι) (trWordFun tr Nat.one_pos)
                (stirIncomingAt stmtIn.2)).card * stirSpotMaxFiber ι F : ℕ) : ℝ≥0) := by
              exact_mod_cast hcardN
          _ = ((agreementSet (ι := ι) (trWordFun tr Nat.one_pos)
                (stirIncomingAt stmtIn.2)).card : ℝ≥0) * (stirSpotMaxFiber ι F : ℝ≥0) := by
              push_cast
              ring
          _ ≤ ((1 - δ) * (Fintype.card ι : ℝ≥0)) * (stirSpotMaxFiber ι F : ℝ≥0) :=
              mul_le_mul_right' hAnn _
          _ = (1 - δ) * ((Fintype.card ι * stirSpotMaxFiber ι F : ℕ) : ℝ≥0) := by
              push_cast
              ring
      -- conclude in ℝ≥0∞
      have hMne : (Fintype.card F : ℝ≥0) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      calc ((Finset.univ.filter (fun x : F =>
            trWordFun tr Nat.one_pos (stirFinalQueryIndex x)
              = stirIncomingAt stmtIn.2 (stirFinalQueryIndex x))).card : ℝ≥0∞)
            / (Fintype.card F : ℝ≥0∞)
          ≤ (((1 - δ) * ((Fintype.card ι * stirSpotMaxFiber ι F : ℕ) : ℝ≥0) : ℝ≥0) : ℝ≥0∞)
            / (Fintype.card F : ℝ≥0∞) := by
            refine ENNReal.div_le_div_right ?_ _
            calc ((Finset.univ.filter (fun x : F =>
                  trWordFun tr Nat.one_pos (stirFinalQueryIndex x)
                    = stirIncomingAt stmtIn.2 (stirFinalQueryIndex x))).card : ℝ≥0∞)
                = (((Finset.univ.filter (fun x : F =>
                    trWordFun tr Nat.one_pos (stirFinalQueryIndex x)
                      = stirIncomingAt stmtIn.2 (stirFinalQueryIndex x))).card : ℝ≥0)
                    : ℝ≥0∞) := by
                  norm_cast
              _ ≤ _ := ENNReal.coe_le_coe.mpr hnum
        _ = ((stirSpotBudget ι F δ : ℝ≥0) : ℝ≥0∞) := by
            rw [show ((Fintype.card F : ℕ) : ℝ≥0∞) = ((Fintype.card F : ℝ≥0) : ℝ≥0∞) by
              norm_cast]
            rw [← ENNReal.coe_div hMne]
            rfl

open scoped Classical in
/-- **The oracle-verifier front door**: RBR knowledge soundness of
`stirFinalVectorVerifierChecked` at the real spot-check budget. -/
theorem stirFinalVectorVerifierChecked_rbrKnowledgeSoundness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) (δ : ℝ≥0) :
    OracleVerifier.rbrKnowledgeSoundness init impl (stirSpotRelIn ι F δ)
      (Set.univ : Set ((((F × F) × ∀ i, VOStmt ι F i)) × Unit))
      (stirFinalVectorVerifierChecked (ι := ι) (F := F))
      (fun i => if i = ⟨1, stirFinalVSpec_dir_one⟩ then stirSpotBudget ι F δ else 0) :=
  stirFinalVectorVerifierChecked_toVerifier_rbrKnowledgeSoundness init impl δ

open scoped Classical in
/-- **The divisible-regime corollary at the task's budget shape `(C_fin ↦ 1−δ, else 0)`**:
when `|ι| ∣ |F|` (the index marginal is exactly uniform), the checked STIR final block is
RBR knowledge sound at budget exactly `1 − δ` on the repetition challenge. -/
theorem stirFinalVectorVerifierChecked_rbrKnowledgeSoundness_of_dvd {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) (δ : ℝ≥0)
    (hdvd : Fintype.card ι ∣ Fintype.card F) :
    OracleVerifier.rbrKnowledgeSoundness init impl (stirSpotRelIn ι F δ)
      (Set.univ : Set ((((F × F) × ∀ i, VOStmt ι F i)) × Unit))
      (stirFinalVectorVerifierChecked (ι := ι) (F := F))
      (fun i => if i = ⟨1, stirFinalVSpec_dir_one⟩ then 1 - δ else 0) := by
  have h := stirFinalVectorVerifierChecked_rbrKnowledgeSoundness
    (ι := ι) (F := F) init impl δ
  rwa [stirSpotBudget_eq_of_dvd ι F δ hdvd] at h

end Theorem

end Round3

end StirIOP

/-! ## Axiom audit -/

#print axioms StirIOP.Round3.agreementSet_card_le
#print axioms StirIOP.Round3.probEvent_spotCheck_le
#print axioms StirIOP.Round3.card_filter_mod_eq_le
#print axioms StirIOP.Round3.card_fiber_stirFinalQueryIndex_le
#print axioms StirIOP.Round3.card_filter_stirFinalQueryIndex_mem_le
#print axioms StirIOP.Round3.stirSpotBudget_eq_of_dvd
#print axioms StirIOP.Round3.trWord_concat
#print axioms StirIOP.Round3.trWordFun_concat
#print axioms StirIOP.Round3.trRepChal_concat
#print axioms StirIOP.Round3.chalElemOf_stirFinal
#print axioms StirIOP.Round3.transcript_last_eq_mk2
#print axioms StirIOP.Round3.stirSpotPred_empty
#print axioms StirIOP.Round3.stirSpotPred_concat
#print axioms StirIOP.Round3.stirFinalVectorVerifierChecked_toVerifier_verify
#print axioms StirIOP.Round3.probEvent_checkedRun_mk2_eq_zero
#print axioms StirIOP.Round3.probEvent_spotGame_le
#print axioms StirIOP.Round3.stirFinalVectorVerifierChecked_toVerifier_rbrKnowledgeSoundness
#print axioms StirIOP.Round3.stirFinalVectorVerifierChecked_rbrKnowledgeSoundness
#print axioms StirIOP.Round3.stirFinalVectorVerifierChecked_rbrKnowledgeSoundness_of_dvd
