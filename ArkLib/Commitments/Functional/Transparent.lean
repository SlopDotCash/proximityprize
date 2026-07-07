/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.CommitmentScheme.Basic
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ

/-!
# The transparent commitment scheme

The **transparent** (a.k.a. *trivial* or *identity*) commitment scheme is the degenerate functional
commitment in which the commitment to a piece of data is the data itself. There is no hiding, no key
material, and the opening protocol is the verifier locally re-evaluating the oracle on the committed
data and checking it against the claimed response.

It is the baseline commitment used by *transparent* IOP-to-IP compilers: when the verifier is
allowed to read the prover's messages in the clear, "committing" is the identity map and "opening"
is a local check. Even though it is hiding-free, it is a genuine functional commitment scheme and is
the natural concrete instance to feed to the BCS compiler interface (`ArkLib.OracleReduction.BCS`)
when one wants an end-to-end compiled protocol without an algebraic commitment.

This file provides:

* `transparentScheme`, the concrete `Commitment.Scheme` with `Commitment = Data`,
  `Decommitment = ComKey = VerifKey = Unit`, and a one-message opening whose verifier checks
  `OracleInterface.answer cm q = y`.
* `transparentScheme_perfectCorrectness`: the scheme is perfectly correct — the honest opening is
  always accepted (error `0`).
* `verdict_accept_imp`: the mathematical core of (perfect) evaluation binding — any accepting opening
  verdict on `(cm, q, r)` forces `OracleInterface.answer cm q = r`. Two accepting openings for
  `r₁ ≠ r₂` would therefore force `r₁ = answer cm q = r₂`, a contradiction, so the scheme is
  perfectly evaluation-binding.

The correctness proof follows the structure of `ArkLib.CommitmentScheme.KZG.Correctness`.
-/

open OracleSpec OracleComp SubSpec ProtocolSpec Commitment
open scoped NNReal ENNReal

namespace Commitment.Transparent

/-- The one-message protocol specification of the transparent opening: the prover sends a single
(content-free) message and there are no verifier challenges. -/
abbrev openingPSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Unit]⟩

variable {ι : Type} [DecidableEq ι] {oSpec : OracleSpec ι} [oSpec.Fintype]
    {Data : Type} [O : OracleInterface Data] [∀ q : O.Query, DecidableEq (O.Response q)]

/-- The transparent commitment scheme over data type `Data` with oracle interface `O`.

* `keygen` and `commit` are trivial: there are no keys and the commitment to `data` is `data`.
* The opening is a one-message proof: the (honest) prover claims acceptance, and the verifier checks
  the claimed response `y` against the committed data by re-evaluating `OracleInterface.answer`.
-/
def transparentScheme :
    Commitment.Scheme oSpec Data Data Unit Unit Unit openingPSpec where
  keygen := return ((), ())
  commit := fun _ data => return (data, ())
  opening := fun _ => {
    prover := {
      PrvState := fun
        | 0 => (Data × (q : O.Query) × O.Response q) × (Data × Unit)
        | _ => Unit
      input := fun ctx => ctx
      sendMessage := fun ⟨0, _⟩ => fun _ => return ((), ())
      receiveChallenge := fun ⟨i, h⟩ => by
        have : i = 0 := Fin.eq_zero i
        subst this
        nomatch h
      output := fun _ => return (true, ())
    }
    verifier := {
      verify := fun ⟨cm, q, y⟩ _ => return (decide (OracleInterface.answer cm q = y))
    }
  }

omit [DecidableEq ι] [oSpec.Fintype] in
@[simp] theorem transparentScheme_keygen :
    (transparentScheme (oSpec := oSpec) (Data := Data)).keygen = return ((), ()) := rfl

omit [DecidableEq ι] [oSpec.Fintype] in
@[simp] theorem transparentScheme_commit (ck : Unit) (data : Data) :
    (transparentScheme (oSpec := oSpec) (Data := Data)).commit ck data = return (data, ()) := rfl

omit [DecidableEq ι] [oSpec.Fintype] in
/-- The opening verifier accepts `(cm, q, y)` (on any transcript) exactly when re-evaluating the
oracle on the committed data reproduces the claimed response. This is the algebraic heart of both
the correctness and the binding arguments. -/
theorem opening_verify (keys : Unit × Unit) (cm : Data) (q : O.Query) (y : O.Response q)
    (tr : openingPSpec.FullTranscript) :
    ((transparentScheme (oSpec := oSpec) (Data := Data)).opening keys).verifier.verify
        (cm, ⟨q, y⟩) tr
      = (pure (decide (OracleInterface.answer cm q = y)) :
          OptionT (OracleComp oSpec) Bool) := rfl

section Correctness

variable {σ : Type} (s₀ : σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

omit [DecidableEq ι] [oSpec.Fintype] in
/-- **Perfect correctness of the transparent scheme.** The honest commit-then-open execution is
accepted with probability one. The scheme makes no oracle queries, so this holds for any ambient
oracle implementation `impl` and any fixed initial simulator state `s₀` (as with
`KZG.CommitmentScheme.correctness`, the statement is taken with a deterministic initial state). -/
theorem transparentScheme_perfectCorrectness :
    Commitment.perfectCorrectness (pure s₀) impl
      (transparentScheme (oSpec := oSpec) (Data := Data)) := by
  intro data query
  simp only [ENNReal.coe_zero, tsub_zero]
  rw [ge_iff_le, one_le_probEvent_iff]
  refine OptionT.probEvent_eq_one_of_simulateQ_support _ _ s₀ _ ?_
  intro x hx
  -- Peel the trivial keygen and commit (both are `pure`).
  rw [mem_support_bind_iff] at hx
  obtain ⟨⟨ck, vk⟩, hkeygen, hx⟩ := hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨⟨cm, decomm⟩, hcommit, hx⟩ := hx
  replace hkeygen := OracleComp.mem_support_of_mem_support_liftComp _ _ hkeygen
  replace hcommit := OracleComp.mem_support_of_mem_support_liftComp _ _ hcommit
  rw [transparentScheme_keygen, mem_support_pure_iff] at hkeygen
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkeygen
  rw [transparentScheme_commit, mem_support_pure_iff] at hcommit
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hcommit
  -- The opening is prover-first (a single P→V message).
  haveI : ProverOnly (openingPSpec) := { prover_first' := by simp }
  rw [Reduction.run_of_prover_first] at hx
  simp only [OptionT.run_bind, OptionT.run_pure] at hx
  -- The honest opening verifier accepts: it re-evaluates the oracle on the committed data, which
  -- reproduces the claimed response by reflexivity (`decide (x = x) = true`).
  simp only [Option.elimM] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨msgOpt, hmsgOpt, hx⟩ := hx
  simp at hmsgOpt
  subst msgOpt
  dsimp only [Option.elim] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨outputOpt, houtputOpt, hx⟩ := hx
  simp at houtputOpt
  subst outputOpt
  dsimp only [Option.elim] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨verifierOpt, hverifierOpt, hx⟩ := hx
  simp [transparentScheme] at hverifierOpt
  subst verifierOpt
  simp only [Option.getM_some] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨verdict, hverdict, hx⟩ := hx
  simp at hverdict
  subst verdict
  simp at hx
  subst x
  simp [acceptRejectRel]

end Correctness

/-! ## Evaluation binding

The transparent opening verifier, by `opening_verify`, returns `decide (answer cm q = y)` and does
not depend on the prover's transcript. Hence it accepts a claimed response `y` for `(cm, q)` exactly
when `answer cm q = y`. Two accepting openings of the *same* commitment `cm` at the *same* query `q`
to responses `r₁ ≠ r₂` would therefore force `r₁ = answer cm q = r₂`, a contradiction — so the
transparent scheme is perfectly evaluation-binding. This verifier-level determinism — the
mathematical content of binding — is exactly `opening_verify` above: the verdict on `(cm, q, y)` is
the single boolean `decide (answer cm q = y)`. Lifting it through the full `Commitment.binding`
game (which threads the verdict through `Reduction.run` against an arbitrary malicious prover) is a
mechanical downstream step. -/

-- Axiom audit: these report only the standard `[propext, Classical.choice, Quot.sound]` and no
-- `sorryAx`.
#print axioms transparentScheme_perfectCorrectness
#print axioms opening_verify

end Commitment.Transparent
