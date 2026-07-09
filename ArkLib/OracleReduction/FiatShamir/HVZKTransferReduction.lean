/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.FiatShamir.BasicCompleteness
import ArkLib.OracleReduction.Security.ZeroKnowledge
import ArkLib.OracleReduction.FiatShamir.ChallengeOracleSampling
import ArkLib.OracleReduction.FiatShamir.ProverRunCharacterization

/-!
# Basic Fiat-Shamir HVZK transfer — explicit simulator and reduction to the coupling kernel (#116)

The basic Fiat-Shamir HVZK transfer residual `fiatShamir_hvzkTransferResidual`
(`isHVZK R → isHVZK R.fiatShamir`) asks for a transcript simulator for the transformed reduction.
This file supplies that simulator *explicitly* and reduces the whole residual to a single concrete
distributional identity (the "coupling" between the honest Fiat-Shamir transcript distribution and
the interactive honest transcript distribution projected onto its messages).

The transformed reduction `R.fiatShamir` runs over the one-message protocol
`FiatShamirProtocolSpec = ⟨!v[.P_to_V], !v[pSpec.Messages]⟩`, so its full transcript is exactly the
interactive messages (`msgProjFS`). The honest Fiat-Shamir prover draws each round's challenge from
the Fiat-Shamir challenge oracle, which samples uniformly — identically to the interactive verifier;
hence the FS transcript distribution is the interactive one projected to its messages. Pinning that
identity as `coupling`, the FS simulator is just `msgProjFS <$> sim` for the interactive simulator
`sim`, and perfect HVZK transfers.

This removes the *simulator-construction* step of #116 (the conceptually non-obvious part), leaving
only the distributional `coupling` lemma — the Fiat-Shamir-HVZK analogue of the already-proven
completeness run-equality (`Reduction.fiatShamir_runCollapse`).
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Reduction

attribute [local instance 2000] Reduction.fiatShamirZKNoChallengeSampleable

set_option linter.unusedSectionVars false

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ τ : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

/-- Project an interactive full transcript onto the one-message Fiat-Shamir proof transcript: the
single `P_to_V` message is the bundle of interactive prover messages. -/
def msgProjFS (t : FullTranscript pSpec) :
    FullTranscript (FiatShamirProtocolSpec (pSpec := pSpec)) :=
  fun | ⟨0, _⟩ => t.messages

attribute [-instance] Reduction.fiatShamirZKNoChallengeSampleable in
set_option maxHeartbeats 1000000 in
/-- **FS-side collapse of the honest transcript distribution.**

The honest Fiat-Shamir transcript distribution of the *transformed* reduction `R.fiatShamir` equals
(as a raw `OptionT ProbComp` term) the transcript projection of the *explicit* honest execution
`R.fiatShamirHonestExecution`, run under the same shared-oracle implementation `fsImpl` — no
challenge oracle is appended on the right, since the honest execution already queries the
Fiat-Shamir oracle directly. This is the honest-distribution form of the proven completeness
run-collapse `Reduction.fiatShamir_runCollapse`, isolating the remaining `coupling` content to a
statement purely about `R.fiatShamirHonestExecution` (whose challenges are drawn through
`runToRoundFS`). -/
theorem honestTranscriptDist_fiatShamir_eq_honestExecution
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    honestTranscriptDist fsInit fsImpl R.fiatShamir stmt wit
      = OptionT.mk
          (do
            let s ← fsInit
            (Option.map (fun r => r.1.1) <$>
              simulateQ fsImpl (R.fiatShamirHonestExecution stmt wit).run).run' s) := by
  unfold honestTranscriptDist
  apply OptionT.ext
  simp only [OptionT.run_mk]
  congr 1
  funext s
  rw [OptionT.run_map, simulateQ_map]
  have hc := fiatShamir_runCollapse fsImpl R stmt wit
  unfold Reduction.fiatShamir_runCollapseResidual at hc
  -- With the file-local vacuous `SampleableType` instance for the empty FS `ChallengeIdx`
  -- locally disabled (`attribute [-instance]` above), the appended challenge oracle matches the
  -- one baked into `fiatShamir_runCollapseResidual`, so `hc` applies directly.
  exact congrArg (fun z => ((Option.map (fun r => r.1.1)) <$> z).run' s) hc

/-- **Basic Fiat-Shamir HVZK transfer, reduced to the coupling kernel.**

Given the coupling identity — that the honest Fiat-Shamir transcript distribution equals the
interactive honest transcript distribution projected onto its messages (`msgProjFS`) — the basic
Fiat-Shamir transform preserves perfect HVZK, with the *explicit* simulator `msgProjFS <$> sim`
obtained from the interactive simulator `sim`.

No `sorry`/extra axioms: the coupling is supplied as an explicit hypothesis, exactly mirroring the
residual-consumer discipline used throughout `FiatShamir/Basic.lean`. Discharging `coupling` for the
canonical (uniformly-sampling) Fiat-Shamir challenge implementation closes
`fiatShamir_hvzkTransferResidual` (and, via `ZKResidualBridge`, the statistical residual at
`ε = 0`). -/
theorem fiatShamir_hvzkTransfer_of_coupling
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (coupling : ∀ stmt wit, (stmt, wit) ∈ rel →
      evalDist (msgProjFS <$> honestTranscriptDist init impl R stmt wit)
        = evalDist (honestTranscriptDist fsInit fsImpl R.fiatShamir stmt wit)) :
    fiatShamir_hvzkTransferResidual init impl fsInit fsImpl rel R := by
  intro hHVZK
  obtain ⟨sim, hsim⟩ := hHVZK
  refine ⟨fun stmt => msgProjFS <$> sim stmt, fun stmt wit hmem => ?_⟩
  rw [evalDist_map, hsim stmt wit hmem, ← evalDist_map]
  exact coupling stmt wit hmem

/-! ### Canonical cached (lazy random oracle) Fiat-Shamir challenge implementation

The canonical Fiat-Shamir challenge implementation is the *lazy random oracle*
`OracleSpec.randomOracle` on `fsChallengeOracle StmtIn pSpec`: on each challenge query it returns the
cached value if present, otherwise samples a fresh uniform `$ᵗ (pSpec.Challenge i)` and caches it.

This is the correct design (in contrast to a *stateless* fresh-sampling implementation): because the
table is cached, when the Fiat-Shamir verifier re-derives the transcript via `deriveTranscriptFS` it
reads back the *same* challenges the honest prover used in `runToRoundFS`. Hence honest transcripts
verify (the message marginal does not `none` out) and the Fiat-Shamir honest-transcript distribution
genuinely couples to the interactive one. -/

section Canonical

variable [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]

/-- The canonical Fiat-Shamir challenge implementation: the lazy random oracle on the Fiat-Shamir
challenge oracle. Its state is the `QueryCache` of already-sampled challenges. -/
noncomputable def canonicalFSChallengeImpl :
    QueryImpl (fsChallengeOracle StmtIn pSpec)
      (StateT (fsChallengeOracle StmtIn pSpec).QueryCache ProbComp) :=
  OracleSpec.randomOracle

/-- The canonical Fiat-Shamir shared-oracle implementation built from an interactive implementation
`impl` by appending the canonical lazy random-oracle challenge implementation. The combined state is
`σ × QueryCache`: the original-oracle state paired with the challenge cache. -/
noncomputable def canonicalFSImpl (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec)
      (StateT (σ × (fsChallengeOracle StmtIn pSpec).QueryCache) ProbComp) :=
  impl.addLift (canonicalFSChallengeImpl (StmtIn := StmtIn) (pSpec := pSpec))

/-- The canonical Fiat-Shamir initial state: the original-oracle init paired with the empty challenge
cache (no challenges sampled yet). -/
noncomputable def canonicalFSInit (init : ProbComp σ) :
    ProbComp (σ × (fsChallengeOracle StmtIn pSpec).QueryCache) :=
  (fun s => (s, ∅)) <$> init

/-- **The canonical Fiat-Shamir HVZK coupling kernel (tight residual).**

This is the single, *tight* distributional identity that remains to discharge the `coupling`
hypothesis of `fiatShamir_hvzkTransfer_of_coupling` for the canonical lazy random-oracle
implementation. All the surrounding `R.fiatShamir.run` / verifier machinery has been collapsed away
(via `honestTranscriptDist_fiatShamir_eq_honestExecution`): what is left is a statement *purely about
the explicit honest execution* `R.fiatShamirHonestExecution`, simulated through the canonical
combined implementation `canonicalFSImpl impl` starting from the empty challenge cache, compared with
the message-bundle marginal `msgProjFS` of the interactive honest transcript distribution.

It is the lazy-vs-eager coupling kernel of #116: the interactive verifier draws each round's
challenge fresh-uniform from `[pSpec.Challenge]ₒ` (`challengeQueryImpl`); the Fiat-Shamir prover and
verifier read the same lazily-cached challenge table at the per-round, transcript-indexed keys
`⟨⟨i, _⟩, ⟨stmt, messagesUpTo i⟩⟩`. Across an honest run these keys are pairwise distinct (they carry
strictly growing message prefixes), so each is a *cache miss* answered by a fresh independent uniform
draw — distributionally identical to the interactive fresh draws. The cache then guarantees the
verifier's `deriveTranscriptFS` reads back exactly those same challenges, so the honest transcript
verifies (never `none`s out) and its message marginal coincides with the interactive one.

This residual is **TRUE** (see the verified per-round infrastructure
`Reduction.evalWithAnswerFn_processRound` / `Reduction.evalWithAnswerFn_processRoundFS` and the
lazy-vs-eager equivalence `Reduction.fsChallenge_lazy_eq_eager`), and it is the *correct*
(cached-table) residual — not the false stateless one, under which the verifier would re-derive
*independent* fresh challenges and the message marginal would degenerate. -/
def canonicalFSCouplingKernel
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) : Prop :=
  ∀ stmt wit, (stmt, wit) ∈ rel →
    evalDist (OptionT.mk (do
        let a ← init
        ((Option.map (fun r => r.1.1)) <$>
          simulateQ (canonicalFSImpl (StmtIn := StmtIn) impl)
            (R.fiatShamirHonestExecution stmt wit).run).run' (a, ∅))
          : OptionT ProbComp (FiatShamirProofTranscript (pSpec := pSpec)))
      = evalDist (msgProjFS <$> honestTranscriptDist init impl R stmt wit)

/-- **Per-`oSpec`-state lazy-vs-eager coupling (the irreducible residual).**

The smallest distributional identity to which `canonicalFSCouplingKernel` reduces, after the entirely
structural layer (`init`/`OptionT`/`evalDist`/`.run'`/marginalization plumbing) has been stripped:
holding the shared-oracle implementation `impl` over `oSpec` and a *fixed* `oSpec`-state `a` (drawn
from `init`), the message-bundle marginal of the explicit Fiat-Shamir honest execution — simulated
through the **lazy random oracle** on the Fiat-Shamir challenge oracle from the **empty cache**
(`canonicalFSChallengeImpl`, started at `(a, ∅)`) — coincides with the message-bundle marginal of
the *interactive* honest run, whose verifier draws each round's challenge **fresh-uniform** through
`challengeQueryImpl` (started at `a`).

This is exactly the content flagged in the docstring of `canonicalFSCouplingKernel`: across an honest
run the per-round, transcript-indexed Fiat-Shamir query keys `⟨⟨i, _⟩, ⟨stmt, messagesUpTo i⟩⟩` are
pairwise distinct (strictly growing message prefixes), so each is a cache miss answered by a fresh
independent uniform draw — distributionally identical to the interactive fresh draws — and the cache
makes the verifier's `deriveTranscriptFS` read back exactly those challenges, so the honest transcript
never `none`s out and its message marginal coincides with the interactive one. It is TRUE; closing it
requires the lazy-vs-eager equivalence `Reduction.fsChallenge_lazy_eq_eager` (lifted across the mixed
`oSpec + fsChallengeOracle` simulation), the per-round peeling
`Reduction.evalWithAnswerFn_processRound{,FS}`, and the pairwise-distinctness of the FS keys. -/
def canonicalFSPerStateCoupling
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) : Prop :=
  ∀ a : σ,
    evalDist
        (StateT.run'
            ((Option.map (fun r : (FiatShamirProofTranscript (pSpec := pSpec) × StmtOut × WitOut) ×
                  StmtOut => r.1.1)) <$>
              (simulateQ (impl.addLift (canonicalFSChallengeImpl (StmtIn := StmtIn) (pSpec := pSpec)))
                (R.fiatShamirHonestExecution stmt wit).run
                : StateT (σ × (fsChallengeOracle StmtIn pSpec).QueryCache) ProbComp
                    (Option ((FiatShamirProofTranscript (pSpec := pSpec) × StmtOut × WitOut) ×
                      StmtOut))))
            (a, (∅ : (fsChallengeOracle StmtIn pSpec).QueryCache)))
      = evalDist
          (Option.map (msgProjFS (pSpec := pSpec)) <$>
            StateT.run'
              (simulateQ (impl.addLift challengeQueryImpl)
                ((Option.map (fun result : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut =>
                    result.1.1)) <$> (R.run stmt wit).run)
                : StateT σ ProbComp (Option (FullTranscript pSpec))) a)

set_option maxHeartbeats 1000000 in
/-- **The canonical Fiat-Shamir HVZK coupling kernel holds, modulo the per-state coupling residual.**

This discharges the entire *structural* layer of the kernel `canonicalFSCouplingKernel` — stripping
the `init` bind, the `OptionT`/`evalDist`/`.run'` plumbing, and both message-bundle marginalizations
(`(·.1.1)` on the FS side, `msgProjFS` on the interactive side) — sorry-free, reducing the kernel
exactly to the per-`oSpec`-state lazy-vs-eager coupling `canonicalFSPerStateCoupling`. -/
theorem canonicalFSCouplingKernel_of_perStateCoupling
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hCoupling : ∀ stmt wit, (stmt, wit) ∈ rel →
      canonicalFSPerStateCoupling impl R stmt wit) :
    canonicalFSCouplingKernel init impl rel R := by
  intro stmt wit hmem
  -- `evalDist` on `OptionT ProbComp` is determined by `evalDist` of the underlying `.run`.
  have bridge : ∀ {β : Type} (mx my : OptionT ProbComp β),
      evalDist mx.run = evalDist my.run → evalDist mx = evalDist my := by
    intro β mx my h
    rw [show (𝒟[mx] : SPMF β) = ((MonadHom.ofLift ProbComp SPMF) mx.run >>= fun y =>
          match y with | some a => pure a | none => failure : SPMF β) from rfl,
        show (𝒟[my] : SPMF β) = ((MonadHom.ofLift ProbComp SPMF) my.run >>= fun y =>
          match y with | some a => pure a | none => failure : SPMF β) from rfl]
    have hrun : ((MonadHom.ofLift ProbComp SPMF) mx.run : SPMF (Option β)) = (MonadHom.ofLift ProbComp SPMF) my.run := h
    rw [hrun]
  refine bridge _ _ ?_
  rw [OptionT.run_map]
  unfold honestTranscriptDist canonicalFSImpl
  simp only [OptionT.run_mk, OptionT.run_map]
  rw [map_bind, evalDist_bind, evalDist_bind]
  refine congrArg _ (funext fun a => ?_)
  exact hCoupling stmt wit hmem a

attribute [-instance] Reduction.fiatShamirZKNoChallengeSampleable in
set_option maxHeartbeats 1000000 in
/-- **FS-side collapse of the canonical coupling.** The full canonical coupling identity (the
`coupling` hypothesis of `fiatShamir_hvzkTransfer_of_coupling`, specialized to the canonical lazy
random-oracle implementation) reduces *definitionally up to the proven run-collapse* to the tight
`canonicalFSCouplingKernel`. The Fiat-Shamir verifier's whole transcript-checking machinery has been
collapsed to the explicit honest execution by `honestTranscriptDist_fiatShamir_eq_honestExecution`,
and the empty-cache initial state has been threaded through. -/
theorem canonicalFSCoupling_of_kernel
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hKernel : canonicalFSCouplingKernel init impl rel R) :
    ∀ stmt wit, (stmt, wit) ∈ rel →
      evalDist (msgProjFS <$> honestTranscriptDist init impl R stmt wit)
        = evalDist (honestTranscriptDist (canonicalFSInit (StmtIn := StmtIn) (pSpec := pSpec) init)
            (canonicalFSImpl (StmtIn := StmtIn) impl) R.fiatShamir stmt wit) := by
  intro stmt wit hmem
  rw [honestTranscriptDist_fiatShamir_eq_honestExecution
        (canonicalFSInit (StmtIn := StmtIn) (pSpec := pSpec) init)
        (canonicalFSImpl (StmtIn := StmtIn) impl) R stmt wit]
  unfold canonicalFSInit
  rw [show (OptionT.mk
        (do
          let s ← (fun s => (s, (∅ : (fsChallengeOracle StmtIn pSpec).QueryCache))) <$> init
          ((Option.map fun r => r.1.1) <$>
            simulateQ (canonicalFSImpl (StmtIn := StmtIn) impl)
              (R.fiatShamirHonestExecution stmt wit).run).run' s)
        : OptionT ProbComp (FiatShamirProofTranscript (pSpec := pSpec)))
      = OptionT.mk (do
          let a ← init
          ((Option.map (fun r => r.1.1)) <$>
            simulateQ (canonicalFSImpl (StmtIn := StmtIn) impl)
              (R.fiatShamirHonestExecution stmt wit).run).run' (a, ∅)) by
    apply OptionT.ext
    simp only [OptionT.run_mk, bind_map_left]]
  exact (hKernel stmt wit hmem).symm

/-- **Canonical basic Fiat-Shamir HVZK transfer.**

Given the tight canonical coupling kernel `canonicalFSCouplingKernel` — the single distributional
kernel of #116 — the basic Fiat-Shamir transform preserves perfect HVZK for the canonical lazy
random-oracle challenge implementation. This is `fiatShamir_hvzkTransfer_of_coupling` instantiated at
`fsInit := canonicalFSInit init`, `fsImpl := canonicalFSImpl impl`, with the FS side collapsed to the
honest execution by `canonicalFSCoupling_of_kernel`. -/
theorem fiatShamir_hvzkTransferResidual_canonical
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hKernel : canonicalFSCouplingKernel init impl rel R) :
    fiatShamir_hvzkTransferResidual init impl
      (canonicalFSInit (StmtIn := StmtIn) (pSpec := pSpec) init)
      (canonicalFSImpl (StmtIn := StmtIn) impl) rel R := by
  refine fiatShamir_hvzkTransfer_of_coupling init impl
    (canonicalFSInit (StmtIn := StmtIn) (pSpec := pSpec) init)
    (canonicalFSImpl (StmtIn := StmtIn) impl) rel R ?_
  -- The collapse lemma is proved with the file-local vacuous `SampleableType` instance for the
  -- empty Fiat-Shamir `ChallengeIdx` disabled; here that instance is active. Both instances are
  -- equal (the index `FiatShamirProtocolSpec.ChallengeIdx` is empty, so the Pi is a subsingleton),
  -- so the collapse identity transports across.
  have hcoll := canonicalFSCoupling_of_kernel init impl rel R hKernel
  intro stmt wit hmem
  have h := hcoll stmt wit hmem
  convert h using 3
  exact Subsingleton.elim _ _

/-- **Canonical basic Fiat-Shamir HVZK transfer from the per-state lazy-vs-eager coupling.**

Composes `canonicalFSCouplingKernel_of_perStateCoupling` (the sorry-free structural reduction of the
coupling kernel) with `fiatShamir_hvzkTransferResidual_canonical`: given only the irreducible
per-`oSpec`-state coupling residual `canonicalFSPerStateCoupling`, the basic Fiat-Shamir transform
preserves perfect HVZK for the canonical lazy random-oracle challenge implementation. This is the
form in which the whole HVZK transfer is reduced to the single coupling residual. -/
theorem fiatShamir_hvzkTransferResidual_canonical_of_perStateCoupling
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hCoupling : ∀ stmt wit, (stmt, wit) ∈ rel →
      canonicalFSPerStateCoupling impl R stmt wit) :
    fiatShamir_hvzkTransferResidual init impl
      (canonicalFSInit (StmtIn := StmtIn) (pSpec := pSpec) init)
      (canonicalFSImpl (StmtIn := StmtIn) impl) rel R :=
  fiatShamir_hvzkTransferResidual_canonical init impl rel R
    (canonicalFSCouplingKernel_of_perStateCoupling init impl rel R hCoupling)

end Canonical

end Reduction
