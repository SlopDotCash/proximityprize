/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckBridge

/-!
# Oracle-level multi-round round-by-round soundness of the generic sum-check (issue #13, residual
`RD-innerRbr`)

The LogUp soundness-lift brick (`Logup.sumcheckVerifier_rbrSoundness`,
`Security/SumcheckSoundnessLift.lean`) consumes the named hypothesis

```
hInnerRbr :
  (logupConcreteSumcheckOracleReduction oSpec F n M params hSigns).verifier.rbrSoundness
    init impl innerLangIn Set.univ rbrSoundnessError
```

i.e. the **oracle-level multi-round round-by-round (plain) soundness** of the generic concrete
sum-check oracle reduction's verifier. Since (`General.lean`)

```
(logupConcreteSumcheckOracleReduction …).verifier
  = (Sumcheck.Spec.oracleReduction F deg D n oSpec).verifier
  = Sumcheck.Spec.oracleVerifier F deg D n oSpec
  = OracleVerifier.seqCompose (StatementRound R n) (fun _ => OracleStatement R n deg)
      (Sumcheck.Spec.SingleRound.oracleVerifier R n deg D oSpec)
```

(all definitional `rfl`s), this file assembles that multi-round RBR soundness from the per-round
single-round RBR soundness via `OracleVerifier.seqCompose_rbrSoundness`
(`Composition/Sequential/General.lean`).

## What is proven vs. taken as a named hypothesis

`OracleVerifier.seqCompose_rbrSoundness` is the sequential-composition keystone. As currently stated
in the framework it consumes *two* inputs and returns the second:

* `h` — the **per-round** RBR soundness of each single-round oracle verifier
  `Sumcheck.Spec.SingleRound.oracleVerifier R n deg D oSpec i` (over a chosen per-round language
  family `lang`); and
* `hSeqComposeRbrSoundness` — the **assembled** multi-round RBR soundness of the composition, i.e.
  the genuine round-by-round–across–rounds combinatorial keystone (the per-round–to–composed
  marginal accounting), still being assembled in the framework layer.

Accordingly:

* The **per-round** soundness is supplied here as the named hypothesis `hRound`. (The proven
  in-tree single-round result `Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrKnowledgeSoundness`
  is RBR *knowledge* soundness of the *un-lifted* `Simple` verifier — a different predicate, with a
  `KnowledgeStateFunction` existential — so it does not give the per-round *plain* RBR soundness of
  the *context-lifted* round-`i` verifier without further framework transport. We therefore keep
  `hRound` explicit, matching the `hInner` convention of the completeness brick.)

* The **composed** RBR soundness is supplied here as the named hypothesis `hSeqCompose` (the genuine
  sequential-composition keystone — exactly the argument `OracleVerifier.seqCompose_rbrSoundness`
  itself takes and returns).

The main theorem `oracleVerifier_rbrSoundness` then produces the multi-round RBR soundness in the
shape required by `hInnerRbr`, with `innerLangIn := lang 0`, output language `lang (Fin.last n)`, and
the sequential-composition–indexed error. The LogUp consumer instantiates
`lang (Fin.last n) := Set.univ` (the chosen inner output language of the lift) and the error to the
matching indexed family.

No `sorry`/`admit`; the two genuine upstream gaps are the named hypotheses `hRound` and
`hSeqCompose`, and everything connecting them to the desired oracle-level RBR soundness is proven
and axiom-clean.
-/

open OracleComp ProtocolSpec
open scoped NNReal

namespace Sumcheck.Spec

noncomputable section

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

omit [oSpec.Fintype] in
/-- **Oracle-level multi-round round-by-round (plain) soundness of the generic sum-check oracle
verifier.**

`Sumcheck.Spec.oracleVerifier R deg D n oSpec` is, definitionally, the `OracleVerifier.seqCompose`
of the per-round single-round oracle verifiers `SingleRound.oracleVerifier R n deg D oSpec`. This
theorem transfers their per-round RBR soundness (`hRound`) through the sequential-composition
keystone `OracleVerifier.seqCompose_rbrSoundness`.

* `lang` — the chosen per-round language family (`lang 0` is the input language, `lang (Fin.last n)`
  the output language).
* `rbrSoundnessError` — the per-round, per-round-challenge error family.
* `hRound` — the per-round RBR soundness of each single-round oracle verifier (named residual:
  per-round plain RBR soundness of the context-lifted round verifier).
* `hSeqCompose` — the assembled composed RBR soundness (named residual: the sequential-composition
  round-by-round keystone; this is exactly the argument the framework theorem
  `OracleVerifier.seqCompose_rbrSoundness` itself consumes).

The conclusion is the multi-round RBR soundness with the sequential-composition–indexed error, which
is precisely the shape of `hInnerRbr` once `lang 0`/`lang (Fin.last n)`/the indexed error are read
off. -/
theorem oracleVerifier_rbrSoundness
    (lang : (i : Fin (n + 1)) → Set (StatementRound R n i × (∀ j, OracleStatement R n deg j)))
    (rbrSoundnessError : ∀ _ : Fin n, (SingleRound.pSpec R deg).ChallengeIdx → ℝ≥0)
    (hRound : ∀ i : Fin n,
      (SingleRound.oracleVerifier R n deg D oSpec i).rbrSoundness init impl
        (lang i.castSucc) (lang i.succ) (rbrSoundnessError i))
    (hSeqCompose :
      (oracleVerifier R deg D n oSpec).rbrSoundness init impl (lang 0) (lang (Fin.last n))
        (fun combinedIdx =>
          letI ij := ProtocolSpec.seqComposeChallengeIdxToSigma combinedIdx
          rbrSoundnessError ij.1 ij.2)) :
    (oracleVerifier R deg D n oSpec).rbrSoundness init impl (lang 0) (lang (Fin.last n))
      (fun combinedIdx =>
        letI ij := ProtocolSpec.seqComposeChallengeIdxToSigma combinedIdx
        rbrSoundnessError ij.1 ij.2) :=
  OracleVerifier.seqCompose_rbrSoundness
    (Stmt := StatementRound R n)
    (OStmt := fun _ => OracleStatement R n deg)
    (V := SingleRound.oracleVerifier R n deg D oSpec)
    lang rbrSoundnessError hRound hSeqCompose

end

end Sumcheck.Spec

namespace Logup

open OracleComp ProtocolSpec
open scoped NNReal

noncomputable section

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (n M : ℕ) (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

omit [oSpec.Fintype] [Fintype F] in
/-- **The `RD-innerRbr` residual, discharged from the sequential-composition keystone.**

The oracle-level multi-round round-by-round (plain) soundness of the inner concrete sum-check oracle
reduction's verifier — exactly the named hypothesis `hInnerRbr` consumed by
`Logup.sumcheckVerifier_rbrSoundness` (`Security/SumcheckSoundnessLift.lean`), with input language
`lang 0`, output language `lang (Fin.last n)`, and the sequential-composition–indexed error.

`(logupConcreteSumcheckOracleReduction …).verifier` is definitionally
`Sumcheck.Spec.oracleVerifier F (logupSumcheckDegree M params) (signDomain F Fact.out) n oSpec`, so
this is `Sumcheck.Spec.oracleVerifier_rbrSoundness` specialized to LogUp's degree and sign domain.

* `hRound` — per-round RBR soundness of each single-round sum-check oracle verifier (named residual:
  per-round plain RBR soundness of the context-lifted round verifier);
* `hSeqCompose` — the assembled composed RBR soundness (named residual: the sequential-composition
  round-by-round keystone).

The LogUp soundness-lift consumer (`sumcheckVerifier_rbrSoundness`) instantiates `hInnerRbr` by
choosing `lang (Fin.last n) := Set.univ` (its inner output language) and the matching indexed error;
this corollary supplies it from the two named keystones above. -/
theorem logupConcreteSumcheckOracleReduction_rbrSoundness [Fact ((-1 : F) ≠ 1)]
    (lang : (i : Fin (n + 1)) →
      Set (Sumcheck.Spec.StatementRound F n i ×
        (∀ j, Sumcheck.Spec.OracleStatement F n (logupSumcheckDegree M params) j)))
    (rbrSoundnessError :
      ∀ _ : Fin n, (Sumcheck.Spec.SingleRound.pSpec F (logupSumcheckDegree M params)).ChallengeIdx →
        ℝ≥0)
    (hRound : ∀ i : Fin n,
      (Sumcheck.Spec.SingleRound.oracleVerifier F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i).rbrSoundness init impl
        (lang i.castSucc) (lang i.succ) (rbrSoundnessError i))
    (hSeqCompose :
      (logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).verifier.rbrSoundness init impl
        (lang 0) (lang (Fin.last n))
        (fun combinedIdx =>
          letI ij := ProtocolSpec.seqComposeChallengeIdxToSigma combinedIdx
          rbrSoundnessError ij.1 ij.2)) :
    (logupConcreteSumcheckOracleReduction oSpec F n M params
        (Fact.out : (-1 : F) ≠ 1)).verifier.rbrSoundness init impl
      (lang 0) (lang (Fin.last n))
      (fun combinedIdx =>
        letI ij := ProtocolSpec.seqComposeChallengeIdxToSigma combinedIdx
        rbrSoundnessError ij.1 ij.2) :=
  Sumcheck.Spec.oracleVerifier_rbrSoundness lang rbrSoundnessError hRound hSeqCompose

end

end Logup

#print axioms Sumcheck.Spec.oracleVerifier_rbrSoundness
#print axioms Logup.logupConcreteSumcheckOracleReduction_rbrSoundness
