# Tight rbr-KS via target-carrying lifts: the #329 patterns

Issue #329 replaced the proven-forced `err₅ = 1` at Spartan's `linearCombination` round with
the paper bound `1/|R|`, end-to-end
(`composedTightFull_rbrKnowledgeSoundness`, `ArkLib/ProofSystem/Spartan/TightComposedFull.lean`).
The reusable patterns, for the next campaign that hits a vacuous-transported-relation or
forced-error-1 wall:

## Why error 1 gets forced (and the fix)

If a lift's `toFunB` **drops** an inner output component (e.g. the sum-check terminal target),
the transported output relation (`Extractor.Lens.Honest.transportedRelOut`) quantifies over all
compatible inner outputs and becomes near-vacuous; downstream relations cannot see the dropped
data, and a prover who behaves honestly *after* the drop forces per-round error 1 (the v=t
attack of #114). Relation-chain tricks cannot fix this: a tight error on a relation that
verifier acceptance does not imply is laundering. **Tight error + meaningful endpoint jointly
force carrying the data** in the outer statement (`FirstSumcheckWithTarget`,
`SecondSumcheckWithTarget` — note the `dropFirstTarget` trick: build the carried lens through a
projection so the plain development's algebra is consumed unchanged).

## The oracle-pinning keystone (don't re-derive it)

`Sumcheck.Spec.mem_support_oracleVerifier_run_oStmt` (`SumcheckPhaseRbr.lean`) pins any
compatible inner output's oracle to the lens-projected (honest) polynomial — with
`seqCompose'_embed_inl` and `oracleVerifier_embed` as the embed computation. Two consumption
directions, neither needing an accepting-transcript construction:

* **doom extraction** (`sent_ne_true_of_binding_of_not_transported`, `TightMidLeaves.lean`):
  `¬transported` *hands you* the ∃-witness; pinning turns its terminal failure into the direct
  inequality `e₁ ≠ eval r_x F̂`.
* **∀-side collapse** (`transported₂_of_direct`, `TightFinalLeaf.lean`): the direct identity
  implies the transported relation, because every compatible witness is pinned.

The terminal sum-check relation collapses to the direct evaluation identity via
`relationRound_last_iff_deg` (degree-generic, in `TightMidLeaves.lean`). The deduplication is
done: the degree-three `relationRound_last_iff` in the same file is now a one-line corollary of
`relationRound_last_iff_deg`.

## The kernel leaf (the 1/|R| shape)

`TightRLCKernel.lean`: for a nonzero claim-error vector the uniform RLC challenge annihilates
it with probability **exactly** `1/|R|` (`probEvent_linearForm_eq`), in the
`Pr[· | $ᵗ C]` form `Verifier.rbrKnowledgeSoundness_singleChallenge_pure` consumes. The tight
chain design that makes the flip *be* this event: `relF := RLC-match ∩ binding`, deliberately
dropping the sum-check conjunct past the challenge (`TightMidLeaves.lean` module docstring has
the case analysis).

## Conjoining invariants at unchanged error

First application of `Verifier.rbrKnowledgeSoundness_conjoin` (`RbrKnowledgeConjoin.lean`):
`TightConjoinedSecondLeaf.lean` threads the e₁-binding identity through the carried second
sum-check at unchanged `2/|R|`. The `hPres` discharge pattern is reusable: failing-determinism
(`sumcheckFull_toVerifier_isFailingDet` + `Verifier.liftContext_failingDet`) yields the verdict
`(v? (lens.proj s) tr).map (lens.lift s)` whose lift forwards passenger statement and oracles —
no support analysis of the multi-round run needed.

## Guarded terminal checks

The canonical oracle `CheckClaim` is a **pure pass-through** (`verify := fun stmt _ => pure
stmt`): it takes no predicate and never rejects, so an input violating the intended check is
accepted exactly like one satisfying it. (The older version ran `pred` and discarded the
resulting `Prop`, with the same effect.) The binding content must therefore live in the *semantic output relation* (the next stage's input
relation), never in `Set.univ` front doors. The pred-generic transport leaf is
`CheckClaim.oracleVerifier_rbrKnowledgeSoundness_transport` (`FinalCheckWithClaimLeaf.lean`);
`tightFinalRelOut` shows the honest endpoint shape: quantifier-free identities over the final
statement and oracles. These relation-preserving leaves are semantic obligations carried to a later stage; they
are not proofs that the terminal verifier enforces the check.

## Assembly mechanics

The composed fold (`TightComposedFull.lean`, mirroring `ComposedRbrKnowledgeSoundness.lean`) is
relation-generic; carried statements change **no protocol specs**, so `composedPSpec`,
`composedRbrError`, and the `sfx*` suffix specs are reused verbatim, and only the private
direction facts need re-mirroring. The `hV` witnesses are the compiled closed forms
(`*_toVerifier_closed` / `*_toVerifier_pure`) and the two failing-det clones
(`TightDeterminismWitnesses.lean`).

## Lean gotchas collected on the way

* Keyed `rw`/`simp` fail invisibly when `Fin ↑(Fin.last n)` hides where you expect `Fin n` in a
  binder type, or when a `⸨c, x⸩` macro cast proof has type `n = ↑(Fin.last n) + (n − ↑(…))`
  (not `n = n + …`). Fix: ∀-quantify helper lemmas over the cast *proof* and match the macro's
  exact type; when a pattern is display-identical but unmatchable, switch to defeq
  (`refine h.trans ?_`).
* `h ▸ h' ▸ x = x` cast collapse: `simp only [eqRec_eq_cast, cast_cast, cast_eq]`;
  `Fin.cast pf i = Fin.castAdd _ ⟨i.val, _⟩` is `Fin.ext rfl`.
* Derive *value-level* component equalities from pair equalities
  (`congrArg (fun p => p.2.1) h` with an ascribed `have`) — pair-level rewrites die on
  invisible elaboration differences.
* Universe metavariables in big instantiations: pin with `theorem_name.{0, 0, 0, 0}` and
  universe-pinned `private abbrev`s (`OracleReduction.{0, 0}`).
