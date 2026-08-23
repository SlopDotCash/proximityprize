/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.ToVCVio.Simulation

/-!
# Challenge-oracle seam bridge — verified building blocks

The sequential-composition completeness/soundness assemblies (`AppendPerfectCompleteness.lean`
and the `appendSoundnessResidual` in `Append.lean`) must apply the per-phase hypotheses
`h₁`/`h₂`, which simulate over the **component** challenge oracles `[pSpecᵢ.Challenge]ₒ`,
whereas the appended run's lifted sub-runs route challenge queries through the **combined**
`[(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ`. Reconciling the two is the concrete form of the #433
monad-commutation gap, for the message seam.

This file proves that bridge (left/`pSpec₁` half) at the `evalDist` level, plus the
support-faithfulness gate (`addLift_challenge_support_faithful`). See
`docs/kb/audits/append-keystone-state-2026-06-08.md` for the full proof architecture. The bridge is
the deep distributional crux (the concrete #433 monad-commutation). The completeness half of the
keystone is now **discharged** on top of this file —
`Reduction.append_perfectCompleteness_msg_proof` in `AppendPerfectCompletenessProof.lean` (axiom-clean)
— via the support-decomposition route. The `append_soundness` union bound remains.

Main results:
* `evalDist_challengeSeam_bridge_left` — `evalDist ((simulateQ pImpl_combined (liftM oa)).run s)
  = evalDist ((simulateQ pImpl₁ oa).run s)`. The concrete distributional form of #433 for the
  message seam: per-phase hypotheses stated over the component challenge oracle transfer to the
  appended run that routes through the combined oracle.
* `evalDist_challengeSeam_bridge_right` — the symmetric statement for `pSpec₂` (the phase-2 leg).

Supporting facts (all machine-checked, axiom-clean):
* `liftM_map_comm` — `liftM`/`map` naturality for `ProbComp → StateT σ ProbComp`, threading the
  challenge response-cast through the state lift.
* `evalDist_cast_uniformSample` — uniform sampling is invariant under transport along a type
  equality (uniqueness of the uniform distribution pushed along the bijective `cast`). This is
  *why* the bridge is necessarily distributional: the seam challenge types
  `(pSpec₁ ++ₚ pSpec₂).Challenge (.inl i)` and `pSpec₁.Challenge i` are only *propositionally*
  equal, so no syntactic computation equality holds — only this `evalDist`/`support` form, which is
  exactly what completeness and soundness consume.
* `support_cast_uniformSample` — the support-level analogue (full support both sides), the lighter
  closer for the support-decomposition perfect-completeness route.
* `simulateQ_addLift_liftM_inl` — the oSpec-query half of the per-query step, an exact computation
  equality.

Remaining for the full keystone (see the audit doc): the `Reduction.run` support-decomposition
(perfect completeness) and the soundness union-bound over the intermediate statement, built on top
of these two bridges plus the proven prover-side run factoring (`Prover.append_run_msg`).
-/

open OracleComp OracleSpec ProtocolSpec SubSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- **Atom 1: `liftM`/`map` naturality for `ProbComp → StateT σ ProbComp`.** Pushing a function
through the state lift commutes with the lift. Used to move the challenge response-cast through
the `StateT` lift of the uniform sampler. -/
theorem liftM_map_comm {σ A B : Type} (f : A → B) (x : ProbComp A) :
    (f <$> (liftM x : StateT σ ProbComp A)) = liftM (f <$> x) := by
  simp only [map_eq_pure_bind, liftM_bind, liftM_pure]

/-- **Atom 2: uniform sampling is invariant under transport along a type equality.** For
`h : A = B` with both types sampleable and `A` finite, transporting the uniform sample of `A`
along `cast h` yields exactly the uniform distribution on `B`. This is uniqueness of the
uniform distribution (`probOutput_map_bijective_uniform_cross`) applied to the bijective
`cast h`. It is the distributional core of the challenge seam: the combined and component
challenge types are propositionally equal, and their uniform samplers agree *as distributions*
across that equality even when the `SampleableType` instances are not definitionally the same. -/
theorem evalDist_cast_uniformSample {A B : Type} [SampleableType A] [SampleableType B]
    [Finite A] (h : A = B) :
    evalDist (cast h <$> (uniformSample A)) = evalDist (uniformSample B) := by
  apply evalDist_ext
  intro y
  exact probOutput_map_bijective_uniform_cross (α := A) (β := B)
    (cast h) (cast_bijective h) y

/-- **Atom 2′ (support form): cast-transport preserves the (full) support of uniform sampling.**
For perfect completeness only support containment is needed, and the uniform sampler has full
support on both (propositionally equal) seam challenge types — so the transport is the identity
on supports. This is the lighter closer used by the support-decomposition completeness route. -/
theorem support_cast_uniformSample {A B : Type} [SampleableType A] [SampleableType B] (h : A = B) :
    support (cast h <$> (uniformSample A)) = support (uniformSample B) := by
  rw [support_map]
  ext y
  simp only [Set.mem_image]
  refine ⟨fun _ => SampleableType.mem_support_selectElem _, fun _ => ?_⟩
  exact ⟨cast h.symm y, SampleableType.mem_support_selectElem _, by simp⟩

variable [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {impl : QueryImpl oSpec (StateT σ ProbComp)} {α : Type}

/-- **Bridge, left (oSpec-query) half — exact computation equality.** Simulating an oSpec query
under the combined challenge oracle (lifted from the `pSpec₁` side) is identical to simulating it
under the `pSpec₁` challenge oracle: the lift is the identity on the `oSpec` summand, so both
reduce to `impl`. This is the `Sum.inl` per-query goal of `simulateQ_liftM_eq_of_query`. -/
theorem simulateQ_addLift_liftM_inl (t : ι) :
    simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp)
        (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)))
      (liftM (liftM (OracleSpec.query (spec := oSpec + [pSpec₁.Challenge]ₒ) (Sum.inl t))
          : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)
        : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
      = impl t := by
  rw [show (liftM (liftM (OracleSpec.query (spec := oSpec + [pSpec₁.Challenge]ₒ) (Sum.inl t))
          : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)
        : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
      = liftM (liftM (OracleSpec.query (spec := oSpec + [pSpec₁.Challenge]ₒ) (Sum.inl t))
          : OracleQuery (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) from rfl]
  rw [OracleQuery.liftM_right_add_right_add_query]
  simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
    QueryImpl.add_apply_inl]
  exact id_map (impl t)

/-- **Challenge-oracle seam bridge (left half), at `evalDist`.** Simulating a computation `oa` over
the `pSpec₁`-side oracles under the *combined* challenge oracle (after lifting into the appended
protocol) has the same output distribution as simulating it directly under the `pSpec₁` challenge
oracle. This is the concrete, distributional form of the #433 monad-commutation gap for the message
seam: the per-phase completeness/soundness hypotheses (stated over the component oracle) transfer to
the appended run (which routes through the combined oracle).

The proof folds the lift into the implementation (`liftComp_def` + `QueryImpl.simulateQ_compose`),
then applies `evalDist_simulateQ_run_eq_of_impl_evalDist_eq` with the per-query distributional
equality: the `Sum.inl` (oSpec) queries agree exactly, and the `Sum.inr` (challenge) queries agree
*as distributions* by `liftM_map_comm` + `evalDist_cast_uniformSample` (the seam challenge types are
only propositionally equal, so this is genuinely distributional, not syntactic). -/
theorem evalDist_challengeSeam_bridge_left (oa : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) α)
    (s : σ) :
    evalDist ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
        QueryImpl _ (StateT σ ProbComp))
        (liftM oa : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)).run s)
      = evalDist ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁)) :
        QueryImpl _ (StateT σ ProbComp)) oa).run s) := by
  rw [show (liftM oa : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)
      = OracleComp.liftComp oa _ from rfl]
  rw [OracleComp.liftComp_def, ← QueryImpl.simulateQ_compose]
  apply evalDist_simulateQ_run_eq_of_impl_evalDist_eq
  intro t s'
  rw [QueryImpl.apply_compose]
  cases t with
  | inl t =>
      -- oSpec query: the two implementations agree exactly (computation equality), so a fortiori
      -- in distribution.
      have hcomp : simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
            QueryImpl _ (StateT σ ProbComp))
            (liftM (OracleSpec.query (spec := oSpec + [pSpec₁.Challenge]ₒ) (Sum.inl t))
              : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
          = (impl.addLift (challengeQueryImpl (pSpec := pSpec₁)) :
              QueryImpl _ (StateT σ ProbComp)) (Sum.inl t) := by
        rw [show (liftM (OracleSpec.query (spec := oSpec + [pSpec₁.Challenge]ₒ) (Sum.inl t))
              : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
            = liftM (liftM (OracleSpec.query (spec := oSpec + [pSpec₁.Challenge]ₒ) (Sum.inl t))
                : OracleQuery (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) from rfl]
        rw [OracleQuery.liftM_right_add_right_add_query]
        simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
          QueryImpl.addLift_def, QueryImpl.add_apply_inl]
        exact id_map _
      rw [hcomp]
  | inr t =>
      have h : (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl t.fst) = pSpec₁.Challenge t.fst := by
        simp [ChallengeIdx.inl, ProtocolSpec.append]
      rw [show (liftM (OracleSpec.query (spec := oSpec + [pSpec₁.Challenge]ₒ) (Sum.inr t))
            : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
          = liftM (liftM (OracleSpec.query (spec := oSpec + [pSpec₁.Challenge]ₒ) (Sum.inr t))
              : OracleQuery (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) from rfl]
      rw [OracleQuery.liftM_right_add_right_add_query, simulateQ_query]
      show evalDist (((cast h) <$>
          (liftM (uniformSample ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl t.fst))) :
            StateT σ ProbComp _)).run s')
        = evalDist ((liftM (uniformSample (pSpec₁.Challenge t.fst)) : StateT σ ProbComp _).run s')
      rw [liftM_map_comm]
      rw [show ((liftM ((cast h) <$>
            uniformSample ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl t.fst))) :
            StateT σ ProbComp _).run s')
          = (·, s') <$> ((cast h) <$>
            uniformSample ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl t.fst))) from rfl,
          show ((liftM (uniformSample (pSpec₁.Challenge t.fst)) : StateT σ ProbComp _).run s')
          = (·, s') <$> uniformSample (pSpec₁.Challenge t.fst) from rfl]
      rw [evalDist_map, evalDist_cast_uniformSample h, ← evalDist_map]

/-- **Challenge-oracle seam bridge (right half), at `evalDist`.** The symmetric counterpart of
`evalDist_challengeSeam_bridge_left` for the second protocol `pSpec₂`: simulating a `pSpec₂`-side
computation under the combined challenge oracle equals simulating it under the `pSpec₂` challenge
oracle. Needed for the phase-2 (`Prover.snd`) leg of the soundness/completeness assembly. Same
structure as the left bridge, routing `pSpec₂` challenges through `ChallengeIdx.inr` and
`range_challenge_append_inr`. -/
theorem evalDist_challengeSeam_bridge_right (oa : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) α)
    (s : σ) :
    evalDist ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
        QueryImpl _ (StateT σ ProbComp))
        (liftM oa : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)).run s)
      = evalDist ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) :
        QueryImpl _ (StateT σ ProbComp)) oa).run s) := by
  rw [show (liftM oa : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)
      = OracleComp.liftComp oa _ from rfl]
  rw [OracleComp.liftComp_def, ← QueryImpl.simulateQ_compose]
  apply evalDist_simulateQ_run_eq_of_impl_evalDist_eq
  intro t s'
  rw [QueryImpl.apply_compose]
  cases t with
  | inl t =>
      have hcomp : simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
            QueryImpl _ (StateT σ ProbComp))
            (liftM (OracleSpec.query (spec := oSpec + [pSpec₂.Challenge]ₒ) (Sum.inl t))
              : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
          = (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) :
              QueryImpl _ (StateT σ ProbComp)) (Sum.inl t) := by
        rw [show (liftM (OracleSpec.query (spec := oSpec + [pSpec₂.Challenge]ₒ) (Sum.inl t))
              : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
            = liftM (liftM (OracleSpec.query (spec := oSpec + [pSpec₂.Challenge]ₒ) (Sum.inl t))
                : OracleQuery (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) from rfl]
        rw [OracleQuery.liftM_right_add_right_add_query]
        simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
          QueryImpl.addLift_def, QueryImpl.add_apply_inl]
        exact id_map _
      rw [hcomp]
  | inr t =>
      have h : (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr t.fst) = pSpec₂.Challenge t.fst := by
        simp [ChallengeIdx.inr, ProtocolSpec.append]
      rw [show (liftM (OracleSpec.query (spec := oSpec + [pSpec₂.Challenge]ₒ) (Sum.inr t))
            : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
          = liftM (liftM (OracleSpec.query (spec := oSpec + [pSpec₂.Challenge]ₒ) (Sum.inr t))
              : OracleQuery (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) from rfl]
      rw [OracleQuery.liftM_right_add_right_add_query, simulateQ_query]
      show evalDist (((cast h) <$>
          (liftM (uniformSample ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr t.fst))) :
            StateT σ ProbComp _)).run s')
        = evalDist ((liftM (uniformSample (pSpec₂.Challenge t.fst)) : StateT σ ProbComp _).run s')
      rw [liftM_map_comm]
      rw [show ((liftM ((cast h) <$>
            uniformSample ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr t.fst))) :
            StateT σ ProbComp _).run s')
          = (·, s') <$> ((cast h) <$>
            uniformSample ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr t.fst))) from rfl,
          show ((liftM (uniformSample (pSpec₂.Challenge t.fst)) : StateT σ ProbComp _).run s')
          = (·, s') <$> uniformSample (pSpec₂.Challenge t.fst) from rfl]
      rw [evalDist_map, evalDist_cast_uniformSample h, ← evalDist_map]

/-- **Support corollary of the left bridge** (the exact form the perfect-completeness
support-decomposition consumes): the `run'`-supports of the appended and component simulations
coincide. Derived from `evalDist_challengeSeam_bridge_left` via `mem_support_iff_of_evalDist_eq`. -/
theorem support_challengeSeam_bridge_left (oa : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) α)
    (s : σ) :
    support ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
        QueryImpl _ (StateT σ ProbComp))
        (liftM oa : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)).run' s)
      = support ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁)) :
        QueryImpl _ (StateT σ ProbComp)) oa).run' s) := by
  have h2 : evalDist ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
        QueryImpl _ (StateT σ ProbComp))
        (liftM oa : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)).run' s)
      = evalDist ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁)) :
        QueryImpl _ (StateT σ ProbComp)) oa).run' s) := by
    rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map,
      evalDist_challengeSeam_bridge_left oa s]
  ext x
  exact mem_support_iff_of_evalDist_eq h2 x

/-- **Support corollary of the right bridge** (`pSpec₂` side). -/
theorem support_challengeSeam_bridge_right (oa : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) α)
    (s : σ) :
    support ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
        QueryImpl _ (StateT σ ProbComp))
        (liftM oa : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)).run' s)
      = support ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) :
        QueryImpl _ (StateT σ ProbComp)) oa).run' s) := by
  have h2 : evalDist ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
        QueryImpl _ (StateT σ ProbComp))
        (liftM oa : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)).run' s)
      = evalDist ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) :
        QueryImpl _ (StateT σ ProbComp)) oa).run' s) := by
    rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map,
      evalDist_challengeSeam_bridge_right oa s]
  ext x
  exact mem_support_iff_of_evalDist_eq h2 x

/-- **Support-faithfulness of the appended challenge implementation.** If the base oSpec
implementation `impl` is support-faithful (`hImplSupp`), then so is `impl.addLift challengeQueryImpl`
over the combined `oSpec + [pSpec.Challenge]ₒ`: each query's stateful-run support (first component)
equals the lifted query's support. The oSpec (`Sum.inl`) queries reduce to `hImplSupp`; the challenge
(`Sum.inr`) queries are uniform with full support (`support_challengeQueryImpl_run_eq`), bridged by
`liftM_map_comm`.

This is the gate for the perfect-completeness *support* route: with it,
`ArkLib.ToVCVio.Simulation`'s `support_simulateQ_run'_eq` /
`OptionT.support_run_simulateQ_run'_eq` collapse the whole `simulateQ pImpl … .run' s` layer of the
appended completeness experiment to OracleComp-level `support (run)`, where the run factoring
(`Prover.append_run_msg` + `Verifier.append_run`) and `h₁`/`h₂` apply. (For `pSpec := pSpec₁ ++ₚ
pSpec₂` it gives faithfulness of the appended-protocol challenge implementation.) -/
theorem addLift_challenge_support_faithful {N : ℕ} {pSpec : ProtocolSpec N}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ∀ {β} (q : OracleQuery (oSpec + [pSpec.Challenge]ₒ) β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery
          (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp)) q).run s)
        = support (liftM q : OracleComp (oSpec + [pSpec.Challenge]ₒ) β) := by
  intro β q s
  obtain ⟨t, f⟩ := q
  cases t with
  | inl t =>
      have hh := hImplSupp (⟨t, f⟩ : OracleQuery oSpec β) s
      simp only [QueryImpl.mapQuery, OracleQuery.input,
        QueryImpl.addLift_def, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        liftM, monadLift, MonadLift.monadLift, mem_support_liftM_iff] at hh ⊢
      refine hh.trans ?_
      ext u; constructor <;> rintro ⟨x, hx⟩ <;> exact ⟨x, hx⟩
  | inr t =>
      have hc := support_challengeQueryImpl_run_eq (pSpec := pSpec)
        (⟨t, f⟩ : OracleQuery [pSpec.Challenge]ₒ β) s
      simp only [QueryImpl.mapQuery, OracleQuery.input,
        QueryImpl.addLift_def, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply] at hc ⊢
      rw [← liftM_map_comm] at hc
      refine hc.trans ?_
      ext u; simp only [mem_support_liftM_iff]
      constructor <;> rintro ⟨x, hx⟩ <;> exact ⟨x, hx⟩

end Prover

-- Axiom audit (verified sorry-free / axiom-clean):
#print axioms Prover.liftM_map_comm
#print axioms Prover.evalDist_cast_uniformSample
#print axioms Prover.simulateQ_addLift_liftM_inl
#print axioms Prover.support_cast_uniformSample
#print axioms Prover.evalDist_challengeSeam_bridge_left
#print axioms Prover.evalDist_challengeSeam_bridge_right
#print axioms Prover.support_challengeSeam_bridge_left
#print axioms Prover.support_challengeSeam_bridge_right
