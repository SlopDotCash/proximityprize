/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Completeness

/-!
# LogUp Protocol 2 — canonical `init` / `impl` data facts (issue #13, residual G-initImpl)

The LogUp Protocol 2 completeness statements
(`Logup.logup_completeness_uncond` in `LogupCompletenessUncond.lean`) are universally quantified
over the completeness initialization `init : ProbComp σ` and the shared-oracle implementation
`impl : QueryImpl oSpec (StateT σ ProbComp)`, carrying two standard *data-fact* side conditions:

* `hInit : NeverFail init` — the initialization computation never produces failure mass;
* `hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,`
    `Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftM q)` — the oracle
    implementation is *support-faithful*: simulating a single query reproduces (on its first
    projection) exactly the support of the honest lifted query.

Because the security statements quantify over `init` / `impl`, this file discharges the two
conditions for the **canonical sampler-based instance** that any concrete LogUp completeness call
can supply, turning them from free hypotheses into proven facts:

* the canonical initialization is `pure x` (e.g. `pure () : ProbComp Unit`), whose `NeverFail` is
  immediate from `NeverFail.instPure` — packaged here as `neverFail_pure_init`;
* the canonical oracle implementation is `canonicalQueryImpl oSpec σ`, which samples each query
  uniformly over its (finite, inhabited) response range and threads the simulation state
  unchanged. Its support faithfulness is `canonicalQueryImpl_implSupp`.

## Instantiation into the LogUp statements

For any `σ` and any `init : ProbComp σ` that is a `pure` return, instantiate
`Logup.logup_completeness_uncond` (or the headline `logup_completeness_final`) with

* `init := pure x`, `hInit := neverFail_pure_init x`;
* `impl := canonicalQueryImpl oSpec σ`, `hImplSupp := canonicalQueryImpl_implSupp oSpec σ`.

Both lemmas are stated generically over `oSpec` (with the `oSpec.Fintype` / `oSpec.Inhabited`
instances already present throughout the LogUp completeness development), so they apply verbatim to
the LogUp shared-oracle spec. The remaining residuals of the per-round-bridge route (`hPerRound`,
`hAppend`) are genuinely-deep protocol facts and are *not* touched here; the headline
`logup_completeness_final` route needs neither. A concrete end-to-end instantiation is
`logup_completeness_final_instantiable` (`LogupCompletenessFinal.lean`).

No `sorry` / `sorryAx` / `admit`: each fact is a real proof. The axiom audit at the bottom confirms
axiom-cleanliness (`propext`, `Classical.choice`, `Quot.sound`).
-/

open OracleComp OracleSpec ProtocolSpec

namespace Logup

universe u

section InitImplFacts

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
variable (σ : Type)

/-! ### `hInit`: a pure initialization never fails -/

/-- **Canonical `hInit`.** The standard LogUp completeness initialization is a `pure` return, which
never produces failure mass. This is the data fact required as `hInit : NeverFail init` by every
LogUp completeness statement, discharged for the canonical `init := pure x`. -/
theorem neverFail_pure_init {σ : Type} (x : σ) : NeverFail (pure x : ProbComp σ) :=
  NeverFail.instPure

/-! ### The canonical uniform query implementation -/

/-- Uniform sampler over a finite, inhabited type, landing in plain `ProbComp` (no failure layer).
Samples a uniformly random index in the inclusive range `[0, card-1]` and transports it to the type
via the canonical `Fintype.equivFin` bijection. This is the response distribution of the canonical
honest oracle implementation: full support, uniform mass. -/
noncomputable def uniformProbSampler (α : Type) [Fintype α] [Nonempty α] : ProbComp α :=
  (fun i : Fin (Fintype.card α - 1 + 1) =>
      (Fintype.equivFin α).symm
        (Fin.cast (by have := Fintype.card_pos (α := α); omega) i))
    <$> ($[0.. (Fintype.card α - 1)])

/-- The uniform sampler hits every element: its support is all of `α`. This is the key fact making
the canonical implementation *support-faithful* with respect to the honest lifted query. -/
@[simp] theorem support_uniformProbSampler (α : Type) [Fintype α] [Nonempty α] :
    support (uniformProbSampler α) = Set.univ := by
  unfold uniformProbSampler
  rw [support_map]
  have huniv : support ($[0.. (Fintype.card α - 1)] : ProbComp _) = Set.univ := by
    show support (ProbComp.uniformFin (Fintype.card α - 1)) = Set.univ
    rw [ProbComp.uniformFin]
    exact support_query _
  rw [huniv, Set.image_univ, Set.range_eq_univ]
  intro a
  refine ⟨Fin.cast (by have := Fintype.card_pos (α := α); omega) ((Fintype.equivFin α) a), ?_⟩
  simp

/-- **The canonical sampler-based oracle implementation.** Each query `t : oSpec.Domain` is answered
by sampling uniformly from its (finite, inhabited) response range `oSpec.Range t`, with the
simulation state `σ` threaded through unchanged. This is the standard honest implementation supplied
to the LogUp completeness statements as `impl`. -/
noncomputable def canonicalQueryImpl :
    QueryImpl oSpec (StateT σ ProbComp) :=
  fun t => liftM (uniformProbSampler (oSpec.Range t))

/-! ### `hImplSupp`: the canonical implementation is support-faithful -/

/-- **Canonical `hImplSupp`.** Simulating a single oracle query under `canonicalQueryImpl` and
reading off the first projection of the support reproduces exactly the support of the honest
lifted query `liftM q`. This is the data fact required as `hImplSupp` by every LogUp completeness
statement, discharged for the canonical `impl := canonicalQueryImpl oSpec σ`.

The proof unfolds `mapQuery`, runs the lifted `StateT` sampler from state `s` (the state is left
untouched), and uses `support_uniformProbSampler` (full support of the uniform sampler) together
with `support_liftM` (`support (liftM q) = Set.range q.cont`). -/
theorem canonicalQueryImpl_implSupp {β : Type}
    (q : OracleQuery oSpec β) (s : σ) :
    Prod.fst <$> support (((canonicalQueryImpl oSpec σ).mapQuery q).run s)
      = support (liftM q : OracleComp oSpec β) := by
  rw [QueryImpl.mapQuery]
  change Prod.fst <$>
      support ((q.cont <$> (liftM (uniformProbSampler (oSpec.Range q.input)) :
        StateT σ ProbComp _)).run s) = _
  rw [StateT.run_map, StateT.run_liftM, support_liftM, support_map, support_bind]
  simp only [support_pure, support_uniformProbSampler, Set.fmap_eq_image]
  ext y
  simp only [Set.mem_image, Set.mem_iUnion, Set.mem_univ, Set.iUnion_true, Set.mem_singleton_iff,
    Set.mem_range, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨a₁, b₁, ⟨i, hi⟩, heq⟩, rfl⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hi
    exact ⟨a₁, congrArg Prod.fst heq⟩
  · rintro ⟨x, rfl⟩
    exact ⟨q.cont x, s, ⟨x, s, ⟨x, rfl⟩, rfl⟩, rfl⟩

/-- The canonical `hImplSupp` phrased with `OracleReduction.liftQuery` (definitionally `liftM`), the
form taken by the generic `OracleReduction` completeness characterizations. -/
theorem canonicalQueryImpl_implSupp_liftQuery {β : Type}
    (q : OracleQuery oSpec β) (s : σ) :
    Prod.fst <$> support (((canonicalQueryImpl oSpec σ).mapQuery q).run s)
      = support (OracleReduction.liftQuery q) :=
  canonicalQueryImpl_implSupp oSpec σ q s

end InitImplFacts

end Logup

/- Axiom audit for the canonical LogUp `init` / `impl` data facts. -/
#print axioms Logup.neverFail_pure_init
#print axioms Logup.support_uniformProbSampler
#print axioms Logup.canonicalQueryImpl_implSupp
#print axioms Logup.canonicalQueryImpl_implSupp_liftQuery
