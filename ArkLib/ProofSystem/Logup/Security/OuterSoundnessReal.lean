/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SoundnessConverse
import ArkLib.ProofSystem.Logup.Security.OuterRun
import ArkLib.ProofSystem.Logup.Security.OuterCompleteness
import ArkLib.Data.Probability.Instances
import ArkLib.Data.Probability.MarginalBound
import Mathlib.Algebra.Polynomial.Roots

/-!
# LogUp Protocol 2 — the *corrected* outer-phase soundness (issue #13)

`Logup.OuterSoundnessResidual` (`Security/SubPhaseSplit.lean`) is **degenerate**. Its intermediate
language is `midLanguage`, which after the outer phase always *contains* the (verifier-honest)
after-outer statement: with the honest helper/multiplicity oracles the sumcheck claim is the grand
sum, which the algebra makes a tautology, so demanding `Pr[outer accepts ↦ midLanguage] ≤ ε` for a
genuinely *bad* input is false — the outer phase always "lands" in `midLanguage`. The genuine
soundness obstruction is not the *outer phase landing in a language*, it is the **algebraic check
polynomial vanishing at the random challenge**.

This file states and *proves* the corrected, non-degenerate outer soundness statement:

> for a **bad** lookup input (`∉ inputRelation`), the cleared grand-sum check polynomial
> `grandSumCheckPoly oStmt` is *nonzero* (`grandSumCheckPoly_ne_zero_of_bad_lookup`), so a uniformly
> sampled outer challenge `x` makes the check **appear to pass** — i.e. lands the after-outer
> statement in the genuine claim language `midSoundnessLanguage` — only with **Schwartz–Zippel
> probability** `≤ natDegree (grandSumCheckPoly oStmt) / |F|`.

## What is proved fully here (no `sorry`, no named hypothesis)

* `Logup.midSoundnessLanguage` — the *genuine* intermediate language: the after-outer statements
  whose grand-sum check polynomial vanishes at the sampled challenge `x = stmt.xChallenge`, i.e. the
  lookup *appears valid* for that intermediate state. This is non-degenerate: it is **not**
  `Set.univ`; for a bad lookup it is hit only on the (few) roots of a nonzero polynomial.
* `Logup.prob_grandSumCheckPoly_root_le` — single-variable Schwartz–Zippel: for *any* nonzero
  `p : F[X]`, `Pr_{x ←$ᵖ F}[ p.eval x = 0 ] ≤ natDegree p / |F|`. Proved from Mathlib's
  `Polynomial.card_roots'` exactly as the in-tree weakened-KState bridge does.
* `Logup.grandSumCheckPoly_natDegree_le` — the degree of the check polynomial is `≤ |F| - 1`
  (every product summand ranges over `univ.erase a`, of size `|F| - 1`), giving a *uniform*
  closed-form SZ error.
* `Logup.outerSoundness_real` — the headline: for a bad input, the probability that a uniformly
  sampled outer challenge lands the check in `midSoundnessLanguage` (claim *appears* true) is at
  most `natDegree (grandSumCheckPoly oStmt) / |F| ≤ (|F| - 1) / |F|`. This is the **true** outer
  soundness bound the degenerate residual should have asked for.

## The one genuine residual (a named hypothesis, not a `sorry`)

Connecting this challenge-level SZ bound to the *protocol-level* `OuterSoundnessResidual`
(`(outerVerifier …).soundness …`) requires unfolding `Reduction.run` of the outer phase to show that
the after-outer statement's `xChallenge` field *is* the uniformly sampled outer challenge and that
the verifier's acceptance event coincides with the check-vanishing event. That `simulateQ`/`run`
unfolding (the prover-run composition side) is the deep monad-plumbing wall flagged throughout
`Security/**`; it is taken here as the explicit, clearly-named hypothesis
`OuterRunSamplesChallenge` of `Logup.outerSoundnessResidual_real_of_runUnfolding`. Everything *else*
— the Schwartz–Zippel mathematics that makes the bound true — is closed unconditionally above.
-/

open scoped NNReal ENNReal
open Polynomial Finset ProbabilityTheory

namespace Logup

section OuterSoundnessReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M : ℕ}

/-! ### Single-variable Schwartz–Zippel for the grand-sum check polynomial -/

/-- **Univariate Schwartz–Zippel (root probability).** For a *nonzero* polynomial `p : F[X]`, a
uniformly sampled challenge `x` is a root of `p` with probability at most `natDegree p / |F|`.

Proved exactly as the in-tree weakened-KState bridge (`KStateWeaken.prob_badPolyAgreement_le`): the
root set has cardinality at most `natDegree p` by `Polynomial.card_roots'`, and uniform sampling
turns that count into the probability `(#roots)/|F| ≤ natDegree p / |F|`. -/
theorem prob_grandSumCheckPoly_root_le (p : F[X]) (hp : p ≠ 0) :
    Pr_{ let x ←$ᵖ F }[ p.eval x = 0 ] ≤ (p.natDegree : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
  classical
  rw [prob_uniform_eq_card_filter_div_card]
  -- The root set is contained in `p.roots.toFinset`, of size `≤ natDegree p`.
  have hsub :
      (Finset.univ.filter (fun x : F => p.eval x = 0)) ⊆ p.roots.toFinset := by
    intro x hx
    rw [Finset.mem_filter] at hx
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hx.2)
  have hcard :
      (Finset.univ.filter (fun x : F => p.eval x = 0)).card ≤ p.natDegree :=
    calc (Finset.univ.filter (fun x : F => p.eval x = 0)).card
        ≤ p.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card p.roots := p.roots.toFinset_card_le
      _ ≤ p.natDegree := Polynomial.card_roots' p
  have hnum :
      ((Finset.univ.filter (fun x : F => p.eval x = 0)).card : ℝ≥0) ≤ (p.natDegree : ℝ≥0) := by
    exact_mod_cast hcard
  gcongr

/-- The grand-sum check polynomial has degree `≤ |F| - 1`: every summand is
`C (coeff) * ∏_{b ∈ univ.erase a} (X + C b)`, a product of `|F| - 1` monic linear factors, hence of
degree at most `|F| - 1`. This gives a *uniform* (input-independent) Schwartz–Zippel error. -/
theorem grandSumCheckPoly_natDegree_le (oStmt : ∀ i, OStmtIn F n M i) :
    (grandSumCheckPoly oStmt).natDegree ≤ Fintype.card F - 1 := by
  classical
  unfold grandSumCheckPoly
  refine Polynomial.natDegree_sum_le_of_forall_le (S := F) (s := Finset.univ)
    (f := fun a : F => Polynomial.C (if tableMultiplicityCount oStmt a = 0
        then (lookupMultiplicityCount oStmt a : F) else 0) *
      ∏ b ∈ Finset.univ.erase a, (Polynomial.X + Polynomial.C b)) ?_
  intro a _
  -- bound the degree of one summand `C c * ∏_{b ∈ erase a}(X + C b)`
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  -- each factor `X + C b` has degree ≤ 1
  have hfac : ∀ b ∈ Finset.univ.erase a,
      (Polynomial.X + Polynomial.C b : F[X]).natDegree ≤ 1 := by
    intro b _
    exact le_trans (Polynomial.natDegree_add_le _ _)
      (by simp [Polynomial.natDegree_X, Polynomial.natDegree_C])
  calc (∑ b ∈ Finset.univ.erase a, (Polynomial.X + Polynomial.C b : F[X]).natDegree)
      ≤ ∑ _b ∈ Finset.univ.erase a, 1 := Finset.sum_le_sum hfac
    _ = (Finset.univ.erase a).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ = Fintype.card F - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]

/-! ### The genuine intermediate "claim is true" language -/

/-- **The genuine soundness intermediate language.** A pair `(stmt, oStmt)` of an after-outer
statement and its oracle statements is in `midSoundnessLanguage` when the cleared grand-sum check
polynomial vanishes at the *outer challenge carried by `stmt`*, i.e. `grandSumCheckPoly oStmt`
evaluated at `stmt.xChallenge` is `0`. This is the genuine claim relation — "the lookup *appears*
valid for this intermediate state" — and, unlike the degenerate `midLanguage`, it is **not**
`Set.univ`: for a bad lookup `grandSumCheckPoly oStmt ≠ 0`, so membership pins `stmt.xChallenge`
to one of the finitely many roots of a nonzero polynomial. -/
def midSoundnessLanguage (oStmt : ∀ i, OStmtIn F n M i) : Set F :=
  { x : F | (grandSumCheckPoly oStmt).eval x = 0 }

/-- For a *bad* lookup the genuine intermediate language is **proper** (not all of `F`): there is a
challenge value at which the check polynomial does not vanish. This certifies that
`midSoundnessLanguage` is non-degenerate — the corrected statement is not vacuous. -/
theorem midSoundnessLanguage_ne_univ_of_bad_lookup
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M)) :
    midSoundnessLanguage oStmt ≠ Set.univ := by
  intro huniv
  -- if `midSoundnessLanguage = univ` then `grandSumCheckPoly` vanishes everywhere
  have hzero : ∀ x : F, (grandSumCheckPoly oStmt).eval x = 0 := by
    intro x
    have : x ∈ midSoundnessLanguage oStmt := by rw [huniv]; trivial
    exact this
  -- a nonzero polynomial has only finitely many roots; `grandSumCheckPoly ≠ 0` for a bad lookup,
  -- so it cannot vanish at *every* point unless the field is finite and small — but we get a
  -- direct contradiction via the proven nonvanishing-at-`-a₀` evaluation inside the converse lemma.
  have hne := grandSumCheckPoly_ne_zero_of_bad_lookup stmt oStmt hBad
  obtain ⟨a₀, hlook, htab⟩ := bad_lookup_exists_column_only_value stmt oStmt hBad
  -- evaluate at `-a₀`; the converse lemma's computation shows this is nonzero
  have heval := hzero (-a₀)
  rw [eval_grandSumCheckPoly] at heval
  -- reuse the exact vanishing argument: only the `a₀` summand survives
  have hterms : ∀ a ∈ (Finset.univ : Finset F), a ≠ a₀ →
      (if tableMultiplicityCount oStmt a = 0 then (lookupMultiplicityCount oStmt a : F) else 0) *
        ∏ b ∈ Finset.univ.erase a, (-a₀ + b) = 0 := by
    intro a _ hane
    exact mul_eq_zero_of_right _
      (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hane, Finset.mem_univ a₀⟩)
        (neg_add_cancel a₀))
  rw [Finset.sum_eq_single a₀ hterms (fun hni => absurd (Finset.mem_univ a₀) hni)] at heval
  rw [if_pos htab] at heval
  rcases mul_eq_zero.mp heval with hc | hprod
  · exact lookupMultiplicityCount_natCast_ne_zero stmt oStmt a₀ hlook hc
  · rw [Finset.prod_eq_zero_iff] at hprod
    obtain ⟨b, hb, hb0⟩ := hprod
    rw [Finset.mem_erase] at hb
    exact hb.1 (by linear_combination hb0)

/-! ### The corrected outer soundness theorem -/

/-- **Corrected outer soundness (challenge level).** For a **bad** lookup input
(`∉ inputRelation`), a uniformly sampled outer challenge `x` lands in the genuine claim language
`midSoundnessLanguage oStmt` — i.e. makes the cleared grand-sum check *appear to pass* — with
probability at most the Schwartz–Zippel error `natDegree (grandSumCheckPoly oStmt) / |F|`.

This is the **non-degenerate replacement** for `OuterSoundnessResidual`: the soundness obstruction
is the algebraic check polynomial vanishing at the random challenge, and a bad lookup makes it
nonzero (`grandSumCheckPoly_ne_zero_of_bad_lookup`), so it vanishes only on its `≤ natDegree`
roots. -/
theorem outerSoundness_real
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M)) :
    Pr_{ let x ←$ᵖ F }[ x ∈ midSoundnessLanguage oStmt ]
      ≤ ((grandSumCheckPoly oStmt).natDegree : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
  have hne := grandSumCheckPoly_ne_zero_of_bad_lookup stmt oStmt hBad
  -- membership in `midSoundnessLanguage x` is *definitionally* the root event `eval x = 0`, so the
  -- two `Pr_{…}[…]` expressions coincide and the univariate SZ bound applies directly.
  show Pr_{ let x ←$ᵖ F }[ (grandSumCheckPoly oStmt).eval x = 0 ]
      ≤ ((grandSumCheckPoly oStmt).natDegree : ℝ≥0) / (Fintype.card F : ℝ≥0)
  exact prob_grandSumCheckPoly_root_le (grandSumCheckPoly oStmt) hne

/-- **Corrected outer soundness with the uniform closed-form error.** The same statement with the
input-independent Schwartz–Zippel error `(|F| - 1) / |F|` obtained from
`grandSumCheckPoly_natDegree_le`. This is the cleanest paper-shaped outer soundness bound: a bad
lookup passes the outer algebraic check at a random challenge with probability `≤ (|F| - 1)/|F|`,
strictly less than `1` whenever `F` is nontrivial. -/
theorem outerSoundness_real_uniformError
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M)) :
    Pr_{ let x ←$ᵖ F }[ x ∈ midSoundnessLanguage oStmt ]
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
  refine le_trans (outerSoundness_real stmt oStmt hBad) ?_
  gcongr
  · exact_mod_cast Nat.cast_le.mpr (grandSumCheckPoly_natDegree_le oStmt)

/-! ### Bridging to the protocol-level residual: the one named run-unfolding gap -/

/-- **The genuine residual interface: the outer run samples the challenge.** This is the *only* gap
between the proven challenge-level Schwartz–Zippel bound and a protocol-level outer-soundness
statement: it asserts that the outer verifier's acceptance probability for a bad input — landing the
after-outer statement in the *genuine* claim language — is bounded by the same uniform-challenge
event probability `Pr_{x ←$ᵖ F}[ x ∈ midSoundnessLanguage oStmt ]`. Discharging it requires unfolding
`Reduction.run` of the outer phase (the prover-run composition side: the after-outer `xChallenge` is
the uniformly sampled outer challenge, and the verifier accepts iff the check vanishes). That is the
deep `simulateQ`/`run` monad-plumbing wall flagged throughout `Security/**`; it is kept here as an
explicit, clearly-named hypothesis rather than hidden behind `sorryAx`. -/
def OuterRunSamplesChallenge
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (outerBadAcceptProb : ℝ≥0∞) : Prop :=
  outerBadAcceptProb ≤ Pr_{ let x ←$ᵖ F }[ x ∈ midSoundnessLanguage oStmt ]

/-! ### Discharging `OuterRunSamplesChallenge` from the run's round-1 challenge draw

`OuterRunSamplesChallenge stmt oStmt outerBadAcceptProb` is, as a `Prop`, *false* for an arbitrary
`outerBadAcceptProb` (e.g. `1`): it can only hold once `outerBadAcceptProb` is the **actual** outer
run's bad-accept probability. The theorem below discharges it for that real value, for any run that
is in the canonical *challenge-first* shape `liftM (getChallenge ⟨1, rfl⟩) >>= k` exposed by the
prover's round-by-round run closed form (`outerProver_run_closed_form` peels the run to exactly the
round-1 `x` draw and round-3 `batch` draw with the round-0 message a pure step). It feeds the
challenge-coherence decomposition `probEvent_run'_simulateQ_addLift_getChallenge_bind` (the run's
event probability is the uniform average over the sampled `x` of the tail's event probability) and
the **verifier-collapse support fact** `hsupp` — proven from the compiled-verifier closed form
`simulateQ_outerVerify_eq`: a surviving run carries `xChallenge = x`, so acceptance into the genuine
claim language forces `x ∈ midSoundnessLanguage oStmt`. The result is exactly the
`OuterRunSamplesChallenge` inequality with the real run probability plugged in. -/

open OracleComp OracleSpec ProtocolSpec in
/-- The round-1 LogUp outer challenge is oracle-accessible (uniform challenge oracle interface),
needed to name the combined oracle spec `oSpec + [(outerPSpec F n params).Challenge]ₒ`. -/
local instance instOuterSoundnessChallengeOI {n : ℕ} {M : ℕ} {params : ProtocolParams M} :
    ∀ i, OracleInterface ((outerPSpec F n params).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

open OracleComp OracleSpec ProtocolSpec

omit [DecidableEq F] in
/-- **Uniform-marginal transport across a challenge-type equality.** For a type `C` carrying a
`Fintype` structure and a *propositional* equality `C = F` (true definitionally for the LogUp
round-1 challenge type `(outerPSpec F n params).Challenge ⟨1, rfl⟩`), a per-element weight
`g : C → ℝ≥0∞` that vanishes off `L` (membership transported through `C = F` via `mem`) and is
pointwise below the uniform mass `(card F)⁻¹` has total mass at most `Pr_{x ←$ᵖ F}[ x ∈ L ]`. Both
sides evaluate to `(#L)/|F|`; the non-defeq `Fintype` instances on `C` and `F` are reconciled by
proof-irrelevance of `Fintype`. This is the bridge that turns the challenge-coherence decomposition's
`∑' c, Pr[= c | $ᵗ C] * …` marginal into the `OuterRunSamplesChallenge` right side. -/
theorem tsum_uniform_challenge_mem_le_prob_uniform
    (L : Set F) [DecidablePred (· ∈ L)]
    {C : Type} [Fintype C] (hTy : C = F)
    (g : C → ℝ≥0∞) (mem : C → Prop)
    (hmemTransport : ∀ c : C, mem c ↔ (hTy ▸ c) ∈ L)
    (hg : ∀ c : C, ¬ mem c → g c = 0)
    (hgle : ∀ c : C, g c ≤ (Fintype.card F : ℝ≥0∞)⁻¹) :
    (∑' c : C, g c) ≤ Pr_{ let x ←$ᵖ F }[ x ∈ L ] := by
  classical
  -- Bound the tsum by the uniform measure of `L` over the challenge type `C`.
  have hbound :
      (∑' c : C, g c)
        ≤ ∑' c : C, (if (hTy ▸ c) ∈ L then (Fintype.card F : ℝ≥0∞)⁻¹ else 0) := by
    refine ENNReal.tsum_le_tsum (fun c => ?_)
    by_cases hc : (hTy ▸ c) ∈ L
    · rw [if_pos hc]; exact hgle c
    · rw [if_neg hc, hg c (fun h => hc ((hmemTransport c).mp h))]
  refine le_trans hbound ?_
  -- Compute both sides as `(#L)/|F|`.
  rw [prob_uniform_eq_card_filter_div_card (F := F)]
  rw [tsum_fintype]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  -- both sides are `((#filter) : ℝ≥0∞) * (card F)⁻¹`; subst the challenge-type equality so the two
  -- filtered universes coincide up to a proof-irrelevant `Fintype` instance, then reconcile.
  subst hTy
  refine le_of_eq ?_
  simp only [ENNReal.coe_natCast]
  -- the two filtered finsets differ only in their (proof-irrelevant) `Fintype` instance on `C`.
  congr 3
  exact Finset.ext fun a => by simp [Finset.mem_filter]

/-- **Discharge of `OuterRunSamplesChallenge` for the real outer run (challenge-first shape).**

Let the outer reduction run be simulated, from state `s`, in the canonical *challenge-first* form
`liftM (getChallenge ⟨1, rfl⟩) >>= k` — the round-1 `x` draw exposed at the head by the prover's
run closed form — with acceptance event `p`. If, for every drawn challenge `c` that is **not** in
`midSoundnessLanguage oStmt`, the tail run has acceptance probability `0` (the verifier-collapse
support fact `hsupp`, true because a surviving run carries `xChallenge = c`, so acceptance into the
genuine claim language forces `c ∈ midSoundnessLanguage`), then the run's bad-accept probability is
at most `Pr_{x ←$ᵖ F}[ x ∈ midSoundnessLanguage oStmt ]` — i.e. `OuterRunSamplesChallenge` holds for
the real run probability. The challenge-average decomposition is the in-tree key brick
`ChallengeCoherence.probEvent_run'_simulateQ_addLift_getChallenge_bind`. -/
theorem OuterRunSamplesChallenge_holds_of_getChallenge_run
    [SampleableType F] [Inhabited F] {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (params : ProtocolParams M)
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (s : σ)
    {β : Type}
    (k : (outerPSpec F n params).Challenge ⟨1, rfl⟩ →
      OracleComp (oSpec + [(outerPSpec F n params).Challenge]ₒ) β)
    (p : β → Prop)
    (hsupp : ∀ c : (outerPSpec F n params).Challenge ⟨1, rfl⟩,
      (show F from c) ∉ midSoundnessLanguage oStmt →
      Pr[p | (simulateQ (QueryImpl.addLift impl ProtocolSpec.challengeQueryImpl :
          QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
          (k c)).run' s] = 0) :
    OuterRunSamplesChallenge stmt oStmt
      (Pr[p | (simulateQ (QueryImpl.addLift impl ProtocolSpec.challengeQueryImpl :
          QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
          ((liftM (ProtocolSpec.getChallenge (outerPSpec F n params) ⟨1, rfl⟩) :
              OracleComp (oSpec + [(outerPSpec F n params).Challenge]ₒ)
                ((outerPSpec F n params).Challenge ⟨1, rfl⟩)) >>= k)).run' s]) := by
  classical
  haveI hfinC : Fintype ((outerPSpec F n params).Challenge ⟨1, rfl⟩) :=
    (inferInstance : Fintype F)
  -- Expand the run's event probability as the uniform average over the sampled challenge.
  unfold OuterRunSamplesChallenge
  rw [ChallengeCoherence.probEvent_run'_simulateQ_addLift_getChallenge_bind
        impl s ⟨1, rfl⟩ k p]
  -- Apply the challenge-type uniform-marginal transport. The per-term mass is the uniform challenge
  -- mass `(card F)⁻¹`, and out-of-language terms vanish by the verifier-collapse support fact
  -- `hsupp`. The `$ᵗ` instance is written explicitly as the `∀ i`-instance the challenge-coherence
  -- brick produces, so the masses match syntactically.
  refine tsum_uniform_challenge_mem_le_prob_uniform (midSoundnessLanguage oStmt)
    (C := (outerPSpec F n params).Challenge ⟨1, rfl⟩) rfl
    (fun c => Pr[= c | (@uniformSample ((outerPSpec F n params).Challenge ⟨1, rfl⟩)
        (instOuterPSpecChallengeSampleable ⟨1, rfl⟩))] *
      Pr[p | (simulateQ (QueryImpl.addLift impl ProtocolSpec.challengeQueryImpl :
          QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
          (k c)).run' s])
    (fun c => (show F from c) ∈ midSoundnessLanguage oStmt)
    (fun c => Iff.rfl) ?_ ?_
  · intro c hc
    simp only []
    rw [hsupp c hc, mul_zero]
  · intro c
    simp only []
    -- `mass c * tail c ≤ (card F)⁻¹`: the mass is exactly `(card F)⁻¹` and `tail c ≤ 1`.
    have hmass : Pr[= c | (@uniformSample ((outerPSpec F n params).Challenge ⟨1, rfl⟩)
        (instOuterPSpecChallengeSampleable ⟨1, rfl⟩))] = (Fintype.card F : ℝ≥0∞)⁻¹ := by
      rw [probOutput_uniformSample]
      congr 1
      exact congrArg Nat.cast (Fintype.card_congr (Equiv.cast (rfl : _ = F)))
    rw [hmass]
    exact le_trans (mul_le_mul' le_rfl probEvent_le_one) (by rw [mul_one])

/-- The result type of the outer LogUp oracle-reduction run: the prover transcript and output
pair, paired with the verifier's recomputed output statement pair. -/
abbrev outerRunResult {ι : Type} (oSpec : OracleSpec ι) (params : ProtocolParams M) :=
  (((outerPSpec F n params).FullTranscript ×
      (StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) × Unit) ×
    StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i))

set_option maxHeartbeats 1000000 in
/-- **Unconditional discharge of `OuterRunSamplesChallenge` for the real outer run.**

The conditional `OuterRunSamplesChallenge_holds_of_getChallenge_run` discharges the residual
*assuming* the simulated run is already in the canonical *challenge-first* shape
`liftM (getChallenge ⟨1, rfl⟩) >>= k`.  This theorem discharges that run-shape hypothesis outright
for the **actual** outer oracle reduction `outerOracleReduction`: the prover's round-by-round run
closed form (`outerProver_run_closed_form`) places the round-1 `x`-challenge draw at the head once
the pure round-0 multiplicity message is collapsed (`pure_bind`), so the whole simulated run *is*
in challenge-first shape.  Feeding the challenge-coherence decomposition
(`ChallengeCoherence.probEvent_run'_simulateQ_addLift_getChallenge_bind`) and the uniform-marginal
transport (`tsum_uniform_challenge_mem_le_prob_uniform`), with the verifier-collapse support fact
proven internally (a surviving run carries `xChallenge = the drawn challenge` by
`outerVerifier_run_accept_eq_pure` + the readback `outerProver_transcript_challenge_readback`, so
acceptance into the genuine claim language forces the drawn challenge into
`midSoundnessLanguage oStmt`), gives the full `OuterRunSamplesChallenge` inequality with the real
run's bad-accept probability plugged in.  This is the protocol-level outer-run-marginal that the
conditional theorem assumed, now closed unconditionally for the honest outer reduction. -/
theorem OuterRunSamplesChallenge_holds
    [Fact ((-1 : F) ≠ 1)] [SampleableType F] [Inhabited F]
    {ι : Type} (oSpec : OracleSpec ι) (params : ProtocolParams M)
    {σ : Type} (impl : QueryImpl oSpec (StateT σ ProbComp)) (s : σ)
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (witIn : WitIn F n M params) :
    OuterRunSamplesChallenge stmt oStmt
      (Pr[(fun o : Option (outerRunResult oSpec params) =>
            o.elim False (fun result => result.2.1.xChallenge ∈ midSoundnessLanguage oStmt))
          | ((simulateQ (QueryImpl.addLift impl ProtocolSpec.challengeQueryImpl :
              QueryImpl (oSpec + [(outerPSpec F n params).Challenge]ₒ) (StateT σ ProbComp))
              (((outerOracleReduction oSpec F n M params).toReduction.run
                  (stmt, oStmt) witIn).run)).run' s)]) := by
  classical
  haveI hfinC : Fintype ((outerPSpec F n params).Challenge ⟨1, rfl⟩) :=
    (inferInstance : Fintype F)
  -- Unfold the residual, place the simulated run in challenge-first shape via the prover-run closed
  -- form (the pure round-0 message collapses, exposing the round-1 `x`-challenge at the head).
  unfold OuterRunSamplesChallenge
  rw [outerReduction_run_closed_form, optionT_lift_bind_run, outerProver_run_closed_form]
  simp only [outerProver, bind_pure_comp, pure_bind, map_pure, bind_assoc, liftM_pure]
  -- Challenge-coherence: the run's event probability is the uniform average over the drawn `x` of the
  -- tail's event probability.
  rw [ChallengeCoherence.probEvent_run'_simulateQ_addLift_getChallenge_bind]
  -- Uniform-marginal transport: out-of-language terms vanish (verifier-collapse), each mass `≤ |F|⁻¹`.
  refine tsum_uniform_challenge_mem_le_prob_uniform (midSoundnessLanguage oStmt)
    (C := (outerPSpec F n params).Challenge ⟨1, rfl⟩) rfl
    _
    (fun c => (show F from c) ∈ midSoundnessLanguage oStmt)
    (fun c => Iff.rfl) ?hg ?hgle
  case hgle =>
    intro c
    have hmass : Pr[= c | (@uniformSample ((outerPSpec F n params).Challenge ⟨1, rfl⟩)
        (instOuterPSpecChallengeSampleable ⟨1, rfl⟩))] = (Fintype.card F : ℝ≥0∞)⁻¹ := by
      rw [probOutput_uniformSample]
      congr 1
      exact congrArg Nat.cast (Fintype.card_congr (Equiv.cast (rfl : _ = F)))
    rw [hmass]
    exact le_trans (mul_le_mul' le_rfl probEvent_le_one) (by rw [mul_one])
  case hg =>
    -- Verifier-collapse support fact: for a drawn challenge `c ∉ midSoundnessLanguage oStmt`, the
    -- tail run has acceptance probability `0`, because every surviving run carries `xChallenge = c`.
    intro c hc
    rw [mul_eq_zero]
    right
    rw [probEvent_eq_zero_iff]
    intro o ho hbad
    cases o with
    | none => exact hbad
    | some result =>
      -- Chase the support down to the verifier run on the closed-form transcript (round-1 = `c`).
      have hsub := _root_.support_simulateQ_run'_subset (impl.addLift challengeQueryImpl) _ s ho
      rw [support_bind] at hsub
      simp only [Set.mem_iUnion, exists_prop] at hsub
      obtain ⟨tr, htr, hverif⟩ := hsub
      rw [support_map] at htr
      obtain ⟨batch, _, rfl⟩ := htr
      -- The transcript carries `c` as its round-1 challenge.
      have hreadback := (outerProver_transcript_challenge_readback F n M params
          (m₀ := honestMultiplicity oStmt) (x := c)
          (m₂ := honestHelpers params oStmt c) (batch := batch)).1
      by_cases hacc : outerVerifyAccepts F n M oStmt c
      · -- Accept: the verifier returns a pure `some` whose `xChallenge` is `chalX … = c`.
        rw [optionT_run_bind, outerVerifier_run_accept_eq_pure oSpec F n M params (stmt, oStmt) _
            (hreadback.symm ▸ hacc)] at hverif
        simp only [liftM_pure, OptionT.run_pure, pure_bind, Option.getM] at hverif
        rw [← bind_pure_comp, optionT_run_bind, OptionT.run_pure, pure_bind] at hverif
        simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff] at hverif
        obtain rfl := Option.some.inj hverif
        simp only [Option.elim_some] at hbad
        exact hc (hreadback ▸ hbad)
      · -- Reject: the verifier fails, so no `some` output survives — `hverif` is absurd.
        rw [optionT_run_bind, outerVerifier_run_reject_eq_none oSpec F n M params (stmt, oStmt) _
            (hreadback.symm ▸ hacc)] at hverif
        simp only [liftM_pure, OptionT.run_pure, pure_bind, Option.getM] at hverif
        rw [← bind_pure_comp, failure_bind, OptionT.run_failure, support_pure] at hverif
        simp only [Set.mem_singleton_iff, reduceCtorEq] at hverif

/-- **Protocol-level corrected outer soundness, modulo the run-unfolding residual.** Given the named
run-unfolding bridge `OuterRunSamplesChallenge` (the after-outer challenge is the uniformly sampled
outer challenge and acceptance is the check-vanishing event), the outer phase maps a bad lookup into
the genuine claim language with probability bounded by the Schwartz–Zippel error. The mathematics is
discharged unconditionally by `outerSoundness_real`; only the monad-plumbing bridge is assumed. -/
theorem outerSoundnessResidual_real_of_runUnfolding
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M))
    (outerBadAcceptProb : ℝ≥0∞)
    (hRun : OuterRunSamplesChallenge stmt oStmt outerBadAcceptProb) :
    outerBadAcceptProb ≤ ((grandSumCheckPoly oStmt).natDegree : ℝ≥0) / (Fintype.card F : ℝ≥0) :=
  le_trans hRun (outerSoundness_real stmt oStmt hBad)

end OuterSoundnessReal

end Logup

/- Axiom audit for the corrected #13 outer-soundness bricks. -/
#print axioms Logup.prob_grandSumCheckPoly_root_le
#print axioms Logup.grandSumCheckPoly_natDegree_le
#print axioms Logup.midSoundnessLanguage_ne_univ_of_bad_lookup
#print axioms Logup.outerSoundness_real
#print axioms Logup.outerSoundness_real_uniformError
#print axioms Logup.outerSoundnessResidual_real_of_runUnfolding
#print axioms Logup.tsum_uniform_challenge_mem_le_prob_uniform
#print axioms Logup.OuterRunSamplesChallenge_holds_of_getChallenge_run
#print axioms Logup.OuterRunSamplesChallenge_holds
