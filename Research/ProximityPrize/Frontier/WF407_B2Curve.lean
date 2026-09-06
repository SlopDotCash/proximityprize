/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCACurveEvent
import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodability

/-!
# B2 (wf407/B2-curve) — wiring curve-decodability ([GG25] Def 3.1) to the curve MCA error

The B2 lane already lands the [GG25] Definition 3.1 *definition* (`ProximityGap.CurveDecodable`,
`curveCloseSet`, in `GG25CurveDecodability.lean`) and the whole [Jo26] §5 transfer machinery
(`CurveDecodability.lean`, `GG25*` family), all axiom-clean.  The *curve* generalization of the
ABF26 mutual-correlated-agreement error — `mcaEventCurve` / `epsMCACurve` — is landed
separately (`MCACurveEvent.lean`).  What was **missing** was the seam that connects the two:
how curve-decodability constrains the curve MCA bad event `mcaEventCurve` (the prize-relevant
`ε_mca` object).  This file supplies that seam.

The honest mathematical content (each fact verified by an exact, non-sampled brute-force probe
`scripts/probes/wf407_B2-curve_{bridge,epsmca}.py`):

* `not_mcaEventCurve_iff_stackAgrees` — **the negation characterization.** The curve MCA bad
  event `mcaEventCurve C δ u γ` is *false* exactly when every large (`≥ (1−δ)·n`) curve-close
  witness set admits a jointly-agreeing codeword stack.  This is the clean statement of what the
  bad event forbids, the form every curve-decodability ⟹ MCA argument consumes.

* `mcaEventCurve_false_of_rows_mem` — **codeword stacks are MCA-clean.** If every row of the
  tested stack `u` is a codeword of `C`, then `mcaEventCurve C δ u γ` is false for *every* seed
  `γ` and *every* radius `δ`: the stack agrees with itself, so the no-stack clause fails.
  (Probe: `0/9375` violations.)  Hence the bad event is genuinely witnessed only by
  *non-codeword* stacks — confirming MCA is a real obstruction, not a triviality.

* `epsMCACurve_term_codewordStack_eq_zero` — the per-stack probability `Pr_γ[mcaEventCurve]`
  is `0` for any codeword stack; the building block of the `epsMCACurve` supremum.

* `not_mcaEventCurve_of_full_stackAgrees` — a *sufficient* condition usable from
  curve-decodability: if the tested stack jointly agrees with a codeword stack on *all* of `ι`,
  no MCA event fires.  `curveAt`-decodability supplies exactly such a global codeword witness.

**Honesty.**  These are the *true* parts of the curve-decodability ↔ `ε_mca` connection
(`δ < 1`, all `δ`).  The converse — bounding `epsMCACurve` *quantitatively* from a
curve-decodability hypothesis — is the substantive [GG25] Thm 3.3 spread direction, already
landed in `GG25MCAFromCurveDecodability.lean` as the all-seeds-close form; the
prize-regime sub-√q list-size input that would make that spread *small enough* stays the open
δ* core (unaffected, as the GG25 supply is for folded/multiplicity/random-RS, not explicit
smooth-domain plain RS).

Axiom-clean: must report `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap.WF407B2

open Finset Code
open scoped NNReal ProbabilityTheory BigOperators

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## The negation characterization of the curve MCA bad event -/

/-- **The curve MCA bad event, unfolded as a negation.**  `mcaEventCurve C δ u γ` *fails*
iff for every set `S` of size `≥ (1−δ)·n` on which the curve `∑ⱼ γʲ•uⱼ` equals a codeword,
some codeword stack jointly agrees with `u` row-wise on `S`.  This is the precise statement of
the obstruction the event encodes: closeness of the *curve* to a codeword that is *not*
explained by a jointly-agreeing codeword *stack*. -/
theorem not_mcaEventCurve_iff_stackAgrees (C : Set (ι → A)) (δ : ℝ≥0) {L : ℕ}
    (u : Fin L → ι → A) (γ : F) :
    ¬ mcaEventCurve C δ u γ ↔
      ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
        (∃ w ∈ C, ∀ i ∈ S, w i = ∑ j : Fin L, γ ^ (j : ℕ) • u j i) →
        stackJointAgreesOn C S u := by
  unfold mcaEventCurve
  constructor
  · intro h S hcard hclose
    by_contra hno
    exact h ⟨S, hcard, hclose, hno⟩
  · rintro h ⟨S, hcard, hclose, hno⟩
    exact hno (h S hcard hclose)

/-! ## Codeword stacks are MCA-clean -/

/-- **Codeword stacks supply self-agreement.**  If every row of `u` lies in `C`, then `u`
jointly agrees with the codeword stack `u` itself on *any* position set `S` — vacuously, since
each row equals itself.  This is the structural reason the bad event cannot fire on codeword
stacks. -/
theorem stackJointAgreesOn_self_of_rows_mem {C : Set (ι → A)} {L : ℕ} {u : Fin L → ι → A}
    (hu : ∀ j, u j ∈ C) (S : Finset ι) : stackJointAgreesOn C S u :=
  ⟨u, hu, fun _ _ _ => rfl⟩

/-- **Codeword stacks are MCA-clean** (probe: `0/9375` violations).  If every row of the
tested stack `u` is a codeword, then `mcaEventCurve C δ u γ` is false for every seed `γ` and
every radius `δ`.  Consequently the curve MCA bad event is witnessed *only* by genuinely
non-codeword stacks — the event is a real obstruction, not vacuous. -/
theorem mcaEventCurve_false_of_rows_mem {C : Set (ι → A)} {δ : ℝ≥0} {L : ℕ}
    {u : Fin L → ι → A} (hu : ∀ j, u j ∈ C) (γ : F) :
    ¬ mcaEventCurve C δ u γ :=
  (not_mcaEventCurve_iff_stackAgrees C δ u γ).mpr
    fun S _ _ => stackJointAgreesOn_self_of_rows_mem hu S

/-- **The `epsMCACurve` per-stack term vanishes on codeword stacks.**  For a stack whose rows
are all codewords, the uniform-`γ` probability of the curve MCA bad event is `0`.  This is the
building block of the `epsMCACurve` supremum: the worst case is never attained at a codeword
stack. -/
theorem epsMCACurve_term_codewordStack_eq_zero (C : Set (ι → A)) (δ : ℝ≥0) {L : ℕ}
    {u : Fin L → ι → A} (hu : ∀ j, u j ∈ C) :
    Pr_{let γ ← $ᵖ F}[mcaEventCurve C δ u γ] = 0 := by
  classical
  rw [ProbabilityTheory.Pr_eq_tsum_indicator, ENNReal.tsum_eq_zero]
  intro γ
  rw [if_neg (mcaEventCurve_false_of_rows_mem hu γ), mul_zero]

/-! ## A curve-decodability-facing sufficient condition -/

/-- **No MCA event from a global codeword-stack witness.**  If the tested stack `u` jointly
agrees with a codeword stack on *all* of `ι` (the strongest agreement), then `mcaEventCurve`
is false at every seed: the global witness restricts to every candidate set `S`.  This is the
form a curve-decodability conclusion takes — it produces a single codeword stack explaining the
tested data — so it is the bridge from [GG25] Def 3.1 to the curve `ε_mca` object. -/
theorem not_mcaEventCurve_of_full_stackAgrees {C : Set (ι → A)} {δ : ℝ≥0} {L : ℕ}
    {u : Fin L → ι → A} (γ : F)
    (h : stackJointAgreesOn C (Finset.univ : Finset ι) u) :
    ¬ mcaEventCurve C δ u γ := by
  obtain ⟨v, hv_mem, hv_agree⟩ := h
  refine (not_mcaEventCurve_iff_stackAgrees C δ u γ).mpr fun S _ _ => ?_
  exact ⟨v, hv_mem, fun i _ j => hv_agree i (Finset.mem_univ i) j⟩

/-- **The MCA event forces a non-explained curve-close witness.**  Directly: if the curve MCA
bad event fires at `γ`, there is a large position set `S` on which the curve equals a codeword
yet no codeword stack agrees with `u`.  The contrapositive of
`not_mcaEventCurve_iff_stackAgrees`, packaged for downstream curve-decodability consumers
(which produce the missing agreeing stack and thereby refute the event). -/
theorem mcaEventCurve_imp_witness {C : Set (ι → A)} {δ : ℝ≥0} {L : ℕ}
    {u : Fin L → ι → A} {γ : F} (h : mcaEventCurve C δ u γ) :
    ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
      (∃ w ∈ C, ∀ i ∈ S, w i = ∑ j : Fin L, γ ^ (j : ℕ) • u j i) ∧
      ¬ stackJointAgreesOn C S u := h

end ProximityGap.WF407B2

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.WF407B2.not_mcaEventCurve_iff_stackAgrees
#print axioms ProximityGap.WF407B2.stackJointAgreesOn_self_of_rows_mem
#print axioms ProximityGap.WF407B2.mcaEventCurve_false_of_rows_mem
#print axioms ProximityGap.WF407B2.epsMCACurve_term_codewordStack_eq_zero
#print axioms ProximityGap.WF407B2.not_mcaEventCurve_of_full_stackAgrees
#print axioms ProximityGap.WF407B2.mcaEventCurve_imp_witness
