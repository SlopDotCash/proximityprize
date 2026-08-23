/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._GaussPeriodRealValued

/-!
# The phase-alignment "tower law" is just reality — a NO-GO for the phase lane (#407)

## The refuted lane (probe-first, then pinned)

The fleet observed (phase-alignment tower probes) that at the worst frequency `b*`, the two
half-coset sums `S0(b*) = ∑_{x∈μ_{n/2}} e_p(b*·x)` and `S1(b*)` are *maximally phase-aligned*
(`cos(S0, S1) = 1.0000`, machine-exact, `n = 8,16,32,64`). This was floated as a candidate
**non-average structural handle** (a tower-recursive self-similarity a descent/Stepanov argument
could exploit, since average/moment methods are blind to worst-frequency alignment).

## Adversarial recheck (refutation)

The interpretation does NOT survive. Probes (`scripts/probes/probe_407_phase_dichotomy.py`,
`probe_407_phase_why.py`, `probe_407_phase_reality.py`, all FFT-exact ~1e-14) show:

1. `|cos(S0(b), S1(b))| = 1.0000` for **EVERY** frequency `b` (256/256, 599/599 sampled), not just
   `b*`. The two half-coset sums are **always real-collinear**.
2. This holds **identically in the THIN (prize) and THICK (anti-prize) regimes** — at `β ≈ 9.8`
   (deep prize) and at `β ≈ 1.07` (very thick) alike. The cosine is `±1` everywhere; the rare `−1`
   cases are sporadic sign flips of two *real* numbers, not a regime signal.
3. **Root cause:** `μ_{n/2}` is a `2`-power cyclic subgroup of **even** order `n/2`, so it contains
   the unique order-`2` element `−1`. Hence `μ_{n/2}` is closed under negation, which forces each
   half-coset sum to be **REAL** (pair `x` with `−x`). Verified `max|Im S0(b)| ~ 1e-15`. Two real
   numbers are trivially collinear, so `cos = ±1` is automatic.

## The constraint (single source of truth = the EVT substrate lemma)

The reality fact is exactly `GaussPeriodRealValued.eta_conj_eq_of_neg_closed` (`conj(η_b) = η_b` for
negation-closed `G`). We do not re-prove it — we **reuse** it here under the phase-alignment reading
(`phase_alignment_is_reality`) and record the no-go:

The "alignment" is forced by reality, holds for **all** `b`, and is identical in the thick window
where the prize is FALSE. So it is **NOT thinness-essential**, and any descent built on the cosine
being `±1` is thickness-monotone — which §3/rule-3 of #407 forbids. The same lemma is a *positive*
EVT substrate (CRACK 7: the period family is real, so the floor is a Gumbel max of real exchangeable
variables); as a *phase-alignment handle* it is empty. **Phase lane pinned.**

Issue #407.
-/

open Finset ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ProximityGap.Frontier.PhaseAlignmentReality

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The phase alignment is reality (no-go restatement).** The observed worst-frequency
"`cos(S0,S1)=±1`" is precisely `conj(η_b)=η_b` for negation-closed `G` (the EVT-substrate lemma
`eta_conj_eq_of_neg_closed`): it holds for **every** `b`, in thin and thick regimes alike, so it is
not a tower-recursive, thinness-essential mechanism. Reused verbatim — no new proof obligation. -/
theorem phase_alignment_is_reality {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hneg : ∀ y ∈ G, -y ∈ G) (b : F) :
    (starRingEnd ℂ) (eta ψ G b) = eta ψ G b :=
  GaussPeriodRealValued.eta_conj_eq_of_neg_closed hψ hneg b

end ProximityGap.Frontier.PhaseAlignmentReality

#print axioms ProximityGap.Frontier.PhaseAlignmentReality.phase_alignment_is_reality
