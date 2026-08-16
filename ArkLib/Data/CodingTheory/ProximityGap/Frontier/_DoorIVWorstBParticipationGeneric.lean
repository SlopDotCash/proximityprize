/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev

set_option linter.style.longLine false

/-!
# Door IV ("outside the moment hierarchy" fork): the WORST-b internal term geometry is the generic
# large deviation of n unit vectors — its coherence is a magnitude (L²) object, no non-moment lever

This file records the axiom-clean kernel behind the probe
`scripts/probes/probe_dooriv_worstb_term_participation.py` (verdict NOTE alongside it).

## Why this matters

The marginal moment hierarchy of the period field `{η_b}` is now closed up to 6th order
(`57b3d915c`: Gaussian to 6th order). Commit `8b2df98a5`'s pointer left two forks: 8th-order+
(diminishing-returns moment grinding) OR "outside the moment hierarchy". This file pursues the
second fork via the INTERNAL geometry of the `n` monomial terms at the WORST frequency `b`:

`η_b = Σ_{j} t_j`, `t_j = e_p(b·g^{mj})` (n unit-modulus terms). `|η_b|` is large iff the `t_j`
ALIGN. A door-(iv) lever would need a NON-MOMENT structural rigidity in this alignment at the worst
`b` (a coherence forced to a structured plateau, or a forward-fraction / participation ratio LOCKED
to a rational of `n`). The probe (PROPER `μ_n`, p≈n⁴≫n³, exact bignum residues, never n=q−1) found:

  * worst-b coherence `R1 = |η_b|/n` tracks the EVT prediction `√(log(p/n)/n)` within a bounded
    NON-monotone constant factor (R1/EVT = 1.20, 1.26, 1.29, 1.13 for n=16..128) — generic EVT,
    no growing structural gap (asymptotic-claim guard untouched).
  * the forward-fraction `A₊` DECAYS (1.00 → 0.766) toward the generic ~½ and is NOT locked to any
    rational of `n`; the aligned participation ratio `PR` DECAYS smoothly (0.874 → 0.669), also
    not locked.

(SAMPLING CAVEAT: at n=64,128 the worst `b` is a SAMPLED max over 60k reps, not the true argmax;
n=16,32 are full scans. This is conservative: a sampled max only UNDERSTATES R1, and the THEOREM
below bounds the TRUE worst-b R1 from above UNCONDITIONALLY (sampling-independent). The true argmax
would be MORE aligned, i.e. even less anti-concentration slack, never more.)

So the worst-b internal geometry is the generic large deviation of `n` unit vectors = door-(iii)
EVT (dead). No non-moment internal lever survives. The Lean kernel below is the UNCONDITIONAL part:
the Cauchy–Schwarz coherence bound holds for ALL `b` (no sampling), pinning the coherence to the L²
magnitude data with no escape to a phase object.

## The formalizable kernel (this file): coherence is a magnitude object (Cauchy–Schwarz)

The formal content of "the internal alignment is a magnitude, not a phase, lever" is that the
coherent (aligned, forward) mass `Σ wⱼ` of `|η_b|` is bounded by the L² data via Cauchy–Schwarz:
`(Σ wⱼ)² ≤ n · Σ wⱼ²`. Equivalently the participation ratio `PR = (Σwⱼ)²/(n·Σwⱼ²) ≤ 1`, so
`|η|/n ≤ √(PR) ≤ 1`. Any candidate bound on the worst-b coherence therefore passes through the L²
magnitude data (`Σ wⱼ²`) — the SAME 2nd-moment object that is the dead Plancherel/EVT wall. There
is no escape to a phase/anti-concentration object the moment hierarchy doesn't already see.
-/

namespace ProximityGap.Frontier.DoorIVWorstBParticipationGeneric

open Finset

/-- Cauchy–Schwarz coherence bound on the aligned forward-mass: for real forward-masses
`w : ι → ℝ` over a finite index set, `(Σ wⱼ)² ≤ |s| · Σ wⱼ²`. The aligned mass `Σ wⱼ` (the coherent
part of `|η_b|`) is controlled by the L² magnitude data — a 2nd-moment (Plancherel/EVT) object, not
a new phase lever. -/
theorem sq_aligned_mass_le_card_mul_sumSq
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) :
    (∑ j ∈ s, w j) ^ 2 ≤ (s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2 := by
  simpa using sq_sum_le_card_mul_sum_sq (s := s) (f := w)

/-- Participation-ratio form: the squared coherence `(Σ wⱼ)²` is at most `card · L²`, hence the
normalized participation ratio `(Σwⱼ)² / (card · Σwⱼ²) ≤ 1` whenever the L² mass is positive.
So the worst-b coherence cannot exceed the magnitude (`√PR ≤ 1`) data — no phase lever beyond L². -/
theorem participation_ratio_le_one
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hpos : 0 < (s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) :
    (∑ j ∈ s, w j) ^ 2 / ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) ≤ 1 := by
  rw [div_le_one hpos]
  simpa using sq_sum_le_card_mul_sum_sq (s := s) (f := w)

/-- Denominator-cleared participation threshold.  A claimed participation-ratio saving
`PR ≤ θ` is exactly the squared aligned-mass budget `(Σwⱼ)² ≤ θ · (card · Σwⱼ²)`.  This packages the
constraint in the form probes use: a participation lever is not a new phase object unless it proves
this L²-normalized squared-mass inequality by some arithmetic input. -/
theorem participation_ratio_le_iff_sq_aligned_le
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) {θ : ℝ}
    (hpos : 0 < (s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) :
    (∑ j ∈ s, w j) ^ 2 / ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) ≤ θ ↔
      (∑ j ∈ s, w j) ^ 2 ≤ θ * ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) := by
  exact div_le_iff₀ hpos

/-- Strict denominator-cleared participation threshold.  Strict participation savings are likewise
nothing more or less than strict L²-normalized squared-aligned-mass savings. -/
theorem participation_ratio_lt_iff_sq_aligned_lt
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) {θ : ℝ}
    (hpos : 0 < (s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) :
    (∑ j ∈ s, w j) ^ 2 / ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) < θ ↔
      (∑ j ∈ s, w j) ^ 2 < θ * ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) := by
  exact div_lt_iff₀ hpos

/-- Contrapositive participation-threshold interface: if the squared aligned mass already exceeds
`θ` times the L² denominator, then the normalized participation ratio cannot be at most `θ`.  This is
the probe-facing way to reject a claimed participation saving without re-opening any phase argument. -/
theorem not_participation_ratio_le_of_sq_aligned_gt
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) {θ : ℝ}
    (hpos : 0 < (s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2)
    (hgt : θ * ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) < (∑ j ∈ s, w j) ^ 2) :
    ¬ (∑ j ∈ s, w j) ^ 2 / ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) ≤ θ := by
  intro hle
  have hsq : (∑ j ∈ s, w j) ^ 2 ≤ θ * ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) :=
    (participation_ratio_le_iff_sq_aligned_le s w hpos).1 hle
  exact not_lt_of_ge hsq hgt

/-- Strict-saving contrapositive: if the squared aligned mass reaches the `θ`-denominator budget, then
the participation ratio cannot be strictly below `θ`.  A strict participation improvement therefore
has exactly the strict squared-mass content named above, and no hidden door-(iv) slack. -/
theorem not_participation_ratio_lt_of_sq_aligned_ge
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) {θ : ℝ}
    (hpos : 0 < (s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2)
    (hge : θ * ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) ≤ (∑ j ∈ s, w j) ^ 2) :
    ¬ (∑ j ∈ s, w j) ^ 2 / ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) < θ := by
  intro hlt
  have hsq : (∑ j ∈ s, w j) ^ 2 < θ * ((s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2) :=
    (participation_ratio_lt_iff_sq_aligned_lt s w hpos).1 hlt
  exact not_lt_of_ge hge hsq

/-- Consequence for the lever search: if a worst-b coherence candidate `C` is controlled by the
aligned mass `Σ wⱼ` and that mass is bounded (Cauchy–Schwarz) by `√(card · L²)`, then `C` is bounded
by the L² magnitude data. Concretely: from `C ≤ (Σ wⱼ)` and `(Σ wⱼ)² ≤ card · L²` we get
`C² ≤ card · L²` (for `0 ≤ C`). The coherence bound passes through the 2nd-moment object. -/
theorem coherence_sq_le_card_mul_sumSq
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : C ≤ ∑ j ∈ s, w j) :
    C ^ 2 ≤ (s.card : ℝ) * ∑ j ∈ s, (w j) ^ 2 := by
  have hmono : C ^ 2 ≤ (∑ j ∈ s, w j) ^ 2 := by
    exact pow_le_pow_left₀ hC0 hC 2
  exact le_trans hmono (sq_aligned_mass_le_card_mul_sumSq s w)

/-- Floor form of the same obstruction: on a nonempty index set, the L² magnitude mass must be at
least the squared aligned mass divided by the number of terms. Thus a large coherent
worst-frequency sum cannot be certified without paying proportional L² mass; the
participation/coherence route has
not escaped the Plancherel object, it has merely rewritten it. -/
theorem aligned_mass_sq_div_card_le_sumSq
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hcard : 0 < (s.card : ℝ)) :
    (∑ j ∈ s, w j) ^ 2 / (s.card : ℝ) ≤ ∑ j ∈ s, (w j) ^ 2 := by
  rw [div_le_iff₀ hcard]
  simpa [mul_comm, mul_left_comm, mul_assoc] using sq_aligned_mass_le_card_mul_sumSq s w

/-- Coherence-certificate floor form: if a nonnegative candidate coherent mass `C` sits below the
aligned mass, then the L² magnitude mass is at least `C² / |s|`.  This is the contrapositive-facing
interface used when a proposed door-(iv) anti-concentration proof tries to prove a large aligned
participation certificate first: the certificate already forces the corresponding L² expenditure. -/
theorem sumSq_ge_coherence_sq_div_card
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hcard : 0 < (s.card : ℝ)) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : C ≤ ∑ j ∈ s, w j) :
    C ^ 2 / (s.card : ℝ) ≤ ∑ j ∈ s, (w j) ^ 2 := by
  rw [div_le_iff₀ hcard]
  simpa [mul_comm, mul_left_comm, mul_assoc] using coherence_sq_le_card_mul_sumSq s w hC0 hC

/-- Contrapositive certificate for failed participation attacks: if the available L² magnitude budget
is strictly below `C² / |s|`, then the aligned mass cannot reach `C`. This packages the exact witness a
probe can emit when a proposed worst-b participation/coherence lever claims a large coherent mass while
also staying under a Plancherel-style L² budget. -/
theorem not_coherence_le_aligned_mass_of_sumSq_lt
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hcard : 0 < (s.card : ℝ)) {C : ℝ}
    (hC0 : 0 ≤ C) (hsmall : ∑ j ∈ s, (w j) ^ 2 < C ^ 2 / (s.card : ℝ)) :
    ¬ C ≤ ∑ j ∈ s, w j := by
  intro hC
  exact not_lt_of_ge (sumSq_ge_coherence_sq_div_card s w hcard hC0 hC) hsmall

/-- Budgeted contrapositive form: an explicit upper budget `B` for the L² mass rules out coherent mass
`C` as soon as `B < C² / |s|`. Any door-(iv) participation proof must therefore either pay this L²
budget or leave the coherent certificate below `C`; no extra arithmetic structure is gained by naming a
participation variable. -/
theorem not_coherence_le_aligned_mass_of_sumSq_le_budget
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hcard : 0 < (s.card : ℝ)) {B C : ℝ}
    (hC0 : 0 ≤ C) (hbudget : ∑ j ∈ s, (w j) ^ 2 ≤ B)
    (hB : B < C ^ 2 / (s.card : ℝ)) :
    ¬ C ≤ ∑ j ∈ s, w j := by
  exact not_coherence_le_aligned_mass_of_sumSq_lt s w hcard hC0 (lt_of_le_of_lt hbudget hB)

end ProximityGap.Frontier.DoorIVWorstBParticipationGeneric

#print axioms
  ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.sq_aligned_mass_le_card_mul_sumSq
#print axioms
  ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.participation_ratio_le_one
#print axioms
  ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.participation_ratio_le_iff_sq_aligned_le
#print axioms
  ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.participation_ratio_lt_iff_sq_aligned_lt
#print axioms
  ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.not_participation_ratio_le_of_sq_aligned_gt
#print axioms
  ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.not_participation_ratio_lt_of_sq_aligned_ge
#print axioms
  ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.coherence_sq_le_card_mul_sumSq
#print axioms
  ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.aligned_mass_sq_div_card_le_sumSq
#print axioms
  ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.sumSq_ge_coherence_sq_div_card
#print axioms
  ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.not_coherence_le_aligned_mass_of_sumSq_lt
#print axioms
  ProximityGap.Frontier.DoorIVWorstBParticipationGeneric.not_coherence_le_aligned_mass_of_sumSq_le_budget
