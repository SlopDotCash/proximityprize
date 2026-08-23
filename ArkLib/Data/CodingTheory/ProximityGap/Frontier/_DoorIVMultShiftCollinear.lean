/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVRealSignMassSlack
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Door IV multiplicative-coset refinement collinearity: real pieces have only a sign DOF

This file records the axiom-clean arithmetic brick behind the probes
`scripts/probes/probe_dooriv_multshift_coherence.py` and `..._coherence2.py`.

## Probe context (door-(iv) Lane 1)

The index-2 / negation-stable refinements of the period sum `S(b) = ∑_{x∈μ_n} e_p(b·x)` are already
proven sign-degenerate (`_DoorIVCosetHalfCoherence`, `_DoorIVMultiPieceSignCoherence`).  The in-tree
note there says the only conceivable escape is a refinement whose pieces are **not**
negation-stable,
so the piece sums are genuinely *complex* and might carry a 2-dimensional angular fan an
anti-concentration bound could grip.

The probe tests the natural such refinement: the **multiplicative-coset** split
`μ_n = ⊔_{j<d} g^j⟨g^d⟩`, whose `d` pieces `P_j(b)` are genuinely complex.  The decisive empirical
finding (n = 16..128, multiple structured primes `p ≫ n³`, proper `μ_n`, exact arithmetic):

* at the worst (`argmax |S(b)|`) `b` — the only `b` that matters for `CORE` — the coarse-to-moderate
  splits `d = 2, 4, 8` give coherence exactly `1` (`rho@smax = 1.0000`) across every prime tested;
* the only slack at finer `d` (`d = 16`) comes, **in the deep thin regime `n ≥ 32`**, with angular
  spread **exactly `π`** — two antipodal real clusters, i.e. a pure *sign* split, not a 2-D fan.

**Honest scope (do NOT over-read):** the `{0, π}` spread dichotomy is an *empirical regime*
statement
for `n ≥ 32` and coarse-to-moderate `d`.  It is **not universal**: at small `n` with fine `d`
(e.g. `n = 16, d = 16`) the probes DO record genuine interior 2-D fans (angular spread `≈ 0.7π`,
histogram buckets `0.75π / 1.25π`) — there the pieces are single-element sums (`|⟨g^d⟩| = 1`) whose
phases are raw `e_p` values, an `n`-too-small artifact rather than thin-regime structure.  So in the
*deep thin regime the multiplicative-coset pieces collapse to the real line up to a sign*, but for
genuinely complex piece configurations the sign-mass lemma below does **not** apply — it is a
*conditional* constraint (hypothesis: pieces are real), not a universal collapse.

## The brick

When the pieces `A i` are **real** (collinear on the `±` axis), the normalized multi-piece coherence

`ρ = |∑ᵢ Aᵢ| / ∑ᵢ |Aᵢ|`

is governed entirely by the **sign-mass imbalance**: writing `P` for the positive mass `∑_{Aᵢ≥0} Aᵢ`
and `N` for the negative mass `∑_{Aᵢ<0} (−Aᵢ)`, `ρ = |P − N| / (P + N)`.  This is a *one-parameter
scalar*: the
only door-(iv) saving available from a real-piece refinement is a sign-cancellation event, never the
angular spread of a 2-D fan.  Concretely (`multiPieceCoherence_lt_one_of_signsplit`): if both a
strictly positive and a strictly negative piece are present, `ρ < 1` **iff** there is genuine sign
cancellation, but the deficit `1 − ρ = 2·min(P,N)/(P+N)` is pinned to the sign-mass imbalance — the
same index-2 mechanism, not new structure.  This is a constraint lemma, not `CORE`, and uses no
moment or completion.
-/

open scoped BigOperators

namespace ProximityGap.Frontier.DoorIVMultShiftCollinear

open ProximityGap.Frontier.DoorIVRealSignMassSlack

/-- Normalized coherence of finitely many real pieces (same statistic as
`DoorIVMultiPieceSignCoherence.multiPieceCoherence`). -/
noncomputable def coherence {ι : Type*} (s : Finset ι) (A : ι → ℝ) : ℝ :=
  |∑ i ∈ s, A i| / (∑ i ∈ s, |A i|)

/-- Positive sign-mass of a real piece family. -/
noncomputable def posMass {ι : Type*} (s : Finset ι) (A : ι → ℝ) : ℝ :=
  ∑ i ∈ s, max (A i) 0

/-- Negative sign-mass (as a nonnegative quantity) of a real piece family. -/
noncomputable def negMass {ι : Type*} (s : Finset ι) (A : ι → ℝ) : ℝ :=
  ∑ i ∈ s, max (-(A i)) 0

theorem posMass_nonneg {ι : Type*} (s : Finset ι) (A : ι → ℝ) : 0 ≤ posMass s A :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

theorem negMass_nonneg {ι : Type*} (s : Finset ι) (A : ι → ℝ) : 0 ≤ negMass s A :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

/-- The signed total decomposes as positive minus negative mass. -/
theorem sum_eq_posMass_sub_negMass {ι : Type*} (s : Finset ι) (A : ι → ℝ) :
    ∑ i ∈ s, A i = posMass s A - negMass s A := by
  unfold posMass negMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases le_or_gt 0 (A i) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith : -(A i) ≤ 0)]; ring
  · rw [max_eq_right (le_of_lt h), max_eq_left (by linarith : 0 ≤ -(A i))]; ring

/-- The absolute mass decomposes as positive plus negative mass. -/
theorem sum_abs_eq_posMass_add_negMass {ι : Type*} (s : Finset ι) (A : ι → ℝ) :
    ∑ i ∈ s, |A i| = posMass s A + negMass s A := by
  unfold posMass negMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases le_or_gt 0 (A i) with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith : -(A i) ≤ 0)]; ring
  · rw [abs_of_neg h, max_eq_right (le_of_lt h), max_eq_left (by linarith : 0 ≤ -(A i))]; ring

/-- **Collinearity collapse.**  For real pieces the multi-piece coherence is exactly the
sign-mass imbalance `|P − N| / (P + N)`: the only degree of freedom is the sign split. -/
theorem coherence_eq_signMass_imbalance {ι : Type*} (s : Finset ι) (A : ι → ℝ) :
    coherence s A = |posMass s A - negMass s A| / (posMass s A + negMass s A) := by
  unfold coherence
  rw [sum_eq_posMass_sub_negMass, sum_abs_eq_posMass_add_negMass]

/-- Compatibility with the reusable two-mass sign-coherence statistic. -/
theorem coherence_eq_signMassCoherence {ι : Type*} (s : Finset ι) (A : ι → ℝ) :
    coherence s A = signMassCoherence (posMass s A) (negMass s A) := by
  rw [coherence_eq_signMass_imbalance]
  rfl

/-- Threshold consumer: for real-collinear pieces, proving a target `ρ ≤ θ` is exactly proving the
minority-sign-mass lower bound.  This packages the multiplicative-refinement wall in the form future
Door-IV anti-concentration claims must discharge. -/
theorem coherence_le_iff_minority_mass_ge {ι : Type*} (s : Finset ι) (A : ι → ℝ) {theta : ℝ}
    (hden : 0 < posMass s A + negMass s A) :
    coherence s A ≤ theta ↔
      (1 - theta) * (posMass s A + negMass s A) / 2 ≤ min (posMass s A) (negMass s A) := by
  rw [coherence_eq_signMassCoherence]
  exact signMassCoherence_le_iff_minority_mass_ge hden

/-- Operational `1 - ε` form of the real-collinear threshold.  A claimed Door-IV coherence saving
`ρ ≤ 1 - ε` for a real multiplicative-shift refinement is exactly the obligation to prove an
`ε/2` minority-sign-mass fraction.  This is the finite obstruction probes use: if the adversarial
frequency is nearly one-signed, a collinear split cannot yield the requested saving. -/
theorem coherence_le_one_sub_iff_minority_mass_ge {ι : Type*} (s : Finset ι) (A : ι → ℝ) {eps : ℝ}
    (hden : 0 < posMass s A + negMass s A) :
    coherence s A ≤ 1 - eps ↔
      eps * (posMass s A + negMass s A) / 2 ≤ min (posMass s A) (negMass s A) := by
  simpa using (coherence_le_iff_minority_mass_ge (s := s) (A := A) (theta := 1 - eps) hden)

/-- Contrapositive budget form.  If the minority sign mass is below the `ε/2` fraction demanded by
the target, then the real-collinear multiplicative-shift refinement cannot certify `ρ ≤ 1 - ε`.
Thus any successful Door-IV proof in this regime must first produce the missing minority-mass lower
bound; the coherence drop is not free bookkeeping. -/
theorem not_coherence_le_one_sub_of_minority_mass_lt {ι : Type*} (s : Finset ι) (A : ι → ℝ)
    {eps : ℝ} (hden : 0 < posMass s A + negMass s A)
    (hminor : min (posMass s A) (negMass s A) < eps * (posMass s A + negMass s A) / 2) :
    ¬ coherence s A ≤ 1 - eps := by
  rw [coherence_eq_signMassCoherence]
  exact DoorIVRealSignMassSlack.not_coherence_le_one_sub_of_minority_mass_lt hden hminor

/-- Strict real-collinear multshift coherence improvement below `1` forces both sign masses to be
positive.  A one-sign real refinement cannot yield any nontrivial Door-IV coherence drop. -/
theorem positive_sign_masses_of_coherence_lt_one_threshold {ι : Type*} (s : Finset ι) (A : ι → ℝ)
    {theta : ℝ} (hden : 0 < posMass s A + negMass s A) (htheta : theta < 1)
    (hcoh : coherence s A ≤ theta) :
    0 < posMass s A ∧ 0 < negMass s A := by
  rw [coherence_eq_signMassCoherence] at hcoh
  exact DoorIVRealSignMassSlack.positive_sign_masses_of_coherence_lt_one_threshold hden htheta hcoh

/-- If all pieces are same-signed (one of the masses vanishes) and the total mass is positive, the
coherence is exactly `1` — recovering the saturation obstruction at the sign-mass level. -/
theorem coherence_eq_one_of_oneMass_zero {ι : Type*} (s : Finset ι) (A : ι → ℝ)
    (h : negMass s A = 0) (hpos : 0 < posMass s A) :
    coherence s A = 1 := by
  rw [coherence_eq_signMass_imbalance, h, sub_zero, add_zero, abs_of_nonneg (le_of_lt hpos)]
  exact div_self (ne_of_gt hpos)

/-- **The sign-split deficit is pinned to the sign-mass imbalance.**  When both masses are strictly
positive (genuine sign cancellation present) the coherence is *strictly* below `1`, and the deficit
`1 − ρ = 2·min(P,N)/(P+N)` is determined entirely by the sign-mass split — there is no angular
degree of freedom.  This is the formal statement that a real-piece (multiplicative-coset)
refinement's only door-(iv) saving is a sign event, not the 2-D fan an anti-concentration bound
would need. -/
theorem coherence_lt_one_of_signsplit {ι : Type*} (s : Finset ι) (A : ι → ℝ)
    (hP : 0 < posMass s A) (hN : 0 < negMass s A) :
    coherence s A < 1 := by
  rw [coherence_eq_signMass_imbalance]
  set P := posMass s A
  set N := negMass s A
  have hden : 0 < P + N := by linarith
  rw [div_lt_one hden, abs_lt]
  constructor <;> linarith

/-- Exact strict-slack criterion for real-collinear multiplicative-shift refinements.  Once the
total real mass is nonzero, coherence drops below `1` if and only if both sign masses are present.
Thus any strict saving in this collinear regime is precisely a sign-cancellation event, not a new
angular anti-concentration mechanism. -/
theorem coherence_lt_one_iff_both_sign_masses_pos {ι : Type*} (s : Finset ι) (A : ι → ℝ)
    (hden : 0 < posMass s A + negMass s A) :
    coherence s A < 1 ↔ 0 < posMass s A ∧ 0 < negMass s A := by
  constructor
  · intro hcoh
    exact positive_sign_masses_of_coherence_lt_one_threshold s A hden hcoh le_rfl
  · intro h
    exact coherence_lt_one_of_signsplit s A h.1 h.2

/-- The exact deficit identity: with both masses strictly positive, `1 − ρ` equals the
doubled smaller sign-mass over the total — a one-parameter scalar, no angular content. -/
theorem one_sub_coherence_eq {ι : Type*} (s : Finset ι) (A : ι → ℝ)
    (hP : 0 < posMass s A) (hN : 0 < negMass s A) :
    1 - coherence s A = 2 * min (posMass s A) (negMass s A) / (posMass s A + negMass s A) := by
  rw [coherence_eq_signMass_imbalance]
  set P := posMass s A
  set N := negMass s A
  have hden : 0 < P + N := by linarith
  rcases le_total P N with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith : P - N ≤ 0)]
    field_simp
    ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith : 0 ≤ P - N)]
    field_simp
    ring

end ProximityGap.Frontier.DoorIVMultShiftCollinear

open ProximityGap.Frontier.DoorIVMultShiftCollinear

#print axioms coherence_eq_signMass_imbalance
#print axioms coherence_eq_signMassCoherence
#print axioms coherence_le_iff_minority_mass_ge
#print axioms coherence_le_one_sub_iff_minority_mass_ge
#print axioms not_coherence_le_one_sub_of_minority_mass_lt
#print axioms positive_sign_masses_of_coherence_lt_one_threshold
#print axioms coherence_eq_one_of_oneMass_zero
#print axioms coherence_lt_one_of_signsplit
#print axioms coherence_lt_one_iff_both_sign_masses_pos
#print axioms one_sub_coherence_eq
