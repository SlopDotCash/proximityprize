/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic

/-!
# Door-(iv) constraint: coherence-slack is vacuous at the prize-worst frequency (#444)

Lane-1 probes `probe_dooriv_coherent_set_size{,2,3}.py` (proper `μ_n`, `p ≫ n³`, structured primes,
never `n = q-1`) measured the index-2 coset-half coherence `ρ(b)` of `η_b = Σ_{y∈μ_n} e_p(b·y)`
jointly with the normalized mass `|η_b|/√n` over the whole group:

* `corr(ρ, |η|) ≈ +0.63`, **positive and stable** across `n = 16, 32, 64`;
* the near-coherent frequencies carry **more** mass (`mean|η|/√n ≈ 1.14` vs `0.80` typical);
* at the prize-worst frequency `b* = argmax_b |η_b|` (the **global** argmax over the full group
  `F_p*` for `n = 16`; sampled lower-bound proxy for larger `n`), the coherence is `ρ(b*) = 1`
  (confirmed numerically to 60 digits, `1 - ρ(b*) = 0`).  This is the separately **proven** same-ray
  fact (`_DoorIVCosetHalfCoherence`, `_DoorIVMultShiftCollinear`), not a floating-point assertion.

The consequence for door (iv): a "coherence-slack" anti-concentration lever — any bound of the shape
`mass b ≤ g(1 - ρ b)` that is only informative when `ρ b < 1` — **gives no information at the
prize-worst frequency**, because there `ρ = 1` so `1 - ρ = 0` and the slack term vanishes.  The slack
lever can only constrain the *light* frequencies (where `ρ < 1`), which are exactly the ones the prize
does not care about.  This file records that obstruction abstractly and axiom-cleanly.

This is a **refutation with mechanism** (a DEAD lever, precisely mapped), not a CORE/cancellation
claim: it does not bound `M(n)`; it shows one specific lever shape cannot.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax

open Finset

variable {ι : Type*}

/-- A *coherence-slack bound* for a `mass` function with `coh` ∈ \[0,1\]: the mass at each index is
controlled by a nonnegative, monotone-in-slack penalty `g` applied to the slack `1 - coh i`.  By
"informative only off the coherent locus" we mean `g 0 = 0`, i.e. the bound degenerates to `mass ≤ 0`
exactly where coherence is full.  This is the abstract shape of every door-(iv) "exploit the
`1 - ρ(b)` slack" proposal. -/
structure CoherenceSlackBound (mass coh : ι → ℝ) (g : ℝ → ℝ) : Prop where
  /-- The penalty vanishes at zero slack: a full-coherence index gets the trivial bound `mass ≤ 0`. -/
  penalty_zero : g 0 = 0
  /-- The slack bound holds pointwise: each mass is at most the penalty of its slack `1 - coh i`. -/
  bound : ∀ i, mass i ≤ g (1 - coh i)

/-- **The slack bound is vacuous at any full-coherence index.**  If `coh i = 1`, the slack `1 - coh i`
is `0`, so the coherence-slack bound only yields `mass i ≤ 0`. -/
theorem slack_bound_trivial_at_coherent {mass coh : ι → ℝ} {g : ℝ → ℝ}
    (hb : CoherenceSlackBound mass coh g) {i : ι} (hcoh : coh i = 1) :
    mass i ≤ 0 := by
  have := hb.bound i
  rwa [hcoh, sub_self, hb.penalty_zero] at this

/-- **Coherence-slack is vacuous at the prize-worst frequency.**  Suppose `b*` is a frequency whose
mass is maximal (`∀ b, mass b ≤ mass b*`), its mass is positive (it is the genuine peak the prize is
about), and it is fully coherent (`coh b* = 1`, the probed fact `ρ(b*) = 1`).  Then **no**
coherence-slack bound can hold: the bound forces `mass b* ≤ 0`, contradicting `0 < mass b*`.

Mechanistically: a slack lever can only ever constrain the *light* frequencies (those with `coh < 1`),
never the heavy prize-worst frequency, whose coherence is pinned at `1`.  Hence the index-2
coset-half coherence cannot be turned into a door-(iv) anti-concentration bound on `M(n)`. -/
theorem no_coherenceSlackBound_of_coherent_argmax {mass coh : ι → ℝ} {g : ℝ → ℝ}
    {bstar : ι} (_hmax : ∀ i, mass i ≤ mass bstar) (hpos : 0 < mass bstar)
    (hcoh : coh bstar = 1) :
    ¬ CoherenceSlackBound mass coh g := by
  intro hb
  exact absurd (slack_bound_trivial_at_coherent hb hcoh) (not_le.2 hpos)

/-- Finite-support form: over a nonempty finite index set, if the `Finset`-argmax of `mass` is fully
coherent and carries positive mass, the same impossibility holds.  This is the form matching the
probe: `bstar = argmax_{b∈F} |η_b|`, `mass = |η|`, `coh = ρ`, with `ρ(bstar) = 1`. -/
theorem no_coherenceSlackBound_of_coherent_finsetArgmax {mass coh : ι → ℝ} {g : ℝ → ℝ}
    {s : Finset ι} {bstar : ι} (_hbs : bstar ∈ s)
    (_hmax : ∀ i ∈ s, mass i ≤ mass bstar) (hpos : 0 < mass bstar)
    (hcoh : coh bstar = 1) :
    ¬ (CoherenceSlackBound mass coh g) := by
  intro hb
  exact absurd (slack_bound_trivial_at_coherent hb hcoh) (not_le.2 hpos)

/-- A relaxed coherence-slack bound with an arbitrary zero-slack baseline.  This covers proposals of
the form `mass i ≤ g (1 - coh i)` even when `g 0` is not forced to vanish.  The theorem below says
that such a lever can only be valid at a fully coherent prize peak if its zero-slack baseline already
pays for the peak itself. -/
structure CoherenceSlackBoundWithBaseline (mass coh : ι → ℝ) (g : ℝ → ℝ) : Prop where
  /-- The slack bound holds pointwise: each mass is at most the penalty of its slack `1 - coh i`. -/
  bound : ∀ i, mass i ≤ g (1 - coh i)

/-- Any relaxed coherence-slack bound evaluated at a full-coherence index reduces to the zero-slack
baseline `g 0`.  Thus `g 0` is not a harmless additive constant: it is exactly the amount of mass the
lever must already concede at a coherent frequency. -/
theorem slack_bound_withBaseline_at_coherent {mass coh : ι → ℝ} {g : ℝ → ℝ}
    (hb : CoherenceSlackBoundWithBaseline mass coh g) {i : ι} (hcoh : coh i = 1) :
    mass i ≤ g 0 := by
  have := hb.bound i
  rwa [hcoh, sub_self] at this

/-- **Baseline lower bound at a coherent argmax.**  If the prize-worst frequency is fully coherent,
then every relaxed coherence-slack certificate must have zero-slack baseline at least the peak mass.
Consequently, any such certificate whose `g 0` is below the target peak is impossible; if it is valid,
the entire hard bound has already been hidden in the baseline rather than extracted from slack. -/
theorem baseline_ge_mass_of_coherent_argmax {mass coh : ι → ℝ} {g : ℝ → ℝ}
    {bstar : ι} (_hmax : ∀ i, mass i ≤ mass bstar) (hcoh : coh bstar = 1)
    (hb : CoherenceSlackBoundWithBaseline mass coh g) :
    mass bstar ≤ g 0 :=
  slack_bound_withBaseline_at_coherent hb hcoh

/-- Impossibility form of `baseline_ge_mass_of_coherent_argmax`: a relaxed coherence-slack bound
with zero-slack baseline strictly below the fully coherent prize peak cannot hold.  This is the
nonzero-baseline version of the vacuity obstruction. -/
theorem no_coherenceSlackBoundWithBaseline_of_small_baseline {mass coh : ι → ℝ} {g : ℝ → ℝ}
    {bstar : ι} (hmax : ∀ i, mass i ≤ mass bstar) (hcoh : coh bstar = 1)
    (hsmall : g 0 < mass bstar) :
    ¬ CoherenceSlackBoundWithBaseline mass coh g := by
  intro hb
  exact not_le.2 hsmall (baseline_ge_mass_of_coherent_argmax hmax hcoh hb)

/-- Finite-support baseline form matching probe output: if the observed finite argmax is fully
coherent and its zero-slack baseline is below the peak mass, the relaxed slack certificate cannot
hold.  The finite argmax hypotheses record provenance of `bstar`; the contradiction is local at the
coherent peak. -/
theorem no_coherenceSlackBoundWithBaseline_of_small_baseline_finsetArgmax
    {mass coh : ι → ℝ} {g : ℝ → ℝ} {s : Finset ι} {bstar : ι}
    (_hbs : bstar ∈ s) (_hmax : ∀ i ∈ s, mass i ≤ mass bstar)
    (hcoh : coh bstar = 1) (hsmall : g 0 < mass bstar) :
    ¬ CoherenceSlackBoundWithBaseline mass coh g := by
  intro hb
  exact not_le.2 hsmall (slack_bound_withBaseline_at_coherent hb hcoh)

/-- An *affine* coherence-slack certificate: the claimed control is a baseline `B` plus a penalty
from the slack `1 - coh i`.  This is the natural patched version of a failed vanishing-slack lever:
allow an additive budget, but keep the anti-concentration content in the slack term. -/
structure AffineCoherenceSlackBound (mass coh : ι → ℝ) (B : ℝ) (g : ℝ → ℝ) : Prop where
  /-- The slack penalty still vanishes at full coherence. -/
  penalty_zero : g 0 = 0
  /-- Pointwise affine slack control. -/
  bound : ∀ i, mass i ≤ B + g (1 - coh i)

/-- At a fully coherent frequency, an affine coherence-slack certificate collapses to its baseline
`B`.  Thus the baseline itself must pay for any full-coherence peak; the slack term contributes
nothing at that frequency. -/
theorem affineSlack_bound_at_coherent {mass coh : ι → ℝ} {B : ℝ} {g : ℝ → ℝ}
    (hb : AffineCoherenceSlackBound mass coh B g) {i : ι} (hcoh : coh i = 1) :
    mass i ≤ B := by
  have := hb.bound i
  rwa [hcoh, sub_self, hb.penalty_zero, add_zero] at this

/-- **Affine baseline necessity at a coherent argmax.**  If the prize-worst frequency is fully
coherent, every affine coherence-slack certificate must put the entire peak mass into the baseline.
So any useful anti-concentration would have to prove `B` is already a prize-quality bound; the
coherence slack does not help at the adversarial frequency. -/
theorem affineBaseline_ge_mass_of_coherent_argmax {mass coh : ι → ℝ} {B : ℝ} {g : ℝ → ℝ}
    {bstar : ι} (_hmax : ∀ i, mass i ≤ mass bstar) (hcoh : coh bstar = 1)
    (hb : AffineCoherenceSlackBound mass coh B g) :
    mass bstar ≤ B :=
  affineSlack_bound_at_coherent hb hcoh

/-- Impossibility form: an affine coherence-slack certificate with baseline strictly below the
fully coherent prize peak cannot hold.  This permanently blocks the common patch "add a small
baseline and use `1 - ρ` for the rest" unless the baseline already covers the hard `L∞` peak. -/
theorem no_affineCoherenceSlackBound_of_small_baseline {mass coh : ι → ℝ} {B : ℝ} {g : ℝ → ℝ}
    {bstar : ι} (hmax : ∀ i, mass i ≤ mass bstar) (hcoh : coh bstar = 1)
    (hsmall : B < mass bstar) :
    ¬ AffineCoherenceSlackBound mass coh B g := by
  intro hb
  exact not_le.2 hsmall (affineBaseline_ge_mass_of_coherent_argmax hmax hcoh hb)

/-- Finite-support affine form matching probe output: a below-peak additive baseline cannot be rescued
by a slack penalty when the finite argmax itself has full coherence. -/
theorem no_affineCoherenceSlackBound_of_small_baseline_finsetArgmax
    {mass coh : ι → ℝ} {B : ℝ} {g : ℝ → ℝ} {s : Finset ι} {bstar : ι}
    (_hbs : bstar ∈ s) (_hmax : ∀ i ∈ s, mass i ≤ mass bstar)
    (hcoh : coh bstar = 1) (hsmall : B < mass bstar) :
    ¬ AffineCoherenceSlackBound mass coh B g := by
  intro hb
  exact not_le.2 hsmall (affineSlack_bound_at_coherent hb hcoh)

/-- A *multiplicative* coherence-slack certificate: the claimed control is a baseline `B` times a
slack factor `g (1 - coh i)`.  This covers ratio-style patches of the failed slack lever, where the
coherence deficit is supposed to damp a baseline budget rather than add to it. -/
structure MultiplicativeCoherenceSlackBound (mass coh : ι → ℝ) (B : ℝ) (g : ℝ → ℝ) : Prop where
  /-- The full-coherence factor is normalized to one, so a fully coherent frequency receives exactly
  the baseline bound `B`. -/
  factor_zero : g 0 = 1
  /-- Pointwise multiplicative slack control. -/
  bound : ∀ i, mass i ≤ B * g (1 - coh i)

/-- At a fully coherent frequency, a multiplicative coherence-slack certificate collapses to its
baseline `B`.  The multiplicative slack factor contributes no damping at `ρ = 1`. -/
theorem multiplicativeSlack_bound_at_coherent {mass coh : ι → ℝ} {B : ℝ} {g : ℝ → ℝ}
    (hb : MultiplicativeCoherenceSlackBound mass coh B g) {i : ι} (hcoh : coh i = 1) :
    mass i ≤ B := by
  have := hb.bound i
  rwa [hcoh, sub_self, hb.factor_zero, mul_one] at this

/-- **Multiplicative baseline necessity at a coherent argmax.**  If the prize-worst frequency is
fully coherent, every multiplicative coherence-slack certificate must put the entire peak mass into
its baseline.  A ratio-style `1 - ρ` factor cannot reduce the adversarial frequency. -/
theorem multiplicativeBaseline_ge_mass_of_coherent_argmax {mass coh : ι → ℝ} {B : ℝ} {g : ℝ → ℝ}
    {bstar : ι} (_hmax : ∀ i, mass i ≤ mass bstar) (hcoh : coh bstar = 1)
    (hb : MultiplicativeCoherenceSlackBound mass coh B g) :
    mass bstar ≤ B :=
  multiplicativeSlack_bound_at_coherent hb hcoh

/-- Impossibility form: a multiplicative coherence-slack certificate with baseline strictly below the
fully coherent prize peak cannot hold.  Thus replacing an additive slack term by a ratio-style slack
factor does not evade the coherent-argmax obstruction; the baseline must already pay the hard `L∞`
peak. -/
theorem no_multiplicativeCoherenceSlackBound_of_small_baseline {mass coh : ι → ℝ}
    {B : ℝ} {g : ℝ → ℝ} {bstar : ι} (hmax : ∀ i, mass i ≤ mass bstar)
    (hcoh : coh bstar = 1) (hsmall : B < mass bstar) :
    ¬ MultiplicativeCoherenceSlackBound mass coh B g := by
  intro hb
  exact not_le.2 hsmall (multiplicativeBaseline_ge_mass_of_coherent_argmax hmax hcoh hb)

/-- Finite-support multiplicative form matching probe output: a below-peak baseline times a normalized
slack factor cannot hold when the finite argmax itself has full coherence. -/
theorem no_multiplicativeCoherenceSlackBound_of_small_baseline_finsetArgmax
    {mass coh : ι → ℝ} {B : ℝ} {g : ℝ → ℝ} {s : Finset ι} {bstar : ι}
    (_hbs : bstar ∈ s) (_hmax : ∀ i ∈ s, mass i ≤ mass bstar)
    (hcoh : coh bstar = 1) (hsmall : B < mass bstar) :
    ¬ MultiplicativeCoherenceSlackBound mass coh B g := by
  intro hb
  exact not_le.2 hsmall (multiplicativeSlack_bound_at_coherent hb hcoh)

end ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax

#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax.slack_bound_trivial_at_coherent
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax.no_coherenceSlackBound_of_coherent_argmax
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax.no_coherenceSlackBound_of_coherent_finsetArgmax
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax.slack_bound_withBaseline_at_coherent
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax.baseline_ge_mass_of_coherent_argmax
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax.no_coherenceSlackBoundWithBaseline_of_small_baseline
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax.no_coherenceSlackBoundWithBaseline_of_small_baseline_finsetArgmax
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax.affineSlack_bound_at_coherent
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax.affineBaseline_ge_mass_of_coherent_argmax
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax.no_affineCoherenceSlackBound_of_small_baseline
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax.no_affineCoherenceSlackBound_of_small_baseline_finsetArgmax
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax.multiplicativeSlack_bound_at_coherent
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax.multiplicativeBaseline_ge_mass_of_coherent_argmax
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax.no_multiplicativeCoherenceSlackBound_of_small_baseline
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax.no_multiplicativeCoherenceSlackBound_of_small_baseline_finsetArgmax
