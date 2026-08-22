/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic

/-!
# Door-(iv) constraint: dyadic worst-`b` selectors need a real spike, not Haar noise

This file packages the formal, axiom-clean kernel behind
`scripts/probes/probe_dooriv_worstb_2adic_valuation.py` and the DISPROOF_LOG entry
`doorIV-worstb-2adic-unstructured`.

For a prize-regime subgroup of size `n = 2^a`, the natural remaining hope after quotienting the
`μ_n`-coset symmetry is that the adversarial frequency `b*` always lives on a fixed dyadic subtower
rung.  The probe measured the valuation `v₂(k*)`, where `k* = dlog_g(b*) mod n`, over many primes and
found the Haar-null law `Pr[v₂=j] ≈ 2^-(j+1)` with no fixed-level spike.

The theorems below deliberately prove only the reusable finite-combinatorial obstruction:

* a fixed-rung rule is impossible as soon as two observed worst frequencies have different dyadic
  valuations;
* a “mostly fixed rung” rule is impossible unless some rung has both a large mass certificate and a
  ratio above its Haar-null expectation.

Thus the dyadic-selector route must exhibit an actual histogram spike.  The latest exact probe found
none.  This is a constraint lemma for door (iv), not a cancellation bound, not CORE, and not a capacity
claim.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVWorstBDyadicSelectorWalled

/-- A sample `x` has a dyadic rung `j : Fin a`, e.g. `j = v₂(dlog_g b*)`. -/
def FixedRungRule {α : Type*} {a : Nat} (S : Finset α) (rung : α → Fin a) (j : Fin a) : Prop :=
  ∀ x, x ∈ S → rung x = j

/-- A fixed dyadic-rung selector cannot explain two observed worst-`b` samples on different rungs. -/
theorem no_fixedRungRule_of_two_rungs {α : Type*} {a : Nat} (S : Finset α) (rung : α → Fin a)
    {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hxy : rung x ≠ rung y) :
    ¬ ∃ j : Fin a, FixedRungRule S rung j := by
  rintro ⟨j, hj⟩
  exact hxy ((hj x hx).trans (hj y hy).symm)

/-- Scaled Haar-spike test for a dyadic valuation histogram.

`hist j` is the number of observed worst frequencies with `v₂(k*) = j`, `total` is the number of
samples, and the Haar null at level `j` is `total / 2^(j+1)`.  The predicate says the observed mass is
strictly larger than `(spikeNum / spikeDen)` times the Haar-null mass, written without division:
`spikeNum * total < spikeDen * 2^(j+1) * hist j`.
-/
def ExceedsHaarBy {a : Nat} (hist : Fin a → Nat) (total spikeNum spikeDen : Nat) (j : Fin a) : Prop :=
  spikeNum * total < spikeDen * (2 ^ (j.val + 1) * hist j)

/-- A level has a raw mass certificate `massNum / massDen`, again written without division. -/
def HasMassAtLeast {a : Nat} (hist : Fin a → Nat) (total massNum massDen : Nat) (j : Fin a) : Prop :=
  massNum * total ≤ massDen * hist j

/-- The probe-facing notion of a fixed-rung spike: high relative to the Haar null and carrying enough
absolute sample mass.  The script used the concrete intuition “`> 2.5×` null and at least `40%` mass”. -/
def FixedRungSpike {a : Nat} (hist : Fin a → Nat)
    (total spikeNum spikeDen massNum massDen : Nat) (j : Fin a) : Prop :=
  ExceedsHaarBy hist total spikeNum spikeDen j ∧
    HasMassAtLeast hist total massNum massDen j

/-- If every dyadic rung stays within the chosen scaled Haar-null envelope, then no rung has a
fixed-level spike.  This is the formal kernel behind the probe verdict “no fixed-level spike”. -/
theorem no_fixedRungSpike_of_no_haar_excess {a : Nat} (hist : Fin a → Nat)
    (total spikeNum spikeDen massNum massDen : Nat)
    (h : ∀ j : Fin a, ¬ ExceedsHaarBy hist total spikeNum spikeDen j) :
    ¬ ∃ j : Fin a, FixedRungSpike hist total spikeNum spikeDen massNum massDen j := by
  rintro ⟨j, hj⟩
  exact h j hj.1

/-- Symmetric interface: if every dyadic rung lacks the required absolute mass, then again no fixed
rung can be certified.  This separates “ratio spike” from “enough samples to matter”. -/
theorem no_fixedRungSpike_of_no_mass {a : Nat} (hist : Fin a → Nat)
    (total spikeNum spikeDen massNum massDen : Nat)
    (h : ∀ j : Fin a, ¬ HasMassAtLeast hist total massNum massDen j) :
    ¬ ∃ j : Fin a, FixedRungSpike hist total spikeNum spikeDen massNum massDen j := by
  rintro ⟨j, hj⟩
  exact h j hj.2

/-- Contrapositive packaging: any successful mostly-fixed dyadic-selector certificate must exhibit an
actual histogram spike at some level.  The exact probe found no such level, so the dyadic-selection
hope is walled empirically; this theorem states the finite combinatorial obligation. -/
theorem fixedRung_certificate_requires_spike {a : Nat} (hist : Fin a → Nat)
    (total spikeNum spikeDen massNum massDen : Nat) :
    (∃ j : Fin a, FixedRungSpike hist total spikeNum spikeDen massNum massDen j) →
      ∃ j : Fin a,
        ExceedsHaarBy hist total spikeNum spikeDen j ∧
          HasMassAtLeast hist total massNum massDen j := by
  rintro ⟨j, hj⟩
  exact ⟨j, hj⟩

/-- A truly fixed dyadic rung (`hist j = total`) is automatically a scaled Haar excess whenever the
chosen spike threshold is below the reciprocal Haar mass `2^(j+1)`.  Thus a genuine fixed-subtower
selection rule would be loudly visible in the histogram; it cannot hide inside Haar-null noise. -/
theorem full_mass_exceeds_haar {a : Nat} (hist : Fin a → Nat)
    {total spikeNum spikeDen : Nat} {j : Fin a} (hfull : hist j = total) (hpos : 0 < total)
    (hthreshold : spikeNum < spikeDen * 2 ^ (j.val + 1)) :
    ExceedsHaarBy hist total spikeNum spikeDen j := by
  unfold ExceedsHaarBy
  have hmul := Nat.mul_lt_mul_of_pos_right hthreshold hpos
  simpa [hfull, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul

/-- Full mass at a rung also satisfies any absolute-mass certificate whose requested fraction is at
most one (`massNum ≤ massDen`). -/
theorem full_mass_has_massAtLeast {a : Nat} (hist : Fin a → Nat)
    {total massNum massDen : Nat} {j : Fin a} (hfull : hist j = total) (hmass : massNum ≤ massDen) :
    HasMassAtLeast hist total massNum massDen j := by
  unfold HasMassAtLeast
  exact hfull ▸ Nat.mul_le_mul_right total hmass

/-- Combined witness: a true fixed-rung histogram necessarily produces the exact spike certificate used
by the probe, provided the ratio threshold is below the Haar reciprocal and the mass threshold is at
most full mass.  The absence of such a spike is therefore a direct finite obstruction to fixed-rung
selection. -/
theorem fixedRung_full_mass_forces_spike {a : Nat} (hist : Fin a → Nat)
    {total spikeNum spikeDen massNum massDen : Nat} {j : Fin a}
    (hfull : hist j = total) (hpos : 0 < total)
    (hthreshold : spikeNum < spikeDen * 2 ^ (j.val + 1)) (hmass : massNum ≤ massDen) :
    FixedRungSpike hist total spikeNum spikeDen massNum massDen j :=
  ⟨full_mass_exceeds_haar hist hfull hpos hthreshold,
   full_mass_has_massAtLeast hist hfull hmass⟩

/-- **No hidden fixed rung behind a no-spike certificate.**  If the histogram has no rung satisfying
the probe's combined spike predicate, then no rung can secretly carry all samples, provided the probe
thresholds are in the honest regime: positive total sample count, the Haar-excess threshold is below
the reciprocal Haar mass at every rung, and the absolute-mass threshold is at most full mass.

This is the finite contrapositive used by the door-(iv) dyadic-selector wall: a true fixed-subtower
worst-`b` law would force a visible histogram spike, so a verified no-spike sweep rules out not only
"mostly fixed" selectors but also exact fixed-rung selectors. -/
theorem no_full_mass_rung_of_no_fixedRungSpike {a : Nat} (hist : Fin a → Nat)
    {total spikeNum spikeDen massNum massDen : Nat}
    (hno : ¬ ∃ j : Fin a, FixedRungSpike hist total spikeNum spikeDen massNum massDen j)
    (hpos : 0 < total)
    (hthreshold : ∀ j : Fin a, spikeNum < spikeDen * 2 ^ (j.val + 1))
    (hmass : massNum ≤ massDen) :
    ∀ j : Fin a, hist j ≠ total := by
  intro j hfull
  exact hno ⟨j, fixedRung_full_mass_forces_spike hist hfull hpos (hthreshold j) hmass⟩

/-- Histogram-count form of the no-hidden-rung wall.  If `total` is an actual sample-count ceiling
for every bin, then the same no-spike certificate proves every dyadic rung has **strictly less** than
full mass.  This is the version consumed by finite probe reports, where `hist j ≤ total` is immediate
from `hist` counting samples: no rung is an exact selector unless a visible spike exists. -/
theorem hist_lt_total_of_no_fixedRungSpike {a : Nat} (hist : Fin a → Nat)
    {total spikeNum spikeDen massNum massDen : Nat}
    (hno : ¬ ∃ j : Fin a, FixedRungSpike hist total spikeNum spikeDen massNum massDen j)
    (hpos : 0 < total)
    (hthreshold : ∀ j : Fin a, spikeNum < spikeDen * 2 ^ (j.val + 1))
    (hmass : massNum ≤ massDen) (hle : ∀ j : Fin a, hist j ≤ total) :
    ∀ j : Fin a, hist j < total := by
  intro j
  exact lt_of_le_of_ne (hle j)
    (no_full_mass_rung_of_no_fixedRungSpike hist hno hpos hthreshold hmass j)

end ArkLib.ProximityGap.Frontier.DoorIVWorstBDyadicSelectorWalled

#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBDyadicSelectorWalled.no_fixedRungRule_of_two_rungs
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBDyadicSelectorWalled.no_fixedRungSpike_of_no_haar_excess
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBDyadicSelectorWalled.fixedRung_certificate_requires_spike
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBDyadicSelectorWalled.full_mass_exceeds_haar
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBDyadicSelectorWalled.fixedRung_full_mass_forces_spike
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBDyadicSelectorWalled.no_full_mass_rung_of_no_fixedRungSpike
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBDyadicSelectorWalled.hist_lt_total_of_no_fixedRungSpike
