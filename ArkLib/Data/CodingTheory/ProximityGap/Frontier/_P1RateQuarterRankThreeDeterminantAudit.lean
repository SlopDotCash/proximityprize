/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterScaleArithmetic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterDeterminantMultiplicity

/-!
# P1 rate-quarter rank-three determinant audit

The three-line determinant has degree at most `2*k-2`.  Its core-multiplicity
consumer therefore fires only when the three core cardinalities exceed
`N + 2*(k-1)`.  This file records the exact literal-P1 onset and compares it
with the two unconditional core-mass floors available from threshold incidence:

* three-set Bonferroni: `3*T-N = 704643074`;
* one sharp Plotkin anchor plus two universal pair intersections:
  `327272221 + 2*(2*T-N) = 550968437`.

Both are far below the determinant onset `1610612735`.  Thus determinant
multiplicity remains a valid amplifier, but cannot fire from the current
rank-three seed without a genuinely new core-growth input.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterRankThreeDeterminantAudit

open P1RateQuarterScaleArithmetic

/-- Literal predecessor agreement threshold. -/
abbrev T : Nat := 592794966

/-- First core sum that strictly exceeds the determinant degree budget after
subtracting the `N`-coordinate universe. -/
abbrev determinantCoreSumOnset : Nat := N + 2 * (k - 1) + 1

theorem determinantCoreSumOnset_eq : determinantCoreSumOnset = 1610612735 := by
  norm_num [determinantCoreSumOnset, N, k]

/-- Three threshold-size sets force this much total pair-intersection mass. -/
theorem threeThreshold_pairCoreMassFloor_eq :
    3 * T - N = 704643074 := by
  norm_num [T, N]

/-- The strongest presently unconditional seed obtained by combining the exact
Plotkin anchor with the two universal inclusion--exclusion pair floors. -/
theorem pinnedAnchor_plus_two_pairFloors_eq :
    327272221 + 2 * (2 * T - N) = 550968437 := by
  norm_num [T, N]

/-- Bonferroni alone misses determinant collapse by `905,969,661` core incidences. -/
theorem bonferroni_determinant_deficit_eq :
    determinantCoreSumOnset - (3 * T - N) = 905969661 := by
  norm_num [determinantCoreSumOnset, T, N, k]

/-- The pinned-anchor-plus-baseline estimate is weaker still. -/
theorem pinnedAnchor_determinant_deficit_eq :
    determinantCoreSumOnset -
      (327272221 + 2 * (2 * T - N)) = 1059644298 := by
  norm_num [determinantCoreSumOnset, T, N, k]

/-- Exact no-go comparison: neither current unconditional core-mass floor
reaches the three-line determinant-collapse onset. -/
theorem current_coreMass_floors_below_determinant_onset :
    3 * T - N < determinantCoreSumOnset ∧
      327272221 + 2 * (2 * T - N) < determinantCoreSumOnset := by
  norm_num [determinantCoreSumOnset, T, N, k]

/-- After paying the pinned anchor core, this is the remaining two-core mass
needed to reach determinant collapse. -/
theorem remaining_twoCore_mass_needed_eq :
    determinantCoreSumOnset - 327272221 = 1283340514 := by
  norm_num [determinantCoreSumOnset, N, k]

/-- Consequently, reaching the determinant onset forces at least one of the
other two cores to have size `641,670,257`. -/
theorem one_other_core_ge_641670257_of_onset
    (z₁ z₂ : Nat)
    (honset : determinantCoreSumOnset ≤ 327272221 + z₁ + z₂) :
    641670257 ≤ z₁ ∨ 641670257 ≤ z₂ := by
  have hOnset := determinantCoreSumOnset_eq
  omega

/-- Two cores below `641,670,257` cannot supplement the pinned anchor enough
to trigger the determinant-degree consumer. -/
theorem pinnedAnchor_sum_below_onset_of_other_cores_le
    (z₁ z₂ : Nat) (hz₁ : z₁ ≤ 641670256) (hz₂ : z₂ ≤ 641670256) :
    327272221 + z₁ + z₂ < determinantCoreSumOnset := by
  have hOnset := determinantCoreSumOnset_eq
  omega

/-! ## One-line petal recursion no-go -/

/-- Fresh agreement size available after deleting one line core. -/
abbrev freshAgreementFloor : Nat := T - (k - 1)

/-- Integer Rankin/Plotkin update forced from a source core lower bound `c`.
The `+1` encodes the strict intersection conclusion. -/
abbrev petalUpdate (c : Nat) : Nat :=
  (freshAgreementFloor ^ 2 - 1) / (N - c) + 1

theorem freshAgreementFloor_eq : freshAgreementFloor = 324359511 := by
  norm_num [freshAgreementFloor, T, k]

/-- The optimized high-core petal does not bootstrap: its next isolated-line
iterate drops by more than thirty-two million coordinates. -/
theorem petalUpdate_145836060_eq : petalUpdate 145836060 = 113383381 := by
  norm_num [petalUpdate, freshAgreementFloor, T, k, N]

/-- Exact attracting integer fixed point of the one-line reduced Plotkin map. -/
theorem petalUpdate_fixedPoint_eq : petalUpdate 109061044 = 109061044 := by
  norm_num [petalUpdate, freshAgreementFloor, T, k, N]

/-- The fixed point is strictly weaker than the universal inclusion--exclusion
pair-core floor.  Therefore independent one-line petal iteration cannot create
the new mass needed by determinant collapse. -/
theorem petalUpdate_fixedPoint_below_universal_pair_floor :
    petalUpdate 109061044 < 2 * T - N := by
  norm_num [petalUpdate, freshAgreementFloor, T, k, N]

/-! ## External common-lift defect onset -/

/-- The first external-core size whose inclusion--exclusion overlap with one
threshold-size base agreement reaches `k` roots of the degree-`<k` external
common-lift defect. -/
abbrev externalDefectCoreOnset : Nat := N - T + k

theorem externalDefectCoreOnset_eq :
    externalDefectCoreOnset = 749382314 := by
  norm_num [externalDefectCoreOnset, T, N, k]

/-- At the onset, the forced base-agreement/core overlap is exactly `k`. -/
theorem threshold_add_externalDefectCoreOnset_sub_domain_eq_k :
    T + externalDefectCoreOnset - N = k := by
  norm_num [externalDefectCoreOnset, T, N, k]

/-- The current four-point core floor remains far below the external-defect
collapse onset; a further `316,902,967` coordinates of core growth are needed. -/
theorem fourPointCore_externalDefect_deficit_eq :
    externalDefectCoreOnset - 432479347 = 316902967 := by
  norm_num [externalDefectCoreOnset, T, N, k]

/-- Common-lift core-union size required to absorb an external line at the
three-point core floor via the arbitrary-cluster overlap cap. -/
theorem clusterUnion_needed_for_externalCore_352321537_eq :
    N + k - 352321537 = 989855743 := by
  norm_num [N, k]

/-- The analogous cluster-union target at the four-point external-core floor. -/
theorem clusterUnion_needed_for_externalCore_432479347_eq :
    N + k - 432479347 = 909697933 := by
  norm_num [N, k]

/-- At the single-factor onset, the required cluster-union carrier drops
exactly to the base threshold `T`. -/
theorem clusterUnion_needed_at_externalDefectOnset_eq_threshold :
    N + k - externalDefectCoreOnset = T := by
  norm_num [externalDefectCoreOnset, T, N, k]

/-! ## Two-heavy-reference plus four-point external closure -/

/-- Two distinct common-base cores at `T-1`, after paying their `k-1`
intersection budget, already have a `917,154,475`-coordinate union. -/
theorem two_nearThreshold_coreUnion_floor_eq :
    2 * (T - 1) - (k - 1) = 917154475 := by
  norm_num [T, k]

/-- Adding an external core at the exact four-point floor crosses the
common-cluster closure threshold `N+k` by `7,456,542`. -/
theorem two_nearThreshold_plus_fourPoint_crosses_clusterClosure :
    N + k + 7456542 =
      (2 * (T - 1) - (k - 1)) + 432479347 := by
  norm_num [T, N, k]

/-- Equivalent three-core mass form: the heavy-heavy-four-point triple exceeds
the two degree budgets by `7,456,543` incidences. -/
theorem two_nearThreshold_plus_fourPoint_coreMass_surplus_eq :
    2 * (T - 1) + 432479347 - (N + 2 * (k - 1)) = 7456543 := by
  norm_num [T, N, k]

/-! ## Ten-point finite multiplicity cutoff -/

/-- Literal packing arithmetic: any line carrying ten threshold points has
core size at least `539,356,427`. -/
theorem tenPoint_packing_forces_core_ge_539356427
    (z : Nat) (hpack : 10 * (T - z) + z ≤ N) :
    539356427 ≤ z := by
  norm_num [T, N] at hpack ⊢
  omega

/-- Three ten-point core floors cross the determinant/common-lift closure
onset by `7,456,546`. -/
theorem three_tenPoint_coreFloors_surplus_eq :
    3 * 539356427 - determinantCoreSumOnset = 7456546 := by
  norm_num [determinantCoreSumOnset, N, k]

/-- Direct comparison form consumed by the three-core mass closure. -/
theorem determinantCoreSumOnset_le_three_tenPoint_coreFloors :
    determinantCoreSumOnset ≤ 3 * 539356427 := by
  norm_num [determinantCoreSumOnset, N, k]

/-! ## Exact Johnson-heavy two-hole seam -/

/-- Three nine-point packing floors remain `12,582,908` incidences below
determinant collapse. -/
theorem three_ninePoint_coreFloors_deficit_eq :
    determinantCoreSumOnset - 3 * 532676609 = 12582908 := by
  norm_num [determinantCoreSumOnset, N, k]

/-- Three cores at the exact Johnson light/heavy boundary miss the onset by
exactly two incidences. -/
theorem three_johnsonHeavy_floors_add_two_eq_onset :
    3 * 536870911 + 2 = determinantCoreSumOnset := by
  norm_num [determinantCoreSumOnset, N, k]

/-- **Two-hole trigger.**  If three cores are each Johnson-heavy and their
union omits at least two domain coordinates, their core mass exceeds the
union plus the determinant degree budget. -/
theorem johnsonHeavy_threeCore_twoHole_trigger
    (z₀ z₁ z₂ unionCard : Nat)
    (hz₀ : 536870911 ≤ z₀) (hz₁ : 536870911 ≤ z₁)
    (hz₂ : 536870911 ≤ z₂) (hholes : unionCard + 2 ≤ N) :
    2 * (k - 1) + unionCard < z₀ + z₁ + z₂ := by
  norm_num [N, k] at hholes ⊢
  omega

/-- One uncovered coordinate is arithmetically insufficient at the exact
heavy floor; the two-hole condition is sharp for this mass argument. -/
theorem oneHole_johnsonHeavy_floor_still_below_trigger :
    3 * 536870911 ≤ 2 * (k - 1) + (N - 1) := by
  norm_num [N, k]

/-- Exact near-cover form: after paying the determinant degree budget, three
Johnson-heavy floors leave `N-1` forced union coordinates. -/
theorem three_johnsonHeavy_sub_determinantBudget_eq_N_sub_one :
    3 * 536870911 - 2 * (k - 1) = N - 1 := by
  norm_num [N, k]

/-- **One-hole equality rigidity.**  For a noncollapsed heavy triple whose
weighted overlap is bounded by `2(k-1)`, exact union size `N-1` forces all
three cores to equal the heavy floor and saturates the overlap budget. -/
theorem johnsonHeavy_oneHole_rigidity
    (z₀ z₁ z₂ weightedOverlap : Nat)
    (hz₀ : 536870911 ≤ z₀) (hz₁ : 536870911 ≤ z₁)
    (hz₂ : 536870911 ≤ z₂)
    (hcap : weightedOverlap ≤ 2 * (k - 1))
    (hledger : weightedOverlap + (N - 1) = z₀ + z₁ + z₂) :
    z₀ = 536870911 ∧ z₁ = 536870911 ∧ z₂ = 536870911 ∧
      weightedOverlap = 2 * (k - 1) := by
  norm_num [N, k] at hcap hledger ⊢
  omega

/-- **Zero-hole one-slack ledger.**  If a noncollapsed heavy triple covers the
whole domain, its total core mass is at most one above the three heavy floors,
and its weighted overlap is at least one below the full determinant budget. -/
theorem johnsonHeavy_zeroHole_oneSlack
    (z₀ z₁ z₂ weightedOverlap : Nat)
    (hz₀ : 536870911 ≤ z₀) (hz₁ : 536870911 ≤ z₁)
    (hz₂ : 536870911 ≤ z₂)
    (hcap : weightedOverlap ≤ 2 * (k - 1))
    (hledger : weightedOverlap + N = z₀ + z₁ + z₂) :
    z₀ + z₁ + z₂ ≤ 3 * 536870911 + 1 ∧
      2 * (k - 1) - 1 ≤ weightedOverlap := by
  norm_num [N, k] at hcap hledger ⊢
  omega

/-- In the zero-hole case every individual core is at most one above the
heavy floor. -/
theorem johnsonHeavy_zeroHole_each_core_le_floor_add_one
    (z₀ z₁ z₂ weightedOverlap : Nat)
    (hz₀ : 536870911 ≤ z₀) (hz₁ : 536870911 ≤ z₁)
    (hz₂ : 536870911 ≤ z₂)
    (hcap : weightedOverlap ≤ 2 * (k - 1))
    (hledger : weightedOverlap + N = z₀ + z₁ + z₂) :
    z₀ ≤ 536870912 ∧ z₁ ≤ 536870912 ∧ z₂ ≤ 536870912 := by
  have hsum := johnsonHeavy_zeroHole_oneSlack
    z₀ z₁ z₂ weightedOverlap hz₀ hz₁ hz₂ hcap hledger
  omega

/-- If the weighted overlap splits across two degree-`k-1` factors, one-hole
saturation forces both factors to use their entire root budgets. -/
theorem twoFactor_fullBudget_rigidity
    (referenceRoots defectRoots : Nat)
    (href : referenceRoots ≤ k - 1) (hdefect : defectRoots ≤ k - 1)
    (hsum : referenceRoots + defectRoots = 2 * (k - 1)) :
    referenceRoots = k - 1 ∧ defectRoots = k - 1 := by
  omega

/-- In the zero-hole one-slack case, each factor is within one root of
saturation. -/
theorem twoFactor_oneSlack_nearSaturation
    (referenceRoots defectRoots : Nat)
    (href : referenceRoots ≤ k - 1) (hdefect : defectRoots ≤ k - 1)
    (hsum : 2 * (k - 1) - 1 ≤ referenceRoots + defectRoots) :
    k - 2 ≤ referenceRoots ∧ k - 2 ≤ defectRoots := by
  have hk : k = 268435456 := by norm_num [k]
  omega

/-! ## One-hole witness-distribution audit -/

/-- A threshold witness loses at most one coordinate to the unique core-union
hole, then three-way pigeonhole guarantees this many agreements in one core. -/
theorem oneHole_threeCore_pigeonhole_floor_eq :
    ((T - 1) + 2) / 3 = 197598322 := by
  norm_num [T]

/-- The one-core share guaranteed by the near-cover remains `70,837,134`
coordinates below the polynomial identity threshold `k`. -/
theorem oneHole_pigeonhole_to_rootThreshold_deficit_eq :
    k - 197598322 = 70837134 := by
  norm_num [k]

/-- Abstract three-bin form consumed after assigning each covered witness
coordinate to one of the three cores. -/
theorem oneHole_threshold_assignment_forces_bin_ge_197598322
    (b₀ b₁ b₂ : Nat) (hcover : T - 1 ≤ b₀ + b₁ + b₂) :
    197598322 ≤ b₀ ∨ 197598322 ≤ b₁ ∨ 197598322 ≤ b₂ := by
  norm_num [T] at hcover
  omega

/-- Exact no-go comparison: the guaranteed bin does not reach `k`. -/
theorem oneHole_threeCore_pigeonhole_below_k : 197598322 < k := by
  norm_num [k]

/-- If the witness uses only two covering cores, the guaranteed share jumps
above `k`. -/
theorem oneHole_twoCore_pigeonhole_floor_eq :
    ((T - 1) + 1) / 2 = 296397483 := by
  norm_num [T]

theorem oneHole_twoCore_pigeonhole_exceeds_k_by_27962027 :
    296397483 - k = 27962027 := by
  norm_num [k]

theorem oneHole_twoCore_assignment_forces_rootThreshold
    (b₀ b₁ : Nat) (hcover : T - 1 ≤ b₀ + b₁) :
    k ≤ b₀ ∨ k ≤ b₁ := by
  norm_num [T, k] at hcover ⊢
  omega

/-- **Balanced one-hole escape is arithmetically realized.**  All `T-1`
covered witness agreements can be distributed across all three cores with
every bin strictly below `k`. -/
theorem oneHole_balanced_threeCore_distribution_realized :
    197598322 + 197598322 + 197598321 = T - 1 ∧
      197598322 < k ∧ 197598322 < k ∧ 197598321 < k := by
  norm_num [T, k]

/-- The zero-hole analogue is perfectly balanced: `T` splits into three equal
subcritical bins. -/
theorem zeroHole_balanced_threeCore_distribution_realized :
    3 * 197598322 = T ∧ 197598322 < k := by
  norm_num [T, k]

/-- Total unused one-core root capacity in the balanced one-hole assignment. -/
theorem oneHole_threeCore_rootCapacity_slack_eq :
    3 * (k - 1) - (T - 1) = 212511400 := by
  norm_num [T, k]

/-! ## Sequential CRT quotient budget -/

/-- Factoring a balanced first-bin locator from a degree-`<k` witness residual
leaves fewer than this many quotient coefficients. -/
theorem balanced_firstBin_remaining_degree_budget_eq :
    k - 197598322 = 70837134 := by
  norm_num [k]

/-- A second balanced bin supplies this many evaluations beyond the remaining
quotient degree budget. -/
theorem balanced_secondBin_overdetermination_eq :
    197598322 - 70837134 = 126761188 := by
  norm_num

/-- The second bin is strictly larger than the full remaining degree budget. -/
theorem balanced_secondBin_gt_remaining_degree_budget :
    70837134 < 197598322 := by
  norm_num

/-! ## Canonical-support cross-root budget -/

/-- With two balanced common-line bins, the Padé cross-root inequalities
force at least this many points of the saturated `k-1` reference support to
lie outside those two bins.  Such points must be assigned to the external
color or omitted from the witness agreement set. -/
theorem balanced_commonBins_leave_referenceSupport_mass
    (r0 r1 : Nat)
    (hr0 : r0 + 197598322 < k)
    (hr1 : r1 + 197598322 < k) :
    126761189 ≤ (k - 1) - (r0 + r1) := by
  norm_num [k] at hr0 hr1 ⊢
  omega

/-- The exact endpoint behind the preceding forced-diversion bound. -/
theorem balanced_commonBins_referenceSupport_diversion_eq :
    (k - 1) - 2 * 70837133 = 126761189 := by
  norm_num [k]

/-! ## Saturated one-hole Venn classification -/

/-- Write the seven nonempty Venn atoms of the two reference cores and the
external core as `a,b,c,d,e,f,t`, where `c` is external-only, `d` is
reference-reference only, `e,f` are the two reference-external-only atoms,
and `t` is triple.  Saturation of the reference support and external-defect
support already forces the external-only atom to have exactly `k` points and
the two reference-only/external-overlap pairs to sum to `k`. -/
theorem saturated_twoSupport_venn_rigidity
    (a b c d e f t : Nat)
    (hcore0 : a + d + e + t = 2 * k - 1)
    (hcore1 : b + d + f + t = 2 * k - 1)
    (hcoreE : c + e + f + t = 2 * k - 1)
    (hR : d + t = k - 1)
    (hQ : e + f + t = k - 1) :
    c = k ∧ a + e = k ∧ b + f = k := by
  norm_num [k] at hcore0 hcore1 hcoreE hR hQ ⊢
  omega

/-- **Extreme saturated Venn countermodel.**  The exact one-hole equations
permit `t=e=0`, with the whole external-defect overlap concentrated in the
second reference core.  All three balanced witness bins then fit in pairwise
disjoint atoms (`a`, `f`, and `c`), while both common-bin choices avoid the
reference support `R=d∪t` entirely.  Hence Venn cardinalities plus the
single-witness `R` cross-root budget cannot by themselves force the
cross-rider support stability needed for `Q` root transfer. -/
theorem extreme_saturated_venn_balancedBins_countermodel :
    let a := k
    let b := 1
    let c := k
    let d := k - 1
    let e := 0
    let f := k - 1
    let t := 0
    a + d + e + t = 2 * k - 1 ∧
      b + d + f + t = 2 * k - 1 ∧
      c + e + f + t = 2 * k - 1 ∧
      d + t = k - 1 ∧ e + f + t = k - 1 ∧
      197598322 ≤ a ∧ 197598322 ≤ f ∧
      197598321 ≤ c ∧
      197598322 + 197598322 + 197598321 = T - 1 := by
  norm_num [k, T]

/-- Even two balanced rider bins fit disjointly inside one Johnson-heavy
core, so pairwise cardinality alone gives no same-color support overlap. -/
theorem two_balanced_riderBins_fit_disjointly_in_heavyCore :
    2 * 197598322 ≤ 536870911 := by
  norm_num

/-- Three balanced bins only exceed one heavy core by this much, still below
the quotient degree budget and far below a root-forcing threshold. -/
theorem three_balanced_riderBins_heavyCore_excess_eq :
    3 * 197598322 - 536870911 = 55924055 := by
  norm_num

/-- At balanced bin size, the cancellation branch of the cross-locator
identity forces a shared-bin intersection of at least `126761189`. -/
theorem balanced_crossLocator_cancellation_intersection_floor
    (sdiff inter : Nat)
    (hcard : sdiff + inter = 197598322)
    (hbudget : sdiff + 197598322 < k) :
    126761189 ≤ inter := by
  norm_num [k] at hbudget ⊢
  omega

/-- Equivalently, cancellation permits at most this many directed bin
differences. -/
theorem balanced_crossLocator_cancellation_sdiff_cap
    (sdiff : Nat) (hbudget : sdiff + 197598322 < k) :
    sdiff ≤ 70837133 := by
  norm_num [k] at hbudget ⊢
  omega

/-- **Three-rider exclusive-atom countermodel.**  Three balanced bins fit
inside a `k`-point atom using three pair-only atoms of size `70837134` and one
triple atom of size `55924054`.  Every bin has the balanced size, their union
has size exactly `k`, and every pair intersection is only `126761188 < k`.
Placed in the reference-only atom `a` or external-only atom `c`, this realizes
all pairwise `Q`-charge inequalities while avoiding `Q` entirely. -/
theorem three_balanced_bins_inside_k_atom_countermodel :
    let pairOnly := 70837134
    let triple := 55924054
    2 * pairOnly + triple = 197598322 ∧
      3 * pairOnly + triple = k ∧
      pairOnly + triple = 126761188 ∧
      pairOnly + triple < k := by
  norm_num [k]

/-- **Arbitrary-multiplicity reused-bin wall.**  If every rider reuses one
balanced reference bin inside the reference-only `k`-atom and one balanced
external bin inside the external-only `k`-atom, both shared-bin intersections
have size `197598322` and both intersections with `Q` are zero.  The two
`Q`-cross-root inequalities remain strictly feasible, independently of how
many riders reuse the bins. -/
theorem reused_balanced_exclusiveBins_QcrossRoot_feasible :
    0 + 197598322 < k ∧ 0 + 197598322 < k := by
  norm_num [k]

/-! ## Received-word bootstrap two-block wall -/

/-- Two threshold blocks can meet at their unavoidable inclusion--exclusion
floor, which is far below the `k` coordinates needed to bootstrap a component
whose lower-rank witnesses all lie in the other block. -/
theorem threshold_twoBlock_bootstrap_crossCoverage_deficit_eq :
    k - (2 * T - N) = 156587348 := by
  norm_num [k, T, N]

theorem threshold_twoBlock_crossCoverage_below_k :
    2 * T - N < k := by
  norm_num [k, T, N]

/-! ## Three-pair Hall-ledger wall -/

/-- The existing low-multiplicity/exact-three ledger cannot improve the
four-disjoint-bad-pair theorem to three pairs.  This literal assignment
saturates the exact-three universe and pair inequality while satisfying the
weighted low-mass and six-endpoint surplus constraints with exact slack
`96076784937031003`. -/
theorem three_pairHall_obstruction_ledger_numerically_feasible :
    let lowMass := 872415239
    let surplus := 1073741821
    let exactThree := N
    (N + 1 - 2) * lowMass ≤ 2 * (N + 1) * (N - T) ∧
      6 * (T - k) ≤ surplus + lowMass ∧
      surplus + 3 ≤ exactThree ∧ exactThree ≤ N := by
  norm_num [N, T, k]

theorem three_pairHall_ledger_weighted_slack_eq :
    2 * (N + 1) * (N - T) -
      (N + 1 - 2) * 872415239 = 96076784937031003 := by
  norm_num [N, T]

end ArkLib.ProximityGap.Frontier.P1RateQuarterRankThreeDeterminantAudit

open ArkLib.ProximityGap.Frontier.P1RateQuarterRankThreeDeterminantAudit

#print axioms determinantCoreSumOnset_eq
#print axioms threeThreshold_pairCoreMassFloor_eq
#print axioms pinnedAnchor_plus_two_pairFloors_eq
#print axioms bonferroni_determinant_deficit_eq
#print axioms pinnedAnchor_determinant_deficit_eq
#print axioms current_coreMass_floors_below_determinant_onset
#print axioms remaining_twoCore_mass_needed_eq
#print axioms one_other_core_ge_641670257_of_onset
#print axioms pinnedAnchor_sum_below_onset_of_other_cores_le
#print axioms freshAgreementFloor_eq
#print axioms petalUpdate_145836060_eq
#print axioms petalUpdate_fixedPoint_eq
#print axioms petalUpdate_fixedPoint_below_universal_pair_floor
#print axioms externalDefectCoreOnset_eq
#print axioms threshold_add_externalDefectCoreOnset_sub_domain_eq_k
#print axioms fourPointCore_externalDefect_deficit_eq
#print axioms clusterUnion_needed_for_externalCore_352321537_eq
#print axioms clusterUnion_needed_for_externalCore_432479347_eq
#print axioms clusterUnion_needed_at_externalDefectOnset_eq_threshold
#print axioms two_nearThreshold_coreUnion_floor_eq
#print axioms two_nearThreshold_plus_fourPoint_crosses_clusterClosure
#print axioms two_nearThreshold_plus_fourPoint_coreMass_surplus_eq
#print axioms tenPoint_packing_forces_core_ge_539356427
#print axioms three_tenPoint_coreFloors_surplus_eq
#print axioms determinantCoreSumOnset_le_three_tenPoint_coreFloors
#print axioms three_ninePoint_coreFloors_deficit_eq
#print axioms three_johnsonHeavy_floors_add_two_eq_onset
#print axioms johnsonHeavy_threeCore_twoHole_trigger
#print axioms oneHole_johnsonHeavy_floor_still_below_trigger
#print axioms three_johnsonHeavy_sub_determinantBudget_eq_N_sub_one
#print axioms johnsonHeavy_oneHole_rigidity
#print axioms johnsonHeavy_zeroHole_oneSlack
#print axioms johnsonHeavy_zeroHole_each_core_le_floor_add_one
#print axioms twoFactor_fullBudget_rigidity
#print axioms twoFactor_oneSlack_nearSaturation
#print axioms oneHole_threeCore_pigeonhole_floor_eq
#print axioms oneHole_pigeonhole_to_rootThreshold_deficit_eq
#print axioms oneHole_threshold_assignment_forces_bin_ge_197598322
#print axioms oneHole_threeCore_pigeonhole_below_k
#print axioms oneHole_twoCore_pigeonhole_floor_eq
#print axioms oneHole_twoCore_pigeonhole_exceeds_k_by_27962027
#print axioms oneHole_twoCore_assignment_forces_rootThreshold
#print axioms oneHole_balanced_threeCore_distribution_realized
#print axioms zeroHole_balanced_threeCore_distribution_realized
#print axioms oneHole_threeCore_rootCapacity_slack_eq
#print axioms balanced_firstBin_remaining_degree_budget_eq
#print axioms balanced_secondBin_overdetermination_eq
#print axioms balanced_secondBin_gt_remaining_degree_budget
#print axioms balanced_commonBins_leave_referenceSupport_mass
#print axioms balanced_commonBins_referenceSupport_diversion_eq
#print axioms saturated_twoSupport_venn_rigidity
#print axioms extreme_saturated_venn_balancedBins_countermodel
#print axioms two_balanced_riderBins_fit_disjointly_in_heavyCore
#print axioms three_balanced_riderBins_heavyCore_excess_eq
#print axioms balanced_crossLocator_cancellation_intersection_floor
#print axioms balanced_crossLocator_cancellation_sdiff_cap
#print axioms three_balanced_bins_inside_k_atom_countermodel
#print axioms reused_balanced_exclusiveBins_QcrossRoot_feasible
#print axioms threshold_twoBlock_bootstrap_crossCoverage_deficit_eq
#print axioms threshold_twoBlock_crossCoverage_below_k
#print axioms three_pairHall_obstruction_ledger_numerically_feasible
#print axioms three_pairHall_ledger_weighted_slack_eq
