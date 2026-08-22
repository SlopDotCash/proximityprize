/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R378SignedDifferenceRotationInvariance
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G75RawDeviationVsRelationAnomaly
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G77FRelationAnomalyFourierGauge

/-!
# G89: the first-incidence cross-orbit bound IS the wall — exact equivalence, constant 1

## The last recorded off-BGK door (issue #505, HONEST-CLOSURE route, exit criterion 2)

After G77 (the signed relation route's TOTAL value is an exact Fourier gauge of the
DC-subtracted moment), G78 (embedding rigidity: the "single-embedding" qualifier has zero
slack), and G80 (the signed `l1` certificate functional is pinned to the wall `M`), the sole
formulation of the signed relation route not yet pinned was the **first-incidence cross-orbit
refinement**: sum the signed doubled-walk endpoint discrepancy only over the FIRST occurrence
of each negacyclic rotation orbit (one representative per orbit, weighted by its orbit size),
across distinct orbits.  Could a bound on THAT functional be a strictly weaker sufficient
condition for `DCEnergyBound` than the BGK/Paley wall itself?

## Answer: no — and the constant is exactly 1

This file constructs the full negacyclic orbit structure on the signed difference family and
proves the equivalence as an exact identity, not an estimate:

1. **Full-orbit dynamics.**  `rotZ^[m] = −id` and `rotZ^[2m] = id`
   (`iterate_rotZ_m`, `iterate_rotZ_two_m`): the negacyclic rotation generates a genuine
   cyclic action of order dividing `2m`, so the full orbits
   `negacyclicOrbit m hm d = {rotZ^[t] d : t < 2m}` are equal-or-disjoint
   (`negacyclicOrbit_eq_of_mem`, `negacyclicOrbit_disjoint_of_not_mem`) — unlike the
   half-orbit `rotationOrbit` of R380, which is not symmetric under membership.
2. **Transversal structure.**  `IsOrbitTransversal m hm S T` says `T ⊆ S` picks one
   first-incidence representative per orbit meeting `S`, with pairwise disjoint orbits;
   representatives are unique per point (`transversal_rep_unique`) and a transversal always
   exists (`exists_orbitTransversal`) — the formulation is non-vacuous.
3. **Exact compression, constant 1.**  The signed summand is constant on each full orbit
   (`signedEndpointSummand_eq_of_mem_negacyclicOrbit`, extending R378/R381 from the
   half-orbit), the difference family is orbit-closed
   (`negacyclicOrbit_subset_allShadowDifferences`), and the sandwich
   `firstIncidence ≤ anomaly ≤ C · firstIncidence` collapses to an EQUALITY with `C = 1`:

   `firstIncidenceDiscrepancy g m r hm T = relationAnomaly g (2m) m r`

   (`firstIncidenceDiscrepancy_eq_relationAnomaly`) — for EVERY transversal `T`; hence the
   value is transversal-independent (`firstIncidenceDiscrepancy_transversal_independent`).
4. **Headline** (`firstIncidence_bound_iff_wall`): at the prize shape
   (`orderOf g = n = 2m`, `g^m = −1`), for every transversal, the first-incidence
   cross-orbit bound at the Wick budget is EQUIVALENT to `DCEnergyBound (powerRootSet g n) r`
   — the production BGK/Paley wall statement (via G75's exact calibration).  More generally
   (`firstIncidence_le_iff_relationAnomaly_le`) the sets of sufficient thresholds for the
   first-incidence functional and for the centered relation anomaly are IDENTICAL: no
   strictly weaker sufficient condition can be phrased through first incidences.
5. **Fourier form** (`firstIncidence_eq_dcMoment_sub_floor`): the first-incidence value IS
   the DC-subtracted moment minus the characteristic-zero floor — literally the wall object,
   via G77's gauge.
6. **Unweighted variant** (`relationAnomaly_eq_orbitSize_mul_rawFirstIncidence`,
   `rawFirstIncidence_le_iff_wall_scaled`): dropping the orbit-size weights rescales the wall
   by EXACTLY the (uniform) orbit size — again no slack, only a known constant.
7. **No hidden cancellation** (`abs_sum_negacyclicOrbit_eq_sum_abs`): the R382
   no-cancellation identity extends from the half-orbit to the FULL `2m`-orbit — each
   first-incidence block is phase-coherent, so the compression neither loses nor gains.

## Honest scope

This is a quantitative-identity pin (a no-go for the "weaker first-incidence sufficient
condition" hope), not a bound on the wall: `DCEnergyBound` itself remains OPEN.  Together with
G77 (total value = gauge), G78 (embedding slack = 0), G80 (`l1` certificate = `M`), and this
file (first-incidence cross-orbit = wall, constant exactly 1), every recorded formulation of
the signed relation route is now formally pinned to the BGK/Paley face.  CORE remains
OPEN / ON-BGK.  The small rotation-dynamics lemmas duplicated from R395 are re-derived locally
to keep the import surface minimal (R395 pulls the decidable-certificate chain).

Issues #505 / #466.  Target axiom set: `[propext, Classical.choice, Quot.sound]`;
no `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence

open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition
open ArkLib.ProximityGap.Frontier.R366CenteredRelationAnomaly
open ArkLib.ProximityGap.Frontier.R367SignedShadowPairDiscrepancy
open ArkLib.ProximityGap.Frontier.R368SignedDifferenceFiberDecomposition
open ArkLib.ProximityGap.Frontier.R369SignedDifferenceMassDoubling
open ArkLib.ProximityGap.Frontier.R371ShadowKernelRotationAction
open ArkLib.ProximityGap.Frontier.R372ShadowRelationRotationEquivariance
open ArkLib.ProximityGap.Frontier.R378SignedDifferenceRotationInvariance
open ArkLib.ProximityGap.Frontier.G75RawDeviationVsRelationAnomaly
open ArkLib.ProximityGap.Frontier.G77RelationAnomalyFourierGauge

/-! ### 1. Full-period rotation dynamics: `rotZ^[m] = −id`, `rotZ^[2m] = id`

The two coordinate-tracking lemmas are local re-derivations of R395's
`iterate_rotZ_apply`/`iterate_rotZ_head` (kept local to avoid importing the
decidable-certificate chain). -/

/-- The head coordinate after one rotation: wrap with a sign flip. -/
theorem rotZ_head (m : ℕ) (hm : 0 < m) (w : Fin m → ℤ) :
    rotZ m hm w ⟨0, hm⟩ = -w ⟨m - 1, by omega⟩ := by
  unfold rotZ
  rw [if_pos rfl]

/-- A tail coordinate after one rotation: shift down by one slot, no sign. -/
theorem rotZ_tail (m : ℕ) (hm : 0 < m) (w : Fin m → ℤ) (j : Fin m) (hj : (j : ℕ) ≠ 0) :
    rotZ m hm w j = w ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ := by
  unfold rotZ
  rw [if_neg hj]

/-- Rotation dynamics without wrap: after `k` steps, coordinate `j` sits at `j + k`. -/
theorem iterate_rotZ_coord (m : ℕ) (hm : 0 < m) (z : Fin m → ℤ) (k j : ℕ)
    (hjk : j + k < m) :
    ((rotZ m hm)^[k] z) ⟨j + k, hjk⟩ = z ⟨j, by omega⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      rw [rotZ_tail m hm _ ⟨j + (k + 1), hjk⟩ (by show j + (k + 1) ≠ 0; omega)]
      rw [show (⟨((⟨j + (k + 1), hjk⟩ : Fin m) : ℕ) - 1, by
          have := (⟨j + (k + 1), hjk⟩ : Fin m).isLt
          omega⟩ : Fin m)
        = ⟨j + k, by omega⟩ from Fin.ext (show j + (k + 1) - 1 = j + k from by omega)]
      exact ih (by omega)

/-- After `m − j` steps, coordinate `j` arrives at the head with a sign flip. -/
theorem iterate_rotZ_head (m : ℕ) (hm : 0 < m) (z : Fin m → ℤ) (j : ℕ) (hj : j < m) :
    ((rotZ m hm)^[m - j] z) ⟨0, hm⟩ = -z ⟨j, hj⟩ := by
  have hstep : m - j = (m - 1 - j) + 1 := by omega
  rw [hstep, Function.iterate_succ_apply', rotZ_head m hm]
  have harr : ((rotZ m hm)^[m - 1 - j] z) ⟨m - 1, by omega⟩ = z ⟨j, hj⟩ := by
    have h0 := iterate_rotZ_coord m hm z (m - 1 - j) j (by omega)
    rw [show (⟨j + (m - 1 - j), by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ from
      Fin.ext (show j + (m - 1 - j) = m - 1 from by omega)] at h0
    exact h0
  rw [harr]

/-- **Half-period sign flip**: `m` negacyclic rotations negate the vector exactly
(the shadow-basis avatar of `ζ^m = −1`). -/
theorem iterate_rotZ_m (m : ℕ) (hm : 0 < m) (z : Fin m → ℤ) :
    (rotZ m hm)^[m] z = -z := by
  funext i
  have hik : 0 + (i : ℕ) < m := by simpa using i.isLt
  have hsplit : (i : ℕ) + (m - (i : ℕ)) = m := by have := i.isLt; omega
  have h1 : ((rotZ m hm)^[(i : ℕ)] ((rotZ m hm)^[m - (i : ℕ)] z)) ⟨0 + (i : ℕ), hik⟩
      = ((rotZ m hm)^[m - (i : ℕ)] z) ⟨0, hm⟩ :=
    iterate_rotZ_coord m hm _ (i : ℕ) 0 hik
  have h2 : ((rotZ m hm)^[m - (i : ℕ)] z) ⟨0, hm⟩ = -z ⟨(i : ℕ), i.isLt⟩ :=
    iterate_rotZ_head m hm z (i : ℕ) i.isLt
  have h3 : (rotZ m hm)^[m] z
      = (rotZ m hm)^[(i : ℕ)] ((rotZ m hm)^[m - (i : ℕ)] z) := by
    rw [← Function.iterate_add_apply, hsplit]
  have h4 : i = (⟨0 + (i : ℕ), hik⟩ : Fin m) := Fin.ext (by simp)
  rw [← h3] at h1
  rw [← h4] at h1
  rw [h1, h2]
  rfl

/-- **Full period**: `2m` negacyclic rotations restore the vector exactly. -/
theorem iterate_rotZ_two_m (m : ℕ) (hm : 0 < m) (z : Fin m → ℤ) :
    (rotZ m hm)^[2 * m] z = z := by
  have h : 2 * m = m + m := by ring
  rw [h, Function.iterate_add_apply, iterate_rotZ_m m hm, iterate_rotZ_m m hm, neg_neg]

/-- Adding one full period to the iterate count changes nothing. -/
theorem iterate_rotZ_add_two_m (m : ℕ) (hm : 0 < m) (z : Fin m → ℤ) (t : ℕ) :
    (rotZ m hm)^[t + 2 * m] z = (rotZ m hm)^[t] z := by
  rw [Function.iterate_add_apply, iterate_rotZ_two_m m hm]

/-- Adding any multiple of the full period changes nothing. -/
theorem iterate_rotZ_add_period_mul (m : ℕ) (hm : 0 < m) (z : Fin m → ℤ) (s k : ℕ) :
    (rotZ m hm)^[s + 2 * m * k] z = (rotZ m hm)^[s] z := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h : s + 2 * m * (k + 1) = s + 2 * m * k + 2 * m := by ring
      rw [h, iterate_rotZ_add_two_m m hm, ih]

/-- Every iterate count reduces modulo the full period `2m`. -/
theorem iterate_rotZ_mod_period (m : ℕ) (hm : 0 < m) (z : Fin m → ℤ) (t : ℕ) :
    (rotZ m hm)^[t] z = (rotZ m hm)^[t % (2 * m)] z := by
  conv_lhs => rw [← Nat.mod_add_div t (2 * m)]
  exact iterate_rotZ_add_period_mul m hm z (t % (2 * m)) (t / (2 * m))

/-! ### 2. The full negacyclic orbit is a genuine (equal-or-disjoint) block system -/

/-- The **full negacyclic rotation orbit**: all `2m` iterated rotations.  After `m` steps the
vector is negated (`iterate_rotZ_m`), after `2m` it returns exactly (`iterate_rotZ_two_m`), so
this is the orbit of the cyclic group generated by `rotZ` — unlike R380's half-orbit
`rotationOrbit` (first `m` rotations only), whose membership relation is not symmetric. -/
noncomputable def negacyclicOrbit (m : ℕ) (hm : 0 < m) (d : Fin m → ℤ) :
    Finset (Fin m → ℤ) :=
  (Finset.range (2 * m)).image (fun t => (rotZ m hm)^[t] d)

/-- Orbit membership is exactly reachability by SOME iterate (period reduction built in). -/
theorem mem_negacyclicOrbit_iff (m : ℕ) (hm : 0 < m) (d e : Fin m → ℤ) :
    e ∈ negacyclicOrbit m hm d ↔ ∃ t : ℕ, e = (rotZ m hm)^[t] d := by
  constructor
  · intro he
    rw [negacyclicOrbit, Finset.mem_image] at he
    obtain ⟨t, _, rfl⟩ := he
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    rw [negacyclicOrbit, Finset.mem_image]
    exact ⟨t % (2 * m), Finset.mem_range.mpr (Nat.mod_lt _ (by omega)),
      (iterate_rotZ_mod_period m hm d t).symm⟩

/-- Every vector lies in its own orbit. -/
theorem self_mem_negacyclicOrbit (m : ℕ) (hm : 0 < m) (d : Fin m → ℤ) :
    d ∈ negacyclicOrbit m hm d :=
  (mem_negacyclicOrbit_iff m hm d d).mpr ⟨0, rfl⟩

/-- The full orbit has at most `2m` elements. -/
theorem card_negacyclicOrbit_le (m : ℕ) (hm : 0 < m) (d : Fin m → ℤ) :
    (negacyclicOrbit m hm d).card ≤ 2 * m :=
  le_trans Finset.card_image_le (by simp)

/-- **Symmetry** of orbit membership (this is where the full period is essential). -/
theorem mem_negacyclicOrbit_symm (m : ℕ) (hm : 0 < m) {d e : Fin m → ℤ}
    (he : e ∈ negacyclicOrbit m hm d) : d ∈ negacyclicOrbit m hm e := by
  obtain ⟨t, rfl⟩ := (mem_negacyclicOrbit_iff m hm d e).mp he
  refine (mem_negacyclicOrbit_iff m hm ((rotZ m hm)^[t] d) d).mpr
    ⟨2 * m - t % (2 * m), ?_⟩
  rw [iterate_rotZ_mod_period m hm d t, ← Function.iterate_add_apply]
  have hmod : t % (2 * m) < 2 * m := Nat.mod_lt t (by omega)
  have h : 2 * m - t % (2 * m) + t % (2 * m) = 2 * m := by omega
  rw [h, iterate_rotZ_two_m m hm]

/-- The orbit of a member is contained in the original orbit. -/
theorem negacyclicOrbit_subset_of_mem (m : ℕ) (hm : 0 < m) {d e : Fin m → ℤ}
    (he : e ∈ negacyclicOrbit m hm d) :
    negacyclicOrbit m hm e ⊆ negacyclicOrbit m hm d := by
  obtain ⟨t, rfl⟩ := (mem_negacyclicOrbit_iff m hm d e).mp he
  intro x hx
  obtain ⟨s, rfl⟩ := (mem_negacyclicOrbit_iff m hm _ x).mp hx
  rw [← Function.iterate_add_apply]
  exact (mem_negacyclicOrbit_iff m hm d _).mpr ⟨s + t, rfl⟩

/-- **Orbits of members coincide**: the block system is well defined. -/
theorem negacyclicOrbit_eq_of_mem (m : ℕ) (hm : 0 < m) {d e : Fin m → ℤ}
    (he : e ∈ negacyclicOrbit m hm d) :
    negacyclicOrbit m hm e = negacyclicOrbit m hm d :=
  Finset.Subset.antisymm (negacyclicOrbit_subset_of_mem m hm he)
    (negacyclicOrbit_subset_of_mem m hm (mem_negacyclicOrbit_symm m hm he))

/-- **Equal or disjoint**: orbits of non-members are disjoint. -/
theorem negacyclicOrbit_disjoint_of_not_mem (m : ℕ) (hm : 0 < m) {d e : Fin m → ℤ}
    (h : e ∉ negacyclicOrbit m hm d) :
    Disjoint (negacyclicOrbit m hm e) (negacyclicOrbit m hm d) := by
  rw [Finset.disjoint_left]
  intro x hxe hxd
  apply h
  have h1 := negacyclicOrbit_eq_of_mem m hm hxe
  have h2 := negacyclicOrbit_eq_of_mem m hm hxd
  have hself : e ∈ negacyclicOrbit m hm e := self_mem_negacyclicOrbit m hm e
  rw [← h1, h2] at hself
  exact hself

/-! ### 3. The signed difference family is orbit-closed and the summand is orbit-constant -/

/-- Rotation commutes with taking a shadow difference (local re-derivation of R381's lemma,
kept here to keep the import surface minimal). -/
theorem rotZ_shadowDifference (m : ℕ) (hm : 0 < m)
    (p : (Fin m → ℤ) × (Fin m → ℤ)) :
    rotZ m hm (shadowDifference p) =
      shadowDifference (rotZ m hm p.1, rotZ m hm p.2) := by
  funext j
  unfold rotZ shadowDifference
  by_cases hj : (j : ℕ) = 0 <;> simp [hj] <;> ring

/-- One rotation preserves membership in the full shadow-difference family
(local re-derivation of R381's `allShadowDifferences_rotZ`). -/
theorem allShadowDifferences_rotZ_mem (m r : ℕ) (hm : 0 < m) {d : Fin m → ℤ}
    (hd : d ∈ allShadowDifferences (2 * m) m r) :
    rotZ m hm d ∈ allShadowDifferences (2 * m) m r := by
  classical
  rw [allShadowDifferences, Finset.mem_image] at hd ⊢
  obtain ⟨p, hp, rfl⟩ := hd
  refine ⟨(rotZ m hm p.1, rotZ m hm p.2), ?_, (rotZ_shadowDifference m hm p).symm⟩
  rw [Finset.mem_offDiag] at hp ⊢
  refine ⟨keysR_rotZ (2 * m) m r hm rfl p.1 hp.1,
    keysR_rotZ (2 * m) m r hm rfl p.2 hp.2.1, ?_⟩
  intro heq
  exact hp.2.2 ((rotZ_bijective m hm).1 heq)

/-- Every iterate of a shadow difference remains a shadow difference. -/
theorem iterate_mem_allShadowDifferences (m r : ℕ) (hm : 0 < m) {d : Fin m → ℤ}
    (hd : d ∈ allShadowDifferences (2 * m) m r) (t : ℕ) :
    (rotZ m hm)^[t] d ∈ allShadowDifferences (2 * m) m r := by
  induction t with
  | zero => simpa using hd
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact allShadowDifferences_rotZ_mem m r hm ih

/-- **Orbit closure**: the full negacyclic orbit of a shadow difference stays inside the
shadow-difference family. -/
theorem negacyclicOrbit_subset_allShadowDifferences (m r : ℕ) (hm : 0 < m)
    {d : Fin m → ℤ} (hd : d ∈ allShadowDifferences (2 * m) m r) :
    negacyclicOrbit m hm d ⊆ allShadowDifferences (2 * m) m r := by
  intro e he
  obtain ⟨t, rfl⟩ := (mem_negacyclicOrbit_iff m hm d e).mp he
  exact iterate_mem_allShadowDifferences m r hm hd t

/-- The signed endpoint summand is invariant under every iterate of the rotation. -/
theorem signedEndpointSummand_iterate
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) (hm : 0 < m) (hg : g ^ m = -1) (hg0 : g ≠ 0)
    (d : Fin m → ℤ) (t : ℕ) :
    signedEndpointSummand g m r ((rotZ m hm)^[t] d) = signedEndpointSummand g m r d := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', signedEndpointSummand_rotZ g m r hm hg hg0, ih]

/-- **Orbit constancy on the FULL orbit** (extends R381's half-orbit statement through the
`d ↦ −d` crossing at step `m`). -/
theorem signedEndpointSummand_eq_of_mem_negacyclicOrbit
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) (hm : 0 < m) (hg : g ^ m = -1) (hg0 : g ≠ 0)
    (d : Fin m → ℤ) {e : Fin m → ℤ} (he : e ∈ negacyclicOrbit m hm d) :
    signedEndpointSummand g m r e = signedEndpointSummand g m r d := by
  obtain ⟨t, rfl⟩ := (mem_negacyclicOrbit_iff m hm d e).mp he
  exact signedEndpointSummand_iterate g m r hm hg hg0 d t

/-- The full-orbit block sum is its cardinality times the representative's summand. -/
theorem sum_negacyclicOrbit_signedEndpointSummand
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) (hm : 0 < m) (hg : g ^ m = -1) (hg0 : g ≠ 0)
    (d : Fin m → ℤ) :
    ∑ e ∈ negacyclicOrbit m hm d, signedEndpointSummand g m r e =
      ((negacyclicOrbit m hm d).card : ℝ) * signedEndpointSummand g m r d := by
  calc
    (∑ e ∈ negacyclicOrbit m hm d, signedEndpointSummand g m r e) =
        ∑ _e ∈ negacyclicOrbit m hm d, signedEndpointSummand g m r d :=
      Finset.sum_congr rfl (fun e he =>
        signedEndpointSummand_eq_of_mem_negacyclicOrbit g m r hm hg hg0 d he)
    _ = ((negacyclicOrbit m hm d).card : ℝ) * signedEndpointSummand g m r d := by simp

/-- **No cancellation inside a FULL orbit block** (extends R382 from the half-orbit): the
triangle inequality on a full negacyclic block is an equality, so the first-incidence
compression below neither loses nor gains signed mass. -/
theorem abs_sum_negacyclicOrbit_eq_sum_abs
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) (hm : 0 < m) (hg : g ^ m = -1) (hg0 : g ≠ 0)
    (d : Fin m → ℤ) :
    |∑ e ∈ negacyclicOrbit m hm d, signedEndpointSummand g m r e| =
      ∑ e ∈ negacyclicOrbit m hm d, |signedEndpointSummand g m r e| := by
  calc |∑ e ∈ negacyclicOrbit m hm d, signedEndpointSummand g m r e|
      = |((negacyclicOrbit m hm d).card : ℝ) * signedEndpointSummand g m r d| := by
        rw [sum_negacyclicOrbit_signedEndpointSummand g m r hm hg hg0 d]
    _ = ((negacyclicOrbit m hm d).card : ℝ) * |signedEndpointSummand g m r d| := by
        rw [abs_mul, Nat.abs_cast]
    _ = ∑ e ∈ negacyclicOrbit m hm d, |signedEndpointSummand g m r e| := by
        rw [Finset.sum_congr rfl (fun e he => by
          rw [signedEndpointSummand_eq_of_mem_negacyclicOrbit g m r hm hg hg0 d he])]
        simp

/-! ### 4. First-incidence transversals: definition, uniqueness, existence -/

/-- `T` is a **first-incidence transversal** of `S` for the negacyclic rotation action: it
selects one representative (the "first incidence") from each rotation orbit meeting `S`,
distinct representatives having pairwise disjoint orbits. -/
def IsOrbitTransversal (m : ℕ) (hm : 0 < m) (S T : Finset (Fin m → ℤ)) : Prop :=
  T ⊆ S ∧
    (∀ e ∈ S, ∃ t ∈ T, e ∈ negacyclicOrbit m hm t) ∧
    Set.PairwiseDisjoint (T : Set (Fin m → ℤ)) (fun t => negacyclicOrbit m hm t)

/-- The first-incidence representative of any point is UNIQUE: the transversal genuinely
counts each orbit once. -/
theorem transversal_rep_unique (m : ℕ) (hm : 0 < m) {S T : Finset (Fin m → ℤ)}
    (hT : IsOrbitTransversal m hm S T) {t₁ t₂ e : Fin m → ℤ}
    (ht₁ : t₁ ∈ T) (ht₂ : t₂ ∈ T)
    (he₁ : e ∈ negacyclicOrbit m hm t₁) (he₂ : e ∈ negacyclicOrbit m hm t₂) :
    t₁ = t₂ := by
  by_contra hne
  have hdis : Disjoint (negacyclicOrbit m hm t₁) (negacyclicOrbit m hm t₂) :=
    hT.2.2 (Finset.mem_coe.mpr ht₁) (Finset.mem_coe.mpr ht₂) hne
  exact (Finset.disjoint_left.mp hdis he₁) he₂

/-- Bounded-cardinality recursion for transversal existence: peel off one full orbit at a
time. -/
theorem exists_orbitTransversal_aux (m : ℕ) (hm : 0 < m) :
    ∀ N : ℕ, ∀ S : Finset (Fin m → ℤ), S.card ≤ N →
      ∃ T : Finset (Fin m → ℤ), IsOrbitTransversal m hm S T := by
  intro N
  induction N with
  | zero =>
      intro S hS
      have hempty : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hS)
      subst hempty
      refine ⟨∅, Finset.Subset.refl _, ?_, ?_⟩
      · intro e he
        exact absurd he (Finset.notMem_empty e)
      · intro a ha
        simp at ha
  | succ N ih =>
      intro S hS
      rcases Finset.eq_empty_or_nonempty S with rfl | ⟨d, hd⟩
      · refine ⟨∅, Finset.Subset.refl _, ?_, ?_⟩
        · intro e he
          exact absurd he (Finset.notMem_empty e)
        · intro a ha
          simp at ha
      · have hdself : d ∈ negacyclicOrbit m hm d := self_mem_negacyclicOrbit m hm d
        have hdnot : d ∉ S \ negacyclicOrbit m hm d := by
          simp [Finset.mem_sdiff, hdself]
        have hssub : S \ negacyclicOrbit m hm d ⊂ S :=
          (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr ⟨d, hd, hdnot⟩
        have hcard : (S \ negacyclicOrbit m hm d).card ≤ N := by
          have := Finset.card_lt_card hssub
          omega
        obtain ⟨T', hT'sub, hT'cov, hT'dis⟩ := ih (S \ negacyclicOrbit m hm d) hcard
        have hT'notin : ∀ t' ∈ T', t' ∉ negacyclicOrbit m hm d := fun t' ht' =>
          (Finset.mem_sdiff.mp (hT'sub ht')).2
        refine ⟨insert d T', ?_, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact hd
          · exact Finset.sdiff_subset (hT'sub hx')
        · intro e heS
          by_cases he : e ∈ negacyclicOrbit m hm d
          · exact ⟨d, Finset.mem_insert_self d T', he⟩
          · obtain ⟨t, ht, het⟩ := hT'cov e (Finset.mem_sdiff.mpr ⟨heS, he⟩)
            exact ⟨t, Finset.mem_insert_of_mem ht, het⟩
        · intro a ha b hb hab
          rw [Finset.coe_insert, Set.mem_insert_iff] at ha hb
          rcases ha with rfl | ha' <;> rcases hb with rfl | hb'
          · exact absurd rfl hab
          · exact (negacyclicOrbit_disjoint_of_not_mem m hm
              (hT'notin b (Finset.mem_coe.mp hb'))).symm
          · exact negacyclicOrbit_disjoint_of_not_mem m hm
              (hT'notin a (Finset.mem_coe.mp ha'))
          · exact hT'dis ha' hb' hab

/-- **Transversal existence**: every finite family admits a first-incidence transversal, so
the equivalence below is non-vacuous. -/
theorem exists_orbitTransversal (m : ℕ) (hm : 0 < m) (S : Finset (Fin m → ℤ)) :
    ∃ T : Finset (Fin m → ℤ), IsOrbitTransversal m hm S T :=
  exists_orbitTransversal_aux m hm S.card S le_rfl

/-! ### 5. The first-incidence functional and the exact compression identity -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The first-incidence cross-orbit functional of issue #505**: the signed doubled-walk
endpoint discrepancy summed over the FIRST incidence of each distinct rotation orbit only —
one representative `t` per orbit, weighted by its orbit size `|orbit(t)|`. -/
noncomputable def firstIncidenceDiscrepancy (g : F) (m r : ℕ) (hm : 0 < m)
    (T : Finset (Fin m → ℤ)) : ℝ :=
  ∑ t ∈ T, ((negacyclicOrbit m hm t).card : ℝ) * signedEndpointSummand g m r t

/-- The **unweighted** first-incidence sum: one raw signed summand per orbit. -/
noncomputable def rawFirstIncidence (g : F) (m r : ℕ) (T : Finset (Fin m → ℤ)) : ℝ :=
  ∑ t ∈ T, signedEndpointSummand g m r t

/-- A transversal's orbit blocks tile the whole signed difference family exactly. -/
theorem transversal_biUnion_eq (m r : ℕ) (hm : 0 < m) {T : Finset (Fin m → ℤ)}
    (hT : IsOrbitTransversal m hm (allShadowDifferences (2 * m) m r) T) :
    T.biUnion (fun t => negacyclicOrbit m hm t) = allShadowDifferences (2 * m) m r := by
  obtain ⟨hsub, hcov, hdis⟩ := hT
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.mp he
    exact negacyclicOrbit_subset_allShadowDifferences m r hm (hsub ht) het
  · intro e he
    obtain ⟨t, ht, het⟩ := hcov e he
    exact Finset.mem_biUnion.mpr ⟨t, ht, het⟩

/-- **The exact compression identity (sandwich constant = 1).**  For EVERY first-incidence
transversal, the cross-orbit functional equals the full signed pair discrepancy: orbit
constancy pays back exactly the orbit multiplicity that first-incidence restriction removes.
This is the two-sided sandwich `firstIncidence ≤ anomaly ≤ C · firstIncidence` collapsed to
an equality. -/
theorem firstIncidenceDiscrepancy_eq_signedShadowPairDiscrepancy
    (g : F) (m r : ℕ) (hm : 0 < m) (hg : g ^ m = -1) (hg0 : g ≠ 0)
    {T : Finset (Fin m → ℤ)}
    (hT : IsOrbitTransversal m hm (allShadowDifferences (2 * m) m r) T) :
    firstIncidenceDiscrepancy g m r hm T = signedShadowPairDiscrepancy g (2 * m) m r := by
  classical
  have hsum : signedShadowPairDiscrepancy g (2 * m) m r =
      ∑ d ∈ allShadowDifferences (2 * m) m r, signedEndpointSummand g m r d := by
    rw [signedShadowPairDiscrepancy_eq_sum_NR_double]
    unfold signedEndpointSummand
    rfl
  unfold firstIncidenceDiscrepancy
  rw [hsum, ← transversal_biUnion_eq m r hm hT, Finset.sum_biUnion hT.2.2]
  exact Finset.sum_congr rfl (fun t ht =>
    (sum_negacyclicOrbit_signedEndpointSummand g m r hm hg hg0 t).symm)

/-- **First incidence = centered relation anomaly, exactly** — the open object of the signed
route (R366/R367) is the first-incidence value verbatim. -/
theorem firstIncidenceDiscrepancy_eq_relationAnomaly
    (g : F) (m r : ℕ) (hm : 0 < m) (hg : g ^ m = -1) (hg0 : g ≠ 0)
    {T : Finset (Fin m → ℤ)}
    (hT : IsOrbitTransversal m hm (allShadowDifferences (2 * m) m r) T) :
    firstIncidenceDiscrepancy g m r hm T = relationAnomaly g (2 * m) m r := by
  rw [firstIncidenceDiscrepancy_eq_signedShadowPairDiscrepancy g m r hm hg hg0 hT,
    signedShadowPairDiscrepancy_eq_relationAnomaly]

/-- The first-incidence value does not depend on which transversal realizes it: there is no
"lucky choice" of first incidences. -/
theorem firstIncidenceDiscrepancy_transversal_independent
    (g : F) (m r : ℕ) (hm : 0 < m) (hg : g ^ m = -1) (hg0 : g ≠ 0)
    {T₁ T₂ : Finset (Fin m → ℤ)}
    (hT₁ : IsOrbitTransversal m hm (allShadowDifferences (2 * m) m r) T₁)
    (hT₂ : IsOrbitTransversal m hm (allShadowDifferences (2 * m) m r) T₂) :
    firstIncidenceDiscrepancy g m r hm T₁ = firstIncidenceDiscrepancy g m r hm T₂ := by
  rw [firstIncidenceDiscrepancy_eq_relationAnomaly g m r hm hg hg0 hT₁,
    firstIncidenceDiscrepancy_eq_relationAnomaly g m r hm hg hg0 hT₂]

/-! ### 6. Headline: the first-incidence bound is the wall — no weaker sufficient condition -/

/-- **Threshold identity.**  For every transversal and EVERY threshold `W`, the
first-incidence bound and the anomaly bound are the same inequality: the sets of sufficient
thresholds coincide EXACTLY, so no strictly weaker sufficient condition for the anomaly
budget can be phrased through the first-incidence functional. -/
theorem firstIncidence_le_iff_relationAnomaly_le
    (g : F) (m r : ℕ) (hm : 0 < m) (hg : g ^ m = -1) (hg0 : g ≠ 0)
    {T : Finset (Fin m → ℤ)}
    (hT : IsOrbitTransversal m hm (allShadowDifferences (2 * m) m r) T) (W : ℝ) :
    firstIncidenceDiscrepancy g m r hm T ≤ W ↔ relationAnomaly g (2 * m) m r ≤ W := by
  rw [firstIncidenceDiscrepancy_eq_relationAnomaly g m r hm hg hg0 hT]

/-- **HEADLINE (`firstIncidence_bound_iff_wall`).**  At the prize shape (`orderOf g = n = 2m`,
`g^m = −1`), for every first-incidence transversal of the signed difference family, the
first-incidence cross-orbit bound at the Wick budget is EQUIVALENT to `DCEnergyBound` on the
power-root set — the production BGK/Paley-wall-scale statement.  The remaining single-embedding
first-incidence cross-orbit formulation of the signed relation route is quantitatively
IDENTICAL to the wall; it admits no weaker sufficient condition. -/
theorem firstIncidence_bound_iff_wall
    (g : F) (n m r : ℕ)
    (hg0 : g ≠ 0) (hord : orderOf g = n) (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1)
    {T : Finset (Fin m → ℤ)}
    (hT : IsOrbitTransversal m hm (allShadowDifferences n m r) T) :
    firstIncidenceDiscrepancy g m r hm T ≤
        relationAnomalyBudget (F := F) n m r
          ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (n : ℝ) ^ r) ↔
      DCEnergyBound (powerRootSet g n) r := by
  subst hn
  rw [firstIncidenceDiscrepancy_eq_relationAnomaly g m r hm hg hg0 hT]
  exact relationAnomaly_le_wickBudget_iff_dcEnergyBound g (2 * m) m r hg0 hord hm rfl hg

/-- Non-vacuous form of the headline: a transversal exists and realizes the equivalence. -/
theorem exists_transversal_wall_equiv
    (g : F) (n m r : ℕ)
    (hg0 : g ≠ 0) (hord : orderOf g = n) (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    ∃ T : Finset (Fin m → ℤ),
      IsOrbitTransversal m hm (allShadowDifferences n m r) T ∧
        (firstIncidenceDiscrepancy g m r hm T ≤
            relationAnomalyBudget (F := F) n m r
              ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (n : ℝ) ^ r) ↔
          DCEnergyBound (powerRootSet g n) r) := by
  obtain ⟨T, hT⟩ := exists_orbitTransversal m hm (allShadowDifferences n m r)
  exact ⟨T, hT, firstIncidence_bound_iff_wall g n m r hg0 hord hm hn hg hT⟩

/-- **The first-incidence value IS the Fourier wall object**: chained through G77's gauge,
the first-incidence cross-orbit functional equals the DC-subtracted `2r`-th moment of the
Gauss periods minus the characteristic-zero floor — the literal BGK/Paley face. -/
theorem firstIncidence_eq_dcMoment_sub_floor
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (g : F) (n m r : ℕ)
    (hg0 : g ≠ 0) (hord : orderOf g = n) (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1)
    {T : Finset (Fin m → ℤ)}
    (hT : IsOrbitTransversal m hm (allShadowDifferences n m r) T) :
    firstIncidenceDiscrepancy g m r hm T =
      (∑ b ∈ univ.erase (0 : F), ‖eta ψ (powerRootSet g n) b‖ ^ (2 * r)) -
        ((Fintype.card F : ℝ) - 1) * (shadowEnergy n m r : ℝ) := by
  subst hn
  rw [firstIncidenceDiscrepancy_eq_relationAnomaly g m r hm hg hg0 hT]
  exact relationAnomaly_eq_dcMoment_sub_floor hψ g (2 * m) m r hg0 hord hm rfl hg

/-! ### 7. The unweighted variant: dropping the weights rescales the wall exactly -/

/-- **Exact rescaling of the unweighted first-incidence sum.**  If the orbits through a
transversal share one size `c` (uniform orbit size), the full anomaly is EXACTLY `c` times the
raw (unweighted) first-incidence sum — the sandwich constant is precisely the orbit size, as
predicted by orbit rigidity (R382 + orbit constancy), with zero analytic slack. -/
theorem relationAnomaly_eq_orbitSize_mul_rawFirstIncidence
    (g : F) (m r : ℕ) (hm : 0 < m) (hg : g ^ m = -1) (hg0 : g ≠ 0)
    {T : Finset (Fin m → ℤ)}
    (hT : IsOrbitTransversal m hm (allShadowDifferences (2 * m) m r) T)
    (c : ℕ) (hc : ∀ t ∈ T, (negacyclicOrbit m hm t).card = c) :
    relationAnomaly g (2 * m) m r = (c : ℝ) * rawFirstIncidence g m r T := by
  rw [← firstIncidenceDiscrepancy_eq_relationAnomaly g m r hm hg hg0 hT]
  unfold firstIncidenceDiscrepancy rawFirstIncidence
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun t ht => by rw [hc t ht])

/-- The unweighted first-incidence bound is the wall bound rescaled by exactly the orbit
size: even discarding the orbit weights yields no weaker sufficient condition, only the same
condition at a known exact scale. -/
theorem rawFirstIncidence_le_iff_wall_scaled
    (g : F) (m r : ℕ) (hm : 0 < m) (hg : g ^ m = -1) (hg0 : g ≠ 0)
    {T : Finset (Fin m → ℤ)}
    (hT : IsOrbitTransversal m hm (allShadowDifferences (2 * m) m r) T)
    (c : ℕ) (hc : ∀ t ∈ T, (negacyclicOrbit m hm t).card = c) (hcpos : 0 < c) (W : ℝ) :
    rawFirstIncidence g m r T ≤ W ↔
      relationAnomaly g (2 * m) m r ≤ (c : ℝ) * W := by
  rw [relationAnomaly_eq_orbitSize_mul_rawFirstIncidence g m r hm hg hg0 hT c hc]
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hcpos
  constructor
  · intro h
    exact mul_le_mul_of_nonneg_left h (le_of_lt hcR)
  · intro h
    exact le_of_mul_le_mul_left h hcR

end ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
set_option linter.style.longLine false
#print axioms
  ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence.iterate_rotZ_m
#print axioms
  ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence.iterate_rotZ_two_m
#print axioms
  ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence.negacyclicOrbit_eq_of_mem
#print axioms
  ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence.negacyclicOrbit_disjoint_of_not_mem
#print axioms
  ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence.negacyclicOrbit_subset_allShadowDifferences
#print axioms
  ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence.signedEndpointSummand_eq_of_mem_negacyclicOrbit
#print axioms
  ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence.abs_sum_negacyclicOrbit_eq_sum_abs
#print axioms
  ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence.transversal_rep_unique
#print axioms
  ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence.exists_orbitTransversal
#print axioms
  ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence.firstIncidenceDiscrepancy_eq_signedShadowPairDiscrepancy
#print axioms
  ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence.firstIncidenceDiscrepancy_eq_relationAnomaly
#print axioms
  ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence.firstIncidenceDiscrepancy_transversal_independent
#print axioms
  ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence.firstIncidence_le_iff_relationAnomaly_le
#print axioms
  ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence.firstIncidence_bound_iff_wall
#print axioms
  ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence.exists_transversal_wall_equiv
#print axioms
  ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence.firstIncidence_eq_dcMoment_sub_floor
#print axioms
  ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence.relationAnomaly_eq_orbitSize_mul_rawFirstIncidence
#print axioms
  ArkLib.ProximityGap.Frontier.G89FirstIncidenceWallEquivalence.rawFirstIncidence_le_iff_wall_scaled
