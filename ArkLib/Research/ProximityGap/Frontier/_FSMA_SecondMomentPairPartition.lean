/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._ConstantWeightPlotkinBound
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorSecantLines
import ArkLib.Research.ProximityGap.Frontier._P1RateQuarterForcedSecantMatching

/-!
# P1 rate-quarter predecessor: second-moment core caps for the pair partition

Second-moment / convexity attack on the pair-partition identity
`sum over lines of L*(L-1) = |G|*(|G|-1)` at the P1 predecessor parameters
`N = 2^30`, `K = 2^28`, `T = 592794966`.

## Landed rungs (all axiom-clean)

* **Generic shrink-and-Plotkin impossibility** (`no_large_pairwise_family`):
  a family of `m` subsets of a finite universe, each of size at least `t` and
  pairwise intersecting in at most `lambda`, is impossible whenever
  `|U|*(t-lambda) < m*(t^2 - |U|*lambda)`.

* **Five-core ceiling at the floor `587673607`**
  (`six_cores_at_floor_impossible`): six subsets of `Fin N` of size at least
  `fivePencilCoreFloor = 587673607`, pairwise intersecting in at most `K-1`,
  are impossible.  Exact margin:
  `N*(587673607-(K-1)) = 342779355618869248 <
   6*(587673607^2 - N*(K-1)) = 342779359718523174`.
  The threshold is sharp for this route: at `587673606` the Plotkin
  inequality is satisfiable (`six_cores_floor_pred_plotkin_satisfiable`).
  Since `587673607 <= T - 2 = 592794964`
  (`fivePencilCoreFloor_le_saturated`), this cap covers all saturated and
  near-saturated cores, `5121357` coordinates below saturation.

* **Supersaturated ladder** (`five_cores_impossible_at_599424501`,
  `four_cores_impossible_at_618146628`, `three_cores_impossible_at_652432610`,
  `two_cores_impossible_at_733379304`): at most `4/3/2/1` pairwise-`(K-1)`
  subsets of size at least `599424501 / 618146628 / 652432610 / 733379304`.
  All four thresholds are exact *for the Plotkin route* (the Plotkin inequality flips one
  below); they are not the true extremal thresholds.  For two and three cores the elementary
  inclusion-exclusion (Bonferroni) bound is strictly stronger
  (`two_cores_impossible_at_671088640`, `three_cores_impossible_at_626349397`):
  `2t-(K-1) > N` forbids two cores once `t >= 671088640 < 733379304`, and
  `3t-3(K-1) > N` forbids three cores once `t >= 626349397 < 652432610`.  Note the
  count drops to *four* exactly at core size `T + 6629535`: the first
  Plotkin-visible shadow of the conjectured four-pencil structure sits just
  above the agreement threshold.

* **Line-level cap** (`lines_with_core_ge_floor_card_le_five`): at most `5`
  pairwise-distinct polynomial lines `(a,r)` with components of degree `< K`
  have joint cores of size at least `fivePencilCoreFloor`.  Uses the
  distinct-line core rigidity (`line_core_inter_card_le_of_ne`, delegating to
  `P1RateQuarterForcedSecantMatching.jointCore_inter_card_le_of_ne`): distinct degree-`< K` lines
  share at most
  `K-1` core coordinates.

* **Big-line dichotomy** (`bigLine_core_ge_floor`, `bigLines_card_le_five`):
  in any `BadScalarRichPointFamily` at threshold at least `T`, every relevant
  secant line carrying at least `95` selected points has core at least
  `fivePencilCoreFloor` (exact fresh-fibre packing:
  `95*(T-z) + z <= N` forces `z >= 587678511`), hence **at most five lines
  carry `95` or more points; every other line carries at most `94`.**

* **Mega-line saturation** (`megaLine_core_ge_T_sub_one`,
  `megaLines_card_le_five`): every line with at least `240473431` points has
  core at least `T - 1` — strictly above the safe-pencil ceiling `T - 2` of
  the four-pencil extraction — and at most five such lines exist.

* **Saturated-pencil count** (`saturatedCoreLines_card_le_five`): at most
  five relevant lines have core at least `T - 2`.

## Honest barrier (machine-checked window certificates)

The pair-partition identity alone cannot force `|G| <= N`: the identity is
self-satisfiable by two-point lines (every pair its own secant), so any
counting argument must inject geometric input beyond pair mass.
Quantitatively, even the five-line cap leaves the mega-line channel open:

* `fiveCap_pair_mass_window_open`:
  `(N+1)*N = 1152921505680588800 < 5*(N-T+1)*(N-T) = 1156549403505095110` —
  five maximal lines could carry the entire required pair mass
  (ratio `1.00315`).
* `fourCap_pair_mass_window_closed`:
  `4*(N-T+1)*(N-T) = 925239522804076088 < (N+1)*N` — a four-line cap would
  close that channel (though small lines would still self-satisfy the
  identity).

So this angle lands the five-cap ladder as unconditional structure but
cannot, by itself, settle `CanonicalUniformPredecessorBadCount`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

open Finset Polynomial
open _root_.ProximityGap Code

namespace ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition

open ConstantWeightPlotkinBound
open HalfPredecessorBadEventRichPointBridge
open HalfPredecessorLineCoreGeometry
open HalfPredecessorSecantLines

attribute [local instance] Classical.propDecidable

/-- Prize length. -/
abbrev N : Nat := 2 ^ 30

/-- Rate-quarter Reed--Solomon dimension. -/
abbrev K : Nat := 2 ^ 28

/-- Agreement threshold at the lattice predecessor of the saturated
common-factor endpoint. -/
abbrev T : Nat := 592794966

/-- The least core size at which the constant-weight Plotkin bound already
forbids six pairwise-`(K-1)`-overlapping cores inside `Fin N`.  Sharp for the
Plotkin route: at `587673606` the inequality is satisfiable. -/
abbrev fivePencilCoreFloor : Nat := 587673607

/-- The five-pencil core floor sits `5121357` coordinates *below* the
saturated two-fresh core size `T - 2`. -/
theorem fivePencilCoreFloor_le_saturated : fivePencilCoreFloor ≤ T - 2 := by
  norm_num [fivePencilCoreFloor, T]

instance moduleInstance_FSMA_SecondMomentPairPartition_1 : Nonempty (Fin N) := ⟨⟨0, by norm_num [N]⟩⟩

/-! ## Generic shrink-and-Plotkin impossibility -/

/-- **Shrink-and-Plotkin impossibility.**  A family of `m` subsets of a
finite universe `U`, each of size at least `t`, pairwise intersecting in at
most `lambda`, cannot exist once `|U|*(t-lambda) < m*(t^2 - |U|*lambda)`.
Each set is shrunk to size exactly `t` (intersections only shrink) and the
constant-weight Plotkin bound is applied. -/
theorem no_large_pairwise_family {U : Type} [Fintype U] [DecidableEq U]
    {m t lambda : ℕ} (A : Fin m → Finset U)
    (hsize : ∀ i, t ≤ (A i).card)
    (hpair : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ lambda)
    (harith : Fintype.card U * (t - lambda) <
      m * (t ^ 2 - Fintype.card U * lambda)) : False := by
  classical
  let A' : Fin m → Finset U := fun i =>
    Classical.choose (Finset.exists_subset_card_eq (hsize i))
  have hA'sub : ∀ i, A' i ⊆ A i := fun i =>
    (Classical.choose_spec (Finset.exists_subset_card_eq (hsize i))).1
  have hA'card : ∀ i, (A' i).card = t := fun i =>
    (Classical.choose_spec (Finset.exists_subset_card_eq (hsize i))).2
  have hpair' : ∀ i j, i ≠ j → (A' i ∩ A' j).card ≤ lambda := by
    intro i j hij
    exact le_trans
      (Finset.card_le_card (Finset.inter_subset_inter (hA'sub i) (hA'sub j)))
      (hpair i j hij)
  have hplot := constantWeight_plotkin A' t lambda hA'card hpair'
  rw [Fintype.card_fin] at hplot
  exact absurd hplot (Nat.not_le.mpr harith)

/-! ## The five-core ceiling at the floor, and the supersaturated ladder -/

/-- **Six cores at the floor are impossible.**  Six subsets of the P1
coordinate set, each of size at least `fivePencilCoreFloor = 587673607`,
pairwise intersecting in at most `K - 1`, cannot exist. -/
theorem six_cores_at_floor_impossible
    (A : Fin 6 → Finset (Fin N))
    (hsize : ∀ i, fivePencilCoreFloor ≤ (A i).card)
    (hpair : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ K - 1) : False := by
  refine no_large_pairwise_family A hsize hpair ?_
  rw [Fintype.card_fin]
  norm_num [N, K, fivePencilCoreFloor]

/-- Sharpness of the floor for the Plotkin route: one coordinate below the
floor the constant-weight Plotkin inequality for six sets is satisfiable. -/
theorem six_cores_floor_pred_plotkin_satisfiable :
    6 * ((fivePencilCoreFloor - 1) ^ 2 - N * (K - 1)) ≤
      N * ((fivePencilCoreFloor - 1) - (K - 1)) := by
  norm_num [N, K, fivePencilCoreFloor]

/-- At most four pairwise-`(K-1)` cores of size at least `599424501`
(`= T + 6629535`; least threshold for the Plotkin route). -/
theorem five_cores_impossible_at_599424501
    (A : Fin 5 → Finset (Fin N))
    (hsize : ∀ i, 599424501 ≤ (A i).card)
    (hpair : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ K - 1) : False := by
  refine no_large_pairwise_family A hsize hpair ?_
  rw [Fintype.card_fin]
  norm_num [N, K]

/-- At most three pairwise-`(K-1)` cores of size at least `618146628`
(least threshold for the Plotkin route). -/
theorem four_cores_impossible_at_618146628
    (A : Fin 4 → Finset (Fin N))
    (hsize : ∀ i, 618146628 ≤ (A i).card)
    (hpair : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ K - 1) : False := by
  refine no_large_pairwise_family A hsize hpair ?_
  rw [Fintype.card_fin]
  norm_num [N, K]

/-- At most two pairwise-`(K-1)` cores of size at least `652432610`
(least threshold for the Plotkin route only; superseded by the inclusion-exclusion cap
`three_cores_impossible_at_626349397`). -/
theorem three_cores_impossible_at_652432610
    (A : Fin 3 → Finset (Fin N))
    (hsize : ∀ i, 652432610 ≤ (A i).card)
    (hpair : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ K - 1) : False := by
  refine no_large_pairwise_family A hsize hpair ?_
  rw [Fintype.card_fin]
  norm_num [N, K]

/-- At most one core of size at least `733379304` in any pairwise-`(K-1)`
family (least threshold for the Plotkin route only; superseded by the inclusion-exclusion cap
`two_cores_impossible_at_671088640`). -/
theorem two_cores_impossible_at_733379304
    (A : Fin 2 → Finset (Fin N))
    (hsize : ∀ i, 733379304 ≤ (A i).card)
    (hpair : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ K - 1) : False := by
  refine no_large_pairwise_family A hsize hpair ?_
  rw [Fintype.card_fin]
  norm_num [N, K]

/-- **Inclusion-exclusion two-core cap** (stronger than the Plotkin route): two subsets of
`Fin N` of size at least `671088640` meeting in at most `K - 1` points would need
`2*671088640 - (K-1) = N + 1 > N` coordinates. -/
theorem two_cores_impossible_at_671088640
    (A : Fin 2 → Finset (Fin N))
    (hsize : ∀ i, 671088640 ≤ (A i).card)
    (hpair : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ K - 1) : False := by
  have h1 := Finset.card_union_add_card_inter (A 0) (A 1)
  have h2 : (A 0 ∪ A 1).card ≤ N := by
    simpa using Finset.card_le_univ (A 0 ∪ A 1)
  have h3 := hpair 0 1 (by decide)
  have h4 := hsize 0
  have h5 := hsize 1
  norm_num [N, K] at h2 h3
  omega

/-- **Inclusion-exclusion three-core cap** (stronger than the Plotkin route): three subsets of
`Fin N` of size at least `626349397`, pairwise meeting in at most `K - 1` points, would need
`3*626349397 - 3*(K-1) > N` coordinates (Bonferroni). -/
theorem three_cores_impossible_at_626349397
    (A : Fin 3 → Finset (Fin N))
    (hsize : ∀ i, 626349397 ≤ (A i).card)
    (hpair : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ K - 1) : False := by
  have h1 := Finset.card_union_add_card_inter (A 0) (A 1)
  have h2 := Finset.card_union_add_card_inter (A 0 ∪ A 1) (A 2)
  have h3 : ((A 0 ∪ A 1) ∩ A 2).card ≤ (A 0 ∩ A 2).card + (A 1 ∩ A 2).card := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_le _ _
  have hU : (A 0 ∪ A 1 ∪ A 2).card ≤ N := by
    simpa using Finset.card_le_univ (A 0 ∪ A 1 ∪ A 2)
  have p01 := hpair 0 1 (by decide)
  have p02 := hpair 0 2 (by decide)
  have p12 := hpair 1 2 (by decide)
  have s0 := hsize 0
  have s1 := hsize 1
  have s2 := hsize 2
  norm_num [N, K] at hU p01 p02 p12
  omega

/-! ## Distinct-line core rigidity

The canonical statement is `P1RateQuarterForcedSecantMatching.jointCore_inter_card_le_of_ne`;
the local name below is kept as a one-line delegation. -/

section Rigidity

variable {ι F : Type} [Fintype ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- **Distinct-line core cap.**  Two polynomial lines that differ in
intercept or slope, with all components of degree `< k`, have joint cores
meeting in at most `k - 1` coordinates. -/
theorem line_core_inter_card_le_of_ne
    (dom : ι ↪ F) (u₀ u₁ : ι → F) {k : ℕ} (hk : 1 ≤ k)
    {a r a' r' : F[X]}
    (hadeg : a.natDegree < k) (hrdeg : r.natDegree < k)
    (hadeg' : a'.natDegree < k) (hrdeg' : r'.natDegree < k)
    (hne : a ≠ a' ∨ r ≠ r') :
    (jointCore dom u₀ u₁ a r ∩ jointCore dom u₀ u₁ a' r').card ≤ k - 1 :=
  P1RateQuarterForcedSecantMatching.jointCore_inter_card_le_of_ne dom u₀ u₁ hk
    hadeg hrdeg hadeg' hrdeg' hne


end Rigidity

/-! ## At most five distinct high-core lines -/

/-- **Line-level five-cap.**  Any finite set of pairwise-distinct polynomial
lines over the P1 domain, with components of degree `< K` and joint cores of
size at least `fivePencilCoreFloor`, has at most five members. -/
theorem lines_with_core_ge_floor_card_le_five
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (S : Finset (F[X] × F[X]))
    (hdeg : ∀ p ∈ S, p.1.natDegree < K ∧ p.2.natDegree < K)
    (hcore : ∀ p ∈ S,
      fivePencilCoreFloor ≤ (jointCore dom u₀ u₁ p.1 p.2).card) :
    S.card ≤ 5 := by
  by_contra hcard
  have hsix : 6 ≤ S.card := by omega
  obtain ⟨S6, hS6sub, hS6card⟩ := Finset.exists_subset_card_eq hsix
  have he : S6 ≃ Fin 6 := by
    rw [← hS6card]
    exact S6.equivFin
  let label : Fin 6 → F[X] × F[X] := fun i => (he.symm i : F[X] × F[X])
  have hinj : Function.Injective label := by
    intro i j hij
    apply he.symm.injective
    exact Subtype.ext hij
  have hlabelS : ∀ i, label i ∈ S := fun i => hS6sub (he.symm i).2
  refine six_cores_at_floor_impossible
    (fun i => jointCore dom u₀ u₁ (label i).1 (label i).2)
    (fun i => hcore _ (hlabelS i)) ?_
  intro i j hij
  have hne : label i ≠ label j := hinj.ne hij
  have hcomp : (label i).1 ≠ (label j).1 ∨ (label i).2 ≠ (label j).2 := by
    by_contra hboth
    push Not at hboth
    exact hne (Prod.ext hboth.1 hboth.2)
  have hK : 1 ≤ K := by norm_num [K]
  exact line_core_inter_card_le_of_ne dom u₀ u₁ hK
    (hdeg _ (hlabelS i)).1 (hdeg _ (hlabelS i)).2
    (hdeg _ (hlabelS j)).1 (hdeg _ (hlabelS j)).2 hcomp

/-! ## Exact fresh-fibre core forcing -/

/-- **Big-line core forcing (arithmetic).**  At threshold `T` in `N`
coordinates, a line carrying at least `95` points has core at least
`fivePencilCoreFloor`.  Exact: `95*(T-z) + z <= N` gives
`94*z >= 95*T - N = 55241779946`, i.e. `z >= 587678511 > 587673607`. -/
theorem core_lower_of_bigLine {L z : ℕ} (hL : 95 ≤ L)
    (hpack : L * max 1 (T - z) + z ≤ N) : fivePencilCoreFloor ≤ z := by
  have hT : T = 592794966 := rfl
  have hN : N = 1073741824 := by norm_num [N]
  have hF : fivePencilCoreFloor = 587673607 := rfl
  by_cases hz : T ≤ z
  · omega
  · push Not at hz
    have h1 : 1 ≤ T - z := by omega
    rw [max_eq_right h1] at hpack
    have h95 : 95 * (T - z) ≤ L * (T - z) := Nat.mul_le_mul_right _ hL
    have h2 : 95 * (T - z) + z ≤ N :=
      le_trans (Nat.add_le_add_right h95 z) hpack
    omega

/-- **Mega-line core forcing (arithmetic).**  A line carrying at least
`240473431` points has core at least `T - 1` — strictly above the safe-pencil
ceiling `T - 2` of the four-pencil extraction. -/
theorem core_ge_T_sub_one_of_megaLine {L z : ℕ} (hL : 240473431 ≤ L)
    (hpack : L * max 1 (T - z) + z ≤ N) : T - 1 ≤ z := by
  have hT : T = 592794966 := rfl
  have hN : N = 1073741824 := by norm_num [N]
  by_cases hz : T ≤ z
  · omega
  · push Not at hz
    have h1 : 1 ≤ T - z := by omega
    rw [max_eq_right h1] at hpack
    have hmul : 240473431 * (T - z) ≤ L * (T - z) :=
      Nat.mul_le_mul_right _ hL
    have h2 : 240473431 * (T - z) + z ≤ N :=
      le_trans (Nat.add_le_add_right hmul z) hpack
    omega

/-! ## Family-level dichotomy at the P1 predecessor -/

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Every relevant secant line of a P1-predecessor family carrying at least
`95` selected points has joint core at least `fivePencilCoreFloor`. -/
theorem bigLine_core_ge_floor
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hthr : T ≤ ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hbig : 95 ≤ (pointsOn family line).card) :
    fivePencilCoreFloor ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card := by
  have hpack := pointsOn_card_mul_max_add_core_le family hline
  set z := (jointCore dom (u 0) (u 1) line.1 line.2).card with hzdef
  set L := (pointsOn family line).card with hLdef
  have hmono : max 1 (T - z) ≤
      max 1 (⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊ - z) :=
    max_le_max le_rfl (Nat.sub_le_sub_right hthr z)
  have hpack' : L * max 1 (T - z) + z ≤ N := by
    have h1 : L * max 1 (T - z) ≤
        L * max 1 (⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊ - z) :=
      Nat.mul_le_mul_left L hmono
    have h2 := le_trans (Nat.add_le_add_right h1 z) hpack
    simpa only [Fintype.card_fin] using h2
  exact core_lower_of_bigLine hbig hpack'

/-- Every relevant secant line carrying at least `240473431` selected points
has joint core at least `T - 1`: mega lines are necessarily unsafe pencils. -/
theorem megaLine_core_ge_T_sub_one
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hthr : T ≤ ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hbig : 240473431 ≤ (pointsOn family line).card) :
    T - 1 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card := by
  have hpack := pointsOn_card_mul_max_add_core_le family hline
  set z := (jointCore dom (u 0) (u 1) line.1 line.2).card with hzdef
  set L := (pointsOn family line).card with hLdef
  have hmono : max 1 (T - z) ≤
      max 1 (⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊ - z) :=
    max_le_max le_rfl (Nat.sub_le_sub_right hthr z)
  have hpack' : L * max 1 (T - z) + z ≤ N := by
    have h1 : L * max 1 (T - z) ≤
        L * max 1 (⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊ - z) :=
      Nat.mul_le_mul_left L hmono
    have h2 := le_trans (Nat.add_le_add_right h1 z) hpack
    simpa only [Fintype.card_fin] using h2
  exact core_ge_T_sub_one_of_megaLine hbig hpack'

/-- **Big-line five-cap.**  At most five relevant secant lines of a
P1-predecessor family carry `95` or more selected points; every other line
carries at most `94`. -/
theorem bigLines_card_le_five
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hthr : T ≤ ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊) :
    ((lineParameters family).filter
      (fun line => 95 ≤ (pointsOn family line).card)).card ≤ 5 := by
  refine lines_with_core_ge_floor_card_le_five dom (u 0) (u 1) _ ?_ ?_
  · intro p hp
    exact lineParameter_degree_lt family (Finset.mem_filter.mp hp).1
  · intro p hp
    have hm := Finset.mem_filter.mp hp
    exact bigLine_core_ge_floor family hthr hm.1 hm.2

/-- **Mega-line five-cap.**  At most five relevant secant lines carry
`240473431` or more selected points. -/
theorem megaLines_card_le_five
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hthr : T ≤ ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊) :
    ((lineParameters family).filter
      (fun line => 240473431 ≤ (pointsOn family line).card)).card ≤ 5 := by
  have hsub : (lineParameters family).filter
      (fun line => 240473431 ≤ (pointsOn family line).card) ⊆
      (lineParameters family).filter
      (fun line => 95 ≤ (pointsOn family line).card) := by
    intro line hline
    rw [Finset.mem_filter] at hline ⊢
    exact ⟨hline.1, le_trans (by norm_num) hline.2⟩
  exact le_trans (Finset.card_le_card hsub) (bigLines_card_le_five family hthr)

/-- **Saturated-pencil five-cap.**  At most five relevant secant lines of a
P1-predecessor family have joint core at least `T - 2`. -/
theorem saturatedCoreLines_card_le_five
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u) :
    ((lineParameters family).filter
      (fun line => T - 2 ≤
        (jointCore dom (u 0) (u 1) line.1 line.2).card)).card ≤ 5 := by
  refine lines_with_core_ge_floor_card_le_five dom (u 0) (u 1) _ ?_ ?_
  · intro p hp
    exact lineParameter_degree_lt family (Finset.mem_filter.mp hp).1
  · intro p hp
    exact le_trans fivePencilCoreFloor_le_saturated (Finset.mem_filter.mp hp).2

/-! ## Pair-mass window certificates (honest barrier)

The pair-partition identity is self-satisfiable by two-point lines, so pair
mass alone can never contradict `N < |G|`.  These certificates quantify the
remaining window for the mega-line channel specifically. -/

/-- Five maximal lines (each with `N - T + 1 = 480946859` points) can carry
more ordered pair mass than an over-budget family requires: the five-cap does
*not* close the pair-partition route.  Ratio `1.00315`. -/
theorem fiveCap_pair_mass_window_open :
    (N + 1) * N < 5 * ((N - T + 1) * (N - T)) := by
  norm_num [N, T]

/-- Four maximal lines fall short of the required pair mass: a four-line cap
would close the mega-line channel of the pair-partition identity. -/
theorem fourCap_pair_mass_window_closed :
    4 * ((N - T + 1) * (N - T)) < (N + 1) * N := by
  norm_num [N, T]

end ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition.no_large_pairwise_family
#print axioms
  ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition.six_cores_at_floor_impossible
#print axioms
  ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition.six_cores_floor_pred_plotkin_satisfiable
#print axioms
  ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition.five_cores_impossible_at_599424501
#print axioms
  ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition.four_cores_impossible_at_618146628
#print axioms
  ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition.three_cores_impossible_at_652432610
#print axioms
  ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition.two_cores_impossible_at_733379304
#print axioms
  ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition.line_core_inter_card_le_of_ne
#print axioms
  ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition.lines_with_core_ge_floor_card_le_five
#print axioms
  ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition.core_lower_of_bigLine
#print axioms
  ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition.core_ge_T_sub_one_of_megaLine
#print axioms
  ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition.bigLine_core_ge_floor
#print axioms
  ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition.megaLine_core_ge_T_sub_one
#print axioms
  ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition.bigLines_card_le_five
#print axioms
  ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition.megaLines_card_le_five
#print axioms
  ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition.saturatedCoreLines_card_le_five
#print axioms
  ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition.fiveCap_pair_mass_window_open
#print axioms
  ArkLib.ProximityGap.Frontier.FSMASecondMomentPairPartition.fourCap_pair_mass_window_closed
