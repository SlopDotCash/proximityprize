/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorSecantLines
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCommonFactorArithmetic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RateQuarterPredecessorFourClusterCapacity
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount

/-!
# P1 rate-quarter predecessor: reduction to four two-fresh pencils

For a bad-scalar rich-point family, a source pencil is a polynomial line
`q_gamma = a + gamma r`.  Its joint core is contained in every agreement set
on the pencil, and the fresh agreement petals of distinct scalars are
disjoint.  Consequently a cover by at most four source pencils whose cores
leave two coordinates before the agreement threshold is enough for the exact
packing inequality.

This file proves that handoff, including the exact P1 predecessor arithmetic.
It deliberately does **not** assert that an arbitrary bad family has such a
cover.  The original saturated extraction target asked for:

* partition the selected lifted points among four polynomial lines;
* every assigned point lies on its line; and
* every one of the four (possibly repeated, for padding) line cores contains
  exactly `592794964` coordinates (equivalently, it has at least that many
  coordinates and leaves two coordinates before the threshold
  `592794966`).

The exact packing inequality in fact needs no saturated lower bound on those
four cores: the two-fresh condition alone closes the P1 arithmetic and gives
the bad-scalar count `N = 2^30`.  Thus the relaxed incidence target keeps only
the first two bullets and the upper-core condition `core.card + 2 <= 592794966`.
The API below records this by setting the existing `coreCard` parameter to
zero while preserving the original saturated API.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped BigOperators NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.RateQuarterPredecessorFourClusterCapacity

namespace ArkLib.ProximityGap.Frontier.RateQuarterPredecessorFourPencilReduction

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- A padded cover of a rich-point family by four saturated polynomial
pencils.  Repeating a source line permits covers by fewer than four lines.

The two numerical fields are kept explicit.  `coreCard` is the saturation
condition supplied by the global extraction argument, while `twoFresh` is
the one-lattice-step gain at the predecessor threshold. -/
structure FourSaturatedPencilCover
    {dom : I ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (t z : Nat) where
  /-- Cluster assignment for selected scalar points. -/
  cluster : F → Fin 4
  /-- The polynomial source line of each cluster. -/
  source : Fin 4 → LineParameter F
  /-- Every selected lifted point lies on its assigned source line. -/
  mem_source : ∀ gamma ∈ family.G,
    gamma ∈ pointsOn family (source (cluster gamma))
  /-- Every (padded) source core is saturated. -/
  coreCard : ∀ i, z ≤
    (jointCore dom (u 0) (u 1) (source i).1 (source i).2).card
  /-- The predecessor threshold leaves at least two fresh coordinates. -/
  twoFresh : ∀ i,
    (jointCore dom (u 0) (u 1) (source i).1 (source i).2).card + 2 ≤ t

/-- The selected scalars assigned to one of the four source pencils. -/
noncomputable def clusterScalars
    {dom : I ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    {family : BadScalarRichPointFamily dom k delta u} {t z : Nat}
    (cover : FourSaturatedPencilCover family t z) (i : Fin 4) : Finset F :=
  family.G.filter fun gamma ↦ cover.cluster gamma = i

@[simp]
theorem mem_clusterScalars_iff
    {dom : I ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    {family : BadScalarRichPointFamily dom k delta u} {t z : Nat}
    (cover : FourSaturatedPencilCover family t z) (i : Fin 4) (gamma : F) :
    gamma ∈ clusterScalars cover i ↔
      gamma ∈ family.G ∧ cover.cluster gamma = i := by
  simp only [clusterScalars, Finset.mem_filter]

/-- The four cluster fibres form an exact partition of the selected scalar
set. -/
theorem sum_clusterScalars_card
    {dom : I ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    {family : BadScalarRichPointFamily dom k delta u} {t z : Nat}
    (cover : FourSaturatedPencilCover family t z) :
    (∑ i : Fin 4, (clusterScalars cover i).card) = family.G.card := by
  classical
  exact (Finset.card_eq_sum_card_fiberwise
    (s := family.G) (t := (Finset.univ : Finset (Fin 4)))
    (f := cover.cluster) (fun gamma _hgamma ↦ Finset.mem_univ _)).symm

/-- **Four-pencil terminal reduction.**  At the exact predecessor threshold,
a four-saturated-pencil cover forces the rich-point family to have at most
the domain size.  All geometric hypotheses of the abstract capacity theorem
are discharged by exact Reed--Solomon line-core geometry. -/
theorem BadScalarRichPointFamily.card_le_of_fourSaturatedPencilCover
    {dom : I ↪ F} {k t m z : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hm : 8 ≤ m) (hI : Fintype.card I = 16 * m)
    (hz : 6 * z = 53 * m - 8)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = t)
    (cover : FourSaturatedPencilCover family t z) :
    family.G.card ≤ 16 * m := by
  let G : Fin 4 → Finset F := fun i ↦ clusterScalars cover i
  let A : Fin 4 → F → Finset I := fun i gamma ↦
    fullAgreement dom (u 0) (u 1) gamma
      ((cover.source i).1 + C gamma * (cover.source i).2)
  let D : Fin 4 → Finset I := fun i ↦
    jointCore dom (u 0) (u 1)
      (cover.source i).1 (cover.source i).2
  have hcap := fourSaturatedCluster_label_card_le G A D t m z
    hm hI hz
    (fun i ↦ by simpa only [D] using cover.coreCard i)
    (fun i gamma _hgamma ↦ by
      simpa only [A, D] using
        (jointCore_subset_fullAgreement dom (u 0) (u 1)
          (cover.source i).1 (cover.source i).2 gamma))
    (fun i gamma _hgamma beta _hbeta hne ↦ by
      simpa only [A, D] using
        (freshAgreement_disjoint dom (u 0) (u 1)
          (cover.source i).1 (cover.source i).2 hne))
    (fun i gamma hgamma ↦ by
      have hmem := (mem_clusterScalars_iff cover i gamma).mp hgamma
      have hon := (mem_pointsOn_iff family (cover.source i) gamma).mp
        (by simpa only [hmem.2] using cover.mem_source gamma hmem.1)
      rw [← hthreshold]
      simpa only [A, ← hon.2] using family.threshold_le gamma hmem.1)
    (fun i ↦ by simpa only [D] using cover.twoFresh i)
  rw [← sum_clusterScalars_card cover]
  simpa only [G] using hcap

/-- **Relaxed four-pencil terminal reduction.**  Four source pencils whose
cores each leave two coordinates before the agreement threshold carry at
most the domain size under the P1 complement arithmetic.  The cover's
`coreCard` field is deliberately unused; in the relaxed extraction API its
lower-bound parameter is zero. -/
theorem BadScalarRichPointFamily.card_le_of_fourTwoFreshPencilCover
    {dom : I ↪ F} {k t z : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (ht : t ≤ Fintype.card I)
    (hroom : 2 * (Fintype.card I - t + 2) ≤ Fintype.card I)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = t)
    (cover : FourSaturatedPencilCover family t z) :
    family.G.card ≤ Fintype.card I := by
  let G : Fin 4 → Finset F := fun i ↦ clusterScalars cover i
  let A : Fin 4 → F → Finset I := fun i gamma ↦
    fullAgreement dom (u 0) (u 1) gamma
      ((cover.source i).1 + C gamma * (cover.source i).2)
  let D : Fin 4 → Finset I := fun i ↦
    jointCore dom (u 0) (u 1)
      (cover.source i).1 (cover.source i).2
  have hcap := fourTwoFreshCluster_label_card_le_universe G A D t ht hroom
    (fun i gamma _hgamma ↦ by
      simpa only [A, D] using
        (jointCore_subset_fullAgreement dom (u 0) (u 1)
          (cover.source i).1 (cover.source i).2 gamma))
    (fun i gamma _hgamma beta _hbeta hne ↦ by
      simpa only [A, D] using
        (freshAgreement_disjoint dom (u 0) (u 1)
          (cover.source i).1 (cover.source i).2 hne))
    (fun i gamma hgamma ↦ by
      have hmem := (mem_clusterScalars_iff cover i gamma).mp hgamma
      have hon := (mem_pointsOn_iff family (cover.source i) gamma).mp
        (by simpa only [hmem.2] using cover.mem_source gamma hmem.1)
      rw [← hthreshold]
      simpa only [A, ← hon.2] using family.threshold_le gamma hmem.1)
    (fun i ↦ by simpa only [D] using cover.twoFresh i)
  rw [← sum_clusterScalars_card cover]
  simpa only [G] using hcap

/-! ## Exact P1 predecessor arithmetic -/

namespace P1

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorArithmetic

/-- The good lattice predecessor has one more required agreement coordinate
than the amplified bad construction. -/
abbrev predecessorThreshold : Nat := amplifiedThreshold + 1

/-- Its radius numerator is therefore one below the amplified bad radius
numerator. -/
abbrev predecessorRadiusNumerator : Nat := N - predecessorThreshold

noncomputable abbrev predecessorDelta : NNReal :=
  predecessorRadiusNumerator / N

theorem predecessor_threshold_value :
    predecessorThreshold = 592794966 := by
  norm_num [predecessorThreshold, amplifiedThreshold, amplifiedCore, m, r, d]

theorem predecessor_radius_numerator_value :
    predecessorRadiusNumerator = 480946858 := by
  norm_num [predecessorRadiusNumerator, predecessorThreshold,
    amplifiedThreshold, amplifiedCore, N, m, r, d]

theorem amplified_core_balance :
    6 * amplifiedCore = 53 * m - 8 := by
  norm_num [amplifiedCore, m, r, d]

theorem predecessor_two_fresh :
    amplifiedCore + 2 = predecessorThreshold := by
  rfl

theorem agreement_mass_eq_predecessorThreshold :
    (1 - predecessorDelta) * (N : NNReal) = predecessorThreshold := by
  have hd : predecessorDelta ≤ 1 := by
    norm_num [predecessorDelta, predecessorRadiusNumerator,
      predecessorThreshold, amplifiedThreshold, amplifiedCore, N, m, r, d]
    rw [div_le_one] <;> norm_num
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_sub hd]
  push_cast
  norm_num [predecessorDelta, predecessorRadiusNumerator,
    predecessorThreshold, amplifiedThreshold, amplifiedCore, N, m, r, d]

theorem ceil_agreement_mass_eq_predecessorThreshold :
    ⌈(1 - predecessorDelta) * (N : NNReal)⌉₊ = predecessorThreshold := by
  rw [agreement_mass_eq_predecessorThreshold, Nat.ceil_natCast]

variable {J : Type} [Fintype J] [Nonempty J] [DecidableEq J]

local instance localInstance_RateQuarterPredecessorFourPencilReduction_1 : Fact (Nat.Prime P) := ⟨prime_P⟩

/-- The canonical selected rich-point family at the P1 predecessor. -/
noncomputable def predecessorRichPointFamily
    (dom : J ↪ P1RateQuarterScaleArithmetic.F)
    (u : WordStack P1RateQuarterScaleArithmetic.F (Fin 2) J) :
    BadScalarRichPointFamily dom k predecessorDelta u :=
  canonicalBadScalarRichPointFamily dom predecessorDelta u (by norm_num [k])

/-- The canonical-choice extraction residual for one received stack.

This retains the original API, whose rich-point family is built from the
library's fixed `Classical.choice` decode at each bad scalar.  Geometric
arguments that need to choose favorable decoded polynomials should use
`FavorableFourPencilExtraction` instead. -/
def FourPencilExtraction
    (dom : J ↪ P1RateQuarterScaleArithmetic.F)
    (u : WordStack P1RateQuarterScaleArithmetic.F (Fin 2) J) : Prop :=
  Nonempty (FourSaturatedPencilCover
    (predecessorRichPointFamily dom u) predecessorThreshold amplifiedCore)

/-- A four-pencil extraction after a favorable choice of one rich-point
witness for every bad scalar.  Unlike `FourPencilExtraction`, this proposition
does not require the arbitrary canonical decoded polynomials to be coverable. -/
def FavorableFourPencilExtraction
    (dom : J ↪ P1RateQuarterScaleArithmetic.F)
    (u : WordStack P1RateQuarterScaleArithmetic.F (Fin 2) J) : Prop :=
  ∃ family : BadScalarRichPointFamily dom k predecessorDelta u,
    Nonempty (FourSaturatedPencilCover family predecessorThreshold amplifiedCore)

/-- A favorable four-pencil extraction requiring only two fresh coordinates
beyond each source core.  The zero lower-bound parameter makes `coreCard`
vacuous, so unlike `FavorableFourPencilExtraction` this does not require the
four source cores to have the saturated size `amplifiedCore`. -/
def FavorableFourTwoFreshPencilExtraction
    (dom : J ↪ P1RateQuarterScaleArithmetic.F)
    (u : WordStack P1RateQuarterScaleArithmetic.F (Fin 2) J) : Prop :=
  ∃ family : BadScalarRichPointFamily dom k predecessorDelta u,
    Nonempty (FourSaturatedPencilCover family predecessorThreshold 0)

/-- A cover of the canonical rich-point family is, in particular, a favorable
witness extraction. -/
theorem favorableFourPencilExtraction_of_fourPencilExtraction
    (dom : J ↪ P1RateQuarterScaleArithmetic.F)
    (u : WordStack P1RateQuarterScaleArithmetic.F (Fin 2) J)
    (hextract : FourPencilExtraction dom u) :
    FavorableFourPencilExtraction dom u :=
  ⟨predecessorRichPointFamily dom u, hextract⟩

/-- Saturated favorable extraction implies the relaxed two-fresh extraction.
This is the formal one-way comparison between the old and new local geometric
certificates. -/
theorem favorableFourTwoFreshPencilExtraction_of_favorableFourPencilExtraction
    (dom : J ↪ P1RateQuarterScaleArithmetic.F)
    (u : WordStack P1RateQuarterScaleArithmetic.F (Fin 2) J)
    (hextract : FavorableFourPencilExtraction dom u) :
    FavorableFourTwoFreshPencilExtraction dom u := by
  obtain ⟨family, ⟨cover⟩⟩ := hextract
  refine ⟨family, ⟨{
    cluster := cover.cluster
    source := cover.source
    mem_source := cover.mem_source
    coreCard := fun _i ↦ Nat.zero_le _
    twoFresh := cover.twoFresh }⟩⟩

/-- **P1 bad-count closure from four-pencil extraction.**  This is the
literal `mcaBadCount ≤ N` conclusion sought at the saturated predecessor. -/
theorem mcaBadCount_le_N_of_fourPencilExtraction
    (dom : J ↪ P1RateQuarterScaleArithmetic.F)
    (u : WordStack P1RateQuarterScaleArithmetic.F (Fin 2) J)
    (hJ : Fintype.card J = N)
    (hextract : FourPencilExtraction dom u) :
    mcaBadCount (F := P1RateQuarterScaleArithmetic.F)
      ((ReedSolomon.code dom k : Set
        (J → P1RateQuarterScaleArithmetic.F)))
      predecessorDelta (u 0) (u 1) ≤ N := by
  obtain ⟨cover⟩ := hextract
  have hJ16 : Fintype.card J = 16 * m := by
    rw [hJ, N_eq_sixteen_mul_m]
  have hthreshold :
      ⌈(1 - predecessorDelta) * (Fintype.card J : NNReal)⌉₊ =
        predecessorThreshold := by
    rw [hJ]
    exact ceil_agreement_mass_eq_predecessorThreshold
  have hfamily :=
    _root_.ArkLib.ProximityGap.Frontier.RateQuarterPredecessorFourPencilReduction.BadScalarRichPointFamily.card_le_of_fourSaturatedPencilCover
      (predecessorRichPointFamily dom u)
      (by norm_num [m]) hJ16 amplified_core_balance hthreshold cover
  change (predecessorRichPointFamily dom u).G.card ≤ N
  rw [N_eq_sixteen_mul_m]
  exact hfamily

/-- **P1 bad-count closure from a favorable four-pencil extraction.**  The
chosen rich-point family may use any decoded polynomial witness at each bad
scalar; `BadScalarRichPointFamily.G_eq_badScalars` identifies its scalar set
with the literal MCA bad-event filter. -/
theorem mcaBadCount_le_N_of_favorableFourPencilExtraction
    (dom : J ↪ P1RateQuarterScaleArithmetic.F)
    (u : WordStack P1RateQuarterScaleArithmetic.F (Fin 2) J)
    (hJ : Fintype.card J = N)
    (hextract : FavorableFourPencilExtraction dom u) :
    mcaBadCount (F := P1RateQuarterScaleArithmetic.F)
      ((ReedSolomon.code dom k : Set
        (J → P1RateQuarterScaleArithmetic.F)))
      predecessorDelta (u 0) (u 1) ≤ N := by
  obtain ⟨family, ⟨cover⟩⟩ := hextract
  have hJ16 : Fintype.card J = 16 * m := by
    rw [hJ, N_eq_sixteen_mul_m]
  have hthreshold :
      ⌈(1 - predecessorDelta) * (Fintype.card J : NNReal)⌉₊ =
        predecessorThreshold := by
    rw [hJ]
    exact ceil_agreement_mass_eq_predecessorThreshold
  have hfamily :=
    _root_.ArkLib.ProximityGap.Frontier.RateQuarterPredecessorFourPencilReduction.BadScalarRichPointFamily.card_le_of_fourSaturatedPencilCover
      family (by norm_num [m]) hJ16 amplified_core_balance hthreshold cover
  change (badScalars dom k predecessorDelta u).card ≤ N
  rw [← family.G_eq_badScalars, N_eq_sixteen_mul_m]
  exact hfamily

/-- **P1 bad-count closure from the relaxed favorable extraction.**  No
saturated lower bound is used: four source cores with the two-fresh gap alone
give the literal `mcaBadCount ≤ N` conclusion. -/
theorem mcaBadCount_le_N_of_favorableFourTwoFreshPencilExtraction
    (dom : J ↪ P1RateQuarterScaleArithmetic.F)
    (u : WordStack P1RateQuarterScaleArithmetic.F (Fin 2) J)
    (hJ : Fintype.card J = N)
    (hextract : FavorableFourTwoFreshPencilExtraction dom u) :
    mcaBadCount (F := P1RateQuarterScaleArithmetic.F)
      ((ReedSolomon.code dom k : Set
        (J → P1RateQuarterScaleArithmetic.F)))
      predecessorDelta (u 0) (u 1) ≤ N := by
  obtain ⟨family, ⟨cover⟩⟩ := hextract
  have ht : predecessorThreshold ≤ Fintype.card J := by
    rw [hJ]
    norm_num [predecessorThreshold, amplifiedThreshold, amplifiedCore,
      N, m, r, d]
  have hroom :
      2 * (Fintype.card J - predecessorThreshold + 2) ≤ Fintype.card J := by
    rw [hJ]
    norm_num [predecessorThreshold, amplifiedThreshold, amplifiedCore,
      N, m, r, d]
  have hthreshold :
      ⌈(1 - predecessorDelta) * (Fintype.card J : NNReal)⌉₊ =
        predecessorThreshold := by
    rw [hJ]
    exact ceil_agreement_mass_eq_predecessorThreshold
  have hfamily :=
    _root_.ArkLib.ProximityGap.Frontier.RateQuarterPredecessorFourPencilReduction.BadScalarRichPointFamily.card_le_of_fourTwoFreshPencilCover
      family ht hroom hthreshold cover
  change (badScalars dom k predecessorDelta u).card ≤ N
  rw [← family.G_eq_badScalars, ← hJ]
  exact hfamily

end P1

end ArkLib.ProximityGap.Frontier.RateQuarterPredecessorFourPencilReduction

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.RateQuarterPredecessorFourPencilReduction
#print axioms sum_clusterScalars_card
#print axioms BadScalarRichPointFamily.card_le_of_fourSaturatedPencilCover
#print axioms BadScalarRichPointFamily.card_le_of_fourTwoFreshPencilCover
#print axioms P1.agreement_mass_eq_predecessorThreshold
#print axioms P1.ceil_agreement_mass_eq_predecessorThreshold
#print axioms P1.mcaBadCount_le_N_of_fourPencilExtraction
#print axioms P1.mcaBadCount_le_N_of_favorableFourPencilExtraction
#print axioms P1.mcaBadCount_le_N_of_favorableFourTwoFreshPencilExtraction
