/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DesignMatrixAffineCluster
import ArkLib.Data.CodingTheory.ProximityGap.CoveragePigeonhole
import ArkLib.Data.CodingTheory.ProximityGap.MCASecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-!
# The weighted secant-slope mass upper lens

Choose, for every bad scalar `gamma`, an explaining codeword `c gamma` and a witness
set `S gamma` of size at least `a`.  Every distinct pair has the codeword-valued secant
slope

`b = (gamma-gamma')^-1 * (c gamma-c gamma')`,

and `b` agrees with the direction row `u1` throughout `S gamma ∩ S gamma'`.

For one fixed slope `b`, equality of secant slope is equality of the affine intercept
`c gamma - gamma*b`.  Its fibers are therefore exactly affine-pencil clusters.  The
`DesignMatrixAffineCluster` theorem bounds every such fiber by

`cap_a(b) = support(u1-b) / max(1, a-agree(u1,b))`.

Combining this with the global Cauchy lower bound on witness intersections gives

`|G| * a^2 <= n^2 + n * WeightedSlopeMass`,

where

`WeightedSlopeMass = sum_{realized b} agree(u1,b) * (cap_a(b)-1)`.

This is an exact bad-count upper lens, not a solution of the good side.  Its remaining
input is a weighted list-mass bound for the realized nearby codewords `b`.  The final
coarse consumer shows that replacing this mass by an ordinary list-size bound recovers
the familiar doubled-radius/list-decoding wall.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators NNReal

namespace ProximityGap.Frontier.WeightedSlopeMassUpperLens

open ProximityGap
open ProximityGap.MCAWitnessSpread
open ProximityGap.Frontier.DesignMatrixAffineCluster

/-! ## Abstract weighted Cauchy engine -/

section AbstractCauchy

variable {kappa iota : Type*} [Fintype kappa] [Nonempty kappa] [DecidableEq kappa]
variable [Fintype iota] [DecidableEq iota]

/-- Total ordered off-diagonal intersection mass of a finite set family. -/
def offDiagInterMass (S : kappa -> Finset iota) : Nat :=
  ∑ x : kappa, ∑ y ∈ (Finset.univ : Finset kappa).erase x, (S x ∩ S y).card

/-- **Weighted Cauchy engine.**  If every set has size at least `a` and the total ordered
off-diagonal intersection mass is at most `|kappa|*R`, then

`|kappa| * a^2 <= |iota|^2 + |iota|*R`.

The cancellation of one factor `|kappa|` is valid because the index type is nonempty. -/
theorem card_mul_sq_le_length_sq_add_weightedMass
    (S : kappa -> Finset iota) (a R : Nat)
    (hsize : ∀ x, a <= (S x).card)
    (hmass : offDiagInterMass S <= Fintype.card kappa * R) :
    Fintype.card kappa * a ^ 2 <=
      (Fintype.card iota) ^ 2 + Fintype.card iota * R := by
  classical
  let L := Fintype.card kappa
  let N := Fintype.card iota
  have hsumLo : L * a <= ∑ x : kappa, (S x).card := by
    rw [show L * a = ∑ _x : kappa, a by simp [L, Nat.mul_comm]]
    exact Finset.sum_le_sum (fun x _ => hsize x)
  have hsplit : (∑ x : kappa, ∑ y : kappa, (S x ∩ S y).card) =
      (∑ x : kappa, (S x).card) + offDiagInterMass S := by
    rw [offDiagInterMass, <- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [show (∑ y : kappa, (S x ∩ S y).card) =
        (S x ∩ S x).card +
          ∑ y ∈ (Finset.univ : Finset kappa).erase x, (S x ∩ S y).card by
      exact (Finset.add_sum_erase Finset.univ
        (fun y => (S x ∩ S y).card) (Finset.mem_univ x)).symm]
    simp
  have hdiag : (∑ x : kappa, (S x).card) <= L * N := by
    calc
      (∑ x : kappa, (S x).card) <= ∑ _x : kappa, N := by
        apply Finset.sum_le_sum
        intro x _
        calc
          (S x).card <= (Finset.univ : Finset iota).card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = N := by simp [N]
      _ = L * N := by simp [L]
  have hCS := ArkLib.Coverage.sq_sum_card_le_card_mul_sum_inter S
  have hmain : (L * a) ^ 2 <= N * (L * N + L * R) := by
    calc
      (L * a) ^ 2 <= (∑ x : kappa, (S x).card) ^ 2 :=
        Nat.pow_le_pow_left hsumLo 2
      _ <= N * (∑ x : kappa, ∑ y : kappa, (S x ∩ S y).card) := by
        simpa [N] using hCS
      _ = N * ((∑ x : kappa, (S x).card) + offDiagInterMass S) := by
        rw [hsplit]
      _ <= N * (L * N + L * R) := by
        gcongr
  have hfactor : (L * a) ^ 2 = L * (L * a ^ 2) := by ring
  have hrhs : N * (L * N + L * R) = L * (N ^ 2 + N * R) := by ring
  rw [hfactor, hrhs] at hmain
  exact Nat.le_of_mul_le_mul_left hmain Fintype.card_pos

end AbstractCauchy

/-! ## Secant slopes and affine intercepts -/

section Slopes

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : Nat} [NeZero n]

/-- Secant slope of two explainer points over distinct scalar coordinates. -/
def secantSlope (gamma gamma' : F) (c c' : Fin n -> F) : Fin n -> F :=
  (gamma - gamma')⁻¹ • (c - c')

/-- Affine intercept of an explainer point relative to a proposed slope. -/
def affineIntercept (gamma : F) (c b : Fin n -> F) : Fin n -> F :=
  c - gamma • b

/-- Coordinates on which a slope codeword agrees with the direction row. -/
noncomputable def slopeAgreeSet (u1 b : Fin n -> F) : Finset (Fin n) :=
  Finset.univ.filter (fun i => b i = u1 i)

/-- Complementary support of the direction-row discrepancy. -/
noncomputable def slopeSupport (u1 b : Fin n -> F) : Finset (Fin n) :=
  Finset.univ.filter (fun i => u1 i - b i ≠ 0)

/-- Uniform pin multiplicity available for every affine cluster of slope `b`. -/
noncomputable def slopePinMultiplicity (a : Nat) (u1 b : Fin n -> F) : Nat :=
  max 1 (a - (slopeAgreeSet u1 b).card)

/-- Maximum affine-cluster size furnished by the support/pin bound. -/
noncomputable def slopeClusterCap (a : Nat) (u1 b : Fin n -> F) : Nat :=
  (slopeSupport u1 b).card / slopePinMultiplicity a u1 b

/-- Equality of a nonvertical secant slope is exactly equality of affine intercepts. -/
theorem secantSlope_eq_iff_affineIntercept_eq
    {gamma gamma' : F} (hne : gamma ≠ gamma') (c c' b : Fin n -> F) :
    secantSlope gamma gamma' c c' = b ↔
      affineIntercept gamma c b = affineIntercept gamma' c' b := by
  have hd : gamma - gamma' ≠ 0 := sub_ne_zero.mpr hne
  constructor
  · intro hslope
    have hdiff := congrArg (fun w : Fin n -> F => (gamma - gamma') • w) hslope
    have hdiff' : c - c' = (gamma - gamma') • b := by
      simpa [secantSlope, smul_smul, hd] using hdiff
    funext i
    have hdiffi := congrFun hdiff' i
    simp only [affineIntercept, Pi.sub_apply, Pi.smul_apply] at hdiffi ⊢
    linear_combination hdiffi
  · intro hintercept
    have hdiff : c - c' = (gamma - gamma') • b := by
      funext i
      have hi := congrFun hintercept i
      simp only [affineIntercept, Pi.sub_apply, Pi.smul_apply] at hi ⊢
      linear_combination hi
    simp [secantSlope, hdiff, smul_smul, hd]

/-- The locked coordinates of an affine pencil are contained in its slope-agreement set. -/
theorem lockedSet_subset_slopeAgreeSet
    (c0 b u0 u1 : Fin n -> F) :
    lockedSet c0 b u0 u1 ⊆ slopeAgreeSet u1 b := by
  classical
  intro i hi
  rw [lockedSet, Finset.mem_filter] at hi
  rw [slopeAgreeSet, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hi.2.2⟩

/-- The cluster-independent pin multiplicity is no larger than the exact locked-set
multiplicity used by `affineCluster_card_mul_le_support`. -/
theorem slopePinMultiplicity_le_lockedMultiplicity
    (a : Nat) (c0 b u0 u1 : Fin n -> F) :
    slopePinMultiplicity a u1 b <= max 1 (a - (lockedSet c0 b u0 u1).card) := by
  have hcard : (lockedSet c0 b u0 u1).card <= (slopeAgreeSet u1 b).card :=
    Finset.card_le_card (lockedSet_subset_slopeAgreeSet c0 b u0 u1)
  exact max_le_max le_rfl (Nat.sub_le_sub_left hcard a)

/-- A witness intersection is contained in the agreement set of its secant slope. -/
theorem witness_inter_subset_slopeAgreeSet
    (C : Submodule F (Fin n -> F)) {S S' : Finset (Fin n)}
    {u0 u1 c c' : Fin n -> F} {gamma gamma' : F}
    (hne : gamma ≠ gamma') (hc : c ∈ C) (hc' : c' ∈ C)
    (hS : ∀ i ∈ S, c i = u0 i + gamma * u1 i)
    (hS' : ∀ i ∈ S', c' i = u0 i + gamma' * u1 i) :
    S ∩ S' ⊆ slopeAgreeSet u1 (secantSlope gamma gamma' c c') := by
  classical
  have hslope := line_slope_codeword_of_two_witnesses C hne hc hc'
    (by simpa [smul_eq_mul] using hS) (by simpa [smul_eq_mul] using hS')
  intro i hi
  rw [slopeAgreeSet, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hslope.2 i hi⟩

/-! ## Fixed-slope affine-cluster count -/

/-- Secant slopes actually realized by ordered distinct pairs from `G`. -/
noncomputable def realizedSlopes (G : Finset F) (c : F -> Fin n -> F) :
    Finset (Fin n -> F) :=
  G.offDiag.image (fun pair => secantSlope pair.1 pair.2 (c pair.1) (c pair.2))

/-- Number of ordered distinct pairs with one prescribed secant slope. -/
noncomputable def slopePairCount (G : Finset F) (c : F -> Fin n -> F)
    (b : Fin n -> F) : Nat :=
  (G.offDiag.filter
    (fun pair => secantSlope pair.1 pair.2 (c pair.1) (c pair.2) = b)).card

/-- The weighted mass of realized slopes that appears in the final Cauchy bound. -/
noncomputable def weightedSlopeMass (a : Nat) (G : Finset F)
    (c : F -> Fin n -> F) (u1 : Fin n -> F) : Nat :=
  ∑ b ∈ realizedSlopes G c,
    (slopeAgreeSet u1 b).card * (slopeClusterCap a u1 b - 1)

/-- Every realized secant slope is a codeword. -/
theorem realizedSlopes_subset_code
    (C : Submodule F (Fin n -> F)) (G : Finset F) (c : F -> Fin n -> F)
    (hcode : ∀ gamma ∈ G, c gamma ∈ C) :
    ∀ b ∈ realizedSlopes G c, b ∈ C := by
  classical
  intro b hb
  obtain ⟨pair, hpair, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hgamma, hgamma', _hne⟩ := Finset.mem_offDiag.mp hpair
  exact C.smul_mem _ (C.sub_mem (hcode pair.1 hgamma) (hcode pair.2 hgamma'))

/-- Each affine-intercept fiber obeys the cluster-independent pin/support bound. -/
theorem interceptFiber_card_mul_le_support
    (C : Submodule F (Fin n -> F)) (G : Finset F)
    (c : F -> Fin n -> F) (S : F -> Finset (Fin n))
    (u0 u1 b d : Fin n -> F) (a : Nat)
    (hcode : ∀ gamma ∈ G, c gamma ∈ C)
    (hsize : ∀ gamma ∈ G, a <= (S gamma).card)
    (hagree : ∀ gamma ∈ G, ∀ i ∈ S gamma,
      c gamma i = u0 i + gamma * u1 i)
    (hno : ∀ gamma ∈ G,
      ¬ pairJointAgreesOn (C : Set (Fin n -> F)) (S gamma) u0 u1)
    (hb : b ∈ C)
    (hd : d ∈ G.image (fun gamma => affineIntercept gamma (c gamma) b)) :
    slopePinMultiplicity a u1 b *
        (G.filter (fun gamma => affineIntercept gamma (c gamma) b = d)).card
      <= (slopeSupport u1 b).card := by
  classical
  let H : Finset F := G.filter (fun gamma => affineIntercept gamma (c gamma) b = d)
  obtain ⟨gamma0, hgamma0, hgamma0d⟩ := Finset.mem_image.mp hd
  have hdCode : d ∈ C := by
    have hmem : affineIntercept gamma0 (c gamma0) b ∈ C := by
      exact C.sub_mem (hcode gamma0 hgamma0) (C.smul_mem gamma0 hb)
    simpa [hgamma0d] using hmem
  have hHexact := affineCluster_card_mul_le_support C d b u0 u1 hdCode hb a H S
    (fun gamma hgamma => hsize gamma (Finset.mem_filter.mp hgamma).1)
    (fun gamma hgamma i hi => by
      have hgammaG := (Finset.mem_filter.mp hgamma).1
      have hintercept := (Finset.mem_filter.mp hgamma).2
      have hintercept_i := congrFun hintercept i
      have hag := hagree gamma hgammaG i hi
      simp only [affineIntercept, Pi.sub_apply, Pi.smul_apply] at hintercept_i
      linear_combination hag - hintercept_i)
    (fun gamma hgamma => hno gamma (Finset.mem_filter.mp hgamma).1)
  have hmu : slopePinMultiplicity a u1 b <=
      max 1 (a - (lockedSet d b u0 u1).card) :=
    slopePinMultiplicity_le_lockedMultiplicity a d b u0 u1
  calc
    slopePinMultiplicity a u1 b * H.card <=
        max 1 (a - (lockedSet d b u0 u1).card) * H.card :=
      Nat.mul_le_mul_right H.card hmu
    _ <= (Finset.univ.filter (fun i => u1 i - b i ≠ 0)).card := hHexact
    _ = (slopeSupport u1 b).card := by rfl

/-- **Fixed-slope ordered-pair cap.**  The pairs of slope `b` split into affine-intercept
fibers, each of size at most `slopeClusterCap`.  Therefore

`slopePairCount b <= |G| * (slopeClusterCap b - 1)`. -/
theorem slopePairCount_le_card_mul_cap_sub_one
    (C : Submodule F (Fin n -> F)) (G : Finset F)
    (c : F -> Fin n -> F) (S : F -> Finset (Fin n))
    (u0 u1 b : Fin n -> F) (a : Nat)
    (hcode : ∀ gamma ∈ G, c gamma ∈ C)
    (hsize : ∀ gamma ∈ G, a <= (S gamma).card)
    (hagree : ∀ gamma ∈ G, ∀ i ∈ S gamma,
      c gamma i = u0 i + gamma * u1 i)
    (hno : ∀ gamma ∈ G,
      ¬ pairJointAgreesOn (C : Set (Fin n -> F)) (S gamma) u0 u1)
    (hb : b ∈ C) :
    slopePairCount G c b <= G.card * (slopeClusterCap a u1 b - 1) := by
  classical
  let f : F -> (Fin n -> F) := fun gamma => affineIntercept gamma (c gamma) b
  let mu : Nat := slopePinMultiplicity a u1 b
  let cap : Nat := slopeClusterCap a u1 b
  have hmu : 0 < mu := by
    dsimp [mu, slopePinMultiplicity]
    omega
  have hfilter : G.offDiag.filter
      (fun pair => secantSlope pair.1 pair.2 (c pair.1) (c pair.2) = b) =
      G.offDiag.filter (fun pair => f pair.1 = f pair.2) := by
    ext pair
    by_cases hp : pair ∈ G.offDiag
    · have hne : pair.1 ≠ pair.2 := (Finset.mem_offDiag.mp hp).2.2
      simp only [Finset.mem_filter, hp, true_and]
      exact secantSlope_eq_iff_affineIntercept_eq hne (c pair.1) (c pair.2) b
    · simp [hp]
  have hfiber : ∀ d ∈ G.image f, (G.filter (fun gamma => f gamma = d)).card <= cap := by
    intro d hd
    apply (Nat.le_div_iff_mul_le hmu).2
    simpa only [mu, cap, slopeClusterCap, f, Nat.mul_comm] using
      interceptFiber_card_mul_le_support C G c S u0 u1 b d a
        hcode hsize hagree hno hb hd
  have hterm : ∀ d ∈ G.image f,
      (G.filter (fun gamma => f gamma = d)).card *
          ((G.filter (fun gamma => f gamma = d)).card - 1) <=
        (G.filter (fun gamma => f gamma = d)).card * (cap - 1) := by
    intro d hd
    exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (hfiber d hd) 1)
  rw [slopePairCount, hfilter,
    ProximityGap.card_offDiag_collisions G f]
  calc
    (∑ d ∈ G.image f, (G.filter (fun gamma => f gamma = d)).card *
        ((G.filter (fun gamma => f gamma = d)).card - 1)) <=
      ∑ d ∈ G.image f, (G.filter (fun gamma => f gamma = d)).card * (cap - 1) :=
        Finset.sum_le_sum hterm
    _ = (∑ d ∈ G.image f, (G.filter (fun gamma => f gamma = d)).card) * (cap - 1) := by
      rw [Finset.sum_mul]
    _ = G.card * (cap - 1) := by
      rw [<- Finset.card_eq_sum_card_image f G]

end Slopes

section FinalLens

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : Nat} [NeZero n]

/-- Reindex the abstract subtype off-diagonal mass by the underlying scalar finset. -/
theorem offDiagInterMass_subtype_eq (G : Finset F) (S : F -> Finset (Fin n)) :
    offDiagInterMass (fun gamma : {x // x ∈ G} => S gamma.1) =
      ∑ gamma ∈ G, ∑ gamma' ∈ G.erase gamma, (S gamma ∩ S gamma').card := by
  classical
  simp only [offDiagInterMass, Finset.univ_eq_attach]
  have hinner : ∀ x : {x // x ∈ G},
      (∑ y ∈ G.attach.erase x, (S x.1 ∩ S y.1).card) =
        ∑ y ∈ G.erase x.1, (S x.1 ∩ S y).card := by
    intro x
    refine Finset.sum_bij'
      (fun y _ => y.1)
      (fun y hy => (⟨y, (Finset.mem_erase.mp hy).2⟩ : {z // z ∈ G})) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      have hy' := Finset.mem_erase.mp hy
      exact Finset.mem_erase.mpr ⟨fun h => hy'.1 (Subtype.ext h), y.2⟩
    · intro y hy
      have hy' := Finset.mem_erase.mp hy
      exact Finset.mem_erase.mpr ⟨fun h => hy'.1 (congrArg Subtype.val h),
        Finset.mem_attach.mpr (Finset.mem_univ _)⟩
    · intro y _
      exact Subtype.ext rfl
    · intro y _
      rfl
    · intro y _
      rfl
  calc
    (∑ x ∈ G.attach, ∑ y ∈ G.attach.erase x, (S x.1 ∩ S y.1).card) =
        ∑ x ∈ G.attach, ∑ y ∈ G.erase x.1, (S x.1 ∩ S y).card :=
      Finset.sum_congr rfl (fun x _ => hinner x)
    _ = ∑ x ∈ G, ∑ y ∈ G.erase x, (S x ∩ S y).card :=
      Finset.sum_attach G (fun x => ∑ y ∈ G.erase x.1, (S x.1 ∩ S y).card)

end FinalLens

end ProximityGap.Frontier.WeightedSlopeMassUpperLens

#print axioms ProximityGap.Frontier.WeightedSlopeMassUpperLens.card_mul_sq_le_length_sq_add_weightedMass
#print axioms ProximityGap.Frontier.WeightedSlopeMassUpperLens.secantSlope_eq_iff_affineIntercept_eq
#print axioms ProximityGap.Frontier.WeightedSlopeMassUpperLens.witness_inter_subset_slopeAgreeSet
