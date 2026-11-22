/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX - License - Identifier: MIT OR Apache - 2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterCoreWeightedJets
import ArkLib.Research.ProximityGap.Frontier._FSMB_CoreAbsorptionLadder

/-! # Three received-row interpolants at 529,940,000 quarter-rate errors

The two ordinary surfaces capture every agreeing section. The order - 38
surface reduces its local order by two for each of three owning joint cores.
It captures every agreeing section different from all three affine heads.
-/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.QuarterTransverseSurfaces

open Finset Polynomial SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation
open QuarterCoreWeightedJets (SectionSurface rowCount columnCount card_rows card_columns
  siteOrder three_core_rows three_core_weight weighted_received_surface uniform_received_surface)
open HalfPredecessorLineCoreGeometry (jointCore)

abbrev n : ℕ := 1073741824
abbrev d : ℕ := 268435455
abbrev e : ℕ := 529940000
abbrev t : ℕ := n - e
abbrev c : ℕ := t - 255
abbrev weight : ℕ := 38 * t - 6 * d

/-- Exact dimensions for the ordinary grids, with their respective surpluses. -/
theorem ordinary_surpluses :
    columnCount 37338 38 d (19 * t) = n * rowCount 37338 19 + 15513500 ∧
    columnCount 1051 74 d (37 * t) = n * rowCount 1051 37 + 5182964995 := by decide +kernel

variable {I F : Type} [Fintype I] [Field F]

/-- Each ordinary interpolant specializes to zero at every section that has
the requisite agreements on the supplied received rows. -/
theorem ordinary_surfaces (dom : I ↪ F) (u v : I → F) (hn : Fintype.card I = n)
    (companion : Bool) :
    let r := if companion then 37 else 19
    let b := if companion then 74 else 38
    let s := if companion then 1051 else 37338
    SectionSurface dom u v s b d (r * t) (fun S => t ≤ S.card) := by
  cases companion
  · apply uniform_received_surface dom u v (by decide) (by decide) (by decide)
    rw [hn, card_rows, card_columns]
    change n * rowCount 37338 19 < columnCount 37338 38 d (19 * t)
    rw [ordinary_surpluses.1]
    omega
  · apply uniform_received_surface dom u v (by decide) (by decide) (by decide)
    rw [hn, card_rows, card_columns]
    change n * rowCount 1051 37 < columnCount 1051 74 d (37 * t)
    rw [ordinary_surpluses.2]
    omega

variable [DecidableEq I]

/-- The four local costs permit a pair-overlap correction of 3,499. -/
theorem refined_residual_surplus (A B C : Finset I) (hn : Fintype.card I = n)
    (ha : c ≤ A.card) (hb : c ≤ B.card) (hc : c ≤ C.card)
    (hab : (A ∩ B).card ≤ d) (hac : (A ∩ C).card ≤ d) (hbc : (B ∩ C).card ≤ d) :
    Fintype.card ((x : I) × JetRows 909 (siteOrder 38 A B C x)) + 116531385053 ≤
      Fintype.card (Monomials 909 70 d weight) := by
  have bound := three_core_rows A B C (s := 909) (r := 38) (gain := 66881)
    (base := 665171) (penalty := 3499) (by decide +kernel)
  have cols : columnCount 909 70 d weight = 608046242959225 := by decide +kernel
  rw [card_columns, cols]
  rw [hn] at bound
  dsimp only [n,c,t,d,e] at *
  omega

/-- The residual row space fits with the indicated surplus for any three
sufficiently large cores having the stated pairwise overlap bounds. -/
theorem residual_surplus (A B C : Finset I) (hn : Fintype.card I = n)
    (ha : c ≤ A.card) (hb : c ≤ B.card) (hc : c ≤ C.card)
    (hab : (A ∩ B).card ≤ d) (hac : (A ∩ C).card ≤ d) (hbc : (B ∩ C).card ≤ d) :
    Fintype.card ((x : I) × JetRows 909 (siteOrder 38 A B C x)) + 2983187588 ≤
      Fintype.card (Monomials 909 70 d weight) := by
  have := refined_residual_surplus A B C hn ha hb hc hab hac hbc
  omega

theorem row_budget (A B C : Finset I) (hn : Fintype.card I = n)
    (ha : c ≤ A.card) (hb : c ≤ B.card) (hc : c ≤ C.card)
    (hab : (A ∩ B).card ≤ d) (hac : (A ∩ C).card ≤ d) (hbc : (B ∩ C).card ≤ d) :
    Fintype.card ((x : I) × JetRows 909 (siteOrder 38 A B C x)) <
      Fintype.card (Monomials 909 70 d weight) := by
  have := residual_surplus A B C hn ha hb hc hab hac hbc
  omega

omit [Fintype I] in
/-- A residual section loses at most six degree budgets in the weighted sum. -/
theorem agreement_weight (A B C S : Finset I) (hs : t ≤ S.card)
    (ha : (S ∩ A).card ≤ d) (hb : (S ∩ B).card ≤ d) (hc : (S ∩ C).card ≤ d) :
    weight ≤ ∑ x ∈ S, siteOrder 38 A B C x := three_core_weight A B C S hs ha hb hc

/-- The single residual interpolant captures all agreeing sections meeting each
of three selected cores at most `d` times. -/
theorem residual_surface (dom : I ↪ F) (u v : I → F) (A B C : Finset I)
    (hn : Fintype.card I = n) (ha : c ≤ A.card) (hb : c ≤ B.card) (hc : c ≤ C.card)
    (hab : (A ∩ B).card ≤ d) (hac : (A ∩ C).card ≤ d) (hbc : (B ∩ C).card ≤ d) :
    SectionSurface dom u v 909 70 d weight (fun S =>
      t ≤ S.card ∧ (S ∩ A).card ≤ d ∧ (S ∩ B).card ≤ d ∧ (S ∩ C).card ≤ d) := by
  obtain ⟨Q, hQ, supp, site, capture⟩ := weighted_received_surface dom u v (siteOrder 38 A B C)
    (QuarterCoreWeightedJets.siteOrder_pos (by decide : 6 < 38) A B C)
    (by decide : 0 < weight) (fun x => by unfold siteOrder; omega)
    (row_budget A B C hn ha hb hc hab hac hbc)
  refine ⟨Q, hQ, supp, site, ?_⟩
  intro g q hq S hs
  exact capture g q hq S (agreement_weight A B C S hs.1 hs.2.1 hs.2.2.1 hs.2.2.2)

/-- Three distinct affine heads with rich joint cores supply all the core bounds.
The resulting nonzero polynomial captures every section outside those heads. -/
theorem residual_off_heads [Fintype F] [DecidableEq F] (dom : I ↪ F) (u v : I → F)
    (hn : Fintype.card I = n) (heads : Fin 3 → F[X] × F[X]) (hinj : Function.Injective heads)
    (hd : ∀ i, (heads i).1.natDegree ≤ d ∧ (heads i).2.natDegree ≤ d)
    (rich : ∀ i, c ≤ (jointCore dom u v (heads i).1 (heads i).2).card) :
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j h x, ((Q.coeff j).coeff h).coeff x ≠ 0 → j ≤ 70 ∧ h + j ≤ 909 ∧ x + j * d < weight) ∧
      (∀ x, Q.eval₂ (mapRingHom (evalRingHom (dom x)))
        (Polynomial.C (u x) + X * Polynomial.C (v x)) = 0) ∧
      ∀ g : F, ∀ q : F[X], q.natDegree ≤ d → ∀ S : Finset I, t ≤ S.card →
        (∀ i, q ≠ (heads i).1 + Polynomial.C g * (heads i).2) →
        (∀ x ∈ S, q.eval (dom x) = u x + g * v x) → Q.eval₂ (evalRingHom (Polynomial.C g)) q = 0 := by
  let K (i : Fin 3) := jointCore dom u v (heads i).1 (heads i).2
  have pair (i j : Fin 3) (he : i ≠ j) : (K i ∩ K j).card ≤ d := by
    have different : (heads i).1 ≠ (heads j).1 ∨ (heads i).2 ≠ (heads j).2 := by
      by_contra! h
      exact he (hinj (Prod.ext h.1 h.2))
    exact FSMBCoreAbsorptionLadder.jointCore_inter_jointCore_card_le dom u v
      (by decide : 1 ≤ d + 1) (Nat.lt_succ_of_le (hd i).1) (Nat.lt_succ_of_le (hd i).2)
      (Nat.lt_succ_of_le (hd j).1) (Nat.lt_succ_of_le (hd j).2) different
  obtain ⟨Q, hQ, supp, site, capture⟩ := residual_surface dom u v (K 0) (K 1) (K 2) hn
    (rich 0) (rich 1) (rich 2) (pair 0 1 (by decide)) (pair 0 2 (by decide))
    (pair 1 2 (by decide))
  refine ⟨Q, hQ, supp, site, ?_⟩
  intro g q hq S hs hout hag
  have overlap (i : Fin 3) : (S ∩ K i).card ≤ d :=
    QuarterCoreWeightedJets.outside_overlap dom u v (heads i).1 (heads i).2 q g (K i) S
      (hd i).1 (hd i).2 hq (hout i) (fun _ hx => (mem_filter.mp hx).2) hag
  exact capture g q hq S ⟨hs, overlap 0, overlap 1, overlap 2⟩ hag

#print axioms ordinary_surfaces
#print axioms residual_surplus
#print axioms residual_off_heads
end ArkLib.ProximityGap.Frontier.QuarterTransverseSurfaces
