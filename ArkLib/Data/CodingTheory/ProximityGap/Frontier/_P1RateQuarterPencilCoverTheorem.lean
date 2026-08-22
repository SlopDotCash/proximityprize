/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPencilHarvestCap

/-!
# Pencil-cover theorem: pair-pencil existence, the pair pigeonhole, and the
# margin-free four-pencil budget

Issue #466, P1 rate-quarter — residual (c) round (cover-by-few-pencils), following
the dyadic-domain round.

**The math.**  Every PAIR of bad scalars rides its divided-difference pencil
(in-tree `pencil_reproduces_first/second`), and the pencil's aligned set contains
the pairwise witness intersection (`pencil_agrees_on_inter`), whose size is at
least `2T − N = 111848108 > 0` at the P1 shape — so cover EXISTENCE is a theorem
(`pair_pencil_aligned_floor`).  Distinct pencils share at most one rider, so the
pencils PARTITION the ordered pairs:
`B(B−1) = Σ_π m_π(m_π−1)` with the unconditional per-pencil cap
`m_π ≤ c = N − T + 1 = 480946859` (`riders_card_le_uniform`).  Pigeonhole: a
pair-cover by `P` pencils forces `B² ≤ P·c²`; at `P = 4` this gives
`B ≤ 2c = 961893718 ≤ N` — a **margin-free** budget theorem
(`stall_budget_of_four_pair_pencil_cover`), strictly complementing the
scalar-cover theorems (which needed margin hypotheses beyond two pencils).
`P = 5` no longer suffices (`(N+1)² ≤ 5c²`): the pigeonhole route caps at four.

**Probe** (`scripts/probes/probe_rate_quarter_p1_pencil_cover.py`, exact): the
census's extremal dual family (`B = 230 = 2c'` at μ_256/q=1031) has pair-pencil
distribution `{m=115: 2 pencils, m=2: 13225 pencils}`, the partition identity
`Σ m(m−1) = B(B−1) = 52670` holds exactly, and the family needs 13227 distinct
pencils — over-budget families live in the MANY-pencil regime (de Bruijn–Erdős
territory), which is where the open content now sits.

**Kernel-checked** (prize shape):

* `pair_pencil_aligned_floor` — every pair of bad scalars rides a common pencil
  whose aligned set has `≥ 2T − N = 111848108` coordinates (cover existence with
  an alignment floor).
* `stall_budget_of_four_pair_pencil_cover` — bad families whose PAIRS are covered
  by four pencils obey the `StallResidual` budget: `B² ≤ 4c² ⟹ B ≤ 2c ≤ N`.
  No margin or alignment hypotheses.
* `overBudget_no_four_pencil_pair_cover` — contrapositive: an over-budget family
  admits no 4-pencil pair-cover (hence, with the partition identity, needs ≥ 5
  distinct pair-pencils; the probe shows extremal families need thousands).
* `pair_pigeonhole_ledger`, `five_cover_insufficient`,
  `pairPencil_floor_constant` — the exact arithmetic.

**Honesty**: this closes the FEW-pencil corner of residual (c) completely
(≤ 4 pencils at pair level, margin-free; ≤ 2 at scalar level unconditionally;
3–4 at scalar level under probe-forced margins).  The open content of
`StallResidual(μ_{2^30})` is now exactly the MANY-pencil regime: families whose
pairs spread over `≥ 5` (extremally, thousands of) distinct pencils, each pencil
`(2T−N)`-aligned — the sub-Johnson direction-swarm picture of the derecursion
file, unchanged.  No δ* movement; bracket `3/8 ≤ δ* ≤ 43/96 + ε` untouched.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCoverTheorem

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge
open ProximityGap.SharedFreshPencil
open ArkLib.ProximityGap.Frontier.P1RateQuarterDChargeDerecursion
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilHarvestCap

local instance localInstance_P1RateQuarterPencilCoverTheorem_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterPencilCoverTheorem_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## Cover existence: every pair rides a `(2T−N)`-aligned pencil -/

section PairPencil

variable (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
variable (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)

/-- **Pair-pencil aligned floor**: two distinct bad scalars ride the
divided-difference pencil of their witnesses, and its aligned set contains the
pairwise witness intersection — at least `2T − N = 111848108` coordinates.  Cover
EXISTENCE for the pencil-class budget theorems is thus unconditional; only
FEWNESS is at stake. -/
theorem pair_pencil_aligned_floor
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    {γ γ' : F} (hγ : γ ∈ G) (hγ' : γ' ∈ G) (hne : γ ≠ γ') :
    (pf γ = pencilBase γ γ' (pf γ) (pf γ') + γ • pencilDir γ γ' (pf γ) (pf γ') ∧
     pf γ' = pencilBase γ γ' (pf γ) (pf γ') + γ' • pencilDir γ γ' (pf γ) (pf γ')) ∧
    Sf γ ∩ Sf γ' ⊆
      alignedSet u₀ u₁ (pencilBase γ γ' (pf γ) (pf γ'))
        (pencilDir γ γ' (pf γ) (pf γ')) ∧
    2 * predecessorThreshold - N ≤ (Sf γ ∩ Sf γ').card := by
  classical
  obtain ⟨hc, _hm, hagree, _⟩ := hdata γ hγ
  obtain ⟨hc', _hm', hagree', _⟩ := hdata γ' hγ'
  refine ⟨⟨(pencil_reproduces_first γ γ' (pf γ) (pf γ')).symm,
      (pencil_reproduces_second hne (pf γ) (pf γ')).symm⟩, ?_, ?_⟩
  · intro i hi
    have h := pencil_agrees_on_inter hne
      (fun j hj => by simpa [smul_eq_mul] using hagree j hj)
      (fun j hj => by simpa [smul_eq_mul] using hagree' j hj) i hi
    exact (mem_alignedSet_iff u₀ u₁ _ _ i).mpr h
  · have hu := Finset.card_union_add_card_inter (Sf γ) (Sf γ')
    have hN : (Sf γ ∪ Sf γ').card ≤ N := by
      have h := Finset.card_le_univ (Sf γ ∪ Sf γ')
      simpa [Finset.card_univ, Fintype.card_fin] using h
    omega

/-- The floor constant: `2T − N = 111848108`. -/
theorem pairPencil_floor_constant : 2 * predecessorThreshold - N = 111848108 := by
  norm_num [predecessorThreshold_eq, N]

end PairPencil

/-! ## The margin-free four-pencil pair-cover budget -/

section FourCover

variable (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
variable (G : Finset F) (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)

/-- **The pair pigeonhole budget**: if every PAIR of scalars in a bad family rides
one of FOUR pencils, then `#bad² ≤ 4c²` (`c = 480946859` the unconditional rider
cap), hence `#bad ≤ 2c = 961893718 ≤ N`.  No margin, alignment, or pool
hypotheses. -/
theorem stall_budget_of_four_pair_pencil_cover
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    {wa₀ wa₁ wb₀ wb₁ wc₀ wc₁ wd₀ wd₁ : Fin N → F}
    (hwa₀ : wa₀ ∈ predecessorCode dom) (hwa₁ : wa₁ ∈ predecessorCode dom)
    (hwb₀ : wb₀ ∈ predecessorCode dom) (hwb₁ : wb₁ ∈ predecessorCode dom)
    (hwc₀ : wc₀ ∈ predecessorCode dom) (hwc₁ : wc₁ ∈ predecessorCode dom)
    (hwd₀ : wd₀ ∈ predecessorCode dom) (hwd₁ : wd₁ ∈ predecessorCode dom)
    (hpair : ∀ γ ∈ G, ∀ γ' ∈ G, γ ≠ γ' →
      (pf γ = wa₀ + γ • wa₁ ∧ pf γ' = wa₀ + γ' • wa₁) ∨
      (pf γ = wb₀ + γ • wb₁ ∧ pf γ' = wb₀ + γ' • wb₁) ∨
      (pf γ = wc₀ + γ • wc₁ ∧ pf γ' = wc₀ + γ' • wc₁) ∨
      (pf γ = wd₀ + γ • wd₁ ∧ pf γ' = wd₀ + γ' • wd₁)) :
    G.card ≤ N := by
  classical
  rcases Nat.lt_or_ge G.card 2 with hB | hB
  · have hN : 2 ≤ N := by norm_num [N]
    omega
  set Ga := G.filter (fun γ => pf γ = wa₀ + γ • wa₁) with hGa
  set Gb := G.filter (fun γ => pf γ = wb₀ + γ • wb₁) with hGb
  set Gc := G.filter (fun γ => pf γ = wc₀ + γ • wc₁) with hGc
  set Gd := G.filter (fun γ => pf γ = wd₀ + γ • wd₁) with hGd
  have hcap : ∀ (w₀ w₁ : Fin N → F), w₀ ∈ predecessorCode dom →
      w₁ ∈ predecessorCode dom →
      (G.filter (fun γ => pf γ = w₀ + γ • w₁)).card ≤ 480946859 := by
    intro w₀ w₁ hw₀ hw₁
    exact riders_card_le_uniform dom u₀ u₁ w₀ w₁ _ Sf hw₀ hw₁
      (ridesAll_of_pencil_subfamily dom u₀ u₁ G Sf pf hdata
        (Finset.filter_subset _ _) (fun γ hγ => (Finset.mem_filter.mp hγ).2))
  -- the ordered square is covered by the four rider squares
  have hsub : G ×ˢ G ⊆
      ((Ga ×ˢ Ga) ∪ (Gb ×ˢ Gb)) ∪ ((Gc ×ˢ Gc) ∪ (Gd ×ˢ Gd)) := by
    rintro ⟨γ, γ'⟩ hp
    have hγ : γ ∈ G := (Finset.mem_product.mp hp).1
    have hγ' : γ' ∈ G := (Finset.mem_product.mp hp).2
    by_cases hne : γ = γ'
    · -- diagonal: pair γ with a DIFFERENT element to place it in some class
      subst hne
      obtain ⟨δ, hδ, hδne⟩ : ∃ δ ∈ G, δ ≠ γ := by
        by_contra hall
        push Not at hall
        have : G ⊆ {γ} := fun x hx => Finset.mem_singleton.mpr (hall x hx)
        have := Finset.card_le_card this
        simp at this
        omega
      rcases hpair γ hγ δ hδ (fun h => hδne h.symm) with ⟨h1, _⟩ | ⟨h1, _⟩ |
        ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hγ, h1⟩,
            Finset.mem_filter.mpr ⟨hγ, h1⟩⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hγ, h1⟩,
            Finset.mem_filter.mpr ⟨hγ, h1⟩⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hγ, h1⟩,
            Finset.mem_filter.mpr ⟨hγ, h1⟩⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hγ, h1⟩,
            Finset.mem_filter.mpr ⟨hγ, h1⟩⟩))
    · rcases hpair γ hγ γ' hγ' hne with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hγ, h1⟩,
            Finset.mem_filter.mpr ⟨hγ', h2⟩⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hγ, h1⟩,
            Finset.mem_filter.mpr ⟨hγ', h2⟩⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hγ, h1⟩,
            Finset.mem_filter.mpr ⟨hγ', h2⟩⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hγ, h1⟩,
            Finset.mem_filter.mpr ⟨hγ', h2⟩⟩))
  have hBB : G.card * G.card ≤ 4 * (480946859 * 480946859) := by
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_product] at hcard
    have h1 : (((Ga ×ˢ Ga) ∪ (Gb ×ˢ Gb)) ∪ ((Gc ×ˢ Gc) ∪ (Gd ×ˢ Gd))).card ≤
        Ga.card * Ga.card + Gb.card * Gb.card +
        (Gc.card * Gc.card + Gd.card * Gd.card) := by
      calc (((Ga ×ˢ Ga) ∪ (Gb ×ˢ Gb)) ∪ ((Gc ×ˢ Gc) ∪ (Gd ×ˢ Gd))).card
          ≤ ((Ga ×ˢ Ga) ∪ (Gb ×ˢ Gb)).card + ((Gc ×ˢ Gc) ∪ (Gd ×ˢ Gd)).card :=
            Finset.card_union_le _ _
        _ ≤ ((Ga ×ˢ Ga).card + (Gb ×ˢ Gb).card) +
            ((Gc ×ˢ Gc).card + (Gd ×ˢ Gd).card) :=
            Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _)
        _ = Ga.card * Ga.card + Gb.card * Gb.card +
            (Gc.card * Gc.card + Gd.card * Gd.card) := by
            simp [Finset.card_product]
    have ha := hcap wa₀ wa₁ hwa₀ hwa₁
    have hb := hcap wb₀ wb₁ hwb₀ hwb₁
    have hc := hcap wc₀ wc₁ hwc₀ hwc₁
    have hd := hcap wd₀ wd₁ hwd₀ hwd₁
    rw [← hGa] at ha
    rw [← hGb] at hb
    rw [← hGc] at hc
    rw [← hGd] at hd
    have hmul : ∀ m : ℕ, m ≤ 480946859 → m * m ≤ 480946859 * 480946859 :=
      fun m hm => Nat.mul_le_mul hm hm
    have := hmul _ ha
    have := hmul _ hb
    have := hmul _ hc
    have := hmul _ hd
    omega
  -- B² ≤ 4c² forces B ≤ 2c ≤ N
  by_contra hover
  push Not at hover
  have hN : N = 1073741824 := by norm_num [N]
  have hge : 1073741825 ≤ G.card := by omega
  have hsq : 1073741825 * 1073741825 ≤ G.card * G.card :=
    Nat.mul_le_mul hge hge
  omega

/-- **Contrapositive**: an over-budget bad family admits NO four-pencil pair-cover
— its pairs must spread over at least five distinct pencils (the probe's extremal
families use thousands). -/
theorem overBudget_no_four_pencil_pair_cover
    (hdata : BadFamilyData dom u₀ u₁ G Sf pf)
    (hover : N + 1 ≤ G.card)
    {wa₀ wa₁ wb₀ wb₁ wc₀ wc₁ wd₀ wd₁ : Fin N → F}
    (hwa₀ : wa₀ ∈ predecessorCode dom) (hwa₁ : wa₁ ∈ predecessorCode dom)
    (hwb₀ : wb₀ ∈ predecessorCode dom) (hwb₁ : wb₁ ∈ predecessorCode dom)
    (hwc₀ : wc₀ ∈ predecessorCode dom) (hwc₁ : wc₁ ∈ predecessorCode dom)
    (hwd₀ : wd₀ ∈ predecessorCode dom) (hwd₁ : wd₁ ∈ predecessorCode dom)
    (hpair : ∀ γ ∈ G, ∀ γ' ∈ G, γ ≠ γ' →
      (pf γ = wa₀ + γ • wa₁ ∧ pf γ' = wa₀ + γ' • wa₁) ∨
      (pf γ = wb₀ + γ • wb₁ ∧ pf γ' = wb₀ + γ' • wb₁) ∨
      (pf γ = wc₀ + γ • wc₁ ∧ pf γ' = wc₀ + γ' • wc₁) ∨
      (pf γ = wd₀ + γ • wd₁ ∧ pf γ' = wd₀ + γ' • wd₁)) :
    False := by
  have h := stall_budget_of_four_pair_pencil_cover dom u₀ u₁ G Sf pf hdata
    hwa₀ hwa₁ hwb₀ hwb₁ hwc₀ hwc₁ hwd₀ hwd₁ hpair
  omega

end FourCover

/-! ## Ledger arithmetic -/

/-- The pigeonhole ledger: `(2c+1)² > 4c²` (so `B² ≤ 4c² ⟹ B ≤ 2c`) and
`2c = 961893718 ≤ N`. -/
theorem pair_pigeonhole_ledger :
    4 * (480946859 * 480946859) < 961893719 * 961893719 ∧
    961893718 ≤ N := by
  constructor <;> norm_num [N]

/-- Five pencils no longer suffice: `(N+1)² ≤ 5c²` — the pair-pigeonhole route
caps at four pencils; beyond that the open content is the many-pencil regime. -/
theorem five_cover_insufficient :
    (N + 1) * (N + 1) ≤ 5 * (480946859 * 480946859) := by
  norm_num [N]

end ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCoverTheorem

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCoverTheorem

#print axioms pair_pencil_aligned_floor
#print axioms pairPencil_floor_constant
#print axioms stall_budget_of_four_pair_pencil_cover
#print axioms overBudget_no_four_pencil_pair_cover
#print axioms pair_pigeonhole_ledger
#print axioms five_cover_insufficient
