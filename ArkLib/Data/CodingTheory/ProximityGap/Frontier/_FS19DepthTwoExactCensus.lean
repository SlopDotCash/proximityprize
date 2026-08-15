/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS13PairingInductionWick

/-!
# LANE FS19 (#466, Fable session 2026-07-09): THE EXACT DEPTH-2 CENSUS —
  `zeroSumCount m 4 = 12m² − 6m`, by three-pairing inclusion–exclusion

The exact analog at depth 2 of the swarm's depth-3 strata count, from the FS machinery
alone.  A zero-sum 4-tuple decomposes into two `m`-shift-cancelling pairs under one of the
THREE perfect pairings `{01|23}, {02|13}, {03|12}`; each pairing class has `(2m)²` members,
the pairwise intersections have `2m`, and the triple intersection is EMPTY (it would force
`c₀ = shift c₀`).  Inclusion–exclusion:

  `Z(4) = 3(2m)² − 3(2m) = 12m² − 6m`,

independently confirming the in-tree carrier value `B 4 m = E₂(2m) = 12m² − 6m`
(`CharZeroEnergyThreeExact`) — now unconditional for the concrete count.  Via FS12,
`trivialCountG m 2 = 12m² − 6m`, so at every FS14 good prime `rEnergy (μ_n) 2` takes this
exact value.

Issue #466, lane FS19.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.FS19DepthTwoExactCensus

open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition
open ArkLib.ProximityGap.Frontier.FS11GenericDepthDecomposition
open ArkLib.ProximityGap.Frontier.FS12ZeroSumCountBijection
open ArkLib.ProximityGap.Frontier.FS13PairingInductionWick

open scoped Classical

variable {m : ℕ}

/-- Folded monomials are injective on `[0, 2m)`. -/
theorem monomF_injOn {x y : ℕ} (hx : x < 2 * m) (hy : y < 2 * m)
    (h : monomF m x = monomF m y) : x = y := by
  have hm : 0 < m := by omega
  by_cases hxm : x < m
  · have hc : (monomF m x).coeff x = (monomF m y).coeff x := by rw [h]
    rw [monomF_coeff_eq hx hxm, monomF_coeff_eq hy hxm] at hc
    simp only [if_pos rfl, if_neg (by omega : ¬ x = x + m)] at hc
    by_cases h1 : y = x
    · omega
    · by_cases h2 : y = x + m
      · rw [if_neg h1, if_pos h2] at hc
        norm_num at hc
      · rw [if_neg h1, if_neg h2] at hc
        norm_num at hc
  · have hres : x - m < m := by omega
    have hc : (monomF m x).coeff (x - m) = (monomF m y).coeff (x - m) := by rw [h]
    rw [monomF_coeff_eq hx hres, monomF_coeff_eq hy hres] at hc
    simp only [if_neg (by omega : ¬ x = x - m), if_pos (by omega : x = x - m + m)] at hc
    by_cases h1 : y = x - m
    · rw [if_pos h1, if_neg (by omega : ¬ y = x - m + m)] at hc
      norm_num at hc
    · by_cases h2 : y = x - m + m
      · omega
      · rw [if_neg h1, if_neg h2] at hc
        norm_num at hc

/-- A cancelling pair is an `m`-shift pair. -/
theorem eq_mshift_of_add_eq_zero {x y : ℕ} (hx : x < 2 * m) (hy : y < 2 * m)
    (h : monomF m x + monomF m y = 0) : y = mshift m x := by
  have hy' : monomF m y = monomF m (mshift m x) := by
    rw [monomF_mshift hx]
    linear_combination h
  exact monomF_injOn hy (mshift_lt hx) hy'

/-- The three pairing classes. -/
noncomputable def pairA (m : ℕ) : Finset (Fin 4 → ℕ) :=
  (expTuples (2 * m) 4).filter (fun c => c 1 = mshift m (c 0) ∧ c 3 = mshift m (c 2))

noncomputable def pairB (m : ℕ) : Finset (Fin 4 → ℕ) :=
  (expTuples (2 * m) 4).filter (fun c => c 2 = mshift m (c 0) ∧ c 3 = mshift m (c 1))

noncomputable def pairC (m : ℕ) : Finset (Fin 4 → ℕ) :=
  (expTuples (2 * m) 4).filter (fun c => c 3 = mshift m (c 0) ∧ c 2 = mshift m (c 1))

theorem mshift_ne_self (hm : 0 < m) (a : ℕ) : mshift m a ≠ a := by
  unfold mshift
  split_ifs <;> omega

/-- **The pairing classification.**  A 4-tuple is zero-sum iff one of the three perfect
pairings cancels. -/
theorem zero_sum_iff_pairings (hm : 0 < m) (c : Fin 4 → ℕ) (hc : ∀ i, c i < 2 * m) :
    ((∑ i, monomF m (c i)) = 0) ↔
      ((c 1 = mshift m (c 0) ∧ c 3 = mshift m (c 2)) ∨
       (c 2 = mshift m (c 0) ∧ c 3 = mshift m (c 1)) ∨
       (c 3 = mshift m (c 0) ∧ c 2 = mshift m (c 1))) := by
  constructor
  · intro hzero
    obtain ⟨j, hj0, hjval⟩ := exists_partner hm c hc hzero 0
    have hsum := hzero
    rw [Fin.sum_univ_four] at hsum
    fin_cases j
    · exact absurd rfl hj0
    · left
      refine ⟨hjval, ?_⟩
      have hjval' : c 1 = mshift m (c 0) := by simpa using hjval
      have h01 : monomF m (c 1) = -(monomF m (c 0)) := by
        rw [hjval', monomF_mshift (hc 0)]
      have hpair : monomF m (c 2) + monomF m (c 3) = 0 := by
        linear_combination hsum - h01
      exact eq_mshift_of_add_eq_zero (hc 2) (hc 3) hpair
    · right; left
      refine ⟨hjval, ?_⟩
      have hjval' : c 2 = mshift m (c 0) := by simpa using hjval
      have h02 : monomF m (c 2) = -(monomF m (c 0)) := by
        rw [hjval', monomF_mshift (hc 0)]
      have hpair : monomF m (c 1) + monomF m (c 3) = 0 := by
        linear_combination hsum - h02
      exact eq_mshift_of_add_eq_zero (hc 1) (hc 3) hpair
    · right; right
      refine ⟨hjval, ?_⟩
      have hjval' : c 3 = mshift m (c 0) := by simpa using hjval
      have h03 : monomF m (c 3) = -(monomF m (c 0)) := by
        rw [hjval', monomF_mshift (hc 0)]
      have hpair : monomF m (c 1) + monomF m (c 2) = 0 := by
        linear_combination hsum - h03
      exact eq_mshift_of_add_eq_zero (hc 1) (hc 2) hpair
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      rw [Fin.sum_univ_four, h1, h2, monomF_mshift (hc _), monomF_mshift (hc _)] <;>
      ring

/-- The zero-sum set is the union of the three pairing classes. -/
theorem filter_eq_union (hm : 0 < m) :
    (expTuples (2 * m) 4).filter (fun c => (∑ i, monomF m (c i)) = 0)
      = pairA m ∪ pairB m ∪ pairC m := by
  ext c
  simp only [pairA, pairB, pairC, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro ⟨hmem, hzero⟩
    have hc : ∀ i, c i < 2 * m := by
      rw [expTuples, Fintype.mem_piFinset] at hmem
      exact fun i => mem_range.mp (hmem i)
    rcases (zero_sum_iff_pairings hm c hc).mp hzero with h | h | h
    · exact Or.inl (Or.inl ⟨hmem, h⟩)
    · exact Or.inl (Or.inr ⟨hmem, h⟩)
    · exact Or.inr ⟨hmem, h⟩
  · rintro ((⟨hmem, h⟩ | ⟨hmem, h⟩) | ⟨hmem, h⟩) <;>
      refine ⟨hmem, ?_⟩ <;>
      have hc : ∀ i, c i < 2 * m := by
        rw [expTuples, Fintype.mem_piFinset] at hmem
        exact fun i => mem_range.mp (hmem i)
    · exact (zero_sum_iff_pairings hm c hc).mpr (Or.inl h)
    · exact (zero_sum_iff_pairings hm c hc).mpr (Or.inr (Or.inl h))
    · exact (zero_sum_iff_pairings hm c hc).mpr (Or.inr (Or.inr h))

/-! ## Cardinalities of the classes -/

/-- Membership rebuild helper: a function-tuple is in `expTuples` iff all values are in range. -/
theorem mem_expTuples_iff {n N : ℕ} (c : Fin N → ℕ) :
    c ∈ expTuples n N ↔ ∀ i, c i < n := by
  rw [expTuples, Fintype.mem_piFinset]
  simp only [mem_range]

theorem pairA_card (hm : 0 < m) : (pairA m).card = (2 * m) * (2 * m) := by
  have : (pairA m).card = ((range (2 * m)) ×ˢ (range (2 * m))).card := by
    refine Finset.card_bij (fun c _ => (c 0, c 2)) ?_ ?_ ?_
    · rintro c hcmem
      simp only [pairA, Finset.mem_filter, mem_expTuples_iff] at hcmem
      rw [Finset.mem_product]
      exact ⟨mem_range.mpr (hcmem.1 0), mem_range.mpr (hcmem.1 2)⟩
    · rintro c hcmem c' hcmem' heq
      dsimp only at heq
      simp only [pairA, Finset.mem_filter] at hcmem hcmem'
      have h0 : c 0 = c' 0 := congrArg Prod.fst heq
      have h2 : c 2 = c' 2 := congrArg Prod.snd heq
      funext i
      fin_cases i
      · show c 0 = c' 0
        exact h0
      · show c 1 = c' 1
        rw [hcmem.2.1, hcmem'.2.1, h0]
      · show c 2 = c' 2
        exact h2
      · show c 3 = c' 3
        rw [hcmem.2.2, hcmem'.2.2, h2]
    · rintro ⟨a, b⟩ hab
      rw [Finset.mem_product] at hab
      have ha := mem_range.mp hab.1
      have hb := mem_range.mp hab.2
      refine ⟨![a, mshift m a, b, mshift m b], ?_, rfl⟩
      simp only [pairA, Finset.mem_filter, mem_expTuples_iff]
      refine ⟨fun i => ?_, rfl, rfl⟩
      fin_cases i
      · exact ha
      · exact mshift_lt ha
      · exact hb
      · exact mshift_lt hb
  rw [this, Finset.card_product, Finset.card_range]

theorem pairB_card (hm : 0 < m) : (pairB m).card = (2 * m) * (2 * m) := by
  have : (pairB m).card = ((range (2 * m)) ×ˢ (range (2 * m))).card := by
    refine Finset.card_bij (fun c _ => (c 0, c 1)) ?_ ?_ ?_
    · rintro c hcmem
      simp only [pairB, Finset.mem_filter, mem_expTuples_iff] at hcmem
      rw [Finset.mem_product]
      exact ⟨mem_range.mpr (hcmem.1 0), mem_range.mpr (hcmem.1 1)⟩
    · rintro c hcmem c' hcmem' heq
      dsimp only at heq
      simp only [pairB, Finset.mem_filter] at hcmem hcmem'
      have h0 : c 0 = c' 0 := congrArg Prod.fst heq
      have h1 : c 1 = c' 1 := congrArg Prod.snd heq
      funext i
      fin_cases i
      · show c 0 = c' 0
        exact h0
      · show c 1 = c' 1
        exact h1
      · show c 2 = c' 2
        rw [hcmem.2.1, hcmem'.2.1, h0]
      · show c 3 = c' 3
        rw [hcmem.2.2, hcmem'.2.2, h1]
    · rintro ⟨a, b⟩ hab
      rw [Finset.mem_product] at hab
      have ha := mem_range.mp hab.1
      have hb := mem_range.mp hab.2
      refine ⟨![a, b, mshift m a, mshift m b], ?_, rfl⟩
      simp only [pairB, Finset.mem_filter, mem_expTuples_iff]
      refine ⟨fun i => ?_, rfl, rfl⟩
      fin_cases i
      · exact ha
      · exact hb
      · exact mshift_lt ha
      · exact mshift_lt hb
  rw [this, Finset.card_product, Finset.card_range]

theorem pairC_card (hm : 0 < m) : (pairC m).card = (2 * m) * (2 * m) := by
  have : (pairC m).card = ((range (2 * m)) ×ˢ (range (2 * m))).card := by
    refine Finset.card_bij (fun c _ => (c 0, c 1)) ?_ ?_ ?_
    · rintro c hcmem
      simp only [pairC, Finset.mem_filter, mem_expTuples_iff] at hcmem
      rw [Finset.mem_product]
      exact ⟨mem_range.mpr (hcmem.1 0), mem_range.mpr (hcmem.1 1)⟩
    · rintro c hcmem c' hcmem' heq
      dsimp only at heq
      simp only [pairC, Finset.mem_filter] at hcmem hcmem'
      have h0 : c 0 = c' 0 := congrArg Prod.fst heq
      have h1 : c 1 = c' 1 := congrArg Prod.snd heq
      funext i
      fin_cases i
      · show c 0 = c' 0
        exact h0
      · show c 1 = c' 1
        exact h1
      · show c 2 = c' 2
        rw [hcmem.2.2, hcmem'.2.2, h1]
      · show c 3 = c' 3
        rw [hcmem.2.1, hcmem'.2.1, h0]
    · rintro ⟨a, b⟩ hab
      rw [Finset.mem_product] at hab
      have ha := mem_range.mp hab.1
      have hb := mem_range.mp hab.2
      refine ⟨![a, b, mshift m b, mshift m a], ?_, rfl⟩
      simp only [pairC, Finset.mem_filter, mem_expTuples_iff]
      refine ⟨fun i => ?_, rfl, rfl⟩
      fin_cases i
      · exact ha
      · exact hb
      · exact mshift_lt hb
      · exact mshift_lt ha
  rw [this, Finset.card_product, Finset.card_range]

/-! ## Intersections -/

theorem interAB_card (hm : 0 < m) : (pairA m ∩ pairB m).card = 2 * m := by
  have : (pairA m ∩ pairB m).card = (range (2 * m)).card := by
    refine Finset.card_bij (fun c _ => c 0) ?_ ?_ ?_
    · rintro c hcmem
      rw [Finset.mem_inter] at hcmem
      simp only [pairA, Finset.mem_filter, mem_expTuples_iff] at hcmem
      exact mem_range.mpr (hcmem.1.1 0)
    · rintro c hcmem c' hcmem' heq
      dsimp only at heq
      rw [Finset.mem_inter] at hcmem hcmem'
      simp only [pairA, pairB, Finset.mem_filter, mem_expTuples_iff] at hcmem hcmem'
      funext i
      fin_cases i
      · show c 0 = c' 0
        exact heq
      · show c 1 = c' 1
        rw [hcmem.1.2.1, hcmem'.1.2.1, heq]
      · show c 2 = c' 2
        rw [hcmem.2.2.1, hcmem'.2.2.1, heq]
      · show c 3 = c' 3
        rw [hcmem.1.2.2, hcmem.2.2.1, hcmem'.1.2.2, hcmem'.2.2.1, heq]
    · rintro a ha
      have ha' := mem_range.mp ha
      refine ⟨![a, mshift m a, mshift m a, a], ?_, rfl⟩
      rw [Finset.mem_inter]
      constructor
      · simp only [pairA, Finset.mem_filter, mem_expTuples_iff]
        refine ⟨fun i => ?_, rfl, ?_⟩
        · fin_cases i
          · exact ha'
          · exact mshift_lt ha'
          · exact mshift_lt ha'
          · exact ha'
        · show a = mshift m (mshift m a)
          exact (mshift_involutive ha').symm
      · simp only [pairB, Finset.mem_filter, mem_expTuples_iff]
        refine ⟨fun i => ?_, rfl, ?_⟩
        · fin_cases i
          · exact ha'
          · exact mshift_lt ha'
          · exact mshift_lt ha'
          · exact ha'
        · show a = mshift m (mshift m a)
          exact (mshift_involutive ha').symm
  rw [this, Finset.card_range]

theorem interAC_card (hm : 0 < m) : (pairA m ∩ pairC m).card = 2 * m := by
  have : (pairA m ∩ pairC m).card = (range (2 * m)).card := by
    refine Finset.card_bij (fun c _ => c 0) ?_ ?_ ?_
    · rintro c hcmem
      rw [Finset.mem_inter] at hcmem
      simp only [pairA, Finset.mem_filter, mem_expTuples_iff] at hcmem
      exact mem_range.mpr (hcmem.1.1 0)
    · rintro c hcmem c' hcmem' heq
      dsimp only at heq
      rw [Finset.mem_inter] at hcmem hcmem'
      simp only [pairA, pairC, Finset.mem_filter, mem_expTuples_iff] at hcmem hcmem'
      funext i
      fin_cases i
      · show c 0 = c' 0
        exact heq
      · show c 1 = c' 1
        rw [hcmem.1.2.1, hcmem'.1.2.1, heq]
      · show c 2 = c' 2
        rw [hcmem.2.2.2, hcmem.1.2.1, hcmem'.2.2.2, hcmem'.1.2.1, heq]
      · show c 3 = c' 3
        rw [hcmem.2.2.1, hcmem'.2.2.1, heq]
    · rintro a ha
      have ha' := mem_range.mp ha
      refine ⟨![a, mshift m a, a, mshift m a], ?_, rfl⟩
      rw [Finset.mem_inter]
      constructor
      · simp only [pairA, Finset.mem_filter, mem_expTuples_iff]
        refine ⟨fun i => ?_, rfl, ?_⟩
        · fin_cases i
          · exact ha'
          · exact mshift_lt ha'
          · exact ha'
          · exact mshift_lt ha'
        · rfl
      · simp only [pairC, Finset.mem_filter, mem_expTuples_iff]
        refine ⟨fun i => ?_, rfl, ?_⟩
        · fin_cases i
          · exact ha'
          · exact mshift_lt ha'
          · exact ha'
          · exact mshift_lt ha'
        · show a = mshift m (mshift m a)
          exact (mshift_involutive ha').symm
  rw [this, Finset.card_range]

theorem interBC_card (hm : 0 < m) : (pairB m ∩ pairC m).card = 2 * m := by
  have : (pairB m ∩ pairC m).card = (range (2 * m)).card := by
    refine Finset.card_bij (fun c _ => c 0) ?_ ?_ ?_
    · rintro c hcmem
      rw [Finset.mem_inter] at hcmem
      simp only [pairB, Finset.mem_filter, mem_expTuples_iff] at hcmem
      exact mem_range.mpr (hcmem.1.1 0)
    · rintro c hcmem c' hcmem' heq
      dsimp only at heq
      rw [Finset.mem_inter] at hcmem hcmem'
      simp only [pairB, pairC, Finset.mem_filter, mem_expTuples_iff] at hcmem hcmem'
      -- from B: c2 = sh c0, c3 = sh c1; from C: c3 = sh c0, c2 = sh c1 → c0 = c1
      have h01 : c 1 = c 0 := by
        have hB := hcmem.1.2.2
        have hC := hcmem.2.2.1
        have : mshift m (c 1) = mshift m (c 0) := by rw [← hB, hC]
        have hlt1 : c 1 < 2 * m := hcmem.1.1 1
        have hlt0 : c 0 < 2 * m := hcmem.1.1 0
        calc c 1 = mshift m (mshift m (c 1)) := (mshift_involutive hlt1).symm
          _ = mshift m (mshift m (c 0)) := by rw [this]
          _ = c 0 := mshift_involutive hlt0
      have h01' : c' 1 = c' 0 := by
        have hB := hcmem'.1.2.2
        have hC := hcmem'.2.2.1
        have : mshift m (c' 1) = mshift m (c' 0) := by rw [← hB, hC]
        have hlt1 : c' 1 < 2 * m := hcmem'.1.1 1
        have hlt0 : c' 0 < 2 * m := hcmem'.1.1 0
        calc c' 1 = mshift m (mshift m (c' 1)) := (mshift_involutive hlt1).symm
          _ = mshift m (mshift m (c' 0)) := by rw [this]
          _ = c' 0 := mshift_involutive hlt0
      funext i
      fin_cases i
      · show c 0 = c' 0
        exact heq
      · show c 1 = c' 1
        rw [h01, h01', heq]
      · show c 2 = c' 2
        rw [hcmem.1.2.1, hcmem'.1.2.1, heq]
      · show c 3 = c' 3
        rw [hcmem.2.2.1, hcmem'.2.2.1, heq]
    · rintro a ha
      have ha' := mem_range.mp ha
      refine ⟨![a, a, mshift m a, mshift m a], ?_, rfl⟩
      rw [Finset.mem_inter]
      constructor
      · simp only [pairB, Finset.mem_filter, mem_expTuples_iff]
        exact ⟨fun i => by fin_cases i <;> first | exact ha' | exact mshift_lt ha', rfl, rfl⟩
      · simp only [pairC, Finset.mem_filter, mem_expTuples_iff]
        exact ⟨fun i => by fin_cases i <;> first | exact ha' | exact mshift_lt ha', rfl, rfl⟩
  rw [this, Finset.card_range]

theorem triple_empty (hm : 0 < m) : pairA m ∩ pairB m ∩ pairC m = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro c hc
  rw [Finset.mem_inter, Finset.mem_inter] at hc
  simp only [pairA, pairB, pairC, Finset.mem_filter, mem_expTuples_iff] at hc
  -- A: c1 = sh c0; B: c3 = sh c1; C: c3 = sh c0 → sh c1 = sh c0 → c1 = c0 = sh c0: absurd
  have hA := hc.1.1.2.1
  have hB := hc.1.2.2.2
  have hC := hc.2.2.1
  have hlt0 : c 0 < 2 * m := hc.1.1.1 0
  have hlt1 : c 1 < 2 * m := hc.1.1.1 1
  have h01 : c 1 = c 0 := by
    have : mshift m (c 1) = mshift m (c 0) := by rw [← hB, hC]
    calc c 1 = mshift m (mshift m (c 1)) := (mshift_involutive hlt1).symm
      _ = mshift m (mshift m (c 0)) := by rw [this]
      _ = c 0 := mshift_involutive hlt0
  rw [h01] at hA
  exact mshift_ne_self hm (c 0) hA.symm

/-- **THE EXACT DEPTH-2 CENSUS.**  `zeroSumCount m 4 = 12m² − 6m`. -/
theorem zeroSumCount_four (hm : 0 < m) :
    zeroSumCount m 4 = 12 * m ^ 2 - 6 * m := by
  unfold zeroSumCount
  rw [filter_eq_union hm]
  have hAB := Finset.card_union_add_card_inter (pairA m) (pairB m)
  have hABC := Finset.card_union_add_card_inter (pairA m ∪ pairB m) (pairC m)
  have hdist : (pairA m ∪ pairB m) ∩ pairC m
      = (pairA m ∩ pairC m) ∪ (pairB m ∩ pairC m) :=
    Finset.union_inter_distrib_right _ _ _
  have hACBC := Finset.card_union_add_card_inter (pairA m ∩ pairC m) (pairB m ∩ pairC m)
  have hsub : (pairA m ∩ pairC m) ∩ (pairB m ∩ pairC m) ⊆ pairA m ∩ pairB m ∩ pairC m := by
    intro c hc
    simp only [Finset.mem_inter] at hc ⊢
    exact ⟨⟨hc.1.1, hc.2.1⟩, hc.1.2⟩
  have hzero : ((pairA m ∩ pairC m) ∩ (pairB m ∩ pairC m)).card = 0 := by
    have := Finset.card_le_card hsub
    rw [triple_empty hm] at this
    simpa using this
  have hA := pairA_card (m := m) hm
  have hB := pairB_card (m := m) hm
  have hC := pairC_card (m := m) hm
  have hab := interAB_card (m := m) hm
  have hac := interAC_card (m := m) hm
  have hbc := interBC_card (m := m) hm
  rw [hdist] at hABC
  rw [hzero] at hACBC
  have hK : (2 * m) * (2 * m) = 4 * m ^ 2 := by ring
  rw [hK] at hA hB hC
  have hmm : m ≤ m ^ 2 := by nlinarith
  have hm1 : 1 ≤ m := hm
  -- all remaining relations are linear in the atoms {cards, m, m^2}
  generalize m ^ 2 = M2 at *
  omega

/-- **The depth-2 concrete census, two-sided form.**  `trivialCountG m 2 = 12m² − 6m`,
hence at every FS14 good prime `rEnergy (μ_n) 2` takes exactly this value. -/
theorem trivialCountG_two (hm : 0 < m) :
    trivialCountG m 2 = 12 * m ^ 2 - 6 * m := by
  rw [trivialCountG_eq_zeroSumCount m 2, show (2 + 2 : ℕ) = 4 from rfl]
  exact zeroSumCount_four hm

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms monomF_injOn
#print axioms zero_sum_iff_pairings
#print axioms zeroSumCount_four
#print axioms trivialCountG_two

end ArkLib.ProximityGap.Frontier.FS19DepthTwoExactCensus
