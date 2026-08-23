/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.RSWeightEnumerator
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

/-!
# The EXACT Reed–Solomon (MDS) weight enumerator (issues #82, #232)

`RSWeightEnumerator.lean` provides the support counts (`q^{deg−|S|}`) and the
weight-distribution **upper bound** `A_d ≤ C(n,d)·q^{d−(n−deg)}`.  This file
lands the **exact** enumerator by inclusion–exclusion
(`Finset.inclusion_exclusion_sum_inf_compl`):

* `card_evalSupport_subset` — `#{p : evalSupport p ⊆ S} = q^{deg − (n − |S|)}`
  (the support count as a filter cardinality);
* `card_evalSupport_eq` — **exact support count**: for any `T`,
  `#{p : evalSupport p = T} = Σ_{t ⊆ T} (−1)^{|t|}·q^{deg − (n − |T| + |t|)}`
  (ℤ-valued alternating sum);
* `card_evalWeight_eq` — **the exact MDS weight enumerator**:
  `A_d = C(n,d) · Σ_{j ≤ d} (−1)^j C(d,j) q^{deg − (n − d + j)}` — the
  classical closed form, now a theorem.  This is the O120/O122 lane's M2
  prerequisite: the distance distribution `B_d = q^deg·A_d` of the code,
  in-tree and exact.

Verified numerically (O109 census `probe_locus_incidence_census.py`: the MDS
closed form matches exhaustive enumeration at every tested `(q, n, k, w)`).
-/

namespace ArkLib.CS25

open Polynomial Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- The support count as a filter cardinality:
`#{p : evalSupport p ⊆ S} = q^{deg − (n − |S|)}`. -/
theorem card_evalSupport_subset (α : ι ↪ F) (deg : ℕ)
    [Fintype (Polynomial.degreeLT F deg)] (S : Finset ι) :
    (Finset.univ.filter
        (fun p : Polynomial.degreeLT F deg => evalSupport α p ⊆ S)).card
      = Fintype.card F ^ (deg - (Fintype.card ι - S.card)) := by
  classical
  haveI : Fintype (LinearMap.ker (evalOnS α deg Sᶜ)) := Fintype.ofFinite _
  have hbij : (Finset.univ.filter
        (fun p : Polynomial.degreeLT F deg => evalSupport α p ⊆ S)).card
      = Fintype.card (LinearMap.ker (evalOnS α deg Sᶜ)) := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr
      (Equiv.subtypeEquivRight (fun p => (mem_ker_evalOnS_compl_iff α deg S p).symm))
  rw [hbij, ← Nat.card_eq_fintype_card, natCard_ker_evalOnS_general,
    Finset.card_compl]

/-- **The exact support count** (inclusion–exclusion): the number of
degree-`< deg` polynomials with evaluation support EXACTLY `T` is the
alternating sum of support counts over removed subsets. -/
theorem card_evalSupport_eq (α : ι ↪ F) (deg : ℕ)
    [Fintype (Polynomial.degreeLT F deg)] (T : Finset ι) :
    ((Finset.univ.filter
        (fun p : Polynomial.degreeLT F deg => evalSupport α p = T)).card : ℤ)
      = ∑ t ∈ T.powerset, (-1 : ℤ) ^ t.card
          * (Fintype.card F : ℤ)
            ^ (deg - (Fintype.card ι - T.card + t.card)) := by
  classical
  set Sv : ι → Finset (Polynomial.degreeLT F deg) :=
    fun i => Finset.univ.filter (fun p => (p : F[X]).eval (α i) = 0) with hSv
  have hIE := Finset.inclusion_exclusion_sum_inf_compl (G := ℤ) T Sv
    (fun p => if evalSupport α p ⊆ T then (1 : ℤ) else 0)
  -- LHS of IE = the exact-support count
  have hmemSv : ∀ (i : ι) (p : Polynomial.degreeLT F deg),
      p ∈ Sv i ↔ (p : F[X]).eval (α i) = 0 := by
    intro i p
    rw [hSv, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hLHS : ∑ p ∈ T.inf fun i => (Sv i)ᶜ,
      (if evalSupport α p ⊆ T then (1 : ℤ) else 0)
      = ((Finset.univ.filter
          (fun p : Polynomial.degreeLT F deg => evalSupport α p = T)).card : ℤ) := by
    rw [Finset.sum_boole]
    congr 1
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_inf, Finset.mem_compl,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hnotin, hsub⟩
      apply Finset.Subset.antisymm hsub
      intro i hiT
      rw [evalSupport, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun h0 => ?_⟩
      exact hnotin i hiT ((hmemSv i p).mpr h0)
    · rintro rfl
      refine ⟨fun i hi hmem => ?_, Finset.Subset.refl _⟩
      have h0 := (hmemSv i p).mp hmem
      rw [evalSupport, Finset.mem_filter] at hi
      exact hi.2 h0
  -- RHS of IE: each inner sum is a subset-support count
  have hRHS : ∀ t ∈ T.powerset,
      (∑ p ∈ t.inf Sv, (if evalSupport α p ⊆ T then (1 : ℤ) else 0))
      = (Fintype.card F : ℤ)
          ^ (deg - (Fintype.card ι - T.card + t.card)) := by
    intro t ht
    have htT : t ⊆ T := Finset.mem_powerset.mp ht
    rw [Finset.sum_boole]
    have hset : (t.inf Sv).filter (fun p => evalSupport α p ⊆ T)
        = Finset.univ.filter
          (fun p : Polynomial.degreeLT F deg => evalSupport α p ⊆ T \ t) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_inf, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hvanish, hsub⟩
        intro i hi
        rw [Finset.mem_sdiff]
        refine ⟨hsub hi, fun hit => ?_⟩
        have h0 := (hmemSv i p).mp (hvanish i hit)
        rw [evalSupport, Finset.mem_filter] at hi
        exact hi.2 h0
      · intro hsub
        constructor
        · intro i hit
          rw [hmemSv i p]
          by_contra h0
          have hi : i ∈ evalSupport α p := by
            rw [evalSupport, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, h0⟩
          exact (Finset.mem_sdiff.mp (hsub hi)).2 hit
        · exact hsub.trans (Finset.sdiff_subset)
    rw [hset]
    have hcount := card_evalSupport_subset α deg (T \ t)
    have hcs : (T \ t).card = T.card - t.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr htT]
    rw [hcount, hcs]
    have harith : Fintype.card ι - (T.card - t.card)
        = Fintype.card ι - T.card + t.card := by
      have h1 : t.card ≤ T.card := Finset.card_le_card htT
      have h2 : T.card ≤ Fintype.card ι := Finset.card_le_univ T
      omega
    rw [harith]
    push_cast
    ring
  rw [hLHS] at hIE
  rw [hIE]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hRHS t ht, zsmul_eq_mul]
  push_cast
  ring

/-- **THE EXACT MDS WEIGHT ENUMERATOR**: the number of degree-`< deg`
polynomials of evaluation weight exactly `d` is
`C(n,d) · Σ_{j ≤ d} (−1)^j C(d,j) q^{deg − (n − d + j)}` — the classical
closed form as a theorem. -/
theorem card_evalWeight_eq (α : ι ↪ F) (deg : ℕ)
    [Fintype (Polynomial.degreeLT F deg)] (d : ℕ) :
    ((Finset.univ.filter
        (fun p : Polynomial.degreeLT F deg => (evalSupport α p).card = d)).card : ℤ)
      = ((Fintype.card ι).choose d : ℤ)
        * ∑ j ∈ Finset.range (d + 1), (-1 : ℤ) ^ j * (d.choose j : ℤ)
            * (Fintype.card F : ℤ)
              ^ (deg - (Fintype.card ι - d + j)) := by
  classical
  -- partition the weight-d filter by exact support
  have hpart : Finset.univ.filter
        (fun p : Polynomial.degreeLT F deg => (evalSupport α p).card = d)
      = (Finset.univ.powersetCard d).biUnion (fun T =>
          Finset.univ.filter
            (fun p : Polynomial.degreeLT F deg => evalSupport α p = T)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.mem_powersetCard]
    constructor
    · intro hcard
      exact ⟨evalSupport α p, ⟨Finset.subset_univ _, hcard⟩, rfl⟩
    · rintro ⟨T, ⟨_, hcard⟩, rfl⟩
      exact hcard
  have hdisj : ∀ T₁ ∈ Finset.univ.powersetCard d,
      ∀ T₂ ∈ Finset.univ.powersetCard d, T₁ ≠ T₂ →
      Disjoint (Finset.univ.filter
          (fun p : Polynomial.degreeLT F deg => evalSupport α p = T₁))
        (Finset.univ.filter
          (fun p : Polynomial.degreeLT F deg => evalSupport α p = T₂)) := by
    intro T₁ _ T₂ _ hne
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    exact hne ((Finset.mem_filter.mp hp₁).2 ▸ (Finset.mem_filter.mp hp₂).2 ▸ rfl)
  rw [hpart, Finset.card_biUnion hdisj]
  push_cast
  rw [Finset.sum_congr rfl (fun T _ => card_evalSupport_eq (F := F) α deg T)]
  -- each per-T sum depends only on |T| = d; regroup the powerset sum by size
  have hperT : ∀ T ∈ (Finset.univ : Finset ι).powersetCard d,
      (∑ t ∈ T.powerset, (-1 : ℤ) ^ t.card
        * (Fintype.card F : ℤ) ^ (deg - (Fintype.card ι - T.card + t.card)))
      = ∑ j ∈ Finset.range (d + 1), (-1 : ℤ) ^ j * (d.choose j : ℤ)
          * (Fintype.card F : ℤ) ^ (deg - (Fintype.card ι - d + j)) := by
    intro T hT
    obtain ⟨-, hTcard⟩ := Finset.mem_powersetCard.mp hT
    -- group the powerset sum by subset size
    rw [← hTcard]
    rw [Finset.sum_powerset]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hconst : ∀ t ∈ T.powersetCard j,
        (-1 : ℤ) ^ t.card
          * (Fintype.card F : ℤ) ^ (deg - (Fintype.card ι - T.card + t.card))
        = (-1 : ℤ) ^ j
          * (Fintype.card F : ℤ) ^ (deg - (Fintype.card ι - T.card + j)) := by
      intro t ht
      obtain ⟨-, htcard⟩ := Finset.mem_powersetCard.mp ht
      rw [htcard]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const,
      Finset.card_powersetCard, hTcard, nsmul_eq_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl hperT, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, nsmul_eq_mul]

end ArkLib.CS25
