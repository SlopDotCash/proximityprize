/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BandCollapse
import ArkLib.Data.CodingTheory.ProximityGap.GeneralSpikeLowerBound

/-!
# The exact staircase: `ε_mca(RS, j/n) = (j+1)/q` on every in-hypothesis band

The assembly of the two proven sides of the staircase law into a single named exactness
theorem for Reed–Solomon codes:

* the **upper** side is the band collapse (`epsMCA_le_band`, O153 — at most `j+1` bad
  scalars when every nonzero codeword has weight `> 3j`), instantiated via the elementary
  RS weight bound `rs_nonzero_wt_lower` (a nonzero degree-`< k` evaluation has at most
  `k − 1` zeros on an injective domain);
* the **lower** side is the in-tree general-`j` spike bound (`epsMCA_generalJ_ge`).

Result: **`epsMCA_band_exact`** — for `3j < n − k + 1` (and the spike's mild size
conditions), `ε_mca(RS[F, domain, k], j/n) = (j+1)/q` **exactly**. The staircase side of
the two-family profile law (O147) is now a single machine-checked equality at every
in-hypothesis band; for production RS the hypothesis covers `δ` up to a third of the
distance. The remaining conjectural regime of the profile law is the census band alone.

## References
* Issue #357 (surface (i)); DISPROOF_LOG O153; `BandCollapse.lean`,
  `GeneralSpikeLowerBound.lean`.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.BandCollapse

open scoped NNReal ProbabilityTheory ENNReal
open ProximityGap Code Finset GrandChallengesLattice

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The elementary RS weight bound:** a nonzero codeword of `ReedSolomon.code domain k`
(injective domain) has weight at least `n − (k − 1)`: its underlying polynomial is nonzero
of degree `< k`, so it vanishes at most `k − 1` of the `n` evaluation points. -/
theorem rs_nonzero_wt_lower (domain : ι ↪ F) {k : ℕ}
    {c : ι → F} (hc : c ∈ ReedSolomon.code domain k) (hne : c ≠ 0) :
    Fintype.card ι - (k - 1) ≤ wt c := by
  classical
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hc
  have hpne : p ≠ 0 := by
    intro h
    apply hne
    rw [h]
    simp
  have hdeg : p.natDegree < k := by
    have hlt := Polynomial.mem_degreeLT.mp hp
    have := Polynomial.natDegree_lt_iff_degree_lt (n := k) hpne
    exact this.mpr hlt
  -- zeros of the codeword inject into the roots of `p`
  have hzero_inj : (Finset.univ.filter
      (fun i => ReedSolomon.evalOnPoints domain p i = 0)).card ≤ p.natDegree := by
    have hmap : ∀ i ∈ Finset.univ.filter
        (fun i => ReedSolomon.evalOnPoints domain p i = 0),
        domain i ∈ p.roots.toFinset := by
      intro i hi
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hpne]
      exact (Finset.mem_filter.mp hi).2
    calc (Finset.univ.filter
        (fun i => ReedSolomon.evalOnPoints domain p i = 0)).card
        ≤ p.roots.toFinset.card :=
          Finset.card_le_card_of_injOn (fun i => domain i) hmap
            (fun a _ b _ h => domain.injective h)
      _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := p.card_roots'
  -- weight = n − #zeros
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset ι))
    (p := fun i => ReedSolomon.evalOnPoints domain p i = 0)
  have hwt : wt (ReedSolomon.evalOnPoints domain p)
      = (Finset.univ.filter
          (fun i => ¬ ReedSolomon.evalOnPoints domain p i = 0)).card := rfl
  rw [hwt]
  have hcard : (Finset.univ : Finset ι).card = Fintype.card ι := rfl
  omega

/-- The radius-forcing fact at the lattice point `j/n`: witness sets have size `≥ n − j`. -/
theorem latticeForce {j : ℕ} (hjn : j ≤ Fintype.card ι) :
    ∀ S : Finset ι,
      ((1 : ℝ≥0) - mcaLatticePoint (Fintype.card ι) ⟨j, by omega⟩)
          * (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) →
        Fintype.card ι - j ≤ S.card := by
  intro S hS
  set n : ℕ := Fintype.card ι with hn
  have hnpos : 0 < n := Fintype.card_pos
  have hval : ((1 : ℝ≥0) - mcaLatticePoint n ⟨j, by omega⟩) * (n : ℝ≥0)
      = ((n - j : ℕ) : ℝ≥0) := by
    unfold mcaLatticePoint
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, NNReal.coe_sub (by
      rw [div_le_one (by exact_mod_cast hnpos)]
      exact_mod_cast hjn)]
    push_cast [Nat.cast_sub hjn]
    have hnne : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.pos_iff_ne_zero.mp hnpos
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hnne]
    rw [NNReal.coe_sub (show (j : ℝ≥0) ≤ (n : ℝ≥0) by exact_mod_cast hjn)]
    push_cast
    ring
  rw [hval] at hS
  exact_mod_cast hS

open Classical in
/-- **THE EXACT STAIRCASE.** For Reed–Solomon codes with `3j < n − (k − 1)` (every nonzero
codeword outweighs `3j`) and the spike conditions `j + 1 + k ≤ n`, `j + 1 ≤ q`:

  `ε_mca(RS[F, domain, k], j/n) = (j + 1)/q` — **exactly**.

The staircase side of the two-family profile law, as one machine-checked equality. -/
theorem epsMCA_band_exact (domain : ι ↪ F) {k : ℕ}
    (j : Fin (Fintype.card ι + 1))
    (hjn : j.val < Fintype.card ι)
    (ht_n : j.val + 1 + k ≤ Fintype.card ι)
    (ht_q : j.val + 1 ≤ Fintype.card F)
    (hd : 3 * j.val < Fintype.card ι - (k - 1)) :
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F))
        (mcaLatticePoint (Fintype.card ι) j)
      = (↑(j.val + 1) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [show ((j.val + 1 : ℕ) : ℝ≥0∞) = (j.val : ℝ≥0∞) + 1 from by push_cast; ring]
  refine le_antisymm ?_ ?_
  case refine_2 =>
    have h := epsMCA_generalJ_ge domain j hjn ht_n ht_q
    rwa [show ((j.val + 1 : ℕ) : ℝ≥0∞) = (j.val : ℝ≥0∞) + 1 from by push_cast; ring] at h
  have hforce := latticeForce (ι := ι) (j := j.val) (le_of_lt hjn)
  have hj : (⟨j.val, by omega⟩ : Fin (Fintype.card ι + 1)) = j := by
    ext
    rfl
  rw [hj] at hforce
  refine epsMCA_le_band (ReedSolomon.code domain k) _ hforce ?_
  intro c hc hne
  have := rs_nonzero_wt_lower domain hc hne
  omega

/-! ## Source audit -/

#print axioms rs_nonzero_wt_lower
#print axioms epsMCA_band_exact

end ProximityGap.BandCollapse
