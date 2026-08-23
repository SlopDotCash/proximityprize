/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallIntersectionGlobal
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# CS25 #82, deliverable 2 (b/d): the MDS min-distance restriction

A nonzero Reed–Solomon codeword of dimension `deg` has Hamming weight `> n - deg` (it has fewer than
`deg` zero coordinates, since the underlying degree-`<deg` polynomial has fewer than `deg` roots).
Hence the off-diagonal ball-intersection sum over the code is dominated by the **high-weight tail**:

  `∑_{e ∈ RS, e ≠ 0} I(e) ≤ ∑_{wt(e) > n - deg} I(e)`.

Combined with the global identity `∑_e I(e) = V²`, this reframes the CS25 second-moment off-diagonal
as a tail bound on the squared ball volume — the form the entropy band [d] controls.
-/

open scoped BigOperators ENNReal NNReal

namespace ArkLib.CS25

open Code Finset Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **MDS root count.** A nonzero Reed–Solomon codeword of dimension `deg` has fewer than `deg`
zero coordinates. -/
theorem rs_card_zeros_lt (domain : ι ↪ F) (deg : ℕ) (c : ι → F)
    (hc : c ∈ ReedSolomon.code domain deg) (hne : c ≠ 0) :
    (univ.filter (fun i => c i = 0)).card < deg := by
  classical
  obtain ⟨p, hp_mem, hp_eval⟩ := Submodule.mem_map.mp hc
  have hci : ∀ i, c i = p.eval (domain i) := by
    intro i; rw [← hp_eval]; rfl
  have hp_ne : p ≠ 0 := by
    rintro rfl
    exact hne (by funext i; rw [hci i]; simp)
  have hdeg : p.natDegree < deg :=
    (Polynomial.natDegree_lt_iff_degree_lt hp_ne).mpr (Polynomial.mem_degreeLT.mp hp_mem)
  have hsub : (univ.filter (fun i => c i = 0)).card ≤ p.roots.toFinset.card := by
    apply Finset.card_le_card_of_injOn (fun i => domain i)
    · intro i hi
      rw [Finset.mem_coe, mem_filter] at hi
      have hmem : domain i ∈ p.roots := by
        rw [Polynomial.mem_roots']
        refine ⟨hp_ne, ?_⟩
        change p.eval (domain i) = 0
        rw [← hci i]; exact hi.2
      simpa using hmem
    · intro a _ b _ hab; exact domain.injective hab
  calc (univ.filter (fun i => c i = 0)).card
        ≤ p.roots.toFinset.card := hsub
    _ ≤ Multiset.card p.roots := p.roots.toFinset_card_le
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ < deg := hdeg

/-- A nonzero Reed–Solomon codeword has Hamming weight `> n - deg`. -/
theorem rs_nonzero_weight_gt (domain : ι ↪ F) (deg : ℕ) (c : ι → F)
    (hc : c ∈ ReedSolomon.code domain deg) (hne : c ≠ 0) :
    Fintype.card ι - deg < hammingDist c (0 : ι → F) := by
  classical
  have hz := rs_card_zeros_lt domain deg c hc hne
  have hpart : (univ.filter (fun i => c i = 0)).card
      + (univ.filter (fun i => ¬ c i = 0)).card = Fintype.card ι := by
    rw [← Finset.card_univ]
    exact Finset.filter_card_add_filter_neg_card_eq_card _
  have hwt : hammingDist c (0 : ι → F) = (univ.filter (fun i => ¬ c i = 0)).card := by
    simp only [hammingDist, Pi.zero_apply, ne_eq]
  have hpos : 0 < (univ.filter (fun i => ¬ c i = 0)).card := by
    rw [Finset.card_pos]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ⟨i, by rw [mem_filter]; exact ⟨mem_univ _, by simpa using hi⟩⟩
  rw [hwt]; omega

open Classical in
/-- **MDS off-diagonal restriction.** The ball-intersection sum over nonzero codewords is dominated
by the high-weight (`wt > n - deg`) tail. -/
theorem sum_RS_jointCover_le_tail (domain : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) :
    (∑ e ∈ univ.filter
        (fun e : ι → F => e ∈ ReedSolomon.code domain deg ∧ e ≠ 0),
        jointCoverCount δ (0 : ι → F) e)
      ≤ ∑ e ∈ univ.filter
          (fun e : ι → F => Fintype.card ι - deg < hammingDist e (0 : ι → F)),
          jointCoverCount δ (0 : ι → F) e := by
  apply Finset.sum_le_sum_of_subset
  intro e he
  rw [mem_filter] at he ⊢
  exact ⟨mem_univ _, rs_nonzero_weight_gt domain deg e he.2.1 he.2.2⟩

end ArkLib.CS25
