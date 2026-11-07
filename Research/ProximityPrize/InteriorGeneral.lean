/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Research.ProximityPrize.InteriorJ1

/-!
# Interior caps: an abstract affine-minor root count and the J2 spike lower bound

This file ports the *minor / determinant* shape of the general wide-regime interior law
(research note `JGENERAL-WIDE-LAW-2026-06-06.md`, §5 Lemma ELIMj) to Lean, lifting the
resultant/quadratic route of the J1 file (`InteriorJ1.lean`) one degree up to the
`(j+1)×(j+1)`-minor *determinant* shape.

The informal law states: for a Reed–Solomon code `C = RS[F, domain, k]` over `n` distinct
evaluation points at an *interior* radius `j/n`, in the **wide regime** `n − k ≥ 2j+1`
(equivalently `R := n − k − j ≥ j+1`),

  `P[j] = q · ε_mca(C, j/n) = j + 1`.

The informal proof of the upper bound `P[j] ≤ j+1` (ELIMj) reduces, via the omit-`j` window
high-coefficient decomposition (HIGHj) and the degree-drop reformulation (LINEj), to the
linear-algebraic fact that every bad scalar is a common root of a `(j+1)×(j+1)` minor of an
`R×(j+1)` matrix whose entries are affine in the line scalar `γ`.

## Honest scope

**This file does not prove the upper bound `P[j] ≤ j+1` for any `j`.**  The upper-bound results
here are *abstract root-counting lemmas* about matrices of affine polynomials: no statement
mentions `mcaEvent`, `epsMCA` or a Reed–Solomon code.  The reduction from `mcaEvent` at radius
`j/n` to the affine containment `bad ⊆ (minor).roots` (HIGHj/LINEj) is **not** formalized here;
it is supplied abstractly as the hypothesis `hsub`.  (At `j = 1` the J1 cap `≤ 2` is proved
end-to-end by other means in `J1Cap.lean`.)  The root count needs no separate nondegeneracy
hypothesis: if the minor is the zero polynomial its root multiset is empty, so `hsub` forces
`bad = ∅`.  The degenerate "all minors vanish" locus is therefore exactly the regime in which
`hsub` cannot be supplied for a nontrivial bad set.

The **lower bound** half at `j = 2` — `3/q ≤ ε_mca(C, 2/n)` via the explicit `3`-spike plant
— is unconditional and kernel-verified (`epsMCA_interiorJ2_ge`), reusing the in-tree
`epsMCA_ge_spike` (the general `t`-spike floor) with `t = 3` and the size lemma
`spike_three_size_at_interiorJ2`.

## Main results

* `affineMatrix_det_natDegree_le` — the determinant of any `m×m` matrix of polynomials whose
  every entry has `natDegree ≤ 1` has `natDegree ≤ m`.
* `affineSystemBadScalars_card_le_of_subset_minor_roots` — an abstract root count: any finset
  contained in the roots of such a determinant has card `≤ m`.
* `affineSystemBadScalars_card_le_two_via_2x2`, `affineSystemBadScalars_card_le_three_via_3x3`,
  `affineSystemBadScalars_card_le_jp1_via_minor` — the `m = 2`, `m = 3` and `m = j + 1`
  specializations of that root count.
* `epsMCA_interiorJ2_ge` — **the J2 lower bound** `3/q ≤ ε_mca(C, 2/n)` (the `3`-spike plant).
* `mcaThreshold` consequences of the J2 lower bound in the adjacent band.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap

namespace GrandChallengesLattice

open Polynomial Matrix
open scoped NNReal ENNReal BigOperators

/-! ## The general minor-degree engine

The heart of the wide-regime upper bound is purely linear-algebraic and independent of the
coding-theoretic reduction: a determinant of affine (`natDegree ≤ 1`) polynomial entries has
degree bounded by the matrix size.  This is the `(j+1)×(j+1)`-minor degree bound of Lemma
ELIMj, valid for every `j` (with `m := j + 1`). -/

variable {F : Type} [Field F]

/-- **The general `(j+1)`-minor degree bound.**  For any `m×m` matrix `M` over `F[X]` whose
every entry has `natDegree ≤ 1`, the determinant has `natDegree ≤ m`.

Via `Matrix.det_apply`, `det M = ∑ σ, sign σ • ∏ i, M (σ i) i`.  Each product ranges over the
`m` rows, so by `natDegree_prod_le` its degree is `≤ ∑ 1 = m`; the signed sum does not raise
the degree (`natDegree_smul_le`, `natDegree_sum_le_of_forall_le`).  Instantiated with
`m = j + 1` this is the *degree-`≤(j+1)`* bound on every `(j+1)×(j+1)` minor of the `R×(j+1)`
elimination matrix (research note §5). -/
theorem affineMatrix_det_natDegree_le {m : ℕ} (M : Matrix (Fin m) (Fin m) F[X])
    (hM : ∀ i j, (M i j).natDegree ≤ 1) :
    M.det.natDegree ≤ m := by
  rw [Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ ?_
  intro σ _
  refine le_trans (natDegree_smul_le _ _) ?_
  refine le_trans (natDegree_prod_le _ _) ?_
  calc ∑ i : Fin m, (M (σ i) i).natDegree
      ≤ ∑ _i : Fin m, 1 := by
        refine Finset.sum_le_sum ?_
        intro i _
        exact hM (σ i) i
    _ = m := by simp

/-! ## The abstract affine-minor root count

We package the ELIMj containment abstractly.  A "bad scalar" is, in the informal proof, a
`γ` for which the affine vector `(1, e₁, …, e_j)` is in the right kernel of the `R×(j+1)`
matrix; every such `γ` is then a common root of every `(j+1)×(j+1)` minor.  We carry the
containment as a hypothesis (`hsub`) on a chosen minor; the conclusion is pure root counting. -/

/-- **Abstract affine-minor root count.**  Let `M` be an `m×m` matrix over `F[X]` with every
entry of `natDegree ≤ 1`, and `bad` a finset of scalars contained in the roots of `M.det`.
Then `bad.card ≤ m`.

No nondegeneracy hypothesis is needed: if `M.det = 0` then `M.det.roots = 0` and `hsub` forces
`bad = ∅`.  This lemma does not connect `bad` to `mcaEvent`; that reduction (HIGHj/LINEj) is
not formalized here. -/
theorem affineSystemBadScalars_card_le_of_subset_minor_roots {m : ℕ}
    (M : Matrix (Fin m) (Fin m) F[X]) (hM : ∀ i j, (M i j).natDegree ≤ 1)
    (bad : Finset F) (hsub : bad.val ⊆ M.det.roots) :
    bad.card ≤ m :=
  le_trans (card_le_degree_of_subset_roots hsub) (affineMatrix_det_natDegree_le M hM)

/-- The `m = 2` specialization of `affineSystemBadScalars_card_le_of_subset_minor_roots`
(the abstract shape of the J1 QUAD route). -/
theorem affineSystemBadScalars_card_le_two_via_2x2
    (M : Matrix (Fin 2) (Fin 2) F[X]) (hM : ∀ i j, (M i j).natDegree ≤ 1)
    (bad : Finset F) (hsub : bad.val ⊆ M.det.roots) :
    bad.card ≤ 2 :=
  affineSystemBadScalars_card_le_of_subset_minor_roots M hM bad hsub

/-- The `m = 3` specialization of `affineSystemBadScalars_card_le_of_subset_minor_roots`
(the abstract shape of the informal J2 `3×3`-eliminant route; the J2 containment itself is
not formalized). -/
theorem affineSystemBadScalars_card_le_three_via_3x3
    (M : Matrix (Fin 3) (Fin 3) F[X]) (hM : ∀ i j, (M i j).natDegree ≤ 1)
    (bad : Finset F) (hsub : bad.val ⊆ M.det.roots) :
    bad.card ≤ 3 :=
  affineSystemBadScalars_card_le_of_subset_minor_roots M hM bad hsub

/-- The `m = j + 1` specialization of `affineSystemBadScalars_card_le_of_subset_minor_roots`,
stated in the `j`-indexing of the interior law. -/
theorem affineSystemBadScalars_card_le_jp1_via_minor (j : ℕ)
    (M : Matrix (Fin (j + 1)) (Fin (j + 1)) F[X]) (hM : ∀ i k, (M i k).natDegree ≤ 1)
    (bad : Finset F) (hsub : bad.val ⊆ M.det.roots) :
    bad.card ≤ j + 1 :=
  affineSystemBadScalars_card_le_of_subset_minor_roots M hM bad hsub

/-! ## The J2 lower bound — the `3`-spike plant at radius `2/n`

The wide-regime lower bound half is unconditional and kernel-verified: the explicit
two-window `3`-spike plant realizes three distinct bad scalars at the interior radius `2/n`.
This reuses the in-tree general `t`-spike floor `epsMCA_ge_spike` with `t = 3` and the size
lemma `spike_three_size_at_interiorJ2` (already proved in `InteriorJ1.lean`).
The spike plant only needs `k + 3 ≤ n` (room for the three spike windows), and `3 ≤ q`. -/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Fintype F] [DecidableEq F]

open ReedSolomon Code

/-- **The J2 lower bound: `3/q ≤ ε_mca(C, 2/n)`.**  The explicit `3`-spike plant
(`epsMCA_ge_spike` with `t = 3`) realizes three bad scalars at the interior radius `2/n`.
This is the research note's two-window plant at `j = 2`; `3 ≤ q` and `k + 3 ≤ n` suffice.
This is the lower half of the informal second interior row `P[2] = 3`; the matching upper
bound is not formalized. -/
theorem epsMCA_interiorJ2_ge
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (hq : 3 ≤ Fintype.card F) :
    (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F))
        (mcaLatticePoint (Fintype.card ι)
          (⟨2, by
            have hn : 0 < Fintype.card ι := Fintype.card_pos
            omega⟩ : Fin (Fintype.card ι + 1))) := by
  classical
  set n := Fintype.card ι with hndef
  have hn3 : 3 ≤ n := by omega
  have ht_n : 3 + k ≤ n := by omega
  have hδ : ((1 - mcaLatticePoint n (⟨2, by omega⟩ : Fin (n + 1))) * n : ℝ≥0)
      ≤ ((n - 3 + 1 : ℕ) : ℝ≥0) :=
    spike_three_size_at_interiorJ2 (n := n) hn3
  have hspike := epsMCA_ge_spike domain k 3
    (mcaLatticePoint n (⟨2, by omega⟩ : Fin (n + 1))) ht_n hq hδ
  simpa using hspike

/-- **J2 satisfaction obstruction.**  If `ε* < 3 / |F|`, then the faithful MCA predicate
cannot hold at the J2 lattice point, because the `3`-spike plant forces
`ε_mca(C, 2/n) ≥ 3 / |F|`.  This is the threshold-existence-free form of
`mcaThreshold_lt_two_of_interiorJ2_gt`. -/
theorem not_mcaSatisfies_interiorJ2_of_interiorJ2_gt
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (hq : 3 ≤ Fintype.card F)
    {ε_star : ℝ≥0}
    (hbad : (ε_star : ℝ≥0∞) < (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    let j2 : Fin (Fintype.card ι + 1) := ⟨2, by
      have hn : 0 < Fintype.card ι := Fintype.card_pos
      omega⟩
    ¬ mcaSatisfies (ReedSolomon.code domain k : Set (ι → F)) ε_star j2 := by
  let C : Set (ι → F) := ReedSolomon.code domain k
  let j2 : Fin (Fintype.card ι + 1) := ⟨2, by
    have hn : 0 < Fintype.card ι := Fintype.card_pos
    omega⟩
  change ¬ mcaSatisfies C ε_star j2
  intro hsat
  have hge : (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (A := F) C (mcaLatticePoint (Fintype.card ι) j2) :=
    epsMCA_interiorJ2_ge domain hk hq
  have hchain : (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ (ε_star : ℝ≥0∞) :=
    le_trans hge hsat
  exact (not_le_of_gt hbad) hchain

set_option maxHeartbeats 800000 in
-- The contradiction proof combines `Fin` threshold order, monotonicity, and ENNReal coercions.
/-- **J2 lattice satisfaction lower bracket.**  At the interior radius `2/n`, if the faithful
MCA bound is to hold (`mcaSatisfies` at index `2`), then `3/q ≤ ε*` is necessary — because
the `3`-spike plant forces `ε_mca(C, 2/n) ≥ 3/q`.  Contrapositively, when `ε* < 3/q` the
faithful threshold is strictly below J2. -/
theorem mcaThreshold_lt_two_of_interiorJ2_gt
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (hq : 3 ≤ Fintype.card F)
    {ε_star : ℝ≥0}
    (hbad : (ε_star : ℝ≥0∞) < (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) ε_star) :
    let j2 : Fin (Fintype.card ι + 1) := ⟨2, by
      have hn : 0 < Fintype.card ι := Fintype.card_pos
      omega⟩
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne < j2 := by
  let C : Set (ι → F) := ReedSolomon.code domain k
  let j2 : Fin (Fintype.card ι + 1) := ⟨2, by
    have hn : 0 < Fintype.card ι := Fintype.card_pos
    omega⟩
  change mcaThreshold C ε_star hne < j2
  by_contra hnot
  have hj2_le : j2 ≤ mcaThreshold C ε_star hne := not_lt.mp hnot
  have hsat_threshold : mcaSatisfies C ε_star (mcaThreshold C ε_star hne) :=
    mcaThreshold_spec C ε_star hne
  have hsat_j2 : mcaSatisfies C ε_star j2 :=
    mcaSatisfies_downward_closed C ε_star hj2_le hsat_threshold
  have hge : (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (A := F) C (mcaLatticePoint (Fintype.card ι) j2) :=
    epsMCA_interiorJ2_ge domain hk hq
  have hchain : (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ (ε_star : ℝ≥0∞) :=
    le_trans hge hsat_j2
  exact (not_le_of_gt hbad) hchain

/-- **Four-rate J2 upper bracket.**  If each prize-rate Reed-Solomon code has room for the
three-spike plant and `ε* < 3 / |F|`, then every faithful MCA prize threshold, when it exists,
is strictly below the J2 lattice index. -/
theorem mcaPrizeLattice_lt_two_of_interiorJ2_gt
    (domain : ι ↪ F)
    (hk : ∀ r : Fin 4,
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 3 ≤ Fintype.card ι)
    (hq : 3 ≤ Fintype.card F)
    (hbad : (epsStar : ℝ≥0∞) < (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
    (hne : ∀ r : Fin 4,
      mcaThresholdExists
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) :
    ∀ r : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
      let j2 : Fin (Fintype.card ι + 1) := ⟨2, by
        have hn : 0 < Fintype.card ι := Fintype.card_pos
        have hkr := hk r
        omega⟩
      mcaThreshold C epsStar (hne r) < j2 := by
  intro r
  simpa using
    (mcaThreshold_lt_two_of_interiorJ2_gt
      (F := F) domain (hk r) hq hbad (hne r))

/-- **Four-rate J2 satisfaction obstruction.**  If each prize-rate Reed-Solomon code has room
for the three-spike plant and `ε* < 3 / |F|`, then none of the four prize-rate codes satisfies
the faithful MCA predicate at the J2 lattice point. -/
theorem not_mcaPrizeLattice_satisfies_two_of_interiorJ2_gt
    (domain : ι ↪ F)
    (hk : ∀ r : Fin 4,
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 3 ≤ Fintype.card ι)
    (hq : 3 ≤ Fintype.card F)
    (hbad : (epsStar : ℝ≥0∞) < (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    ∀ r : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
      let j2 : Fin (Fintype.card ι + 1) := ⟨2, by
        have hn : 0 < Fintype.card ι := Fintype.card_pos
        have hkr := hk r
        omega⟩
      ¬ mcaSatisfies C epsStar j2 := by
  intro r
  simpa using
    (not_mcaSatisfies_interiorJ2_of_interiorJ2_gt
      (F := F) (ε_star := epsStar) domain
      (k := ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊) (hk r) hq hbad)

/-- **Formal-prize J2 upper bracket in the large-domain, small-field-side band.**
For domains with at least six evaluation points, all four prize-rate degrees satisfy the
`k + 3 ≤ n` spike window. If additionally `3 ≤ |F|` and `|F| < 3 * 2^128`, then the formal
threshold `ε* = 2^-128` lies below `3 / |F|`, so all existing faithful MCA prize thresholds are
strictly below J2. -/
theorem mcaPrizeLattice_lt_two_of_card_ge_six_and_card_lt_three_mul_two_pow
    (domain : ι ↪ F)
    (hn : 6 ≤ Fintype.card ι)
    (hq : 3 ≤ Fintype.card F)
    (hcard_hi : Fintype.card F < (3 : ℕ) * 2 ^ (128 : ℕ))
    (hne : ∀ r : Fin 4,
      mcaThresholdExists
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) :
    ∀ r : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
      let j2 : Fin (Fintype.card ι + 1) := ⟨2, by omega⟩
      mcaThreshold C epsStar (hne r) < j2 :=
  mcaPrizeLattice_lt_two_of_interiorJ2_gt domain
    (fun r => prizeRate_floor_add_three_le_of_card_ge_six r hn)
    hq
    (epsStar_lt_three_div_card_of_card_lt_three_mul_two_pow (F := F) hcard_hi)
    hne

/-- **Formal-prize J2 satisfaction obstruction in the large-domain, small-field-side band.**
For domains with at least six evaluation points and `|F| < 3 * 2^128`, the formal prize
threshold `ε* = 2^-128` is too small for the J2 spike lower bound, so no prize-rate code
satisfies the faithful MCA predicate at J2. -/
theorem not_mcaPrizeLattice_satisfies_two_of_card_ge_six_and_card_lt_three_mul_two_pow
    (domain : ι ↪ F)
    (hn : 6 ≤ Fintype.card ι)
    (hq : 3 ≤ Fintype.card F)
    (hcard_hi : Fintype.card F < (3 : ℕ) * 2 ^ (128 : ℕ)) :
    ∀ r : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
      let j2 : Fin (Fintype.card ι + 1) := ⟨2, by omega⟩
      ¬ mcaSatisfies C epsStar j2 :=
  not_mcaPrizeLattice_satisfies_two_of_interiorJ2_gt domain
    (fun r => prizeRate_floor_add_three_le_of_card_ge_six r hn)
    hq
    (epsStar_lt_three_div_card_of_card_lt_three_mul_two_pow (F := F) hcard_hi)

end GrandChallengesLattice

end ProximityGap

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
section AxiomAudit
open ProximityGap.GrandChallengesLattice
#print axioms affineMatrix_det_natDegree_le
#print axioms affineSystemBadScalars_card_le_of_subset_minor_roots
#print axioms affineSystemBadScalars_card_le_two_via_2x2
#print axioms affineSystemBadScalars_card_le_three_via_3x3
#print axioms affineSystemBadScalars_card_le_jp1_via_minor
#print axioms epsMCA_interiorJ2_ge
#print axioms not_mcaSatisfies_interiorJ2_of_interiorJ2_gt
#print axioms mcaThreshold_lt_two_of_interiorJ2_gt
#print axioms mcaPrizeLattice_lt_two_of_interiorJ2_gt
#print axioms mcaPrizeLattice_lt_two_of_card_ge_six_and_card_lt_three_mul_two_pow
#print axioms not_mcaPrizeLattice_satisfies_two_of_interiorJ2_gt
#print axioms not_mcaPrizeLattice_satisfies_two_of_card_ge_six_and_card_lt_three_mul_two_pow
end AxiomAudit
