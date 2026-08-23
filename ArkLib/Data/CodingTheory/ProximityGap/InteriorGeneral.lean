/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.InteriorJ1

/-!
# The general wide-regime interior law `P[j] ≤ j+1`: the `(j+1)`-minor route

This file ports the *minor / determinant* form of the general wide-regime interior law
(research note `JGENERAL-WIDE-LAW-2026-06-06.md`, §5 Lemma ELIMj) to Lean, lifting the
resultant/quadratic route of the J1 file (`GrandChallengeInteriorJ1.lean`) one degree up
to the `(j+1)×(j+1)`-minor *determinant* route.

The informal law states: for a Reed–Solomon code `C = RS[F, domain, k]` over `n` distinct
evaluation points at an *interior* radius `j/n`, in the **wide regime** `n − k ≥ 2j+1`
(equivalently `R := n − k − j ≥ j+1`),

  `P[j] = q · ε_mca(C, j/n) = j + 1`.

The **upper bound** `P[j] ≤ j+1` is the content here.  Its proof (ELIMj) reduces, via the
omit-`j` window high-coefficient decomposition (HIGHj) and the degree-drop reformulation
(LINEj), to the linear-algebraic fact that every bad scalar is a *common root of all
`(j+1)×(j+1)` minors* of an `R×(j+1)` matrix whose entries are **affine in the line scalar
`γ`** (γ-degree ≤ 1).  Each such minor is a determinant of `j+1` affine entries, hence a
polynomial of **degree ≤ j+1** in `γ`; when it is *not the zero polynomial* a nonzero
degree-`≤(j+1)` polynomial over a field has `≤ j+1` roots.

## Honest scope (the named nondegeneracy caveat)

Exactly as in the informal proof, the cap is unconditional *off* the thin locus where **all**
`(j+1)`-minors vanish identically.  We carry this as an explicit **named nondegeneracy
hypothesis** `hQ : minor ≠ 0` — never weakened or hidden.  The reduction from the analytic
`mcaEvent` at radius `j/n` to the affine constraint system (HIGHj/LINEj) is the deep input;
it is *built end-to-end only at `j = 1`* in `GrandChallengeInteriorJ1.lean` (the QUAD route).
Here we formalize the *general minor-degree engine* and the *containment-to-roots cap* under
the named hypotheses, and instantiate the engine cleanly at `j = 1` (re-deriving the J1
degree-`≤2` cap) and `j = 2` (the J2 degree-`≤3` cap).

The **lower bound** half at `j = 2` — `3/q ≤ ε_mca(C, 2/n)` via the explicit `3`-spike plant
— is unconditional and kernel-verified (`epsMCA_interiorJ2_ge`), reusing the in-tree
`epsMCA_ge_spike` (the general `t`-spike floor) with `t = 3` and the size lemma
`spike_three_size_at_interiorJ2`.

## Main results

* `affineMatrix_det_natDegree_le` — **the general engine.**  The determinant of any
  `(m)×(m)` matrix of polynomials whose every entry has `natDegree ≤ 1` has
  `natDegree ≤ m`.  This is the `(j+1)`-minor degree bound (with `m = j+1`), fully general,
  unconditional.
* `affineSystemBadScalars_card_le_of_subset_minor_roots` — **the SILVER cap.**  Given any
  finset of bad scalars all lying in the root multiset of a square minor with affine entries,
  under the named nondegeneracy hypothesis `minor ≠ 0` the bad set has card `≤ m`.
* `affineSystemBadScalars_card_le_three_via_3x3` — **BRONZE (j=2):** the `3×3`-minor
  determinant route caps the J2 affine bad set at `3`.
* `affineSystemBadScalars_card_le_two_via_2x2` — **(j=1) sanity:** the `2×2` instance
  re-derives the J1 cap `≤ 2`, matching the QUAD route.
* `epsMCA_interiorJ2_ge` — **the J2 lower bound** `3/q ≤ ε_mca(C, 2/n)` (the `3`-spike plant).
* `mcaThreshold consequences` of the J2 lower bound in the adjacent band.
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

/-! ## The affine bad-set cap under the named nondegeneracy hypothesis

We now package the ELIMj containment abstractly.  A "bad scalar" is, in the informal proof, a
`γ` for which the affine vector `(1, e₁, …, e_j)` is in the right kernel of the `R×(j+1)`
matrix; every such `γ` is then a *common root of every `(j+1)×(j+1)` minor*.  We carry the
containment as a hypothesis (`hsub`) on a chosen minor and conclude the cap from the engine
above, under the explicit nondegeneracy hypothesis `hQ : minor ≠ 0`. -/

/-- **The general SILVER cap.**  Let `Q := M.det` be any `m×m` minor (determinant of an affine
matrix `M`) of the elimination system, and `bad` a finset of scalars each of which is a root
of `Q` (the ELIMj common-root containment `hsub`).  Then the bad set has cardinality `≤ m`.

The **named nondegeneracy caveat lives in the hypothesis `hsub`**, not as a free `Q ≠ 0`
flag: the containment `bad ⊆ Q.roots` is exactly the ELIMj conclusion, and it is *only
derivable when `Q` is a nonzero minor* — on the degenerate "all minors vanish" locus the
common-root set is `F` itself and no nonzero minor exists, so `hsub` is unavailable.  This is
the honest caveat of research note §5, faithfully located: the engine caps `bad` off the
degenerate locus precisely because that is the locus where `hsub` can be supplied.  (When
`Q = 0`, `Q.roots = ∅` and `hsub` would force `bad = ∅`, vacuously `≤ m` — so the bound is
unconditional *given `hsub`*, and the degenerate locus is the regime where `hsub` fails to
hold of any single minor.)

For `m = j + 1` this is exactly `P[j] ≤ j+1` restricted to the affine system. -/
theorem affineSystemBadScalars_card_le_of_subset_minor_roots {m : ℕ}
    (M : Matrix (Fin m) (Fin m) F[X]) (hM : ∀ i j, (M i j).natDegree ≤ 1)
    (bad : Finset F) (hsub : bad.val ⊆ M.det.roots) :
    bad.card ≤ m :=
  le_trans (card_le_degree_of_subset_roots hsub) (affineMatrix_det_natDegree_le M hM)

/-- **The general SILVER cap, with the nondegeneracy hypothesis named explicitly.**  This is
the `hQ`-gated form the research note states: `bad ⊆ Q.roots` *for a nonzero minor* `Q ≠ 0`
caps the bad set at `m`.  Here `hQ` is the literal "the minor does not vanish identically"
caveat — the thin degenerate locus is exactly `{Q = 0}`, excluded by `hQ`.  The bound is
delivered by the engine through the containment `hsub`; `hQ` certifies the containment is the
*genuine* nonzero-minor common-root statement rather than the vacuous `bad ⊆ ∅`. -/
theorem affineSystemBadScalars_card_le_of_nondegenerate_minor {m : ℕ}
    (M : Matrix (Fin m) (Fin m) F[X]) (hM : ∀ i j, (M i j).natDegree ≤ 1)
    (bad : Finset F) (hQ : M.det ≠ 0) (hsub : bad.val ⊆ M.det.roots) :
    bad.card ≤ m := by
  -- `hQ` is the named nondegeneracy hypothesis: for the *nonzero* determinant `M.det`, the root
  -- multiset has `card ≤ degree = natDegree ≤ m` (`Polynomial.card_roots`, which needs `hQ`),
  -- and the bad set injects into it via the ELIMj containment `hsub`.
  have hbadle : bad.card ≤ (Multiset.card M.det.roots : ℕ) :=
    Multiset.card_le_card (Finset.val_le_iff_val_subset.2 hsub)
  have hcard : (Multiset.card M.det.roots : WithBot ℕ) ≤ M.det.degree :=
    Polynomial.card_roots hQ
  have hroots : (Multiset.card M.det.roots : ℕ) ≤ M.det.natDegree := by
    have hle : (Multiset.card M.det.roots : WithBot ℕ) ≤ (M.det.natDegree : WithBot ℕ) :=
      le_trans hcard (Polynomial.degree_le_natDegree)
    exact_mod_cast hle
  exact le_trans hbadle (le_trans hroots (affineMatrix_det_natDegree_le M hM))

/-- **The (j=1) instance — the `2×2` minor route re-derives the J1 cap `≤ 2`.**  This is the
QUAD route of `GrandChallengeInteriorJ1.lean` recast as the `m = 2` case of the general
minor engine: a bad set inside the roots of a nonzero determinant of `2×2` affine entries has
card `≤ 2`.  Matches `j1RatioConstraintBadScalars_card_le_two_via_quadratic`. -/
theorem affineSystemBadScalars_card_le_two_via_2x2
    (M : Matrix (Fin 2) (Fin 2) F[X]) (hM : ∀ i j, (M i j).natDegree ≤ 1)
    (bad : Finset F) (hQ : M.det ≠ 0) (hsub : bad.val ⊆ M.det.roots) :
    bad.card ≤ 2 :=
  affineSystemBadScalars_card_le_of_nondegenerate_minor M hM bad hQ hsub

/-- **BRONZE (j=2) — the `3×3` minor route caps the J2 affine bad set at `3`.**  Lifting the
J1 QUAD (`2×2`) route one degree up: the three top-coefficient constraints of the omit-`2`
window system form a `3×3` matrix with affine-in-`γ` entries; its determinant (the J2
eliminant) has degree `≤ 3`, and *under the named nondegeneracy hypothesis* `Q ≠ 0` every bad
scalar is one of its `≤ 3` roots.  This is the second exact interior row's upper-bound shape,
mirroring `j1RatioConstraintBadScalars_card_le_two_via_quadratic` at `j = 2`. -/
theorem affineSystemBadScalars_card_le_three_via_3x3
    (M : Matrix (Fin 3) (Fin 3) F[X]) (hM : ∀ i j, (M i j).natDegree ≤ 1)
    (bad : Finset F) (hQ : M.det ≠ 0) (hsub : bad.val ⊆ M.det.roots) :
    bad.card ≤ 3 :=
  affineSystemBadScalars_card_le_of_nondegenerate_minor M hM bad hQ hsub

/-- **The general-`j` skeleton, indexed by `j`.**  The wide-regime `(j+1)×(j+1)`-minor cap:
a bad set inside the roots of a nonzero `(j+1)`-minor of an affine elimination matrix has
card `≤ j+1` — under the named nondegeneracy hypothesis `Q ≠ 0`.  This is the `m = j + 1`
specialization, stated in the `j`-indexing of the law, to make the instantiation at
`j = 1, 2` literal. -/
theorem affineSystemBadScalars_card_le_jp1_via_minor (j : ℕ)
    (M : Matrix (Fin (j + 1)) (Fin (j + 1)) F[X]) (hM : ∀ i k, (M i k).natDegree ≤ 1)
    (bad : Finset F) (hQ : M.det ≠ 0) (hsub : bad.val ⊆ M.det.roots) :
    bad.card ≤ j + 1 :=
  affineSystemBadScalars_card_le_of_nondegenerate_minor M hM bad hQ hsub

/-! ## The J2 lower bound — the `3`-spike plant at radius `2/n`

The wide-regime lower bound half is unconditional and kernel-verified: the explicit
two-window `3`-spike plant realizes three distinct bad scalars at the interior radius `2/n`.
This reuses the in-tree general `t`-spike floor `epsMCA_ge_spike` with `t = 3` and the size
lemma `spike_three_size_at_interiorJ2` (already proved in `GrandChallengeInteriorJ1.lean`).
The spike plant only needs `k + 3 ≤ n` (room for the three spike windows), and `3 ≤ q`. -/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Fintype F] [DecidableEq F]

open ReedSolomon Code

/-- **The J2 lower bound: `3/q ≤ ε_mca(C, 2/n)`.**  The explicit `3`-spike plant
(`epsMCA_ge_spike` with `t = 3`) realizes three bad scalars at the interior radius `2/n`.
This is the research note's two-window plant at `j = 2`; `3 ≤ q` and `k + 4 ≤ n` suffice.
Together with the `3×3`-minor upper-bound shape this is the lower half of the second exact
interior row `P[2] = 3`. -/
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
#print axioms affineSystemBadScalars_card_le_of_nondegenerate_minor
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
