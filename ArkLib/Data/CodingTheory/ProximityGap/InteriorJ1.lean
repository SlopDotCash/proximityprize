/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.J1Cap
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount
import ArkLib.Data.CodingTheory.ProximityGap.MCAEndpointLower

/-!
# The exact interior radius-`1/n` MCA error: `ε_mca(C, 1/n) = 2/q`

This file ports the *resultant / quadratic* form of the proven interior J1 theorem
("`P[1] = 2`", research note `J1-EXACT-THEOREM-2026-06-06.md`) to Lean: for a Reed–Solomon
code `C = RS[F, domain, k]` over an `n`-point domain (`n := #ι`) with `n ≥ k + 3` (so an
interior lattice point exists) and `2 ≤ q := |F|`,

  `ε_mca(C, 1/n) = 2 / q`.

The radius `1/n` is the first nonzero MCA lattice point, `mcaLatticePoint n 1`.

## The two directions

* **Upper bound `ε_mca(C, 1/n) ≤ 2/q`** — the new content.  Via the exact extremal form
  `ε_mca(C, δ) = (⨆ u, mcaBadCount C δ (u 0) (u 1)) / q` (`epsMCA_eq_iSup_mcaBadCount`) this
  reduces to the finite cap `mcaBadCount C (1/n) u₀ u₁ ≤ 2`, which we re-derive here through
  the **resultant route** the research note specifies:

  - **Lemma HIGH / LINE** (imported from `GrandChallengesLattice`).  Every MCA-bad scalar `γ`
    at radius `1/n` is a J1 ratio constraint (`mcaEvent_j1_exists_window_ratio_constraints`),
    and the omit-one-window high-coefficient equations
    (`cT_vanish_on_j1_window_full_top_coeff_equations`) eliminate the omitted coordinate.
  - **Lemma QUAD** (this file: `j1FullTopQuadratic_natDegree_le_two`,
    `j1RatioConstraintBadScalars_subset_quadratic_roots`,
    `j1RatioConstraintBadScalars_card_le_two_via_quadratic`).  The eliminant is the universal
    degree-`≤ 2` polynomial `Q := j1FullTopQuadratic domain u₀ u₁`; every constrained scalar is
    a root of it (`j1RatioConstraint_eval_j1FullTopQuadratic_eq_zero`).  When `Q ≠ 0`, a nonzero
    degree-`≤ 2` polynomial over a field has `≤ 2` roots (`card_le_degree_of_subset_roots`), so
    the constrained set has `≤ 2` elements.
  - **Lemma DEGEN** (imported `j1RatioConstraintBadScalars_card_le_two`).  When `Q ≡ 0` the
    resultant carries no information; the cap is instead closed by the joint-extendability
    window-collision argument (`not_three_j1_ratioConstraints`), which is unconditional.

* **Lower bound `2/q ≤ ε_mca(C, 1/n)`** — the explicit `2`-spike plant
  (`epsMCA_ge_spike` with `t = 2`), the in-tree two-window construction.  At radius `1/n` its
  size hypothesis `(1 - 1/n)·n ≤ n - 2 + 1` is an equality, and `n ≥ k + 3`, `2 ≤ q` discharge
  the remaining hypotheses.  This realizes the research note's *two-window plant* and is even
  cleaner than the note's stated `q ≥ 2n` threshold (`2 ≤ q` suffices).

## Main results

* `j1FullTopQuadratic_natDegree_le_two` — the QUAD eliminant has degree `≤ 2`.
* `j1RatioConstraintBadScalars_card_le_two_via_quadratic` — the resultant-route finite cap.
* `mcaBadCount_j1_le_two_via_quadratic` — the radius-`1/n` bad-count cap via the resultant.
* `epsMCA_interiorJ1_le` — `ε_mca(C, 1/n) ≤ 2/q` (upper bound; SILVER).
* `epsMCA_interiorJ1_ge` — `2/q ≤ ε_mca(C, 1/n)` (lower bound; spike plant).
* `epsMCA_interiorJ1_eq` — `ε_mca(C, 1/n) = 2/q` (GOLD).
* `mcaSatisfies_interiorJ1_iff_two_div_card_le`,
  `mcaSatisfies_interiorJ1_of_two_div_card_le`,
  `not_mcaSatisfies_interiorJ1_of_interiorJ1_gt`, `one_le_mcaThreshold_of_interiorJ1`,
  `mcaThreshold_lt_one_of_interiorJ1_gt`, `mcaPrizeLattice_satisfies_one_of_interiorJ1`,
  `not_mcaPrizeLattice_satisfies_one_of_interiorJ1_gt`,
  `mcaPrizeLattice_one_le_of_interiorJ1`, `mcaPrizeLattice_lt_one_of_interiorJ1_gt` —
  faithful lattice-threshold consequences of the exact J1 value.
* `mcaThreshold_eq_j1_of_interiorJ1_and_spikeJ2`,
  `mcaPrizeLatticeResolved_j1_of_interiorJ1_and_spikeJ2` — exact J1 threshold resolution in
  the adjacent band `2/q ≤ ε* < 3/q`, using the exact J1 value and the `3`-spike obstruction at
  lattice index J2.
* `mcaPrizeLatticeResolved_j1_of_interiorJ1_and_card_between` — the same adjacent-band
  resolution specialized to the formal prize threshold `ε* = 2⁻¹²⁸`, using the field-size band
  `2·2¹²⁸ ≤ q < 3·2¹²⁸`.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap

namespace GrandChallengesLattice

open Polynomial Code ReedSolomon
open scoped NNReal ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Lemma QUAD — the degree-`≤ 2` resultant and its roots

The universal quadratic eliminant `j1FullTopQuadratic domain u₀ u₁` is defined in
`GrandChallengesLattice` as `r * r − C n₁ · q · r + C n₂ · q · q − q · s`, where `q, r, s` are
the affine-in-`γ` coefficient polynomials `j1AffineCoeffPolynomial` (degree `≤ 1` each) carrying
the top three full-interpolant coefficients of `u₀, u₁`, and `n₁, n₂` are the top two nodal
coefficients (constants).  Hence it has degree `≤ 2`. -/

/-- The affine-in-`γ` coefficient polynomial `C a + C b · X` has degree `≤ 1`. -/
theorem j1AffineCoeffPolynomial_natDegree_le (a b : F) :
    (j1AffineCoeffPolynomial a b).natDegree ≤ 1 := by
  unfold j1AffineCoeffPolynomial
  compute_degree

/-- **Lemma QUAD, degree bound.**  The universal J1 eliminant `Q = j1FullTopQuadratic` is a
polynomial of degree `≤ 2` in the line scalar `γ`. -/
theorem j1FullTopQuadratic_natDegree_le_two (domain : ι ↪ F) (u₀ u₁ : ι → F) :
    (j1FullTopQuadratic domain u₀ u₁).natDegree ≤ 2 := by
  rw [j1FullTopQuadratic]
  set P₀ := Lagrange.interpolate Finset.univ (fun a => domain a) u₀
  set P₁ := Lagrange.interpolate Finset.univ (fun a => domain a) u₁
  set N := Lagrange.nodal Finset.univ (fun a => domain a)
  set q := j1AffineCoeffPolynomial (P₀.coeff (Fintype.card ι - 1)) (P₁.coeff (Fintype.card ι - 1))
  set r := j1AffineCoeffPolynomial (P₀.coeff (Fintype.card ι - 2)) (P₁.coeff (Fintype.card ι - 2))
  set s := j1AffineCoeffPolynomial (P₀.coeff (Fintype.card ι - 3)) (P₁.coeff (Fintype.card ι - 3))
  have hq : q.natDegree ≤ 1 := j1AffineCoeffPolynomial_natDegree_le _ _
  have hr : r.natDegree ≤ 1 := j1AffineCoeffPolynomial_natDegree_le _ _
  have hs : s.natDegree ≤ 1 := j1AffineCoeffPolynomial_natDegree_le _ _
  have h1 : (r * r).natDegree ≤ 2 := le_trans natDegree_mul_le (by omega)
  have h2 : (C (N.coeff (Fintype.card ι - 1)) * q * r).natDegree ≤ 2 := by
    refine le_trans natDegree_mul_le ?_
    have hcq : (C (N.coeff (Fintype.card ι - 1)) * q).natDegree ≤ 1 := by
      refine le_trans natDegree_mul_le ?_; rw [natDegree_C]; omega
    omega
  have h3 : (C (N.coeff (Fintype.card ι - 2)) * q * q).natDegree ≤ 2 := by
    refine le_trans natDegree_mul_le ?_
    have hcq : (C (N.coeff (Fintype.card ι - 2)) * q).natDegree ≤ 1 := by
      refine le_trans natDegree_mul_le ?_; rw [natDegree_C]; omega
    omega
  have h4 : (q * s).natDegree ≤ 2 := le_trans natDegree_mul_le (by omega)
  refine le_trans (natDegree_sub_le _ _) ?_
  refine max_le ?_ h4
  refine le_trans (natDegree_add_le _ _) ?_
  refine max_le ?_ h3
  exact le_trans (natDegree_sub_le _ _) (max_le h1 h2)

/-- **Lemma QUAD, root inclusion.**  When the eliminant `Q` is not the zero polynomial, every
J1-constrained scalar lies in its root multiset.  (Every constrained scalar is a root of `Q`
by `j1RatioConstraint_eval_j1FullTopQuadratic_eq_zero`; over a field a nonzero polynomial's roots
are exactly its zeros.) -/
theorem j1RatioConstraintBadScalars_subset_quadratic_roots
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (u₀ u₁ : ι → F)
    (hQ : j1FullTopQuadratic domain u₀ u₁ ≠ 0) :
    (j1RatioConstraintBadScalars domain k u₀ u₁).val ⊆
      (j1FullTopQuadratic domain u₀ u₁).roots := by
  classical
  intro γ hγ
  have hγc : j1RatioConstraint domain k u₀ u₁ γ := by
    have : γ ∈ j1RatioConstraintBadScalars domain k u₀ u₁ := hγ
    rwa [mem_j1RatioConstraintBadScalars] at this
  rw [mem_roots hQ]
  exact j1RatioConstraint_eval_j1FullTopQuadratic_eq_zero domain hk hγc

/-- **Lemma QUAD + Lemma DEGEN — the finite cap via the resultant route.**

The set of scalars cut out by the J1 window ratio constraints has at most two elements.

This is a *new proof* of `j1RatioConstraintBadScalars_card_le_two`, structured as the research
note's resultant argument:

* **non-degenerate (`Q ≠ 0`):** the constrained set injects into the root multiset of the
  degree-`≤ 2` eliminant `Q`, so its cardinality is `≤ deg Q ≤ 2`;
* **degenerate (`Q ≡ 0`):** the resultant is vacuous, and the cap is closed by the
  joint-extendability window-collision argument `not_three_j1_ratioConstraints` (Lemma DEGEN). -/
theorem j1RatioConstraintBadScalars_card_le_two_via_quadratic
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (u₀ u₁ : ι → F) :
    (j1RatioConstraintBadScalars domain k u₀ u₁).card ≤ 2 := by
  classical
  by_cases hQ : j1FullTopQuadratic domain u₀ u₁ = 0
  · -- Lemma DEGEN: `Q ≡ 0`, close by window collision.
    exact j1RatioConstraintBadScalars_card_le_two domain hk u₀ u₁
  · -- Lemma QUAD: bad scalars are roots of the degree-`≤ 2` eliminant.
    refine le_trans (card_le_degree_of_subset_roots
      (j1RatioConstraintBadScalars_subset_quadratic_roots domain hk u₀ u₁ hQ)) ?_
    exact j1FullTopQuadratic_natDegree_le_two domain u₀ u₁

/-- **Radius-`1/n` bad-count cap via the resultant route.**  Every stack `(u₀, u₁)` has at most
two MCA-bad scalars at the interior lattice radius `1/n`, proved through the QUAD eliminant +
DEGEN window collision. -/
theorem mcaBadCount_j1_le_two_via_quadratic
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (u₀ u₁ : ι → F) :
    mcaBadCount (F := F)
      (ReedSolomon.code domain k : Set (ι → F))
      (mcaLatticePoint (Fintype.card ι)
        (⟨1, by
          have hn : 0 < Fintype.card ι := Fintype.card_pos
          omega⟩ : Fin (Fintype.card ι + 1)))
      u₀ u₁ ≤ 2 :=
  mcaBadCount_j1_le_two_of_ratioConstraint_card_le_two domain u₀ u₁
    (j1RatioConstraintBadScalars_card_le_two_via_quadratic domain hk u₀ u₁)

/-! ## The interior radius-`1/n` MCA error -/

/-- **Upper bound (SILVER): `ε_mca(C, 1/n) ≤ 2/q`.**  The exact extremal identity
`ε_mca = (⨆ u, mcaBadCount)/q` (`epsMCA_eq_iSup_mcaBadCount`) turns the per-stack resultant cap
`mcaBadCount_j1_le_two_via_quadratic` into the error bound. -/
theorem epsMCA_interiorJ1_le
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) :
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F))
        (mcaLatticePoint (Fintype.card ι)
          (⟨1, by
            have hn : 0 < Fintype.card ι := Fintype.card_pos
            omega⟩ : Fin (Fintype.card ι + 1)))
      ≤ (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  rw [epsMCA_eq_iSup_mcaBadCount]
  apply ENNReal.div_le_div_right
  refine iSup_le fun u => ?_
  have := mcaBadCount_j1_le_two_via_quadratic domain hk (u 0) (u 1)
  exact_mod_cast this

/-- The size hypothesis of the `2`-spike construction at radius `1/n`: `(1 - 1/n)·n ≤ n - 2 + 1`.
For `2 ≤ n` this is the equality `(1 - 1/n)·n = n - 1 = n - 2 + 1`; for `n = 1` the right side is
`1 ≥ 0` and the bound is loose.  Note `ℝ≥0` has truncated subtraction (no `AddGroupWithOne`), so
the cast `↑(n - 1) = ↑n - 1` is routed through `NNReal.coe_sub`. -/
theorem spike_two_size_at_interiorJ1 {n : ℕ} (hn1 : 1 ≤ n) :
    ((1 - (1 : ℝ≥0) / (n : ℝ≥0)) * (n : ℝ≥0)) ≤ ((n - 2 + 1 : ℕ) : ℝ≥0) := by
  have hnne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have key : ((1 - (1 : ℝ≥0) / (n : ℝ≥0)) * (n : ℝ≥0)) = (n : ℝ≥0) - 1 := by
    rw [tsub_mul, one_mul, div_mul_cancel₀ _ hnne]
  rw [key]
  by_cases hn2 : 2 ≤ n
  · have h1 : (n - 2 + 1 : ℕ) = n - 1 := by omega
    rw [h1, ← NNReal.coe_le_coe, NNReal.coe_sub]
    · change (n : ℝ) - 1 ≤ ((n - 1 : ℕ) : ℝ)
      rw [Nat.cast_sub hn1, Nat.cast_one]
    · exact_mod_cast hn1
  · -- `n = 1`: the left side is `0`, while the right side is `1`.
    have hn_eq : n = 1 := by omega
    subst hn_eq
    norm_num

/-- The size hypothesis of the `3`-spike construction at radius `2/n`:
`(1 - 2/n)·n ≤ n - 3 + 1`.  Under `3 ≤ n`, this is the equality
`(1 - 2/n)·n = n - 2 = n - 3 + 1`. -/
theorem spike_three_size_at_interiorJ2 {n : ℕ} (hn3 : 3 ≤ n) :
    ((1 - mcaLatticePoint n
        (⟨2, by omega⟩ : Fin (n + 1))) * (n : ℝ≥0)) ≤
      ((n - 3 + 1 : ℕ) : ℝ≥0) := by
  have hnne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2n : (2 : ℝ≥0) ≤ (n : ℝ≥0) := by
    exact_mod_cast (by omega : 2 ≤ n)
  unfold mcaLatticePoint
  change ((1 - (2 : ℝ≥0) / (n : ℝ≥0)) * (n : ℝ≥0)) ≤
    ((n - 3 + 1 : ℕ) : ℝ≥0)
  have key :
      ((1 - (2 : ℝ≥0) / (n : ℝ≥0)) * (n : ℝ≥0)) = (n : ℝ≥0) - 2 := by
    rw [tsub_mul, one_mul, div_mul_cancel₀ _ hnne]
  rw [key]
  have hright : (n - 3 + 1 : ℕ) = n - 2 := by omega
  rw [hright, ← NNReal.coe_le_coe, NNReal.coe_sub h2n]
  change (n : ℝ) - 2 ≤ ((n - 2 : ℕ) : ℝ)
  rw [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_ofNat]

/-- **Lower bound: `2/q ≤ ε_mca(C, 1/n)`.**  The explicit `2`-spike plant
(`epsMCA_ge_spike` with `t = 2`) realizes two bad scalars at radius `1/n`.  This is the research
note's two-window plant; here `2 ≤ q` and `n ≥ k + 3` suffice (cleaner than the note's `q ≥ 2n`
sufficient threshold). -/
theorem epsMCA_interiorJ1_ge
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (hq : 2 ≤ Fintype.card F) :
    (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F))
        (mcaLatticePoint (Fintype.card ι)
          (⟨1, by
            have hn : 0 < Fintype.card ι := Fintype.card_pos
            omega⟩ : Fin (Fintype.card ι + 1))) := by
  classical
  set n := Fintype.card ι with hndef
  have hn1 : 1 ≤ n := Fintype.card_pos
  have ht_n : 2 + k ≤ n := by omega
  have hδ : ((1 - mcaLatticePoint n (⟨1, by omega⟩ : Fin (n + 1))) * n : ℝ≥0)
      ≤ ((n - 2 + 1 : ℕ) : ℝ≥0) := by
    rw [mcaLatticePoint]
    simpa using spike_two_size_at_interiorJ1 (n := n) hn1
  have hspike := epsMCA_ge_spike domain k 2
    (mcaLatticePoint n (⟨1, by omega⟩ : Fin (n + 1))) ht_n hq hδ
  simpa using hspike

/-- **GOLD — the exact interior radius-`1/n` MCA error.**  For `RS[F, domain, k]` over an
`n`-point domain with `n ≥ k + 3` and `2 ≤ q`,

  `ε_mca(C, 1/n) = 2/q`.

The upper bound is the resultant cap; the lower bound is the `2`-spike plant. -/
theorem epsMCA_interiorJ1_eq
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (hq : 2 ≤ Fintype.card F) :
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F))
        (mcaLatticePoint (Fintype.card ι)
          (⟨1, by
            have hn : 0 < Fintype.card ι := Fintype.card_pos
            omega⟩ : Fin (Fintype.card ι + 1)))
      = (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  le_antisymm (epsMCA_interiorJ1_le domain hk) (epsMCA_interiorJ1_ge domain hk hq)

/-! ## Faithful threshold consequences of the exact J1 value -/

/-- **Exact J1 lattice satisfaction criterion.**  At the first nonzero MCA lattice point, the
faithful predicate `mcaSatisfies` is equivalent to the single scalar inequality `2 / |F| ≤ ε*`. -/
theorem mcaSatisfies_interiorJ1_iff_two_div_card_le
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (hq : 2 ≤ Fintype.card F)
    (ε_star : ℝ≥0) :
    let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
      have hn : 0 < Fintype.card ι := Fintype.card_pos
      omega⟩
    mcaSatisfies
        (ReedSolomon.code domain k : Set (ι → F)) ε_star j1 ↔
      (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ (ε_star : ℝ≥0∞) := by
  let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
    have hn : 0 < Fintype.card ι := Fintype.card_pos
    omega⟩
  simpa [mcaSatisfies, j1] using
    (show
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F))
          (mcaLatticePoint (Fintype.card ι) j1) ≤ (ε_star : ℝ≥0∞) ↔
        (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ (ε_star : ℝ≥0∞) from by
          rw [epsMCA_interiorJ1_eq domain hk hq])

/-- **J1 satisfaction projection.**  If `2 / |F| ≤ ε*`, then the faithful MCA predicate holds
at the first nonzero MCA lattice point.  This is the threshold-existence-free positive half of
the exact J1 satisfaction criterion. -/
theorem mcaSatisfies_interiorJ1_of_two_div_card_le
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (hq : 2 ≤ Fintype.card F)
    {ε_star : ℝ≥0}
    (hgood : (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ (ε_star : ℝ≥0∞)) :
    let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
      have hn : 0 < Fintype.card ι := Fintype.card_pos
      omega⟩
    mcaSatisfies (ReedSolomon.code domain k : Set (ι → F)) ε_star j1 :=
  (mcaSatisfies_interiorJ1_iff_two_div_card_le domain hk hq ε_star).mpr hgood

/-- **J1 satisfaction obstruction.**  If `ε* < 2 / |F|`, then the faithful MCA predicate
cannot hold at the first nonzero MCA lattice point.  This is the threshold-existence-free
obstruction companion to `mcaThreshold_lt_one_of_interiorJ1_gt`. -/
theorem not_mcaSatisfies_interiorJ1_of_interiorJ1_gt
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (hq : 2 ≤ Fintype.card F)
    {ε_star : ℝ≥0}
    (hbad : (ε_star : ℝ≥0∞) < (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
      have hn : 0 < Fintype.card ι := Fintype.card_pos
      omega⟩
    ¬ mcaSatisfies (ReedSolomon.code domain k : Set (ι → F)) ε_star j1 := by
  let C : Set (ι → F) := ReedSolomon.code domain k
  let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
    have hn : 0 < Fintype.card ι := Fintype.card_pos
    omega⟩
  change ¬ mcaSatisfies C ε_star j1
  intro hsat
  exact (not_le_of_gt hbad)
    ((mcaSatisfies_interiorJ1_iff_two_div_card_le domain hk hq ε_star).mp hsat)

/-- If `2 / |F| ≤ ε*`, the faithful MCA lattice threshold is at least the J1 index. -/
theorem one_le_mcaThreshold_of_interiorJ1
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (hq : 2 ≤ Fintype.card F)
    {ε_star : ℝ≥0}
    (hgood : (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ (ε_star : ℝ≥0∞)) :
    let C : Set (ι → F) := ReedSolomon.code domain k
    let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
      have hn : 0 < Fintype.card ι := Fintype.card_pos
      omega⟩
    let hne : mcaThresholdExists C ε_star :=
      ⟨j1, (mcaSatisfies_interiorJ1_iff_two_div_card_le domain hk hq ε_star).mpr hgood⟩
    j1 ≤ mcaThreshold C ε_star hne := by
  let C : Set (ι → F) := ReedSolomon.code domain k
  let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
    have hn : 0 < Fintype.card ι := Fintype.card_pos
    omega⟩
  have hsat : mcaSatisfies C ε_star j1 :=
    (mcaSatisfies_interiorJ1_iff_two_div_card_le domain hk hq ε_star).mpr hgood
  let hne : mcaThresholdExists C ε_star := ⟨j1, hsat⟩
  exact le_mcaThreshold C ε_star hne hsat

/-- If `ε* < 2 / |F|`, then any existing faithful MCA threshold is strictly below J1. -/
theorem mcaThreshold_lt_one_of_interiorJ1_gt
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (hq : 2 ≤ Fintype.card F)
    {ε_star : ℝ≥0}
    (hbad : (ε_star : ℝ≥0∞) < (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) ε_star) :
    let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
      have hn : 0 < Fintype.card ι := Fintype.card_pos
      omega⟩
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne < j1 := by
  let C : Set (ι → F) := ReedSolomon.code domain k
  let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
    have hn : 0 < Fintype.card ι := Fintype.card_pos
    omega⟩
  by_contra hnot
  have hj1_le : j1 ≤ mcaThreshold C ε_star hne := not_lt.mp hnot
  have hsat_threshold : mcaSatisfies C ε_star (mcaThreshold C ε_star hne) :=
    mcaThreshold_spec C ε_star hne
  have hsat_j1 : mcaSatisfies C ε_star j1 :=
    mcaSatisfies_downward_closed C ε_star hj1_le hsat_threshold
  exact (not_le_of_gt hbad)
    ((mcaSatisfies_interiorJ1_iff_two_div_card_le domain hk hq ε_star).mp hsat_j1)

/-- Four-rate MCA prize lower bracket from the exact J1 value.  When `2 / |F| ≤ ε*` and each
prize-rate degree has a genuine J1 window (`k + 3 ≤ n`), every faithful MCA prize threshold is at
least index `1`. -/
theorem mcaPrizeLattice_one_le_of_interiorJ1
    (domain : ι ↪ F)
    (hk : ∀ r : Fin 4,
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 3 ≤ Fintype.card ι)
    (hq : 2 ≤ Fintype.card F)
    (hgood : (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ (epsStar : ℝ≥0∞)) :
    ∀ r : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
      let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
        have hn : 0 < Fintype.card ι := Fintype.card_pos
        omega⟩
      let hne : mcaThresholdExists C epsStar :=
        ⟨j1,
          (mcaSatisfies_interiorJ1_iff_two_div_card_le domain (hk r) hq epsStar).mpr
            hgood⟩
      j1 ≤ mcaThreshold C epsStar hne := by
  intro r
  exact one_le_mcaThreshold_of_interiorJ1 domain (hk r) hq hgood

/-- Four-rate MCA prize upper bracket below J1 when `ε* < 2 / |F|`.  In that small-field regime,
any existing faithful threshold at the prize rates must be the zero lattice index. -/
theorem mcaPrizeLattice_lt_one_of_interiorJ1_gt
    (domain : ι ↪ F)
    (hk : ∀ r : Fin 4,
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 3 ≤ Fintype.card ι)
    (hq : 2 ≤ Fintype.card F)
    (hbad : (epsStar : ℝ≥0∞) < (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
    (hne : ∀ r : Fin 4,
      mcaThresholdExists
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) :
    ∀ r : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
      let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
        have hn : 0 < Fintype.card ι := Fintype.card_pos
        omega⟩
      mcaThreshold C epsStar (hne r) < j1 := by
  intro r
  exact mcaThreshold_lt_one_of_interiorJ1_gt domain (hk r) hq hbad (hne r)

/-- Four-rate J1 satisfaction projection from the exact J1 value.  When `2 / |F| ≤ ε*` and
each prize-rate degree has a genuine J1 window, every prize-rate code satisfies the faithful MCA
predicate at the J1 lattice point. -/
theorem mcaPrizeLattice_satisfies_one_of_interiorJ1
    (domain : ι ↪ F)
    (hk : ∀ r : Fin 4,
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 3 ≤ Fintype.card ι)
    (hq : 2 ≤ Fintype.card F)
    (hgood : (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ (epsStar : ℝ≥0∞)) :
    ∀ r : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
      let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
        have hn : 0 < Fintype.card ι := Fintype.card_pos
        omega⟩
      mcaSatisfies C epsStar j1 := by
  intro r
  exact mcaSatisfies_interiorJ1_of_two_div_card_le domain (hk r) hq hgood

/-- Four-rate J1 satisfaction obstruction.  If `ε* < 2 / |F|`, then none of the four
prize-rate codes satisfies the faithful MCA predicate at the J1 lattice point. -/
theorem not_mcaPrizeLattice_satisfies_one_of_interiorJ1_gt
    (domain : ι ↪ F)
    (hk : ∀ r : Fin 4,
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 3 ≤ Fintype.card ι)
    (hq : 2 ≤ Fintype.card F)
    (hbad : (epsStar : ℝ≥0∞) < (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    ∀ r : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
      let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
        have hn : 0 < Fintype.card ι := Fintype.card_pos
        omega⟩
      ¬ mcaSatisfies C epsStar j1 := by
  intro r
  exact not_mcaSatisfies_interiorJ1_of_interiorJ1_gt
    (F := F) (ε_star := epsStar) domain
    (k := ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊) (hk r) hq hbad

/-! ## Exact adjacent J1/J2 threshold band -/

/-- **Exact J1 threshold from the exact J1 value and the adjacent `3`-spike obstruction.**

If `2 / |F| ≤ ε* < 3 / |F|`, then J1 satisfies the faithful MCA bound while the explicit
`3`-spike construction makes J2 fail it.  Since the faithful threshold is the greatest
satisfying lattice index, any existing threshold is exactly J1. -/
theorem mcaThreshold_eq_j1_of_interiorJ1_and_spikeJ2
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι)
    (hq3 : 3 ≤ Fintype.card F)
    {ε_star : ℝ≥0}
    (hJ1 : (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ (ε_star : ℝ≥0∞))
    (hJ2 : (ε_star : ℝ≥0∞) < (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) ε_star) :
    let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
      have hn : 0 < Fintype.card ι := Fintype.card_pos
      omega⟩
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne = j1 := by
  let C : Set (ι → F) := ReedSolomon.code domain k
  let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
    have hn : 0 < Fintype.card ι := Fintype.card_pos
    omega⟩
  let j2 : Fin (Fintype.card ι + 1) := ⟨2, by
    have hn : 0 < Fintype.card ι := Fintype.card_pos
    omega⟩
  have hq2 : 2 ≤ Fintype.card F := by omega
  have hsat_j1 : mcaSatisfies C ε_star j1 :=
    (mcaSatisfies_interiorJ1_iff_two_div_card_le domain hk hq2 ε_star).mpr hJ1
  have hle : j1 ≤ mcaThreshold C ε_star hne :=
    le_mcaThreshold C ε_star hne hsat_j1
  have hn3 : 3 ≤ Fintype.card ι := by omega
  have ht_n : 3 + k ≤ Fintype.card ι := by omega
  have hspike_size :
      ((1 - mcaLatticePoint (Fintype.card ι) j2) * (Fintype.card ι : ℝ≥0)) ≤
        ((Fintype.card ι - 3 + 1 : ℕ) : ℝ≥0) := by
    simpa [j2] using spike_three_size_at_interiorJ2 (n := Fintype.card ι) hn3
  have hspike := epsMCA_ge_spike domain k 3
    (mcaLatticePoint (Fintype.card ι) j2) ht_n hq3 hspike_size
  have hbad_j2 :
      epsMCA (F := F) (A := F) C (mcaLatticePoint (Fintype.card ι) j2) >
        (ε_star : ℝ≥0∞) :=
    lt_of_lt_of_le hJ2 (by simpa [C] using hspike)
  have hlt : mcaThreshold C ε_star hne < j2 := by
    by_contra hnot
    have hj2_le : j2 ≤ mcaThreshold C ε_star hne := not_lt.mp hnot
    have hsat_threshold : mcaSatisfies C ε_star (mcaThreshold C ε_star hne) :=
      mcaThreshold_spec C ε_star hne
    have hsat_j2 : mcaSatisfies C ε_star j2 :=
      mcaSatisfies_downward_closed C ε_star hj2_le hsat_threshold
    exact (not_le_of_gt hbad_j2) hsat_j2
  have hval : (mcaThreshold C ε_star hne).val = j1.val := by
    have hle_val : j1.val ≤ (mcaThreshold C ε_star hne).val :=
      Fin.le_iff_val_le_val.mp hle
    have hlt_val : (mcaThreshold C ε_star hne).val < j2.val :=
      Fin.lt_def.mp hlt
    have hj1val : j1.val = 1 := rfl
    have hj2val : j2.val = 2 := rfl
    omega
  exact Fin.ext hval

/-- **Four-rate faithful MCA prize resolution in the adjacent J1/J2 band.**

When every prize-rate Reed-Solomon code has a genuine J1 window and
`2 / |F| ≤ ε* < 3 / |F|`, the faithful MCA prize lattice is exactly the constant J1
assignment. -/
theorem mcaPrizeLatticeResolved_j1_of_interiorJ1_and_spikeJ2
    (domain : ι ↪ F)
    (hk : ∀ r : Fin 4,
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 3 ≤ Fintype.card ι)
    (hq3 : 3 ≤ Fintype.card F)
    (hJ1 : (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ (epsStar : ℝ≥0∞))
    (hJ2 : (epsStar : ℝ≥0∞) < (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    mcaPrizeLatticeResolved domain
      (fun _ : Fin 4 => ⟨1, by
        have hn : 0 < Fintype.card ι := Fintype.card_pos
        omega⟩) := by
  intro r
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
  let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
    have hn : 0 < Fintype.card ι := Fintype.card_pos
    omega⟩
  have hq2 : 2 ≤ Fintype.card F := by omega
  have hsat : mcaSatisfies C epsStar j1 :=
    (mcaSatisfies_interiorJ1_iff_two_div_card_le domain (hk r) hq2 epsStar).mpr hJ1
  let hne : mcaThresholdExists C epsStar := ⟨j1, hsat⟩
  refine ⟨hne, ?_⟩
  simpa [C, j1] using
    (mcaThreshold_eq_j1_of_interiorJ1_and_spikeJ2
      domain (hk r) hq3 hJ1 hJ2 hne)

/-! ## Concrete `ε* = 2⁻¹²⁸` field-size specialization -/

/-- Field-size lower band for the J1 side of the formal prize threshold:
`2/q ≤ 2⁻¹²⁸` follows from `2·2¹²⁸ ≤ q`. -/
theorem two_div_card_le_epsStar_of_card_ge_two_mul_two_pow
    (hcard : (2 : ℕ) * 2 ^ (128 : ℕ) ≤ Fintype.card F) :
    (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ (epsStar : ℝ≥0∞) := by
  set q := Fintype.card F with hq_def
  have heps : (epsStar : ℝ≥0∞) = (2 ^ (128 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [epsStar]
    push_cast
    rw [one_div]
  rw [heps]
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    rw [hq_def]
    exact Fintype.card_ne_zero
  have hqtop : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top q
  rw [ENNReal.div_le_iff hq0 hqtop]
  have hpow_ne_zero : (2 ^ (128 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  have hpow_ne_top : (2 ^ (128 : ℕ) : ℝ≥0∞) ≠ ⊤ := by finiteness
  rw [← ENNReal.div_eq_inv_mul]
  rw [ENNReal.le_div_iff_mul_le (Or.inl hpow_ne_zero) (Or.inl hpow_ne_top)]
  have hcast :
      (((2 : ℕ) * 2 ^ (128 : ℕ) : ℕ) : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
    exact_mod_cast (by simpa [hq_def] using hcard)
  calc (2 : ℝ≥0∞) * (2 ^ (128 : ℕ) : ℝ≥0∞)
      = (((2 : ℕ) * 2 ^ (128 : ℕ) : ℕ) : ℝ≥0∞) := by push_cast; ring
    _ ≤ (q : ℝ≥0∞) := hcast

/-- Field-size upper band for the J2 spike obstruction at the formal prize threshold:
`2⁻¹²⁸ < 3/q` follows from `q < 3·2¹²⁸`. -/
theorem epsStar_lt_three_div_card_of_card_lt_three_mul_two_pow
    (hcard : Fintype.card F < (3 : ℕ) * 2 ^ (128 : ℕ)) :
    (epsStar : ℝ≥0∞) < (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  set q := Fintype.card F with hq_def
  have heps : (epsStar : ℝ≥0∞) = (2 ^ (128 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [epsStar]
    push_cast
    rw [one_div]
  rw [heps]
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    rw [hq_def]
    exact Fintype.card_ne_zero
  have hqtop : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top q
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hq0) (Or.inl hqtop)]
  have hpow_ne_zero : (2 ^ (128 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  have hpow_ne_top : (2 ^ (128 : ℕ) : ℝ≥0∞) ≠ ⊤ := by finiteness
  rw [← ENNReal.div_eq_inv_mul]
  rw [ENNReal.div_lt_iff (Or.inl hpow_ne_zero) (Or.inl hpow_ne_top)]
  have hcast :
      (q : ℝ≥0∞) < (((3 : ℕ) * 2 ^ (128 : ℕ) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast (by simpa [hq_def] using hcard)
  calc (q : ℝ≥0∞)
      < (((3 : ℕ) * 2 ^ (128 : ℕ) : ℕ) : ℝ≥0∞) := hcast
    _ = (3 : ℝ≥0∞) * (2 ^ (128 : ℕ) : ℝ≥0∞) := by push_cast; ring

/-- Every ABF26 prize rate is at most `1/2`. -/
lemma prizeRates_le_half (r : Fin 4) : prizeRates r ≤ (1 / 2 : ℝ≥0) := by
  unfold prizeRates
  have hpow : (2 : ℝ≥0) ^ (1 : ℕ) ≤ 2 ^ (r.val + 1) :=
    pow_le_pow_right₀ one_le_two (by omega)
  rw [pow_one] at hpow
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpow

/-- If `6 ≤ n`, then `3 ≤ n/2`. -/
private lemma three_le_half_mul_of_six_le {n : ℕ} (hn : 6 ≤ n) :
    (3 : ℝ≥0) ≤ (1 / 2 : ℝ≥0) * (n : ℝ≥0) := by
  calc (3 : ℝ≥0) = (1 / 2 : ℝ≥0) * 6 := by norm_num
    _ ≤ (1 / 2 : ℝ≥0) * (n : ℝ≥0) := by
        gcongr
        exact_mod_cast hn

/-- If the evaluation domain has at least six points, every ABF26 prize-rate Reed-Solomon code
has the `k + 3 ≤ n` window needed by the exact interior-J1 theorem. -/
lemma prizeRate_floor_add_three_le_of_card_ge_six (r : Fin 4)
    (hn : 6 ≤ Fintype.card ι) :
    ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 3 ≤ Fintype.card ι := by
  set k := ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ with hk_def
  have hkr : (k : ℝ≥0) ≤ (1 / 2 : ℝ≥0) * (Fintype.card ι : ℝ≥0) := by
    rw [hk_def]
    refine le_trans (Nat.floor_le (zero_le _)) ?_
    gcongr
    exact prizeRates_le_half r
  have hcast : ((k + 3 : ℕ) : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := by
    push_cast
    calc (k : ℝ≥0) + 3
        ≤ (1 / 2 : ℝ≥0) * (Fintype.card ι : ℝ≥0) + 3 := by gcongr
      _ ≤ (1 / 2 : ℝ≥0) * (Fintype.card ι : ℝ≥0) +
            (1 / 2 : ℝ≥0) * (Fintype.card ι : ℝ≥0) := by
          gcongr
          exact three_le_half_mul_of_six_le hn
      _ = (Fintype.card ι : ℝ≥0) := by
          rw [← add_mul]
          norm_num
  exact_mod_cast hcast

/-- **Formal-prize J1 satisfaction projection.**  If every prize-rate RS code has a genuine J1
window and `2·2¹²⁸ ≤ |F|`, then the formal threshold `ε* = 2⁻¹²⁸` is large enough for all four
prize-rate codes to satisfy the faithful MCA predicate at J1. -/
theorem mcaPrizeLattice_satisfies_one_of_interiorJ1_and_card_ge_two_mul_two_pow
    (domain : ι ↪ F)
    (hk : ∀ r : Fin 4,
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 3 ≤ Fintype.card ι)
    (hcard_lo : (2 : ℕ) * 2 ^ (128 : ℕ) ≤ Fintype.card F) :
    ∀ r : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
      let j1 : Fin (Fintype.card ι + 1) := ⟨1, by
        have hn : 0 < Fintype.card ι := Fintype.card_pos
        omega⟩
      mcaSatisfies C epsStar j1 := by
  have hq : 2 ≤ Fintype.card F :=
    le_trans (by norm_num : 2 ≤ (2 : ℕ) * 2 ^ (128 : ℕ)) hcard_lo
  exact mcaPrizeLattice_satisfies_one_of_interiorJ1 domain hk hq
    (two_div_card_le_epsStar_of_card_ge_two_mul_two_pow (F := F) hcard_lo)

/-- **Formal-prize J1 satisfaction projection, with prize-degree windows automatic.**
For domains with at least six evaluation points, `2·2¹²⁸ ≤ |F|` alone supplies the formal
large-field-side J1 satisfaction projection at all four ABF26 prize rates. -/
theorem mcaPrizeLattice_satisfies_one_of_card_ge_six_and_card_ge_two_mul_two_pow
    (domain : ι ↪ F)
    (hn : 6 ≤ Fintype.card ι)
    (hcard_lo : (2 : ℕ) * 2 ^ (128 : ℕ) ≤ Fintype.card F) :
    ∀ r : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
      let j1 : Fin (Fintype.card ι + 1) := ⟨1, by omega⟩
      mcaSatisfies C epsStar j1 :=
  mcaPrizeLattice_satisfies_one_of_interiorJ1_and_card_ge_two_mul_two_pow domain
    (fun r => prizeRate_floor_add_three_le_of_card_ge_six r hn)
    hcard_lo

/-- **Formal-prize adjacent J1/J2 field-size band.**

If every prize-rate RS code has a genuine J1 window and
`2·2¹²⁸ ≤ |F| < 3·2¹²⁸`, then the faithful MCA prize lattice is exactly the constant J1
assignment at the formal threshold `ε* = 2⁻¹²⁸`. -/
theorem mcaPrizeLatticeResolved_j1_of_interiorJ1_and_card_between
    (domain : ι ↪ F)
    (hk : ∀ r : Fin 4,
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 3 ≤ Fintype.card ι)
    (hcard_lo : (2 : ℕ) * 2 ^ (128 : ℕ) ≤ Fintype.card F)
    (hcard_hi : Fintype.card F < (3 : ℕ) * 2 ^ (128 : ℕ)) :
    mcaPrizeLatticeResolved domain
      (fun _ : Fin 4 => ⟨1, by
        have hn : 0 < Fintype.card ι := Fintype.card_pos
        omega⟩) := by
  have hq3 : 3 ≤ Fintype.card F :=
    le_trans (by norm_num : 3 ≤ (2 : ℕ) * 2 ^ (128 : ℕ)) hcard_lo
  exact mcaPrizeLatticeResolved_j1_of_interiorJ1_and_spikeJ2 domain hk hq3
    (two_div_card_le_epsStar_of_card_ge_two_mul_two_pow (F := F) hcard_lo)
    (epsStar_lt_three_div_card_of_card_lt_three_mul_two_pow (F := F) hcard_hi)

/-- **Formal-prize adjacent J1/J2 field-size band, with prize-degree windows automatic.**

For domains with at least six evaluation points, every ABF26 prize-rate degree satisfies
`k_r + 3 ≤ n`. Thus the adjacent J1/J2 field-size band resolves the faithful MCA prize
lattice to the constant J1 assignment without a separate degree-window hypothesis. -/
theorem mcaPrizeLatticeResolved_j1_of_card_ge_six_and_card_between
    (domain : ι ↪ F)
    (hn : 6 ≤ Fintype.card ι)
    (hcard_lo : (2 : ℕ) * 2 ^ (128 : ℕ) ≤ Fintype.card F)
    (hcard_hi : Fintype.card F < (3 : ℕ) * 2 ^ (128 : ℕ)) :
    mcaPrizeLatticeResolved domain
      (fun _ : Fin 4 => ⟨1, Nat.succ_lt_succ Fintype.card_pos⟩) :=
  mcaPrizeLatticeResolved_j1_of_interiorJ1_and_card_between domain
    (fun r => prizeRate_floor_add_three_le_of_card_ge_six r hn)
    hcard_lo hcard_hi

end GrandChallengesLattice

end ProximityGap

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
section AxiomAudit
open ProximityGap.GrandChallengesLattice
#print axioms mcaSatisfies_interiorJ1_of_two_div_card_le
#print axioms not_mcaSatisfies_interiorJ1_of_interiorJ1_gt
#print axioms mcaPrizeLattice_satisfies_one_of_interiorJ1
#print axioms not_mcaPrizeLattice_satisfies_one_of_interiorJ1_gt
#print axioms mcaPrizeLattice_satisfies_one_of_interiorJ1_and_card_ge_two_mul_two_pow
#print axioms mcaPrizeLattice_satisfies_one_of_card_ge_six_and_card_ge_two_mul_two_pow
end AxiomAudit
