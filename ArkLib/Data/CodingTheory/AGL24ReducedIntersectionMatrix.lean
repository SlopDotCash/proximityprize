/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24WeakPartition

/-!
# [AGL24] §2.3: the reduced intersection matrix (issue #346, brick 2)

**Definition 2.6** of [AGL24] (arXiv 2304.09445), formalized faithfully: the reduced
intersection matrix `RIM_{k,q,H}` of a hypergraph `H = ([t], (e₁, …, eₙ))` is a
`wt(E) × (t−1)k` matrix whose rows are indexed by pairs (edge `i`, non-minimal vertex `j`
of `eᵢ`), with row blocks of length `k` per non-reduced vertex (`[t−1]` — the last vertex is
reduced away): the minimal vertex's block carries the Vandermonde row
`Vᵢ = [1, Xᵢ, …, Xᵢ^{k−1}]`, vertex `j`'s block carries `−Vᵢ` (when `j` is not the reduced
vertex), all other blocks vanish.

* `RIMRowIdx` — the row index type: `Σ i, {j ∈ eᵢ : j not minimal in eᵢ}`;
* `card_RIMRowIdx` — **the dimension fidelity lemma**: the number of rows is exactly the
  total edge weight `∑ᵢ wt(eᵢ)` of brick 0 (the paper's "`wt(E) × (t−1)k` matrix");
* `RIM` — the matrix itself, with entries in the polynomial ring `F[X₁, …, Xₙ]` (the paper
  works in the fraction field `F_q(X₁, …, Xₙ)`; the entries are polynomials, and rank over
  the fraction field is the next brick's concern);
* the three entry equations (`RIM_apply_min`, `RIM_apply_self`, `RIM_apply_other`).

Next bricks: the rank ⟹ average-radius-list-decodability implication (§2.4) and the
probabilistic full-rank theorem (the campaign's research-grade core).
-/

open Finset

namespace AGL24

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The row index type of the reduced intersection matrix: one row per (edge, non-minimal
vertex of that edge). Empty and singleton edges contribute no rows. -/
def RIMRowIdx {t : ℕ} (e : ι → Finset (Fin t)) : Type _ :=
  Σ i : ι, {j : Fin t // j ∈ e i ∧ ∃ j' ∈ e i, j' < j}

instance {t : ℕ} (e : ι → Finset (Fin t)) : Fintype (RIMRowIdx e) :=
  inferInstanceAs (Fintype (Σ i : ι, {j : Fin t // j ∈ e i ∧ ∃ j' ∈ e i, j' < j}))

/-- Per-edge row count: the non-minimal vertices of `eᵢ` number exactly `wt(eᵢ)`. -/
theorem card_nonminimal_eq_edgeWeight {t : ℕ} (s : Finset (Fin t)) :
    (s.filter (fun j => ∃ j' ∈ s, j' < j)).card = edgeWeight s := by
  classical
  unfold edgeWeight
  rcases Finset.eq_empty_or_nonempty s with rfl | hne
  · simp
  · -- The non-minimal elements are exactly s minus its minimum.
    have hfilter : s.filter (fun j => ∃ j' ∈ s, j' < j) = s.erase (s.min' hne) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hj, j', hj', hlt⟩
        refine ⟨?_, hj⟩
        intro heq
        exact absurd (heq ▸ Finset.min'_le s j' hj') (not_le.mpr hlt)
      · rintro ⟨hne', hj⟩
        refine ⟨hj, s.min' hne, Finset.min'_mem s hne, ?_⟩
        exact lt_of_le_of_ne (Finset.min'_le s j hj) (Ne.symm hne')
    rw [hfilter, Finset.card_erase_of_mem (Finset.min'_mem s hne)]

/-- **The dimension fidelity lemma**: the reduced intersection matrix has exactly
`∑ᵢ wt(eᵢ)` rows — the paper's "`wt(E) × (t−1)k` matrix" claim, row side. -/
theorem card_RIMRowIdx {t : ℕ} (e : ι → Finset (Fin t)) :
    Fintype.card (RIMRowIdx e) = ∑ i, edgeWeight (e i) := by
  rw [show Fintype.card (RIMRowIdx e)
      = Fintype.card (Σ i : ι, {j : Fin t // j ∈ e i ∧ ∃ j' ∈ e i, j' < j}) from rfl]
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show Fintype.card {j : Fin t // j ∈ e i ∧ ∃ j' ∈ e i, j' < j}
      = ((Finset.univ.filter (fun j : Fin t => j ∈ e i ∧ ∃ j' ∈ e i, j' < j))).card from
    Fintype.card_subtype _]
  rw [show Finset.univ.filter (fun j : Fin t => j ∈ e i ∧ ∃ j' ∈ e i, j' < j)
      = (e i).filter (fun j => ∃ j' ∈ e i, j' < j) from by
    ext j
    simp [Finset.mem_filter]]
  exact card_nonminimal_eq_edgeWeight (e i)

variable (F : Type*) [Field F]

open MvPolynomial in
/-- **[AGL24] Definition 2.6 (reduced intersection matrix).** Entries in `F[X₁, …, Xₙ]`
(edges indexed by `ι`); columns indexed by (non-reduced vertex `∈ [t−1]`) × (degree `< k`).
The row of (edge `i`, non-minimal vertex `j`): the minimal vertex's block is the Vandermonde
row `Xᵢ^m`, vertex `j`'s block is `−Xᵢ^m` (absent if `j` is the reduced last vertex), the
rest vanish. -/
noncomputable def RIM {t k : ℕ} (e : ι → Finset (Fin (t + 1))) :
    Matrix (RIMRowIdx e) (Fin t × Fin k) (MvPolynomial ι F) :=
  fun r c =>
    let i := r.1
    let jmin := (e i).min' ⟨r.2.val, r.2.property.1⟩
    if c.1.castSucc = jmin then (X i : MvPolynomial ι F) ^ (c.2 : ℕ)
    else if c.1.castSucc = r.2.val then -((X i : MvPolynomial ι F) ^ (c.2 : ℕ))
    else 0

open MvPolynomial in
/-- Entry equation, minimal-vertex block: the Vandermonde row. -/
theorem RIM_apply_min {t k : ℕ} (e : ι → Finset (Fin (t + 1))) (r : RIMRowIdx e)
    (c : Fin t × Fin k)
    (h : c.1.castSucc = (e r.1).min' ⟨r.2.val, r.2.property.1⟩) :
    RIM F e r c = (X r.1 : MvPolynomial ι F) ^ (c.2 : ℕ) := by
  unfold RIM
  rw [if_pos h]

open MvPolynomial in
/-- Entry equation, own-vertex block: the negated Vandermonde row. (The hypothesis
`c.1.castSucc = r.2.val` can only hold when `r.2.val` is not the reduced vertex `t`, since
`castSucc` never reaches it — the paper's "if `j_u ≠ t`" is automatic.) -/
theorem RIM_apply_self {t k : ℕ} (e : ι → Finset (Fin (t + 1))) (r : RIMRowIdx e)
    (c : Fin t × Fin k)
    (hmin : c.1.castSucc ≠ (e r.1).min' ⟨r.2.val, r.2.property.1⟩)
    (h : c.1.castSucc = r.2.val) :
    RIM F e r c = -((X r.1 : MvPolynomial ι F) ^ (c.2 : ℕ)) := by
  unfold RIM
  rw [if_neg hmin, if_pos h]

open MvPolynomial in
/-- Entry equation, all other blocks vanish. -/
theorem RIM_apply_other {t k : ℕ} (e : ι → Finset (Fin (t + 1))) (r : RIMRowIdx e)
    (c : Fin t × Fin k)
    (hmin : c.1.castSucc ≠ (e r.1).min' ⟨r.2.val, r.2.property.1⟩)
    (hself : c.1.castSucc ≠ r.2.val) :
    RIM F e r c = 0 := by
  unfold RIM
  rw [if_neg hmin, if_neg hself]

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.card_RIMRowIdx
#print axioms AGL24.RIM_apply_min
#print axioms AGL24.RIM_apply_self
#print axioms AGL24.RIM_apply_other
