/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24ReducedIntersectionMatrix
import ArkLib.Data.CodingTheory.AGL24AgreementHypergraph

/-!
# [AGL24] §2.4: the kernel vector — Lemma 2.8 (issue #346, brick 3)

**Lemma 2.8** of [AGL24] (arXiv 2304.09445): the reduced intersection matrix of an agreement
hypergraph of Reed–Solomon codewords, evaluated at the evaluation points, does **not** have
full column rank — display (2.6): the vector of coefficient differences
`(f⁽¹⁾ − f⁽ᵗ⁾, …, f⁽ᵗ⁻¹⁾ − f⁽ᵗ⁾)` lies in its kernel, and is nonzero when the coefficient
vectors are not all equal.

* `rsEval` — the codeword of a coefficient vector: `c⁽ʲ⁾ᵢ = ∑ₘ fⱼₘ·αᵢᵐ`;
* `coeffDiffVector` — the display-(2.6) vector;
* `RIM_eval_row_dot` — the abstract row-dot computation (the elaboration-robust core);
* `RIM_eval_mulVec_coeffDiff` — **display (2.6)**: the evaluated RIM kills it (row-by-row:
  the Vandermonde blocks evaluate the coefficient differences to codeword differences, and
  both row vertices agree with `y` at the row's position);
* `coeffDiffVector_ne_zero` — nonzero when the coefficient vectors are not all equal;
* `RIM_eval_not_injective` — **Lemma 2.8** in kernel-witness form: a nonzero kernel vector
  exists (the form the rank machinery consumes).

The remaining [AGL24] core after this brick: the probabilistic full-rank theorem (§3–§4:
`RIM_H` at *random* evaluation points has full column rank w.h.p. for `k`-wpc `H` — where
the field-size bound and the symmetry classes of Remark 2.9 enter). That is the campaign's
research-grade heart.
-/

open Finset MvPolynomial

namespace AGL24

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]

/-- The Reed–Solomon codeword of the coefficient vector `f j`: position `i` carries the
evaluation `∑ₘ fⱼₘ·αᵢᵐ`. -/
def rsEval {t k : ℕ} (α : ι → F) (f : Fin (t + 1) → Fin k → F)
    (j : Fin (t + 1)) (i : ι) : F :=
  ∑ m : Fin k, f j m * α i ^ (m : ℕ)

/-- The display-(2.6) vector: blockwise coefficient differences against the last codeword. -/
def coeffDiffVector {t k : ℕ} (f : Fin (t + 1) → Fin k → F) :
    Fin t × Fin k → F :=
  fun jm => f jm.1.castSucc jm.2 - f (Fin.last t) jm.2

/-- The per-block evaluation of the difference vector telescopes to a codeword difference. -/
theorem sum_block_eval {t k : ℕ} (α : ι → F) (f : Fin (t + 1) → Fin k → F)
    (i : ι) (j : Fin (t + 1)) :
    ∑ m : Fin k, α i ^ (m : ℕ) * (f j m - f (Fin.last t) m)
      = rsEval α f j i - rsEval α f (Fin.last t) i := by
  unfold rsEval
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun m _ => by ring

variable [DecidableEq F]

/-! ### Display (2.6) and Lemma 2.8

Proven via the **abstract-edges route**: the row-dot computation is stated over an abstract
edge family (`RIM_eval_row_dot`), so the row subtype's propositions stay small during
rewrite matching — the earlier `whnf` walls came from the agreement-edge filter and `rsEval`
unfoldings embedded in the row's dependent type. Instantiation at the agreement hypergraph
then only *feeds* the heavy facts (never rewrites against them). -/

set_option maxHeartbeats 800000 in
/-- **The abstract row-dot computation** (route (b) of the parked-note): over *abstract*
edges `e` — so the row subtype's propositions stay small during rewrite matching — each
evaluated RIM row dotted with the blockwise difference vector of `g` telescopes to a
difference of block evaluations. The instantiation at agreement edges (Lemma 2.8) feeds the
agreement facts afterwards, with no heavy-term rewriting. -/
theorem RIM_eval_row_dot {t k : ℕ} (e : ι → Finset (Fin (t + 1))) (α : ι → F)
    (g : Fin (t + 1) → Fin k → F) (i : ι) (ju : Fin (t + 1))
    (hmem : ju ∈ e i) (hnonmin : ∃ j' ∈ e i, j' < ju) :
    (∑ jm : Fin t × Fin k,
        (MvPolynomial.eval α) (RIM F e ⟨i, ⟨ju, hmem, hnonmin⟩⟩ jm)
          * (g jm.1.castSucc jm.2 - g (Fin.last t) jm.2))
      = (∑ m : Fin k, α i ^ (m : ℕ)
            * (g ((e i).min' ⟨ju, hmem⟩) m - g (Fin.last t) m))
        - (if ju = Fin.last t then 0
           else ∑ m : Fin k, α i ^ (m : ℕ) * (g ju m - g (Fin.last t) m)) := by
  classical
  set jmin := (e i).min' ⟨ju, hmem⟩ with hjmin
  have hmin_lt : jmin < ju := by
    obtain ⟨j', hj'mem, hj'lt⟩ := hnonmin
    rw [hjmin]
    exact lt_of_le_of_lt (Finset.min'_le (e i) j' hj'mem) hj'lt
  have hmin_ne_last : jmin ≠ Fin.last t := by
    intro h
    exact absurd (h ▸ hmin_lt) (not_lt.mpr (Fin.le_last ju))
  obtain ⟨jmin0, hjmin0⟩ := Fin.exists_castSucc_eq.mpr hmin_ne_last
  rw [Fintype.sum_prod_type]
  have hinner : ∀ j : Fin t,
      (∑ m : Fin k, (MvPolynomial.eval α)
          (RIM F e ⟨i, ⟨ju, hmem, hnonmin⟩⟩ (j, m))
            * (g (j, m).1.castSucc (j, m).2 - g (Fin.last t) (j, m).2))
      = (if j.castSucc = jmin
          then ∑ m : Fin k, α i ^ (m : ℕ) * (g jmin m - g (Fin.last t) m)
          else if j.castSucc = ju
          then -(∑ m : Fin k, α i ^ (m : ℕ) * (g ju m - g (Fin.last t) m))
          else 0) := by
    intro j
    by_cases hj1 : j.castSucc = jmin
    · rw [if_pos hj1]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [RIM_apply_min F e _ (j, m) hj1]
      rw [map_pow, eval_X, hj1]
    · rw [if_neg hj1]
      by_cases hj2 : j.castSucc = ju
      · rw [if_pos hj2]
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [RIM_apply_self F e _ (j, m) hj1 hj2]
        rw [map_neg, map_pow, eval_X, hj2]
        ring
      · rw [if_neg hj2]
        refine Finset.sum_eq_zero fun m _ => ?_
        rw [RIM_apply_other F e _ (j, m) hj1 hj2, map_zero, zero_mul]
  rw [Finset.sum_congr rfl fun j _ => hinner j]
  by_cases hju_last : ju = Fin.last t
  · rw [if_pos hju_last]
    rw [Finset.sum_eq_single jmin0]
    · rw [if_pos hjmin0, sub_zero]
    · intro j _ hjne
      have hne1 : j.castSucc ≠ jmin := fun h =>
        hjne (Fin.castSucc_injective t (h.trans hjmin0.symm))
      have hne2 : j.castSucc ≠ ju := fun h =>
        absurd (h.trans hju_last) (Fin.castSucc_ne_last j)
      rw [if_neg hne1, if_neg hne2]
    · intro h
      exact absurd (Finset.mem_univ jmin0) h
  · rw [if_neg hju_last]
    obtain ⟨ju0, hju0⟩ := Fin.exists_castSucc_eq.mpr hju_last
    have hne0 : jmin0 ≠ ju0 := fun h => by
      rw [h, hju0] at hjmin0
      exact absurd hjmin0.symm (ne_of_lt hmin_lt)
    rw [show (Finset.univ : Finset (Fin t)) = insert jmin0 (Finset.univ.erase jmin0) from
      (Finset.insert_erase (Finset.mem_univ jmin0)).symm]
    rw [Finset.sum_insert (Finset.notMem_erase jmin0 _)]
    rw [if_pos hjmin0]
    rw [Finset.sum_eq_single ju0]
    · have hju0_ne_min : ju0.castSucc ≠ jmin := by
        rw [hju0]
        exact fun h => absurd (h ▸ hmin_lt) (lt_irrefl ju)
      rw [if_neg hju0_ne_min, if_pos hju0]
      ring
    · intro j hj hjne
      have hne1 : j.castSucc ≠ jmin := fun h =>
        (Finset.mem_erase.mp hj).1 (Fin.castSucc_injective t (h.trans hjmin0.symm))
      have hne2 : j.castSucc ≠ ju := fun h =>
        hjne (Fin.castSucc_injective t (h.trans hju0.symm))
      rw [if_neg hne1, if_neg hne2]
    · intro h
      exact absurd (Finset.mem_erase.mpr ⟨hne0.symm, Finset.mem_univ ju0⟩) h

/-- **[AGL24] display (2.6).** The evaluated RIM of the agreement hypergraph kills the
coefficient-difference vector: instantiate the abstract row-dot at the agreement edges and
kill both block evaluations with the agreement facts. -/
theorem RIM_eval_mulVec_coeffDiff {t k : ℕ} (α : ι → F)
    (f : Fin (t + 1) → Fin k → F) (y : ι → F) :
    ((RIM F (agreementEdge y (rsEval α f))).map (MvPolynomial.eval α)).mulVec
      (coeffDiffVector f) = 0 := by
  classical
  funext r
  obtain ⟨i, ju, hju_mem, hju_nonmin⟩ := r
  have hrow := RIM_eval_row_dot (agreementEdge y (rsEval α f)) α f i ju hju_mem hju_nonmin
  have hagree : ∀ j ∈ agreementEdge y (rsEval α f) i, rsEval α f j i = y i := by
    intro j hj
    rw [agreementEdge, Finset.mem_filter] at hj
    exact hj.2
  have hmin_mem := Finset.min'_mem (agreementEdge y (rsEval α f) i) ⟨ju, hju_mem⟩
  show (∑ jm : Fin t × Fin k,
      (MvPolynomial.eval α)
        (RIM F (agreementEdge y (rsEval α f)) ⟨i, ⟨ju, hju_mem, hju_nonmin⟩⟩ jm)
        * coeffDiffVector f jm) = 0
  rw [show (∑ jm : Fin t × Fin k,
      (MvPolynomial.eval α)
        (RIM F (agreementEdge y (rsEval α f)) ⟨i, ⟨ju, hju_mem, hju_nonmin⟩⟩ jm)
        * coeffDiffVector f jm)
    = ∑ jm : Fin t × Fin k,
      (MvPolynomial.eval α)
        (RIM F (agreementEdge y (rsEval α f)) ⟨i, ⟨ju, hju_mem, hju_nonmin⟩⟩ jm)
        * (f jm.1.castSucc jm.2 - f (Fin.last t) jm.2) from rfl]
  rw [hrow]
  rw [sum_block_eval α f i, sum_block_eval α f i]
  rw [hagree _ hmin_mem]
  by_cases hju_last : ju = Fin.last t
  · rw [if_pos hju_last]
    have : rsEval α f (Fin.last t) i = y i := hagree _ (hju_last ▸ hju_mem)
    rw [this, sub_self, sub_zero]
  · rw [if_neg hju_last]
    rw [hagree _ hju_mem]
    ring

/-- The coefficient-difference vector is nonzero when the coefficient vectors are not all
equal. -/
theorem coeffDiffVector_ne_zero {t k : ℕ} {f : Fin (t + 1) → Fin k → F}
    (hne : ∃ j j' : Fin (t + 1), f j ≠ f j') :
    coeffDiffVector f ≠ 0 := by
  intro hzero
  -- All blocks vanish ⟹ every f j equals f (last) ⟹ all equal.
  have hall : ∀ j : Fin (t + 1), f j = f (Fin.last t) := by
    intro j
    by_cases hj : j = Fin.last t
    · rw [hj]
    · obtain ⟨j0, hj0⟩ := Fin.exists_castSucc_eq.mpr hj
      funext m
      have := congrFun hzero (j0, m)
      unfold coeffDiffVector at this
      rw [hj0] at this
      simpa [sub_eq_zero] using this
  obtain ⟨j, j', hjj⟩ := hne
  exact hjj ((hall j).trans (hall j').symm)

/-- **[AGL24] Lemma 2.8 (kernel-witness form).** The evaluated reduced intersection matrix of
an agreement hypergraph of Reed–Solomon codewords with not-all-equal coefficient vectors has
a nonzero kernel vector — it does not have full column rank. -/
theorem RIM_eval_not_injective {t k : ℕ} (α : ι → F)
    (f : Fin (t + 1) → Fin k → F) (y : ι → F)
    (hne : ∃ j j' : Fin (t + 1), f j ≠ f j') :
    ∃ v : Fin t × Fin k → F, v ≠ 0 ∧
      ((RIM F (agreementEdge y (rsEval α f))).map (MvPolynomial.eval α)).mulVec v = 0 :=
  ⟨coeffDiffVector f, coeffDiffVector_ne_zero hne,
    RIM_eval_mulVec_coeffDiff α f y⟩

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.sum_block_eval
#print axioms AGL24.RIM_eval_row_dot
#print axioms AGL24.RIM_eval_mulVec_coeffDiff
#print axioms AGL24.RIM_eval_not_injective
#print axioms AGL24.coeffDiffVector_ne_zero
