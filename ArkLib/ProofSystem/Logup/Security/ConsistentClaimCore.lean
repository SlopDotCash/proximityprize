/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Field

/-!
# The per-multiplicity cleared grand-sum numerator (issue #13, piece α1′ — abstract core)

The adversarial-multiplicity analogue of `grandSumCheckPolyS_ne_zero_of_bad_lookup`: for an
**arbitrary** weight function `m` on the table rows (the prover's round-`0` multiplicity message),
the cleared numerator of the consistent-helpers claim

  `Q_m(X) = ∑_idx ∏_{a ∈ A \ {cv idx}} (X + a)  −  ∑_r (m r) · ∏_{a ∈ A \ {tv r}} (X + a)`

(over the pole value-set `A`, with `cv` the column values and `tv` the table values) is **nonzero**
whenever some column value `v` is unmatched by the table (`v ∉ tv`-image) and its occurrence count
does not vanish in `F`. The witness is the evaluation at `X = −v`: every column term with
`cv idx ≠ v` and **every** table term contains the factor `(X + v)` and dies; the survivors all
contribute the common nonzero value `∏_{a ∈ A \ {v}} (a − v)`, so

  `Q_m(−v) = count · ∏_{a ∈ A \ {v}} (a − v) ≠ 0` — **independently of `m`**.

Together with the degree bound `natDegree Q_m ≤ |A| − 1`, a uniformly random challenge avoiding
the poles is a root of `Q_m` with probability at most `(|A| − 1)/(|F| − poles)` — the `x`-stage of
the outer mid-claim soundness, at the *adversarial* multiplicity.

No `sorry`; axiom audit at the bottom.
-/

open Polynomial Finset

namespace Logup

variable {F : Type} [Field F] [DecidableEq F]
variable {ColIdx Row : Type} [Fintype ColIdx] [Fintype Row]

/-- The per-multiplicity cleared grand-sum numerator over the pole value-set `A`. -/
noncomputable def perMNumerator (A : Finset F) (cv : ColIdx → F) (tv : Row → F)
    (m : Row → F) : Polynomial F :=
  (∑ idx : ColIdx, ∏ a ∈ A.erase (cv idx), (Polynomial.X + Polynomial.C a))
    - ∑ r : Row, Polynomial.C (m r) * ∏ a ∈ A.erase (tv r), (Polynomial.X + Polynomial.C a)

/-- Evaluation of one erased-product factor at `−v` vanishes when the erased value differs from
`v` and `v ∈ A` (the factor `(X + v)` survives the erasure). -/
theorem prod_erase_eval_neg_eq_zero (A : Finset F) (b v : F) (hvA : v ∈ A) (hbv : b ≠ v) :
    (∏ a ∈ A.erase b, (Polynomial.X + Polynomial.C a)).eval (-v) = 0 := by
  rw [Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨(Ne.symm hbv), hvA⟩) ?_
  simp

/-- Evaluation of the `v`-erased product at `−v`: the common survivor value
`∏_{a ∈ A \ {v}} (a − v)`. -/
theorem prod_erase_eval_neg_self (A : Finset F) (v : F) :
    (∏ a ∈ A.erase v, (Polynomial.X + Polynomial.C a)).eval (-v)
      = ∏ a ∈ A.erase v, (a - v) := by
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  simp [sub_eq_neg_add]

/-- **The per-multiplicity numerator does not vanish at the unmatched value** — independently of
the weight `m`: only the `v`-matching column terms survive evaluation at `−v`, each contributing
the common nonzero survivor value. -/
theorem perMNumerator_eval_neg_unmatched (A : Finset F) (cv : ColIdx → F) (tv : Row → F)
    (m : Row → F) (v : F) (hvA : v ∈ A)
    (hvt : ∀ r : Row, tv r ≠ v) :
    (perMNumerator A cv tv m).eval (-v)
      = ((Finset.univ.filter (fun idx : ColIdx => cv idx = v)).card : F)
          * ∏ a ∈ A.erase v, (a - v) := by
  classical
  unfold perMNumerator
  rw [Polynomial.eval_sub, Polynomial.eval_finset_sum, Polynomial.eval_finset_sum]
  -- The table sum dies entirely.
  have htable : ∑ r : Row,
      (Polynomial.C (m r) * ∏ a ∈ A.erase (tv r), (Polynomial.X + Polynomial.C a)).eval (-v)
      = 0 := by
    refine Finset.sum_eq_zero (fun r _ => ?_)
    rw [Polynomial.eval_mul, prod_erase_eval_neg_eq_zero A (tv r) v hvA (hvt r), mul_zero]
  rw [htable, sub_zero]
  -- The column sum reduces to the `v`-matching survivors.
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun idx => cv idx = v)]
  have hdead : ∑ idx ∈ Finset.univ.filter (fun idx : ColIdx => ¬ cv idx = v),
      (∏ a ∈ A.erase (cv idx), (Polynomial.X + Polynomial.C a)).eval (-v) = 0 := by
    refine Finset.sum_eq_zero (fun idx hidx => ?_)
    rw [Finset.mem_filter] at hidx
    exact prod_erase_eval_neg_eq_zero A (cv idx) v hvA hidx.2
  have halive : ∑ idx ∈ Finset.univ.filter (fun idx : ColIdx => cv idx = v),
      (∏ a ∈ A.erase (cv idx), (Polynomial.X + Polynomial.C a)).eval (-v)
      = ((Finset.univ.filter (fun idx : ColIdx => cv idx = v)).card : F)
          * ∏ a ∈ A.erase v, (a - v) := by
    rw [Finset.sum_congr rfl (fun idx hidx => ?_), Finset.sum_const, nsmul_eq_mul]
    rw [Finset.mem_filter] at hidx
    rw [hidx.2]
    exact prod_erase_eval_neg_self A v
  rw [hdead, add_zero, halive]

/-- **Nonvanishing of the per-multiplicity numerator** (the α1′ core): if some column value `v` is
unmatched by the table, occurs a non-vanishing number of times (in `F`), and all values lie in the
pole set `A`, then `Q_m ≠ 0` for **every** weight `m`. -/
theorem perMNumerator_ne_zero (A : Finset F) (cv : ColIdx → F) (tv : Row → F)
    (m : Row → F) (v : F) (hvA : v ∈ A)
    (hvt : ∀ r : Row, tv r ≠ v)
    (hcount : ((Finset.univ.filter (fun idx : ColIdx => cv idx = v)).card : F) ≠ 0)
    (hA : ∀ a ∈ A.erase v, a - v ≠ 0) :
    perMNumerator A cv tv m ≠ 0 := by
  intro hzero
  have heval := perMNumerator_eval_neg_unmatched A cv tv m v hvA hvt
  rw [hzero] at heval
  simp only [Polynomial.eval_zero] at heval
  have hprod : (∏ a ∈ A.erase v, (a - v)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hA
  exact (mul_ne_zero hcount hprod) heval.symm

/-- **Degree bound**: every erased product has `|A| − 1` linear factors, so
`natDegree Q_m ≤ |A| − 1` — the `x`-stage Schwartz–Zippel budget at the adversarial
multiplicity. -/
theorem perMNumerator_natDegree_le (A : Finset F) (cv : ColIdx → F) (tv : Row → F)
    (m : Row → F) (hcv : ∀ idx, cv idx ∈ A) (htv : ∀ r, tv r ∈ A) :
    (perMNumerator A cv tv m).natDegree ≤ A.card - 1 := by
  classical
  unfold perMNumerator
  refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
  rw [max_le_iff]
  constructor
  · refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun idx _ => ?_⟩
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    calc ∑ a ∈ A.erase (cv idx), (Polynomial.X + Polynomial.C a).natDegree
        ≤ ∑ _a ∈ A.erase (cv idx), 1 := by
          refine Finset.sum_le_sum (fun a _ => ?_)
          exact le_trans (Polynomial.natDegree_add_le _ _) (by simp)
      _ = (A.erase (cv idx)).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ = A.card - 1 := Finset.card_erase_of_mem (hcv idx)
  · refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun r _ => ?_⟩
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    rw [Polynomial.natDegree_C, zero_add]
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    calc ∑ a ∈ A.erase (tv r), (Polynomial.X + Polynomial.C a).natDegree
        ≤ ∑ _a ∈ A.erase (tv r), 1 := by
          refine Finset.sum_le_sum (fun a _ => ?_)
          exact le_trans (Polynomial.natDegree_add_le _ _) (by simp)
      _ = (A.erase (tv r)).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ = A.card - 1 := Finset.card_erase_of_mem (htv r)

/-- **Root-count**: for every weight `m`, the per-multiplicity numerator has at most `|A| − 1`
roots — the adversarial `x`-stage budget, uniform in `m`. -/
theorem perMNumerator_roots_card_le [Fintype F] (A : Finset F) (cv : ColIdx → F) (tv : Row → F)
    (m : Row → F) (v : F) (hvA : v ∈ A)
    (hvt : ∀ r : Row, tv r ≠ v)
    (hcount : ((Finset.univ.filter (fun idx : ColIdx => cv idx = v)).card : F) ≠ 0)
    (hA : ∀ a ∈ A.erase v, a - v ≠ 0)
    (hcv : ∀ idx, cv idx ∈ A) (htv : ∀ r, tv r ∈ A) :
    (Finset.univ.filter (fun x : F => (perMNumerator A cv tv m).eval x = 0)).card
      ≤ A.card - 1 := by
  classical
  have hne := perMNumerator_ne_zero A cv tv m v hvA hvt hcount hA
  have hdeg := perMNumerator_natDegree_le A cv tv m hcv htv
  calc (Finset.univ.filter (fun x : F => (perMNumerator A cv tv m).eval x = 0)).card
      ≤ (perMNumerator A cv tv m).roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
        exact hx.2
    _ ≤ (perMNumerator A cv tv m).roots.card := Multiset.toFinset_card_le _
    _ ≤ (perMNumerator A cv tv m).natDegree := Polynomial.card_roots' _
    _ ≤ A.card - 1 := hdeg

/-- One pole fraction over the common denominator: `(x + b)⁻¹ = ∏_{a ∈ A∖b}(x+a) / ∏_{a∈A}(x+a)`
for `b ∈ A` and a pole-free `x`. -/
theorem inv_eq_eraseProd_div (A : Finset F) (b x : F) (hb : b ∈ A)
    (hx : ∀ a ∈ A, x + a ≠ 0) :
    (x + b)⁻¹ = (∏ a ∈ A.erase b, (x + a)) / ∏ a ∈ A, (x + a) := by
  have hfull : (∏ a ∈ A, (x + a)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hx
  rw [eq_div_iff hfull, ← Finset.mul_prod_erase A _ hb]
  rw [← mul_assoc, inv_mul_cancel₀ (hx b hb), one_mul]

/-- **The fraction-sum value bridge** (α-bridge, abstract half): at a pole-free `x`, the
partial-fraction total `∑ 1/(x + cv idx) − ∑ m r/(x + tv r)` equals the per-multiplicity cleared
numerator over the common denominator. The consistent-helpers LogUp claim is (up to global sign)
exactly this total, so its zero set at pole-free challenges is the root set of `perMNumerator`. -/
theorem fracSum_eq_perMNumerator_div (A : Finset F) (cv : ColIdx → F) (tv : Row → F)
    (m : Row → F) (x : F)
    (hx : ∀ a ∈ A, x + a ≠ 0) (hcv : ∀ idx, cv idx ∈ A) (htv : ∀ r, tv r ∈ A) :
    (∑ idx : ColIdx, (x + cv idx)⁻¹) - (∑ r : Row, m r * (x + tv r)⁻¹)
      = (perMNumerator A cv tv m).eval x / ∏ a ∈ A, (x + a) := by
  classical
  have hcols : (∑ idx : ColIdx, (x + cv idx)⁻¹)
      = (∑ idx : ColIdx, ∏ a ∈ A.erase (cv idx), (x + a)) / ∏ a ∈ A, (x + a) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun idx _ => ?_)
    exact inv_eq_eraseProd_div A (cv idx) x (hcv idx) hx
  have htbl : (∑ r : Row, m r * (x + tv r)⁻¹)
      = (∑ r : Row, m r * ∏ a ∈ A.erase (tv r), (x + a)) / ∏ a ∈ A, (x + a) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [inv_eq_eraseProd_div A (tv r) x (htv r) hx, mul_div_assoc]
  rw [hcols, htbl, div_sub_div_same]
  congr 1
  unfold perMNumerator
  rw [Polynomial.eval_sub, Polynomial.eval_finset_sum, Polynomial.eval_finset_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun idx _ => ?_)
    rw [Polynomial.eval_prod]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    simp
  · refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
    congr 1
    refine Finset.prod_congr rfl (fun a _ => ?_)
    simp

end Logup

/- Axiom audit. -/
#print axioms Logup.perMNumerator_ne_zero
#print axioms Logup.perMNumerator_natDegree_le
#print axioms Logup.perMNumerator_roots_card_le
#print axioms Logup.fracSum_eq_perMNumerator_div
