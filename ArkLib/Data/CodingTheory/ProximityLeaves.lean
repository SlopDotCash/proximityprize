/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.Basic.Entropy
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Proximity-prize foundation leaves

Verified leaf lemmas toward the Layer-2/3 proximity-prize theorems (see
research/formal/arklib-patches/proximity-prize-infrastructure-roadmap.md):
the GK16 folded-Wronskian degree bound (subspace-design cornerstone), the
AGL23 alphabet-size extraction step, a q-ary entropy identity, and linear-code
cardinality. Each produced by the foundation-research workflow and
independently re-verified (compiles, sorry-free, axiom-clean).
-/

/- ════ from GK16 folded-Wronskian degree bound (subspace-design Layer 2) ════ -/
/-!
# Leaf sub-lemma for `frs_is_subspaceDesign_gk16` (ABF26 Theorem 2.18 [GK16])

One genuine, dependency-ordered ingredient of the folded-Wronskian degree-counting
argument of Guruswami–Kopparty "Explicit Subspace Designs": the degree bound of the
folded Wronskian determinant, `deg L ≤ (k-1)·s`. Compiles sorry-free; `#print axioms`
gives exactly `[propext, Classical.choice, Quot.sound]` (no sorryAx).
-/

open Polynomial Matrix Finset

namespace ArkLib.FRS.GK16

/-- A per-row dilation matrix: `M a j = (P j).comp (q a)` where each `q a` has degree ≤ 1
(the folded-Wronskian shape uses `q a = C (ω^a) * X`). -/
noncomputable def dilateMatrix {F : Type*} [CommRing F] {s : ℕ}
    (P : Fin s → F[X]) (q : Fin s → F[X]) : Matrix (Fin s) (Fin s) F[X] :=
  fun a j => (P j).comp (q a)

/-- **Folded Wronskian** (GK16 Definition 11, `t = s` case). With `q a = C (ω^a) * X`
this is `det [ (P j)(ω^a · X) ]_{a, j < s}`. -/
noncomputable def foldedWronskian {F : Type*} [CommRing F] {s : ℕ}
    (P : Fin s → F[X]) (ω : F) : F[X] :=
  (dilateMatrix P (fun a => Polynomial.C (ω ^ (a : ℕ)) * Polynomial.X)).det

/-- A single dilated entry `(P j).comp (q a)` has degree at most `natDegree (P j)`
when the substitution polynomial `q a` has degree ≤ 1. -/
lemma natDegree_comp_dilate_le {F : Type*} [CommRing F] (p q : F[X])
    (hq : q.natDegree ≤ 1) :
    (p.comp q).natDegree ≤ p.natDegree := by
  calc (p.comp q).natDegree ≤ p.natDegree * q.natDegree := natDegree_comp_le
    _ ≤ p.natDegree * 1 := by exact Nat.mul_le_mul_left _ hq
    _ = p.natDegree := by rw [mul_one]

/-- **Degree bound for the dilation determinant (GK16 / ABF26 T2.18, the `deg L ≤
(k-1)s` step).** If every `P j` has degree `< k` and every substitution polynomial
`q a` has degree ≤ 1, the determinant of the `s × s` dilation matrix has degree at
most `s · (k - 1)`. -/
theorem natDegree_dilateMatrix_det_le {F : Type*} [CommRing F] {s k : ℕ}
    (P : Fin s → F[X]) (q : Fin s → F[X])
    (hP : ∀ j, (P j).natDegree ≤ k - 1)
    (hq : ∀ a, (q a).natDegree ≤ 1) :
    (dilateMatrix P q).det.natDegree ≤ s * (k - 1) := by
  rw [Matrix.det_apply']
  refine (natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, ?_⟩
  intro σ _hσ
  refine (natDegree_mul_le).trans ?_
  rw [natDegree_intCast, zero_add]
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ a : Fin s, ((dilateMatrix P q) (σ a) a).natDegree
      ≤ ∑ _a : Fin s, (k - 1) := by
        refine Finset.sum_le_sum ?_
        intro a _ha
        exact (natDegree_comp_dilate_le (P a) (q (σ a)) (hq (σ a))).trans (hP a)
    _ = s * (k - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]

/-- The folded Wronskian satisfies the GK16 degree bound: if every `P j` has degree
`< k`, then `natDegree (foldedWronskian P ω) ≤ s · (k - 1)`. -/
theorem natDegree_foldedWronskian_le {F : Type*} [CommRing F] {s k : ℕ}
    (P : Fin s → F[X]) (ω : F)
    (hP : ∀ j, (P j).natDegree ≤ k - 1) :
    (foldedWronskian P ω).natDegree ≤ s * (k - 1) := by
  unfold foldedWronskian
  refine natDegree_dilateMatrix_det_le P _ hP (fun a => ?_)
  calc (Polynomial.C (ω ^ (a : ℕ)) * Polynomial.X).natDegree
      ≤ (Polynomial.C (ω ^ (a : ℕ))).natDegree + Polynomial.X.natDegree :=
        natDegree_mul_le
    _ ≤ 0 + 1 := by
        gcongr
        · exact (natDegree_C _).le
        · exact natDegree_X_le
    _ = 1 := by ring

end ArkLib.FRS.GK16

/- ════ from AGL23 alphabet-size extraction leaf ════ -/
open Real

/-- **Alphabet-size extraction leaf (AGL23 / arXiv:2308.13424, final algebraic step).**
From a counting bound `2^m ≤ (q:ℝ)^t` with `1 ≤ q` and `1 ≤ t`, derive the headline
exponential alphabet lower bound `2 ^ (m / t) ≤ q`. -/
theorem alphabet_lower_of_pow_ge
    (q : ℝ) (t : ℝ) (m : ℝ)
    (hq : 1 ≤ q) (ht : 1 ≤ t)
    (hcount : (2 : ℝ) ^ m ≤ q ^ t) :
    (2 : ℝ) ^ (m / t) ≤ q := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hmono :
      ((2 : ℝ) ^ m) ^ (1 / t) ≤ (q ^ t) ^ (1 / t) :=
    Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) m) hcount (by positivity)
  have hrhs : (q ^ t) ^ (1 / t) = q := by
    rw [← Real.rpow_mul (le_of_lt hq0), mul_one_div, div_self (ne_of_gt ht0), Real.rpow_one]
  have hlhs : ((2 : ℝ) ^ m) ^ (1 / t) = (2 : ℝ) ^ (m / t) := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), mul_one_div]
  rw [hrhs, hlhs] at hmono
  exact hmono

/- ════ from qEntropy ↔ q-ary entropy identity ════ -/
namespace CodingTheory

open Real

/-- **Base-change bridge for the `q`-ary entropy.** For `q ≥ 2`, ArkLib's `qEntropy`
(defined with base-`q` logarithms `Real.logb q`) equals Mathlib's `Real.qaryEntropy`
(defined with natural logarithms) divided by `Real.log q`. Stated multiplicatively:

  `qEntropy q x * Real.log q = Real.qaryEntropy q x`   (for `2 ≤ q`).

The hypothesis `2 ≤ q` is necessary: for `q ∈ {0, 1}` we have `Real.log q = 0`, so the
LHS collapses to `0` while the RHS `qaryEntropy q x` is generally nonzero — the identity
is FALSE there. This matches the regime of every consumer (`q = |F| ≥ 2` for a field). -/
theorem qEntropy_mul_log_eq_qaryEntropy {q : ℕ} (hq : 2 ≤ q) (x : ℝ) :
    qEntropy q x * Real.log q = Real.qaryEntropy q x := by
  -- `q ≥ 2` ⟹ `log q ≠ 0`.
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlog : Real.log q ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by
    intro h; rw [h] at hq1; exact lt_irrefl _ hq1)
  -- Unfold both sides to a `Real.log`/`Real.logb` normal form.
  unfold qEntropy Real.qaryEntropy Real.binEntropy
  rw [Real.logb, Real.logb, Real.logb]
  -- Reduce the integer cast `((q : ℤ) - 1 : ℝ)` to `((q : ℝ) - 1)`.
  push_cast
  rw [Real.log_inv, Real.log_inv]
  -- Now both sides are rational expressions in `log (q-1)`, `log x`, `log (1-x)`, `log q`.
  field_simp
  ring

end CodingTheory

-- #print axioms CodingTheory.qEntropy_mul_log_eq_qaryEntropy
-- ⟹ [propext, Classical.choice, Quot.sound]  (sorry-free, axiom-clean)
-- Compiled with `lake env lean` on leanprover/lean4:v4.29.0 in the ArkLib toolchain.

/- ════ from linear-code cardinality |C| = q^dim ════ -/
open Polynomial

namespace ReedSolomon

variable {ι : Type} [Fintype ι] {F : Type} [Field F] [Fintype F]

/-- **Cardinality of a Reed-Solomon code.** For an injective evaluation domain
`domain : ι ↪ F` and degree bound `k ≤ |ι|`, the Reed-Solomon code `code domain k` has
exactly `|F|^k` codewords. Consequence of `dim_eq_deg_of_le'` (finrank = `k`) and
`Module.card_eq_pow_finrank`. -/
theorem ncard_code_eq_pow_card
    (domain : ι ↪ F) (k : ℕ) (hk : k ≤ Fintype.card ι) :
    Set.ncard ((ReedSolomon.code domain k : Submodule F (ι → F)) : Set (ι → F))
      = Fintype.card F ^ k := by
  classical
  haveI : Fintype (ReedSolomon.code domain k) := Fintype.ofFinite _
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  simp only [SetLike.coe_sort_coe]
  rw [Module.card_eq_pow_finrank (K := F) (V := ReedSolomon.code domain k)]
  have hdim : LinearCode.dim (ReedSolomon.code domain k) = k :=
    ReedSolomon.dim_eq_deg_of_le' hk
  rw [show Module.finrank F (ReedSolomon.code domain k)
        = LinearCode.dim (ReedSolomon.code domain k) from rfl, hdim]

end ReedSolomon

-- #print axioms ReedSolomon.ncard_code_eq_pow_card
-- ⇒ depends on axioms: [propext, Classical.choice, Quot.sound]
-- (clean; sorry-free; compiles exit 0)
