/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# RingSwitching trace/tensor algebra (issue #29)

The degree-bounded agreement counting + the tensor coordinate maps phi0/phi1 with their product
and smul identities. The KState design decision is separate.
-/

open Polynomial Finset
open scoped TensorProduct

namespace Issue29Ring

/-! ================================================================
    (A) SCHWARTZ–ZIPPEL RESIDUAL — the math that PRICES the KState weakening.

    This is the standalone core of `ArkLib/ToMathlib/KStateWeaken.lean`
    (`card_filter_eval_eq_le_natDegree`, `prob_badPolyAgreement_le`) and of
    `ExtractedIssueBricks.lean` (`Polynomial.card_filter_eval_zero_le`).
    Re-proved here from `Polynomial.card_roots'` with no ArkLib dependency.
    ================================================================ -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Named per-round residual = the weakened-KState bad event.**
The prover message `p` differs from the ground-truth round polynomial `q` (so the
strong KState check `p = q` FAILS), yet they agree at the verifier's challenge `r`
(so the next-round target stays consistent and round-by-round extraction silently
fails).  The whole point of the weakening: this event is *rare*, not impossible. -/
def badPolyAgreement (r : F) (p q : F[X]) : Prop :=
  p ≠ q ∧ p.eval r = q.eval r

noncomputable instance decidablePred_badPolyAgreement (p q : F[X]) :
    DecidablePred fun r : F => badPolyAgreement r p q := by
  classical
  infer_instance

/-- **Root-counting core (Schwartz–Zippel, finite-field form).**
For two distinct polynomials, the set of challenges on which they agree has
cardinality ≤ `natDegree (p - q)`.  Proven from mathlib's `Polynomial.card_roots'`
applied to `p - q`.  This is the cardinality fact that becomes the `D/|F|` numerator
once divided by `Fintype.card F`. -/
theorem card_filter_eval_eq_le_natDegree {p q : F[X]} (hpq : p ≠ q) :
    (Finset.univ.filter (fun r : F => p.eval r = q.eval r)).card ≤ (p - q).natDegree := by
  classical
  have hd0 : p - q ≠ 0 := sub_ne_zero.mpr hpq
  -- The agreement set is contained in the root set of `p - q`.
  have hsub :
      (Finset.univ.filter (fun r : F => p.eval r = q.eval r)) ⊆ (p - q).roots.toFinset := by
    intro r hr
    rw [Finset.mem_filter] at hr
    have hroot : (p - q).IsRoot r := by
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, hr.2, sub_self]
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hd0).mpr hroot)
  calc (Finset.univ.filter (fun r : F => p.eval r = q.eval r)).card
      ≤ (p - q).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (p - q).roots := (p - q).roots.toFinset_card_le
    _ ≤ (p - q).natDegree := Polynomial.card_roots' (p - q)

/-- **Degree-budget form.** Bound the agreement-set cardinality by any common degree
bound `D` (`natDegree p ≤ D`, `natDegree q ≤ D`).  This is the exact numerator that
the probability wrapper divides by `|F|`. -/
theorem card_filter_eval_eq_le_of_degree_le {p q : F[X]} {D : ℕ}
    (hpq : p ≠ q) (hp : p.natDegree ≤ D) (hq : q.natDegree ≤ D) :
    (Finset.univ.filter (fun r : F => p.eval r = q.eval r)).card ≤ D := by
  refine le_trans (card_filter_eval_eq_le_natDegree hpq) ?_
  exact le_trans (Polynomial.natDegree_sub_le p q) (max_le hp hq)

/-- **The full bad event (with the `p ≠ q` conjunct) reduces to the bare agreement
filter** when `p ≠ q`.  This is the step the probability wrapper uses to drop the
`badPolyAgreement` conjunction before applying root counting. -/
theorem filter_badPolyAgreement_eq {p q : F[X]} (hpq : p ≠ q) :
    (Finset.univ.filter (fun r : F => badPolyAgreement r p q))
      = Finset.univ.filter (fun r : F => p.eval r = q.eval r) := by
  apply Finset.filter_congr
  intro r _
  simp only [badPolyAgreement, and_iff_right_iff_imp]
  exact fun _ => hpq

/-- **Degree-2 specialization = the sharp `2/|F|` ring-switching per-round error.**
The ring-switching / Binius round polynomial has degree ≤ 2 (carrier `↥F⦃≤ 2⦄[X]`).
Here we state the cardinality form `#{r : p(r)=q(r)} ≤ 2`; dividing by `|F|` (done by
the in-tree `Pr_{r ←$ᵖ F}[…]` wrapper `prob_badPolyAgreement_degree_two_le`) gives the
`2/|F|` knowledge error that replaces the current trivial `roundKnowledgeError = 1`. -/
theorem card_filter_eval_eq_degree_two {p q : F[X]}
    (hpq : p ≠ q) (hp : p.natDegree ≤ 2) (hq : q.natDegree ≤ 2) :
    (Finset.univ.filter (fun r : F => p.eval r = q.eval r)).card ≤ 2 :=
  card_filter_eval_eq_le_of_degree_le hpq hp hq

/-! ================================================================
    (B) TENSOR / TRACE STRUCTURE — the algebraic skeleton of ring-switching:
    the embeddings `φ₀ : α ↦ α ⊗ 1` (columns) and `φ₁ : α ↦ 1 ⊗ α` (rows) of the
    big ring `A = L ⊗_K L`.  Mirrors `RingSwitching/Prelude.lean` φ₀/φ₁ (lines 69–86).
    Re-proven here from `Algebra.TensorProduct` to hand-verify the ring-hom laws —
    these are the identities that make the "claim over big ring ↦ small ring"
    reduction algebraically well-defined.
    ================================================================ -/

section TensorAlgebra

variable (K L : Type*) [CommRing K] [CommRing L] [Algebra K L]

/-- Column embedding `φ₀ : L → L ⊗[K] L`, `α ↦ α ⊗ 1`, as a ring homomorphism.
(`RingSwitching/Prelude.lean:69`.) -/
def φ₀ : L →+* (L ⊗[K] L) where
  toFun α := α ⊗ₜ[K] (1 : L)
  map_one' := rfl
  map_mul' α β := by simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := by simp only [TensorProduct.zero_tmul]
  map_add' α β := by simp only [TensorProduct.add_tmul]

/-- Row embedding `φ₁ : L → L ⊗[K] L`, `α ↦ 1 ⊗ α`, as a ring homomorphism.
(`RingSwitching/Prelude.lean:80`.) -/
def φ₁ : L →+* (L ⊗[K] L) where
  toFun α := (1 : L) ⊗ₜ[K] α
  map_one' := rfl
  map_mul' α β := by simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := by simp only [TensorProduct.tmul_zero]
  map_add' α β := by simp only [TensorProduct.tmul_add]

variable {K L}

/-- `φ₀ α = α ⊗ 1` (definitional unfold, used by every downstream tensor computation). -/
@[simp] theorem φ₀_apply (α : L) : φ₀ K L α = α ⊗ₜ[K] (1 : L) := rfl

/-- `φ₁ α = 1 ⊗ α`. -/
@[simp] theorem φ₁_apply (α : L) : φ₁ K L α = (1 : L) ⊗ₜ[K] α := rfl

/-- **Commuting columns and rows.** `φ₀ α · φ₁ β = α ⊗ β = φ₁ β · φ₀ α`.
This is the structural identity that lets the protocol factor a tensor `α ⊗ β` into
its row factor (`φ₁`) and column factor (`φ₀`) independently — the algebraic basis of
the row/column decomposition `ŝ = Σ_u β_u ⊗ ŝ_u`. -/
theorem φ₀_mul_φ₁ (α β : L) : (φ₀ K L α) * (φ₁ K L β) = α ⊗ₜ[K] β := by
  simp only [φ₀_apply, φ₁_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem φ₀_mul_φ₁_comm (α β : L) : (φ₀ K L α) * (φ₁ K L β) = (φ₁ K L β) * (φ₀ K L α) := by
  simp only [φ₀_apply, φ₁_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- **`φ₀` is K-linear scaling-compatible:** the column embedding respects the K-action,
so K-coefficients pass through the embedding unchanged.  (Needed when the protocol pushes
the small-field basis `β : Basis (Fin κ → Fin 2) K L` through `φ₀`.) -/
theorem φ₀_smul (c : K) (α : L) : φ₀ K L (c • α) = c • (φ₀ K L α) := by
  simp only [φ₀_apply, TensorProduct.smul_tmul']

theorem φ₁_smul (c : K) (α : L) : φ₁ K L (c • α) = c • (φ₁ K L α) := by
  simp only [φ₁_apply, TensorProduct.tmul_smul]

end TensorAlgebra

/-! ================================================================
    HONEST SCOPE STATEMENT (what is NOT provable here, and why).
    ================================================================

    The two blocks above are the *entire* extractable-math content of issue #29.
    The 5 holes are discharged by COMBINING (A) and (B) with construction-level
    transcript/extractor plumbing that has no further math:

      1-3. SumcheckPhase.lean:723/726/738 (`iteratedSumcheckKStateProp` strong check
           `h_i = h_star`; `toFun_full` at :816; the post-challenge branch at :766–792
           currently stubbed `True`).  The MATH needed is:
             - (A) above → prices the doom-escape at `2/|L|` via
               `probEvent_badSumcheckEventProp_degree_two_le` (already in-tree,
               SumcheckPhase.lean:242), AND
             - the round-transition identity `getSumcheckRoundPoly_eval_eq_cube_succ`
               (SumcheckPhase.lean:409, ALREADY PROVEN) which gives
               `h_star(r') = ∑_{next cube} (advanced H)`, matching `relOut`'s
               sumcheck-consistency `h_i(r') = ∑_{next cube} witOut.H`.
           Both math hooks EXIST.  What is missing is a DESIGN DECISION on the KState
           payload: swap `localizedRoundPolyCheck : h_i = h_star` for the provable
           `localizedTargetCheck : h_i(r') = h_star(r')`, then re-route the
           `KnowledgeStateFunction.toFun_full` proof + the matching local probability
           bound.  This is a coordinated edit across the KState `def` and the
           soundness theorem (and a migration of consumers in General/Binius/FRIBinius),
           NOT a new lemma.  => DESIGN-BLOCKED PLUMBING, not unprovable math.

      4.   SumcheckPhase.lean:224 — run-shape ("peel") of the multi-round composition.
           Pure structural induction over the round protocol spec.  No math.

      5.   BatchingPhase.lean:558/614 — DP24 §2.5 row-decomposition capstone + the
           `probEvent` root-count bridge.  The root-count bridge is the SAME (A) above;
           the row-decomposition is the SAME `Basis.baseChange` reconstruction already
           proven in Prelude/Profile.  Currently closed with `probEvent_le_one`
           (trivial bound).  Tightening it reuses (A); no new math.

    CONCLUSION: #29 has genuine extractable algebra — blocks (A) and (B) — and it is
    ALREADY landed in-tree (KStateWeaken.lean / ExtractedIssueBricks.lean / Prelude.lean
    φ₀,φ₁ / SumcheckPhase.lean:409,242).  The 5 OPEN holes are NOT blocked on missing
    math; they are blocked on a COORDINATED KSTATE DESIGN DECISION (payload swap +
    consumer migration) plus run-shape induction.  Honest verdict: design-blocked
    construction/plumbing, with all required math primitives proven.
-/

#print axioms card_filter_eval_eq_le_natDegree
#print axioms decidablePred_badPolyAgreement
#print axioms card_filter_eval_eq_le_of_degree_le
#print axioms filter_badPolyAgreement_eq
#print axioms card_filter_eval_eq_degree_two
#print axioms φ₀_apply
#print axioms φ₁_apply
#print axioms φ₀_mul_φ₁
#print axioms φ₀_mul_φ₁_comm
#print axioms φ₀_smul
#print axioms φ₁_smul

end Issue29Ring
