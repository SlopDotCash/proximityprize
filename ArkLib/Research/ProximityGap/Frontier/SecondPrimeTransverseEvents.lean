/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterSuccessorSplitCriterion

/-! # Fresh scalar directions from a transverse fourth polynomial head -/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeTransverseEvents

open Finset Polynomial Code _root_.ProximityGap SmoothFourHeadColored
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [Field F] [Finite F]

omit [Finite F] in
private theorem dynamic_hit (x a c p t : F) (hp : p ≠ 0) (hc : c ≠ t / p) :
    c * p ≠ t ∧ x * (c * p) + a * p + (-x - a / (c - t / p)) * (c * p) =
      x * t + (-x - a / (c - t / p)) * t := by
  have h : c * p ≠ t := fun h => hc ((eq_div_iff hp).mpr h)
  refine ⟨h,?_⟩
  have aux : a / (c - t / p) * (c * p - t) = a * p := by
    rw [show c * p - t = (c - t / p) * p by rw [sub_mul, div_mul_cancel₀ _ hp]]
    rw [← mul_assoc, div_mul_cancel₀ _ (sub_ne_zero.mpr hc)]
  linear_combination - aux

private theorem fresh (D : I ↪ F) (k : ℕ) (δ : ℝ≥0) (u : WordStack F (Fin 2) I)
    (z : F) (S : Finset I) (x : I) (A B : F[X])
    (dA : A.natDegree < k) (dB : B.natDegree < k)
    (rank : k ≤ S.card)
    (support : (1 - δ) * (Fintype.card I : ℝ≥0) ≤ ((S.card + 1 : ℕ) : ℝ≥0))
    (core : ∀ i ∈ S, A.eval (D i) = u 0 i ∧ B.eval (D i) = u 1 i)
    (mismatch : B.eval (D x) ≠ u 1 x) (hit : A.eval (D x) + z * B.eval (D x) = u 0 x + z * u 1 x) :
    mcaEvent (ReedSolomon.code D k : Set (I → F)) δ (u 0) (u 1) z := by
  classical
  let _ := Fintype.ofFinite F
  have ha := degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr dA)
  have hb := degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr dB)
  apply HalfPredecessorCoreFreshDecode.mcaEvent_of_affine_core_fresh D k δ u z S x A B
    (fun h => mismatch (core _ h).2) ha hb _ rank support core _
    (fun h => mismatch (congrArg Prod.snd h))
  · apply (degree_add_le _ _).trans_lt (max_lt ha _)
    by_cases hz : z=0
    · simp [hz]
    · rwa [degree_C_mul hz]
  · simpa only [eval_add, eval_mul, eval_C] using hit

open Classical in
/-- All three kinds of selected slots give bad events for the same received pair. On
the zero fiber of the second pencil head the fourth head also vanishes. Elsewhere
its nonconstant affine label has a different slope from the fixed pencil label. -/
theorem events (D : I ↪ F) (k : ℕ) (δ : ℝ≥0) (col : I → Fin 8) (f : Fin 3 → F[X])
    (a c : F) (deg : ∀ j, 1 + (f j).natDegree < k) (zero : f 0 = 0)
    (fiber : ∀ x, col x = 2 ↔ (f 1).eval (D x) = 0)
    (agree : ∀ x j, col x ∈ coreClasses j → (f j).eval (D x) = (f (owner (col x))).eval (D x))
    (misses : ∀ x, col x ∈ ordinaryClasses →
      (f (miss (col x))).eval (D x) ≠ (f (owner (col x))).eval (D x))
    (avoid : ∀ j x, c ≠ (f j).eval (D x) / (f 1).eval (D x))
    (rank : ∀ j, k ≤ (univ.filter fun x => col x ∈ coreClasses j).card)
    (support : ∀ j, (1 - δ) * (Fintype.card I : ℝ≥0) ≤
      (((univ.filter fun x => col x ∈ coreClasses j).card + 1 : ℕ) : ℝ≥0))
    (rank₄ : k ≤ (univ.filter fun x => col x = 2 ∨ col x = 7).card)
    (support₄ : (1 - δ) * (Fintype.card I : ℝ≥0) ≤
      (((univ.filter fun x => col x = 2 ∨ col x = 7).card + 1 : ℕ) : ℝ≥0)) :
    ∃ u : WordStack F (Fin 2) I,
      let bad := mcaEvent (ReedSolomon.code D k : Set (I → F)) δ (u 0) (u 1)
      (∀ x, col x ∈ ordinaryClasses → bad (-D x)) ∧
      (∀ x, col x ∈ ordinaryClasses → col x ≠ 2 →
        bad (-D x - a / (c - (f (owner (col x))).eval (D x) / (f 1).eval (D x)))) ∧
      ∀ x, col x = 7 → ∀ j, bad (-D x - a / (c - (f j).eval (D x) / (f 1).eval (D x))) := by
  classical
  let P := f 1
  let val (j : Fin 3) (x : I) := (f j).eval (D x)
  let base (x : I) := val (owner (col x)) x
  let B := C c * P
  let A : F[X] := Polynomial.X * B + C a * P
  let u : WordStack F (Fin 2) I := ![fun x => if col x = 7 then (A.eval (D x)) else D x * base x,
    fun x => if col x = 7 then (B.eval (D x)) else base x]
  have dB : B.natDegree ≤ P.natDegree := natDegree_C_mul_le c P
  have dXA (g : F[X]) : (Polynomial.X * g).natDegree ≤ 1 + g.natDegree :=
    (natDegree_mul_le).trans (by rw [natDegree_X])
  have degP₁ : 1 + P.natDegree < k := deg 1
  have dA : A.natDegree < k := (natDegree_add_le ..).trans_lt (max_lt
    ((dXA B).trans_lt (by omega))
    ((natDegree_C_mul_le a P).trans_lt (by omega)))
  have degP : P.natDegree < k := by omega
  have ordinary (x : I) (hx : col x ∈ ordinaryClasses) : col x ≠ 7 := by
    intro eq
    exact (by decide : (7 : Fin 8) ∉ ordinaryClasses) (eq ▸ hx)
  have received (x : I) (hx : col x ≠ 7) : u 0 x = D x * base x ∧ u 1 x = base x := by
    simp [u, hx]
  have hole (x : I) (hx : col x = 7) : u 0 x = A.eval (D x) ∧ u 1 x = B.eval (D x) := by
    simp [u, hx]
  have values (x : I) :
      A.eval (D x) = D x * (c * P.eval (D x)) + a * P.eval (D x) ∧
      B.eval (D x) = c * P.eval (D x) := by
    simp [A,B]
  have pencil (j : Fin 3) (x : I) (z : F) (hm : val j x ≠ u 1 x)
      (hit : D x * val j x + z * val j x = u 0 x + z * u 1 x) :
      mcaEvent (ReedSolomon.code D k : Set (I → F)) δ (u 0) (u 1) z := by
    refine fresh D k δ u z _ x (Polynomial.X * f j) (f j) ((dXA _).trans_lt (deg j))
      (by have := deg j; omega) (rank j) (support j) ?_ hm ?_
    · intro y hy
      have hc := (mem_filter.mp hy).2
      have h7 : col y ≠ 7 := fun he =>
        (by decide : ∀ j : Fin 3, (7 : Fin 8) ∉ coreClasses j) j (he ▸ hc)
      rw [(received y h7).1, (received y h7).2, eval_mul, eval_X, agree y j hc]
      exact ⟨rfl,rfl⟩
    · simpa only [eval_mul, eval_X] using hit
  refine ⟨u, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨ha,hb⟩ := received x (ordinary x hx)
    apply pencil (miss (col x)) x _ (hb ▸ misses x hx)
    rw [ha,hb]
    ring
  · intro x hx h₂
    let p := P.eval (D x)
    let z := -D x - a / (c - base x / p)
    have hp : p ≠ 0 := fun h => h₂ ((fiber x).mpr h)
    have dyn := dynamic_hit (D x) a c p (base x) hp (avoid _ x)
    obtain ⟨ha,hb⟩ := received x (ordinary x hx)
    refine fresh D k δ u z _ x A B dA (dB.trans_lt degP) rank₄ support₄ ?_ ?_ ?_
    · intro y hy
      rcases (mem_filter.mp hy).2 with h | h
      · have recv :=  received y (by rw [h]; decide)
        have p0 := (fiber y).mp h
        have b0 : base y = 0 := by
          change (f (owner (col y))).eval (D y) = 0
          rw [h, show owner 2 = 0 by decide, zero, eval_zero]
        rw [(values y).1, (values y).2, recv.1, recv.2, b0]
        change _ * (_ * (f 1).eval _) + _ * (f 1).eval _ = _ ∧ _ = _
        simp [P, p0]
      · exact ⟨(hole y h).1.symm,(hole y h).2.symm⟩
    · rw [(values x).2, hb]
      exact dyn.1
    · rw [(values x).1, (values x).2, ha, hb]
      exact dyn.2
  · intro x hx j
    let p := P.eval (D x)
    have hp : p ≠ 0 := fun h => (by decide : (7 : Fin 8) ≠ 2) (hx.symm.trans ((fiber x).mpr h))
    have dyn := dynamic_hit (D x) a c p (val j x) hp (avoid j x)
    obtain ⟨ha,hb⟩ := hole x hx
    apply pencil j x _ _ _
    · rw [hb, (values x).2]
      exact dyn.1.symm
    · rw [ha,hb,(values x).1,(values x).2]
      exact dyn.2.symm

end ArkLib.ProximityGap.Frontier.SecondPrimeTransverseEvents
