/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
Round 13b (issue #232): the LINEAR-CODE collapse of the ball-intersection second moment (the #82
kernel object). `∑_w |Λ(w)|² = ∑_{c,c'∈C} |B(c,r)∩B(c',r)|` (ListAroundBallIntersectionKernel)
reduces, for a *linear* (subtraction-closed) code, to a single sum over codewords:
    `∑_{c,c'∈C} |B(c,r)∩B(c',r)|  =  |C| · ∑_{e∈C} |B(0,r)∩B(e,r)|`
and the triangle inequality kills every term with `wt(e) > 2r`. So the open kernel is exactly
`|C| · ∑_{e∈C, wt(e) ≤ 2r} |B(0,r)∩B(e,r)|` = MDS weight enumerator `A_w` (w≤2r) × ball-intersection
volumes — the CS25/#82 object whose sharp bound is the research kernel.
-/

open Finset

namespace Round13bSecondMoment

variable {n : ℕ} {F : Type*} [DecidableEq F] [Fintype F] [AddCommGroup F]

/-- The Hamming ball of radius `r` around `c`. -/
def hammingBall (c : Fin n → F) (r : ℕ) : Finset (Fin n → F) :=
  Finset.univ.filter (fun w => hammingDist c w ≤ r)

@[simp] theorem mem_hammingBall {c w : Fin n → F} {r : ℕ} :
    w ∈ hammingBall c r ↔ hammingDist c w ≤ r := by
  simp [hammingBall]

/-- **Translation invariance of Hamming distance:** `Δ(x−z, y−z) = Δ(x, y)`, via
`hammingDist_comp` with the injective per-coordinate maps `a ↦ a − z i`. -/
theorem hammingDist_sub_right (x y z : Fin n → F) :
    hammingDist (x - z) (y - z) = hammingDist x y := by
  have h := hammingDist_comp (β := fun _ : Fin n => F)
    (fun (i : Fin n) (a : F) => a - z i) (x := x) (y := y)
    (fun i a b hab => by simpa using congrArg (· + z i) hab)
  simpa only [Pi.sub_apply] using h

/-- **Translation invariance of the ball intersection:** `|B(c,r) ∩ B(c',r)| = |B(0,r) ∩ B(c'−c,r)|`,
via the bijection `w ↦ w − c`. -/
theorem ball_inter_translation (c c' : Fin n → F) (r : ℕ) :
    (hammingBall c r ∩ hammingBall c' r).card
      = (hammingBall 0 r ∩ hammingBall (c' - c) r).card := by
  apply Finset.card_nbij' (fun w => w - c) (fun x => x + c)
  · intro w hw
    have h1 : hammingDist c w ≤ r := mem_hammingBall.mp (Finset.mem_inter.mp hw).1
    have h2 : hammingDist c' w ≤ r := mem_hammingBall.mp (Finset.mem_inter.mp hw).2
    refine Finset.mem_inter.mpr ⟨mem_hammingBall.mpr ?_, mem_hammingBall.mpr ?_⟩
    · have e : hammingDist (0 : Fin n → F) (w - c) = hammingDist c w := by
        have h := hammingDist_sub_right c w c; rwa [sub_self] at h
      rw [e]; exact h1
    · rw [hammingDist_sub_right c' w c]; exact h2
  · intro x hx
    have h1 : hammingDist (0 : Fin n → F) x ≤ r := mem_hammingBall.mp (Finset.mem_inter.mp hx).1
    have h2 : hammingDist (c' - c) x ≤ r := mem_hammingBall.mp (Finset.mem_inter.mp hx).2
    refine Finset.mem_inter.mpr ⟨mem_hammingBall.mpr ?_, mem_hammingBall.mpr ?_⟩
    · have e : hammingDist c (x + c) = hammingDist (0 : Fin n → F) x := by
        have h := hammingDist_sub_right c (x + c) c
        rw [sub_self, add_sub_cancel_right] at h; exact h.symm
      rw [e]; exact h1
    · have e : hammingDist c' (x + c) = hammingDist (c' - c) x := by
        have h := hammingDist_sub_right c' (x + c) c
        rw [add_sub_cancel_right] at h; exact h.symm
      rw [e]; exact h2
  · intro w _; simp
  · intro x _; simp

/-- **The linear-code collapse (headline).** For a subtraction-closed code `C` (linear),
`∑_{c∈C}∑_{c'∈C} |B(c,r)∩B(c',r)| = |C| · ∑_{e∈C} |B(0,r)∩B(e,r)|`. Translation invariance + the
reindex `c' ↦ c'−c` (a bijection of `C`, inverse `e ↦ e+c`, using `0,−c ∈ C`). -/
theorem sum_ball_inter_linear (C : Finset (Fin n → F)) (r : ℕ)
    (hsub : ∀ a ∈ C, ∀ b ∈ C, a - b ∈ C) :
    (∑ c ∈ C, ∑ c' ∈ C, (hammingBall c r ∩ hammingBall c' r).card)
      = C.card * ∑ e ∈ C, (hammingBall 0 r ∩ hammingBall e r).card := by
  classical
  have inner : ∀ c ∈ C,
      (∑ c' ∈ C, (hammingBall c r ∩ hammingBall c' r).card)
        = ∑ e ∈ C, (hammingBall 0 r ∩ hammingBall e r).card := by
    intro c hc
    rw [Finset.sum_congr rfl (fun c' _ => ball_inter_translation c c' r)]
    refine Finset.sum_nbij' (fun c' => c' - c) (fun e => e + c) ?_ ?_ ?_ ?_ ?_
    · intro c' hc'; exact hsub c' hc' c hc
    · intro e he
      have h0 : (0 : Fin n → F) ∈ C := by have := hsub c hc c hc; rwa [sub_self] at this
      have hnc : -c ∈ C := by have := hsub 0 h0 c hc; rwa [zero_sub] at this
      have : e - (-c) ∈ C := hsub e he (-c) hnc
      rwa [sub_neg_eq_add] at this
    · intro c' _; simp
    · intro e _; simp
    · intro c' _; rfl
  rw [Finset.sum_congr rfl inner, Finset.sum_const, smul_eq_mul]

/-- **Triangle cutoff:** for `wt(e) > 2r` the balls `B(0,r)` and `B(e,r)` are disjoint, so
`B(0,r) ∩ B(e,r) = ∅`. Hence only codewords of weight `≤ 2r` contribute to the second moment. -/
theorem ball_inter_empty_of_wt_gt (e : Fin n → F) (r : ℕ)
    (h : 2 * r < hammingNorm e) :
    hammingBall 0 r ∩ hammingBall e r = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  simp only [Finset.mem_inter, mem_hammingBall] at hx
  obtain ⟨h1, h2⟩ := hx
  -- wt e = Δ(e,0) ≤ Δ(e,x) + Δ(x,0) ≤ r + r = 2r, contradicting 2r < wt e.
  have htri : hammingDist e 0 ≤ hammingDist e x + hammingDist x 0 := hammingDist_triangle e x 0
  have he0 : hammingDist e (0 : Fin n → F) = hammingNorm e := hammingDist_zero_right e
  have hx0 : hammingDist x (0 : Fin n → F) ≤ r := by rwa [hammingDist_comm] at h1
  rw [he0] at htri
  omega

/-- **The reduced kernel (corollary).** The ball-intersection second moment of a linear code is
`|C| · ∑_{e∈C} |B(0,r)∩B(e,r)|`, and every `e` with `wt(e) > 2r` contributes `0`. So the open
research kernel is the sharp bound on `∑_{e∈C, wt(e)≤2r} |B(0,r)∩B(e,r)|` (= MDS weight enumerator
weighted by ball-intersection volumes). We record the contribution-zero fact in card form. -/
theorem ball_inter_card_zero_of_wt_gt (e : Fin n → F) (r : ℕ)
    (h : 2 * r < hammingNorm e) :
    (hammingBall 0 r ∩ hammingBall e r).card = 0 := by
  rw [ball_inter_empty_of_wt_gt e r h, Finset.card_empty]

end Round13bSecondMoment

#print axioms Round13bSecondMoment.sum_ball_inter_linear
#print axioms Round13bSecondMoment.ball_inter_translation
#print axioms Round13bSecondMoment.ball_inter_empty_of_wt_gt
#print axioms Round13bSecondMoment.ball_inter_card_zero_of_wt_gt
