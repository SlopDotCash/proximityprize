/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineSecondMomentSharp

/-!
# Issue #232: the linear-code collapse of the per-line close-pair count (round 14g)

The per-line second moment (round 14e) is charged to `|closePairs|`, the ordered codeword pairs at
Hamming distance `≤ 2(n−a)`. For a **linear** (subtraction-closed) code this count collapses, by
translation invariance, to a multiple of the **weight enumerator slice**:
    `|closePairs C a|  =  |C| · #{e ∈ C : e ≠ 0 ∧ wt(e) ≤ 2(n−a)}`.
The bijection is `(c, c') ↦ (c, c' − c)`: the second component is a nonzero codeword (`c' − c ∈ C`
by linearity, `≠ 0` since `c ≠ c'`) whose weight `wt(c' − c) = Δ(c, c')` is exactly the pair
distance. So the off-diagonal of the per-line second moment is `|C|` times the count of nonzero
codewords of weight `≤ 2(n−a)` — precisely the `w ≤ 2(n−a)` slice of the code's weight enumerator
`∑_w A_w`, and for an MDS/RS code (`A_w = 0` for `0 < w < d = n−k+1`) this is the explicit
RS object the prize's interior regime turns on.

This is the per-line companion of the O29 ball-intersection linear collapse
(`BallIntersectionSecondMomentLinear`), and the bridge from the abstract per-line chain (rounds
14–14f) to genuine Reed–Solomon structure: above the unique-decoding radius the slice is empty
(round 14f); the open interior `(1−√ρ, 1−ρ)` is exactly where the slice becomes nonzero and the
RS weight enumerator must be bounded.

Axiom-clean: `propext, Classical.choice, Quot.sound`.
-/

open Finset

namespace LinePairCooccurrence

variable {n : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Support is translation-invariant:** `supp c c' = supp (c' − c) 0` (a coordinate where `c, c'`
differ is exactly one where `c' − c` is nonzero). -/
theorem supp_eq_supp_sub (c c' : Fin n → F) : supp c c' = supp (c' - c) 0 := by
  ext i
  simp only [mem_supp, Pi.sub_apply, Pi.zero_apply, sub_ne_zero]
  exact ne_comm

/-- The **weight-enumerator slice**: nonzero codewords of weight `≤ r` (`wt(e) = |supp e 0|`). -/
def weightSlice (C : Finset (Fin n → F)) (r : ℕ) : Finset (Fin n → F) :=
  C.filter (fun e => e ≠ 0 ∧ (supp e 0).card ≤ r)

@[simp] theorem mem_weightSlice {C : Finset (Fin n → F)} {r : ℕ} {e : Fin n → F} :
    e ∈ weightSlice C r ↔ e ∈ C ∧ e ≠ 0 ∧ (supp e 0).card ≤ r := by
  simp [weightSlice]

/-- **The linear-code collapse of the per-line close-pair count.** For a subtraction-closed code,
`|closePairs C a| = |C| · |weightSlice C (2(n−a))|` — the off-diagonal is `|C|` copies of the
`w ≤ 2(n−a)` weight-enumerator slice. Proven by the translation bijection `(c, c') ↦ (c, c' − c)`. -/
theorem closePairs_card_linear (C : Finset (Fin n → F)) (a : ℕ)
    (hC : ∀ c ∈ C, ∀ c' ∈ C, c' - c ∈ C) :
    (closePairs C a).card = C.card * (weightSlice C (2 * (n - a))).card := by
  classical
  -- `0 ∈ C` (if `C` is empty both sides are `0`), used to build negatives.
  have hzero : C.Nonempty → (0 : Fin n → F) ∈ C := by
    rintro ⟨c, hc⟩; simpa using hC c hc c hc
  rw [← Finset.card_product]
  apply Finset.card_nbij' (fun p => (p.1, p.2 - p.1)) (fun p => (p.1, p.2 + p.1))
  · -- forward maps into `C ×ˢ weightSlice`
    rintro ⟨c, c'⟩ hp
    simp only [Finset.coe_filter, closePairs, Set.mem_setOf_eq, Finset.mem_offDiag] at hp
    obtain ⟨⟨hc, hc', hne⟩, hclose⟩ := hp
    refine Finset.mem_product.mpr ⟨hc, mem_weightSlice.mpr ⟨hC c hc c' hc', ?_, ?_⟩⟩
    · exact sub_ne_zero.mpr (Ne.symm hne)
    · rw [← supp_eq_supp_sub]; exact hclose
  · -- backward maps into `closePairs`
    rintro ⟨c, e⟩ hp
    rw [Finset.mem_coe, Finset.mem_product] at hp
    obtain ⟨hc, he⟩ := hp
    rw [mem_weightSlice] at he
    obtain ⟨heC, hene, hew⟩ := he
    have h0 : (0 : Fin n → F) ∈ C := hzero ⟨c, hc⟩
    have hnegc : (-c : Fin n → F) ∈ C := by simpa using hC c hc 0 h0
    have hsum : e + c ∈ C := by
      have := hC (-c) hnegc e heC; simpa [sub_neg_eq_add] using this
    simp only [Finset.mem_coe, closePairs, Finset.mem_filter, Finset.mem_offDiag]
    refine ⟨⟨hc, hsum, ?_⟩, ?_⟩
    · intro h
      exact hene (add_right_cancel (b := c) (by rw [zero_add]; exact h.symm))
    · rw [supp_eq_supp_sub c (e + c)]
      have hee : (e + c) - c = e := by abel
      rw [hee]; exact hew
  · -- left inverse
    rintro ⟨c, c'⟩ _
    have h : c' - c + c = c' := by abel
    simp only [h]
  · -- right inverse
    rintro ⟨c, e⟩ _
    have h : e + c - c = e := by abel
    simp only [h]

/-- **The weight-enumerator form of the sharp per-line second moment.** For a linear code, the
off-diagonal term of `line_second_moment_bound_sharp` is `|C| · |weightSlice C (2(n−a))| · 2(n−d)`
— the per-line second moment is controlled by `|C|` and the `w ≤ 2(n−a)` weight slice alone. -/
theorem line_second_moment_bound_weightSlice (C : Finset (Fin n → F)) (f g : Fin n → F) (a d : ℕ)
    (hg : ∀ i, g i ≠ 0) (hn : n < 2 * a)
    (hd : ∀ p ∈ C.offDiag, d ≤ (supp p.1 p.2).card)
    (hC : ∀ c ∈ C, ∀ c' ∈ C, c' - c ∈ C) :
    (∑ γ : F, (lineList C f g a γ).card ^ 2) * (2 * a - d)
      ≤ (∑ γ : F, (lineList C f g a γ).card) * (2 * a - d)
        + C.card * (weightSlice C (2 * (n - a))).card * (2 * (n - d)) := by
  have h := line_second_moment_bound_sharp C f g a d hg hn hd
  rwa [closePairs_card_linear C a hC] at h

end LinePairCooccurrence
