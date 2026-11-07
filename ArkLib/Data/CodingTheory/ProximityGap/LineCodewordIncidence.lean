/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Per-codeword line–ball incidence on a smooth domain (#389)

A clean structural brick for the far-line incidence law `δ* = sup{δ : max-far-line-incidence ≤
q·ε*}`. On a **smooth** evaluation domain the far direction `v` (e.g. the evaluation of a monomial
`X^a` on `μ_n`) is **nowhere zero**. For such a direction, the number of scalars `γ` whose line
point `u + γ·v` agrees with a *fixed* target word `c` on at least `w` coordinates is `≤ ⌊n/w⌋`.

The proof is a one-line fiber count: `u_i + γ·v_i = c_i ⟺ γ = (c_i − u_i)/v_i =: f i`, so the
agreement set of `γ` is exactly the fiber `f⁻¹(γ)`; the fibers partition `Fin n`, so the `γ` with
`≥ w` agreements number at most `n/w`.

Summing over codewords gives `line_list_incidence_le`: the number of scalars `γ` for which
`u + γ·v` is `w`-close to *some* codeword is at most `⌊n/w⌋` times the size of the
**line-union list** `lineUnionList u v w C` — the codewords of `C` that are `w`-close to *some*
point of the whole line.

**This is not a list-decoding/MCA equivalence.**  The line-union list is not the list around a
single received word, and an ordinary (point-centred) list-decoding bound does not bound it.
Example: the constant code on `3` coordinates over `F₇`, `w = 2`, `u = (0,0,1)`, `v = (1,2,3)`.
Any point-centred list has at most one constant codeword (two `2`-subsets of `3` coordinates
meet, forcing the constants to agree), and `v` agrees with a constant on at most one
coordinate, so `v` is a far direction.  Yet `γ = 0, 3, 6` make `u + γ·v` agree with the
constants `0, 3, 5` on two coordinates, so the line-union list has `3` members and the bound
proved here reads `3 ≤ 3 · ⌊3/2⌋ = 3`.  Substituting the point-centred bound `1` for the
union list would give the false `3 ≤ 1`.  Turning a point-centred list bound into a bound on
the line-union list (and accounting for the MCA no-joint-agreement clause, which this count
ignores) is a separate reduction that is not proved here, so this file does not show that the
MCA threshold and the list-decoding radius coincide.  It also does not bound any list size.

Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Finset

namespace ProximityGap.LineCodewordIncidence

variable {n : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Per-codeword line–ball incidence (multiplicative form).** For a line `{u + γ·v}` with `v`
nowhere zero and any word `c`, the number of scalars `γ` whose line point agrees with `c` on `≥ w`
coordinates, times `w`, is `≤ n`. Fibers of `i ↦ (c_i − u_i)/v_i` partition `Fin n`. -/
theorem line_codeword_incidence_mul_le
    (u v c : Fin n → F) (hv : ∀ i, v i ≠ 0) (w : ℕ) :
    (univ.filter (fun γ : F =>
        w ≤ (univ.filter (fun i : Fin n => u i + γ * v i = c i)).card)).card * w ≤ n := by
  classical
  set f : Fin n → F := fun i => (c i - u i) / v i with hf
  have hfib : ∀ γ : F, (univ.filter (fun i : Fin n => u i + γ * v i = c i))
      = univ.filter (fun i : Fin n => f i = γ) := by
    intro γ; apply filter_congr; intro i _
    rw [hf, div_eq_iff (hv i)]
    constructor <;> intro h <;> linear_combination -h
  simp only [hfib]
  have htot : ∑ γ : F, (univ.filter (fun i : Fin n => f i = γ)).card = n := by
    rw [← card_eq_sum_card_fiberwise (fun i _ => mem_univ (f i)), card_univ, Fintype.card_fin]
  calc (univ.filter (fun γ : F =>
          w ≤ (univ.filter (fun i : Fin n => f i = γ)).card)).card * w
      = ∑ _γ ∈ univ.filter (fun γ : F => w ≤ (univ.filter (fun i : Fin n => f i = γ)).card), w := by
        rw [sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ univ.filter (fun γ : F => w ≤ (univ.filter (fun i : Fin n => f i = γ)).card),
          (univ.filter (fun i : Fin n => f i = γ)).card := by
        apply sum_le_sum; intro γ hγ; rw [mem_filter] at hγ; exact hγ.2
    _ ≤ ∑ γ : F, (univ.filter (fun i : Fin n => f i = γ)).card :=
        sum_le_sum_of_subset (filter_subset _ _)
    _ = n := htot

/-- **Per-codeword line–ball incidence (`⌊n/w⌋` form).** The number of scalars `γ` whose line
point `u + γ·v` (`v` nowhere zero) agrees with a fixed word `c` on `≥ w` coordinates is `≤ ⌊n/w⌋`.
-/
theorem line_codeword_incidence_le
    (u v c : Fin n → F) (hv : ∀ i, v i ≠ 0) {w : ℕ} (hw : 0 < w) :
    (univ.filter (fun γ : F =>
        w ≤ (univ.filter (fun i : Fin n => u i + γ * v i = c i)).card)).card ≤ n / w :=
  Nat.le_div_iff_mul_le hw |>.mpr (line_codeword_incidence_mul_le u v c hv w)

open Classical in
/-- The **line-union list**: the codewords of `C` that agree on `≥ w` coordinates with *some*
point `u + γ·v` of the line.  This is a union over all line points, not the list around one
received word. -/
noncomputable def lineUnionList (u v : Fin n → F) (w : ℕ) (C : Finset (Fin n → F)) :
    Finset (Fin n → F) :=
  C.filter (fun c => ∃ γ : F, w ≤ (univ.filter (fun i : Fin n => u i + γ * v i = c i)).card)

open Classical in
/-- **Line incidence versus the line-union list.** The number of scalars `γ` for which
`u + γ·v` agrees on `≥ w` coordinates with *some* codeword in `C` is at most `⌊n/w⌋` times the
size of the line-union list `lineUnionList u v w C`.  In the window `w ~ n/2`, `⌊n/w⌋ ≤ 2`.
The right-hand side is a line-union count, not a point-centred list size; bounding it by an
ordinary list-decoding bound needs a separate reduction (see the module docstring). -/
theorem line_list_incidence_le (u v : Fin n → F) (hv : ∀ i, v i ≠ 0) {w : ℕ} (hw : 0 < w)
    (C : Finset (Fin n → F)) :
    (univ.filter (fun γ : F =>
        ∃ c ∈ C, w ≤ (univ.filter (fun i : Fin n => u i + γ * v i = c i)).card)).card
      ≤ (lineUnionList u v w C).card * (n / w) := by
  set close := lineUnionList u v w C with hclose
  have hsub : (univ.filter (fun γ : F =>
        ∃ c ∈ C, w ≤ (univ.filter (fun i : Fin n => u i + γ * v i = c i)).card))
      ⊆ close.biUnion (fun c => univ.filter (fun γ : F =>
          w ≤ (univ.filter (fun i : Fin n => u i + γ * v i = c i)).card)) := by
    intro γ hγ
    rw [mem_filter] at hγ; obtain ⟨_, c, hcC, hcw⟩ := hγ
    rw [mem_biUnion]
    exact ⟨c, by rw [hclose, lineUnionList, mem_filter]; exact ⟨hcC, γ, hcw⟩,
      by rw [mem_filter]; exact ⟨mem_univ _, hcw⟩⟩
  calc (univ.filter (fun γ : F =>
          ∃ c ∈ C, w ≤ (univ.filter (fun i : Fin n => u i + γ * v i = c i)).card)).card
      ≤ (close.biUnion (fun c => univ.filter (fun γ : F =>
          w ≤ (univ.filter (fun i : Fin n => u i + γ * v i = c i)).card))).card := card_le_card hsub
    _ ≤ ∑ c ∈ close, (univ.filter (fun γ : F =>
          w ≤ (univ.filter (fun i : Fin n => u i + γ * v i = c i)).card)).card := card_biUnion_le
    _ ≤ ∑ _c ∈ close, n / w := by
        apply sum_le_sum; intro c _; exact line_codeword_incidence_le u v c hv hw
    _ = close.card * (n / w) := by rw [sum_const, smul_eq_mul]

end ProximityGap.LineCodewordIncidence

/-! ## Axiom audit -/
#print axioms ProximityGap.LineCodewordIncidence.line_codeword_incidence_mul_le
#print axioms ProximityGap.LineCodewordIncidence.line_codeword_incidence_le
#print axioms ProximityGap.LineCodewordIncidence.line_list_incidence_le
