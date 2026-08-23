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

This is the **per-codeword half of the LD⟺MCA bridge**: summing over the `L` codewords within the
ball gives `#{bad γ} ≤ ⌊n/w⌋ · L`, i.e. the far-line incidence is controlled by the list size `L`
(in the window `w ~ n/2`, `⌊n/w⌋ ≤ 2`, so incidence `≤ 2L`). It makes precise that the MCA
threshold and the list-decoding radius coincide up to the factor `⌊n/w⌋` — the two grand
challenges are the same `δ*`. (The remaining open content is the list size `L` itself for explicit
smooth RS beyond Johnson; this lemma does not bound `L`.)

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
/-- **The quantified LD⟺MCA bridge.** The far-line incidence — the number of scalars `γ` for which
`u + γ·v` agrees on `≥ w` coordinates with *some* codeword in `C` — is at most `⌊n/w⌋` times the
number of codewords of `C` that lie within `w`-agreement of the line. In the window `w ~ n/2`,
`⌊n/w⌋ ≤ 2`, so the incidence is `≤ 2·L` where `L` is the line's close-codeword list size: the MCA
threshold and the list-decoding radius coincide up to the factor `⌊n/w⌋`. -/
theorem line_list_incidence_le (u v : Fin n → F) (hv : ∀ i, v i ≠ 0) {w : ℕ} (hw : 0 < w)
    (C : Finset (Fin n → F)) :
    (univ.filter (fun γ : F =>
        ∃ c ∈ C, w ≤ (univ.filter (fun i : Fin n => u i + γ * v i = c i)).card)).card
      ≤ (C.filter (fun c => ∃ γ : F,
          w ≤ (univ.filter (fun i : Fin n => u i + γ * v i = c i)).card)).card * (n / w) := by
  set close := C.filter (fun c => ∃ γ : F,
      w ≤ (univ.filter (fun i : Fin n => u i + γ * v i = c i)).card) with hclose
  have hsub : (univ.filter (fun γ : F =>
        ∃ c ∈ C, w ≤ (univ.filter (fun i : Fin n => u i + γ * v i = c i)).card))
      ⊆ close.biUnion (fun c => univ.filter (fun γ : F =>
          w ≤ (univ.filter (fun i : Fin n => u i + γ * v i = c i)).card)) := by
    intro γ hγ
    rw [mem_filter] at hγ; obtain ⟨_, c, hcC, hcw⟩ := hγ
    rw [mem_biUnion]
    exact ⟨c, by rw [hclose, mem_filter]; exact ⟨hcC, γ, hcw⟩,
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
