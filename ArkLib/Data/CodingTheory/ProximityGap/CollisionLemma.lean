/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.Submodule.Basic

/-!
# The collision lemma for the proximity-gap line (#232)

Verified, axiom-clean (`[propext, Classical.choice, Quot.sound]`). Elementary Hamming-agreement
inclusion–exclusion, same technique as `ListDecodingThreshold`.

## Statement

Combined with `MCAGammaReduction` (`#bad-γ ≤ (line list)·1/(1-δ)`), this is the hinge of the
BCIKS20-style dichotomy for the line `{u₀ + γ·u₁}`. If two codewords `P, P'` are `δ`-close to the line
at **distinct** scalars `γ ≠ γ'`, then the codeword `(P-P')/(γ-γ')` agrees with the *direction* `u₁`
on `≥ (1-2δ)n` coordinates — i.e. `Δ(u₁, C) ≤ 2δ`. Contrapositive: if the direction `u₁` is `> 2δ`-far
from the code, then *all* line-list codewords share a single scalar, collapsing the line list to a
single per-word list.

Proof: on the `≥ (1-2δ)n` coordinates where both `P = u₀+γu₁` and `P' = u₀+γ'u₁`, subtracting gives
`P - P' = (γ-γ')·u₁`, so `(γ-γ')⁻¹·(P-P') = u₁` there; inclusion–exclusion bounds the disagreement.
-/

namespace ArkLib.CodingTheory.Collision

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-- **Collision lemma.** If `P` is `r`-close to `u₀+γ·u₁` and `P'` is
`r`-close to `u₀+γ'·u₁` with `γ ≠ γ'`, then the scaled difference `(γ-γ')⁻¹·(P-P')` is `2r`-close to
the direction `u₁`. Hence two distinct line-list codewords at different scalars pin `u₁` near the
code. -/
theorem collision (P P' u₀ u₁ : ι → F) {γ γ' : F} (hγ : γ ≠ γ') (r : ℕ)
    (hP : hammingDist P (u₀ + γ • u₁) ≤ r) (hP' : hammingDist P' (u₀ + γ' • u₁) ≤ r) :
    hammingDist ((γ - γ')⁻¹ • (P - P')) u₁ ≤ 2 * r := by
  have hd : γ - γ' ≠ 0 := sub_ne_zero.mpr hγ
  -- the disagreement coordinates of `(γ-γ')⁻¹·(P-P')` vs `u₁` lie in the union of the two
  -- per-codeword disagreement sets
  have hsub : (Finset.univ.filter (fun i => ((γ - γ')⁻¹ • (P - P')) i ≠ u₁ i))
      ⊆ (Finset.univ.filter (fun i => P i ≠ (u₀ + γ • u₁) i))
        ∪ (Finset.univ.filter (fun i => P' i ≠ (u₀ + γ' • u₁) i)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hcon
    simp only [not_or, ne_eq, not_not] at hcon
    obtain ⟨h1, h2⟩ := hcon
    apply hi
    have e1 : P i = u₀ i + γ * u₁ i := by
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h1
    have e2 : P' i = u₀ i + γ' * u₁ i := by
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h2
    show ((γ - γ')⁻¹ • (P - P')) i = u₁ i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, e1, e2]
    rw [show (u₀ i + γ * u₁ i) - (u₀ i + γ' * u₁ i) = (γ - γ') * u₁ i by ring,
      ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  calc hammingDist ((γ - γ')⁻¹ • (P - P')) u₁
      = (Finset.univ.filter (fun i => ((γ - γ')⁻¹ • (P - P')) i ≠ u₁ i)).card := rfl
    _ ≤ ((Finset.univ.filter (fun i => P i ≠ (u₀ + γ • u₁) i))
          ∪ (Finset.univ.filter (fun i => P' i ≠ (u₀ + γ' • u₁) i))).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter (fun i => P i ≠ (u₀ + γ • u₁) i)).card
          + (Finset.univ.filter (fun i => P' i ≠ (u₀ + γ' • u₁) i)).card := Finset.card_union_le _ _
    _ ≤ r + r := Nat.add_le_add hP hP'
    _ = 2 * r := by ring

/-- **Dichotomy corollary: a far direction forces a single scalar.** If every codeword is `> 2r`-far
from the direction `u₁` (i.e. `Δ(u₁, C) > 2δ`), then any two codewords of `C` that are `r`-close to the
line `{u₀+γ·u₁}` must be close at the **same** scalar `γ`. Contrapositive of `collision`: distinct
scalars would put `(γ-γ')⁻¹·(P-P') ∈ C` within `2r` of `u₁`. Hence the line list collapses to a single
per-word list `Λ(C, u₀+γu₁, δ)` — the far branch of the BCIKS20 dichotomy for #232. -/
theorem same_scalar_of_far (C : Submodule F (ι → F)) (P P' u₀ u₁ : ι → F)
    (hP_C : P ∈ C) (hP'_C : P' ∈ C) {γ γ' : F} (r : ℕ)
    (hfar : ∀ c ∈ C, 2 * r < hammingDist u₁ c)
    (hP : hammingDist P (u₀ + γ • u₁) ≤ r) (hP' : hammingDist P' (u₀ + γ' • u₁) ≤ r) :
    γ = γ' := by
  by_contra hne
  have hmem : (γ - γ')⁻¹ • (P - P') ∈ C := C.smul_mem _ (C.sub_mem hP_C hP'_C)
  have hco := collision P P' u₀ u₁ hne r hP hP'
  have hf := hfar _ hmem
  rw [hammingDist_comm] at hf
  omega


/-- Translation: `d(a - x, b) = d(a, b + x)` (relabel the disagreement coordinates). -/
theorem hammingDist_sub_left (a x b : ι → F) :
    hammingDist (a - x) b = hammingDist a (b + x) := by
  unfold hammingDist
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, Pi.add_apply, ne_eq,
    sub_eq_iff_eq_add]

/-- Translation invariance: `d(u + a, u + b) = d(a, b)`. -/
theorem hammingDist_add_left_cancel (u a b : ι → F) :
    hammingDist (u + a) (u + b) = hammingDist a b := by
  unfold hammingDist
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, ne_eq, add_right_inj]

/-- **Near-direction branch.** If the direction `u₁` is within `2r` of a codeword `c₁ ∈ C`, then any
codeword `P` that is `r`-close to the line `{u₀+γ·u₁}` has its shift `P - γ·c₁` within `3r` of `u₀`.
So in the near branch every line-list codeword, shifted by `γ·c₁`, lands in the single per-word list
`Λ(C, u₀, 3δ)` — the structured branch of the BCIKS20 dichotomy for #232. -/
theorem near_case (P u₀ u₁ c₁ : ι → F) {γ : F} (r : ℕ)
    (hnear : hammingDist u₁ c₁ ≤ 2 * r)
    (hP : hammingDist P (u₀ + γ • u₁) ≤ r) :
    hammingDist (P - γ • c₁) u₀ ≤ 3 * r := by
  have hdir : hammingDist (u₀ + γ • u₁) (u₀ + γ • c₁) ≤ 2 * r := by
    rw [hammingDist_add_left_cancel]
    refine le_trans ?_ hnear
    unfold hammingDist
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.smul_apply, smul_eq_mul,
      ne_eq] at hi ⊢
    intro he
    exact hi (by rw [he])
  calc hammingDist (P - γ • c₁) u₀
      = hammingDist P (u₀ + γ • c₁) := hammingDist_sub_left P (γ • c₁) u₀
    _ ≤ hammingDist P (u₀ + γ • u₁) + hammingDist (u₀ + γ • u₁) (u₀ + γ • c₁) :=
        hammingDist_triangle _ _ _
    _ ≤ r + 2 * r := Nat.add_le_add hP hdir
    _ = 3 * r := by ring

end ArkLib.CodingTheory.Collision
#print axioms ArkLib.CodingTheory.Collision.collision
#print axioms ArkLib.CodingTheory.Collision.same_scalar_of_far
#print axioms ArkLib.CodingTheory.Collision.near_case
