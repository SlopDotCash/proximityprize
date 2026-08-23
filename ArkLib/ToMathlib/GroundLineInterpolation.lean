/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Ground-line interpolation (BCIKS20 Claim 5.9, interpolation step)

Pure-Mathlib lemma file. Let `F` be a field and `A` a commutative domain that is an
`F`-algebra, with a distinguished element `ζ : A`. The *ground line* (through `1` and `ζ`)
is the set `{algebraMap F A u + ζ * algebraMap F A v | u v : F} ⊆ A`.

**Main result** (`groundLine_of_eval_groundLine`): a polynomial `γ : A[X]` of `natDegree ≤ k`
whose evaluations at `k + 1` distinct *base-field* points (the image under `algebraMap F A` of
a finset `s : Finset F` with `s.card = k + 1`) all lie on the ground line is itself of
ground-line form: `γ = v₀.map (algebraMap F A) + C ζ * v₁.map (algebraMap F A)` for some
`v₀ v₁ : F[X]` of `natDegree ≤ k`.

Proof: Lagrange-interpolate the prescribed ground-line coordinates `u₀ u₁ : F → F` over `s`
(`Lagrange.interpolate`, degree `< s.card` by `Lagrange.degree_interpolate_lt`), subtract,
and observe the difference has `natDegree ≤ k` but vanishes at the `k + 1` distinct points
`algebraMap F A x` (`x ∈ s`; distinct since `algebraMap` from a field into a nontrivial ring
is injective), hence is zero (`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`).

Also provided:
* `groundLine_coeff` — the same existential with the coefficient-wise reading
  `γ.coeff t = algebraMap F A (v₀.coeff t) + ζ * algebraMap F A (v₁.coeff t)` included;
* `groundLine_value_unique` — when `ζ ∉ Set.range (algebraMap F A)`, ground-line coordinates
  are unique;
* `eval_eq_of_groundLine_rep` — under the same genuineness hypothesis on `ζ`, any ground-line
  representation of `γ` reads off the prescribed values: `v₀.eval x = u₀ x` and
  `v₁.eval x = u₁ x` for all `x ∈ s`.

This is the interpolation step of [BCIKS20] (Ben-Sasson–Carmon–Ishai–Kopparty–Saraf,
*Proximity Gaps for Reed–Solomon Codes*), Claim 5.9. Axiom-clean.
-/

noncomputable section

open Polynomial

namespace ArkLib.GroundLine

variable {F A : Type*} [Field F] [CommRing A] [IsDomain A] [Algebra F A]

/-- Degree budget for the Lagrange interpolant through `k + 1` base-field nodes:
`natDegree ≤ k` (from `Lagrange.degree_interpolate_lt`: degree `< s.card = k + 1`). -/
lemma natDegree_interpolate_le [DecidableEq F] {k : ℕ} (s : Finset F)
    (hcard : s.card = k + 1) (u : F → F) :
    (Lagrange.interpolate s id u).natDegree ≤ k := by
  have h : (Lagrange.interpolate s id u).degree < ((k + 1 : ℕ) : WithBot ℕ) := by
    rw [← hcard]
    exact Lagrange.degree_interpolate_lt u (Set.injOn_id _)
  by_cases h0 : Lagrange.interpolate s id u = 0
  · simp [h0]
  · exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt h0).mpr h)

omit [IsDomain A] in
/-- Evaluating a mapped polynomial at an embedded point commutes with the embedding:
`(p.map (algebraMap F A)).eval (algebraMap F A x) = algebraMap F A (p.eval x)`.
(Named with a `_base` suffix to avoid clashing with Mathlib's simp lemma
`Polynomial.eval_map_algebraMap`, which rewrites to `aeval` instead.) -/
lemma eval_map_algebraMap_base (p : F[X]) (x : F) :
    (p.map (algebraMap F A)).eval (algebraMap F A x) = algebraMap F A (p.eval x) := by
  rw [eval_map, eval₂_at_apply]

/-- **Ground-line interpolation (BCIKS20 Claim 5.9, interpolation step).**
A polynomial `γ : A[X]` of `natDegree ≤ k` whose evaluations at the `k + 1` distinct
base-field points `algebraMap F A x` (`x ∈ s`, `s.card = k + 1`) lie on the ground line
`{algebraMap u + ζ * algebraMap v}` is itself of ground-line form
`γ = v₀.map (algebraMap F A) + C ζ * v₁.map (algebraMap F A)`, with `v₀ v₁ : F[X]` of
`natDegree ≤ k` (namely the Lagrange interpolants of the prescribed coordinates). -/
theorem groundLine_of_eval_groundLine
    (γ : A[X]) {k : ℕ} (hdeg : γ.natDegree ≤ k)
    (ζ : A) (s : Finset F) (hcard : s.card = k + 1) (u₀ u₁ : F → F)
    (hval : ∀ x ∈ s, γ.eval (algebraMap F A x)
      = algebraMap F A (u₀ x) + ζ * algebraMap F A (u₁ x)) :
    ∃ v₀ v₁ : F[X], v₀.natDegree ≤ k ∧ v₁.natDegree ≤ k ∧
      γ = v₀.map (algebraMap F A) + C ζ * v₁.map (algebraMap F A) := by
  classical
  set v₀ : F[X] := Lagrange.interpolate s id u₀ with hv₀
  set v₁ : F[X] := Lagrange.interpolate s id u₁ with hv₁
  have hd₀ : v₀.natDegree ≤ k := natDegree_interpolate_le s hcard u₀
  have hd₁ : v₁.natDegree ≤ k := natDegree_interpolate_le s hcard u₁
  refine ⟨v₀, v₁, hd₀, hd₁, ?_⟩
  set δ : A[X] := γ - (v₀.map (algebraMap F A) + C ζ * v₁.map (algebraMap F A)) with hδ
  have hδdeg : δ.natDegree ≤ k := by
    refine (natDegree_sub_le _ _).trans (max_le hdeg ?_)
    refine (natDegree_add_le _ _).trans (max_le (natDegree_map_le.trans hd₀) ?_)
    exact (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans hd₁)
  have hroots : ∀ y ∈ s.image (algebraMap F A), δ.eval y = 0 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have he₀ : v₀.eval x = u₀ x := by
      simpa using Lagrange.eval_interpolate_at_node u₀ (Function.injective_id.injOn) hx
    have he₁ : v₁.eval x = u₁ x := by
      simpa using Lagrange.eval_interpolate_at_node u₁ (Function.injective_id.injOn) hx
    have hsplit : δ.eval (algebraMap F A x)
        = γ.eval (algebraMap F A x)
          - (algebraMap F A (v₀.eval x) + ζ * algebraMap F A (v₁.eval x)) := by
      simp only [hδ, eval_sub, eval_add, eval_mul, eval_C, eval_map_algebraMap_base]
    rw [hsplit, hval x hx, he₀, he₁, sub_self]
  have hcardim : δ.natDegree < (s.image (algebraMap F A)).card := by
    rw [Finset.card_image_of_injective s (algebraMap F A).injective, hcard]
    exact Nat.lt_succ_of_le hδdeg
  have hδ0 : δ = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' δ
      (s.image (algebraMap F A)) hroots hcardim
  rw [hδ] at hδ0
  exact sub_eq_zero.mp hδ0

/-- **Coefficient-wise reading of ground-line interpolation.** Same hypotheses as
`groundLine_of_eval_groundLine`; the existential additionally carries the coefficient
identity `γ.coeff t = algebraMap F A (v₀.coeff t) + ζ * algebraMap F A (v₁.coeff t)`. -/
theorem groundLine_coeff
    (γ : A[X]) {k : ℕ} (hdeg : γ.natDegree ≤ k)
    (ζ : A) (s : Finset F) (hcard : s.card = k + 1) (u₀ u₁ : F → F)
    (hval : ∀ x ∈ s, γ.eval (algebraMap F A x)
      = algebraMap F A (u₀ x) + ζ * algebraMap F A (u₁ x)) :
    ∃ v₀ v₁ : F[X], v₀.natDegree ≤ k ∧ v₁.natDegree ≤ k ∧
      γ = v₀.map (algebraMap F A) + C ζ * v₁.map (algebraMap F A) ∧
      ∀ t, γ.coeff t = algebraMap F A (v₀.coeff t) + ζ * algebraMap F A (v₁.coeff t) := by
  obtain ⟨v₀, v₁, hd₀, hd₁, heq⟩ :=
    groundLine_of_eval_groundLine γ hdeg ζ s hcard u₀ u₁ hval
  refine ⟨v₀, v₁, hd₀, hd₁, heq, fun t => ?_⟩
  rw [heq]
  simp [coeff_map]

/-- **Uniqueness of ground-line coordinates.** When `ζ` is genuinely off the base field
(`ζ ∉ Set.range (algebraMap F A)`), ground-line representations of an element of `A` have
unique coordinates. -/
theorem groundLine_value_unique (ζ : A) (hζ : ζ ∉ Set.range (algebraMap F A))
    {a₀ a₁ b₀ b₁ : F}
    (h : algebraMap F A a₀ + ζ * algebraMap F A a₁
      = algebraMap F A b₀ + ζ * algebraMap F A b₁) :
    a₀ = b₀ ∧ a₁ = b₁ := by
  have hinj : Function.Injective (algebraMap F A) := (algebraMap F A).injective
  have key : a₁ = b₁ := by
    by_contra hne
    have hd : a₁ - b₁ ≠ 0 := sub_ne_zero.mpr hne
    refine hζ ⟨(b₀ - a₀) / (a₁ - b₁), ?_⟩
    have h2 : ζ * algebraMap F A (a₁ - b₁) = algebraMap F A (b₀ - a₀) := by
      rw [map_sub, map_sub]
      linear_combination h
    have h4 : algebraMap F A (a₁ - b₁) ≠ 0 := fun hc =>
      hd (hinj (hc.trans (map_zero (algebraMap F A)).symm))
    have h3 : algebraMap F A ((b₀ - a₀) / (a₁ - b₁)) * algebraMap F A (a₁ - b₁)
        = ζ * algebraMap F A (a₁ - b₁) := by
      rw [← map_mul, div_mul_cancel₀ _ hd, h2]
    exact mul_right_cancel₀ h4 h3
  refine ⟨hinj ?_, key⟩
  rw [key] at h
  exact add_right_cancel h

/-- **Value reading.** When `ζ ∉ Set.range (algebraMap F A)`, *any* ground-line
representation `γ = v₀.map (algebraMap F A) + C ζ * v₁.map (algebraMap F A)` of a polynomial
satisfying the ground-line evaluation constraints reads off the prescribed values at the
nodes: `v₀.eval x = u₀ x` and `v₁.eval x = u₁ x` for all `x ∈ s`. -/
theorem eval_eq_of_groundLine_rep
    (γ : A[X]) (ζ : A) (hζ : ζ ∉ Set.range (algebraMap F A))
    (s : Finset F) (u₀ u₁ : F → F)
    (hval : ∀ x ∈ s, γ.eval (algebraMap F A x)
      = algebraMap F A (u₀ x) + ζ * algebraMap F A (u₁ x))
    (v₀ v₁ : F[X])
    (hrep : γ = v₀.map (algebraMap F A) + C ζ * v₁.map (algebraMap F A)) :
    ∀ x ∈ s, v₀.eval x = u₀ x ∧ v₁.eval x = u₁ x := by
  intro x hx
  have h : algebraMap F A (v₀.eval x) + ζ * algebraMap F A (v₁.eval x)
      = algebraMap F A (u₀ x) + ζ * algebraMap F A (u₁ x) := by
    rw [← hval x hx, hrep]
    simp only [eval_add, eval_mul, eval_C, eval_map_algebraMap_base]
  exact groundLine_value_unique ζ hζ h

end ArkLib.GroundLine

end

section AxiomAudit

#print axioms ArkLib.GroundLine.natDegree_interpolate_le
#print axioms ArkLib.GroundLine.eval_map_algebraMap_base
#print axioms ArkLib.GroundLine.groundLine_of_eval_groundLine
#print axioms ArkLib.GroundLine.groundLine_coeff
#print axioms ArkLib.GroundLine.groundLine_value_unique
#print axioms ArkLib.GroundLine.eval_eq_of_groundLine_rep

end AxiomAudit
