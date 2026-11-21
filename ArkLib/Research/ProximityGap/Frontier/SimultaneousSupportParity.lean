/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.SimultaneousSupportRank
import ArkLib.Data.CodingTheory.ReedSolomon

/-! # Explicit interpolation matrices for the MCA support-rank test

On a support `S`, choose `k` anchors, or all of `S` when it has fewer than `k` sites.
The parity equations subtract the polynomial interpolated at the anchors from the
received value at each site. The same matrices apply to the two received rows and to
each proposed fold. Their coefficients depend only on the supplied evaluation points. -/

namespace ProximityGap.SimultaneousSupportParity

open ProjectiveQuotientSupport SimultaneousSupportRank
open scoped NNReal ENNReal

variable {F I : Type} [Field F]

/-- Anchors for interpolation on a support. -/
def Anchors (k : ℕ) (S T : Finset I) : Prop :=
  T ⊆ S ∧ T.card ≤ k ∧ (T.card = k ∨ T = S)

/-- Every support admits anchors, including the empty support and dimension zero. -/
theorem exists_anchors (k : ℕ) (S : Finset I) : ∃ T, Anchors k S T := by
  by_cases h : k ≤ S.card
  · obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq h
    exact ⟨T, hT, hcard.le, Or.inl hcard⟩
  · exact ⟨S, Finset.Subset.rfl, le_of_not_ge h, Or.inr rfl⟩

variable [DecidableEq I]

/-- The residual of the anchor interpolant evaluated on every site in the support. -/
noncomputable def parity (D : I ↪ F) (S T : Finset I) : (I → F) →ₗ[F] (S → F) :=
  LinearMap.pi fun i =>
    LinearMap.proj (i : I) - (Polynomial.leval (D i)).comp (Lagrange.interpolate T D)

/-- A row in the parity matrix is a point value minus a weighted sum of anchor values. -/
theorem parity_apply (D : I ↪ F) (S T : Finset I) (w : I → F) (i : S) :
    parity D S T w i =
      w i - ∑ j ∈ T, w j * (Lagrange.basis T D j).eval (D i) := by
  change w i - (Lagrange.interpolate T D w).eval (D i) = _
  simp [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul]

section

variable [Finite I] [Nonempty I] [Finite F]

/-- The explicit parity kernel is exactly the space of words with a codeword on the support. -/
theorem ker_parity (D : I ↪ F) (S T : Finset I) {k : ℕ} (h : Anchors k S T) :
    LinearMap.ker (parity D S T) = restrictedCode (ReedSolomon.code D k) S := by
  classical
  let _ := Fintype.ofFinite I
  let _ := Fintype.ofFinite F
  ext w
  change parity D S T w = 0 ↔ _
  rw [show w ∈ restrictedCode (ReedSolomon.code D k) S ↔
        ∃ c ∈ ReedSolomon.code D k, ∀ i ∈ S, c i = w i from
      quotient_mk_mem_quotientSupportSubmodule_iff _ S w]
  constructor
  · intro hw
    let p := Lagrange.interpolate T D w
    have hdeg : p.degree < k :=
      (Lagrange.degree_interpolate_lt w D.injective.injOn).trans_le (by exact_mod_cast h.2.1)
    refine ⟨fun i => p.eval (D i),
      ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval p hdeg (fun _ => rfl), ?_⟩
    intro i hi
    exact (sub_eq_zero.mp (congrFun hw ⟨i, hi⟩)).symm
  · rintro ⟨c, hc, hw⟩
    obtain ⟨p, hp, heval⟩ := ReedSolomon.mem_code_iff_eval.mp hc
    ext i
    change w i - (Lagrange.interpolate T D w).eval (D i) = 0
    apply sub_eq_zero.mpr
    rcases h.2.2 with hfull | rfl
    · have eqp : p = Lagrange.interpolate T D w :=
        Lagrange.eq_interpolate_of_eval_eq _ D.injective.injOn (hfull.symm ▸ hp)
          (fun j hj => (heval j).trans (hw j (h.1 hj)))
      rw [← eqp]
      exact (hw i i.property).symm.trans (heval i).symm
    · exact (Lagrange.eval_interpolate_at_node w D.injective.injOn i.property).symm

/-- All selected folded rows are tested by stacking their parity matrices. -/
noncomputable def folded (D : I ↪ F) (G : Finset F) (S T : G → Finset I) :
    ((I → F) × (I → F)) →ₗ[F] ((g : G) → S g → F) :=
  LinearMap.pi fun g => (parity D (S g) (T g)).comp
    (LinearMap.fst F (I → F) (I → F) + (g : F) • LinearMap.snd F (I → F) (I → F))

/-- Stacking the explicit parity matrices gives precisely the simultaneous folded space. -/
theorem ker_folded (D : I ↪ F) {k : ℕ} (G : Finset F) (S T : G → Finset I)
    (h : ∀ g, Anchors k (S g) (T g)) :
    LinearMap.ker (folded D G S T) = space (ReedSolomon.code D k) G S := by
  ext x
  change (folded D G S T x = 0) ↔ _
  rw [funext_iff]
  change (∀ g : G, parity D (S g) (T g) (x.1 + (g : F) • x.2) = 0) ↔ _
  simp only [space, Submodule.mem_iInf, foldSpace, Submodule.mem_comap]
  apply forall_congr'
  intro g
  exact SetLike.ext_iff.mp (ker_parity D (S g) (T g) (h g)) _

/-- The second block in a joint-agreement test applies the same parity matrix to each row. -/
theorem joint_eq (D : I ↪ F) {k : ℕ} (S T : Finset I) (h : Anchors k S T) :
    jointSpace (ReedSolomon.code D k) S =
      (LinearMap.ker (parity D S T)).prod (LinearMap.ker (parity D S T)) := by
  rw [ker_parity D S T h]
  rfl

end

section

variable [Nonempty I] [Fintype I] [Fintype F] [SampleableType F]

/-- The sponsor's affine-line probability exceeds the count budget iff some collection of
explicit folded interpolation matrices has a dimension drop at every assigned scalar. -/
theorem canonical_failure_iff_parity (D : I ↪ F) (k B : ℕ) (δ : ℝ≥0) :
    (B : ℝ≥0∞) / Fintype.card F <
      CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator F) (ReedSolomon.code D k)
        (δ : ℝ) ↔
      ∃ (G : Finset F) (_ : G.card = B + 1) (S T : G → Finset I),
        (∀ g, (S g).card ≥ (1 - δ) * Fintype.card I) ∧
        (∀ g, Anchors k (S g) (T g)) ∧
        ∀ g, Module.finrank F ↥(LinearMap.ker (folded D G S T) ⊓
          (LinearMap.ker (parity D (S g) (T g))).prod (LinearMap.ker (parity D (S g) (T g)))) <
          Module.finrank F (LinearMap.ker (folded D G S T)) := by
  classical
  rw [canonical_failure_iff]
  constructor
  · rintro ⟨G, hG, S, hs, hdim⟩
    choose T hT using fun g => exists_anchors k (S g)
    refine ⟨G, hG, S, T, hs, hT, fun g => ?_⟩
    rw [ker_folded D G S T hT, ← joint_eq D (S g) (T g) (hT g)]
    exact hdim g
  · rintro ⟨G, hG, S, T, hs, hT, hdim⟩
    refine ⟨G, hG, S, hs, fun g => ?_⟩
    rw [← ker_folded D G S T hT, joint_eq D (S g) (T g) (hT g)]
    exact hdim g

end

#print axioms ker_parity
#print axioms canonical_failure_iff_parity

end ProximityGap.SimultaneousSupportParity
