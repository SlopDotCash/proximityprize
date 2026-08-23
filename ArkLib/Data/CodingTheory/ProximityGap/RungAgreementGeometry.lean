/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowParametricCapstone

/-!
# The rung agreement geometry (#371, round-7 target): polynomial-pair bricks

The d = 2 level-1 rung at `p = 12289` (issue #371 round 7) needs a good-side
surface beyond per-witness subset counting.  This file lands the k-GENERAL,
RADIUS-GENERAL skeleton for polynomial-pair stacks — the stratum of the rung's
antipodal-pencil extremal `(X^h, X^{h+1})`:

* `poly_witness_defect_dichotomy` — for rows that ARE polynomial evaluations
  (`uⱼ = Rⱼ` on the domain, any degrees), every bad scalar yields an agreement
  set `S` and a codeword `P` (`deg P < k`) with either the zero-class
  `R₀ + γR₁ = P` or a nonzero defect `R₀ + γR₁ − P = g·m_S` — at EVERY
  radius, both below and above UDR;
* **`poly_cross_agreement`** — the rung's key law: two DISTINCT bad scalars
  force `R₁` to agree with a degree-`< k` polynomial on the overlap of their
  witnesses (subtract the identities and evaluate: the vanishing terms die).
  Witness overlaps live inside the `(<k)`-agreement geometry of `R₁`;
* `lowDegree_agreement_inter_le` — distinct `(<k)`-agreement sets of `R₁`
  pairwise intersect in `< k` points (roots of the difference): the agreement
  geometry is a near-sunflower-free design, Fisher-countable by
  `pairwise_inter_le_subsets_card_le`.

Probe record: `probe_rung_fiber.py` — at the rung instance the mod-`R₁` fiber
reproduces the bad set exactly (16 = inversion orbit + zero-class, uniform
multiplicity 28); adversarial pairs have EMPTY fibers; the pencil's degeneracy
is `x⁹ ≡ ±x` on half-cosets — `maxAgree(R₁) = 8` attained by half-cosets.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section RungBricks

variable {dom : Fin n ↪ F} {k : ℕ}
variable {u₀ u₁ : Fin n → F} {R₀ R₁ : F[X]}

open Classical in
/-- **The polynomial-pair defect dichotomy** (any k, any radius).  For rows
that are polynomial evaluations, every bad scalar yields an agreement set and
a codeword with the zero-class or a nonzero defect multiple of `m_S`. -/
theorem poly_witness_defect_dichotomy
    (hpoly₀ : ∀ i, u₀ i = R₀.eval (dom i))
    (hpoly₁ : ∀ i, u₁ i = R₁.eval (dom i))
    {δ : ℝ≥0} {γ : F}
    (hbad : mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ) :
    ∃ (S : Finset (Fin n)) (P : F[X]), P.degree < k ∧
      (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card (Fin n) ∧
      (R₀ + C γ * R₁ - P = 0 ∨
        ∃ g : F[X], g ≠ 0 ∧
          R₀ + C γ * R₁ - P = g * vanishingPoly dom S) := by
  obtain ⟨S, hsz, ⟨wc, hwc, hag⟩, -⟩ := hbad
  obtain ⟨P, hPdeg, rfl⟩ := hwc
  refine ⟨S, P, hPdeg, hsz, ?_⟩
  set Φ : F[X] := R₀ + C γ * R₁ - P with hΦdef
  rcases eq_or_ne Φ 0 with h0 | hne
  · exact Or.inl h0
  · refine Or.inr ?_
    have hΦeval : ∀ i ∈ S, Φ.eval (dom i) = 0 := by
      intro i hi
      have hwci := hag i hi
      simp only [hΦdef, eval_sub, eval_add, eval_mul, eval_C]
      rw [← hpoly₀ i, ← hpoly₁ i]
      have : P.eval (dom i) = u₀ i + γ * u₁ i := by
        simpa [smul_eq_mul] using hwci
      linear_combination -this
    have hdvd : vanishingPoly dom S ∣ Φ := by
      rw [vanishingPoly]
      refine Finset.prod_dvd_of_coprime ?_ ?_
      · intro i hi j hj hij
        exact isCoprime_X_sub_C_of_isUnit_sub
          (Ne.isUnit (sub_ne_zero.mpr (fun h => hij (dom.injective h))))
      · intro i hi
        rw [Polynomial.dvd_iff_isRoot]
        exact hΦeval i hi
    obtain ⟨g, hg⟩ := hdvd
    have hgne : g ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hg
      exact hne hg
    exact ⟨g, hgne, by rw [hg, mul_comm]⟩

/-- **THE CROSS-AGREEMENT LAW** (the rung's key mechanism): two distinct bad
scalars force the direction row to agree with a degree-`< k` polynomial on the
overlap of their witnesses. -/
theorem poly_cross_agreement (hk : 1 ≤ k)
    {γ₁ γ₂ : F} (hne : γ₁ ≠ γ₂)
    {P₁ P₂ g₁ g₂ : F[X]} {S₁ S₂ : Finset (Fin n)}
    (hdP₁ : P₁.degree < k) (hdP₂ : P₂.degree < k)
    (hid₁ : R₀ + C γ₁ * R₁ - P₁ = g₁ * vanishingPoly dom S₁)
    (hid₂ : R₀ + C γ₂ * R₁ - P₂ = g₂ * vanishingPoly dom S₂) :
    ∃ q : F[X], q.natDegree < k ∧
      ∀ i ∈ S₁ ∩ S₂, R₁.eval (dom i) = q.eval (dom i) := by
  have hP₁' : P₁.natDegree < k := by
    rcases eq_or_ne P₁ 0 with rfl | h
    · simpa using hk
    · exact (natDegree_lt_iff_degree_lt h).mpr (by exact_mod_cast hdP₁)
  have hP₂' : P₂.natDegree < k := by
    rcases eq_or_ne P₂ 0 with rfl | h
    · simpa using hk
    · exact (natDegree_lt_iff_degree_lt h).mpr (by exact_mod_cast hdP₂)
  refine ⟨C (γ₁ - γ₂)⁻¹ * (P₁ - P₂), ?_, ?_⟩
  · have h1 := natDegree_C_mul_le ((γ₁ - γ₂)⁻¹) (P₁ - P₂)
    have h2 := natDegree_sub_le P₁ P₂
    have h3 : max P₁.natDegree P₂.natDegree < k := max_lt hP₁' hP₂'
    omega
  · intro i hi
    rw [Finset.mem_inter] at hi
    have hγne : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
    -- evaluate the subtracted identities at dom i: the m-terms vanish
    have hev₁ := congrArg (Polynomial.eval (dom i)) hid₁
    have hev₂ := congrArg (Polynomial.eval (dom i)) hid₂
    rw [eval_mul, vanishingPoly_eval_eq_zero dom hi.1, mul_zero] at hev₁
    rw [eval_mul, vanishingPoly_eval_eq_zero dom hi.2, mul_zero] at hev₂
    simp only [eval_sub, eval_add, eval_mul, eval_C] at hev₁ hev₂ ⊢
    have hkey : (γ₁ - γ₂) * R₁.eval (dom i)
        = P₁.eval (dom i) - P₂.eval (dom i) := by
      linear_combination hev₁ - hev₂
    field_simp
    linear_combination hkey

/-- **The agreement geometry is near-disjoint**: agreement sets of `R₁` with
DISTINCT degree-`< k` polynomials intersect in fewer than `k` points
(`k ≥ 1`; the intersection embeds into the roots of the difference). -/
theorem lowDegree_agreement_inter_le (dom : Fin n ↪ F) (R₁ : F[X])
    {q₁ q₂ : F[X]} (hq : q₁ ≠ q₂) (hd₁ : q₁.natDegree < k) (hd₂ : q₂.natDegree < k)
    (hk : 1 ≤ k) :
    ((Finset.univ.filter (fun i => R₁.eval (dom i) = q₁.eval (dom i))) ∩
     (Finset.univ.filter (fun i => R₁.eval (dom i) = q₂.eval (dom i)))).card
      ≤ k - 1 := by
  classical
  have hsub : ((Finset.univ.filter (fun i => R₁.eval (dom i) = q₁.eval (dom i))) ∩
      (Finset.univ.filter (fun i => R₁.eval (dom i) = q₂.eval (dom i))))
        ⊆ Finset.univ.filter (fun i => (q₁ - q₂).eval (dom i) = 0) := by
    intro i hi
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [eval_sub, sub_eq_zero, ← hi.1.2, ← hi.2.2]
  refine le_trans (Finset.card_le_card hsub) ?_
  -- roots of a nonzero polynomial of degree ≤ k−1 among embedded points
  have hqne : q₁ - q₂ ≠ 0 := sub_ne_zero.mpr hq
  have hdvd : vanishingPoly dom
      (Finset.univ.filter (fun i => (q₁ - q₂).eval (dom i) = 0)) ∣ (q₁ - q₂) := by
    rw [vanishingPoly]
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro i hi j hj hij
      exact isCoprime_X_sub_C_of_isUnit_sub
        (Ne.isUnit (sub_ne_zero.mpr (fun h => hij (dom.injective h))))
    · intro i hi
      rw [Finset.mem_filter] at hi
      rw [Polynomial.dvd_iff_isRoot]
      exact hi.2
  have hdeg := Polynomial.natDegree_le_of_dvd hdvd hqne
  rw [vanishingPoly_natDegree] at hdeg
  have hdq : (q₁ - q₂).natDegree ≤ k - 1 := by
    have := natDegree_sub_le q₁ q₂
    omega
  omega

/-- **Zero-class uniqueness**: when the direction row has degree >= k, at most
one scalar puts the pencil inside the code (`R₀ + γR₁` of degree `< k`). -/
theorem poly_zero_class_unique (hR₁ : k ≤ R₁.natDegree)
    {γ₁ γ₂ : F} {P₁ P₂ : F[X]}
    (hdP₁ : P₁.natDegree < k) (hdP₂ : P₂.natDegree < k)
    (h₁ : R₀ + C γ₁ * R₁ = P₁) (h₂ : R₀ + C γ₂ * R₁ = P₂) :
    γ₁ = γ₂ := by
  by_contra hne
  have hkey : C (γ₁ - γ₂) * R₁ = P₁ - P₂ := by
    rw [C_sub]
    linear_combination h₁ - h₂
  have hCne : (C (γ₁ - γ₂) : F[X]) ≠ 0 :=
    C_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hR₁ne : R₁ ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hR₁
    omega
  have hdeg : (C (γ₁ - γ₂) * R₁).natDegree = R₁.natDegree := by
    rw [Polynomial.natDegree_mul hCne hR₁ne, natDegree_C, zero_add]
  have hsub : (P₁ - P₂).natDegree < k :=
    lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hdP₁ hdP₂)
  rw [hkey] at hdeg
  omega

end RungBricks

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.poly_witness_defect_dichotomy
#print axioms ProximityGap.WBPencil.poly_cross_agreement
#print axioms ProximityGap.WBPencil.lowDegree_agreement_inter_le
#print axioms ProximityGap.WBPencil.poly_zero_class_unique
