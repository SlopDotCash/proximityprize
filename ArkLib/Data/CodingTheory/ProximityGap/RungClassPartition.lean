/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungInstanceF12289

/-!
# The rung class keystone (#371): big-overlap pairs share a frame class

(The module name says "partition"; only the pairwise statement is proved —
see the scope note below.)

The pairwise keystone of the census assembly.  Two scalars whose witnesses
overlap in `≥ k` points are not merely cross-agreeing: they attach to the SAME
maximal agreement set `A` of the direction row with the SAME frame
polynomial `r`, and both defect identities convert exactly into the
`(A, h, r)` frame form

  `(R₀ − r) + C γⱼ·(m_A·h) = gⱼ·m_{Sⱼ}`

consumed by `maximal_frame_attached_card_le` (off-part disjointness,
per-class cap `n − |A|`).

**Scope: this is a PAIRWISE statement, not a global partition.**  The
theorems below attach each *pair* of witnesses with overlap `≥ k` to a
common frame.  They do **not** show that the bad set decomposes into
*solo* scalars (pairwise `< k` witness overlaps — the Fisher regime) and
disjoint *frame classes* (the reservoir regime): the relation "witnesses
overlap in `≥ k` points" need not be transitive, and one scalar can attach
to different frames through different neighbours.  Concrete instance
(checked by exact `F₁₇` enumeration in the 2026-10-28 audit, not in Lean):
`D = (1,2,4,8,16,15,13,9) = μ₈ ⊂ F₁₇`, `k = 2`, radius `5/8`,
`u₀ = (0,0,0,13,6,0,0,0)`, `u₁ = (1,0,0,4,3,1,1,1)`.  Scalars `0, 1, 2`
have bad witnesses `S₀ = {0,1,2}`, `S₁ = {1,2,3}`, `S₂ = {2,3,4}` explained
by `0, 0, X − 4`; adjacent overlaps have size `2`, the outer one size `1`.
The pair `(0,1)` gets cross polynomial `0`, maximal agreement set `{1,2}`
and frame `0`; the pair `(1,2)` gets `X − 4`, agreement set `{2,3}` and
frame `4 − X`.  So scalar `1` lies in two distinct pair-induced frames.
This does not rule out a cleverly chosen alternative witness assignment
or a later global covering argument, but a class partition (or a cover
with controlled multiplicities) needs a separate global
uniqueness/selection theorem, which is not proved here.  The declarations:

* `eq_of_degree_lt_of_agree` — interpolation uniqueness on the domain;
* `cross_frame_poly_eq` — the two scalars' frames coincide as polynomials;
* **`paired_scalars_share_class`** — the pairwise keystone: for one pair,
  the maximal agreement set, the `m_A·h` factorization, frame equality,
  and both frame-form identities, packaged.

Probe record (empirical, specific instances only): the pencil
(16 = 2 classes × 8) and the 2-block record (20 = 2 × 10) are exactly
2-class configurations; the census ceiling 22 adds two fiber-tuned extras
(`probe_wb371_blockladder2.py`).
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section ClassPartition

variable {dom : Fin n ↪ F} {k : ℕ} {R₀ R₁ : F[X]}

/-- Equality of polynomials of degree `< k` agreeing at `k` domain points
(the workhorse uniqueness form of `pencil_degenerate_of_roots`). -/
theorem eq_of_degree_lt_of_agree (hk : 1 ≤ k) {f g : F[X]}
    {T : Finset (Fin n)}
    (hdf : f.natDegree < k) (hdg : g.natDegree < k) (hT : k ≤ T.card)
    (hag : ∀ i ∈ T, f.eval (dom i) = g.eval (dom i)) : f = g := by
  classical
  by_contra hne
  have hWne : f - g ≠ 0 := sub_ne_zero.mpr hne
  have hdvd : vanishingPoly dom T ∣ f - g :=
    vanishingPoly_dvd_of_eval_zero dom (fun i hi => by
      rw [eval_sub, hag i hi, sub_self])
  have hdeg := Polynomial.natDegree_le_of_dvd hdvd hWne
  rw [vanishingPoly_natDegree] at hdeg
  have : (f - g).natDegree < k := lt_of_le_of_lt (natDegree_sub_le f g)
    (max_lt hdf hdg)
  omega

/-- **Cross-pair frame equality**: when two distinct bad scalars overlap in
`≥ k` points, their frames `Pⱼ − γⱼ·q` (against the cross polynomial `q`)
coincide as polynomials. -/
theorem cross_frame_poly_eq (hk : 1 ≤ k)
    {γ₁ γ₂ : F} (hne : γ₁ ≠ γ₂) {P₁ P₂ g₁ g₂ q : F[X]}
    {S₁ S₂ : Finset (Fin n)}
    (hdP₁ : P₁.natDegree < k) (hdP₂ : P₂.natDegree < k)
    (hdq : q.natDegree < k)
    (hq : ∀ i ∈ S₁ ∩ S₂, R₁.eval (dom i) = q.eval (dom i))
    (hcard : k ≤ (S₁ ∩ S₂).card)
    (hid₁ : R₀ + C γ₁ * R₁ - P₁ = g₁ * vanishingPoly dom S₁)
    (hid₂ : R₀ + C γ₂ * R₁ - P₂ = g₂ * vanishingPoly dom S₂) :
    P₁ - C γ₁ * q = P₂ - C γ₂ * q := by
  refine eq_of_degree_lt_of_agree (dom := dom) hk ?_ ?_ hcard ?_
  · exact lt_of_le_of_lt (natDegree_sub_le _ _)
      (max_lt hdP₁ (lt_of_le_of_lt (natDegree_C_mul_le _ _) hdq))
  · exact lt_of_le_of_lt (natDegree_sub_le _ _)
      (max_lt hdP₂ (lt_of_le_of_lt (natDegree_C_mul_le _ _) hdq))
  · intro i hi
    rw [Finset.mem_inter] at hi
    have hev₁ := congrArg (Polynomial.eval (dom i)) hid₁
    have hev₂ := congrArg (Polynomial.eval (dom i)) hid₂
    rw [eval_mul, vanishingPoly_eval_eq_zero dom hi.1, mul_zero] at hev₁
    rw [eval_mul, vanishingPoly_eval_eq_zero dom hi.2, mul_zero] at hev₂
    have hqi := hq i (Finset.mem_inter.mpr hi)
    simp only [eval_sub, eval_add, eval_mul, eval_C] at hev₁ hev₂ ⊢
    rw [← hqi]
    linear_combination hev₂ - hev₁

/-- **THE CLASS KEYSTONE**: two distinct bad scalars with witness overlap
`≥ k` share a full frame class — a common maximal agreement set `A ⊇ S₁∩S₂`
of the direction row, a factor `h` with `R₁ − q = m_A·h`, and a common
frame `r` putting BOTH identities in the exact `(A, h, r)` form consumed by
the per-class reservoir cap. -/
theorem paired_scalars_share_class (hk : 1 ≤ k)
    {γ₁ γ₂ : F} (hne : γ₁ ≠ γ₂) {P₁ P₂ g₁ g₂ : F[X]}
    {S₁ S₂ : Finset (Fin n)}
    (hdP₁ : P₁.degree < k) (hdP₂ : P₂.degree < k)
    (hcard : k ≤ (S₁ ∩ S₂).card)
    (hid₁ : R₀ + C γ₁ * R₁ - P₁ = g₁ * vanishingPoly dom S₁)
    (hid₂ : R₀ + C γ₂ * R₁ - P₂ = g₂ * vanishingPoly dom S₂) :
    ∃ (q r h : F[X]) (A : Finset (Fin n)),
      q.natDegree < k ∧ r.natDegree < k ∧
      (∀ i, i ∈ A ↔ R₁.eval (dom i) = q.eval (dom i)) ∧
      S₁ ∩ S₂ ⊆ A ∧
      R₁ - q = vanishingPoly dom A * h ∧
      (R₀ - r) + C γ₁ * (vanishingPoly dom A * h)
        = g₁ * vanishingPoly dom S₁ ∧
      (R₀ - r) + C γ₂ * (vanishingPoly dom A * h)
        = g₂ * vanishingPoly dom S₂ := by
  classical
  obtain ⟨q, hdq, hqag⟩ := poly_cross_agreement hk hne hdP₁ hdP₂ hid₁ hid₂
  set A : Finset (Fin n) :=
    Finset.univ.filter (fun i => R₁.eval (dom i) = q.eval (dom i)) with hAdef
  have hAmem : ∀ i, i ∈ A ↔ R₁.eval (dom i) = q.eval (dom i) := by
    intro i
    rw [hAdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ i, h⟩⟩
  have hsub : S₁ ∩ S₂ ⊆ A := fun i hi => (hAmem i).mpr (hqag i hi)
  obtain ⟨h, hfac⟩ : ∃ h : F[X], R₁ - q = vanishingPoly dom A * h := by
    obtain ⟨h, hh⟩ := vanishingPoly_dvd_of_eval_zero dom
      (T := A) (f := R₁ - q) (fun i hi => by
        rw [eval_sub, (hAmem i).mp hi, sub_self])
    exact ⟨h, hh⟩
  have hdP₁' : P₁.natDegree < k := by
    rcases eq_or_ne P₁ 0 with rfl | h0
    · simpa using (show 0 < k by omega)
    · exact (natDegree_lt_iff_degree_lt h0).mpr (by exact_mod_cast hdP₁)
  have hdP₂' : P₂.natDegree < k := by
    rcases eq_or_ne P₂ 0 with rfl | h0
    · simpa using (show 0 < k by omega)
    · exact (natDegree_lt_iff_degree_lt h0).mpr (by exact_mod_cast hdP₂)
  have hreq := cross_frame_poly_eq (dom := dom) hk hne hdP₁' hdP₂' hdq
    hqag hcard hid₁ hid₂
  refine ⟨q, P₁ - C γ₁ * q, h, A, hdq, ?_, hAmem, hsub, hfac, ?_, ?_⟩
  · exact lt_of_le_of_lt (natDegree_sub_le _ _)
      (max_lt hdP₁' (lt_of_le_of_lt (natDegree_C_mul_le _ _) hdq))
  · rw [← hfac]
    linear_combination hid₁
  · rw [← hfac, hreq]
    linear_combination hid₂

end ClassPartition

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.eq_of_degree_lt_of_agree
#print axioms ProximityGap.WBPencil.cross_frame_poly_eq
#print axioms ProximityGap.WBPencil.paired_scalars_share_class
