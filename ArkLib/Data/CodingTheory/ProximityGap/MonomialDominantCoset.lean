/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MonomialDivisorWitness
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-!
# The dominant-coset MCA event (#371): both clauses, general parameters

The full assembly of the divisor-witness mechanism into a genuine `mcaEvent` —
the first interior witness with **both clauses discharged at arbitrary
parameters** (every previous interior evidence was per-instance kernel
enumeration).

Setting: the monomial stack `(x^{2d+1}, x^{2d})` on any injective domain, a
`d`-point *equal-power locus* `T` (`x^{2d} = A²` on `T`; in the smooth
instance, `T` = a `μ_d`-coset with `A = c₁^d`), and an anchor `x₀ = dom i₀`
**off** the locus.  At the scalar `γ = −x₀`:

* *agreement clause* — the line equals the degree-1 codeword `A²(x − x₀)` on
  all of `{i₀} ∪ T` (the divisor identity, `monomial_divisor_agreement`);
* *negative clause* — any joint pair must match the second row `x^{2d}` on the
  `d ≥ k` locus points, forcing (degree `< k` interpolation) the constant
  `A²`; at the anchor this demands `x₀^{2d} = A²` — excluded.  So no joint
  pair exists: the event is genuinely mutual.

Consequences, proven below:

* `dominantCoset_mcaEvent` — the event itself;
* `epsMCA_dominantCoset_floor` — every off-locus anchor produces a distinct
  bad scalar, so `ε_mca ≥ (#off-locus points)/q` at the slice
  `(1−δ)·n ≤ d+1`;
* `card_locus_le` + `epsMCA_interior_divisor_floor` — the locus has at most
  `2d` points, so `ε_mca ≥ (n − 2d)/q`.

This matches the probe-extracted census exactly (`(37, μ₉)`, `d = 3`:
`6 = 9 − 3` anchors per locus class, `18 = 3 classes × 6`); the bad scalars
`−x₀` range over `−`(domain∖locus) — the **dominant coset** `−μ_n` of the
SPECTRUM law, now a theorem at every parameter.  Together with
`monomial_badSet_mul_invariant` (closure) and `mcaEvent_lift_subdomain` (the
tower restriction), this is the complete lower half of the spectrum law; the
upper half is `InteriorSpectrumSilent` (`DeltaStarCeilingTightTheory.lean`).
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.MonomialDominantCoset

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The dominant-coset MCA event**: for the monomial stack `(x^{2d+1}, x^{2d})`,
a `d`-point equal-power locus `T` (`x^{2d} = A²` there) with `k ≤ d`, and an
off-locus anchor `i₀` (`x₀^{2d} ≠ A²`), the scalar `γ = −x₀` exhibits the MCA
event at every radius `δ` with `(1−δ)·n ≤ d+1`.  Both clauses are discharged:
the divisor identity gives the agreement, and degree-`< k` interpolation on the
locus plus the anchor exclusion kills every joint pair. -/
theorem dominantCoset_mcaEvent (dom : Fin n ↪ F) {k d : ℕ}
    (hk2 : 2 ≤ k) (hkd : k ≤ d)
    {A : F} {T : Finset (Fin n)} (hTcard : T.card = d)
    (hT : ∀ i ∈ T, (dom i) ^ (2 * d) = A ^ 2)
    {i₀ : Fin n} (hx₀ : ¬ (dom i₀) ^ (2 * d) = A ^ 2)
    {u₀ u₁ : Fin n → F}
    (hu₀ : ∀ i, u₀ i = (dom i) ^ (2 * d + 1))
    (hu₁ : ∀ i, u₁ i = (dom i) ^ (2 * d))
    {δ : ℝ≥0} (hδ : (1 - δ) * (n : ℝ≥0) ≤ (d : ℝ≥0) + 1) :
    mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      u₀ u₁ (-(dom i₀)) := by
  have hi₀T : i₀ ∉ T := fun h => hx₀ (hT i₀ h)
  refine ⟨insert i₀ T, ?_, ?_, ?_⟩
  · -- cardinality: |{i₀} ∪ T| = d + 1
    rw [Finset.card_insert_of_notMem hi₀T, hTcard, Fintype.card_fin]
    calc (1 - δ) * (n : ℝ≥0) ≤ (d : ℝ≥0) + 1 := hδ
      _ = ((d + 1 : ℕ) : ℝ≥0) := by push_cast; ring
  · -- agreement: the degree-1 codeword A²(x − x₀) explains the line on the set
    have hdegP : (C (A ^ 2) * (X - C (dom i₀))).degree < ((k : ℕ) : WithBot ℕ) := by
      have hnd : (C (A ^ 2) * (X - C (dom i₀))).natDegree ≤ 1 := by
        refine le_trans Polynomial.natDegree_mul_le ?_
        rw [Polynomial.natDegree_C, Polynomial.natDegree_X_sub_C]
      refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
      exact_mod_cast
        (by omega : (C (A ^ 2) * (X - C (dom i₀))).natDegree < k)
    refine ⟨fun i => (C (A ^ 2) * (X - C (dom i₀))).eval (dom i),
      ⟨C (A ^ 2) * (X - C (dom i₀)), hdegP, rfl⟩, ?_⟩
    intro i hi
    have hx : dom i = dom i₀ ∨ (dom i) ^ (2 * d) = A ^ 2 := by
      rcases Finset.mem_insert.mp hi with h | h
      · left; rw [h]
      · right; exact hT i h
    have hid := ProximityGap.MonomialDivisorWitness.monomial_divisor_agreement
      d (dom i₀) A (dom i) hx
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_X]
    rw [hu₀ i, hu₁ i, smul_eq_mul]
    linear_combination -hid
  · -- the negative clause: no joint pair survives the anchor exclusion
    rintro ⟨v₀, hv₀, v₁, hv₁, hagr⟩
    obtain ⟨Q, hQ, rfl⟩ := hv₁
    have hQA : Q = C (A ^ 2) := by
      have hzero : Q - C (A ^ 2) = 0 := by
        refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
          (f := Q - C (A ^ 2)) (s := T.image dom) ?_ ?_
        · have hcard : (T.image dom).card = d := by
            rw [Finset.card_image_of_injective _ dom.injective, hTcard]
          rw [hcard]
          have h0k : (C (A ^ 2)).degree < ((k : ℕ) : WithBot ℕ) :=
            lt_of_le_of_lt Polynomial.degree_C_le
              (by exact_mod_cast (by omega : 0 < k))
          calc (Q - C (A ^ 2)).degree
              ≤ max Q.degree (C (A ^ 2)).degree := Polynomial.degree_sub_le _ _
            _ < ((k : ℕ) : WithBot ℕ) := max_lt hQ h0k
            _ ≤ ((d : ℕ) : WithBot ℕ) := by exact_mod_cast hkd
        · intro x hx
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
          have h1 : Q.eval (dom i) = u₁ i :=
            (hagr i (Finset.mem_insert_of_mem hi)).2
          rw [Polynomial.eval_sub, Polynomial.eval_C, h1, hu₁ i, hT i hi,
            sub_self]
      exact sub_eq_zero.mp hzero
    have h2 : Q.eval (dom i₀) = u₁ i₀ :=
      (hagr i₀ (Finset.mem_insert_self _ _)).2
    rw [hQA, Polynomial.eval_C, hu₁ i₀] at h2
    exact hx₀ h2.symm

open Classical in
/-- **The dominant-coset floor**: every off-locus domain point is an anchor,
each producing a distinct bad scalar `−x₀` — so `ε_mca` at the slice is at
least `(#off-locus points)/q`. -/
theorem epsMCA_dominantCoset_floor (dom : Fin n ↪ F) {k d : ℕ}
    (hk2 : 2 ≤ k) (hkd : k ≤ d)
    {A : F} {T : Finset (Fin n)} (hTcard : T.card = d)
    (hT : ∀ i ∈ T, (dom i) ^ (2 * d) = A ^ 2)
    {δ : ℝ≥0} (hδ : (1 - δ) * (n : ℝ≥0) ≤ (d : ℝ≥0) + 1) :
    ((Finset.univ.filter
        (fun i : Fin n => ¬ (dom i) ^ (2 * d) = A ^ 2)).card : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ := by
  set u₀ : Fin n → F := fun i => (dom i) ^ (2 * d + 1) with hu₀def
  set u₁ : Fin n → F := fun i => (dom i) ^ (2 * d) with hu₁def
  have hinj : Function.Injective (fun i : Fin n => -(dom i)) :=
    fun a b hab => dom.injective (neg_injective hab)
  have hGcard : ((Finset.univ.filter
      (fun i : Fin n => ¬ (dom i) ^ (2 * d) = A ^ 2)).image
        (fun i => -(dom i))).card
      = (Finset.univ.filter
          (fun i : Fin n => ¬ (dom i) ^ (2 * d) = A ^ 2)).card :=
    Finset.card_image_of_injective _ hinj
  rw [← hGcard]
  refine ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    _ δ ![u₀, u₁] _ ?_
  intro γ hγ
  obtain ⟨i₀, hi₀mem, rfl⟩ := Finset.mem_image.mp hγ
  have hx₀ : ¬ (dom i₀) ^ (2 * d) = A ^ 2 :=
    (Finset.mem_filter.mp hi₀mem).2
  exact dominantCoset_mcaEvent dom hk2 hkd hTcard hT hx₀
    (fun i => rfl) (fun i => rfl) hδ

/-- **The locus is small**: at most `2d` domain points satisfy `x^{2d} = A²`
(they inject into the roots of `X^{2d} − A²`). -/
theorem card_locus_le (dom : Fin n ↪ F) {d : ℕ} (hd : 1 ≤ d) (A : F) :
    (Finset.univ.filter
        (fun i : Fin n => (dom i) ^ (2 * d) = A ^ 2)).card ≤ 2 * d := by
  classical
  have hPne : (X ^ (2 * d) - C (A ^ 2) : Polynomial F) ≠ 0 := by
    intro h
    have h2 : (X ^ (2 * d) - C (A ^ 2) : Polynomial F).natDegree = 2 * d :=
      Polynomial.natDegree_X_pow_sub_C
    rw [h, Polynomial.natDegree_zero] at h2
    omega
  have hmap : ∀ i ∈ Finset.univ.filter
      (fun i : Fin n => (dom i) ^ (2 * d) = A ^ 2),
      dom i ∈ (X ^ (2 * d) - C (A ^ 2) : Polynomial F).roots.toFinset := by
    intro i hi
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne]
    have hroot : (dom i) ^ (2 * d) = A ^ 2 := (Finset.mem_filter.mp hi).2
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, hroot, sub_self]
  calc (Finset.univ.filter
      (fun i : Fin n => (dom i) ^ (2 * d) = A ^ 2)).card
      ≤ (X ^ (2 * d) - C (A ^ 2) : Polynomial F).roots.toFinset.card :=
        Finset.card_le_card_of_injOn (fun i => dom i) hmap
          (fun a _ b _ h => dom.injective h)
    _ ≤ Multiset.card (X ^ (2 * d) - C (A ^ 2) : Polynomial F).roots :=
        Multiset.toFinset_card_le _
    _ ≤ (X ^ (2 * d) - C (A ^ 2) : Polynomial F).natDegree :=
        Polynomial.card_roots' _
    _ = 2 * d := Polynomial.natDegree_X_pow_sub_C

open Classical in
/-- **The interior divisor floor**: at the slice `(1−δ)·n ≤ d+1`, any `d`-point
equal-power locus in the domain forces `ε_mca ≥ (n − 2d)/q` — the formal lower
half of the SPECTRUM law at every divisor level (at the smooth instance, `T` is
a `μ_d`-coset and the bad scalars sweep `−μ_n` minus the locus). -/
theorem epsMCA_interior_divisor_floor (dom : Fin n ↪ F) {k d : ℕ}
    (hk2 : 2 ≤ k) (hkd : k ≤ d)
    {A : F} {T : Finset (Fin n)} (hTcard : T.card = d)
    (hT : ∀ i ∈ T, (dom i) ^ (2 * d) = A ^ 2)
    {δ : ℝ≥0} (hδ : (1 - δ) * (n : ℝ≥0) ≤ (d : ℝ≥0) + 1) :
    (((n - 2 * d : ℕ)) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ := by
  refine le_trans ?_ (epsMCA_dominantCoset_floor dom hk2 hkd hTcard hT hδ)
  have hd1 : 1 ≤ d := by omega
  have hle := card_locus_le dom hd1 A
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin n)))
    (p := fun i : Fin n => (dom i) ^ (2 * d) = A ^ 2)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  have hcard : n - 2 * d ≤ (Finset.univ.filter
      (fun i : Fin n => ¬ (dom i) ^ (2 * d) = A ^ 2)).card := by omega
  gcongr

end ProximityGap.MonomialDominantCoset

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.MonomialDominantCoset.dominantCoset_mcaEvent
#print axioms ProximityGap.MonomialDominantCoset.epsMCA_dominantCoset_floor
#print axioms ProximityGap.MonomialDominantCoset.card_locus_le
#print axioms ProximityGap.MonomialDominantCoset.epsMCA_interior_divisor_floor
