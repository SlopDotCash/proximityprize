/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS

/-!
# The general locus-collapse MCA event (#371): every anchored witness class

The cycle-2 R1 classification (`probe_wb_r1_witness_locus_converse.py`,
q-stable across 8 fields) shows the anchored interior witnesses of the monomial
stack `(x^a, x^{a−1})` are exactly the *equal-`(a−1)`-power loci*: sets `T`
where `x^{a−1}` is constant (`= c`), of any size `≥ k`, plus the line root.
This file proves that mechanism at full generality — subsuming
`MonomialDominantCoset.lean` (the special case `a−1 = 2d`, `c = A²`,
`|T| = d`):

* `locus_agreement` — the pointwise identity: at every `x` with `x = x₀` or
  `x^{a−1} = c`, the line `x^{a−1}(x − x₀)` equals the degree-1 codeword
  `c(x − x₀)` (one `pow_succ` + `ring`; the polynomial identity is
  `X^{a−1}(X−x₀) − c(X−x₀) = (X−x₀)(X^{a−1}−c)`).
* `locusCollapse_mcaEvent` — the full both-clause event: `T` an equal-power
  locus with `k ≤ |T|`, anchor `x₀` off the locus (`x₀^{a−1} ≠ c`),
  `γ = −x₀` ⟹ MCA event at every radius with `(1−δ)·n ≤ |T| + 1`.  The
  negative clause: any joint `v₁` is forced constant `c` on `T` by
  degree-`<k` interpolation, contradicting the anchor.
* `epsMCA_locusCollapse_floor` — `ε_mca ≥ (n − (a−1))/q` at the slice: the
  locus condition `x^{a−1} = c` excludes at most `a−1` domain points, and
  every remaining point is an anchor.

Consumers instantiate `T` inside any equal-`e`-power class with `e ∣ a−1`
(`x^e = E ⟹ x^{a−1} = E^{(a−1)/e}`): the `μ_e`-coset loci of the SPECTRUM
law at every divisor level and every sub-locus size `≥ k`.  The remaining
witness classes are the rootless ones (`e ∣ a` constant collapse at `γ = 0`,
and the balanced sign-mixed quadruples — see DISPROOF_LOG cycle-2 R1).
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.MonomialLocusCollapse

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The locus-collapse identity**, pointwise: at every `x` with `x = x₀` or
`x^{a−1} = c`, the monomial line at scalar `−x₀` equals the degree-1 codeword
`c·(x − x₀)`. -/
theorem locus_agreement (a : ℕ) (ha : 1 ≤ a) (x₀ c x : F)
    (hx : x = x₀ ∨ x ^ (a - 1) = c) :
    x ^ a + (-x₀) * x ^ (a - 1) = c * x - c * x₀ := by
  have hpow : x ^ a = x * x ^ (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 from by omega]
    rw [pow_succ]
    ring
  rcases hx with h | h
  · subst h
    rw [hpow]
    ring
  · rw [hpow, h]
    ring

/-- **The general locus-collapse MCA event**: for the monomial stack
`(x^a, x^{a−1})`, an equal-`(a−1)`-power locus `T` (`x^{a−1} = c` there) of
size `≥ k`, and an off-locus anchor `i₀` (`x₀^{a−1} ≠ c`), the scalar
`γ = −x₀` exhibits the MCA event at every radius `δ` with
`(1−δ)·n ≤ |T| + 1`. -/
theorem locusCollapse_mcaEvent (dom : Fin n ↪ F) {k a : ℕ}
    (hk2 : 2 ≤ k) (ha : 1 ≤ a)
    {c : F} {T : Finset (Fin n)} (hm : k ≤ T.card)
    (hT : ∀ i ∈ T, (dom i) ^ (a - 1) = c)
    {i₀ : Fin n} (hx₀ : ¬ (dom i₀) ^ (a - 1) = c)
    {u₀ u₁ : Fin n → F}
    (hu₀ : ∀ i, u₀ i = (dom i) ^ a)
    (hu₁ : ∀ i, u₁ i = (dom i) ^ (a - 1))
    {δ : ℝ≥0} (hδ : (1 - δ) * (n : ℝ≥0) ≤ (T.card : ℝ≥0) + 1) :
    mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      u₀ u₁ (-(dom i₀)) := by
  have hi₀T : i₀ ∉ T := fun h => hx₀ (hT i₀ h)
  refine ⟨insert i₀ T, ?_, ?_, ?_⟩
  · -- cardinality: |{i₀} ∪ T| = |T| + 1
    rw [Finset.card_insert_of_notMem hi₀T, Fintype.card_fin]
    calc (1 - δ) * (n : ℝ≥0) ≤ (T.card : ℝ≥0) + 1 := hδ
      _ = ((T.card + 1 : ℕ) : ℝ≥0) := by push_cast; ring
  · -- agreement: the degree-1 codeword c·(x − x₀) explains the line
    have hdegP : (C c * (X - C (dom i₀))).degree < ((k : ℕ) : WithBot ℕ) := by
      have hnd : (C c * (X - C (dom i₀))).natDegree ≤ 1 := by
        refine le_trans Polynomial.natDegree_mul_le ?_
        rw [Polynomial.natDegree_C, Polynomial.natDegree_X_sub_C]
      refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
      exact_mod_cast
        (by omega : (C c * (X - C (dom i₀))).natDegree < k)
    refine ⟨fun i => (C c * (X - C (dom i₀))).eval (dom i),
      ⟨C c * (X - C (dom i₀)), hdegP, rfl⟩, ?_⟩
    intro i hi
    have hx : dom i = dom i₀ ∨ (dom i) ^ (a - 1) = c := by
      rcases Finset.mem_insert.mp hi with h | h
      · left; rw [h]
      · right; exact hT i h
    have hid := locus_agreement a ha (dom i₀) c (dom i) hx
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_X]
    rw [hu₀ i, hu₁ i, smul_eq_mul]
    linear_combination -hid
  · -- the negative clause: interpolation forces v₁ = c, the anchor refuses
    rintro ⟨v₀, hv₀, v₁, hv₁, hagr⟩
    obtain ⟨Q, hQ, rfl⟩ := hv₁
    have hQA : Q = C c := by
      have hzero : Q - C c = 0 := by
        refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
          (f := Q - C c) (s := T.image dom) ?_ ?_
        · have hcard : (T.image dom).card = T.card :=
            Finset.card_image_of_injective _ dom.injective
          rw [hcard]
          have h0k : (C c).degree < ((k : ℕ) : WithBot ℕ) :=
            lt_of_le_of_lt Polynomial.degree_C_le
              (by exact_mod_cast (by omega : 0 < k))
          calc (Q - C c).degree
              ≤ max Q.degree (C c).degree := Polynomial.degree_sub_le _ _
            _ < ((k : ℕ) : WithBot ℕ) := max_lt hQ h0k
            _ ≤ ((T.card : ℕ) : WithBot ℕ) := by exact_mod_cast hm
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

/-- **The off-locus count**: at most `a−1` domain points satisfy
`x^{a−1} = c` (they inject into the roots of `X^{a−1} − c`), provided
`1 ≤ a − 1`. -/
theorem card_locus_le (dom : Fin n ↪ F) {a : ℕ} (ha2 : 2 ≤ a) (c : F) :
    (Finset.univ.filter
        (fun i : Fin n => (dom i) ^ (a - 1) = c)).card ≤ a - 1 := by
  classical
  have hPne : (X ^ (a - 1) - C c : Polynomial F) ≠ 0 := by
    intro h
    have h2 : (X ^ (a - 1) - C c : Polynomial F).natDegree = a - 1 :=
      Polynomial.natDegree_X_pow_sub_C
    rw [h, Polynomial.natDegree_zero] at h2
    omega
  have hmap : ∀ i ∈ Finset.univ.filter
      (fun i : Fin n => (dom i) ^ (a - 1) = c),
      dom i ∈ (X ^ (a - 1) - C c : Polynomial F).roots.toFinset := by
    intro i hi
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne]
    have hroot : (dom i) ^ (a - 1) = c := (Finset.mem_filter.mp hi).2
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, hroot, sub_self]
  calc (Finset.univ.filter
      (fun i : Fin n => (dom i) ^ (a - 1) = c)).card
      ≤ (X ^ (a - 1) - C c : Polynomial F).roots.toFinset.card :=
        Finset.card_le_card_of_injOn (fun i => dom i) hmap
          (fun x _ y _ h => dom.injective h)
    _ ≤ Multiset.card (X ^ (a - 1) - C c : Polynomial F).roots :=
        Multiset.toFinset_card_le _
    _ ≤ (X ^ (a - 1) - C c : Polynomial F).natDegree :=
        Polynomial.card_roots' _
    _ = a - 1 := Polynomial.natDegree_X_pow_sub_C

open Classical in
/-- **The locus-collapse floor**: any equal-`(a−1)`-power locus of size `≥ k`
forces `ε_mca ≥ (n − (a−1))/q` at the slice `(1−δ)·n ≤ |T| + 1` — every
off-locus domain point anchors a distinct bad scalar. -/
theorem epsMCA_locusCollapse_floor (dom : Fin n ↪ F) {k a : ℕ}
    (hk2 : 2 ≤ k) (ha2 : 2 ≤ a)
    {c : F} {T : Finset (Fin n)} (hm : k ≤ T.card)
    (hT : ∀ i ∈ T, (dom i) ^ (a - 1) = c)
    {δ : ℝ≥0} (hδ : (1 - δ) * (n : ℝ≥0) ≤ (T.card : ℝ≥0) + 1) :
    (((n - (a - 1) : ℕ)) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ := by
  set u₀ : Fin n → F := fun i => (dom i) ^ a with hu₀def
  set u₁ : Fin n → F := fun i => (dom i) ^ (a - 1) with hu₁def
  have hinj : Function.Injective (fun i : Fin n => -(dom i)) :=
    fun x y hxy => dom.injective (neg_injective hxy)
  have hGcard : ((Finset.univ.filter
      (fun i : Fin n => ¬ (dom i) ^ (a - 1) = c)).image
        (fun i => -(dom i))).card
      = (Finset.univ.filter
          (fun i : Fin n => ¬ (dom i) ^ (a - 1) = c)).card :=
    Finset.card_image_of_injective _ hinj
  have hbound : (((n - (a - 1) : ℕ)) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ (((Finset.univ.filter
          (fun i : Fin n => ¬ (dom i) ^ (a - 1) = c)).image
            (fun i => -(dom i))).card : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞) := by
    rw [hGcard]
    have hle := card_locus_le dom ha2 c
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin n)))
      (p := fun i : Fin n => (dom i) ^ (a - 1) = c)
    rw [Finset.card_univ, Fintype.card_fin] at hsplit
    have hcard : n - (a - 1) ≤ (Finset.univ.filter
        (fun i : Fin n => ¬ (dom i) ^ (a - 1) = c)).card := by omega
    gcongr
  refine le_trans hbound ?_
  refine ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    _ δ ![u₀, u₁] _ ?_
  intro γ hγ
  obtain ⟨i₀, hi₀mem, rfl⟩ := Finset.mem_image.mp hγ
  have hx₀ : ¬ (dom i₀) ^ (a - 1) = c :=
    (Finset.mem_filter.mp hi₀mem).2
  exact locusCollapse_mcaEvent dom hk2 (by omega) hm hT hx₀
    (fun i => rfl) (fun i => rfl) hδ

end ProximityGap.MonomialLocusCollapse

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.MonomialLocusCollapse.locus_agreement
#print axioms ProximityGap.MonomialLocusCollapse.locusCollapse_mcaEvent
#print axioms ProximityGap.MonomialLocusCollapse.card_locus_le
#print axioms ProximityGap.MonomialLocusCollapse.epsMCA_locusCollapse_floor
