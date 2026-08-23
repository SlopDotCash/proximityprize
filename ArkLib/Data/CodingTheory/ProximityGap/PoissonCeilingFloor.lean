/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CeilingMarch

/-!
# The Poisson ceiling floor, Part A: the exact incidence counts (#371, cycle 2 S1′)

The probe-discovered **Poisson ceiling law** (five field sizes, 1–3%):
`E[badcount at the ceiling] = q(1 − e^{−C(n,k+1)/q})`.  Since `sup ≥ mean`, its
Bonferroni lower bound is an **unconditional, census-free bad side** for the ceiling
radius of every fixed-dimension evaluation code — no cyclotomic injectivity, no
`(2^μ)^{2^{μ−1}}` threshold, no Landau resultants, no Thorner–Zaman supply.

**This file (Part A)** proves the exact counting core:

1. *(the solve-one-coordinate characterization)* `explainableOn_iff_solve`: on a
   `(d+2)`-subset `T`, a word is explainable at degree `d` iff its value at any chosen
   `i₀ ∈ T` equals the Lagrange evaluation of its other `d+1` values — explainability on
   a minimal overdetermined set is ONE solved coordinate.
2. *(the singleton count)* `card_explainable_words`: exactly `q^{n−1}` words of `F^n`
   are explainable on a fixed `(d+2)`-subset.
3. *(the direction count)* `card_not_explainable_words`: exactly `q^n − q^{n−1}` words
   are NOT explainable on a fixed `(d+2)`-subset.
4. *(the pair count, the triangular solve)* `card_explainable_words_pair`: for distinct
   `(d+2)`-subsets exactly `q^{n−2}` words are explainable on both — choosing
   `i₀ ∈ T \ T'` and `i₁ ∈ T' \ T`, the `T'`-completion reads neither special
   coordinate, so the constraint system is triangular: solve `i₁`, then `i₀`.

Part B2 (next) adds pointwise Bonferroni and assembles everything into
`ε_mca(evalCode, 1 − (d+2)/n) ≥ (C(n,d+2) − corrections)/q ≥ C(n,d+2)/(4q)` for
`2·C(n,d+2) ≤ q`, and the census-free pin family it opens (bands
`[(C(n,r)/r)/q, C(n,r)/(4q))`, nonempty for every `r ≥ 5` — every `μ`, polynomial
thresholds, the μ = 7 wall removed).

Probe: `probe_poisson_ceiling_law.py` (to land with Part B).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Finset Polynomial
open scoped NNReal ENNReal
open ArkLib.ProximityGap.KKH26 ArkLib.ProximityGap.KKH26CeilingMarch

namespace ArkLib.ProximityGap.PoissonCeilingFloor

variable {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n]

/-! ## The solve-one-coordinate characterization -/

open Classical in
/-- The Lagrange completion: the value at `i₀` of the degree-`≤ d` interpolant through
the values of `v` on `T.erase i₀`. -/
noncomputable def lagrangeCompletion (g : ZMod p) (i₀ : Fin n) (T : Finset (Fin n))
    (v : Fin n → ZMod p) : ZMod p :=
  (Lagrange.interpolate (T.erase i₀) (fun i : Fin n => g ^ (i : ℕ)) v).eval (g ^ (i₀ : ℕ))

open Classical in
/-- **The solve-one-coordinate characterization**: on a `(d+2)`-set `T`, explainability
at degree `d` says exactly that the value at a chosen `i₀ ∈ T` is the Lagrange completion
of the other `d + 1` values. -/
theorem explainableOn_iff_solve (hg : orderOf g = n) {d : ℕ} {T : Finset (Fin n)}
    (hT : T.card = d + 2) {i₀ : Fin n} (hi₀ : i₀ ∈ T) (v : Fin n → ZMod p) :
    ExplainableOn g d v T ↔ v i₀ = lagrangeCompletion g i₀ T v := by
  have hcard : (T.erase i₀).card = d + 1 := by
    rw [Finset.card_erase_of_mem hi₀, hT]
    omega
  have hdeg : (Lagrange.interpolate (T.erase i₀) (fun i : Fin n => g ^ (i : ℕ)) v).natDegree
      ≤ d := by
    have hlt := Lagrange.degree_interpolate_lt (r := v)
      (nodes_injOn hg (T.erase i₀))
    rcases eq_or_ne (Lagrange.interpolate (T.erase i₀) (fun i : Fin n => g ^ (i : ℕ)) v) 0
      with h0 | h0
    · rw [h0]; simp
    · have := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hlt
      omega
  constructor
  · rintro ⟨q, hqd, hq⟩
    -- q agrees with the interpolant on T.erase i₀ (d+1 nodes) hence everywhere
    have heq : q = Lagrange.interpolate (T.erase i₀) (fun i : Fin n => g ^ (i : ℕ)) v := by
      refine explain_unique hg hqd hdeg (le_of_eq hcard.symm) (fun i hi => ?_)
      rw [← hq i (Finset.mem_of_mem_erase hi)]
      exact (Lagrange.eval_interpolate_at_node v (nodes_injOn hg (T.erase i₀)) hi).symm
    rw [hq i₀ hi₀, heq]
    unfold lagrangeCompletion
    rfl
  · intro hsolve
    refine ⟨Lagrange.interpolate (T.erase i₀) (fun i : Fin n => g ^ (i : ℕ)) v, hdeg,
      fun i hi => ?_⟩
    by_cases hii : i = i₀
    · subst hii
      exact hsolve
    · exact (Lagrange.eval_interpolate_at_node v
        (nodes_injOn hg (T.erase i₀)) (Finset.mem_erase.mpr ⟨hii, hi⟩)).symm

/-! ## The exact counts -/

open Classical in
/-- The completion only reads values on `T.erase i₀`. -/
theorem lagrangeCompletion_congr (g : ZMod p) (i₀ : Fin n) (T : Finset (Fin n))
    {v w : Fin n → ZMod p} (h : ∀ i ∈ T.erase i₀, v i = w i) :
    lagrangeCompletion g i₀ T v = lagrangeCompletion g i₀ T w := by
  unfold lagrangeCompletion
  congr 1
  exact Lagrange.interpolate_eq_of_values_eq_on _ _ h

open Classical in
/-- **The singleton count**: exactly `q^{n−1}` words are explainable on a fixed
`(d+2)`-subset — explainability on a minimal overdetermined set is one solved
coordinate. -/
theorem card_explainable_words (hg : orderOf g = n) {d : ℕ} {T : Finset (Fin n)}
    (hT : T.card = d + 2) {i₀ : Fin n} (hi₀ : i₀ ∈ T) :
    (Finset.univ.filter (fun v : Fin n → ZMod p => ExplainableOn g d v T)).card
      = p ^ (n - 1) := by
  classical
  have htarget : Fintype.card ({j : Fin n // j ≠ i₀} → ZMod p) = p ^ (n - 1) := by
    have h1 : Fintype.card {j : Fin n // j ≠ i₀} = n - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
    rw [Fintype.card_fun, h1, ZMod.card]
  -- the zero-padded reading of a restricted word
  set pad : ({j : Fin n // j ≠ i₀} → ZMod p) → (Fin n → ZMod p) :=
    fun w i => if h : i = i₀ then 0 else w ⟨i, h⟩ with hpad
  set ext : ({j : Fin n // j ≠ i₀} → ZMod p) → (Fin n → ZMod p) :=
    fun w i => if h : i = i₀ then lagrangeCompletion g i₀ T (pad w) else w ⟨i, h⟩
    with hext
  have hext_off : ∀ (w : {j : Fin n // j ≠ i₀} → ZMod p) (i : Fin n) (h : i ≠ i₀),
      ext w i = w ⟨i, h⟩ := by
    intro w i h
    simp [hext, h]
  have hext_read : ∀ w : {j : Fin n // j ≠ i₀} → ZMod p,
      lagrangeCompletion g i₀ T (ext w) = lagrangeCompletion g i₀ T (pad w) := by
    intro w
    refine lagrangeCompletion_congr g i₀ T (fun i hi => ?_)
    have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
    simp [hext, hpad, hne]
  rw [show p ^ (n - 1) = Fintype.card ({j : Fin n // j ≠ i₀} → ZMod p) from htarget.symm,
    ← Finset.card_univ]
  refine Finset.card_bij'
    (fun (v : Fin n → ZMod p) _ => fun i : {j : Fin n // j ≠ i₀} => v i.1)
    (fun w _ => ext w) ?_ ?_ ?_ ?_
  · intro v _
    exact Finset.mem_univ _
  · intro w _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [explainableOn_iff_solve hg hT hi₀]
    calc ext w i₀ = lagrangeCompletion g i₀ T (pad w) := by simp [hext]
    _ = lagrangeCompletion g i₀ T (ext w) := (hext_read w).symm
  · intro v hv
    funext i
    dsimp only
    by_cases hii : i = i₀
    · rw [hii]
      have hv' := (Finset.mem_filter.mp hv).2
      rw [explainableOn_iff_solve hg hT hi₀] at hv'
      calc ext (fun j : {j : Fin n // j ≠ i₀} => v j.1) i₀
          = lagrangeCompletion g i₀ T (pad (fun j : {j : Fin n // j ≠ i₀} => v j.1)) := by
            simp [hext]
      _ = lagrangeCompletion g i₀ T v := by
            refine lagrangeCompletion_congr g i₀ T (fun i hi => ?_)
            have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
            simp [hpad, hne]
      _ = v i₀ := hv'.symm
    · exact hext_off (fun j : {j : Fin n // j ≠ i₀} => v j.1) i hii
  · intro w _
    funext i
    dsimp only
    rw [hext_off w i.1 i.2]

open Classical in
/-- **The complement count**: exactly `q^n − q^{n−1}` words are NOT explainable on a
fixed `(d+2)`-subset. -/
theorem card_not_explainable_words (hg : orderOf g = n) {d : ℕ} {T : Finset (Fin n)}
    (hT : T.card = d + 2) {i₀ : Fin n} (hi₀ : i₀ ∈ T) :
    (Finset.univ.filter (fun v : Fin n → ZMod p => ¬ ExplainableOn g d v T)).card
      = p ^ n - p ^ (n - 1) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n → ZMod p)))
    (fun v => ExplainableOn g d v T)
  have htot : (Finset.univ : Finset (Fin n → ZMod p)).card = p ^ n := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hexp := card_explainable_words hg hT hi₀ (g := g)
  omega

end ArkLib.ProximityGap.PoissonCeilingFloor



/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.explainableOn_iff_solve
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.card_explainable_words
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.card_not_explainable_words

namespace ArkLib.ProximityGap.PoissonCeilingFloor

variable {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n]

/-! ## Part B1: the pair count — the triangular solve -/

open Classical in
/-- **The pair count**: for distinct `(d+2)`-subsets `T ≠ T'`, exactly `q^{n−2}` words are
explainable on both.  The system is *triangular*: choosing `i₀ ∈ T \ T'` and
`i₁ ∈ T' \ T`, the `T'`-completion reads `T'.erase i₁` (neither special coordinate), so
it is determined by the free coordinates alone; the `T`-completion reads `T.erase i₀`
(which may contain `i₁`, already determined).  Two solved coordinates: `q^{n−2}`. -/
theorem card_explainable_words_pair (hg : orderOf g = n) {d : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = d + 2) (hT' : T'.card = d + 2)
    (hne : T ≠ T') :
    (Finset.univ.filter (fun v : Fin n → ZMod p =>
        ExplainableOn g d v T ∧ ExplainableOn g d v T')).card
      = p ^ (n - 2) := by
  classical
  obtain ⟨i₀, hi₀T, hi₀T'⟩ : ∃ i, i ∈ T ∧ i ∉ T' := by
    by_contra hc
    push Not at hc
    exact hne (Finset.eq_of_subset_of_card_le (fun x hx => hc x hx)
      (le_of_eq (hT'.trans hT.symm)))
  obtain ⟨i₁, hi₁T', hi₁T⟩ : ∃ i, i ∈ T' ∧ i ∉ T := by
    by_contra hc
    push Not at hc
    exact hne (Finset.eq_of_subset_of_card_le (fun x hx => hc x hx)
      (le_of_eq (hT.trans hT'.symm))).symm
  have hi₀₁ : i₀ ≠ i₁ := fun h => hi₀T' (h ▸ hi₁T')
  have htarget : Fintype.card ({j : Fin n // j ≠ i₀ ∧ j ≠ i₁} → ZMod p) = p ^ (n - 2) := by
    have h1 : Fintype.card {j : Fin n // j ≠ i₀ ∧ j ≠ i₁} = n - 2 := by
      have he : Fintype.card {j : Fin n // j ≠ i₀ ∧ j ≠ i₁}
          = ((Finset.univ : Finset (Fin n)).filter (fun j => j ≠ i₀ ∧ j ≠ i₁)).card :=
        Fintype.card_subtype _
      have hsplit : (Finset.univ : Finset (Fin n)).filter (fun j => j ≠ i₀ ∧ j ≠ i₁)
          = (Finset.univ \ {i₀, i₁}) := by
        ext j
        simp [Finset.mem_sdiff, not_or, and_comm]
      rw [he, hsplit, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
        Fintype.card_fin, Finset.card_insert_of_notMem (by simp [hi₀₁]),
        Finset.card_singleton]
    rw [Fintype.card_fun, h1, ZMod.card]
  set pad : ({j : Fin n // j ≠ i₀ ∧ j ≠ i₁} → ZMod p) → (Fin n → ZMod p) :=
    fun w i => if h : i = i₀ ∨ i = i₁ then 0 else w ⟨i, by tauto⟩ with hpad
  set step1 : ({j : Fin n // j ≠ i₀ ∧ j ≠ i₁} → ZMod p) → (Fin n → ZMod p) :=
    fun w i => if h : i = i₁ then lagrangeCompletion g i₁ T' (pad w) else pad w i
    with hstep1
  set ext2 : ({j : Fin n // j ≠ i₀ ∧ j ≠ i₁} → ZMod p) → (Fin n → ZMod p) :=
    fun w i => if h : i = i₀ then lagrangeCompletion g i₀ T (step1 w) else step1 w i
    with hext2
  have hT'sub : ∀ i ∈ T'.erase i₁, i ≠ i₀ ∧ i ≠ i₁ := by
    intro i hi
    exact ⟨fun h => hi₀T' (h ▸ Finset.mem_of_mem_erase hi), (Finset.mem_erase.mp hi).1⟩
  have hstep1_off : ∀ w (i : Fin n), i ≠ i₁ → step1 w i = pad w i := by
    intro w i h
    simp [hstep1, h]
  have hext2_off : ∀ w (i : Fin n), i ≠ i₀ → ext2 w i = step1 w i := by
    intro w i h
    simp [hext2, h]
  have hext2_free : ∀ w (i : Fin n) (h : i ≠ i₀ ∧ i ≠ i₁), ext2 w i = w ⟨i, h⟩ := by
    intro w i h
    rw [hext2_off w i h.1, hstep1_off w i h.2]
    simp [hpad, h.1, h.2]
  have hcompl1 : ∀ w, lagrangeCompletion g i₁ T' (ext2 w)
      = lagrangeCompletion g i₁ T' (pad w) := by
    intro w
    refine lagrangeCompletion_congr g i₁ T' (fun i hi => ?_)
    obtain ⟨h0, h1⟩ := hT'sub i hi
    rw [hext2_off w i h0, hstep1_off w i h1]
  have hcompl2 : ∀ w, lagrangeCompletion g i₀ T (ext2 w)
      = lagrangeCompletion g i₀ T (step1 w) := by
    intro w
    refine lagrangeCompletion_congr g i₀ T (fun i hi => ?_)
    exact hext2_off w i (Finset.mem_erase.mp hi).1
  have hboth : ∀ w, ExplainableOn g d (ext2 w) T ∧ ExplainableOn g d (ext2 w) T' := by
    intro w
    constructor
    · rw [explainableOn_iff_solve hg hT hi₀T]
      calc ext2 w i₀ = lagrangeCompletion g i₀ T (step1 w) := by simp [hext2]
      _ = lagrangeCompletion g i₀ T (ext2 w) := (hcompl2 w).symm
    · rw [explainableOn_iff_solve hg hT' hi₁T']
      calc ext2 w i₁ = step1 w i₁ := hext2_off w i₁ (Ne.symm hi₀₁)
      _ = lagrangeCompletion g i₁ T' (pad w) := by simp [hstep1]
      _ = lagrangeCompletion g i₁ T' (ext2 w) := (hcompl1 w).symm
  rw [show p ^ (n - 2)
      = Fintype.card ({j : Fin n // j ≠ i₀ ∧ j ≠ i₁} → ZMod p) from htarget.symm,
    ← Finset.card_univ]
  refine Finset.card_bij'
    (fun (v : Fin n → ZMod p) _ => fun i : {j : Fin n // j ≠ i₀ ∧ j ≠ i₁} => v i.1)
    (fun w _ => ext2 w) ?_ ?_ ?_ ?_
  · intro v _
    exact Finset.mem_univ _
  · intro w _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hboth w⟩
  · intro v hv
    funext i
    dsimp only
    obtain ⟨hvT, hvT'⟩ := (Finset.mem_filter.mp hv).2
    set vr : {j : Fin n // j ≠ i₀ ∧ j ≠ i₁} → ZMod p :=
      fun k => v k.1 with hvr
    -- the padded restriction agrees with v on T'.erase i₁
    have hpadv : ∀ l ∈ T'.erase i₁, pad vr l = v l := by
      intro l hl
      obtain ⟨hl0, hl1⟩ := hT'sub l hl
      simp [hpad, hvr, hl0, hl1]
    -- step1 of the restriction agrees with v on T.erase i₀
    have hstep1v : ∀ j ∈ T.erase i₀, step1 vr j = v j := by
      intro j hj
      have hj₀ : j ≠ i₀ := (Finset.mem_erase.mp hj).1
      by_cases hj₁ : j = i₁
      · rw [hj₁]
        rw [explainableOn_iff_solve hg hT' hi₁T'] at hvT'
        calc step1 vr i₁ = lagrangeCompletion g i₁ T' (pad vr) := by simp [hstep1]
        _ = lagrangeCompletion g i₁ T' v := lagrangeCompletion_congr g i₁ T' hpadv
        _ = v i₁ := hvT'.symm
      · rw [hstep1_off vr j hj₁]
        simp [hpad, hvr, hj₀, hj₁]
    by_cases h₀ : i = i₀
    · rw [h₀]
      rw [explainableOn_iff_solve hg hT hi₀T] at hvT
      calc ext2 vr i₀ = lagrangeCompletion g i₀ T (step1 vr) := by simp [hext2]
      _ = lagrangeCompletion g i₀ T v := lagrangeCompletion_congr g i₀ T hstep1v
      _ = v i₀ := hvT.symm
    · by_cases h₁ : i = i₁
      · rw [h₁]
        rw [explainableOn_iff_solve hg hT' hi₁T'] at hvT'
        calc ext2 vr i₁ = step1 vr i₁ := hext2_off vr i₁ (Ne.symm hi₀₁)
        _ = lagrangeCompletion g i₁ T' (pad vr) := by simp [hstep1]
        _ = lagrangeCompletion g i₁ T' v := lagrangeCompletion_congr g i₁ T' hpadv
        _ = v i₁ := hvT'.symm
      · exact hext2_free vr i ⟨h₀, h₁⟩
  · intro w _
    funext k
    dsimp only
    exact hext2_free w k.1 k.2

end ArkLib.ProximityGap.PoissonCeilingFloor

#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.card_explainable_words_pair

namespace ArkLib.ProximityGap.PoissonCeilingFloor

/-! ## Part B2a: pointwise Bonferroni (ordered-pair, ℕ-clean form) -/

open Classical in
/-- **Bonferroni, second order**: over any finite family,
`2·Σ_T |A_T| ≤ 2·|⋃ A_T| + Σ_{(T,T') distinct ordered} |A_T ∩ A_T'|`.  Pointwise this is
`2m ≤ 2 + m(m−1)` for multiplicity `m ≥ 1`. -/
theorem two_mul_sum_card_le {α β : Type} [DecidableEq α] [DecidableEq β]
    (𝒯 : Finset β) (A : β → Finset α) :
    2 * ∑ T ∈ 𝒯, (A T).card
      ≤ 2 * (𝒯.biUnion A).card
        + ∑ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card := by
  classical
  set U := 𝒯.biUnion A with hU
  -- single counts through U
  have hsub : ∀ T ∈ 𝒯, A T ⊆ U := fun T hT x hx =>
    Finset.mem_biUnion.mpr ⟨T, hT, hx⟩
  have hsingle : ∀ T ∈ 𝒯, (A T).card
      = ∑ x ∈ U, (if x ∈ A T then 1 else 0) := by
    intro T hT
    rw [Finset.sum_ite_mem U (A T) (fun _ => 1)]
    rw [Finset.inter_comm, Finset.inter_eq_left.mpr (hsub T hT)]
    simp
  -- pair counts through U
  have hpair : ∀ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card
      = ∑ x ∈ U, (if x ∈ A TT'.1 ∧ x ∈ A TT'.2 then 1 else 0) := by
    intro TT' hTT'
    have hmem := Finset.mem_offDiag.mp hTT'
    have hsubI : A TT'.1 ∩ A TT'.2 ⊆ U :=
      subset_trans (Finset.inter_subset_left) (hsub _ hmem.1)
    calc (A TT'.1 ∩ A TT'.2).card
        = ∑ x ∈ U, (if x ∈ A TT'.1 ∩ A TT'.2 then 1 else 0) := by
          rw [Finset.sum_ite_mem U (A TT'.1 ∩ A TT'.2) (fun _ => 1)]
          rw [Finset.inter_comm U (A TT'.1 ∩ A TT'.2), Finset.inter_eq_left.mpr hsubI]
          simp
    _ = ∑ x ∈ U, (if x ∈ A TT'.1 ∧ x ∈ A TT'.2 then 1 else 0) :=
        Finset.sum_congr rfl (fun x _ =>
          if_congr (by simp [Finset.mem_inter]) rfl rfl)
  -- the multiplicity of a point
  set m : α → ℕ := fun x => (𝒯.filter (fun T => x ∈ A T)).card with hm
  have hswap1 : (∑ T ∈ 𝒯, (A T).card) = ∑ x ∈ U, m x := by
    rw [Finset.sum_congr rfl hsingle, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact (Finset.card_filter _ _).symm
  have hswap2 : (∑ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card)
      = ∑ x ∈ U, (m x * m x - m x) := by
    rw [Finset.sum_congr rfl hpair, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have hoff : (𝒯.offDiag.filter
        (fun TT' : β × β => x ∈ A TT'.1 ∧ x ∈ A TT'.2))
        = (𝒯.filter (fun T => x ∈ A T)).offDiag := by
      ext TT'
      simp only [Finset.mem_filter, Finset.mem_offDiag]
      tauto
    calc (∑ TT' ∈ 𝒯.offDiag, if x ∈ A TT'.1 ∧ x ∈ A TT'.2 then 1 else 0)
        = (𝒯.offDiag.filter
            (fun TT' : β × β => x ∈ A TT'.1 ∧ x ∈ A TT'.2)).card :=
          (Finset.card_filter _ _).symm
    _ = ((𝒯.filter (fun T => x ∈ A T)).offDiag).card := by rw [hoff]
    _ = m x * m x - m x := by
          rw [Finset.offDiag_card]
  -- the multiplicity is positive on U
  have hpos : ∀ x ∈ U, 1 ≤ m x := by
    intro x hx
    obtain ⟨T, hT, hxT⟩ := Finset.mem_biUnion.mp hx
    exact Finset.card_pos.mpr ⟨T, Finset.mem_filter.mpr ⟨hT, hxT⟩⟩
  -- pointwise: 2m ≤ 2 + (m² − m) for m ≥ 1
  have hptw : ∀ x ∈ U, 2 * m x ≤ 2 + (m x * m x - m x) := by
    intro x hx
    have h1 := hpos x hx
    have key : 3 * m x ≤ m x * m x + 2 := by
      rcases Nat.lt_or_ge (m x) 3 with h | h
      · have h12 : m x = 1 ∨ m x = 2 := by omega
        rcases h12 with h' | h' <;> rw [h'] <;> norm_num
      · have h3 : 3 * m x ≤ m x * m x := Nat.mul_le_mul_right _ h
        omega
    have hsq : m x ≤ m x * m x := Nat.le_mul_of_pos_left _ (by omega)
    omega
  -- assemble
  calc 2 * ∑ T ∈ 𝒯, (A T).card = 2 * ∑ x ∈ U, m x := by rw [hswap1]
  _ = ∑ x ∈ U, 2 * m x := by rw [Finset.mul_sum]
  _ ≤ ∑ x ∈ U, (2 + (m x * m x - m x)) := Finset.sum_le_sum hptw
  _ = 2 * U.card + ∑ x ∈ U, (m x * m x - m x) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  _ = 2 * U.card + ∑ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card := by rw [hswap2]

end ArkLib.ProximityGap.PoissonCeilingFloor

#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.two_mul_sum_card_le

namespace ArkLib.ProximityGap.PoissonCeilingFloor

variable {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n]

/-! ## Part B2b-ii: the γ-slice bridge to MCA badness -/

open Classical in
/-- The Poisson union of `(W, U)` pairs: some minimal overdetermined tuple `T`
explains `W` but does not explain `U`. -/
noncomputable def poissonPairUnion (g : ZMod p) (n d : ℕ) :
    Finset ((Fin n → ZMod p) × (Fin n → ZMod p)) :=
  (Finset.powersetCard (d + 2) (Finset.univ : Finset (Fin n))).biUnion
    (fun T => (Finset.univ.filter (fun W : Fin n → ZMod p => ExplainableOn g d W T))
      ×ˢ (Finset.univ.filter (fun U : Fin n → ZMod p => ¬ ExplainableOn g d U T)))

open Classical in
/-- If the second row is not explainable on `S`, then the stack cannot be jointly explained
on `S`, regardless of the first row. -/
theorem not_pairJointAgreesOn_of_not_explainable {d : ℕ} {S : Finset (Fin n)}
    {u₀ u₁ : Fin n → ZMod p} (hnot : ¬ ExplainableOn g d u₁ S) :
    ¬ ProximityGap.pairJointAgreesOn (evalCode g n d) S u₀ u₁ := by
  rintro ⟨v₀, hv₀, v₁, hv₁, hagree⟩
  obtain ⟨q, hqd, hq⟩ := hv₁
  exact hnot ⟨q, hqd, fun i hi => by
    calc u₁ i = v₁ i := (hagree i hi).2.symm
      _ = q.eval (g ^ (i : ℕ)) := hq i⟩

open Classical in
/-- **γ-slice bridge.** If `W` is explainable on `T` but `U` is not, then for the stack
`(W - γU, U)` the scalar `γ` is MCA-bad on witness `T`. -/
theorem mcaEvent_of_explainable_not_explainable {d : ℕ} {δ : ℝ≥0}
    {T : Finset (Fin n)} {W U : Fin n → ZMod p}
    (hTδ : (T.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hW : ExplainableOn g d W T) (hU : ¬ ExplainableOn g d U T) (γ : ZMod p) :
    ProximityGap.mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
      (fun i => W i - γ * U i) U γ := by
  obtain ⟨q, hqd, hq⟩ := hW
  refine ⟨T, hTδ, ?_, ?_⟩
  · refine ⟨fun i : Fin n => q.eval (g ^ (i : ℕ)), ⟨q, hqd, fun _ => rfl⟩, ?_⟩
    intro i hi
    change q.eval (g ^ (i : ℕ)) = W i - γ * U i + γ • U i
    rw [hq i hi, smul_eq_mul]
    ring
  · exact not_pairJointAgreesOn_of_not_explainable (g := g) (d := d)
      (S := T) (u₀ := fun i => W i - γ * U i) hU

open Classical in
/-- Every γ-slice of the Poisson pair union injects into the γ-bad stack set by the shear
`(W, U) ↦ (W - γU, U)`. -/
theorem poissonPairUnion_card_le_badPairs_at_gamma {d : ℕ} {δ : ℝ≥0}
    (hδ : ((d + 2 : ℕ) : ℝ≥0) ≥ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (γ : ZMod p) :
    (poissonPairUnion g n d).card ≤
      (Finset.univ.filter (fun P : (Fin n → ZMod p) × (Fin n → ZMod p) =>
        ProximityGap.mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
          P.1 P.2 γ)).card := by
  classical
  let shear : ((Fin n → ZMod p) × (Fin n → ZMod p)) ≃
      ((Fin n → ZMod p) × (Fin n → ZMod p)) :=
    { toFun := fun P => (fun i => P.1 i - γ * P.2 i, P.2)
      invFun := fun P => (fun i => P.1 i + γ * P.2 i, P.2)
      left_inv := fun P => by
        ext i <;> simp
      right_inv := fun P => by
        ext i <;> simp }
  refine Finset.card_le_card_of_injOn (fun P => shear P) ?_ ?_
  · intro P hP
    obtain ⟨T, hTmem, hPT⟩ := Finset.mem_biUnion.mp hP
    obtain ⟨hW, hU⟩ := Finset.mem_product.mp hPT
    have hTcard : T.card = d + 2 := (Finset.mem_powersetCard.mp hTmem).2
    have hWexp : ExplainableOn g d P.1 T := (Finset.mem_filter.mp hW).2
    have hUnot : ¬ ExplainableOn g d P.2 T := (Finset.mem_filter.mp hU).2
    have hevent : ProximityGap.mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
        (fun i => P.1 i - γ * P.2 i) P.2 γ :=
      mcaEvent_of_explainable_not_explainable (g := g) (T := T)
      (by simpa [hTcard] using hδ) hWexp hUnot γ
    simpa [shear, Finset.mem_filter] using hevent
  · intro P hP Q hQ hPQ
    exact shear.injective hPQ

open Classical in
/-- Summing the γ-slice bridge over all scalars gives the total bad-incidence lower bound
over all stacks. -/
theorem poisson_total_badIncidence_ge_pairUnion {d : ℕ} {δ : ℝ≥0}
    (hδ : ((d + 2 : ℕ) : ℝ≥0) ≥ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) :
    p * (poissonPairUnion g n d).card ≤
      ∑ P : (Fin n → ZMod p) × (Fin n → ZMod p),
        (Finset.univ.filter (fun γ : ZMod p =>
          ProximityGap.mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
            P.1 P.2 γ)).card := by
  classical
  set M := (poissonPairUnion g n d).card with hM
  have hslice : ∀ γ : ZMod p, M ≤
      (Finset.univ.filter (fun P : (Fin n → ZMod p) × (Fin n → ZMod p) =>
        ProximityGap.mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
          P.1 P.2 γ)).card := by
    intro γ
    rw [hM]
    exact poissonPairUnion_card_le_badPairs_at_gamma (g := g) hδ γ
  calc p * M = ∑ _γ : ZMod p, M := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
    _ ≤ ∑ γ : ZMod p,
        (Finset.univ.filter (fun P : (Fin n → ZMod p) × (Fin n → ZMod p) =>
          ProximityGap.mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
            P.1 P.2 γ)).card :=
        Finset.sum_le_sum fun γ _ => hslice γ
    _ = ∑ P : (Fin n → ZMod p) × (Fin n → ZMod p),
        (Finset.univ.filter (fun γ : ZMod p =>
          ProximityGap.mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
            P.1 P.2 γ)).card := by
        simp_rw [Finset.card_filter]
        rw [Finset.sum_comm]

open Classical in
/-- Finite mean-to-sup in the doubled Nat form used by the Poisson floor: if the average of
`2 * f` is at least `C`, then some fiber has `2 * f ≥ C`. -/
theorem exists_two_mul_ge_of_card_mul_le_two_sum {α : Type} [Fintype α] [Nonempty α]
    (C : ℕ) (f : α → ℕ) (hC : 0 < C)
    (h : C * Fintype.card α ≤ 2 * ∑ a, f a) :
    ∃ a, C ≤ 2 * f a := by
  classical
  by_contra hnone
  push Not at hnone
  have hbound : ∀ a, 2 * f a ≤ C - 1 := by
    intro a
    have := hnone a
    omega
  have hsum : 2 * ∑ a, f a ≤ Fintype.card α * (C - 1) := by
    calc 2 * ∑ a, f a = ∑ a, 2 * f a := by rw [Finset.mul_sum]
      _ ≤ ∑ _a : α, (C - 1) := by
          exact Finset.sum_le_sum (s := Finset.univ) fun a _ => hbound a
      _ = Fintype.card α * (C - 1) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hlt : Fintype.card α * (C - 1) < C * Fintype.card α := by
    have hcard : 0 < Fintype.card α := Fintype.card_pos_iff.mpr inferInstance
    calc Fintype.card α * (C - 1) < Fintype.card α * C :=
        (Nat.mul_lt_mul_left hcard).mpr (by omega)
      _ = C * Fintype.card α := by ring
  omega

open Classical in
/-- ENNReal division cancellation for Nat inequalities of the form `C ≤ m * B`. -/
theorem ennreal_natCast_div_mul_le_div_of_le_mul {C B q m : ℕ} (hm0 : m ≠ 0)
    (h : C ≤ m * B) :
    (C : ℝ≥0∞) / ((m : ℝ≥0∞) * (q : ℝ≥0∞))
      ≤ (B : ℝ≥0∞) / (q : ℝ≥0∞) := by
  have hm0E : (m : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hm0
  have hmtop : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top m
  calc
    (C : ℝ≥0∞) / ((m : ℝ≥0∞) * (q : ℝ≥0∞))
        ≤ ((m * B : ℕ) : ℝ≥0∞) / ((m : ℝ≥0∞) * (q : ℝ≥0∞)) := by
          exact ENNReal.div_le_div_right (by exact_mod_cast h) _
    _ = (B : ℝ≥0∞) / (q : ℝ≥0∞) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (ENNReal.mul_div_mul_right (a := (B : ℝ≥0∞)) (b := (q : ℝ≥0∞))
              (c := (m : ℝ≥0∞)) hm0E hmtop)

/-! ## Part B2b-i: the master union count over the `(W, U)`-space -/

open Classical in
/-- **The master count**: under `C + 1 ≤ q` (`C = C(n,d+2)`), the configurations
`(W, U)` with some `(d+2)`-tuple `T` carrying an explanation of `W` and a
non-explanation of `U` number at least `C·q^{2n−1}/2` (stated doubled, ℕ-clean). -/
theorem card_union_ge (hg : orderOf g = n) {d : ℕ} (hdn : d + 2 ≤ n)
    (hq : n.choose (d + 2) + 1 ≤ p) :
    n.choose (d + 2) * p ^ (2 * n - 1)
      ≤ 2 * ((Finset.powersetCard (d + 2) (Finset.univ : Finset (Fin n))).biUnion
          (fun T => (Finset.univ.filter (fun W : Fin n → ZMod p => ExplainableOn g d W T))
            ×ˢ (Finset.univ.filter (fun U : Fin n → ZMod p => ¬ ExplainableOn g d U T)))).card := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set 𝒯 := Finset.powersetCard (d + 2) (Finset.univ : Finset (Fin n)) with h𝒯
  set A : Finset (Fin n) → Finset ((Fin n → ZMod p) × (Fin n → ZMod p)) :=
    fun T => (Finset.univ.filter (fun W : Fin n → ZMod p => ExplainableOn g d W T))
      ×ˢ (Finset.univ.filter (fun U : Fin n → ZMod p => ¬ ExplainableOn g d U T)) with hA
  have hcard𝒯 : 𝒯.card = n.choose (d + 2) := by
    rw [h𝒯, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hmemT : ∀ T ∈ 𝒯, T.card = d + 2 := fun T hT =>
    (Finset.mem_powersetCard.mp hT).2
  have hTne : ∀ T ∈ 𝒯, ∃ i₀, i₀ ∈ T := by
    intro T hT
    have := hmemT T hT
    exact Finset.card_pos.mp (by omega)
  -- the single count
  have hsingle : ∀ T ∈ 𝒯, (A T).card = p ^ (n - 1) * (p ^ n - p ^ (n - 1)) := by
    intro T hT
    obtain ⟨i₀, hi₀⟩ := hTne T hT
    rw [hA]
    rw [Finset.card_product]
    rw [card_explainable_words hg (hmemT T hT) hi₀,
      card_not_explainable_words hg (hmemT T hT) hi₀]
  -- the pair bound
  have hpair : ∀ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card ≤ p ^ (n - 2) * p ^ n := by
    intro TT' hTT'
    obtain ⟨hT1, hT2, hne⟩ := Finset.mem_offDiag.mp hTT'
    have hsub : A TT'.1 ∩ A TT'.2
        ⊆ (Finset.univ.filter (fun W : Fin n → ZMod p =>
            ExplainableOn g d W TT'.1 ∧ ExplainableOn g d W TT'.2)) ×ˢ Finset.univ := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
      rw [hA] at hx1 hx2
      obtain ⟨hW1, _⟩ := Finset.mem_product.mp hx1
      obtain ⟨hW2, _⟩ := Finset.mem_product.mp hx2
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hW1).2, (Finset.mem_filter.mp hW2).2⟩
    calc (A TT'.1 ∩ A TT'.2).card
        ≤ ((Finset.univ.filter (fun W : Fin n → ZMod p =>
            ExplainableOn g d W TT'.1 ∧ ExplainableOn g d W TT'.2)) ×ˢ
            (Finset.univ : Finset (Fin n → ZMod p))).card := Finset.card_le_card hsub
    _ = p ^ (n - 2) * p ^ n := by
        rw [Finset.card_product,
          card_explainable_words_pair hg (hmemT _ hT1) (hmemT _ hT2) hne,
          Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  -- Bonferroni
  have hbonf := two_mul_sum_card_le 𝒯 A
  have hsum1 : (∑ T ∈ 𝒯, (A T).card)
      = n.choose (d + 2) * (p ^ (n - 1) * (p ^ n - p ^ (n - 1))) := by
    rw [Finset.sum_congr rfl hsingle, Finset.sum_const, smul_eq_mul, hcard𝒯]
  have hsum2 : (∑ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card)
      ≤ (n.choose (d + 2) * n.choose (d + 2)) * (p ^ (n - 2) * p ^ n) := by
    calc (∑ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card)
        ≤ ∑ _TT' ∈ 𝒯.offDiag, p ^ (n - 2) * p ^ n := Finset.sum_le_sum hpair
    _ = 𝒯.offDiag.card * (p ^ (n - 2) * p ^ n) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (n.choose (d + 2) * n.choose (d + 2)) * (p ^ (n - 2) * p ^ n) := by
        refine Nat.mul_le_mul_right _ ?_
        rw [Finset.offDiag_card, hcard𝒯]
        omega
  -- power algebra: everything reduces to the atom S = Q²p², Q = p^{n−2}
  have hn2 : 2 ≤ n := by omega
  set C := n.choose (d + 2) with hC
  set Q := p ^ (n - 2) with hQ
  have hppos : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  set S := Q * Q * (p * p) with hS
  have hX : p ^ (2 * n - 1) = S * p := by
    rw [hS, hQ, show p * p = p ^ 2 from (sq p).symm, ← pow_add, ← pow_add, ← pow_succ]
    congr 1
    omega
  have hY : Q * p ^ n = S := by
    rw [hS, hQ, show p * p = p ^ 2 from (sq p).symm, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  have hsingle' : p ^ (n - 1) * (p ^ n - p ^ (n - 1)) = S * p - S := by
    have h1 : p ^ (n - 1) * p ^ n = S * p := by
      rw [hS, hQ, show p * p = p ^ 2 from (sq p).symm, ← pow_add, ← pow_add, ← pow_add,
        ← pow_succ]
      congr 1
      omega
    have h2 : p ^ (n - 1) * p ^ (n - 1) = S := by
      rw [hS, hQ, show p * p = p ^ 2 from (sq p).symm, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega
    rw [Nat.mul_sub, h1, h2]
  -- the factored comparison: (C² + C)·S ≤ C·S·p  from  C + 1 ≤ p
  have hfac : C * C * S + C * S ≤ C * (S * p) := by
    calc C * C * S + C * S = (C * (C + 1)) * S := by ring
    _ ≤ (C * p) * S := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hq)
    _ = C * (S * p) := by ring
  have hbS : C * S ≤ C * (S * p) := by
    calc C * S = C * (S * 1) := by rw [Nat.mul_one]
    _ ≤ C * (S * p) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hppos)
  have hccS : C * S ≤ C * C * S := by
    have hC1 : 1 ≤ C := by
      have := Nat.choose_pos (n := n) (k := d + 2) hdn
      omega
    calc C * S = 1 * (C * S) := (Nat.one_mul _).symm
    _ ≤ C * (C * S) := Nat.mul_le_mul_right _ hC1
    _ = C * C * S := by ring
  -- rewrite the three quantities in S-form
  have hsum1' : 2 * (∑ T ∈ 𝒯, (A T).card) = 2 * (C * (S * p)) - 2 * (C * S) := by
    rw [hsum1, hsingle']
    rw [Nat.mul_sub, Nat.mul_sub]
  have hsum2' : (∑ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card)
      ≤ C * C * S - C * S := by
    calc (∑ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card)
        ≤ 𝒯.offDiag.card * (p ^ (n - 2) * p ^ n) := by
          calc (∑ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card)
              ≤ ∑ _TT' ∈ 𝒯.offDiag, p ^ (n - 2) * p ^ n := Finset.sum_le_sum hpair
          _ = 𝒯.offDiag.card * (p ^ (n - 2) * p ^ n) := by
              rw [Finset.sum_const, smul_eq_mul]
    _ = (C * C - C) * (Q * p ^ n) := by
        rw [Finset.offDiag_card, hcard𝒯, hQ]
    _ = C * C * S - C * S := by
        rw [hY, Nat.sub_mul]
  -- assemble linearly
  have hbonf' := two_mul_sum_card_le 𝒯 A
  rw [hX]
  omega

open Classical in
/-- Named form of `card_union_ge` for the Poisson pair union. -/
theorem poissonPairUnion_card_ge (hg : orderOf g = n) {d : ℕ} (hdn : d + 2 ≤ n)
    (hq : n.choose (d + 2) + 1 ≤ p) :
    n.choose (d + 2) * p ^ (2 * n - 1)
      ≤ 2 * (poissonPairUnion g n d).card := by
  simpa [poissonPairUnion] using card_union_ge (g := g) (n := n) hg hdn hq

open Classical in
/-- **Poisson mean-to-sup payoff.**  Under the Bonferroni range and the radius whose legal
witnesses include `(d+2)`-tuples, some stack has at least half of the Poisson tuple mass as
bad scalars, in doubled Nat form. -/
theorem poisson_exists_stack_two_mul_badCount_ge (hg : orderOf g = n) {d : ℕ} {δ : ℝ≥0}
    (hdn : d + 2 ≤ n) (hq : n.choose (d + 2) + 1 ≤ p)
    (hδ : ((d + 2 : ℕ) : ℝ≥0) ≥ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) :
    ∃ P : (Fin n → ZMod p) × (Fin n → ZMod p),
      n.choose (d + 2) ≤ 2 *
        (Finset.univ.filter (fun γ : ZMod p =>
          ProximityGap.mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
            P.1 P.2 γ)).card := by
  classical
  set C := n.choose (d + 2) with hCdef
  set M := (poissonPairUnion g n d).card with hMdef
  set total := ∑ P : (Fin n → ZMod p) × (Fin n → ZMod p),
        (Finset.univ.filter (fun γ : ZMod p =>
          ProximityGap.mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
            P.1 P.2 γ)).card with htotaldef
  have hCpos : 0 < C := by
    rw [hCdef]
    exact Nat.choose_pos hdn
  have hPairCard :
      Fintype.card ((Fin n → ZMod p) × (Fin n → ZMod p)) = p ^ (2 * n) := by
    rw [Fintype.card_prod]
    simp [Fintype.card_fin, ZMod.card, ← pow_add]
    congr 1
    omega
  have hU : C * p ^ (2 * n - 1) ≤ 2 * M := by
    simpa [hCdef, hMdef] using poissonPairUnion_card_ge (g := g) (n := n) hg hdn hq
  have hI : p * M ≤ total := by
    simpa [hMdef, htotaldef] using poisson_total_badIncidence_ge_pairUnion (g := g) hδ
  have hmain :
      C * Fintype.card ((Fin n → ZMod p) × (Fin n → ZMod p)) ≤ 2 * total := by
    rw [hPairCard]
    have hpow : p * p ^ (2 * n - 1) = p ^ (2 * n) := by
      rw [Nat.mul_comm p (p ^ (2 * n - 1)), ← pow_succ]
      congr 1
      omega
    calc C * p ^ (2 * n) = p * (C * p ^ (2 * n - 1)) := by
          rw [← hpow]
          ring
      _ ≤ p * (2 * M) := Nat.mul_le_mul_left _ hU
      _ = 2 * (p * M) := by ring
      _ ≤ 2 * total := Nat.mul_le_mul_left _ hI
  simpa [hCdef, htotaldef] using
    exists_two_mul_ge_of_card_mul_le_two_sum C
      (fun P : (Fin n → ZMod p) × (Fin n → ZMod p) =>
        (Finset.univ.filter (fun γ : ZMod p =>
          ProximityGap.mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
            P.1 P.2 γ)).card) hCpos hmain

open Classical in
/-- **Poisson `ε_mca` lower payoff.**  The doubled Nat stack bound yields the exact integer
half-mass lower bound `ceil(C(n,d+2)/2) / p` for `ε_mca`. -/
theorem poisson_epsMCA_floor_half_int (hg : orderOf g = n) {d : ℕ} {δ : ℝ≥0}
    (hdn : d + 2 ≤ n) (hq : n.choose (d + 2) + 1 ≤ p)
    (hδ : ((d + 2 : ℕ) : ℝ≥0) ≥ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) :
    ((((n.choose (d + 2) + 1) / 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))
      ≤ ProximityGap.epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n d) δ := by
  classical
  obtain ⟨P, hP⟩ := poisson_exists_stack_two_mul_badCount_ge (g := g) (n := n) hg hdn hq hδ
  set G : Finset (ZMod p) := Finset.univ.filter (fun γ : ZMod p =>
    ProximityGap.mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ P.1 P.2 γ) with hG
  have hceil : (n.choose (d + 2) + 1) / 2 ≤ G.card := by
    rw [hG] at hP
    rw [hG]
    omega
  set u : Code.WordStack (ZMod p) (Fin 2) (Fin n) := ![P.1, P.2] with hu
  have hbad : ∀ γ ∈ G,
      ProximityGap.mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
        (u 0) (u 1) γ := by
    intro γ hγ
    have hγbad : ProximityGap.mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
        P.1 P.2 γ := by
      simpa [hG] using hγ
    simpa [hu] using hγbad
  have hengine := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (F := ZMod p) (A := ZMod p) (C := evalCode g n d) (δ := δ) (u := u) (G := G) hbad
  rw [ZMod.card p] at hengine
  exact le_trans (ENNReal.div_le_div_right (by exact_mod_cast hceil) _) hengine

open Classical in
/-- Literal ENNReal half-mass form of `poisson_epsMCA_floor_half_int`. -/
theorem poisson_epsMCA_floor_half (hg : orderOf g = n) {d : ℕ} {δ : ℝ≥0}
    (hdn : d + 2 ≤ n) (hq : n.choose (d + 2) + 1 ≤ p)
    (hδ : ((d + 2 : ℕ) : ℝ≥0) ≥ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) :
    ((n.choose (d + 2) : ℝ≥0∞) / ((2 : ℝ≥0∞) * (p : ℝ≥0∞)))
      ≤ ProximityGap.epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n d) δ := by
  classical
  have hhalf := poisson_epsMCA_floor_half_int (g := g) (n := n) hg hdn hq hδ
  have hnat : n.choose (d + 2) ≤ 2 * ((n.choose (d + 2) + 1) / 2) := by
    omega
  exact le_trans
    (ennreal_natCast_div_mul_le_div_of_le_mul (q := p) (m := 2) (by norm_num) hnat)
    hhalf

open Classical in
/-- Slackened `/4p` integer form of `poisson_epsMCA_floor_half_int`, matching the constant
usually advertised for the Poisson floor. -/
theorem poisson_epsMCA_floor_quarter_int (hg : orderOf g = n) {d : ℕ} {δ : ℝ≥0}
    (hdn : d + 2 ≤ n) (hq : n.choose (d + 2) + 1 ≤ p)
    (hδ : ((d + 2 : ℕ) : ℝ≥0) ≥ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) :
    (((n.choose (d + 2) / 4 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))
      ≤ ProximityGap.epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n d) δ := by
  classical
  have hhalf := poisson_epsMCA_floor_half_int (g := g) (n := n) hg hdn hq hδ
  exact le_trans
    (ENNReal.div_le_div_right
      (by
        exact_mod_cast (by
          omega : n.choose (d + 2) / 4 ≤ (n.choose (d + 2) + 1) / 2))
      _)
    hhalf

open Classical in
/-- Literal ENNReal `/4p` form of the Poisson floor. -/
theorem poisson_epsMCA_floor_quarter (hg : orderOf g = n) {d : ℕ} {δ : ℝ≥0}
    (hdn : d + 2 ≤ n) (hq : n.choose (d + 2) + 1 ≤ p)
    (hδ : ((d + 2 : ℕ) : ℝ≥0) ≥ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) :
    ((n.choose (d + 2) : ℝ≥0∞) / ((4 : ℝ≥0∞) * (p : ℝ≥0∞)))
      ≤ ProximityGap.epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n d) δ := by
  classical
  have hhalf := poisson_epsMCA_floor_half_int (g := g) (n := n) hg hdn hq hδ
  have hnat : n.choose (d + 2) ≤ 4 * ((n.choose (d + 2) + 1) / 2) := by
    omega
  exact le_trans
    (ennreal_natCast_div_mul_le_div_of_le_mul (q := p) (m := 4) (by norm_num) hnat)
    hhalf

open Classical in
/-- `δ*` upper bracket from the Poisson half-mass floor. -/
theorem poisson_mcaDeltaStar_le_floor_half_int (hg : orderOf g = n) {d : ℕ} {δ : ℝ≥0}
    (hdn : d + 2 ≤ n) (hq : n.choose (d + 2) + 1 ≤ p)
    (hδ : ((d + 2 : ℕ) : ℝ≥0) ≥ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (εstar : ℝ≥0∞)
    (hεstar : εstar < ((((n.choose (d + 2) + 1) / 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g n d) εstar ≤ δ :=
  ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hεstar (poisson_epsMCA_floor_half_int (g := g) (n := n) hg hdn hq hδ))

open Classical in
/-- `δ*` upper bracket from the literal Poisson half-mass floor. -/
theorem poisson_mcaDeltaStar_le_floor_half (hg : orderOf g = n) {d : ℕ} {δ : ℝ≥0}
    (hdn : d + 2 ≤ n) (hq : n.choose (d + 2) + 1 ≤ p)
    (hδ : ((d + 2 : ℕ) : ℝ≥0) ≥ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (εstar : ℝ≥0∞)
    (hεstar : εstar < ((n.choose (d + 2) : ℝ≥0∞) / ((2 : ℝ≥0∞) * (p : ℝ≥0∞)))) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g n d) εstar ≤ δ :=
  ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hεstar (poisson_epsMCA_floor_half (g := g) (n := n) hg hdn hq hδ))

open Classical in
/-- `δ*` upper bracket from the slackened Poisson `/4p` floor. -/
theorem poisson_mcaDeltaStar_le_floor_quarter_int (hg : orderOf g = n) {d : ℕ} {δ : ℝ≥0}
    (hdn : d + 2 ≤ n) (hq : n.choose (d + 2) + 1 ≤ p)
    (hδ : ((d + 2 : ℕ) : ℝ≥0) ≥ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (εstar : ℝ≥0∞)
    (hεstar : εstar < (((n.choose (d + 2) / 4 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g n d) εstar ≤ δ :=
  ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hεstar (poisson_epsMCA_floor_quarter_int (g := g) (n := n)
      hg hdn hq hδ))

open Classical in
/-- `δ*` upper bracket from the literal Poisson `/4p` floor. -/
theorem poisson_mcaDeltaStar_le_floor_quarter (hg : orderOf g = n) {d : ℕ} {δ : ℝ≥0}
    (hdn : d + 2 ≤ n) (hq : n.choose (d + 2) + 1 ≤ p)
    (hδ : ((d + 2 : ℕ) : ℝ≥0) ≥ (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (εstar : ℝ≥0∞)
    (hεstar : εstar < ((n.choose (d + 2) : ℝ≥0∞) / ((4 : ℝ≥0∞) * (p : ℝ≥0∞)))) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g n d) εstar ≤ δ :=
  ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hεstar (poisson_epsMCA_floor_quarter (g := g) (n := n)
      hg hdn hq hδ))

end ArkLib.ProximityGap.PoissonCeilingFloor

#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.not_pairJointAgreesOn_of_not_explainable
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.mcaEvent_of_explainable_not_explainable
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.poissonPairUnion_card_le_badPairs_at_gamma
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.poisson_total_badIncidence_ge_pairUnion
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.exists_two_mul_ge_of_card_mul_le_two_sum
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.ennreal_natCast_div_mul_le_div_of_le_mul
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.card_union_ge
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.poissonPairUnion_card_ge
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.poisson_exists_stack_two_mul_badCount_ge
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.poisson_epsMCA_floor_half_int
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.poisson_epsMCA_floor_half
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.poisson_epsMCA_floor_quarter_int
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.poisson_epsMCA_floor_quarter
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.poisson_mcaDeltaStar_le_floor_half_int
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.poisson_mcaDeltaStar_le_floor_half
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.poisson_mcaDeltaStar_le_floor_quarter_int
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.poisson_mcaDeltaStar_le_floor_quarter
