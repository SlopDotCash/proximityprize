/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CaptureKernelUD
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CurveCapture

/-!
# `L`-ary K4 on the unique-decoding window: the depth-0 curve pinning

The pair depth-0 K4 (`Hab25CaptureKernelUD.lean`) solved a `2×2` system through two cell
members and forced the rest by root counting on the triple witness intersection. At
general arity the same architecture runs through **Lagrange interpolation in the scalar
variable**: `L` distinct cell scalars determine the curve tuple
`a_j := ∑_t (ℓ_t).coeff j · P(ν t)` (the `ℓ_t` are the Lagrange basis polynomials at the
chosen nodes `ν`), the curve identity `∑_j C(γʲ)·a_j = ∑_t C(ℓ_t(γ))·P(ν t)` plus the
monomial reproduction `∑_t ℓ_t(γ)·(ν t)ʲ = γʲ` make the curve match the fold on the
`(L+1)`-fold witness intersection, and the window `L·n + k ≤ (L+1)·⌈(1−δ)n⌉` makes that
intersection larger than the degree:

* `sum_card_le_inf_card_add` — the iterated intersection bound;
* `lagrangeCurve` machinery — the tuple, its degree bound, the curve identity, the
  monomial reproduction;
* **`exists_curve_tuple_of_decode_family_window`** — depth-0 K4 at arity `L` (mirrors
  `exists_pencil_of_decode_family_window`);
* `cell_card_le_of_curve_decode_family_window` — with the `L`-ary Claim-1 dichotomy:
  every decoded cell obeys `|Ecell| ≤ T` for `T ≥ n·(L−1)`, no pinning hypothesis left;
* `badScalarsCurve_card_le_of_window` — the unconditional `L`-ary bad-scalar count on
  the window: every `L`-row stack has `≤ n·(L−1)` bad scalars.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Finset
open _root_.ProximityGap Code
open scoped NNReal

attribute [local instance] Classical.propDecidable

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-! ## The iterated intersection bound -/

/-- Iterated inclusion–exclusion: `∑_{t∈s} |Sf t| + |Sγ| ≤ |s.inf Sf ∩ Sγ| + |s|·n`. -/
lemma sum_card_le_inf_card_add {L : ℕ} (Sf : Fin L → Finset ι₀) (Sγ : Finset ι₀)
    (s : Finset (Fin L)) :
    (∑ t ∈ s, (Sf t).card) + Sγ.card ≤
      (s.inf Sf ∩ Sγ).card + s.card * Fintype.card ι₀ := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    simp [Finset.top_eq_univ, Finset.univ_inter]
  | cons a s ha ih =>
    rw [Finset.inf_cons, Finset.sum_cons, Finset.card_cons]
    have hassoc : (Sf a ⊓ s.inf Sf) ∩ Sγ = Sf a ∩ (s.inf Sf ∩ Sγ) := by
      rw [Finset.inf_eq_inter, Finset.inter_assoc]
    rw [hassoc]
    have h1 := Finset.card_union_add_card_inter (Sf a) (s.inf Sf ∩ Sγ)
    have h2 : (Sf a ∪ (s.inf Sf ∩ Sγ)).card ≤ Fintype.card ι₀ := by
      refine le_trans (Finset.card_le_card (Finset.subset_univ _)) ?_
      exact le_of_eq Finset.card_univ
    nlinarith [ih]

/-! ## The Lagrange curve tuple -/

/-- The witness-set size floor of a curve decode (mirrors `McaDecode.floor_le_card`). -/
theorem McaDecodeCurve.floor_le_card {n L : ℕ} [NeZero n] {domain : Fin n ↪ F₀} {k : ℕ}
    {δ : ℝ≥0} {u : WordStack F₀ (Fin L) (Fin n)} {γ : F₀}
    (d : McaDecodeCurve domain k δ u γ) :
    ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ ≤ d.S.card := by
  refine Nat.ceil_le.mpr ?_
  exact_mod_cast d.hcard

/-- The Lagrange curve tuple through the values `V` at the nodes `ν`:
`a_j = ∑_t (ℓ_t).coeff j · V t`. -/
noncomputable def lagrangeCurve {L : ℕ} (ν : Fin L → F₀) (V : Fin L → F₀[X])
    (j : Fin L) : F₀[X] :=
  ∑ t : Fin L, Polynomial.C ((Lagrange.basis Finset.univ ν t).coeff (j : ℕ)) * V t

/-- Degree bound: each tuple entry inherits the value degrees. -/
lemma lagrangeCurve_natDegree_lt {L k : ℕ} (hk : 0 < k) (ν : Fin L → F₀)
    {V : Fin L → F₀[X]} (hV : ∀ t, (V t).natDegree < k) (j : Fin L) :
    (lagrangeCurve ν V j).natDegree < k := by
  have hle : (lagrangeCurve ν V j).natDegree ≤ k - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun t _ => ?_
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    exact Nat.le_sub_one_of_lt (hV t)
  omega

/-- **The curve identity**: `∑_j C(γʲ)·a_j = ∑_t C(ℓ_t(γ))·V t`. -/
lemma lagrangeCurve_eval {L : ℕ} (ν : Fin L → F₀) (hν : Function.Injective ν)
    (V : Fin L → F₀[X]) (γ : F₀) :
    ∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) * lagrangeCurve ν V j =
      ∑ t : Fin L, Polynomial.C ((Lagrange.basis Finset.univ ν t).eval γ) * V t := by
  unfold lagrangeCurve
  calc ∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) *
        ∑ t : Fin L, Polynomial.C ((Lagrange.basis Finset.univ ν t).coeff (j : ℕ)) * V t
      = ∑ j : Fin L, ∑ t : Fin L,
          Polynomial.C (γ ^ (j : ℕ) *
            (Lagrange.basis Finset.univ ν t).coeff (j : ℕ)) * V t := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← mul_assoc, ← Polynomial.C_mul]
    _ = ∑ t : Fin L, ∑ j : Fin L,
          Polynomial.C (γ ^ (j : ℕ) *
            (Lagrange.basis Finset.univ ν t).coeff (j : ℕ)) * V t := Finset.sum_comm
    _ = ∑ t : Fin L, Polynomial.C ((Lagrange.basis Finset.univ ν t).eval γ) * V t := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← Finset.sum_mul, ← map_sum Polynomial.C]
        congr 2
        have hdeg : (Lagrange.basis Finset.univ ν t).natDegree < L := by
          have h := Lagrange.natDegree_basis
            (Set.injOn_of_injective hν) (Finset.mem_univ t)
          rw [Finset.card_univ, Fintype.card_fin] at h
          have hL : 0 < L := t.pos
          omega
        rw [Polynomial.eval_eq_sum_range' hdeg γ]
        rw [← Fin.sum_univ_eq_sum_range
          (fun j => (Lagrange.basis Finset.univ ν t).coeff j * γ ^ j) L]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **Monomial reproduction**: `∑_t ℓ_t(γ)·(ν t)ʲ = γʲ` for `j : Fin L`. -/
lemma lagrange_monomial_reproduction {L : ℕ} (ν : Fin L → F₀)
    (hν : Function.Injective ν) (γ : F₀) (j : Fin L) :
    ∑ t : Fin L, (Lagrange.basis Finset.univ ν t).eval γ * ν t ^ (j : ℕ) =
      γ ^ (j : ℕ) := by
  have hinj : Set.InjOn ν (Finset.univ : Finset (Fin L)) := Set.injOn_of_injective hν
  have hdeg : ((Polynomial.X : F₀[X]) ^ (j : ℕ)).degree <
      ((Finset.univ : Finset (Fin L)).card : ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    refine lt_of_le_of_lt (Polynomial.degree_X_pow_le _) ?_
    exact_mod_cast j.isLt
  have h := Lagrange.eq_interpolate (f := (Polynomial.X : F₀[X]) ^ (j : ℕ)) hinj hdeg
  have heval := congrArg (Polynomial.eval γ) h
  rw [Lagrange.interpolate_apply, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_finset_sum] at heval
  refine Eq.trans (Finset.sum_congr rfl fun t _ => ?_) heval.symm
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

/-! ## Depth-0 K4 at arity `L` -/

/-- **`L`-ary K4 on the unique-decoding window, antecedent-free** (mirrors
`exists_pencil_of_decode_family_window`): on `L·n + k ≤ (L+1)·⌈(1−δ)n⌉`, any decode
family on a cell with at least `L` scalars is pinned to one polynomial curve. -/
theorem exists_curve_tuple_of_decode_family_window {n L : ℕ} [NeZero n]
    {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin L) (Fin n)} (hk : 0 < k) (Ecell : Finset F₀)
    (P : F₀ → F₀[X])
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ)
    (hwin : L * Fintype.card (Fin n) + k ≤
      (L + 1) * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊)
    (hL : L ≤ Ecell.card) :
    ∃ a : Fin L → F₀[X], (∀ j, (a j).natDegree < k) ∧
      ∀ γ ∈ Ecell, P γ = ∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) * a j := by
  classical
  set t₀ : ℕ := ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ with ht₀
  -- choose `L` distinct nodes in the cell
  obtain ⟨s, hsub, hcard⟩ := Finset.exists_subset_card_eq hL
  set ι : Fin L ≃ {x // x ∈ s} :=
    (Fin.castOrderIso hcard.symm).toEquiv.trans s.equivFin.symm with hι
  set ν : Fin L → F₀ := fun t => (ι t : F₀) with hνdef
  have hνinj : Function.Injective ν := fun t₁ t₂ h => ι.injective (Subtype.ext h)
  have hνmem : ∀ t, ν t ∈ Ecell := fun t => hsub (ι t).2
  -- the node decodes and the Lagrange curve tuple through them
  have hnode : ∀ t : Fin L, ∃ d : McaDecodeCurve domain k δ u (ν t), d.P = P (ν t) :=
    fun t => hdec (ν t) (hνmem t)
  choose dν hdν using hnode
  set V : Fin L → F₀[X] := fun t => P (ν t) with hV
  have hVdeg : ∀ t, (V t).natDegree < k := by
    intro t
    have h := (dν t).hdeg
    rw [hdν t] at h
    exact natDegree_lt_of_degree_lt_of_pos hk h
  refine ⟨lagrangeCurve ν V, lagrangeCurve_natDegree_lt hk ν hVdeg, ?_⟩
  -- every cell member is forced onto the curve
  intro γ hγ
  obtain ⟨d, hd⟩ := hdec γ hγ
  set W : Finset (Fin n) :=
    ((Finset.univ : Finset (Fin L)).inf fun t => (dν t).S) ∩ d.S with hW
  -- the `(L+1)`-fold intersection is large
  have hWcard : k ≤ W.card := by
    have hsumle := sum_card_le_inf_card_add (fun t => (dν t).S) d.S Finset.univ
    rw [Finset.card_univ, Fintype.card_fin, ← hW] at hsumle
    have hfloorγ : t₀ ≤ d.S.card := d.floor_le_card
    have hsumge : L * t₀ ≤ ∑ t : Fin L, (dν t).S.card := by
      have h := Finset.card_nsmul_le_sum Finset.univ
        (fun t : Fin L => (dν t).S.card) t₀ (fun t _ => (dν t).floor_le_card)
      rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
      exact h
    have hexp : (L + 1) * t₀ = L * t₀ + t₀ := by ring
    omega
  -- the curve matches the fold on the intersection
  have hvan : ∀ i ∈ W,
      (P γ - ∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) * lagrangeCurve ν V j).eval
        (domain i) = 0 := by
    intro i hi
    obtain ⟨hiinf, hiγ⟩ := Finset.mem_inter.mp hi
    -- node agreements at `i`
    have hPt : ∀ t : Fin L, (V t).eval (domain i) =
        ∑ j : Fin L, ν t ^ (j : ℕ) * u j i := by
      intro t
      have hmem : i ∈ (dν t).S := by
        have hle : (Finset.univ : Finset (Fin L)).inf (fun t => (dν t).S) ≤ (dν t).S :=
          Finset.inf_le (Finset.mem_univ t)
        exact hle hiinf
      have h := (dν t).hagree i hmem
      rw [hdν t] at h
      rw [hV]
      simpa [smul_eq_mul] using h
    -- the curve evaluates to the fold at `γ`
    have hcurve : (∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) *
        lagrangeCurve ν V j).eval (domain i) = ∑ j : Fin L, γ ^ (j : ℕ) * u j i := by
      rw [lagrangeCurve_eval ν hνinj V γ, Polynomial.eval_finset_sum]
      calc ∑ t : Fin L,
            (Polynomial.C ((Lagrange.basis Finset.univ ν t).eval γ) * V t).eval
              (domain i)
          = ∑ t : Fin L, (Lagrange.basis Finset.univ ν t).eval γ *
              ∑ j : Fin L, ν t ^ (j : ℕ) * u j i := by
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [Polynomial.eval_mul, Polynomial.eval_C, hPt t]
        _ = ∑ t : Fin L, ∑ j : Fin L,
              ((Lagrange.basis Finset.univ ν t).eval γ * ν t ^ (j : ℕ)) * u j i := by
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
        _ = ∑ j : Fin L, ∑ t : Fin L,
              ((Lagrange.basis Finset.univ ν t).eval γ * ν t ^ (j : ℕ)) * u j i :=
            Finset.sum_comm
        _ = ∑ j : Fin L, γ ^ (j : ℕ) * u j i := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← Finset.sum_mul, lagrange_monomial_reproduction ν hνinj γ j]
    -- the decode at `γ` matches the fold at `γ`
    have hPγ : (P γ).eval (domain i) = ∑ j : Fin L, γ ^ (j : ℕ) * u j i := by
      have h := d.hagree i hiγ
      rw [hd] at h
      simpa [smul_eq_mul] using h
    rw [Polynomial.eval_sub, hPγ, hcurve, sub_self]
  -- root counting closes
  have hdegg : (P γ - ∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) *
      lagrangeCurve ν V j).degree < k := by
    rcases eq_or_ne (P γ - ∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) *
        lagrangeCurve ν V j) 0 with hz | hz
    · rw [hz, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe k
    · rw [← Polynomial.natDegree_lt_iff_degree_lt hz]
      refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt ?_ ?_)
      · exact natDegree_lt_of_degree_lt_of_pos hk (hd ▸ d.hdeg)
      · have hle : (∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) *
            lagrangeCurve ν V j).natDegree ≤ k - 1 := by
          refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
          refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
          exact Nat.le_sub_one_of_lt (lagrangeCurve_natDegree_lt hk ν hVdeg j)
        omega
  have hzero := eq_zero_of_degree_lt_of_vanishes_on (domain := domain) hdegg W
    hWcard hvan
  exact sub_eq_zero.mp hzero

/-- **The cell bound from K1 alone, on the window** (mirrors
`cell_card_le_of_decode_family_window`): any `L`-ary decoded cell obeys `|Ecell| ≤ T`
for any threshold `T ≥ n·(L−1)`, with no pinning hypothesis left. -/
theorem cell_card_le_of_curve_decode_family_window {n L : ℕ} [NeZero n]
    {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin L) (Fin n)} (hk : 0 < k) (Ecell : Finset F₀) (T : ℕ)
    (P : F₀ → F₀[X])
    (hn : Fintype.card (Fin n) * (L - 1) ≤ T)
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ)
    (hwin : L * Fintype.card (Fin n) + k ≤
      (L + 1) * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊) :
    Ecell.card ≤ T := by
  refine cell_card_le_of_curve_decode_family_pinning Ecell T P hn hdec ?_
  intro hT
  have hL : L ≤ Ecell.card := by
    have hn1 : 1 ≤ Fintype.card (Fin n) := Fintype.card_pos
    have h1 : L - 1 ≤ Fintype.card (Fin n) * (L - 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  exact exists_curve_tuple_of_decode_family_window hk Ecell P hdec hwin hL

/-- **The unconditional `L`-ary bad-scalar count on the window** (mirrors
`badScalars_card_le_of_window`): every `L`-row word stack has at most `n·(L−1)` bad
scalars of `mcaEventCurve` — the whole bad set is one decoded cell, and depth-0 `L`-ary
K4 + the `L`-ary Claim-1 dichotomy bound it. -/
theorem badScalarsCurve_card_le_of_window {n L : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    {k : ℕ} (δ : ℝ≥0) (u : WordStack F₀ (Fin L) (Fin n)) (hk : 0 < k)
    (hwin : L * Fintype.card (Fin n) + k ≤
      (L + 1) * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊) :
    (Finset.univ.filter (fun γ : F₀ =>
      _root_.ProximityGap.mcaEventCurve
        ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ u γ)).card ≤
      Fintype.card (Fin n) * (L - 1) := by
  classical
  set bad : Finset F₀ := Finset.univ.filter (fun γ : F₀ =>
    _root_.ProximityGap.mcaEventCurve
      ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ u γ) with hbad
  have hex : ∀ γ : F₀, ∃ p : F₀[X],
      γ ∈ bad → ∃ d : McaDecodeCurve domain k δ u γ, d.P = p := by
    intro γ
    by_cases hγ : γ ∈ bad
    · obtain ⟨d⟩ := exists_mcaDecodeCurve_of_mcaEventCurve (Finset.mem_filter.mp hγ).2
      exact ⟨d.P, fun _ => ⟨d, rfl⟩⟩
    · exact ⟨0, fun h => absurd h hγ⟩
  choose P hPdec using hex
  exact cell_card_le_of_curve_decode_family_window hk bad
    (Fintype.card (Fin n) * (L - 1)) P le_rfl (fun γ hγ => hPdec γ hγ) hwin

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms lagrangeCurve_eval
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms lagrange_monomial_reproduction
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_curve_tuple_of_decode_family_window
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms cell_card_le_of_curve_decode_family_window
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms badScalarsCurve_card_le_of_window
