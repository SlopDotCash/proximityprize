/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CurveCellProduction

/-!
# The `L`-ary Claim-1 capture assembly: `CurveCaptured` and the dichotomy at `(L−1)·n`

The pair lane (`Hab25AffineCapture.lean` + `Hab25Claim1.lean`) closes the Claim-1
dichotomy through the improvement count: a captured cell's scalars are roots of nonzero
*affine* functionals at disagreement coordinates — at most `1` root each, so at most `n`
scalars. This file is the general-arity mirror: the curve functional
`g_x(Z) = ∑ⱼ dⱼ(x)·Zʲ` has degree `≤ L−1`, so each disagreement coordinate accounts for at
most `L−1` scalars, and the dichotomy closes at threshold `n·(L−1)`:

* `CurveCaptured` — the `L`-ary capture predicate (the polynomial curve
  `∑ⱼ C(γʲ)·aⱼ` matches the fold `∑ⱼ γʲ·uⱼ` on a large witness set, no stack joint
  agreement) — mirrors `AffineCaptured`;
* `gapPoly` machinery — the per-coordinate gap polynomial, its degree bound, nonvanishing
  on the disagreement set, and evaluation identity;
* `curve_endgame_count` — the `(L−1)`-roots fibration: any set of improving scalars has
  `≤ n·(L−1)` members — mirrors `hab25_endgame_count ∘ factorImprove_card_le_n`;
* `curveCaptured_improve` — capture with codeword-degree rows yields an improvement
  coordinate — mirrors `affineCaptured_improve`;
* **`claim1_dichotomy_curve`** — the `L`-ary Claim-1 dichotomy: a uniformly captured cell
  has `≤ T` members for any `T ≥ n·(L−1)` — mirrors `claim1_dichotomy`;
* `cell_card_le_of_curve_decode_family_pinning` — the K4-input seam at arity `L`: a
  decoded cell whose family is pinned to one polynomial curve obeys the size bound —
  mirrors `cell_card_le_of_decode_family_pinning`.

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

/-! ## The per-coordinate gap polynomial -/

/-- The `L`-ary disagreement set: coordinates where some row differs. -/
noncomputable def disagreeSetCurve {L : ℕ} (d : Fin L → ι₀ → F₀) : Finset ι₀ :=
  Finset.univ.filter (fun x => ∃ j, d j x ≠ 0)

/-- The `L`-ary gap functional `∑ⱼ zʲ·dⱼ(x)`. -/
def curveGap {L : ℕ} (d : Fin L → ι₀ → F₀) (z : F₀) (x : ι₀) : F₀ :=
  ∑ j : Fin L, z ^ (j : ℕ) * d j x

/-- The per-coordinate gap polynomial `∑ⱼ C(dⱼ(x))·Xʲ`. -/
noncomputable def gapPoly {L : ℕ} (d : Fin L → ι₀ → F₀) (x : ι₀) : F₀[X] :=
  ∑ j : Fin L, Polynomial.C (d j x) * Polynomial.X ^ (j : ℕ)

lemma gapPoly_natDegree_le {L : ℕ} (d : Fin L → ι₀ → F₀) (x : ι₀) :
    (gapPoly d x).natDegree ≤ L - 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  refine le_trans (Polynomial.natDegree_X_pow_le _) ?_
  omega

lemma gapPoly_coeff {L : ℕ} (d : Fin L → ι₀ → F₀) (x : ι₀) (j₀ : Fin L) :
    (gapPoly d x).coeff (j₀ : ℕ) = d j₀ x := by
  unfold gapPoly
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single j₀]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hne
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun hc => hne (Fin.ext hc.symm)), mul_zero]
  · intro habs
    exact absurd (Finset.mem_univ _) habs

lemma gapPoly_ne_zero {L : ℕ} {d : Fin L → ι₀ → F₀} {x : ι₀}
    (hx : x ∈ disagreeSetCurve d) : gapPoly d x ≠ 0 := by
  obtain ⟨-, j, hj⟩ := Finset.mem_filter.mp hx
  intro h0
  apply hj
  have := gapPoly_coeff d x j
  rw [h0, Polynomial.coeff_zero] at this
  exact this.symm

lemma gapPoly_eval {L : ℕ} (d : Fin L → ι₀ → F₀) (x : ι₀) (z : F₀) :
    (gapPoly d x).eval z = curveGap d z x := by
  unfold gapPoly curveGap
  rw [Polynomial.eval_finset_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      mul_comm]

/-! ## The `(L−1)`-roots improvement count -/

/-- **The `L`-ary endgame count.** Any set of scalars, each a root of the gap functional
at some disagreement coordinate, has at most `n·(L−1)` members: each coordinate's gap
polynomial is nonzero of degree `≤ L−1`, hence has `≤ L−1` roots. -/
theorem curve_endgame_count {L : ℕ} (d : Fin L → ι₀ → F₀) (T : Finset F₀)
    (hT : ∀ z ∈ T, ∃ x ∈ disagreeSetCurve d, curveGap d z x = 0) :
    T.card ≤ Fintype.card ι₀ * (L - 1) := by
  classical
  -- the coordinate choice, totalized
  have hex : ∀ z : F₀, ∃ x : ι₀,
      z ∈ T → x ∈ disagreeSetCurve d ∧ curveGap d z x = 0 := by
    intro z
    by_cases hz : z ∈ T
    · obtain ⟨x, hx, hg⟩ := hT z hz
      exact ⟨x, fun _ => ⟨hx, hg⟩⟩
    · exact ⟨Classical.arbitrary ι₀, fun h => absurd h hz⟩
  choose xf hxf using hex
  -- fibration over the disagreement coordinates
  have hcover : T ⊆ (disagreeSetCurve d).biUnion
      (fun x => T.filter (fun z => xf z = x)) := by
    intro z hz
    exact Finset.mem_biUnion.mpr
      ⟨xf z, (hxf z hz).1, Finset.mem_filter.mpr ⟨hz, rfl⟩⟩
  -- each fiber injects into the roots of the gap polynomial
  have hfiber : ∀ x ∈ disagreeSetCurve d,
      (T.filter (fun z => xf z = x)).card ≤ L - 1 := by
    intro x hx
    have hsub : T.filter (fun z => xf z = x) ⊆ (gapPoly d x).roots.toFinset := by
      intro z hz
      obtain ⟨hzT, hzx⟩ := Finset.mem_filter.mp hz
      have hg : curveGap d z x = 0 := hzx ▸ (hxf z hzT).2
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (gapPoly_ne_zero hx)]
      rw [Polynomial.IsRoot, gapPoly_eval]
      exact hg
    calc (T.filter (fun z => xf z = x)).card
        ≤ (gapPoly d x).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (gapPoly d x).roots := Multiset.toFinset_card_le _
      _ ≤ (gapPoly d x).natDegree := Polynomial.card_roots' _
      _ ≤ L - 1 := gapPoly_natDegree_le d x
  calc T.card
      ≤ ((disagreeSetCurve d).biUnion
          (fun x => T.filter (fun z => xf z = x))).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ x ∈ disagreeSetCurve d, (T.filter (fun z => xf z = x)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ disagreeSetCurve d, (L - 1) := Finset.sum_le_sum hfiber
    _ = (disagreeSetCurve d).card * (L - 1) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ Fintype.card ι₀ * (L - 1) := by
        refine Nat.mul_le_mul_right _ ?_
        refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
        exact le_of_eq Finset.card_univ

/-! ## The `L`-ary capture predicate and the improvement lemma -/

/-- **The `L`-ary capture predicate** (mirrors `AffineCaptured`): the polynomial curve
`∑ⱼ C(γʲ)·aⱼ` matches the fold `∑ⱼ γʲ·uⱼ` on a large witness set, with no stack joint
agreement. -/
def CurveCaptured {L : ℕ} (domain : ι₀ ↪ F₀) (k : ℕ) (δ : ℝ≥0)
    (u : WordStack F₀ (Fin L) ι₀) (γ : F₀) (a : Fin L → F₀[X]) : Prop :=
  ∃ S : Finset ι₀, ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι₀) ∧
    (∀ i ∈ S, (∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) * a j).eval (domain i) =
      ∑ j : Fin L, γ ^ (j : ℕ) • u j i) ∧
    ¬ _root_.ProximityGap.stackJointAgreesOn
      ((ReedSolomon.code domain k : Set (ι₀ → F₀))) S u

/-- **The `L`-ary improvement lemma** (mirrors `affineCaptured_improve`): capture with
codeword-degree rows yields a disagreement coordinate where the gap functional vanishes. -/
theorem curveCaptured_improve {L : ℕ} {domain : ι₀ ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin L) ι₀} {γ : F₀} {a : Fin L → F₀[X]}
    (hdeg : ∀ j, (a j).natDegree < k)
    (hcap : CurveCaptured domain k δ u γ a) :
    ∃ x ∈ disagreeSetCurve (fun j i => (a j).eval (domain i) - u j i),
      curveGap (fun j i => (a j).eval (domain i) - u j i) γ x = 0 := by
  classical
  obtain ⟨S, _hScard, hagree, hnjp⟩ := hcap
  -- the rows are Reed–Solomon codewords
  have hv : ∀ j, (fun i => (a j).eval (domain i)) ∈
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) := fun j =>
    ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval (a j) (hdeg j) fun i => rfl
  -- forbidden joint agreement ⇒ a disagreeing row at some witness coordinate
  have hdis : ¬ ∀ i ∈ S, ∀ j, (a j).eval (domain i) = u j i := by
    intro hall
    exact hnjp ⟨fun j i => (a j).eval (domain i), hv, fun i hi j => hall i hi j⟩
  push Not at hdis
  obtain ⟨x, hxS, j₀, hj₀⟩ := hdis
  refine ⟨x, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨j₀, sub_ne_zero_of_ne hj₀⟩⟩
  · -- the fold agreement at `x` makes the gap vanish
    have h := hagree x hxS
    rw [Polynomial.eval_finset_sum] at h
    unfold curveGap
    have hexp : ∀ j : Fin L,
        γ ^ (j : ℕ) * ((a j).eval (domain x) - u j x) =
        (Polynomial.C (γ ^ (j : ℕ)) * a j).eval (domain x) - γ ^ (j : ℕ) • u j x := by
      intro j
      rw [Polynomial.eval_mul, Polynomial.eval_C, smul_eq_mul]
      ring
    calc ∑ j : Fin L, γ ^ (j : ℕ) * ((a j).eval (domain x) - u j x)
        = ∑ j : Fin L, ((Polynomial.C (γ ^ (j : ℕ)) * a j).eval (domain x) -
            γ ^ (j : ℕ) • u j x) := Finset.sum_congr rfl fun j _ => hexp j
      _ = (∑ j : Fin L, (Polynomial.C (γ ^ (j : ℕ)) * a j).eval (domain x)) -
            ∑ j : Fin L, γ ^ (j : ℕ) • u j x := by rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [h, sub_self]

/-! ## The `L`-ary Claim-1 dichotomy and the K4 seam -/

/-- **The `L`-ary Claim-1 dichotomy** (mirrors `claim1_dichotomy`): a cell whose scalars
are uniformly captured by one polynomial curve has at most `T` members, for any threshold
`T ≥ n·(L−1)`. -/
theorem claim1_dichotomy_curve {L : ℕ} (domain : ι₀ ↪ F₀) (k : ℕ) (δ : ℝ≥0)
    (u : WordStack F₀ (Fin L) ι₀) (Ecell : Finset F₀) (T : ℕ)
    (hn : Fintype.card ι₀ * (L - 1) ≤ T)
    (hsteps57 : T < Ecell.card →
      ∃ a : Fin L → F₀[X], (∀ j, (a j).natDegree < k) ∧
        ∀ γ ∈ Ecell, CurveCaptured domain k δ u γ a) :
    Ecell.card ≤ T := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨a, hdeg, hcap⟩ := hsteps57 hcon
  have himprove : ∀ γ ∈ Ecell,
      ∃ x ∈ disagreeSetCurve (fun j i => (a j).eval (domain i) - u j i),
        curveGap (fun j i => (a j).eval (domain i) - u j i) γ x = 0 := fun γ hγ =>
    curveCaptured_improve hdeg (hcap γ hγ)
  have hcount := curve_endgame_count
    (fun j i => (a j).eval (domain i) - u j i) Ecell himprove
  omega

/-- **The K4-input seam at arity `L`** (mirrors `cell_card_le_of_decode_family_pinning`):
a decoded cell whose family is pinned past the threshold to one polynomial curve obeys
the size bound, for any `T ≥ n·(L−1)`. -/
theorem cell_card_le_of_curve_decode_family_pinning {n L : ℕ} [NeZero n]
    {domain : Fin n ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin L) (Fin n)} (Ecell : Finset F₀) (T : ℕ)
    (P : F₀ → F₀[X])
    (hn : Fintype.card (Fin n) * (L - 1) ≤ T)
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecodeCurve domain k δ u γ, d.P = P γ)
    (hpin : T < Ecell.card →
      ∃ a : Fin L → F₀[X], (∀ j, (a j).natDegree < k) ∧
        ∀ γ ∈ Ecell, P γ = ∑ j : Fin L, Polynomial.C (γ ^ (j : ℕ)) * a j) :
    Ecell.card ≤ T := by
  classical
  refine claim1_dichotomy_curve domain k δ u Ecell T hn ?_
  intro hT
  obtain ⟨a, hdeg, hPa⟩ := hpin hT
  refine ⟨a, hdeg, ?_⟩
  intro γ hγ
  obtain ⟨d, hd⟩ := hdec γ hγ
  refine ⟨d.S, d.hcard, ?_, d.hnjp⟩
  intro i hi
  rw [← hPa γ hγ, ← hd]
  exact d.hagree i hi

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms curve_endgame_count
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms curveCaptured_improve
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms claim1_dichotomy_curve
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms cell_card_le_of_curve_decode_family_pinning
