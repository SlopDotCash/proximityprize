/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallIntersection

/-!
# CS25 #82, deliverable 2: weight-invariance of the ball-intersection count

The joint `δ`-cover count `I(e) := jointCoverCount δ 0 e = |B(0,δ) ∩ B(e,δ)|` depends **only on the
Hamming weight of `e`**, not on `e` itself.  This is the keystone that turns the second-moment
off-diagonal sum into the classical *weight-enumerator* form

  `∑_{e ∈ C} I(e) = ∑_d A_d · I_d`,   `A_d = #{e ∈ C : wt(e) = d}`,   `I_d = I(weight-d rep)`,

complementing the list-size route (`CS25SecondMomentListSize`) and feeding the MDS weight enumerator
`A_d` bounds (`RSWeightEnumerator`).

## Why it is true

Over a field, two vectors of equal Hamming weight are related by a **monomial transformation**: a
coordinate permutation `σ` followed by per-coordinate scaling by nonzero scalars `c i`.  Such a map
is a Hamming isometry (`hammingDist_monomial`), and it fixes `0`, so it carries `B(0,δ) ∩ B(e,δ)`
bijectively onto `B(0,δ) ∩ B(e',δ)` whenever it carries `e` to `e'`.

## Main results

* `hammingDist_monomial` / `relHammingDist_monomial` — monomial maps are Hamming isometries.
* `exists_monomial_of_hammingNorm_eq` — equal-weight vectors are monomially related.
* `jointCoverCount_monomial` — the ball-intersection count is monomial-invariant.
* `jointCoverCount_weight_invariant` — **`I(e)` depends only on `wt(e)`**.
* `sum_jointCoverCount_weight_fiber` — a fixed-weight fiber of a code contributes `A_d · I_d`.
-/

set_option linter.style.longLine false


open scoped BigOperators ENNReal NNReal

namespace ArkLib.CS25

open Code Finset

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [Field F]

/-- **Monomial invariance of Hamming distance.** Reindexing both arguments by a permutation `σ`
and scaling each coordinate by a nonzero `c i` preserves Hamming distance. -/
theorem hammingDist_monomial (σ : Equiv.Perm ι) (c : ι → F) (hc : ∀ i, c i ≠ 0)
    (w u : ι → F) :
    hammingDist (fun i => c i * w (σ.symm i)) (fun i => c i * u (σ.symm i))
      = hammingDist w u := by
  classical
  unfold hammingDist
  refine Finset.card_bij' (fun i _ => σ.symm i) (fun j _ => σ j) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact fun h => hi (by rw [h])
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    simpa [mul_right_inj' (hc (σ j))] using hj
  · intro i _; simp
  · intro j _; simp

/-- Relative-distance form of `hammingDist_monomial`. -/
theorem relHammingDist_monomial (σ : Equiv.Perm ι) (c : ι → F) (hc : ∀ i, c i ≠ 0)
    (w u : ι → F) :
    relHammingDist (fun i => c i * w (σ.symm i)) (fun i => c i * u (σ.symm i))
      = relHammingDist w u := by
  unfold relHammingDist
  rw [hammingDist_monomial σ c hc]

/-- The membership-mapping property of `Equiv.subtypeCongr`: it sends `{x // p x}` onto
`{x // q x}` (and complements to complements). -/
theorem subtypeCongr_prop {α : Type*} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (e : {x // p x} ≃ {x // q x}) (f : {x // ¬ p x} ≃ {x // ¬ q x}) (a : α) :
    q (Equiv.subtypeCongr e f a) ↔ p a := by
  by_cases ha : p a
  · have hsymm : (Equiv.sumCompl p).symm a = Sum.inl ⟨a, ha⟩ :=
      (Equiv.symm_apply_eq _).2 (by rw [Equiv.sumCompl_apply_inl])
    have : Equiv.subtypeCongr e f a = ↑(e ⟨a, ha⟩) := by
      simp only [Equiv.subtypeCongr, Equiv.trans_apply, hsymm, Equiv.sumCongr_apply,
        Sum.map_inl, Equiv.sumCompl_apply_inl]
    rw [this]; exact iff_of_true (e ⟨a, ha⟩).property ha
  · have hsymm : (Equiv.sumCompl p).symm a = Sum.inr ⟨a, ha⟩ :=
      (Equiv.symm_apply_eq _).2 (by rw [Equiv.sumCompl_apply_inr])
    have : Equiv.subtypeCongr e f a = ↑(f ⟨a, ha⟩) := by
      simp only [Equiv.subtypeCongr, Equiv.trans_apply, hsymm, Equiv.sumCongr_apply,
        Sum.map_inr, Equiv.sumCompl_apply_inr]
    rw [this]; exact iff_of_false (f ⟨a, ha⟩).property ha

/-- **Equal-weight vectors are monomially related.** If `e, e'` have the same Hamming norm, there is
a coordinate permutation `σ` and a nonzero scaling `c` with `c i · e (σ⁻¹ i) = e' i`. -/
theorem exists_monomial_of_hammingNorm_eq (e e' : ι → F) (hwt : hammingNorm e = hammingNorm e') :
    ∃ (σ : Equiv.Perm ι) (c : ι → F), (∀ i, c i ≠ 0) ∧
      (fun i => c i * e (σ.symm i)) = e' := by
  classical
  have hsupp : Fintype.card {x // e x ≠ 0} = Fintype.card {x // e' x ≠ 0} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]; exact hwt
  have hcompl : Fintype.card {x // ¬ e x ≠ 0} = Fintype.card {x // ¬ e' x ≠ 0} := by
    have h1 := Fintype.card_subtype_compl (fun x => e x ≠ 0)
    have h2 := Fintype.card_subtype_compl (fun x => e' x ≠ 0)
    rw [h1, h2, hsupp]
  let eOn := Fintype.equivOfCardEq hsupp
  let eOff := Fintype.equivOfCardEq hcompl
  let σ : Equiv.Perm ι := Equiv.subtypeCongr eOn eOff
  have hkey : ∀ i, (e' i ≠ 0) ↔ (e (σ.symm i) ≠ 0) := by
    intro i
    have := subtypeCongr_prop eOn eOff (σ.symm i)
    rwa [Equiv.apply_symm_apply] at this
  refine ⟨σ, fun i => if e' i ≠ 0 then e' i * (e (σ.symm i))⁻¹ else 1, ?_, ?_⟩
  · intro i
    change (if e' i ≠ 0 then e' i * (e (σ.symm i))⁻¹ else 1) ≠ 0
    by_cases h : e' i ≠ 0
    · rw [if_pos h]; exact mul_ne_zero h (inv_ne_zero ((hkey i).mp h))
    · rw [if_neg h]; exact one_ne_zero
  · funext i
    by_cases h : e' i ≠ 0
    · change (if e' i ≠ 0 then e' i * (e (σ.symm i))⁻¹ else 1) * e (σ.symm i) = e' i
      rw [if_pos h, mul_assoc, inv_mul_cancel₀ ((hkey i).mp h), mul_one]
    · change (if e' i ≠ 0 then e' i * (e (σ.symm i))⁻¹ else 1) * e (σ.symm i) = e' i
      rw [if_neg h, one_mul]
      have he0 : e (σ.symm i) = 0 := not_not.mp (fun hc => h ((hkey i).mpr hc))
      rw [he0, not_not.mp h]

/-- The monomial map `w ↦ (i ↦ c i · w (σ⁻¹ i))` packaged as an `Equiv` of `ι → F`. -/
def monomialEquiv (σ : Equiv.Perm ι) (c : ι → F) (hc : ∀ i, c i ≠ 0) : (ι → F) ≃ (ι → F) :=
  (Equiv.piCongrLeft' (fun _ => F) σ).trans
    (Equiv.piCongrRight (fun i => Equiv.mulLeft₀ (c i) (hc i)))

@[simp] theorem monomialEquiv_apply (σ : Equiv.Perm ι) (c : ι → F) (hc : ∀ i, c i ≠ 0)
    (w : ι → F) : monomialEquiv σ c hc w = fun i => c i * w (σ.symm i) := by
  funext i; simp [monomialEquiv, Equiv.piCongrLeft', Equiv.piCongrRight, Equiv.mulLeft₀]

/-- **Monomial invariance of the ball-intersection count.** A coordinate permutation `σ` together
with nonzero per-coordinate scalings `c` is a Hamming isometry, so it preserves the joint
`δ`-cover count of any two centers. -/
theorem jointCoverCount_monomial (δ : ℝ≥0) (σ : Equiv.Perm ι) (c : ι → F) (hc : ∀ i, c i ≠ 0)
    (a b : ι → F) :
    jointCoverCount δ (fun i => c i * a (σ.symm i)) (fun i => c i * b (σ.symm i))
      = jointCoverCount δ a b := by
  classical
  set T := monomialEquiv σ c hc with hT
  unfold jointCoverCount
  refine Finset.card_bij' (fun v _ => T.symm v) (fun w _ => T w) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    have hTv : T (T.symm v) = v := T.apply_symm_apply v
    have e1 : relHammingDist (T.symm v) a = relHammingDist v (fun i => c i * a (σ.symm i)) := by
      have := relHammingDist_monomial σ c hc (T.symm v) a
      rw [show (fun i => c i * (T.symm v) (σ.symm i)) = T (T.symm v) from
        (monomialEquiv_apply σ c hc (T.symm v)).symm, hTv] at this
      exact this.symm
    have e2 : relHammingDist (T.symm v) b = relHammingDist v (fun i => c i * b (σ.symm i)) := by
      have := relHammingDist_monomial σ c hc (T.symm v) b
      rw [show (fun i => c i * (T.symm v) (σ.symm i)) = T (T.symm v) from
        (monomialEquiv_apply σ c hc (T.symm v)).symm, hTv] at this
      exact this.symm
    rw [e1, e2]; exact ⟨hv.1, hv.2⟩
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    have e1 : relHammingDist (T w) (fun i => c i * a (σ.symm i)) = relHammingDist w a := by
      rw [show T w = (fun i => c i * w (σ.symm i)) from monomialEquiv_apply σ c hc w]
      exact relHammingDist_monomial σ c hc w a
    have e2 : relHammingDist (T w) (fun i => c i * b (σ.symm i)) = relHammingDist w b := by
      rw [show T w = (fun i => c i * w (σ.symm i)) from monomialEquiv_apply σ c hc w]
      exact relHammingDist_monomial σ c hc w b
    rw [e1, e2]; exact ⟨hw.1, hw.2⟩
  · intro v _; exact T.apply_symm_apply v
  · intro w _; exact T.symm_apply_apply w

/-- **Weight-invariance of the ball-intersection count (`I(e)` depends only on `wt(e)`).**
If `e` and `e'` have the same Hamming norm, then `B(0,δ) ∩ B(e,δ)` and `B(0,δ) ∩ B(e',δ)` have equal
cardinality.  This is the keystone for the weight-enumerator form of the second moment. -/
theorem jointCoverCount_weight_invariant (δ : ℝ≥0) (e e' : ι → F)
    (hwt : hammingNorm e = hammingNorm e') :
    jointCoverCount δ 0 e = jointCoverCount δ 0 e' := by
  obtain ⟨σ, c, hc, hTe⟩ := exists_monomial_of_hammingNorm_eq e e' hwt
  have h0 : (0 : ι → F) = fun i => c i * (0 : ι → F) (σ.symm i) := by funext i; simp
  calc jointCoverCount δ 0 e
      = jointCoverCount δ (fun i => c i * (0 : ι → F) (σ.symm i))
          (fun i => c i * e (σ.symm i)) := (jointCoverCount_monomial δ σ c hc 0 e).symm
    _ = jointCoverCount δ 0 e' := by rw [← h0, hTe]

/-- **Weight-fiber collapse.** A fixed-weight fiber `{e ∈ C : wt(e) = d}` of a code contributes
`A_d · I_d` to `∑_{e ∈ C} I(e)`, where `A_d` is the fiber cardinality and `I_d = I(e₀)` is the common
intersection count of any weight-`d` representative `e₀`.  This is the per-weight term of the
classical weight-enumerator expansion of the CS25 second moment. -/
theorem sum_jointCoverCount_weight_fiber (C : Finset (ι → F)) (δ : ℝ≥0) (d : ℕ) (e₀ : ι → F)
    (he₀ : hammingNorm e₀ = d) :
    ∑ e ∈ C.filter (fun e => hammingNorm e = d), jointCoverCount δ 0 e
      = (C.filter (fun e => hammingNorm e = d)).card * jointCoverCount δ 0 e₀ := by
  classical
  have hconst : ∀ e ∈ C.filter (fun e => hammingNorm e = d),
      jointCoverCount δ 0 e = jointCoverCount δ 0 e₀ := by
    intro e he
    rw [Finset.mem_filter] at he
    exact jointCoverCount_weight_invariant δ e e₀ (by rw [he.2, he₀])
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]

/-- **Weight-enumerator form of the second-moment sum.** For a code `C` with a choice of weight-`d`
representative `rep d` for each occurring weight, the total ball-intersection splits as the
weight-enumerator sum `∑_d A_d · I_d`, with `A_d = #{e ∈ C : wt(e) = d}` and `I_d = I(rep d)`.

This is the classical weight-enumerator route to the CS25 second moment: combined with the MDS
weight-enumerator bound `A_d ≤ C(n,d) q^{d-(n-k)}` (`RSWeightEnumerator.card_evalWeight_le`) and any
per-weight ball-intersection bound `I_d ≤ g(d)`, it bounds `E[N²]` off-diagonal directly. -/
theorem sum_jointCoverCount_eq_weight_enumerator (C : Finset (ι → F)) (δ : ℝ≥0)
    (rep : ℕ → (ι → F)) (hrep : ∀ d ∈ C.image hammingNorm, hammingNorm (rep d) = d) :
    ∑ e ∈ C, jointCoverCount δ 0 e
      = ∑ d ∈ C.image hammingNorm,
          (C.filter (fun e => hammingNorm e = d)).card * jointCoverCount δ 0 (rep d) := by
  classical
  rw [show (∑ e ∈ C, jointCoverCount δ 0 e)
        = ∑ d ∈ C.image hammingNorm,
            ∑ e ∈ C.filter (fun e => hammingNorm e = d), jointCoverCount δ 0 e
      from (Finset.sum_fiberwise_of_maps_to (fun e he => Finset.mem_image_of_mem _ he) _).symm]
  exact Finset.sum_congr rfl
    (fun d hd => sum_jointCoverCount_weight_fiber C δ d (rep d) (hrep d hd))

end ArkLib.CS25
