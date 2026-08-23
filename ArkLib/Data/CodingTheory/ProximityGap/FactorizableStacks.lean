/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SplittingLadder

/-!
# Factorizable stacks: the splitting mechanism beyond monomials, and the fiber
# reach–count tradeoff

First formal brick of the `MonomialDomination` structure programme (#357). The
splitting-ladder events live on monomial pairs; this file shows the *mechanism* is a
property of the **factorizable class** — stacks of the form `(dom·f, f)` for an
arbitrary row `f` — and that within this class the tradeoff between *reach* (how deep
in radius the events go) and *count* (how many scalars are bad) is governed entirely by
`f`'s **fiber structure**:

* `factorizable_mcaEvent` — for any `f`, any fiber `f⁻¹(c)` with `≥ a − 1` points
  (`a ≥ k + 1`, `k ≥ 2`), and any crossing point `x₀` outside the fiber:
  `γ = −dom x₀` is MCA-bad for the stack `(dom·f, f)` at agreement `a`. The line is
  `f(x)·(x + γ)`: on the fiber it is the affine codeword `c·(X + γ)`, at the crossing
  it vanishes (as does the explanation), and the row `f` — constant on `≥ k` points yet
  different at the crossing — defeats every joint explanation (`lowdeg_const_fail`).
* `factorizable_eps_ge` — the counted floor: `c` distinct crossings against (possibly
  different) big fibers give `ε_mca(C, 1 − a/n) ≥ c/|F|`.

**The tradeoff law this formalizes:** at agreement `a`, the mechanism's yield for `f`
with fiber sizes `φ₁ ≥ φ₂ ≥ …` is `n − φ₁` if `φ₂ < a − 1 ≤ φ₁` and `n` if
`φ₂ ≥ a − 1`; reach is `a ≤ φ₂ + 1` for the full-`n` yield. The half-pair (`f = x^m`,
two fibers of size `m`) simultaneously maximizes reach (`m + 1` — the UDR) and count
(`n`) — **the monomial member dominates the factorizable class within this mechanism**,
the first provable instance of the domination phenomenon on a class that is not itself
monomial. (Matching upper bounds for the class — the converse — remain with the main
`MonomialDomination` surface.)

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- Issue #357 (the domination programme); `SplittingLadder.lean` (the monomial
  specialization), `CosetSplittingFloor.lean` (`lowdeg_const_fail`).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.FactorizableStacks

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code Polynomial
open ProximityGap.CensusConditionalPin
open ProximityGap.CensusLowerBound
open ProximityGap.CosetSplittingFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} (dom : Fin n → F) (f : Fin n → F)

/-- **The factorizable splitting event.** For any row `f`, a fiber of value `c` with
`≥ a − 1` points, and a crossing point `x₀` outside it with the fiber value `c` itself
explainable budget-wise (`k ≥ 2`, `a ≥ k + 1`): the scalar `−dom x₀` is MCA-bad for
the stack `(dom·f, f)` at agreement `a`. -/
theorem factorizable_mcaEvent [Nonempty (Fin n)] (hinj : Function.Injective dom)
    (hk : 2 ≤ k) {a : ℕ} (hka : k + 1 ≤ a) (han : a ≤ n)
    (c : F) (Fib : Finset (Fin n)) (hFib : ∀ i ∈ Fib, f i = c)
    (hFcard : a - 1 ≤ Fib.card)
    (x₀ : Fin n) (hx₀ : x₀ ∉ Fib) (hx₀val : f x₀ ≠ c) :
    mcaEvent (F := F) (A := F) (evalCode dom k : Set (Fin n → F))
      (1 - (a : ℝ≥0) / (Fintype.card (Fin n) : ℝ≥0))
      (fun i => dom i * f i) f (-(dom x₀)) := by
  classical
  obtain ⟨T₀, hT₀sub, hT₀card⟩ := Finset.exists_subset_card_eq hFcard
  have hx₀T₀ : x₀ ∉ T₀ := fun hx => hx₀ (hT₀sub hx)
  set T : Finset (Fin n) := insert x₀ T₀ with hT
  have hTcard : T.card = a := by
    rw [hT, Finset.card_insert_of_notMem hx₀T₀, hT₀card]
    omega
  set lam : F := -(dom x₀) with hlam
  -- the explanation: c·(X + λ), degree ≤ 1 < k
  have hexpl_mem : (fun i => c * (dom i + lam)) ∈
      (evalCode dom k : Set (Fin n → F)) := by
    refine (mem_evalCode _).mpr ⟨C c * (X + C lam), ?_, fun i => ?_⟩
    · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      refine le_trans (Polynomial.natDegree_add_le _ _) ?_
      rw [Polynomial.natDegree_X, Polynomial.natDegree_C]
      omega
    · simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_X]
  rw [mcaEvent_agree_iff, agreeOf_grid Fintype.card_ne_zero
    (by rw [Fintype.card_fin]; omega)]
  refine ⟨T, by rw [hTcard], ⟨fun i => c * (dom i + lam), hexpl_mem, fun i hi => ?_⟩,
    ?_⟩
  · -- agreement on T: line = f(x)(x + λ)
    rw [smul_eq_mul]
    rw [hT, Finset.mem_insert] at hi
    rcases hi with hix | hi
    · -- the crossing: both sides vanish
      subst hix
      rw [hlam]
      ring
    · -- a fiber point: f = c
      have hic : f i = c := hFib i (hT₀sub hi)
      rw [hic]
      ring
  · -- no joint explanation: the row f is constant c on T₀ (≥ k points) but ≠ c at x₀
    rintro ⟨w₀, _, w₁, hw₁, hag⟩
    obtain ⟨q', hq', hw₁'⟩ := (mem_evalCode w₁).mp hw₁
    refine lowdeg_const_fail (d := k - 1) (c := c) (y := f x₀)
      (P := T₀.image dom) (x₀ := dom x₀) hq' ?_ ?_ ?_ hx₀val
    · rw [Finset.card_image_of_injective _ hinj, hT₀card]
      omega
    · intro x hx
      obtain ⟨i, hiT₀, rfl⟩ := Finset.mem_image.mp hx
      have hiT : i ∈ T := by
        rw [hT]
        exact Finset.mem_insert_of_mem hiT₀
      have hagi : w₁ i = f i := (hag i hiT).2
      rw [← hw₁' i, hagi, hFib i (hT₀sub hiT₀)]
    · have hx₀T : x₀ ∈ T := by
        rw [hT]
        exact Finset.mem_insert_self _ _
      have hagx : w₁ x₀ = f x₀ := (hag x₀ hx₀T).2
      rw [← hw₁' x₀, hagx]

open Classical in
/-- **The counted factorizable floor:** `c` distinct crossing points, each against a
(possibly different) `≥ a − 1`-point fiber not containing it, give
`ε_mca(C, 1 − a/n) ≥ c/|F|`. The half-pair instantiation (two fibers of size `m`,
every domain point a crossing against the opposite fiber) recovers the ladder's
`n/|F|`. -/
theorem factorizable_eps_ge [Nonempty (Fin n)] (hinj : Function.Injective dom)
    (hk : 2 ≤ k) {a : ℕ} (hka : k + 1 ≤ a) (han : a ≤ n)
    {cnum : ℕ} (xs : Fin cnum → Fin n) (hxs : Function.Injective xs)
    (cs : Fin cnum → F) (Fibs : Fin cnum → Finset (Fin n))
    (hFib : ∀ j, ∀ i ∈ Fibs j, f i = cs j)
    (hFcard : ∀ j, a - 1 ≤ (Fibs j).card)
    (hx : ∀ j, xs j ∉ Fibs j) (hxval : ∀ j, f (xs j) ≠ cs j) :
    ((cnum : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F) (evalCode dom k : Set (Fin n → F))
          (1 - (a : ℝ≥0) / (Fintype.card (Fin n) : ℝ≥0)) := by
  refine le_trans ?_ (mcaEvent_prob_le_epsMCA (F := F) (A := F) _ _
    ![fun i => dom i * f i, f])
  have h0 : (![fun i => dom i * f i, f] : WordStack F (Fin 2) (Fin n)) 0
      = fun i => dom i * f i := rfl
  have h1 : (![fun i => dom i * f i, f] : WordStack F (Fin 2) (Fin n)) 1 = f := rfl
  rw [h0, h1, prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  have hsub : Finset.univ.image (fun j : Fin cnum => -(dom (xs j))) ⊆ Finset.filter
      (fun lam : F => mcaEvent (F := F) (A := F)
        (evalCode dom k : Set (Fin n → F))
        (1 - (a : ℝ≥0) / (Fintype.card (Fin n) : ℝ≥0))
        (fun i => dom i * f i) f lam) Finset.univ := by
    intro lam hlam
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hlam
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      factorizable_mcaEvent dom f hinj hk hka han (cs j) (Fibs j) (hFib j)
        (hFcard j) (xs j) (hx j) (hxval j)⟩
  have himg : (Finset.univ.image (fun j : Fin cnum => -(dom (xs j)))).card = cnum := by
    rw [Finset.card_image_of_injective _ (fun u v huv => hxs (hinj
      (neg_injective huv))), Finset.card_univ, Fintype.card_fin]
  gcongr
  calc (cnum : ℕ)
      = (Finset.univ.image (fun j : Fin cnum => -(dom (xs j)))).card := himg.symm
    _ ≤ _ := Finset.card_le_card hsub

/-! ## Source audit -/

#print axioms factorizable_mcaEvent
#print axioms factorizable_eps_ge

end ProximityGap.FactorizableStacks
