/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Round 9 (Issue #232, ABF26) — roots of unity have MINIMAL additive energy (characteristic 0).

`SubgroupGaussSumFourthMoment` reduced the deep-interior proximity question to the **additive energy**
`E(G) = #{(y₁,y₂,y₃,y₄)∈G⁴ : y₁+y₂ = y₃+y₄}` of the smooth (roots-of-unity) subgroup. This file proves
the structural fact that, **in characteristic 0**, that energy is *minimal* — `E(S) ≤ 3|S|²` for any
finite set `S` on the complex unit circle (in particular the `n`-th roots of unity):

> `unitCircle_reps_le_two`: for `s ≠ 0`, the number of representations `#{y∈S : s−y∈S}` of `s` as an
> ordered sum of two unit-circle points is **at most 2**, and
> `unitCircle_additiveEnergy_le`: hence `∑_{a,b∈S} #{y∈S : (a+b)−y∈S} ≤ 3·|S|²`.

The mechanism is the classical "two unit vectors with a given sum are determined" fact, made algebraic:
a unit-circle point `y` with `s−y` also on the circle satisfies the **quadratic**
`conj(s)·y² − (s·conj s)·y + s = 0` (from `y·conj y = 1` and `(s−y)·conj(s−y) = 1`), and a nonzero
quadratic has `≤ 2` roots. Minimal additive energy `E(S)=Θ(|S|²)` is exactly maximal *anti-concentration*
of the subset-sum count — the regime in which the §7/averaging attack is *defeated*.

**Honest scope.** This is the **characteristic-0** statement: the complex `n`-th roots of unity resist
the attack by having minimal additive energy. The Proximity Prize lives over a *finite field* `F_q`,
where the additive energy of the `2^k`-subgroup is the genuinely *open* sum-product quantity (a
multiplicative subgroup of `F_q^×` can have large additive energy depending on `|G|` vs `q`). So this
result proves the smooth domain is "good" in the char-0 model and pins the finite-field gap precisely as
a sum-product/additive-energy bound. All `sorry`-free and axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

set_option linter.style.longLine false


open Polynomial Finset
open Complex (I)
open scoped ComplexConjugate

namespace ArkLib.ProximityGap.RootsOfUnityAdditiveEnergy

/-- **A nonzero sum has at most two representations on the unit circle.** For `s ≠ 0` and a finite set
`S ⊆ {z : ℂ | z·conj z = 1}` (the unit circle), the number of `y∈S` with `s−y∈S` is at most `2`.
The map `y ↦ (y, s−y)` exhibits these as roots of the fixed quadratic
`conj(s)·X² − (s·conj s)·X + s`, which has `≤ 2` roots. -/
theorem unitCircle_reps_le_two (s : ℂ) (hs : s ≠ 0) (S : Finset ℂ)
    (hunit : ∀ y ∈ S, y * conj y = 1) :
    (S.filter (fun y => s - y ∈ S)).card ≤ 2 := by
  classical
  set P : ℂ[X] := C (conj s) * X ^ 2 - C (s * conj s) * X + C s with hP
  -- `P ≠ 0` (its `X²`-coefficient is `conj s ≠ 0`)
  have hcs : conj s ≠ 0 := by simpa using hs
  have hP0 : P ≠ 0 := by
    intro h
    have hc2 : P.coeff 2 = conj s := by
      simp [hP, coeff_C, coeff_X_pow, coeff_C_mul]
    rw [h] at hc2; simp at hc2; exact hcs hc2.symm
  have hdeg : P.natDegree ≤ 2 := by
    rw [hP]; compute_degree
  -- every filtered `y` is a root of `P`
  have hsub : (S.filter (fun y => s - y ∈ S)) ⊆ P.roots.toFinset := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨hyS, hsyS⟩ := hy
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def]
    have hy1 : y * conj y = 1 := hunit y hyS
    have hsy1 : (s - y) * conj (s - y) = 1 := hunit (s - y) hsyS
    rw [map_sub] at hsy1
    have hrel : s * conj s - s * conj y - y * conj s = 0 := by
      have hexp : (s - y) * (conj s - conj y)
          = s * conj s - s * conj y - y * conj s + y * conj y := by ring
      rw [hexp, hy1] at hsy1
      linear_combination hsy1
    rw [hP]
    simp only [eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    linear_combination (-y) * hrel + (-s) * hy1
  calc (S.filter (fun y => s - y ∈ S)).card
      ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ 2 := hdeg

/-- The number of representations of `0` is at most `|S|` (the map `y ↦ −y` is injective). -/
theorem unitCircle_reps_zero_le (S : Finset ℂ) :
    (S.filter (fun y => (0 : ℂ) - y ∈ S)).card ≤ S.card :=
  le_trans (Finset.card_filter_le _ _) le_rfl

/-- **Roots of unity have minimal additive energy: `E(S) ≤ 3|S|²` (characteristic 0).** For any finite
`S` on the unit circle, the additive energy `∑_{a,b∈S} #{y∈S : (a+b)−y∈S}` is at most `3·|S|²`: each
inner representation count is `≤ |S|`, and for `a+b ≠ 0` it is `≤ 2`; the diagonal `a+b=0` contributes
`≤ |S|` ordered pairs each counting `≤ |S|`, the rest `≤ |S|²` pairs each counting `≤ 2`. -/
theorem unitCircle_additiveEnergy_le (S : Finset ℂ) (hunit : ∀ y ∈ S, y * conj y = 1) :
    ∑ a ∈ S, ∑ b ∈ S, (S.filter (fun y => (a + b) - y ∈ S)).card ≤ 3 * S.card ^ 2 := by
  classical
  -- Bound each inner count by `if a+b = 0 then |S| else 2`.
  have hbound : ∀ a ∈ S, ∀ b ∈ S,
      (S.filter (fun y => (a + b) - y ∈ S)).card ≤ (if a + b = 0 then S.card else 2) := by
    intro a _ b _
    by_cases h0 : a + b = 0
    · rw [if_pos h0]; exact Finset.card_filter_le _ _
    · rw [if_neg h0]; exact unitCircle_reps_le_two (a + b) h0 S hunit
  calc ∑ a ∈ S, ∑ b ∈ S, (S.filter (fun y => (a + b) - y ∈ S)).card
      ≤ ∑ a ∈ S, ∑ b ∈ S, (if a + b = 0 then S.card else 2) := by
        refine Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hbound a ha b hb))
    _ ≤ ∑ a ∈ S, (S.card + 2 * S.card) := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        -- for fixed `a`: at most one `b` (namely `b = -a`) has `a+b=0`, contributing `≤ |S|`;
        -- the rest contribute `2` each, over `≤ |S|` terms.
        calc ∑ b ∈ S, (if a + b = 0 then S.card else 2)
            ≤ ∑ b ∈ S, (if a + b = 0 then S.card else 0)
              + ∑ b ∈ S, (if a + b = 0 then 0 else 2) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_le_sum (fun b _ => ?_)
              by_cases h : a + b = 0 <;> simp [h]
          _ ≤ S.card + 2 * S.card := by
              gcongr
              · -- `∑_b (if a+b=0 then |S| else 0) ≤ |S|`: at most one `b` qualifies
                calc ∑ b ∈ S, (if a + b = 0 then S.card else 0)
                    ≤ ∑ b ∈ S, (if b = -a then S.card else 0) := by
                      refine Finset.sum_le_sum (fun b _ => ?_)
                      by_cases h : a + b = 0
                      · have hba : b = -a := by linear_combination h
                        simp [h, hba]
                      · simp [h]
                  _ ≤ S.card := by
                      rw [Finset.sum_ite_eq' S (-a) (fun _ => S.card)]
                      split <;> simp
              · -- `∑_b (if a+b=0 then 0 else 2) ≤ 2|S|`
                calc ∑ b ∈ S, (if a + b = 0 then 0 else 2)
                    ≤ ∑ _b ∈ S, 2 := by
                      refine Finset.sum_le_sum (fun b _ => ?_)
                      by_cases h : a + b = 0 <;> simp [h]
                  _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul]; ring
    _ = 3 * S.card ^ 2 := by
        rw [Finset.sum_const, smul_eq_mul]; ring

end ArkLib.ProximityGap.RootsOfUnityAdditiveEnergy

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.RootsOfUnityAdditiveEnergy.unitCircle_reps_le_two
#print axioms ArkLib.ProximityGap.RootsOfUnityAdditiveEnergy.unitCircle_additiveEnergy_le
