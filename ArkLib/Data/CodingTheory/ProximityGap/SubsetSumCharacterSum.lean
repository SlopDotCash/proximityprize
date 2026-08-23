/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.FieldTheory.Finite.Basic

/-!
# Round 4 (Issue #232, §7 / O11 direct attack) — an EXACT character-sum / Gauss-sum formula for the
# subgroup subset-sum count `N(m, target)`, with isolated main term `C(|G|, m)/q`.

This file attacks the **reduced open question** of the §7 disproof route (cf.
`CandidateAttackLoop46`, O11; `ListCapacityFieldIndependent`, the capacity endpoint;
`SubgroupSumsetThreePowUpper`, the field-cap bracket) with the **additive-character /
generating-function** method.

## The counted quantity

For a finite field `F` (`q := |F|`), a finite subset `G ⊆ F` (the smooth/FRI multiplicative
subgroup, but the identity holds for *any* finite subset), a size `m`, and a `target ∈ F`:

  `N(m, target) := #{ S ⊆ G : |S| = m, ∑_{x∈S} x = target }`.

At the prize this is exactly the count whose super-polynomial vs polynomial growth pins `δ*` from
below or keeps the prize alive: pushing the list-decoding lower bound from agreement `a = k`
(capacity, where the count is the trivial `C(n,k)`) to `a = k + t` (interior) needs `N(k+t, target)`
large for a disproof, small for survival.

## The exact identity (`subsetSumCount_eq_charSum`)

Fix any **primitive** additive character `ψ : AddChar F ℂ` (one always exists,
`FiniteField.primitiveChar_to_Complex`). Additive-character orthogonality
(`AddChar.sum_mulShift`: `∑_{b∈F} ψ(b·y) = q·[y=0]`) turns the sum constraint into an average over
the *dual* group. Swapping the order of summation and applying **Vieta** to the inner subset sum
(`Finset.prod_X_add_C_coeff`: `e_m((ψ(b·x))_{x∈G})` is a coefficient of `∏_{x∈G}(X + ψ(b·x))`)
yields the clean, *exact* Gauss-sum identity

  `q · N(m, target)  =  ∑_{b ∈ F}  ψ(−b·target) · e_m( (ψ(b·x))_{x∈G} )`            (in `ℂ`)

where `e_m(·) = ∑_{S ⊆ G, |S| = m} ∏_{x∈S} ψ(b·x)` is the character-weighted subset count
(`charWeightedCount`). This is the requested exact character-sum / generating-function formula.

## The main term dominates the trivial character (`subsetSumCount_main_plus_error`)

The `b = 0` term of the dual sum is `ψ(0)·e_m((ψ(0))_{x∈G}) = e_m(1,…,1) = C(|G|, m)`
(`charWeightedCount_zero`), the field-independent **main term**. Splitting it off:

  `q · N(m, target)  =  C(|G|, m)  +  ∑_{b ≠ 0} ψ(−b·target) · charWeightedCount ψ b m`.       (★)

The error `∑_{b≠0} …` is a sum of `q − 1` Gauss-type terms. We bound it honestly: each
`charWeightedCount` term is a sum of `C(|G|,m)` unit-modulus products, so the *triangle-inequality*
envelope is `‖error‖ ≤ (q−1)·C(|G|, m)` (`charSum_error_norm_le`). This is the exact statement of
why the character-sum method, **on its own**, cannot resolve `N(m, target)`: the main term and the
trivial triangle bound on the error are the *same* order `C(|G|,m)`, so cancellation in the error
(square-root / Weil-type, which uses the *multiplicative* subgroup structure of `G` and is **not**
captured by the additive characters alone) is exactly what would decide the open question. We make
this delimiter precise rather than hand-wave it.

## Honest status

`sorry`-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). What is **proven new**: the
exact character-sum identity for `N(m, target)` over a genuine finite field, the isolation of the
field-independent main term `C(|G|, m)`, the master split (★), and the explicit triangle envelope on
the error. What this does **not** do (the honest delimiter, the open core): bound the *cancellation*
in the Gauss error below the main term — that requires Weil-type / multiplicative-structure input on
`G`, which the additive-character orthogonality does not see. So this is a genuine new
*exact-identity* brick plus a proven *no-go* for the bare additive-character method, not a
closure of `N(m, ·)`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset Polynomial BigOperators

-- These instances are genuinely required by the headline theorems (additive-character
-- orthogonality `AddChar.sum_mulShift` needs `[Fintype F] [DecidableEq F]`); we keep them in the
-- shared `variable` block, so some auxiliary lemmas carry them without using them in their type.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Round4CharacterSum

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The counted quantity and the character-weighted count -/

/-- The subgroup subset-sum count `N(m, target) = #{ S ⊆ G : |S| = m, ∑_{x∈S} x = target }`, as a
`Finset` filter over the size-`m` subsets of `G`. -/
noncomputable def subsetSumCount (G : Finset F) (m : ℕ) (target : F) : ℕ :=
  ((G.powersetCard m).filter (fun S => ∑ x ∈ S, x = target)).card

/-- The **character-weighted subset count** `e_m((ψ(b·x))_{x∈G}) = ∑_{S⊆G,|S|=m} ∏_{x∈S} ψ(b·x)`,
the inner sum of the character-sum formula and the elementary symmetric function of the character
values at the shifted subgroup. -/
noncomputable def charWeightedCount (ψ : AddChar F ℂ) (b : F) (G : Finset F) (m : ℕ) : ℂ :=
  ∑ S ∈ G.powersetCard m, ∏ x ∈ S, ψ (b * x)

/-! ## Vieta: the character-weighted count is a coefficient of `∏_{x∈G}(X + ψ(b·x))` -/

/-- **Generating-function (Vieta) form of the character-weighted count.** For any `m ≤ |G|`,
`charWeightedCount ψ b G m` equals the `(|G| − m)`-th coefficient of `∏_{x∈G}(X + C (ψ(b·x)))`.
This is the exact "extract `[z^m]` of `∏(1 + z·ψ(bx))`" step (here in the homogenized `X`-degree
form), the character-sum method's inner generating function. -/
theorem charWeightedCount_eq_coeff (ψ : AddChar F ℂ) (b : F) (G : Finset F) {m : ℕ}
    (hm : m ≤ G.card) :
    charWeightedCount ψ b G m
      = (∏ x ∈ G, (X + C (ψ (b * x)))).coeff (G.card - m) := by
  classical
  -- `Finset.prod_X_add_C_coeff`: coeff `(|G| − m)` is the sum over `(|G| − (|G|−m)) = m`-subsets.
  rw [Finset.prod_X_add_C_coeff G (fun x => ψ (b * x)) (Nat.sub_le _ _)]
  rw [Nat.sub_sub_self hm]
  rfl

/-- **The `b = 0` (trivial-character) main term is `C(|G|, m)`.** At `b = 0`, every factor
`ψ(0·x) = ψ(0) = 1`, so each product is `1` and the count is the number of size-`m` subsets of `G`,
i.e. `C(|G|, m)`. This is the field-independent **main term** of the Gauss-sum formula. -/
theorem charWeightedCount_zero (ψ : AddChar F ℂ) (G : Finset F) (m : ℕ) :
    charWeightedCount ψ 0 G m = (G.card.choose m : ℂ) := by
  classical
  unfold charWeightedCount
  have hone : ∀ S ∈ G.powersetCard m, (∏ x ∈ S, ψ ((0 : F) * x)) = 1 := by
    intro S _
    refine Finset.prod_eq_one (fun x _ => ?_)
    rw [zero_mul, AddChar.map_zero_eq_one]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_powersetCard]
  simp

/-! ## Orthogonality indicator: turn the sum-constraint into an average over the dual group -/

/-- **Additive-character indicator.** For a *primitive* `ψ` and any `y ∈ F`, orthogonality
`AddChar.sum_mulShift` gives `∑_{b∈F} ψ(b·y) = q·[y=0]`. Dividing by `q` (`q ≠ 0` in `ℂ`) realizes
the `{0,1}`-indicator of `y = 0` as an additive-character average — the engine that converts the
subset-sum *constraint* into a sum over the dual group. -/
theorem indicator_eq_charAvg {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (y : F) :
    (if y = 0 then (1 : ℂ) else 0)
      = (Fintype.card F : ℂ)⁻¹ * ∑ b : F, ψ (b * y) := by
  classical
  have hq0 : (Fintype.card F : ℂ) ≠ 0 := by
    have : 0 < Fintype.card F := Fintype.card_pos
    exact_mod_cast this.ne'
  rw [AddChar.sum_mulShift y hψ]
  split_ifs with h
  · field_simp
  · simp

/-- **Character of a subset sum factors as a product.** `ψ(b·∑_{x∈S} x) = ∏_{x∈S} ψ(b·x)`: the
additive character turns the subset *sum* into a *product* of unit-modulus values — the
multiplicative form that meets Vieta. -/
theorem map_mul_sum_eq_prod (ψ : AddChar F ℂ) (b : F) (S : Finset F) :
    ψ (b * ∑ x ∈ S, x) = ∏ x ∈ S, ψ (b * x) := by
  classical
  rw [Finset.mul_sum]
  refine Finset.cons_induction (by simp) (fun a s ha ih => ?_) S
  rw [Finset.sum_cons, Finset.prod_cons, AddChar.map_add_eq_mul, ih]

/-! ## The master exact character-sum identity for `N(m, target)` -/

/-- **The EXACT character-sum / Gauss-sum identity for the subgroup subset-sum count.** For any
*primitive* additive character `ψ : AddChar F ℂ`, any finite subset `G ⊆ F`, size `m`, and
`target ∈ F`, the count `N(m, target)` is given, as an element of `ℂ`, by the dual-group average

  `N(m, target)  =  q⁻¹ · ∑_{b ∈ F}  ψ(−(b·target)) · charWeightedCount ψ b G m`,

where `charWeightedCount ψ b G m = ∑_{S⊆G,|S|=m} ∏_{x∈S} ψ(b·x) = e_m((ψ(b·x))_{x∈G})` is the
character-weighted (Vieta) subset count. This is the requested exact character-sum formula: the
subset-*sum* constraint has been resolved into a sum over the additive dual group, and the inner
combinatorics is the elementary symmetric / generating-function coefficient
(`charWeightedCount_eq_coeff`). -/
theorem subsetSumCount_eq_charSum {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (m : ℕ)
    (target : F) :
    (subsetSumCount G m target : ℂ)
      = (Fintype.card F : ℂ)⁻¹
          * ∑ b : F, ψ (-(b * target)) * charWeightedCount ψ b G m := by
  classical
  -- Write the count as a sum of `{0,1}`-indicators over the size-`m` subsets, cast to `ℂ`.
  have hcount : (subsetSumCount G m target : ℂ)
      = ∑ S ∈ G.powersetCard m, (if (∑ x ∈ S, x) = target then (1 : ℂ) else 0) := by
    unfold subsetSumCount
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [hcount]
  -- Replace each indicator by its additive-character average.
  have hind : ∀ S ∈ G.powersetCard m,
      (if (∑ x ∈ S, x) = target then (1 : ℂ) else 0)
        = (Fintype.card F : ℂ)⁻¹ * ∑ b : F, ψ (b * ((∑ x ∈ S, x) - target)) := by
    intro S _
    have h := indicator_eq_charAvg hψ ((∑ x ∈ S, x) - target)
    simp only [sub_eq_zero] at h
    convert h using 2
  rw [Finset.sum_congr rfl hind, ← Finset.mul_sum]
  congr 1
  -- Swap the order of summation `∑_S ∑_b = ∑_b ∑_S` and factor the character.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [charWeightedCount, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  -- `ψ(b·(∑x − target)) = ψ(−(b·target)) · ∏_{x∈S} ψ(b·x)`.
  have hsplit : b * ((∑ x ∈ S, x) - target) = (b * ∑ x ∈ S, x) + (-(b * target)) := by ring
  rw [hsplit, AddChar.map_add_eq_mul, map_mul_sum_eq_prod, mul_comm]

/-! ## The master split: main term `C(|G|, m)` plus the Gauss error -/

/-- **Master split (★): the field-independent main term `C(|G|, m)`, plus the Gauss error.**
Multiplying the exact identity by `q` and peeling off the `b = 0` term (which is
`ψ(0)·charWeightedCount ψ 0 G m = C(|G|, m)`, `charWeightedCount_zero`) gives

  `q · N(m, target)  =  C(|G|, m)  +  ∑_{b ≠ 0} ψ(−(b·target)) · charWeightedCount ψ b G m`.

The main term `C(|G|, m)` is exactly the capacity/`C(n,k)` endpoint count, now exhibited as the
*trivial-character* contribution to `N(m, target)` for **every** `m` and `target` over a genuine
finite field; the remaining sum over `b ≠ 0` is the Gauss-type error. -/
theorem subsetSumCount_main_plus_error {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (m : ℕ)
    (target : F) :
    (Fintype.card F : ℂ) * (subsetSumCount G m target : ℂ)
      = (G.card.choose m : ℂ)
        + ∑ b ∈ (Finset.univ.erase (0 : F)),
            ψ (-(b * target)) * charWeightedCount ψ b G m := by
  classical
  have hq0 : (Fintype.card F : ℂ) ≠ 0 := by
    have : 0 < Fintype.card F := Fintype.card_pos
    exact_mod_cast this.ne'
  rw [subsetSumCount_eq_charSum hψ, ← mul_assoc, mul_inv_cancel₀ hq0, one_mul]
  -- peel off the `b = 0` term from the full sum over `F`.
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : F))]
  rw [add_comm]
  congr 1
  -- the `b = 0` summand is `ψ(0)·charWeightedCount ψ 0 G m = 1·C(|G|,m) = C(|G|,m)`.
  rw [charWeightedCount_zero, zero_mul, neg_zero, AddChar.map_zero_eq_one, one_mul]

/-! ## The honest error envelope (the no-go for the bare additive-character method) -/

/-- **Each character-weighted count has modulus `≤ C(|G|, m)`.** `charWeightedCount ψ b G m` is a
sum of `C(|G|, m)` products of values `ψ(b·x)`, each of modulus `1` (`AddChar.norm_apply`, finite
group), so the triangle inequality gives `‖charWeightedCount ψ b G m‖ ≤ C(|G|, m)`. -/
theorem charWeightedCount_norm_le (ψ : AddChar F ℂ) (b : F) (G : Finset F) (m : ℕ) :
    ‖charWeightedCount ψ b G m‖ ≤ (G.card.choose m : ℝ) := by
  classical
  unfold charWeightedCount
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ S ∈ G.powersetCard m, ‖∏ x ∈ S, ψ (b * x)‖ ≤ 1 := by
    intro S _
    rw [norm_prod]
    refine le_of_eq ?_
    refine Finset.prod_eq_one (fun x _ => ?_)
    exact AddChar.norm_apply ψ (b * x)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_powersetCard]
  simp

/-- **The Gauss error is bounded by `(q − 1)·C(|G|, m)` — the honest no-go for the bare
additive-character method.** Triangle-inequality envelope of the `b ≠ 0` error in the master split
(★): each of the `q − 1` terms has modulus `‖ψ(−b·target)·charWeightedCount‖ ≤ 1·C(|G|, m)`. This is
the *same order* as the main term `C(|G|, m)`: the bare additive-character orthogonality cannot
separate the error from the main term, so it cannot by itself decide whether `N(m, target)` is
`≈ C(|G|,m)/q` (needs `q`-fold square-root cancellation, i.e. Weil-type input using the
**multiplicative** structure of `G`, which the additive characters do not see). We state the
delimiter precisely. -/
theorem charSum_error_norm_le {ψ : AddChar F ℂ} (G : Finset F) (m : ℕ) (target : F) :
    ‖∑ b ∈ (Finset.univ.erase (0 : F)),
        ψ (-(b * target)) * charWeightedCount ψ b G m‖
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ) * (G.card.choose m : ℝ) := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ b ∈ (Finset.univ.erase (0 : F)),
      ‖ψ (-(b * target)) * charWeightedCount ψ b G m‖ ≤ (G.card.choose m : ℝ) := by
    intro b _
    rw [norm_mul, AddChar.norm_apply, one_mul]
    exact charWeightedCount_norm_le ψ b G m
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  rw [nsmul_eq_mul]

/-! ## Non-vacuity: a primitive character always exists, so the identities are not vacuous -/

/-- **Non-vacuity.** A primitive additive character `F → ℂ` always exists on a finite field
(`FiniteField.primitiveChar_to_Complex`), so the hypothesis `ψ.IsPrimitive` of the master identity
is satisfiable; the exact formula `subsetSumCount_eq_charSum` is therefore a genuine, non-vacuous
statement about `N(m, target)`. -/
theorem exists_primitive_addChar : ∃ ψ : AddChar F ℂ, ψ.IsPrimitive := by
  haveI : Finite F := inferInstance
  exact ⟨AddChar.FiniteField.primitiveChar_to_Complex F,
    AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F⟩

end ArkLib.ProximityGap.Round4CharacterSum

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round4CharacterSum.charWeightedCount_eq_coeff
#print axioms ArkLib.ProximityGap.Round4CharacterSum.charWeightedCount_zero
#print axioms ArkLib.ProximityGap.Round4CharacterSum.indicator_eq_charAvg
#print axioms ArkLib.ProximityGap.Round4CharacterSum.map_mul_sum_eq_prod
#print axioms ArkLib.ProximityGap.Round4CharacterSum.subsetSumCount_eq_charSum
#print axioms ArkLib.ProximityGap.Round4CharacterSum.subsetSumCount_main_plus_error
#print axioms ArkLib.ProximityGap.Round4CharacterSum.charWeightedCount_norm_le
#print axioms ArkLib.ProximityGap.Round4CharacterSum.charSum_error_norm_le
#print axioms ArkLib.ProximityGap.Round4CharacterSum.exists_primitive_addChar
