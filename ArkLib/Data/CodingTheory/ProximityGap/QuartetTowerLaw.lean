/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Polynomial.Expand

/-!
# The quartet-tower law (#357, items 11/13/14 — the char-0 census mechanism)

The probe-discovered mechanism behind the char-0 constrained census
(`probe_char0_death_law.py`), machine-checked:

* `quartet_prod` — a quartet `{x, ix, −x, −ix}` has characteristic polynomial
  `T⁴ − x⁴` (pure ring identity from `i² = −1`);
* `prod_quartets_eq_expand` — a union of quartets has characteristic polynomial
  `expand 4 (∏ (T − x⁴))`: the census **recurses down the 4-adic tower**;
* `coeff_prod_quartets` — hence all its coefficients at indices `≢ 0 (mod 4)` vanish;
* `esymm_quartetUnion_eq_zero` — **the headline** (via Vieta): every elementary
  symmetric value `e_j` of a quartet union vanishes for `j ≢ 0 (mod 4)`.

Consequences (verified exactly by the probe at `n ∈ {8,16,32,64}`): quartet unions
satisfy the constrained-census system `e₂ = e₃ = 0` automatically; deeper constraints
(`e₄, e₈, …`) recurse to vanishing-sum systems on `μ_{n/4}`; the window-interior
rungs of the adjacent-pair family die in characteristic zero (parity + the odd-size
Lam–Leung kill on the recursion), so the family's interior census at large `p` is
pure characteristic-`p` surplus.
-/

open Polynomial Finset

namespace ProximityGap.QuartetTower

variable {F : Type*} [Field F]

/-- **The quartet characteristic polynomial**: for `i² = −1`,
`(T−x)(T−ix)(T+x)(T+ix) = T⁴ − x⁴`. -/
theorem quartet_prod {i : F} (hi : i ^ 2 = -1) (x : F) :
    (X - C x) * (X - C (i * x)) * (X - C (-x)) * (X - C (-(i * x)))
      = X ^ 4 - C (x ^ 4) := by
  have hci : (C i : F[X]) ^ 2 = -1 := by
    rw [← C_pow, hi, map_neg, map_one]
  calc (X - C x) * (X - C (i * x)) * (X - C (-x)) * (X - C (-(i * x)))
      = (X ^ 2 - C x ^ 2) * (X ^ 2 - (C i) ^ 2 * C x ^ 2) := by
        rw [map_neg, map_neg, map_mul]
        ring
    _ = (X ^ 2 - C x ^ 2) * (X ^ 2 + C x ^ 2) := by rw [hci]; ring
    _ = X ^ 4 - C (x ^ 4) := by
        have hc4 : (C (x ^ 4) : F[X]) = (C x) ^ 4 := by rw [C_pow]
        rw [hc4]
        ring

/-- The product over a quartet family is the 4-adic expansion of the product over
the fourth powers — **the tower recursion**. -/
theorem prod_quartets_eq_expand (xs : Finset F) :
    ∏ x ∈ xs, (X ^ 4 - C (x ^ 4))
      = Polynomial.expand F 4 (∏ x ∈ xs, (X - C (x ^ 4))) := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [map_sub, Polynomial.expand_X, Polynomial.expand_C]

/-- Coefficients of a quartet-family product vanish at every index `≢ 0 (mod 4)`. -/
theorem coeff_prod_quartets (xs : Finset F) {j : ℕ} (hj : ¬ 4 ∣ j) :
    (∏ x ∈ xs, (X ^ 4 - C (x ^ 4))).coeff j = 0 := by
  rw [prod_quartets_eq_expand, Polynomial.coeff_expand (by norm_num : 0 < 4),
    if_neg hj]

/-- The quartet multiset on a seed `x`. -/
def quartet (i x : F) : Multiset F := {x, i * x, -x, -(i * x)}

theorem quartet_card (i x : F) : Multiset.card (quartet i x) = 4 := rfl

/-- The union (with multiplicity) of the quartets over a seed family. -/
def quartetUnion (i : F) (xs : Finset F) : Multiset F :=
  xs.val.bind fun x => quartet i x

theorem quartetUnion_card (i : F) (xs : Finset F) :
    Multiset.card (quartetUnion i xs) = 4 * xs.card := by
  rw [quartetUnion, Multiset.card_bind]
  simp only [Function.comp_def]
  have hmap : Multiset.map (fun x => Multiset.card (quartet i x)) xs.val
      = Multiset.map (fun _ => 4) xs.val :=
    Multiset.map_congr rfl fun x _ => quartet_card i x
  rw [hmap, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_comm]
  rfl

/-- The characteristic polynomial of the quartet union is the quartet-family
product. -/
theorem prod_quartetUnion (i : F) (hi : i ^ 2 = -1) (xs : Finset F) :
    (Multiset.map (fun y => X - C y) (quartetUnion i xs)).prod
      = ∏ x ∈ xs, (X ^ 4 - C (x ^ 4)) := by
  rw [quartetUnion, Multiset.map_bind, Multiset.prod_bind]
  rw [show (Finset.prod xs fun x => X ^ 4 - C (x ^ 4))
    = Multiset.prod (Multiset.map (fun x => X ^ 4 - C (x ^ 4)) xs.val) from rfl]
  congr 1
  rw [Multiset.map_congr rfl]
  intro x _
  rw [quartet]
  show (Multiset.map (fun y => X - C y) {x, i * x, -x, -(i * x)}).prod
    = X ^ 4 - C (x ^ 4)
  simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Multiset.insert_eq_cons]
  rw [← quartet_prod hi x]
  ring

/-- **THE QUARTET-TOWER LAW** (via Vieta): every elementary symmetric value of a
quartet union vanishes at indices `≢ 0 (mod 4)` — in particular `e₂ = e₃ = 0`
always: quartet unions satisfy the first two census constraints automatically, and
the deeper constraints recurse to `μ_{n/4}`. -/
theorem esymm_quartetUnion_eq_zero (i : F) (hi : i ^ 2 = -1) (xs : Finset F)
    {j : ℕ} (hj4 : ¬ 4 ∣ j) (hjle : j ≤ 4 * xs.card) :
    (quartetUnion i xs).esymm j = 0 := by
  have hcard := quartetUnion_card i xs
  have hk : 4 * xs.card - j ≤ Multiset.card (quartetUnion i xs) := by
    rw [hcard]
    omega
  have hvieta := Multiset.prod_X_sub_C_coeff (quartetUnion i xs) hk
  rw [hcard] at hvieta
  have hsub : 4 * xs.card - (4 * xs.card - j) = j := by omega
  rw [hsub] at hvieta
  have hcoeff : (Multiset.map (fun y => X - C y) (quartetUnion i xs)).prod.coeff
      (4 * xs.card - j) = 0 := by
    rw [prod_quartetUnion i hi xs]
    refine coeff_prod_quartets xs ?_
    intro hdvd
    exact hj4 (by omega : 4 ∣ j)
  rw [hcoeff] at hvieta
  have hpow : ((-1 : F) ^ j) ≠ 0 := by
    refine pow_ne_zero _ ?_
    exact neg_ne_zero.mpr one_ne_zero
  exact (mul_eq_zero.mp hvieta.symm).resolve_left hpow

end ProximityGap.QuartetTower

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.QuartetTower.quartet_prod
#print axioms ProximityGap.QuartetTower.prod_quartets_eq_expand
#print axioms ProximityGap.QuartetTower.coeff_prod_quartets
#print axioms ProximityGap.QuartetTower.esymm_quartetUnion_eq_zero
