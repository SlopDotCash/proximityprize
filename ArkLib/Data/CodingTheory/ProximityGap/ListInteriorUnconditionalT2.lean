/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListInteriorT2TwoSymmetric
import ArkLib.Data.CodingTheory.ProximityGap.ListInteriorUnconditionalT1

/-!
# Round 6 (Issue #232, ABF26) — the UNCONDITIONAL `t = 2`, general-`n` interior list lower bound,
# one full agreement step DEEPER than the `t = 1` capacity sliver.

Round 5 produced two reusable, axiom-clean facts:

* **The `t = 1` weld** (`ListInteriorUnconditionalT1.lean`,
  `exists_interior_list_ge_unconditional`): choosing the word polynomial `g = X^k·(X − C target)` to
  *match* a heavy window-sum target, and feeding the index window-sum fiber to the Round-4 bridge,
  gives the FIRST unconditional general-`n` interior list lower bound `C(n,k+1) ≤ q·#{list}` at the
  radius `δ = 1 − (k+1)/n` (the sliver just inside capacity `1 − ρ`).
* **The exact `t = 2` joint criterion** (`ListInteriorT2TwoSymmetric.lean`,
  `degDrop_t2_iff_two_symmetric` and the bridge `twoSymmetric_interior_list_card_ge`): a `(k+2)`-set
  forces the *full* drop `deg(p_S) < k` **iff** its top two symmetric functions hit fixed targets
  `e_1(D_S) = −g.coeff(k+1)/c ∧ e_2(D_S) = g.coeff(k)/c`. But Round 5 left the *count* hypothesis in
  place: the bridge needs a `(k+2)`-set family in the JOINT fiber handed to it.

## What this file does — push the unconditional weld one step deeper to `t = 2`

This file **discharges the `t = 2` count hypothesis unconditionally**, exactly as Round 5 did at
`t = 1`, but now with a **double pigeonhole over both targets `(c₁, c₂)` simultaneously**:

* `sum_jointFamily_card_eq_choose` — the `(k+2)`-subsets are partitioned by the *pair*
  `(∑_{i∈S} D i, ∑_{{i,j}⊆S} D i·D j) ∈ F × F`, so summing the joint-fiber sizes over **all** pairs
  recovers `C(n, k+2)`. (Single fiberwise count into `F × F`.)
* `exists_jointFamily_card_ge` — therefore **some** pair `(c₁, c₂)` has joint fiber
  `q² · (fiber size) ≥ C(n, k+2)` (the double pigeonhole; the `q²` is the `|F × F|` denominator).
* `wordPoly2 k c₁ c₂ := X^k·(X² − C c₁·X + C c₂)` — the explicit monic degree-`(k+2)` word polynomial
  whose top two coefficients realize the chosen `(c₁, c₂)`: `coeff (k+1) = −c₁`, `coeff k = c₂`, so its
  `t = 2` joint targets are `−g.coeff(k+1)/1 = c₁` and `g.coeff(k)/1 = c₂` exactly.

Welding these (the joint fiber forces `deg(p_S) < k` via `degDrop_t2_iff_two_symmetric`, and the
Round-4 bridge turns the family into a list lower bound) gives the headline:

## The headline (`exists_interior_list_ge_unconditional_t2`)

For a smooth-domain Reed–Solomon code `RS[F, D, k]` (`D : ι ↪ F` injective, `0 < k`, `k ≤ n = |ι|`)
at the **interior** radius `δ = 1 − (k+2)/n` (interiorness `(k+2)² < k·n`), **there exists** an
explicit received word `w = g ∘ D` (`g` of degree exactly `k+2`) such that

  `C(n, k+2)  ≤  q² · #{ v ∈ RS[F,D,k] : agree(v, w) ≥ k+2 }`,

i.e. the interior list has size `≥ C(n,k+2)/q²`, **with no count hypothesis and no degree-drop family
supplied** — all three of `g`, the joint family, and the count bound are constructed internally. This
is one full agreement step deeper than the Round-5 `t = 1` result.

## Honest scope (what this is NOT — strictly weaker on two of the three axes than `t = 1`)

* The radius is `δ = 1 − (k+2)/n`, *deeper* than the `t = 1` radius `1 − (k+1)/n` (this is the one
  axis on which it improves — it moves one agreement step further into the gap `(1 − √ρ, 1 − ρ)`).
* The bound carries a `1/q²` factor (`q = |F|`), **weaker** than the `t = 1` `1/q`: it exceeds the
  trivial `1` only once `C(n, k+2) > q²`. Like `t = 1` this is NOT a `q`-independent statement, and it
  is *less* `q`-independent.
* It is still **near capacity** (`t = 2` vs `t = 1` — both are `O(1)` steps inside the right endpoint
  `1 − ρ`, not the deep interior near `1 − √ρ`). It does **not** pin `δ*`, and it does **not** decide
  the prize: pushing to general `t` with a `q`-INDEPENDENT count is the still-open additive question
  (a field-independent super-polynomial lower bound on the JOINTLY-prescribed `(k+t)`-subset count).

What is genuinely new over Round 5: the `t = 2` count hypothesis is now **discharged** — the second
(quadratic `e_2`) constraint is handled by extending the pigeonhole to `F × F`, and the word
polynomial is constructed to realize *both* targets at once. The result is the deepest unconditional
interior list brick in this development.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Polynomial BigOperators Finset
open ArkLib.CodingTheory.Round4InteriorList
open ArkLib.CodingTheory.Round5SliceRankT2

namespace ArkLib.CodingTheory.Round6DeeperT2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The explicit word polynomial `g = X^k · (X² − C c₁·X + C c₂)` for `t = 2`. -/

/-- The chosen degree-`(k+2)` word polynomial: `g = X^k · (X² − C c₁·X + C c₂)`. As a product of
monics it is monic of natDegree `k+2`; expanded it is `X^{k+2} − c₁·X^{k+1} + c₂·X^k`, so its
`X^{k+1}` coefficient is `−c₁` and its `X^k` coefficient is `+c₂`. Hence its `t = 2` joint targets
`−g.coeff(k+1)/leadingCoeff = c₁` and `g.coeff(k)/leadingCoeff = c₂` match the pigeonhole pair
`(c₁, c₂)` exactly. -/
noncomputable def wordPoly2 (k : ℕ) (c₁ c₂ : F) : F[X] :=
  X ^ k * (X ^ 2 - C c₁ * X + C c₂)

/-- Expansion of `wordPoly2` as a difference of monomials: `X^{k+2} − c₁·X^{k+1} + c₂·X^k`. -/
theorem wordPoly2_expand (k : ℕ) (c₁ c₂ : F) :
    wordPoly2 k c₁ c₂ = X ^ (k + 2) - C c₁ * X ^ (k + 1) + C c₂ * X ^ k := by
  have hmid : (X : F[X]) ^ k * (C c₁ * X) = C c₁ * X ^ (k + 1) := by
    rw [pow_succ]; ring
  have hlast : (X : F[X]) ^ k * C c₂ = C c₂ * X ^ k := by ring
  rw [wordPoly2, mul_add, mul_sub, ← pow_add, hmid, hlast]

/-- The quadratic `X² − C c₁·X + C c₂` in Mathlib's canonical quadratic shape
`C 1·X² + C (−c₁)·X + C c₂`. -/
theorem quad_eq (c₁ c₂ : F) :
    (X ^ 2 - C c₁ * X + C c₂ : F[X]) = C 1 * X ^ 2 + C (-c₁) * X + C c₂ := by
  rw [C_neg, C_1]; ring

/-- `X² − C c₁·X + C c₂` has natDegree `2` (leading coefficient `1 ≠ 0`). -/
theorem quad_natDegree (c₁ c₂ : F) : (X ^ 2 - C c₁ * X + C c₂ : F[X]).natDegree = 2 := by
  rw [quad_eq]; exact natDegree_quadratic one_ne_zero

/-- `X² − C c₁·X + C c₂` has leadingCoeff `1`. -/
theorem quad_leadingCoeff (c₁ c₂ : F) : (X ^ 2 - C c₁ * X + C c₂ : F[X]).leadingCoeff = 1 := by
  rw [quad_eq]; exact leadingCoeff_quadratic one_ne_zero

/-- `X² − C c₁·X + C c₂` is monic (leadingCoeff `1`). -/
theorem quad_monic (c₁ c₂ : F) : (X ^ 2 - C c₁ * X + C c₂ : F[X]).Monic :=
  quad_leadingCoeff c₁ c₂

/-- `wordPoly2 k c₁ c₂` is monic (a product of two monics). -/
theorem wordPoly2_monic (k : ℕ) (c₁ c₂ : F) : (wordPoly2 k c₁ c₂).Monic :=
  (monic_X_pow k).mul (quad_monic c₁ c₂)

/-- `wordPoly2 k c₁ c₂` has natDegree exactly `k + 2`. -/
theorem wordPoly2_natDegree (k : ℕ) (c₁ c₂ : F) : (wordPoly2 k c₁ c₂).natDegree = k + 2 := by
  rw [wordPoly2, Polynomial.Monic.natDegree_mul (monic_X_pow k) (quad_monic c₁ c₂),
    natDegree_X_pow, quad_natDegree]

/-- `wordPoly2 k c₁ c₂` is nonzero (it is monic over a field, hence nonzero). -/
theorem wordPoly2_ne_zero (k : ℕ) (c₁ c₂ : F) : wordPoly2 k c₁ c₂ ≠ 0 :=
  (wordPoly2_monic k c₁ c₂).ne_zero

/-- `wordPoly2 k c₁ c₂` has leading coefficient `1`. -/
theorem wordPoly2_leadingCoeff (k : ℕ) (c₁ c₂ : F) : (wordPoly2 k c₁ c₂).leadingCoeff = 1 :=
  wordPoly2_monic k c₁ c₂

/-- The `X^{k+1}` coefficient of `wordPoly2 k c₁ c₂` is `−c₁`. From the expansion
`X^{k+2} − c₁·X^{k+1} + c₂·X^k`, only the middle term contributes at index `k+1` (since `k ≠ k+1`
and `k+2 ≠ k+1`). -/
theorem wordPoly2_coeff_kp1 (k : ℕ) (c₁ c₂ : F) : (wordPoly2 k c₁ c₂).coeff (k + 1) = -c₁ := by
  rw [wordPoly2_expand, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [if_neg (by omega : ¬ k + 1 = k + 2), if_pos rfl, if_neg (by omega : ¬ k + 1 = k)]
  ring

/-- The `X^k` coefficient of `wordPoly2 k c₁ c₂` is `c₂`. From the expansion
`X^{k+2} − c₁·X^{k+1} + c₂·X^k`, only the last term contributes at index `k`. -/
theorem wordPoly2_coeff_k (k : ℕ) (c₁ c₂ : F) : (wordPoly2 k c₁ c₂).coeff k = c₂ := by
  rw [wordPoly2_expand, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [if_neg (by omega : ¬ k = k + 2), if_neg (by omega : ¬ k = k + 1), if_pos rfl]
  ring

/-- The `t = 2` joint targets of `wordPoly2 k c₁ c₂` are `(c₁, c₂)` itself:
`−(g.coeff (k+1))/leadingCoeff = −(−c₁)/1 = c₁` and `g.coeff k / leadingCoeff = c₂/1 = c₂`. -/
theorem wordPoly2_joint_targets (k : ℕ) (c₁ c₂ : F) :
    -((wordPoly2 k c₁ c₂).coeff (k + 1)) / (wordPoly2 k c₁ c₂).leadingCoeff = c₁ ∧
      (wordPoly2 k c₁ c₂).coeff k / (wordPoly2 k c₁ c₂).leadingCoeff = c₂ := by
  refine ⟨?_, ?_⟩
  · rw [wordPoly2_coeff_kp1, wordPoly2_leadingCoeff, neg_neg, div_one]
  · rw [wordPoly2_coeff_k, wordPoly2_leadingCoeff, div_one]

/-! ## The joint window-fiber carrier and its total over the pair of targets `(c₁, c₂) ∈ F × F`. -/

/-- The `e_1, e_2` **joint** window family: `(k+2)`-subsets of `ι` whose `D`-image has
`e_1 = ∑_{i∈S} D i = c₁` **and** `e_2 = ∑_{{i,j}⊆S} D i·D j = c₂`. For `g = wordPoly2 k c₁ c₂` each
such `S` forces `deg(p_S) < k` (`degDrop_t2_iff_two_symmetric`), so this is exactly the carrier of the
`t = 2` degree-drop family. -/
noncomputable def jointFamily (D : ι ↪ F) (k : ℕ) (c₁ c₂ : F) : Finset (Finset ι) :=
  (Finset.univ.powersetCard (k + 2)).filter
    (fun S => (∑ i ∈ S, D i) = c₁ ∧ (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = c₂)

/-- **Total over pairs `= C(n, k+2)`.** The `(k+2)`-subsets of `ι` are partitioned by the *pair*
`(∑_{i∈S} D i, ∑_{{i,j}⊆S} D i·D j) ∈ F × F`, so summing the joint-fiber sizes over all pairs recovers
`C(n, k+2)`. This is the conservation law that drives the double pigeonhole. -/
theorem sum_jointFamily_card_eq_choose [Fintype F] (D : ι ↪ F) (k : ℕ) :
    ∑ p : F × F, (jointFamily D k p.1 p.2).card = (Fintype.card ι).choose (k + 2) := by
  classical
  have hpart : (Finset.univ.powersetCard (k + 2) : Finset (Finset ι)).card
      = ∑ p : F × F,
          ((Finset.univ.powersetCard (k + 2)).filter
            (fun S => (∑ i ∈ S, D i, ∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = p)).card :=
    Finset.card_eq_sum_card_fiberwise
      (f := fun S => (∑ i ∈ S, D i, ∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i))
      (t := (Finset.univ : Finset (F × F)))
      (fun S _ => Finset.mem_univ _)
  rw [Finset.card_powersetCard, Finset.card_univ] at hpart
  -- rewrite each `jointFamily` (conjunction predicate) into the pair-equality fiber, then use hpart.
  have hconv : ∑ p : F × F, (jointFamily D k p.1 p.2).card
      = ∑ p : F × F,
          ((Finset.univ.powersetCard (k + 2)).filter
            (fun S => (∑ i ∈ S, D i, ∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = p)).card := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    unfold jointFamily
    congr 1
    apply Finset.filter_congr
    intro S _
    constructor
    · rintro ⟨h1, h2⟩; rw [Prod.ext_iff]; exact ⟨h1, h2⟩
    · intro h; rw [Prod.ext_iff] at h; exact ⟨h.1, h.2⟩
  rw [hconv, ← hpart]

/-- **Double pigeonhole on the joint fiber.** Since the `(k+2)`-fibers total `C(n, k+2)` over the
`q² = |F × F|` pairs of targets, some pair `(c₁, c₂)` has `q² · (fiber size) ≥ C(n, k+2)`. (Same
averaging argument as the `t = 1` case `exists_indexFamily_card_ge`, run on the joint family over the
product index set `F × F`.) -/
theorem exists_jointFamily_card_ge [Fintype F] (D : ι ↪ F) (k : ℕ) (hq : 0 < Fintype.card F) :
    ∃ c₁ c₂ : F,
      (Fintype.card ι).choose (k + 2)
        ≤ Fintype.card F * Fintype.card F * (jointFamily D k c₁ c₂).card := by
  classical
  by_contra hcon
  push_neg at hcon
  -- recast as: every fiber `< C(n,k+2)/q²`.
  have hcon' : ∀ p : F × F,
      (jointFamily D k p.1 p.2).card * (Fintype.card F * Fintype.card F)
        < (Fintype.card ι).choose (k + 2) := by
    intro p
    rw [mul_comm]
    exact hcon p.1 p.2
  have hsum : ∑ p : F × F, (jointFamily D k p.1 p.2).card = (Fintype.card ι).choose (k + 2) :=
    sum_jointFamily_card_eq_choose D k
  have hqq : 0 < Fintype.card F * Fintype.card F := Nat.mul_pos hq hq
  have hprodne : (Finset.univ : Finset (F × F)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact (Fintype.card_pos_iff.mp (by rw [Fintype.card_prod]; exact hqq))
  have hbound : ∑ p : F × F, (jointFamily D k p.1 p.2).card < (Fintype.card ι).choose (k + 2) := by
    by_cases hn0 : (Fintype.card ι).choose (k + 2) = 0
    · exact absurd (hcon' (Classical.arbitrary (F × F))) (by rw [hn0]; exact Nat.not_lt_zero _)
    · have hmul : (∑ p : F × F, (jointFamily D k p.1 p.2).card)
            * (Fintype.card F * Fintype.card F)
          < (Fintype.card F * Fintype.card F) * (Fintype.card ι).choose (k + 2) := by
        calc (∑ p : F × F, (jointFamily D k p.1 p.2).card) * (Fintype.card F * Fintype.card F)
            = ∑ p : F × F, (jointFamily D k p.1 p.2).card * (Fintype.card F * Fintype.card F) := by
              rw [Finset.sum_mul]
          _ < ∑ _p : F × F, (Fintype.card ι).choose (k + 2) :=
              Finset.sum_lt_sum_of_nonempty hprodne (fun p _ => hcon' p)
          _ = (Fintype.card F * Fintype.card F) * (Fintype.card ι).choose (k + 2) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul]
      exact lt_of_mul_lt_mul_right
        (by rwa [mul_comm (Fintype.card F * Fintype.card F)] at hmul) (Nat.zero_le _)
  rw [hsum] at hbound
  exact lt_irrefl _ hbound

/-! ## Each joint-fiber member forces the degree drop: the carrier is a genuine `DegDropFamily`. -/

/-- **The joint window-fiber lies inside the two-symmetric joint fiber of `wordPoly2`.** For
`g = wordPoly2 k c₁ c₂` and any `S ∈ jointFamily D k c₁ c₂`, the membership conditions
`∑_{i∈S} D i = c₁` and `∑_{{i,j}⊆S} D i·D j = c₂` are *exactly* the two joint targets
`−g.coeff(k+1)/lc = c₁` and `g.coeff k/lc = c₂` (by `wordPoly2_joint_targets`), so `S` satisfies the
`degDrop_t2_iff_two_symmetric` hypothesis. -/
theorem jointFamily_hfiber (D : ι ↪ F) (k : ℕ) (c₁ c₂ : F)
    {S : Finset ι} (hS : S ∈ jointFamily D k c₁ c₂) :
    (∑ i ∈ S, D i) = -(wordPoly2 k c₁ c₂).coeff (k + 1) / (wordPoly2 k c₁ c₂).leadingCoeff
      ∧ (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i)
          = (wordPoly2 k c₁ c₂).coeff k / (wordPoly2 k c₁ c₂).leadingCoeff := by
  rw [jointFamily, Finset.mem_filter, Finset.mem_powersetCard] at hS
  obtain ⟨_, hS1, hS2⟩ := hS
  obtain ⟨ht1, ht2⟩ := wordPoly2_joint_targets (F := F) k c₁ c₂
  rw [ht1, ht2]
  exact ⟨hS1, hS2⟩

/-- Every member of `jointFamily D k c₁ c₂` has card `k + 2` (by definition of the carrier). -/
theorem jointFamily_card (D : ι ↪ F) (k : ℕ) (c₁ c₂ : F)
    {S : Finset ι} (hS : S ∈ jointFamily D k c₁ c₂) : S.card = k + 2 := by
  rw [jointFamily, Finset.mem_filter, Finset.mem_powersetCard] at hS
  exact hS.1.2

/-- The `t = 2` degree-drop family for `g = wordPoly2 k c₁ c₂` with carrier the joint window-fiber
`jointFamily D k c₁ c₂`. Built by feeding each fiber member (which hits both joint targets, by
`jointFamily_hfiber`) to the Round-5 packager `degDrop_t2_family_of_two_symmetric`. -/
noncomputable def jointDegDropFamily (D : ι ↪ F) (k : ℕ) (c₁ c₂ : F) (hk : 0 < k) :
    DegDropFamily D (wordPoly2 k c₁ c₂) k 2 :=
  degDrop_t2_family_of_two_symmetric D (wordPoly2 k c₁ c₂)
    (wordPoly2_natDegree k c₁ c₂) (wordPoly2_ne_zero k c₁ c₂) hk
    (jointFamily D k c₁ c₂)
    (fun _S hS => jointFamily_card D k c₁ c₂ hS)
    (fun _S hS => jointFamily_hfiber D k c₁ c₂ hS)

/-- The carrier of `jointDegDropFamily` is `jointFamily D k c₁ c₂` (by definition). -/
theorem jointDegDropFamily_carrier (D : ι ↪ F) (k : ℕ) (c₁ c₂ : F) (hk : 0 < k) :
    (jointDegDropFamily D k c₁ c₂ hk).carrier = jointFamily D k c₁ c₂ := rfl

/-! ## The headline: the unconditional `t = 2` interior list lower bound. -/

open Classical in
/-- **The unconditional, general-`n`, interior list-decoding lower bound, one step DEEPER than the
`t = 1` capacity sliver** (Issue #232, `t = 2`).

For a smooth-domain Reed–Solomon code `RS[F, D, k]` (`D : ι ↪ F` injective, `0 < k`, `k ≤ n = |ι|`)
at the interior radius `δ = 1 − (k+2)/n` (interiorness certified by `(k+2)² < k·n`), there exists
an explicit received word `w = (i ↦ g(D i))` with `g = X^k·(X² − C c₁·X + C c₂)` of degree exactly
`k+2` such that the list of codewords agreeing with `w` on `≥ k+2` coords has size `≥ C(n,k+2)/q²`:

  `C(n, k+2)  ≤  q² · #{ v ∈ RS[F,D,k] : agree(v, w) ≥ k+2 }`.

No degree-drop family and no count hypothesis are assumed — all are constructed internally (the
family is the `(e_1, e_2)` joint window-fiber; the count is the double-pigeonhole lower bound
`C(n,k+2)/q²`). This is the Round-5 `t = 1` weld pushed one full agreement step deeper, at the cost
of the weaker `1/q²` (rather than `1/q`) denominator. -/
theorem exists_interior_list_ge_unconditional_t2 [Fintype F] (D : ι ↪ F) {k : ℕ}
    (hk : 0 < k) (hkn : k ≤ Fintype.card ι) (hq : 0 < Fintype.card F)
    (hint : (k + 2) ^ 2 < k * Fintype.card ι) :
    ∃ (g : F[X]), g.natDegree = k + 2 ∧
      (Fintype.card ι).choose (k + 2) ≤
        Fintype.card F * Fintype.card F *
          (Finset.univ.filter (fun v : ι → F =>
            v ∈ ReedSolomon.code D k ∧
              k + 2 ≤ agreeCount v (fun i => g.eval (D i)))).card := by
  classical
  -- interiorness certificate (kept to tie the statement to the strictly-interior radius).
  have _hinterior : k < k + 2 ∧ (k + 2) ^ 2 < k * Fintype.card ι :=
    interior_radius_witness (by norm_num) hint
  -- double pigeonhole: pick the heavy `(e_1, e_2)` pair.
  obtain ⟨c₁, c₂, hcount⟩ := exists_jointFamily_card_ge D k hq
  refine ⟨wordPoly2 k c₁ c₂, wordPoly2_natDegree k c₁ c₂, ?_⟩
  -- the bridge: list ≥ |carrier| = |jointFamily|.
  have hbridge :=
    interior_list_card_ge_family D (wordPoly2 k c₁ c₂)
      (wordPoly2_ne_zero k c₁ c₂) hkn (jointDegDropFamily D k c₁ c₂ hk)
  rw [jointDegDropFamily_carrier D k c₁ c₂ hk] at hbridge
  -- chain: C(n,k+2) ≤ q²·|jointFamily| ≤ q²·(list size).
  calc (Fintype.card ι).choose (k + 2)
      ≤ Fintype.card F * Fintype.card F * (jointFamily D k c₁ c₂).card := hcount
    _ ≤ Fintype.card F * Fintype.card F * _ := Nat.mul_le_mul_left _ hbridge

/-- **The headline hypotheses are jointly satisfiable (non-vacuity).** At `k = 50` and `n = 220`
(rate `ρ = 50/220 ≈ 0.227`), all four arithmetic premises of
`exists_interior_list_ge_unconditional_t2` hold simultaneously: `0 < k`, `k ≤ n`,
`(k+2)² = 52² = 2704 < 11000 = k·n`. Pairing this with any finite field `F` (`0 < |F|`) and a domain
`ι` with `|ι| = 220` (e.g. `ι = Fin 220`, `D : Fin 220 ↪ F` into a field of size `≥ 220`)
instantiates the theorem with `C(220, 52) > 0` on the right — so the list bound
`C(220, 52) ≤ q² · (list size)` is a genuine, non-vacuous statement, not `0 ≤ …`. -/
theorem headline_hypotheses_satisfiable_t2 :
    0 < 50 ∧ (50 : ℕ) ≤ 220 ∧ (50 + 2) ^ 2 < 50 * 220 ∧ 0 < Nat.choose 220 (50 + 2) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  exact Nat.choose_pos (by norm_num)

end ArkLib.CodingTheory.Round6DeeperT2

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round6DeeperT2.wordPoly2_natDegree
#print axioms ArkLib.CodingTheory.Round6DeeperT2.wordPoly2_coeff_kp1
#print axioms ArkLib.CodingTheory.Round6DeeperT2.wordPoly2_coeff_k
#print axioms ArkLib.CodingTheory.Round6DeeperT2.wordPoly2_joint_targets
#print axioms ArkLib.CodingTheory.Round6DeeperT2.sum_jointFamily_card_eq_choose
#print axioms ArkLib.CodingTheory.Round6DeeperT2.exists_jointFamily_card_ge
#print axioms ArkLib.CodingTheory.Round6DeeperT2.jointFamily_hfiber
#print axioms ArkLib.CodingTheory.Round6DeeperT2.jointDegDropFamily_carrier
#print axioms ArkLib.CodingTheory.Round6DeeperT2.exists_interior_list_ge_unconditional_t2
#print axioms ArkLib.CodingTheory.Round6DeeperT2.headline_hypotheses_satisfiable_t2
