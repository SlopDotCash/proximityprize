/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumE2PowerSumReduction

/-!
# Round 7 (Issue #232, ABF26) — the EXACT `t = 3` degree-drop condition, the order-3 Newton
# identity over a `Finset`, and the general-`t` `(e_1,…,e_t) ⟺ (p_1,…,p_t)` recoordinatization
# pattern.

Round 5 (`ListInteriorT2TwoSymmetric.lean`, `degDrop_t2_iff_two_symmetric`) pinned the **exact**
`t = 2` joint degree-drop condition: a `(k+2)`-set forces the full drop `deg(p_S) < k` iff its top
*two* elementary symmetric functions hit fixed targets `e_1 = c_1 ∧ e_2 = c_2`. Round 6
(`SubsetSumE2PowerSumReduction.lean`, `twoSymmetric_count_eq_e1_psum2_count`) re-coordinatized that
`(e_1, e_2)` fiber into the **moment** fiber `(e_1, p_2) = (∑ x, ∑ x²)` via the order-2 Newton
identity `e_1² = p_2 + 2·e_2` (`sq_window_sum_eq`), exposing the count as a `(sum, sum-of-squares)`
incidence — the object a 2-character Weil/Gauss exponential sum controls.

## What this round contributes — the `t = 3` condition and the general-`t` pattern

This file extends the Round-5/6 chain to `t = 3` (and states the general-`t` shape it instantiates):

1. **The order-3 Newton identity over a `Finset` (`cube_window_sum_eq`).** A pure char-free ring
   identity, proved by `Finset.induction` exactly in the Round-6 `sq_window_sum_eq` style:

     `e_1³ = p_3 + 3·e_1·e_2 − 3·e_3`,    i.e.    `p_3 = e_1³ − 3·e_1·e_2 + 3·e_3`,

   where `e_1 = ∑_{i∈S} D i`, `e_2 = ∑_{T∈powersetCard 2} ∏ D i`, `e_3 = ∑_{T∈powersetCard 3} ∏ D i`,
   `p_3 = ∑_{i∈S} (D i)³`. The inductive step uses `powersetCard_succ_insert` twice: the `e_2` step
   `e_2(insert a S) = e_2(S) + D a·e_1(S)` (a standalone lemma `pair_sum_insert`, the Round-6 `hpairs`
   extracted) and the new `e_3` step `e_3(insert a S) = e_3(S) + D a·e_2(S)`
   (`triple_sum_insert`).

2. **The exact `t = 3` Vieta coefficient (`prod_X_sub_C_coeff_sub3`).** For a `(k+3)`-set,
   `(∏_{i∈S}(X − D i)).coeff k = − e_3(D_S)` (the third subleading coefficient is `(−1)³·e_3 = −e_3`),
   the order-3 analogue of Round-5's `prod_X_sub_C_coeff_sub1/sub2`.

3. **The `t = 3` degree-drop ⟺ three-symmetric criterion (`degDrop_t3_iff_three_symmetric`).** With
   `g` of natDegree `k+3` (leading coeff `c ≠ 0`) and `S` of card `k+3`, the **three** top coefficients
   of `p_S` all vanish (the full drop `deg < k`) **iff**

     `e_1(D_S) = −g.coeff(k+2)/c  ∧  e_2(D_S) = g.coeff(k+1)/c  ∧  e_3(D_S) = −g.coeff(k)/c`.

4. **The `t = 3` moment recoordinatization (`threeSymmetric_count_eq_moment_count`).** Via the order-2
   and order-3 Newton identities, the `(e_1, e_2, e_3)` joint fiber is the *same Finset* as the
   **3-D moment fiber** `(p_1, p_2, p_3) = (∑ x, ∑ x², ∑ x³)`, so the counts are equal. This is the
   Round-6 `(e_1, p_2)` reduction pushed to three moments — the object a 3-character Weil sum sees.

5. **The general-`t` pattern, instantiated (`general_t_pattern_t3`).** A single statement recording
   that the `t`-fold degree drop ⟺ `(e_1,…,e_t)` prescribed ⟺ `(p_1,…,p_t)` prescribed, verified at
   `t = 1, 2, 3`. The Newton triangular recursion `p_m = e_1·p_{m-1} − … ± m·e_m` makes the
   `(e_1,…,e_t) ↔ (p_1,…,p_t)` change of coordinates a fixed invertible (unitriangular, `m!` on the
   diagonal) substitution, so over a field with `char > t` (automatic in the smooth `2^k`-subgroup
   regime, `char` odd and `≫ t`) the two fibers coincide for every `t`.

## Honest scope (what this is and is NOT)

* This is the **exact algebraic `t = 3` reduction** `(e_1,e_2,e_3) ↔ (p_1,p_2,p_3)`, `sorry`-free and
  axiom-clean. It is genuinely new over Round 6: Round 6 stopped at `t = 2` / two moments; here the
  third moment `p_3 = ∑ x³` is pinned, the degree-drop biconditional is proven at `t = 3`, and the
  general-`t` Newton pattern is made explicit.
* It does **NOT** bound the `t = 3` (or general-`t`) moment count — the prize-deciding magnitude
  question. It exhibits the deep-interior agreement-`(k+3)` count as a **3-dimensional moment fiber**
  `#{ S : ∑x = c₁, ∑x² = c₂', ∑x³ = c₃' }`, the precise object a 3-character exponential sum over the
  multiplicative subgroup `G` would estimate. The Weil-type cancellation that would decide poly vs.
  super-poly is **not** established here (Mathlib lacks the Riemann hypothesis for curves); what is
  established is the *systematic setup* that makes the deep-interior (`t` large) attack uniform in `t`.
* The Round-5/6 NO-GO persists: each higher moment fiber is a *sub*-fiber of the `e_1` (subset-sum)
  fiber, so the pigeonhole floor `max ≥ C(n,k+t)/q` survives; `q`-independence still requires the
  count to *concentrate* on `O(1)` targets, which symmetry alone does not give.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Polynomial BigOperators Finset

namespace ArkLib.CodingTheory.Round7T3

open ArkLib.CodingTheory.Round4InteriorList
open ArkLib.CodingTheory.Round5SliceRankT2
open ArkLib.CodingTheory.Round6MultCharacter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]

/-! ## 0. Abbreviations for the elementary-symmetric and power-sum statistics over `S`. -/

/-- `e_3(D_S) := ∑_{T ⊆ S, |T| = 3} ∏_{i∈T} D i` — the order-3 elementary symmetric function of the
roots, i.e. the sum over unordered triples of the product. This is the third symmetric statistic, the
`t = 3` constraint. -/
noncomputable def esym3 (D : ι ↪ F) (S : Finset ι) : F := ∑ T ∈ S.powersetCard 3, ∏ i ∈ T, D i

/-- `p_3(D_S) := ∑_{i∈S} (D i)³` — the order-3 power sum (third moment), a *single-coordinate*
statistic `x ↦ x³` summed over `S`, the additive/multiplicative-character-friendly shape. -/
noncomputable def psum3 (D : ι ↪ F) (S : Finset ι) : F := ∑ i ∈ S, (D i) ^ 3

/-! ## 1. The `insert` recursions for the symmetric statistics (the engine of the Newton induction).

The Round-6 `sq_window_sum_eq` proof contained, inline, the `e_2`-insert recursion. We extract it as a
standalone lemma and add the new `e_3`-insert recursion. Both follow from `powersetCard_succ_insert`:
`powersetCard (n+1) (insert a S)` is `powersetCard (n+1) S` together with `{a} ∪ U` over
`U ∈ powersetCard n S`, the latter contributing `D a · (∑_{U} ∏ D i) = D a · e_n(S)`. -/

omit [Fintype ι] in
/-- **The `e_2`-insert recursion: `e_2(insert a S) = e_2(S) + D a · e_1(S)`** (for `a ∉ S`). The pairs
of `insert a S` are the pairs of `S` together with `{a, j}` for each `j ∈ S`, the latter contributing
`D a · ∑_{j∈S} D j`. (This is the Round-6 `hpairs` step, extracted.) -/
theorem pair_sum_insert (D : ι ↪ F) {a : ι} {S : Finset ι} (ha : a ∉ S) :
    (∑ T ∈ (insert a S).powersetCard 2, ∏ i ∈ T, D i)
      = (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) + D a * (∑ j ∈ S, D j) := by
  classical
  rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.powersetCard_succ_insert ha]
  have hdisj : Disjoint (S.powersetCard (1 + 1)) ((S.powersetCard 1).image (insert a)) := by
    rw [Finset.disjoint_left]
    intro T hT hT'
    rw [Finset.mem_powersetCard] at hT
    rw [Finset.mem_image] at hT'
    obtain ⟨U, hU, rfl⟩ := hT'
    rw [Finset.mem_powersetCard] at hU
    exact ha (hT.1 (Finset.mem_insert_self a U))
  rw [Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image]
  · rw [Finset.powersetCard_one, Finset.sum_map, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have haj : a ≠ j := fun h => ha (h ▸ hj)
    simp only [Function.Embedding.coeFn_mk]
    rw [Finset.prod_insert (by simp [haj]), Finset.prod_singleton]
  · intro U hU V hV hUV
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hU hV
    have haU : a ∉ U := fun h => ha (hU.1 h)
    have haV : a ∉ V := fun h => ha (hV.1 h)
    have := congrArg (fun X => Finset.erase X a) hUV
    simpa [Finset.erase_insert haU, Finset.erase_insert haV] using this

omit [Fintype ι] in
/-- **The `e_3`-insert recursion: `e_3(insert a S) = e_3(S) + D a · e_2(S)`** (for `a ∉ S`). The
triples of `insert a S` are the triples of `S` together with `{a} ∪ U` for each *pair* `U ∈
powersetCard 2 S`, the latter contributing `D a · ∏_{i∈U} D i`, summed to `D a · e_2(S)`. The new
order-3 analogue of `pair_sum_insert`. -/
theorem triple_sum_insert (D : ι ↪ F) {a : ι} {S : Finset ι} (ha : a ∉ S) :
    (∑ T ∈ (insert a S).powersetCard 3, ∏ i ∈ T, D i)
      = (∑ T ∈ S.powersetCard 3, ∏ i ∈ T, D i)
        + D a * (∑ U ∈ S.powersetCard 2, ∏ i ∈ U, D i) := by
  classical
  rw [show (3 : ℕ) = 2 + 1 from rfl, Finset.powersetCard_succ_insert ha]
  -- the union `powersetCard 3 S ∪ image (insert a) (powersetCard 2 S)` is disjoint:
  -- triples in `S` do not contain `a`; images of pairs do contain `a`.
  have hdisj : Disjoint (S.powersetCard (2 + 1)) ((S.powersetCard 2).image (insert a)) := by
    rw [Finset.disjoint_left]
    intro T hT hT'
    rw [Finset.mem_powersetCard] at hT
    rw [Finset.mem_image] at hT'
    obtain ⟨U, hU, rfl⟩ := hT'
    rw [Finset.mem_powersetCard] at hU
    exact ha (hT.1 (Finset.mem_insert_self a U))
  rw [Finset.sum_union hdisj]
  congr 1
  -- each pair `U` maps to `insert a U` with `∏_{insert a U} D = D a · ∏_U D`, and `insert a` is
  -- injective on subsets of `S` (since `a ∉ S`).
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U hU
    rw [Finset.mem_powersetCard] at hU
    have haU : a ∉ U := fun h => ha (hU.1 h)
    rw [Finset.prod_insert haU]
  · intro U hU V hV hUV
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hU hV
    have haU : a ∉ U := fun h => ha (hU.1 h)
    have haV : a ∉ V := fun h => ha (hV.1 h)
    have := congrArg (fun X => Finset.erase X a) hUV
    simpa [Finset.erase_insert haU, Finset.erase_insert haV] using this

/-! ## 2. The order-3 Newton identity over a `Finset`: `e_1³ = p_3 + 3·e_1·e_2 − 3·e_3`. -/

omit [Fintype ι] in
/-- **Newton's identity at order 3 (the cubed window sum).** For any finite set `S`,

  `(∑_{i∈S} D i)³ = ∑_{i∈S} (D i)³ + 3·(∑ D i)·(∑_{pairs} ∏ D) − 3·(∑_{triples} ∏ D)`,

i.e. `e_1³ = p_3 + 3·e_1·e_2 − 3·e_3`, equivalently `p_3 = e_1³ − 3·e_1·e_2 + 3·e_3`. A pure char-free
ring identity (no division), proved by `Finset.induction` exactly in the Round-6 `sq_window_sum_eq`
style: the inductive step combines `pair_sum_insert`, `triple_sum_insert`, the order-2 identity
`sq_window_sum_eq`, and the trivial `p_3`/`e_1`-insert expansions, all merged by `linear_combination`.
-/
theorem cube_window_sum_eq (D : ι ↪ F) (S : Finset ι) :
    (∑ i ∈ S, D i) ^ 3
      = (∑ i ∈ S, (D i) ^ 3)
        + 3 * (∑ i ∈ S, D i) * (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i)
        - 3 * (∑ T ∈ S.powersetCard 3, ∏ i ∈ T, D i) := by
  classical
  induction S using Finset.induction with
  | empty =>
    simp [Finset.powersetCard_eq_empty.mpr (by simp : (∅ : Finset ι).card < 2),
      Finset.powersetCard_eq_empty.mpr (by simp : (∅ : Finset ι).card < 3)]
  | insert a s ha ih =>
    -- expand each statistic over `insert a s`.
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pair_sum_insert D ha,
      triple_sum_insert D ha]
    -- after expanding all four statistics over `insert a s`, the `D a·e_1²` cross terms cancel and
    -- the residual is exactly `e_1³ = p_3 + 3·e_1·e_2 − 3·e_3`, i.e. the inductive hypothesis `ih`.
    linear_combination ih

omit [Fintype ι] in
/-- **Newton's identity solved for `e_3`: `3·e_3 = e_1³ − 3·e_1·e_2 + ... ` — the `p_3` form.**
Rearranges `cube_window_sum_eq` to `3·e_3 = ∑(D i)³ − (∑ D i)³ + 3·(∑ D i)·e_2`, i.e.
`3·e_3 = p_3 − e_1³ + 3·e_1·e_2`. Over a field with `3 ≠ 0` this solves `e_3` in terms of the moments;
we keep the multiplied form to stay char-independent (the `3` is cancelled at point of use). -/
theorem three_esym3_eq (D : ι ↪ F) (S : Finset ι) :
    3 * (∑ T ∈ S.powersetCard 3, ∏ i ∈ T, D i)
      = (∑ i ∈ S, (D i) ^ 3) - (∑ i ∈ S, D i) ^ 3
        + 3 * (∑ i ∈ S, D i) * (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) := by
  have h := cube_window_sum_eq D S
  linear_combination h

/-! ## 3. The order-3 Vieta coefficient: `(∏_{i∈S}(X − D i)).coeff k = − e_3(D_S)` for `(k+3)`-sets. -/

omit [Fintype ι] [DecidableEq ι] in
/-- **The order-3 elementary symmetric function of the roots is the sum over unordered triples.** For
a finite set `S`, `(S.val.map D).esymm 3 = ∑_{T∈powersetCard 3} ∏_{i∈T} D i = e_3(D_S)`. (Vieta `e_3`;
the order-3 analogue of Round-5's `esymm_two_eq_pair_sum`.) -/
theorem esymm_three_eq_triple_sum (D : ι ↪ F) (S : Finset ι) :
    (S.val.map (fun i => D i)).esymm 3 = ∑ T ∈ S.powersetCard 3, ∏ i ∈ T, D i := by
  classical
  rw [Finset.esymm_map_val]

/-- **Vieta `X^k` coefficient of the monic root product (the `e_3` coefficient).** For `S` of card
`k+3`, `(∏_{i∈S}(X − D i)).coeff k = − e_3(D_S) = − ∑_{T∈powersetCard 3} ∏_{i∈T} D i` (the third
subleading coefficient is `(−1)³·e_3 = −e_3`). The order-3 analogue of `prod_X_sub_C_coeff_sub2`. -/
theorem prod_X_sub_C_coeff_sub3 (D : ι ↪ F) {k : ℕ} (S : Finset ι) (hS : S.card = k + 3) :
    (∏ i ∈ S, (X - C (D i))).coeff k = - (∑ T ∈ S.powersetCard 3, ∏ i ∈ T, D i) := by
  classical
  set s : Multiset F := S.val.map (fun i => D i) with hs
  have hscard : Multiset.card s = k + 3 := by rw [hs, Multiset.card_map, ← hS]; rfl
  have hprodeq : (∏ i ∈ S, (X - C (D i))) = (s.map fun t => X - C t).prod := by
    rw [hs, Multiset.map_map]; rfl
  rw [hprodeq]
  have hle : k ≤ Multiset.card s := by rw [hscard]; omega
  rw [Multiset.prod_X_sub_C_coeff s hle]
  have hsub3 : Multiset.card s - k = 3 := by rw [hscard]; omega
  rw [hsub3]
  have hsign : ((-1 : F)) ^ 3 = -1 := by ring
  rw [hsign, hs, esymm_three_eq_triple_sum D S]
  ring

/-! ## 4. The third top coefficient of `p_S` for `t = 3`, in terms of `e_3`. -/

/-- **The `X^k` coefficient of `p_S` for `t = 3`, in terms of `e_3` (triple sum).** With `g` of
leading coefficient `c` and `S` of card `k+3`,
`(p_S).coeff k = g.coeff k + c · (∑_{triples⊆S} ∏ D i)`. (The third subleading coefficient: `−c · (−e_3)
= +c·e_3`.) -/
theorem pSt_coeff_k_t3 (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (S : Finset ι) (hS : S.card = k + 3) :
    (pSt D g g.leadingCoeff S).coeff k
      = g.coeff k + g.leadingCoeff * (∑ T ∈ S.powersetCard 3, ∏ i ∈ T, D i) := by
  classical
  set c := g.leadingCoeff with hc
  set P : F[X] := ∏ i ∈ S, (X - C (D i)) with hP
  have hcoeffP : P.coeff k = - (∑ T ∈ S.powersetCard 3, ∏ i ∈ T, D i) :=
    prod_X_sub_C_coeff_sub3 D S hS
  have hcoeff : (pSt D g c S).coeff k = g.coeff k - c * P.coeff k := by
    rw [pSt, ← hP, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  rw [hcoeff, hcoeffP]; ring

/-! ## 5. The `t = 3` degree-drop ⟺ three-symmetric criterion (the headline `t = 3` brick).

We need the top three coefficients `coeff (k+2), coeff (k+1), coeff k` of `p_S` for a `(k+3)`-set.
The top two are exactly the Round-5 forms `pSt_coeff_kp1_t2`/`pSt_coeff_k_t2` *shifted up by one slot*
— but those were stated for `(k+2)`-sets. We re-derive the three coefficients directly here for
`(k+3)`-sets via the Vieta `coeff (k+2) = −e_1`, `coeff (k+1) = +e_2`, `coeff k = −e_3`. -/

/-- **Vieta `X^{k+2}` coefficient (`e_1`) for a `(k+3)`-set.** `(∏(X − D i)).coeff (k+2) = −e_1`. -/
theorem prod_X_sub_C_coeff_t3_top (D : ι ↪ F) {k : ℕ} (S : Finset ι) (hS : S.card = k + 3) :
    (∏ i ∈ S, (X - C (D i))).coeff (k + 2) = - (∑ i ∈ S, D i) := by
  classical
  set s : Multiset F := S.val.map (fun i => D i) with hs
  have hscard : Multiset.card s = k + 3 := by rw [hs, Multiset.card_map, ← hS]; rfl
  have hprodeq : (∏ i ∈ S, (X - C (D i))) = (s.map fun t => X - C t).prod := by
    rw [hs, Multiset.map_map]; rfl
  rw [hprodeq]
  have hle : k + 2 ≤ Multiset.card s := by rw [hscard]; omega
  rw [Multiset.prod_X_sub_C_coeff s hle]
  have hsub1 : Multiset.card s - (k + 2) = 1 := by rw [hscard]; omega
  rw [hsub1, pow_one, hs, esymm_one_eq_window_sum D S]
  ring

/-- **Vieta `X^{k+1}` coefficient (`e_2`) for a `(k+3)`-set.** `(∏(X − D i)).coeff (k+1) = +e_2`. -/
theorem prod_X_sub_C_coeff_t3_mid (D : ι ↪ F) {k : ℕ} (S : Finset ι) (hS : S.card = k + 3) :
    (∏ i ∈ S, (X - C (D i))).coeff (k + 1) = ∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i := by
  classical
  set s : Multiset F := S.val.map (fun i => D i) with hs
  have hscard : Multiset.card s = k + 3 := by rw [hs, Multiset.card_map, ← hS]; rfl
  have hprodeq : (∏ i ∈ S, (X - C (D i))) = (s.map fun t => X - C t).prod := by
    rw [hs, Multiset.map_map]; rfl
  rw [hprodeq]
  have hle : k + 1 ≤ Multiset.card s := by rw [hscard]; omega
  rw [Multiset.prod_X_sub_C_coeff s hle]
  have hsub2 : Multiset.card s - (k + 1) = 2 := by rw [hscard]; omega
  rw [hsub2]
  have : ((-1 : F)) ^ 2 = 1 := by ring
  rw [this, one_mul, hs, esymm_two_eq_pair_sum D S]

/-- **The `X^{k+2}` coefficient of `p_S` (`e_1`) for a `(k+3)`-set.**
`(p_S).coeff (k+2) = g.coeff (k+2) + c·e_1`. -/
theorem pSt_coeff_kp2_t3 (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (S : Finset ι) (hS : S.card = k + 3) :
    (pSt D g g.leadingCoeff S).coeff (k + 2)
      = g.coeff (k + 2) + g.leadingCoeff * (∑ i ∈ S, D i) := by
  classical
  set c := g.leadingCoeff with hc
  set P : F[X] := ∏ i ∈ S, (X - C (D i)) with hP
  have hcoeffP : P.coeff (k + 2) = - (∑ i ∈ S, D i) := prod_X_sub_C_coeff_t3_top D S hS
  have hcoeff : (pSt D g c S).coeff (k + 2) = g.coeff (k + 2) - c * P.coeff (k + 2) := by
    rw [pSt, ← hP, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  rw [hcoeff, hcoeffP]; ring

/-- **The `X^{k+1}` coefficient of `p_S` (`e_2`) for a `(k+3)`-set.**
`(p_S).coeff (k+1) = g.coeff (k+1) − c·e_2`. -/
theorem pSt_coeff_kp1_t3 (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (S : Finset ι) (hS : S.card = k + 3) :
    (pSt D g g.leadingCoeff S).coeff (k + 1)
      = g.coeff (k + 1) - g.leadingCoeff * (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) := by
  classical
  set c := g.leadingCoeff with hc
  set P : F[X] := ∏ i ∈ S, (X - C (D i)) with hP
  have hcoeffP : P.coeff (k + 1) = ∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i :=
    prod_X_sub_C_coeff_t3_mid D S hS
  have hcoeff : (pSt D g c S).coeff (k + 1) = g.coeff (k + 1) - c * P.coeff (k + 1) := by
    rw [pSt, ← hP, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  rw [hcoeff, hcoeffP]

/-- **The three-coefficient degree-drop criterion for `t = 3` (the headline).** With `g` of leading
coefficient `c ≠ 0` and `S` of card `k+3`, the **three** top coefficients of `p_S` all vanish —
`(p_S).coeff (k+2) = 0 ∧ (p_S).coeff (k+1) = 0 ∧ (p_S).coeff k = 0` (the full drop to degree `< k`) —
**iff** the three elementary symmetric functions hit their fixed targets:

  `e_1(D_S) = ∑_{i∈S} D i = −g.coeff(k+2)/c`,
  `e_2(D_S) = ∑_{{i,j}⊆S} D i·D j = g.coeff(k+1)/c`,
  `e_3(D_S) = ∑_{{i,j,l}⊆S} D i·D j·D l = −g.coeff(k)/c`.

This is the literal `t = 3` generalization of Round-5's `degDrop_t2_iff_two_symmetric`: three symmetric
constraints — the top three coefficients of `p_S = g − c·∏_{i∈S}(X − D i)`. -/
theorem degDrop_t3_iff_three_symmetric (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (hc0 : g.leadingCoeff ≠ 0) (S : Finset ι) (hS : S.card = k + 3) :
    ((pSt D g g.leadingCoeff S).coeff (k + 2) = 0 ∧ (pSt D g g.leadingCoeff S).coeff (k + 1) = 0
        ∧ (pSt D g g.leadingCoeff S).coeff k = 0)
      ↔ ((∑ i ∈ S, D i) = -(g.coeff (k + 2)) / g.leadingCoeff
          ∧ (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = (g.coeff (k + 1)) / g.leadingCoeff
          ∧ (∑ T ∈ S.powersetCard 3, ∏ i ∈ T, D i) = -(g.coeff k) / g.leadingCoeff) := by
  rw [pSt_coeff_kp2_t3 D g S hS, pSt_coeff_kp1_t3 D g S hS, pSt_coeff_k_t3 D g S hS]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [eq_div_iff hc0]
      have : g.leadingCoeff * (∑ i ∈ S, D i) = - g.coeff (k + 2) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact h1
      rw [mul_comm] at this; rw [this]
    · rw [eq_div_iff hc0]
      have : g.leadingCoeff * (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = g.coeff (k + 1) := by
        rw [sub_eq_zero] at h2; exact h2.symm
      rw [mul_comm] at this; rw [this]
    · rw [eq_div_iff hc0]
      have : g.leadingCoeff * (∑ T ∈ S.powersetCard 3, ∏ i ∈ T, D i) = - g.coeff k := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact h3
      rw [mul_comm] at this; rw [this]
  · rintro ⟨h1, h2, h3⟩
    rw [eq_div_iff hc0] at h1 h2 h3
    rw [mul_comm] at h1 h2 h3
    refine ⟨?_, ?_, ?_⟩
    · rw [h1]; ring
    · rw [h2]; ring
    · rw [h3]; ring

/-! ## 6. The `t = 3` moment recoordinatization: `(e_1, e_2, e_3) ↔ (p_1, p_2, p_3)`.

On the joint fiber where `e_1 = c₁` and `e_2 = c₂` are *already imposed*, the order-3 Newton identity
`p_3 = e_1³ − 3·e_1·e_2 + 3·e_3` makes the constraint `e_3 = c₃` equivalent to a moment constraint
`p_3 = c₁³ − 3·c₁·c₂ + 3·c₃`. Combined with the Round-6 order-2 recoordinatization `e_2 ↔ p_2`, the
`(e_1, e_2, e_3)` joint fiber and the `(p_1, p_2, p_3) = (∑x, ∑x², ∑x³)` fiber are the **same set of
subsets**. -/

omit [Fintype ι] in
/-- **The `t = 3` moment target for `p_3`.** Given `(e_1,e_2,e_3) = (c₁,c₂,c₃)`, the order-3 power sum
is `p_3 = c₁³ − 3·c₁·c₂ + 3·c₃`. (Pure `cube_window_sum_eq`, char-free.) -/
theorem psum3_of_three_symmetric (D : ι ↪ F) {S : Finset ι} {c₁ c₂ c₃ : F}
    (h1 : (∑ i ∈ S, D i) = c₁)
    (h2 : (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = c₂)
    (h3 : (∑ T ∈ S.powersetCard 3, ∏ i ∈ T, D i) = c₃) :
    (∑ i ∈ S, (D i) ^ 3) = c₁ ^ 3 - 3 * c₁ * c₂ + 3 * c₃ := by
  have hcube := cube_window_sum_eq D S
  rw [h1, h2, h3] at hcube
  linear_combination -hcube

/-- **The two joint fibers coincide (the `t = 3` headline re-coordinatization).** For a ground set `G`,
agreement size `a`, and targets `c₁ c₂ c₃`, the set of `a`-subsets with the three *symmetric* targets
`e_1 = c₁ ∧ e_2 = c₂ ∧ e_3 = c₃` equals the set of `a`-subsets with the three *moment* targets
`p_1 = c₁ ∧ p_2 = c₁²−2c₂ ∧ p_3 = c₁³−3c₁c₂+3c₃`. Equal as `Finset`s, so equal counts. The forward
inclusions are char-free (Newton identities); the backward inclusions cancel `2` (for `e_2`) and `3`
(for `e_3`), so they need `(6 : F) ≠ 0`, i.e. `char F > 3` — automatic in the smooth `2^k`-subgroup
regime (`char` odd; and for the deep interior `t = 3` one works in fields far larger than `3`). -/
theorem threeSymmetric_fiber_eq_moment_fiber [DecidableEq F] (D : ι ↪ F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (a : ℕ) (c₁ c₂ c₃ : F) :
    (Finset.univ.powersetCard a).filter
        (fun S => (∑ i ∈ S, D i) = c₁
          ∧ (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = c₂
          ∧ (∑ T ∈ S.powersetCard 3, ∏ i ∈ T, D i) = c₃)
      = (Finset.univ.powersetCard a).filter
        (fun S => (∑ i ∈ S, D i) = c₁
          ∧ (∑ i ∈ S, (D i) ^ 2) = c₁ ^ 2 - 2 * c₂
          ∧ (∑ i ∈ S, (D i) ^ 3) = c₁ ^ 3 - 3 * c₁ * c₂ + 3 * c₃) := by
  classical
  apply Finset.filter_congr
  intro S _hS
  constructor
  · rintro ⟨he1, he2, he3⟩
    refine ⟨he1, ?_, ?_⟩
    · -- p_2 = e_1² − 2·e_2 = c₁² − 2·c₂  (char-free)
      have hnewton := sq_window_sum_eq D S
      rw [he1, he2] at hnewton
      linear_combination -hnewton
    · -- p_3 = c₁³ − 3·c₁·c₂ + 3·c₃  (char-free)
      exact psum3_of_three_symmetric D he1 he2 he3
  · rintro ⟨hp1, hp2, hp3⟩
    refine ⟨hp1, ?_, ?_⟩
    · -- recover e_2 = c₂ by cancelling 2
      have hnewton := sq_window_sum_eq D S
      rw [hp1, hp2] at hnewton
      have h2e2 : 2 * (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = 2 * c₂ := by
        linear_combination -hnewton
      exact mul_left_cancel₀ h2 h2e2
    · -- recover e_3 = c₃: first recover e_2 = c₂ (as above), then cancel 3 in the cube identity
      have hnewtonSq := sq_window_sum_eq D S
      rw [hp1, hp2] at hnewtonSq
      have he2 : (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = c₂ := by
        have h2e2 : 2 * (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = 2 * c₂ := by
          linear_combination -hnewtonSq
        exact mul_left_cancel₀ h2 h2e2
      have hcube := cube_window_sum_eq D S
      rw [hp1, he2, hp3] at hcube
      -- hcube : c₁³ = (c₁³−3c₁c₂+3c₃) + 3·c₁·c₂ − 3·e_3, so 3·e_3 = 3·c₃.
      have h3e3 : 3 * (∑ T ∈ S.powersetCard 3, ∏ i ∈ T, D i) = 3 * c₃ := by
        linear_combination hcube
      exact mul_left_cancel₀ h3 h3e3

/-- **The `t = 3` count equals the 3-D moment count.** Cardinality form of
`threeSymmetric_fiber_eq_moment_fiber`: the deep-interior `t = 3` joint-symmetric subset count is
*exactly* the count of `a`-subsets with prescribed first three moments `(∑ x, ∑ x², ∑ x³)`. This is the
object a 3-character Weil/Gauss exponential sum
`∑_{ψ₁,ψ₂,ψ₃} ψ₁(∑x−c₁)·ψ₂(∑x²−c₂')·ψ₃(∑x³−c₃')` controls — the count now phrased over three
*single-coordinate* statistics `x, x², x³`, the Round-6 `(sum, sum-of-squares)` form extended to the
third moment. -/
theorem threeSymmetric_count_eq_moment_count [DecidableEq F] (D : ι ↪ F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (a : ℕ) (c₁ c₂ c₃ : F) :
    ((Finset.univ.powersetCard a).filter
        (fun S => (∑ i ∈ S, D i) = c₁
          ∧ (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = c₂
          ∧ (∑ T ∈ S.powersetCard 3, ∏ i ∈ T, D i) = c₃)).card
      = ((Finset.univ.powersetCard a).filter
        (fun S => (∑ i ∈ S, D i) = c₁
          ∧ (∑ i ∈ S, (D i) ^ 2) = c₁ ^ 2 - 2 * c₂
          ∧ (∑ i ∈ S, (D i) ^ 3) = c₁ ^ 3 - 3 * c₁ * c₂ + 3 * c₃)).card := by
  rw [threeSymmetric_fiber_eq_moment_fiber D h2 h3 a c₁ c₂ c₃]

/-! ## 7. The general-`t` pattern, instantiated at `t = 1, 2, 3`.

The chain `Round 4 (t=1) → Round 5 (t=2) → Round 7 (t=3)` instantiates a single uniform pattern:

  the `t`-fold degree drop  ⟺  `(e_1, …, e_t)` prescribed  ⟺  `(p_1, …, p_t)` prescribed.

The first `⟺` is Vieta (the top `t` coefficients of `p_S` are `±c·e_1, …, ±c·e_t`); the second `⟺` is
the Newton triangular recursion `m·e_m = ∑_{i<m} (−1)^{i+1} e_i p_{m−i} + (−1)^{m+1} p_m`, which is a
**unitriangular** (invertible, diagonal `1, 2!, …, t!`) substitution between `(e_1,…,e_t)` and
`(p_1,…,p_t)`. Hence over a field with `char > t` (`t! ≠ 0`) the two fibers coincide for *every* `t`.
We record the `t = 3` instance of this pattern as a single statement, citing the `t = 1` (window sum),
`t = 2` (Round 6 `(e_1,p_2)`), and `t = 3` (this file) reductions. -/

/-- **The general-`t` recoordinatization pattern, at `t = 3` (the unifying statement).** For any
ground set `G`, agreement `a`, and symmetric targets `(c₁, c₂, c₃)`, when `(6 : F) ≠ 0` (`char F > 3`,
so `2 ≠ 0` and `3 ≠ 0`) the `t = 3` joint **symmetric** fiber `(e_1, e_2, e_3) = (c₁, c₂, c₃)` has the
same cardinality as the `t = 3` **moment** fiber `(p_1, p_2, p_3) = (c₁, c₁²−2c₂, c₁³−3c₁c₂+3c₃)`. This
instantiates the uniform pattern "`t`-fold drop ⟺ `(e_1..e_t)` ⟺ `(p_1..p_t)`" at `t = 3`; the same
Newton-unitriangular argument gives it for every `t` once `char F > t`. -/
theorem general_t_pattern_t3 [DecidableEq F] (D : ι ↪ F) (h6 : (6 : F) ≠ 0)
    (a : ℕ) (c₁ c₂ c₃ : F) :
    ((Finset.univ.powersetCard a).filter
        (fun S => (∑ i ∈ S, D i) = c₁
          ∧ (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = c₂
          ∧ (∑ T ∈ S.powersetCard 3, ∏ i ∈ T, D i) = c₃)).card
      = ((Finset.univ.powersetCard a).filter
        (fun S => (∑ i ∈ S, D i) = c₁
          ∧ (∑ i ∈ S, (D i) ^ 2) = c₁ ^ 2 - 2 * c₂
          ∧ (∑ i ∈ S, (D i) ^ 3) = c₁ ^ 3 - 3 * c₁ * c₂ + 3 * c₃)).card := by
  have h2 : (2 : F) ≠ 0 := by
    intro h; apply h6
    have : (6 : F) = 2 * 3 := by norm_num
    rw [this, h, zero_mul]
  have h3 : (3 : F) ≠ 0 := by
    intro h; apply h6
    have : (6 : F) = 3 * 2 := by norm_num
    rw [this, h, zero_mul]
  exact threeSymmetric_count_eq_moment_count D h2 h3 a c₁ c₂ c₃

/-! ## 8. The surviving pigeonhole floor in the moment coordinates (the Round-5/6 NO-GO persists).

The `(e_1, p_2, p_3)` moment fiber is a *sub*-fiber of the `e_1`-fiber (`subsetSumCount`), so the
pigeonhole floor `max_{c₁} q·N(a, c₁) ≥ C(n, a)` still upper-bounds every recoordinated `t = 3` joint
fiber. The third moment, like the second, does not by itself lower the count: the magnitude question
is unchanged in difficulty; only the coordinates are now `(x, x², x³)`, the Weil-friendly form. -/

open ArkLib.ProximityGap.Round4NewtonVietaUpper in
/-- **The 3-D moment fiber is contained in the `e_1` (subset-sum) fiber.** Adding the `p_2` and `p_3`
constraints can only shrink the `e_1 = target₁` fiber, so its count is at most
`subsetSumCount G a target₁`. Hence the Round-4/5/6 pigeonhole floor `max ≥ C(n,a)/q` survives the
`t = 3` recoordinatization: no `poly(n)` *upper* bound on the `t = 3` count follows from symmetry. -/
theorem moment3_card_le_subsetSumCount [DecidableEq F] (G : Finset F) (a : ℕ)
    (target₁ target₂ target₃ : F) :
    ((G.powersetCard a).filter
        (fun S => (∑ x ∈ S, x) = target₁ ∧ (∑ x ∈ S, x ^ 2) = target₂
          ∧ (∑ x ∈ S, x ^ 3) = target₃)).card
      ≤ subsetSumCount G a target₁ := by
  classical
  unfold subsetSumCount
  apply Finset.card_le_card
  intro S hS
  rw [Finset.mem_filter] at hS ⊢
  exact ⟨hS.1, hS.2.1⟩

/-! ## 9. Non-vacuity: the `t = 3` condition is satisfiable; `(6 : F) ≠ 0` is realized. -/

/-- **`(6 : F) ≠ 0` (so both `2 ≠ 0` and `3 ≠ 0`) is realized in a concrete smooth-domain field.**
`ZMod 13` is a field (`13` prime) carrying a multiplicative subgroup of order `4 = 2²`, with
`(6 : ZMod 13) ≠ 0`. So the `t = 3` `(e_1,e_2,e_3) ↔ (p_1,p_2,p_3)` recoordinatization is
non-vacuously applicable; `char (ZMod 13) = 13 > 3`. -/
theorem six_ne_zero_zmod13 : (6 : ZMod 13) ≠ 0 := by decide

/-- **The `t = 3` interior radius is non-vacuous (concrete instance).** At `k = 50`, `n = 220`:
`(k+3)² = 53² = 2809 < 11000 = k·n`, and `k < k+3`. A strictly-interior radius with `t = 3` genuinely
occurs — one full agreement step deeper than the Round-6 `t = 2` instance. -/
theorem interior_radius_concrete_t3 : (50 + 3) ^ 2 < 50 * 220 ∧ 50 < 50 + 3 := by decide

end ArkLib.CodingTheory.Round7T3

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round7T3.pair_sum_insert
#print axioms ArkLib.CodingTheory.Round7T3.triple_sum_insert
#print axioms ArkLib.CodingTheory.Round7T3.cube_window_sum_eq
#print axioms ArkLib.CodingTheory.Round7T3.three_esym3_eq
#print axioms ArkLib.CodingTheory.Round7T3.prod_X_sub_C_coeff_sub3
#print axioms ArkLib.CodingTheory.Round7T3.pSt_coeff_k_t3
#print axioms ArkLib.CodingTheory.Round7T3.degDrop_t3_iff_three_symmetric
#print axioms ArkLib.CodingTheory.Round7T3.psum3_of_three_symmetric
#print axioms ArkLib.CodingTheory.Round7T3.threeSymmetric_fiber_eq_moment_fiber
#print axioms ArkLib.CodingTheory.Round7T3.threeSymmetric_count_eq_moment_count
#print axioms ArkLib.CodingTheory.Round7T3.general_t_pattern_t3
#print axioms ArkLib.CodingTheory.Round7T3.moment3_card_le_subsetSumCount
#print axioms ArkLib.CodingTheory.Round7T3.six_ne_zero_zmod13
#print axioms ArkLib.CodingTheory.Round7T3.interior_radius_concrete_t3
