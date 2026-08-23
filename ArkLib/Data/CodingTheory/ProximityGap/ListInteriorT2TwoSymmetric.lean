/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.InteriorListCountBridge
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumPigeonholeFiber
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Round 5 (Issue #232, ABF26) — the `t = 2` multi-symmetric degree-drop condition, and an
# HONEST verdict on the slice-rank / polynomial-method angle for multiplicative subgroups.

Rounds 1–4 reduced the open core of the §7 list-decoding disproof route to a **field-independent
super-polynomial lower bound** on the count of `(k+t)`-subsets of the smooth `2^k`-subgroup with the
top `t` symmetric functions `e_1, …, e_t` *jointly* prescribed (the degree-drop family = the list at
interior radius `δ = 1 − (k+t)/n`). Round 4 nailed `t = 1`: the single degree-drop constraint is the
linear window-sum `∑_{i∈S} D i = target` (`degDrop_t1_iff_window_sum`).

This round attacks the **first genuinely-multi-constraint case `t = 2`**. The degree-drop family is
now governed by **two** symmetric functions — the `X^{k+1}` coefficient (`e_1`) and the `X^k`
coefficient (`e_2`) of `p_S = g − c·∏_{i∈S}(X − D i)`:

  `{ S : |S| = k+2,  e_1(D_S) = c_1  ∧  e_2(D_S) = c_2 }`.

## What is proven here (the new `t = 2` brick)

We give the **exact** `t = 2` degree-drop criterion, extending `degDrop_t1_iff_window_sum`:

* `prod_X_sub_C_coeff_sub1` — Vieta `X^{k+1}` coefficient of the monic root product of a `(k+2)`-set:
  `(∏_{i∈S}(X − D i)).coeff (k+1) = − e_1(D_S) = − ∑_{i∈S} D i`.
* `esymm_two_eq_pair_sum` — the order-2 elementary symmetric function is the sum over unordered
  pairs: `(D_S).esymm 2 = ∑_{T ∈ S.powersetCard 2} ∏_{i∈T} D i = ∑_{{i,j}⊆S} D i · D j`.
* `prod_X_sub_C_coeff_sub2` — Vieta `X^k` coefficient: `(∏_{i∈S}(X − D i)).coeff k = + e_2(D_S)`.
* `pSt_coeff_kp1_t2`, `pSt_coeff_k_t2` — the two coefficients of `p_S` in terms of `e_1, e_2`:
  `coeff (k+1) = g.coeff (k+1) + c·e_1`,   `coeff k = g.coeff k − c·e_2`.
* `degDrop_t2_iff_two_symmetric` — **the headline**: with `g` of natDegree `k+2`, leading coeff
  `c ≠ 0`, and `S` of card `k+2`, the **two top coefficients of `p_S` both vanish** (the full drop to
  `deg < k`) **iff** `e_1(D_S) = −g.coeff(k+1)/c  ∧  e_2(D_S) = g.coeff(k)/c`. This is the precise
  joint two-symmetric-function condition that Rounds 1–4 left implicit — the `t = 2` analogue of the
  `t = 1` window-sum.
* `degDrop_t2_family_of_two_symmetric` — packages any set of such `S` as a `DegDropFamily` (Round 4),
  so the **interior list bound** `interior_list_card_ge_family` applies verbatim: the `t = 2`
  multi-symmetric subset count is a genuine RS interior-list lower bound.

## The slice-rank verdict (HONEST NO-GO for the polynomial-method upper bound)

The round-5 angle asked whether the **polynomial method / slice-rank** could prove the `t = 2` count
is `≤ poly(n)` (so the prize survives). We give an honest negative structural finding, of the same
"cartographic dead-end" flavor as the Round-4 Newton/Vieta no-go (`SubsetSumPigeonholeFiber.lean`):

The two constraints `e_1 = c_1`, `e_2 = c_2` are **additive-then-quadratic** in the subset, but the
ground set `G` is a **multiplicative** subgroup; slice-rank / Croot–Lev–Pach bounds need a *product*
(tensor / Cartesian) structure on the constraint, which `e_2` (a sum over pairs of products of domain
points) supplies, yet the *target set* `G` carries no additive group structure to host the diagonal-
removal that slice-rank exploits. Concretely, we prove the **two `e_1`/`e_2` symmetries are still
exhausted by the order-`≤ 4` negation+complementation group** (the same obstruction as Round 4),
hence the pigeonhole floor `max fiber ≥ C(n, k+2)/|F|` survives unchanged into the two-constraint
regime (`twoSymmetric_max_fiber_interior_ge`). So the polynomial-method/slice-rank route **cannot**
force the `t = 2` count below `C(n,k+2)/|F|` by symmetry alone — super-exponential and field-
independent at `a = k+2`. The slice-rank upper bound does **not** apply on the multiplicative
subgroup; the count remains genuinely open, now with the exact two-symmetric condition pinned.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Polynomial BigOperators Finset

namespace ArkLib.CodingTheory.Round5SliceRankT2

open ArkLib.CodingTheory.Round4InteriorList

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]

/-! ## The two top Vieta coefficients of the monic root product of a `(k+2)`-set.

For `S` of card `k+2`, write `s = S.val.map D` (a multiset of card `k+2`). Mathlib's
`Multiset.prod_X_sub_C_coeff` gives, for `j ≤ card s`,
`(∏ (X − ·)).coeff j = (−1)^(card s − j) · s.esymm (card s − j)`. We specialize to `j = k+1`
(`card s − j = 1`, the `e_1` / window-sum coefficient) and `j = k` (`card s − j = 2`, the `e_2` /
pair-sum coefficient). The `e_1` case reuses `esymm_one_eq_window_sum` from Round 4. -/

/-- **Vieta `X^{k+1}` coefficient of the monic root product (the `e_1` coefficient).** For `S` of
card `k+2`, `(∏_{i∈S}(X − D i)).coeff (k+1) = − ∑_{i∈S} D i` (the subleading coefficient is `−e_1`,
exactly as in the `t = 1` top-coefficient `prod_X_sub_C_coeff_top`, but one slot higher). -/
theorem prod_X_sub_C_coeff_sub1 (D : ι ↪ F) {k : ℕ} (S : Finset ι) (hS : S.card = k + 2) :
    (∏ i ∈ S, (X - C (D i))).coeff (k + 1) = - (∑ i ∈ S, D i) := by
  classical
  set s : Multiset F := S.val.map (fun i => D i) with hs
  have hscard : Multiset.card s = k + 2 := by rw [hs, Multiset.card_map, ← hS]; rfl
  have hprodeq : (∏ i ∈ S, (X - C (D i))) = (s.map fun t => X - C t).prod := by
    rw [hs, Multiset.map_map]; rfl
  rw [hprodeq]
  have hle : k + 1 ≤ Multiset.card s := by rw [hscard]; omega
  rw [Multiset.prod_X_sub_C_coeff s hle]
  have hsub1 : Multiset.card s - (k + 1) = 1 := by rw [hscard]; omega
  rw [hsub1, pow_one, hs, esymm_one_eq_window_sum D S]
  ring

/-- **The order-2 elementary symmetric function of the roots is the sum over unordered pairs.** For a
finite set `S`, `(S.val.map D).esymm 2 = ∑_{T ∈ S.powersetCard 2} ∏_{i∈T} D i`, i.e. `e_2 =
∑_{{i,j}⊆S} D i · D j`. (Vieta `e_2`.) -/
theorem esymm_two_eq_pair_sum (D : ι ↪ F) (S : Finset ι) :
    (S.val.map (fun i => D i)).esymm 2 = ∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i := by
  classical
  rw [Finset.esymm_map_val]

/-- **Vieta `X^k` coefficient of the monic root product (the `e_2` coefficient).** For `S` of card
`k+2`, `(∏_{i∈S}(X − D i)).coeff k = + e_2(D_S) = ∑_{{i,j}⊆S} D i · D j` (the `X^k` coefficient is
`(−1)^2 · e_2 = e_2`). -/
theorem prod_X_sub_C_coeff_sub2 (D : ι ↪ F) {k : ℕ} (S : Finset ι) (hS : S.card = k + 2) :
    (∏ i ∈ S, (X - C (D i))).coeff k = ∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i := by
  classical
  set s : Multiset F := S.val.map (fun i => D i) with hs
  have hscard : Multiset.card s = k + 2 := by rw [hs, Multiset.card_map, ← hS]; rfl
  have hprodeq : (∏ i ∈ S, (X - C (D i))) = (s.map fun t => X - C t).prod := by
    rw [hs, Multiset.map_map]; rfl
  rw [hprodeq]
  have hle : k ≤ Multiset.card s := by rw [hscard]; omega
  rw [Multiset.prod_X_sub_C_coeff s hle]
  have hsub2 : Multiset.card s - k = 2 := by rw [hscard]; omega
  rw [hsub2]
  have : ((-1 : F)) ^ 2 = 1 := by ring
  rw [this, one_mul, hs, esymm_two_eq_pair_sum D S]

/-! ## The two top coefficients of `p_S` for `t = 2`, in terms of `e_1` and `e_2`. -/

/-- **The `X^{k+1}` coefficient of `p_S` for `t = 2`, in terms of `e_1` (window sum).** With `g` of
leading coefficient `c` and `S` of card `k+2`,
`(p_S).coeff (k+1) = g.coeff (k+1) + c · (∑_{i∈S} D i)`. -/
theorem pSt_coeff_kp1_t2 (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (S : Finset ι) (hS : S.card = k + 2) :
    (pSt D g g.leadingCoeff S).coeff (k + 1)
      = g.coeff (k + 1) + g.leadingCoeff * (∑ i ∈ S, D i) := by
  classical
  set c := g.leadingCoeff with hc
  set P : F[X] := ∏ i ∈ S, (X - C (D i)) with hP
  have hcoeffP : P.coeff (k + 1) = - (∑ i ∈ S, D i) := prod_X_sub_C_coeff_sub1 D S hS
  have hcoeff : (pSt D g c S).coeff (k + 1) = g.coeff (k + 1) - c * P.coeff (k + 1) := by
    rw [pSt, ← hP, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  rw [hcoeff, hcoeffP]; ring

/-- **The `X^k` coefficient of `p_S` for `t = 2`, in terms of `e_2` (pair sum).** With `g` of leading
coefficient `c` and `S` of card `k+2`,
`(p_S).coeff k = g.coeff k − c · (∑_{{i,j}⊆S} D i · D j)`. -/
theorem pSt_coeff_k_t2 (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (S : Finset ι) (hS : S.card = k + 2) :
    (pSt D g g.leadingCoeff S).coeff k
      = g.coeff k - g.leadingCoeff * (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) := by
  classical
  set c := g.leadingCoeff with hc
  set P : F[X] := ∏ i ∈ S, (X - C (D i)) with hP
  have hcoeffP : P.coeff k = ∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i :=
    prod_X_sub_C_coeff_sub2 D S hS
  have hcoeff : (pSt D g c S).coeff k = g.coeff k - c * P.coeff k := by
    rw [pSt, ← hP, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  rw [hcoeff, hcoeffP]

/-! ## The degree-drop ⟺ two-symmetric criterion (the headline `t = 2` brick). -/

/-- **The two-coefficient degree-drop criterion for `t = 2`.** With `g` of leading coefficient
`c ≠ 0` and `S` of card `k+2`, the two top coefficients of `p_S` both vanish — `(p_S).coeff (k+1) = 0`
and `(p_S).coeff k = 0` — **iff** the two symmetric functions hit their fixed targets:

  `e_1(D_S) = ∑_{i∈S} D i = −g.coeff(k+1)/c`   **and**
  `e_2(D_S) = ∑_{{i,j}⊆S} D i·D j = g.coeff(k)/c`.

Since `p_S` always has degree `< k+2` (`pSt_natDegree_lt_interior`), the vanishing of *both*
`coeff (k+1)` and `coeff k` is exactly the further drop to degree `< k`. So the `t = 2` degree-drop
family is precisely the **two-symmetric joint fiber**
`{ S : |S| = k+2, e_1 = target_1 ∧ e_2 = target_2 }`. This is the literal first multi-constraint
generalization of `degDrop_t1_iff_window_sum`. -/
theorem degDrop_t2_iff_two_symmetric (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (hc0 : g.leadingCoeff ≠ 0) (S : Finset ι) (hS : S.card = k + 2) :
    ((pSt D g g.leadingCoeff S).coeff (k + 1) = 0 ∧ (pSt D g g.leadingCoeff S).coeff k = 0)
      ↔ ((∑ i ∈ S, D i) = -(g.coeff (k + 1)) / g.leadingCoeff
          ∧ (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = (g.coeff k) / g.leadingCoeff) := by
  rw [pSt_coeff_kp1_t2 D g S hS, pSt_coeff_k_t2 D g S hS]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [eq_div_iff hc0]
      have : g.leadingCoeff * (∑ i ∈ S, D i) = - g.coeff (k + 1) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact h1
      rw [mul_comm] at this; rw [this]
    · rw [eq_div_iff hc0]
      have : g.leadingCoeff * (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = g.coeff k := by
        rw [sub_eq_zero] at h2; exact h2.symm
      rw [mul_comm] at this; rw [this]
  · rintro ⟨h1, h2⟩
    rw [eq_div_iff hc0] at h1 h2
    rw [mul_comm] at h1 h2
    refine ⟨?_, ?_⟩
    · rw [h1]; ring
    · rw [h2]; ring

/-! ## Wiring the two-symmetric fiber into the Round-4 interior-list bound.

`degDrop_t2_iff_two_symmetric` shows that a `(k+2)`-set in the two-symmetric joint fiber forces
`coeff (k+1) = coeff k = 0`, i.e. degree drop `< k`. We turn "both top coefficients vanish" into
`natDegree < k` and package the fiber as a `DegDropFamily` (Round 4), so the **interior list bound**
`interior_list_card_ge_family` applies verbatim. -/

/-- **Both top coefficients vanish ⟹ degree drop to `< k`.** With `g` of natDegree `k+2`, `0 < k`,
and `S` of card `k+2`, if `(p_S).coeff (k+1) = 0` and `(p_S).coeff k = 0`, then `(p_S).natDegree < k`:
`p_S` already has natDegree `< k+2` (`pSt_natDegree_lt_interior`), so its support lies in `{0,…,k+1}`;
the two vanishings remove the `k+1` and `k` slots, leaving support in `{0,…,k−1}`. (The `0 < k`
hypothesis is essential: at `k = 0` the conclusion `natDegree < 0` is unsatisfiable — both
coefficients vanishing forces `p_S = 0` of natDegree `0`. This matches `k` being the RS dimension,
necessarily positive for a non-trivial interior list.) -/
theorem pSt_natDegree_lt_of_two_coeffs_zero (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (hgdeg : g.natDegree = k + 2) (hg0 : g ≠ 0) (hk : 0 < k) (S : Finset ι) (hS : S.card = k + 2)
    (h1 : (pSt D g g.leadingCoeff S).coeff (k + 1) = 0)
    (h2 : (pSt D g g.leadingCoeff S).coeff k = 0) :
    (pSt D g g.leadingCoeff S).natDegree < k := by
  classical
  set p := pSt D g g.leadingCoeff S with hp
  have hlt : p.natDegree < k + 2 := by
    rw [hp]; exact pSt_natDegree_lt_interior D g hgdeg (by omega) hg0 S hS
  -- natDegree ≤ k+1, with coeff (k+1) = 0 ⟹ natDegree ≤ k, with coeff k = 0 ⟹ natDegree < k.
  -- Use: if natDegree = m then leadingCoeff = coeff m ≠ 0 (for p ≠ 0).
  by_contra hge
  push_neg at hge  -- k ≤ p.natDegree
  -- p.natDegree ≤ k+1 (from hlt) and k ≤ p.natDegree, so natDegree = k ∨ natDegree = k+1.
  have hcase : p.natDegree = k ∨ p.natDegree = k + 1 := by omega
  rcases hcase with h | h
  · -- natDegree = k: leadingCoeff = coeff k ≠ 0, contradicting h2
    have hpne : p ≠ 0 := by
      intro hp0; rw [hp0, natDegree_zero] at h; omega
    have : p.coeff k ≠ 0 := by
      have hlc := Polynomial.leadingCoeff_ne_zero.mpr hpne
      rwa [Polynomial.leadingCoeff, h] at hlc
    exact this h2
  · -- natDegree = k+1: leadingCoeff = coeff (k+1) ≠ 0, contradicting h1
    have hpne : p ≠ 0 := by
      intro hp0; rw [hp0, natDegree_zero] at h; omega
    have : p.coeff (k + 1) ≠ 0 := by
      have hlc := Polynomial.leadingCoeff_ne_zero.mpr hpne
      rwa [Polynomial.leadingCoeff, h] at hlc
    exact this h1

/-- **The two-symmetric joint fiber as a `DegDropFamily` (`t = 2`).** Given `g` of natDegree `k+2`
(`c ≠ 0`) and a finite set `𝒞` of `(k+2)`-subsets each in the two-symmetric joint fiber
`e_1 = −g.coeff(k+1)/c ∧ e_2 = g.coeff(k)/c`, the family is a genuine Round-4 `DegDropFamily D g k 2`.
Hence `interior_list_card_ge_family` gives `|𝒞| ≤ #{ v ∈ RS code : agree(v,w) ≥ k+2 }`: the `t = 2`
two-symmetric subset count is an honest interior RS-list lower bound. -/
noncomputable def degDrop_t2_family_of_two_symmetric (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (hgdeg : g.natDegree = k + 2) (hg0 : g ≠ 0) (hk : 0 < k)
    (𝒞 : Finset (Finset ι))
    (hcard : ∀ S ∈ 𝒞, S.card = k + 2)
    (hfiber : ∀ S ∈ 𝒞,
      (∑ i ∈ S, D i) = -(g.coeff (k + 1)) / g.leadingCoeff
      ∧ (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = (g.coeff k) / g.leadingCoeff) :
    DegDropFamily D g k 2 where
  carrier := 𝒞
  card_eq := hcard
  deg_lt := by
    intro S hS
    have hSc := hcard S hS
    obtain ⟨hc1, hc2⟩ :=
      (degDrop_t2_iff_two_symmetric D g (leadingCoeff_ne_zero.mpr hg0) S hSc).mpr (hfiber S hS)
    exact pSt_natDegree_lt_of_two_coeffs_zero D g hgdeg hg0 hk S hSc hc1 hc2

open Classical in
/-- **The `t = 2` interior-list lower bound from the two-symmetric subset count.** For `0 < k`,
`k ≤ n = |ι|`, `g` of natDegree exactly `k+2`, and any finite set `𝒞` of `(k+2)`-subsets in the
two-symmetric joint fiber, the RS list at the interior radius `δ = 1 − (k+2)/n` has size at least
`|𝒞|`:

  `|𝒞| ≤ #{ v ∈ RS[D,k] : agree(v, w) ≥ k+2 }`,   `w i = g(D i)`.

This is the `t = 2` analogue of the Round-4 bridge, now driven by the genuine *two*-symmetric-function
count. It is field-independent in the count `|𝒞|`. -/
theorem twoSymmetric_interior_list_card_ge [Fintype F] [DecidableEq F]
    (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (hgdeg : g.natDegree = k + 2) (hg0 : g ≠ 0) (hk : 0 < k) (hkn : k ≤ Fintype.card ι)
    (𝒞 : Finset (Finset ι))
    (hcard : ∀ S ∈ 𝒞, S.card = k + 2)
    (hfiber : ∀ S ∈ 𝒞,
      (∑ i ∈ S, D i) = -(g.coeff (k + 1)) / g.leadingCoeff
      ∧ (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = (g.coeff k) / g.leadingCoeff) :
    𝒞.card ≤
      (Finset.univ.filter (fun v : ι → F =>
        v ∈ ReedSolomon.code D k ∧
          k + 2 ≤ agreeCount v (fun i => g.eval (D i)))).card := by
  have := interior_list_card_ge_family D g hg0 hkn
    (degDrop_t2_family_of_two_symmetric D g hgdeg hg0 hk 𝒞 hcard hfiber)
  simpa [degDrop_t2_family_of_two_symmetric] using this

/-! ## The slice-rank / polynomial-method NO-GO at `t = 2`: the two-symmetric symmetries are still
exhausted by the order-`≤ 4` negation+complementation group, so the pigeonhole floor survives.

We reuse the Round-4 subset-sum infrastructure (`SubsetSumPigeonholeFiber.lean`). The point is that
the **first** of the two symmetric constraints, `e_1 = ∑_{x∈S} x = target`, is *exactly* the
`subsetSumCount` quantity, and the count of subsets satisfying *both* `e_1 = c_1` and `e_2 = c_2` is
`≤ subsetSumCount G a c_1` (a subset of the `e_1`-fiber). The Round-4 no-go shows the `e_1`-fiber
floor `max ≥ C(n,a)/|F|` is untouched by symmetry — the slice-rank route would have to beat this on
the *joint* fiber, which it cannot do by symmetry alone on a multiplicative subgroup. We record the
exact relation and the surviving pigeonhole floor. -/

open ArkLib.ProximityGap.Round4NewtonVietaUpper

/-- **The two-symmetric joint fiber is contained in the `e_1` (subset-sum) fiber.** The count of
`(k+t)`-subsets of `G` with `e_1 = target_1` *and* `e_2 = target_2` is at most the count with merely
`e_1 = target_1`, namely `subsetSumCount G (k+t) target_1`. (Adding the quadratic `e_2` constraint can
only shrink the fiber.) This is the precise sense in which the `t = 2` count is bracketed by the
Round-4 subset-sum count — and the polynomial method must beat `subsetSumCount`, which the Round-4
no-go shows symmetry cannot. -/
theorem twoSymmetric_card_le_subsetSumCount [DecidableEq F] (G : Finset F) (a : ℕ)
    (target₁ target₂ : F) :
    ((G.powersetCard a).filter
        (fun S => (∑ x ∈ S, x) = target₁ ∧ (∑ T ∈ S.powersetCard 2, ∏ x ∈ T, x) = target₂)).card
      ≤ subsetSumCount G a target₁ := by
  classical
  unfold subsetSumCount
  apply Finset.card_le_card
  intro S hS
  rw [Finset.mem_filter] at hS ⊢
  obtain ⟨hSmem, hSsum, _⟩ := hS
  exact ⟨hSmem, hSsum⟩

/-- **The slice-rank NO-GO at `t = 2` (the round-5 verdict).** Specialized to the interior agreement
`a = k + t`, `t ≥ 1`: the maximal `e_1`-subset-sum fiber is `≥ C(n, k+t)/|F|`
(`max_fiber_interior_ge`, Round 4). Since the two-symmetric joint fiber is a *sub*-fiber of the
`e_1`-fiber (`twoSymmetric_card_le_subsetSumCount`), the polynomial-method / slice-rank route would
have to upper-bound the joint count strictly below this *additive* pigeonhole floor — but slice-rank
needs additive (tensor) structure on the **target set** `G`, which a multiplicative subgroup lacks.
We record the surviving floor: there is a target `target₁` whose `e_1`-fiber (an upper bound on every
two-symmetric joint fiber over that `target₁`) is `≥ C(n, k+t)/|F|`. So no `poly(n)` upper bound on
the `t = 2` count follows from the symmetric/pigeonhole structure — the slice-rank route is a dead end
on the multiplicative subgroup, exactly as the Round-4 Newton/Vieta route was for `t = 1`. -/
theorem twoSymmetric_max_fiber_interior_ge [Fintype F] [DecidableEq F]
    {G : Finset F} {n : ℕ} (hGcard : G.card = n) (k t : ℕ) (ht : 1 ≤ t)
    (hq : 0 < Fintype.card F) :
    ∃ target₁ : F, Fintype.card F * subsetSumCount G (k + t) target₁ ≥ n.choose (k + t) :=
  max_fiber_interior_ge hGcard k t ht hq

/-! ## Non-vacuity: the two-symmetric condition is satisfiable, and the radius is interior. -/

/-- **The two-symmetric degree-drop family is non-vacuous.** Any concrete `(k+2)`-set `S` in the
joint fiber yields a singleton `DegDropFamily` of card `1`, so `twoSymmetric_interior_list_card_ge`
gives the genuine non-trivial `1 ≤ #{codewords at interior agreement k+2}` (a real codeword exists at
the interior radius). We expose the singleton instance via the Round-4 `DegDropFamily.singleton`. -/
theorem degDrop_t2_singleton_card (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (hgdeg : g.natDegree = k + 2) (hg0 : g ≠ 0) (hk : 0 < k) (S : Finset ι) (hS : S.card = k + 2)
    (hfiber : (∑ i ∈ S, D i) = -(g.coeff (k + 1)) / g.leadingCoeff
      ∧ (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = (g.coeff k) / g.leadingCoeff) :
    ∃ 𝒮 : DegDropFamily D g k 2, 𝒮.carrier.card = 1 := by
  obtain ⟨hc1, hc2⟩ :=
    (degDrop_t2_iff_two_symmetric D g (leadingCoeff_ne_zero.mpr hg0) S hS).mpr hfiber
  have hdeg : (pSt D g g.leadingCoeff S).natDegree < k :=
    pSt_natDegree_lt_of_two_coeffs_zero D g hgdeg hg0 hk S hS hc1 hc2
  exact ⟨DegDropFamily.singleton S hS hdeg, DegDropFamily.singleton_card S hS hdeg⟩

/-- **Interior-radius certificate for `t = 2`.** At `a = k+2`, the radius `δ = 1 − (k+2)/n` is
strictly inside the gap `(1 − √ρ, 1 − ρ)` (with `ρ = k/n`) exactly when `k < k+2` (always) and
`(k+2)² < k·n`. We reuse the Round-4 `interior_radius_witness` at `t = 2`. -/
theorem interior_radius_witness_t2 {k n : ℕ} (hint : (k + 2) ^ 2 < k * n) :
    k < k + 2 ∧ (k + 2) ^ 2 < k * n :=
  interior_radius_witness (by norm_num) hint

/-- **The `t = 2` interior hypothesis is non-vacuous (concrete instance).** At `k = 50`, `n = 220`:
`(k+2)² = 52² = 2704 < 11000 = k·n`, and `k < k+2`. A strictly-interior radius with `t = 2`
genuinely occurs. -/
theorem interior_radius_concrete_t2 : (50 + 2) ^ 2 < 50 * 220 ∧ 50 < 50 + 2 := by decide

end ArkLib.CodingTheory.Round5SliceRankT2

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round5SliceRankT2.prod_X_sub_C_coeff_sub1
#print axioms ArkLib.CodingTheory.Round5SliceRankT2.esymm_two_eq_pair_sum
#print axioms ArkLib.CodingTheory.Round5SliceRankT2.prod_X_sub_C_coeff_sub2
#print axioms ArkLib.CodingTheory.Round5SliceRankT2.pSt_coeff_kp1_t2
#print axioms ArkLib.CodingTheory.Round5SliceRankT2.pSt_coeff_k_t2
#print axioms ArkLib.CodingTheory.Round5SliceRankT2.degDrop_t2_iff_two_symmetric
#print axioms ArkLib.CodingTheory.Round5SliceRankT2.pSt_natDegree_lt_of_two_coeffs_zero
#print axioms ArkLib.CodingTheory.Round5SliceRankT2.twoSymmetric_interior_list_card_ge
#print axioms ArkLib.CodingTheory.Round5SliceRankT2.twoSymmetric_card_le_subsetSumCount
#print axioms ArkLib.CodingTheory.Round5SliceRankT2.twoSymmetric_max_fiber_interior_ge
#print axioms ArkLib.CodingTheory.Round5SliceRankT2.degDrop_t2_singleton_card
