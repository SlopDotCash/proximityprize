/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Round 4 (Issue #232, §7 / O11 direct attack) — the generating function `∏_{x∈G}(Y − x) = Y^n − 1`,
# the vanishing of all subleading elementary symmetric functions, and exactly what this pins (and
# does *not* pin) about the subset-**sum** count `N(t, target)`.

This file grounds every other §7 angle in the **cleanest exact handle** on a smooth multiplicative
subgroup `G = ⟨ω⟩` of order `n` (the FRI domain, `G = ` the `n`-th roots of unity in a field): the
generating polynomial

  `∏_{x ∈ G} (Y − x) = Y^n − 1`     (`Mathlib.X_pow_sub_one_eq_prod`).

Reading off coefficients (Vieta / `Polynomial.coeff_eq_esymm_roots_of_card`) gives the **complete**
elementary-symmetric profile of `G`:

  `e_0(G) = 1`,   `e_j(G) = 0` for every `0 < j < n`,   `e_n(G) = ±1`.

We formalize the vanishing `e_j(G) = 0` (`esymm_nthRoots_eq_zero`) and re-express it as the genuine
**subset-product** vanishing identity

  `∑_{S ⊆ G, |S| = j} ∏_{x ∈ S} x = 0`     (`subset_prod_sum_eq_zero`, `0 < j < n`)

— an exact, field-structural constraint on the subgroup.

## The crux question this file targets — and the honest verdict

The Round-1..3 reduction pins `δ*` past Johnson to the **subset-SUM** count
`N(t, target) = #{S ⊆ G : |S| = k+t, ∑_{x∈S} x = target}`. The generating function `∏(Y − x)`
controls subset **products** (it is the *multiplicative* generating object), so the honest content
here is twofold.

* **What it pins exactly (the `j = 1` consequence).** `e_1(G) = ∑_{x∈G} x = 0`
  (`subgroup_sum_eq_zero`, `n ≥ 2`). This single additive identity is genuinely about subset *sums*,
  and it forces an **exact complementation symmetry** on the count `N`:

    `N(G, a, target) = N(G, n − a, −target)`     (`Ncount_compl_symm`).

  Specialized to the list-decoding regime `a = k + t`, this reflects agreement `k+t` (the gap
  *interior*) onto agreement `n − k − t`. It is a real, exact, field-independent structural fact
  about `N` — but it is a **symmetry, not a magnitude bound**: it is *invariant* under the
  reflection, so it cannot by itself certify `N` as poly (prize survives) or super-poly (disproof).

* **The verified no-go (why this angle stops here).** Beyond `e_1`, the higher `e_j = 0` say
  *nothing* about `N`: they pin subset *products*, and the subset-product count and the subset-sum
  count `N` are different incidence structures. The total `∑_{target} N(G, a, target) = C(n, a)`
  (`Ncount_total`) is field-independent and fixed, so the *average* fibre has size `C(n,a)/|F|`;
  the open question is purely the **worst-case spread** of `N` over targets, which the symmetric-
  function generating polynomial `Y^n − 1` does not see. So this angle gives an exact symmetry
  reduction of `N` and a clean no-go: the multiplicative generating function is **blind to the
  additive worst-case magnitude of `N(t,·)`**.

## Status

`sorry`-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). Non-vacuous: the hypotheses
are realized by any primitive `n`-th root (e.g. the §7 STARK-domain roots of unity of
`CandidateFiniteFieldDisproofLoop53.lean`); the conclusions are genuine statements about `G` and
`N`, not restatements of `C(n,k)` at `t = 0`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Polynomial BigOperators Finset

namespace ArkLib.ProximityGap.Round4EsymmGenFun

/-! ## 1. The exact symmetric-function profile of the subgroup `G` -/

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **The subleading elementary symmetric functions of the `n`-th roots of unity all vanish.**
For a primitive `n`-th root of unity `ζ ∈ R`, the roots `G = {x : x^n = 1}` satisfy
`e_j(G) = 0` for every `0 < j < n`. This is the coefficient reading of the generating identity
`∏_{x ∈ G}(Y − x) = Y^n − 1` (`X_pow_sub_one_eq_prod`): all coefficients of `Y^n − 1` between the
top `Y^n` and the constant `−1` are zero, and by Vieta the `Y^{n−j}`-coefficient is `(−1)^j e_j(G)`.
The `e_j` are taken on the root multiset `nthRoots n 1` of `G`. -/
theorem esymm_nthRoots_eq_zero {ζ : R} {n : ℕ} (hpos : 0 < n) (h : IsPrimitiveRoot ζ n)
    {j : ℕ} (hj0 : 0 < j) (hjn : j < n) :
    (nthRoots n (1 : R)).esymm j = 0 := by
  -- Work with `p = Y^n − 1`; its roots are exactly `G`, leadingCoeff `1`, `natDegree n`.
  set p : R[X] := X ^ n - C 1 with hp
  have hroots_eq : p.roots = nthRoots n (1 : R) := rfl
  have hnatdeg : p.natDegree = n := natDegree_X_pow_sub_C
  have hcard : Multiset.card p.roots = p.natDegree := by
    rw [hroots_eq, h.card_nthRoots_one, hnatdeg]
  -- Vieta at the coefficient `k = n − j`.
  set k := n - j with hk
  have hkle : k ≤ p.natDegree := by rw [hnatdeg, hk]; omega
  have hcoeff := Polynomial.coeff_eq_esymm_roots_of_card hcard hkle
  have hlead : p.leadingCoeff = 1 := monic_X_pow_sub_C (1 : R) (by omega : n ≠ 0)
  -- The coefficient of `Y^n − 1` at `0 < k < n` is `0`.
  have hcoeff0 : p.coeff k = 0 := by
    rw [hp, coeff_sub, coeff_X_pow, coeff_C]
    rw [if_neg (by omega : ¬ k = n), if_neg (by omega : ¬ k = 0), sub_zero]
  rw [hcoeff0, hlead, one_mul, hnatdeg] at hcoeff
  -- `n − k = j`, and `(−1)^j ≠ 0`, so the `esymm` factor must vanish.
  have hnk : n - k = j := by rw [hk]; omega
  rw [hnk, hroots_eq] at hcoeff
  have hsign : ((-1 : R) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
  rcases mul_eq_zero.mp hcoeff.symm with h1 | h2
  · exact absurd h1 hsign
  · exact h2

/-- **`e_j(G)` as the sum of products over `j`-subsets of `G`.** The `j`-th elementary symmetric
function of the root *multiset* equals the sum, over all `j`-element subsets `S` of the *finset*
`G = nthRootsFinset n 1`, of the product `∏_{x ∈ S} x`. (Uses that the roots are distinct,
`nthRoots_one_nodup`, so the multiset and the finset agree.) -/
theorem esymm_eq_subset_prod_sum {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) (j : ℕ) :
    (nthRoots n (1 : R)).esymm j
      = ∑ S ∈ (nthRootsFinset n (1 : R)).powersetCard j, ∏ x ∈ S, x := by
  classical
  have hval : (nthRootsFinset n (1 : R)).val = nthRoots n (1 : R) := by
    rw [nthRootsFinset, Multiset.toFinset_val]
    exact Multiset.dedup_eq_self.mpr (IsPrimitiveRoot.nthRoots_one_nodup h)
  have hmap := Finset.esymm_map_val (id : R → R) (nthRootsFinset n (1 : R)) j
  simp only [Multiset.map_id', id_eq] at hmap
  rw [hval] at hmap
  rw [← hmap]

/-- **Subset-product vanishing identity (the generating-function brick).** For a primitive `n`-th
root of unity and `0 < j < n`, the sum of products over all `j`-subsets of `G` vanishes:

  `∑_{S ⊆ G, |S| = j} ∏_{x ∈ S} x = 0`.

This is the exact, field-structural constraint that `∏_{x∈G}(Y − x) = Y^n − 1` imposes on `G`. It is
a genuine statement about the subgroup (an abstract finite abelian group of order `n` would *not*
satisfy it); it constrains subset **products**, the multiplicative analogue of the subset-sum count
`N`. -/
theorem subset_prod_sum_eq_zero {ζ : R} {n : ℕ} (hpos : 0 < n) (h : IsPrimitiveRoot ζ n)
    {j : ℕ} (hj0 : 0 < j) (hjn : j < n) :
    ∑ S ∈ (nthRootsFinset n (1 : R)).powersetCard j, ∏ x ∈ S, x = 0 := by
  rw [← esymm_eq_subset_prod_sum h]
  exact esymm_nthRoots_eq_zero hpos h hj0 hjn

/-- **The `j = 1` case: the full-subgroup sum vanishes — `e_1(G) = ∑_{x∈G} x = 0`** (for `n ≥ 2`).
This is the single elementary-symmetric identity that is genuinely *additive* (a sum, not product),
hence the only part of the generating-function profile that speaks directly to the subset-**sum**
count `N`. It is Vieta's subleading coefficient `−e_1` of `Y^n − 1`, which is `0` once `n ≥ 2`. -/
theorem subgroup_sum_eq_zero {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) (hn2 : 2 ≤ n) :
    ∑ x ∈ nthRootsFinset n (1 : R), x = 0 := by
  classical
  have hpos : 0 < n := by omega
  have hprod := subset_prod_sum_eq_zero hpos h (j := 1) (by norm_num) (by omega)
  -- `j = 1`: products over singletons are just the elements.
  rw [Finset.powersetCard_one, Finset.sum_map] at hprod
  simpa using hprod

end ArkLib.ProximityGap.Round4EsymmGenFun

/-! ## 2. The subset-sum count `N` and the exact complementation symmetry from `e_1 = 0` -/

namespace ArkLib.ProximityGap.Round4EsymmGenFun

variable {R : Type*} [DecidableEq R] [CommRing R]

/-- The subgroup **subset-sum count**: the number of `a`-element subsets `S ⊆ G` whose sum is
`target`. With `a = k + t` and `target = −g_k/c`, this is exactly the §7 list-decoding count
`N(t, target)` of the Round-1..3 reduction. -/
noncomputable def Ncount (G : Finset R) (a : ℕ) (target : R) : ℕ := by
  classical
  exact ((G.powersetCard a).filter (fun S => ∑ x ∈ S, x = target)).card

/-- **Exact complementation symmetry of `N`, from `∑_{x∈G} x = 0`.** When the ambient sum vanishes
(true for the subgroup `G`, `subgroup_sum_eq_zero`), complementing `S ↦ G \ S` is a bijection from
the `a`-subsets summing to `target` onto the `(|G| − a)`-subsets summing to `−target`:

  `N(G, a, target) = N(G, |G| − a, −target)`.

Specialized to the list-decoding regime `a = k + t`, this reflects agreement `k+t` (the gap
*interior*) onto agreement `n − k − t`. It is an **exact symmetry**, hence does not by itself bound
the magnitude of `N` (it is invariant under the reflection) — but it is a genuine, field-independent
structural identity on the subset-sum count, available *only* because the subgroup sum is `0`. -/
theorem Ncount_compl_symm (G : Finset R) (a : ℕ) (target : R)
    (hsum : ∑ x ∈ G, x = 0) (ha : a ≤ G.card) :
    Ncount G a target = Ncount G (G.card - a) (-target) := by
  classical
  unfold Ncount
  apply Finset.card_bij (fun S _ => G \ S)
  · -- the complement is an `(|G| − a)`-subset summing to `−target`
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hS ⊢
    obtain ⟨⟨hSsub, hScard⟩, hSsum⟩ := hS
    refine ⟨⟨Finset.sdiff_subset, ?_⟩, ?_⟩
    · rw [Finset.card_sdiff_of_subset hSsub, hScard]
    · have hcompl : ∑ x ∈ G \ S, x = (∑ x ∈ G, x) - ∑ x ∈ S, x :=
        Finset.sum_sdiff_eq_sub hSsub
      rw [hcompl, hsum, hSsum, zero_sub]
  · -- injective: complementation is involutive on subsets of `G`
    intro S1 hS1 S2 hS2 heq
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hS1 hS2
    obtain ⟨⟨h1sub, _⟩, _⟩ := hS1
    obtain ⟨⟨h2sub, _⟩, _⟩ := hS2
    have e1 : G \ (G \ S1) = S1 := Finset.sdiff_sdiff_eq_self h1sub
    have e2 : G \ (G \ S2) = S2 := Finset.sdiff_sdiff_eq_self h2sub
    rw [← e1, ← e2, heq]
  · -- surjective: every `(|G| − a)`-subset `T` summing to `−target` is `G \ (G \ T)`
    intro T hT
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
    obtain ⟨⟨hTsub, hTcard⟩, hTsum⟩ := hT
    refine ⟨G \ T, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.sdiff_subset, ?_⟩, ?_⟩
      · rw [Finset.card_sdiff_of_subset hTsub, hTcard]; omega
      · have hcompl : ∑ x ∈ G \ T, x = (∑ x ∈ G, x) - ∑ x ∈ T, x :=
          Finset.sum_sdiff_eq_sub hTsub
        rw [hcompl, hsum, hTsum, zero_sub, neg_neg]
    · exact Finset.sdiff_sdiff_eq_self hTsub

/-- **The §7-specialized complementation symmetry on the subgroup.** For the smooth subgroup
`G = nthRootsFinset n 1` (a primitive `n`-th root, `n ≥ 2`), the list-decoding subset-sum count at
agreement `a` and target `target` equals the count at agreement `n − a` and target `−target`:

  `N(G, a, target) = N(G, n − a, −target)`.

This is `Ncount_compl_symm` fed the subgroup's own vanishing sum `subgroup_sum_eq_zero`. With
`a = k + t` it is the exact reflection of the *gap-interior* count onto the *complementary*
agreement. -/
theorem Ncount_subgroup_compl_symm {ζ : R} [IsDomain R] {n : ℕ} (h : IsPrimitiveRoot ζ n)
    (hn2 : 2 ≤ n) (a : ℕ) (target : R)
    (ha : a ≤ (nthRootsFinset n (1 : R)).card) :
    Ncount (nthRootsFinset n (1 : R)) a target
      = Ncount (nthRootsFinset n (1 : R)) ((nthRootsFinset n (1 : R)).card - a) (-target) :=
  Ncount_compl_symm _ a target (subgroup_sum_eq_zero h hn2) ha

/-! ## 3. The no-go: the generating function is blind to the worst-case magnitude of `N` -/

variable [Fintype R]

/-- **Total subset-sum count is field-independent: `∑_{target} N(G, a, target) = C(|G|, a)`.**
Summing `N` over *all* targets just recovers the total number of `a`-subsets of `G`, a pure
combinatorial count independent of the field structure. So the *average* fibre size is
`C(|G|, a)/|F|`; the open list-decoding question is entirely the **worst-case spread** of `N` over
targets, i.e. how much one fibre can exceed this average. The symmetric-function generating
polynomial `Y^n − 1` (which pins all subset-*products* and the single additive identity `e_1 = 0`)
sees only this total and the complementation symmetry — **not** the worst-case additive spread. This
is the honest boundary of the generating-function angle: it does not certify whether `N(t, ·)` is
poly (prize survives) or super-poly (disproof). -/
theorem Ncount_total (G : Finset R) (a : ℕ) :
    ∑ target : R, Ncount G a target = (G.card).choose a := by
  classical
  unfold Ncount
  rw [← Finset.card_powersetCard a G]
  exact (Finset.card_eq_sum_card_fiberwise (f := fun S => ∑ x ∈ S, x) (t := Finset.univ)
    (fun S _ => Finset.mem_univ _)).symm

end ArkLib.ProximityGap.Round4EsymmGenFun

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round4EsymmGenFun.esymm_nthRoots_eq_zero
#print axioms ArkLib.ProximityGap.Round4EsymmGenFun.esymm_eq_subset_prod_sum
#print axioms ArkLib.ProximityGap.Round4EsymmGenFun.subset_prod_sum_eq_zero
#print axioms ArkLib.ProximityGap.Round4EsymmGenFun.subgroup_sum_eq_zero
#print axioms ArkLib.ProximityGap.Round4EsymmGenFun.Ncount_compl_symm
#print axioms ArkLib.ProximityGap.Round4EsymmGenFun.Ncount_subgroup_compl_symm
#print axioms ArkLib.ProximityGap.Round4EsymmGenFun.Ncount_total
