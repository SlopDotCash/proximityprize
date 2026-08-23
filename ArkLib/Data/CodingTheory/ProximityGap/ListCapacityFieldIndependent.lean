/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# A field-independent list-decoding lower bound at the capacity radius (Proximity Prize, #232)

This file attacks the **near-capacity list-decoding lower bound** for an explicit Reed–Solomon code
`C = RS[F, domain, k]` and pushes it down from "the MCA radius `1`" / "`δ = capacity − 1/n`" to a
clean *direct list-decoding* statement at the **capacity radius itself** (`δ = 1 − ρ`), with a list
size that is **field-independent**: `C(n, k)`.

## Why this is a different mechanism from the existing near-capacity bricks

* `MCANearCapacityGeneralRate.lean` (window interpolation) realizes a *spread of bad MCA scalars* of
  size `O(n)`–`O(n²)`, but only for the **MCA** quantity and at `δ = 1 − (k+1)/n`. It is field-
  independent but only linear/quadratic in `n`.
* `CandidateSubsetSumLowerLoop50/53.lean` (roots of unity) gives a *super-exponential* list, but it
  is **field-capped** (`subsetSumset_card_le_field`): the values live in `F_p`, so the bound is
  useless once the domain is large under `|F| < 2^256`.

This file's construction gives a **super-exponential** list (`C(n, k) ≈ 2^n/√n` at rate `1/2`) that
is **NOT field-capped**: the list members are *distinct codewords* of `C ⊆ Fⁿ`, and the count
`C(n, k)` is a pure combinatorial count of `k`-subsets of the domain, independent of `|F|`. This is
the honest, field-independent form of the near-capacity list lower bound the literature establishes.

## The construction (root-set interpolation)

Fix any polynomial `g` of degree **exactly** `k` (leading coefficient `c ≠ 0`); the received word is
`w i = g(D i)`. For each `k`-subset `S ⊆ ι` of the evaluation domain, define
`p_S := g − c · ∏_{i ∈ S} (X − D i)`.
* `p_S` has degree `< k`: both `g` and `c · ∏` have `Xᵏ`-coefficient `c`, so they cancel
  (`Wpoly_degree_lt_capacity`).
* `p_S` agrees with `g` on `S`: the product vanishes on `S`, so `p_S(D i) = g(D i) = w i`
  (`pS_eval_eq_on_S`). Hence the codeword `c_S` agrees with `w` on the `k` coordinates `S`.
* `S ↦ c_S` is **injective**: distinct `k`-subsets give distinct degree-`< k` polynomials (distinct
  root sets, `D` injective), and distinct degree-`< k` polynomials give distinct codewords on the
  `n ≥ k` injective domain (`Polynomial.eq_of_natDegree_lt_card_of_eval_eq`).

Therefore the list of codewords agreeing with `w` on `≥ k` coordinates has size `≥ C(n, k)`, at the
relative agreement `k/n = ρ`, i.e. the decoding radius `δ = 1 − ρ` — the **capacity endpoint** of the
open gap `(1 − √ρ, 1 − ρ)`.

## Honest scope (the obstruction)

`δ = 1 − ρ` is the *capacity endpoint*, not the *interior* `(1 − √ρ, 1 − ρ)`. Pushing the same
construction to agreement `k + t` (i.e. `δ = 1 − (k+t)/n`, strictly inside the gap) requires `t`
extra leading coefficients of `p_S` to cancel; for `t = 1` this is the single linear condition
`∑_{i ∈ S} D i = −g_{k}/c` on the window sum. The list size then becomes
`#{(k+1)-subsets S ⊆ L : ∑ S = target}`, a **subset-sum count on the smooth domain** — which is
field-independent but whose super-polynomial growth on a *smooth* (multiplicative-subgroup) domain is
exactly the open question (`CandidateSubsetSumLowerLoop50` only controls it in char 0 / via field-
capped roots of unity). So this file pins the capacity *endpoint* with a clean field-independent
super-exponential list, and reduces the *interior* to a smooth-domain subset-sum count — it does not
close the interior.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Polynomial BigOperators Finset

namespace ArkLib.CodingTheory.CapacityLowerSharpen

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]

/-- The root-set codeword polynomial for a `k`-subset `S` and a degree-`k` word polynomial `g` with
leading coefficient `c`:  `p_S = g − c · ∏_{i ∈ S} (X − D i)`. -/
noncomputable def pS (D : ι ↪ F) (g : F[X]) (c : F) (S : Finset ι) : F[X] :=
  g - C c * ∏ i ∈ S, (X - C (D i))

/-- `p_S` agrees with `g` (the received word) on every coordinate of `S`: the product vanishes on
`S`, so `p_S(D i) = g(D i)`. -/
theorem pS_eval_eq_on_S (D : ι ↪ F) (g : F[X]) (c : F) (S : Finset ι)
    {i : ι} (hi : i ∈ S) :
    (pS D g c S).eval (D i) = g.eval (D i) := by
  have hvanish : (∏ j ∈ S, (X - C (D j))).eval (D i) = 0 := by
    rw [eval_prod]; exact Finset.prod_eq_zero hi (by simp)
  rw [pS, eval_sub, eval_mul, eval_C, hvanish, mul_zero, sub_zero]

/-- **Degree drop at capacity.** If `g` has degree exactly `k` with leading coefficient `c`, then
`p_S = g − c · ∏_{i ∈ S}(X − D i)` has degree `< k` for every `k`-subset `S`: both `g` and
`c · ∏` are degree-`k` with the same leading coefficient `c`, so the top coefficients cancel. -/
theorem pS_degree_lt_capacity (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (hgdeg : g.natDegree = k) (hk : 0 < k) (hg0 : g ≠ 0) (S : Finset ι) (hS : S.card = k) :
    (pS D g g.leadingCoeff S).degree < (k : ℕ) := by
  set c := g.leadingCoeff with hc
  set P : F[X] := ∏ i ∈ S, (X - C (D i)) with hP
  -- `P` is monic of degree `k`.
  have hPmonic : P.Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (D i))
  have hPnatdeg : P.natDegree = k := by
    rw [hP, natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (D i))]; simp [hS]
  -- `c • P = c * P` has degree `k`, leading coeff `c`.
  have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr hg0
  have hcP_natdeg : (C c * P).natDegree = k := by
    rw [natDegree_C_mul hc0, hPnatdeg]
  have hcP_lead : (C c * P).leadingCoeff = c := hPmonic.leadingCoeff_C_mul c
  -- `g` and `C c * P` have equal degree `k` and equal leading coeff `c`; subtract.
  have hg_natdeg : g.natDegree = k := hgdeg
  have hdeg_eq : g.degree = (C c * P).degree := by
    rw [degree_eq_natDegree hg0, degree_eq_natDegree (by
      rw [← leadingCoeff_ne_zero, hcP_lead]; exact hc0), hg_natdeg, hcP_natdeg]
  have hlead_eq : g.leadingCoeff = (C c * P).leadingCoeff := by rw [hcP_lead, hc]
  have hsub : (g - C c * P).degree < g.degree :=
    Polynomial.degree_sub_lt hdeg_eq hg0 hlead_eq
  rw [degree_eq_natDegree hg0, hg_natdeg] at hsub
  show (g - C c * ∏ i ∈ S, (X - C (D i))).degree < (k : ℕ)
  rw [← hP]; exact hsub

/-- The natDegree-`< k` version of `pS_degree_lt_capacity`. -/
theorem pS_natDegree_lt_capacity (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (hgdeg : g.natDegree = k) (hk : 0 < k) (hg0 : g ≠ 0) (S : Finset ι) (hS : S.card = k) :
    (pS D g g.leadingCoeff S).natDegree < k := by
  have h := pS_degree_lt_capacity D g hgdeg hk hg0 S hS
  by_cases h0 : pS D g g.leadingCoeff S = 0
  · rw [h0, natDegree_zero]; exact hk
  · rwa [Polynomial.natDegree_lt_iff_degree_lt h0]

/-- The two root products are equal as polynomials iff the subsets are equal (`D` injective). -/
theorem prod_X_sub_C_injOn_subsets (D : ι ↪ F) {k : ℕ} {S T : Finset ι}
    (hS : S.card = k) (hT : T.card = k)
    (hprod : (∏ i ∈ S, (X - C (D i))) = ∏ i ∈ T, (X - C (D i))) :
    S = T := by
  classical
  -- Roots of `∏_{i∈S}(X − D i)` are exactly `{D i : i ∈ S}`; equal products ⟹ equal root sets.
  apply Finset.eq_of_subset_of_card_le _ (by rw [hS, hT])
  intro x hxS
  -- `D x` is a root of the `S`-product, hence (by `hprod`) of the `T`-product, hence `D x ∈ D '' T`.
  have hxroot : (∏ i ∈ T, (X - C (D i))).eval (D x) = 0 := by
    rw [← hprod, eval_prod]; exact Finset.prod_eq_zero hxS (by simp)
  rw [eval_prod] at hxroot
  obtain ⟨j, hjT, hj⟩ := Finset.prod_eq_zero_iff.mp hxroot
  rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hj
  rw [D.injective hj]; exact hjT

/-- **Injectivity of the root-set codeword map.** Distinct `k`-subsets give distinct codewords.
The polynomials `p_S` differ (their root products differ, `D` injective), and two distinct
degree-`< k` polynomials evaluate differently on the `n ≥ k` injective domain. -/
theorem pS_codeword_injOn (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (hgdeg : g.natDegree = k) (hk : 0 < k) (hg0 : g ≠ 0) (hkn : k ≤ Fintype.card ι) :
    Set.InjOn (fun S : Finset ι => fun i => (pS D g g.leadingCoeff S).eval (D i))
      (((Finset.univ : Finset ι).powersetCard k : Finset (Finset ι)) : Set (Finset ι)) := by
  classical
  intro S hS T hT hfun
  rw [Finset.mem_coe, Finset.mem_powersetCard] at hS hT
  obtain ⟨_, hS⟩ := hS
  obtain ⟨_, hT⟩ := hT
  -- From equal codewords, deduce equal polynomials `p_S = p_T` (both natDegree `< k ≤ n`).
  have hSdeg : (pS D g g.leadingCoeff S).natDegree < Fintype.card ι :=
    lt_of_lt_of_le (pS_natDegree_lt_capacity D g hgdeg hk hg0 S hS) hkn
  have hTdeg : (pS D g g.leadingCoeff T).natDegree < Fintype.card ι :=
    lt_of_lt_of_le (pS_natDegree_lt_capacity D g hgdeg hk hg0 T hT) hkn
  have heval : ∀ i : ι, (pS D g g.leadingCoeff S).eval (D i)
      = (pS D g g.leadingCoeff T).eval (D i) := fun i => congrFun hfun i
  have hpoly : pS D g g.leadingCoeff S = pS D g g.leadingCoeff T :=
    Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ D.injective heval (by
      rw [max_lt_iff]; exact ⟨hSdeg, hTdeg⟩)
  -- `g − c·∏_S = g − c·∏_T ⟹ ∏_S = ∏_T` (cancel `g`, divide by `c ≠ 0`).
  have hc0 : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
  have hprodCmul : C g.leadingCoeff * ∏ i ∈ S, (X - C (D i))
      = C g.leadingCoeff * ∏ i ∈ T, (X - C (D i)) := by
    have h := hpoly
    rw [pS, pS, sub_right_inj] at h
    exact h
  have hCne : (C g.leadingCoeff : F[X]) ≠ 0 := by
    rwa [Ne, Polynomial.C_eq_zero]
  have hprod : (∏ i ∈ S, (X - C (D i))) = ∏ i ∈ T, (X - C (D i)) :=
    mul_left_cancel₀ hCne hprodCmul
  exact prod_X_sub_C_injOn_subsets D hS hT hprod

section ListBound

variable [Fintype F] [DecidableEq F]

open Classical in
/-- The agreement count (number of coordinates where two words coincide). -/
noncomputable def agreeCount (x y : ι → F) : ℕ :=
  (Finset.univ.filter (fun i => x i = y i)).card

/-- Each root-set codeword `c_S = (i ↦ p_S(D i))` agrees with the received word `w = (i ↦ g(D i))`
on at least `k` coordinates (exactly the `k` coordinates of `S`). -/
theorem pS_agreeCount_ge (D : ι ↪ F) (g : F[X]) (c : F) {k : ℕ}
    (S : Finset ι) (hS : S.card = k) :
    k ≤ agreeCount (fun i => (pS D g c S).eval (D i)) (fun i => g.eval (D i)) := by
  classical
  rw [agreeCount]
  refine le_trans (le_of_eq hS.symm) (Finset.card_le_card ?_)
  intro i hi
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ i, pS_eval_eq_on_S D g c S hi⟩

open Classical in
/-- **Field-independent near-capacity list lower bound (capacity endpoint).**
Let `C = RS[F, domain, k]` with `0 < k ≤ n = |ι|`, and let `g` be a polynomial of degree *exactly*
`k` with received word `w i = g(D i)`. Then the list of codewords of `C` agreeing with `w` on at
least `k` coordinates (relative agreement `k/n = ρ`, i.e. decoding radius `δ = 1 − ρ`) has
cardinality at least `C(n, k)`:

`C(n, k) ≤ #{ v ∈ C : agree(v, w) ≥ k }`.

The list members are the distinct codewords `c_S` for the `C(n, k)` many `k`-subsets `S ⊆ ι`; the
count is a pure combinatorial subset count, **independent of `|F|`** (unlike the field-capped
roots-of-unity lower bound `subsetSumset_card_le_field`). -/
theorem list_card_ge_choose_at_capacity (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (hgdeg : g.natDegree = k) (hk : 0 < k) (hg0 : g ≠ 0) (hkn : k ≤ Fintype.card ι) :
    (Fintype.card ι).choose k ≤
      (Finset.univ.filter (fun v : ι → F =>
        v ∈ ReedSolomon.code D k ∧
          k ≤ agreeCount v (fun i => g.eval (D i)))).card := by
  classical
  set w : ι → F := fun i => g.eval (D i) with hw
  set Φ : Finset ι → (ι → F) :=
    fun S => fun i => (pS D g g.leadingCoeff S).eval (D i) with hΦ
  -- The image of the `k`-subsets under `Φ` lands inside the list filter.
  have hmaps : ∀ S ∈ (Finset.univ : Finset ι).powersetCard k,
      Φ S ∈ Finset.univ.filter (fun v : ι → F =>
        v ∈ ReedSolomon.code D k ∧ k ≤ agreeCount v w) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    obtain ⟨_, hScard⟩ := hS
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · -- `Φ S` is a codeword (deg `< k` polynomial evaluation).
      refine ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval (pS D g g.leadingCoeff S)
        (by exact_mod_cast pS_degree_lt_capacity D g hgdeg hk hg0 S hScard) (fun i => rfl)
    · -- `Φ S` agrees with `w` on `≥ k` coordinates.
      exact pS_agreeCount_ge D g g.leadingCoeff S hScard
  -- `Φ` is injective on the `k`-subsets, so the image has the full `C(n, k)` cardinality.
  have hinj : Set.InjOn Φ ((Finset.univ : Finset ι).powersetCard k : Set (Finset ι)) :=
    pS_codeword_injOn D g hgdeg hk hg0 hkn
  calc (Fintype.card ι).choose k
      = ((Finset.univ : Finset ι).powersetCard k).card := by
        rw [Finset.card_powersetCard, Finset.card_univ]
    _ = (((Finset.univ : Finset ι).powersetCard k).image Φ).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card (by
          intro v hv
          rw [Finset.mem_image] at hv
          obtain ⟨S, hSmem, rfl⟩ := hv
          exact hmaps S hSmem)

end ListBound

end ArkLib.CodingTheory.CapacityLowerSharpen

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.CapacityLowerSharpen.pS_eval_eq_on_S
#print axioms ArkLib.CodingTheory.CapacityLowerSharpen.pS_degree_lt_capacity
#print axioms ArkLib.CodingTheory.CapacityLowerSharpen.pS_codeword_injOn
#print axioms ArkLib.CodingTheory.CapacityLowerSharpen.list_card_ge_choose_at_capacity
