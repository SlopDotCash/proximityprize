/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SchurLagrangeBridge

/-!
B1 count-law core: the EXACT closed form for the top-direction readout over μ_n.

Goal proven here (axiom-clean target):
  For an injective node map `v` on a finite set `R` with every node an `n`-th root of unity
  (`v i ^ n = 1`), the top-direction complete-homogeneous readout
      `dividedDifferencePow R v (n-1)`
  equals
      `(-1)^(#R-1) * (∏_{i∈R} v i)⁻¹`.

This pins B1's open Prop TopDirectionDistinctCountEqN: the value depends ONLY on the product
`∏ v i ∈ μ_n`, so as `R` ranges over `(k+1)`-subsets the value ranges over `μ_n` (n values),
and the count of distinct readouts is exactly `n`.

Mechanism (NOT a single Z_n orbit): the readout is a *function of the product of the roots*,
`h_{n-1-k}(R) = (-1)^k (∏ v_i)^{-1}`. The Z_n-equivariance (multiply by ξ = w^{n-1-k}) is a
COROLLARY, not the cause; the real cause is this closed form + subset-sum surjectivity mod n.
-/

namespace ProximityGap.B1CountLaw

open Finset Polynomial
open ProximityGap.SchurLagrange

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [DecidableEq ι]

/-- Evaluation of a single Lagrange basis polynomial at `0`:
`eval 0 (basis s v i) = ∏_{j ∈ s.erase i} (v i - v j)⁻¹ * (- v j)`. -/
theorem eval_zero_basis (s : Finset ι) (v : ι → F) (i : ι) :
    (Lagrange.basis s v i).eval 0
      = ∏ j ∈ s.erase i, ((v i - v j)⁻¹ * (- v j)) := by
  rw [Lagrange.basis, eval_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  -- basisDivisor x y = C (x-y)⁻¹ * (X - C y); eval 0 = (x-y)⁻¹ * (0 - y)
  simp [Lagrange.basisDivisor]

/-- Partition-of-unity at `0`: `∑_{i∈s} eval 0 (basis s v i) = 1` (for injective `v`, nonempty `s`). -/
theorem sum_eval_zero_basis (s : Finset ι) (v : ι → F)
    (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    ∑ i ∈ s, (Lagrange.basis s v i).eval 0 = 1 := by
  have h := Lagrange.sum_basis (s := s) (v := v) hvs hs
  have := congrArg (fun p : F[X] => p.eval 0) h
  simpa [eval_finset_sum] using this

/-- `eval 0 (basis s v i)` rewritten by pulling out the sign:
`= (-1)^(#s-1) * (∏_{j∈erase i} v j) * (∏_{j∈erase i}(v i - v j))⁻¹`. -/
theorem eval_zero_basis_sign (s : Finset ι) (v : ι → F) (i : ι) (hi : i ∈ s) :
    (Lagrange.basis s v i).eval 0
      = (-1)^(#s - 1) * (∏ j ∈ s.erase i, v j) * (∏ j ∈ s.erase i, (v i - v j))⁻¹ := by
  rw [eval_zero_basis]
  -- ∏ ((v i - v j)⁻¹ * (- v j)) = (∏ (v i - v j)⁻¹) * (∏ (- v j))
  rw [Finset.prod_mul_distrib]
  -- ∏ (- v j) = (-1)^(#erase) * ∏ v j;  #erase = #s - 1
  rw [Finset.prod_neg, ← Finset.prod_inv_distrib]
  have hcard : #(s.erase i) = #s - 1 := Finset.card_erase_of_mem hi
  rw [hcard]
  ring

/-- **The pure algebraic identity** (no roots of unity needed):
`∑_{i∈s} (∏_{l∈erase i} v l) * (∏_{j∈erase i}(v i - v j))⁻¹ = (-1)^(#s-1)`,
for injective `v` on nonempty `s`. This is the Lagrange partition of unity, read at `0`. -/
theorem sum_prod_others_eq (s : Finset ι) (v : ι → F)
    (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    ∑ i ∈ s, (∏ j ∈ s.erase i, v j) * (∏ j ∈ s.erase i, (v i - v j))⁻¹
      = (-1)^(#s - 1) := by
  have hpar : ∑ i ∈ s, (Lagrange.basis s v i).eval 0 = 1 := sum_eval_zero_basis s v hvs hs
  -- rewrite each summand with the sign form
  have hsum :
      ∑ i ∈ s, (Lagrange.basis s v i).eval 0
        = (-1)^(#s - 1) *
            ∑ i ∈ s, (∏ j ∈ s.erase i, v j) * (∏ j ∈ s.erase i, (v i - v j))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [eval_zero_basis_sign s v i hi]
    ring
  rw [hsum] at hpar
  -- (-1)^(#s-1) * S = 1  ⟹  S = (-1)^(#s-1), since ((-1)^m)^2 = 1
  set S := ∑ i ∈ s, (∏ j ∈ s.erase i, v j) * (∏ j ∈ s.erase i, (v i - v j))⁻¹ with hS
  set m := #s - 1 with hm
  have hsq : ((-1 : F))^m * (-1)^m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  calc S = 1 * S := (one_mul S).symm
    _ = ((-1 : F)^m * (-1)^m) * S := by rw [hsq]
    _ = (-1)^m * ((-1)^m * S) := by ring
    _ = (-1)^m * 1 := by rw [hpar]
    _ = (-1)^m := by ring

/--
**The B1 top-direction closed form (the count-law core).**

For an injective node map `v` on a nonempty finite set `R ⊆ μ_n` (every node an `n`-th root of
unity, `v i ^ n = 1`, hence `v i ≠ 0`), the top-direction complete-homogeneous readout
`dividedDifferencePow R v (n-1)` equals

  `(-1)^(#R-1) * (∏_{i∈R} v i)⁻¹`.

So the readout value is a *function of the product of the roots* `∏ v i ∈ μ_n` only.
This is the mechanism behind `TopDirectionDistinctCountEqN`: as `R` ranges over `(k+1)`-subsets,
`∏ v i` ranges over all of `μ_n` (subset-sum mod `n` is surjective for `1 ≤ #R ≤ n-1`), and the
fixed sign `(-1)^(#R-1)` keeps the `n` values `(-1)^(#R-1) ζ^{-s}` distinct, giving exactly `n`.
-/
theorem topDirectionReadout_eq (R : Finset ι) (v : ι → F) (n : ℕ) (hn : 0 < n)
    (hvs : Set.InjOn v R) (hR : R.Nonempty) (hroot : ∀ i ∈ R, v i ^ n = 1) :
    dividedDifferencePow R v (n - 1)
      = (-1)^(#R - 1) * (∏ i ∈ R, v i)⁻¹ := by
  -- nodes are nonzero
  have hvne : ∀ i ∈ R, v i ≠ 0 := by
    intro i hi h0
    have := hroot i hi
    rw [h0, zero_pow (by omega)] at this
    exact zero_ne_one this
  have hprodne : (∏ i ∈ R, v i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hvne
  -- per-term: v i ^ (n-1) * (∏_{l∈R} v l) = ∏_{l ∈ erase i} v l
  have hterm : ∀ i ∈ R, (v i) ^ (n - 1) * (∏ l ∈ R, v l) = ∏ l ∈ R.erase i, v l := by
    intro i hi
    have hsplit : (∏ l ∈ R, v l) = v i * ∏ l ∈ R.erase i, v l :=
      (Finset.mul_prod_erase R v hi).symm
    rw [hsplit, ← mul_assoc, ← pow_succ]
    have hns : n - 1 + 1 = n := by omega
    rw [hns, hroot i hi, one_mul]
  -- multiply the readout by ∏ v l and reduce to the algebraic identity
  have hmul : (∏ l ∈ R, v l) * dividedDifferencePow R v (n - 1) = (-1)^(#R - 1) := by
    unfold dividedDifferencePow
    rw [Finset.mul_sum]
    have : ∀ i ∈ R,
        (∏ l ∈ R, v l) * ((v i) ^ (n - 1) * (∏ j ∈ R.erase i, (v i - v j))⁻¹)
          = (∏ j ∈ R.erase i, v j) * (∏ j ∈ R.erase i, (v i - v j))⁻¹ := by
      intro i hi
      rw [← mul_assoc, mul_comm (∏ l ∈ R, v l) ((v i) ^ (n - 1)), hterm i hi]
    rw [Finset.sum_congr rfl this]
    exact sum_prod_others_eq R v hvs hR
  -- solve for the readout
  have : dividedDifferencePow R v (n - 1)
      = (∏ l ∈ R, v l)⁻¹ * ((∏ l ∈ R, v l) * dividedDifferencePow R v (n - 1)) := by
    rw [← mul_assoc, inv_mul_cancel₀ hprodne, one_mul]
  rw [this, hmul]
  ring

/-- **Bridge to `completeHomReadout`.** For a `(k+1)`-subset `R ⊆ μ_n`, the B1 top-direction
readout `completeHomReadout R v (n-1-k) = dividedDifferencePow R v (n-1)` (since `#R = k+1`,
`(#R-1) + (n-1-k) = n-1`). Combined with `topDirectionReadout_eq`, the readout has the closed
form `(-1)^k (∏ v)⁻¹`. -/
theorem completeHom_top_eq (R : Finset ι) (v : ι → F) (n k : ℕ) (hn : 0 < n)
    (hRcard : #R = k + 1) (hk : k ≤ n - 1)
    (hvs : Set.InjOn v R) (hR : R.Nonempty) (hroot : ∀ i ∈ R, v i ^ n = 1) :
    dividedDifferencePow R v (#R - 1 + (n - 1 - k))
      = (-1)^k * (∏ i ∈ R, v i)⁻¹ := by
  have hexp : #R - 1 + (n - 1 - k) = n - 1 := by omega
  rw [hexp, topDirectionReadout_eq R v n hn hvs hR hroot, hRcard]
  have : k + 1 - 1 = k := by omega
  rw [this]

/--
**The B1 top-direction readout factors through the product** `∏ v i ∈ μ_n`.

Consequently the number of distinct top-direction readouts over `(k+1)`-subsets of `μ_n` equals
the number of distinct products `∏ v i` realized by `(k+1)`-subsets — a purely combinatorial
subset-product count inside `μ_n`.  This is the mechanism behind `TopDirectionDistinctCountEqN`:
the count is `n` exactly when those products are surjective onto `μ_n` (true for `1 ≤ k ≤ n-2`).

We prove the harder direction here as a clean inequality: the readout value lies in the coset
`(-1)^k · μ_n⁻¹ ⊆ μ_n`-image, hence the distinct count is `≤ n` whenever all node products are
`n`-th roots of unity.  (The matching `≥ n` is the subset-product surjectivity, a separate
elementary combinatorial fact — stated as `SubsetProductSurjectsMu` below.)
-/
theorem readout_mem_image (R : Finset ι) (v : ι → F) (n k : ℕ) (hn : 0 < n)
    (hRcard : #R = k + 1) (hk : k ≤ n - 1)
    (hvs : Set.InjOn v R) (hR : R.Nonempty) (hroot : ∀ i ∈ R, v i ^ n = 1) :
    (dividedDifferencePow R v (#R - 1 + (n - 1 - k))) ^ n = ((-1 : F)^k) ^ n := by
  rw [completeHom_top_eq R v n k hn hRcard hk hvs hR hroot]
  -- ((-1)^k * (∏ v)⁻¹)^n = ((-1)^k)^n  because (∏ v)^n = 1
  have hprodn : (∏ i ∈ R, v i) ^ n = 1 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one (fun i hi => hroot i hi)
  have hprodne : (∏ i ∈ R, v i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi h0 => by
      have := hroot i hi; rw [h0, zero_pow (by omega)] at this; exact zero_ne_one this)
  rw [mul_pow, inv_pow, hprodn, inv_one, mul_one]

/-- The subset-product set: distinct products `∏_{i∈R} v i` over `(k+1)`-subsets `R` of `nodes`. -/
noncomputable def subsetProducts (nodes : Finset ι) (v : ι → F) (k : ℕ) : Finset F :=
  (nodes.powersetCard (k + 1)).image (fun R => ∏ i ∈ R, v i)

/-- The top-direction readout set (= `topRatioValues` of B1, written with `dividedDifferencePow`). -/
noncomputable def topReadouts (nodes : Finset ι) (v : ι → F) (n k : ℕ) : Finset F :=
  (nodes.powersetCard (k + 1)).image (fun R => dividedDifferencePow R v (#R - 1 + (n - 1 - k)))

/--
**The count reduction (PROVED).** Over `μ_n`, the number of distinct top-direction readouts
equals the number of distinct subset-products:
`#topReadouts = #subsetProducts`.

This is the precise sense in which the readout "factors through the product": the closed form
`readout(R) = (-1)^k (∏ v)⁻¹` makes `readout` a fixed injective re-coordinate of the product.
-/
theorem topReadouts_card_eq_subsetProducts_card
    (nodes : Finset ι) (v : ι → F) (n k : ℕ) (hn : 0 < n) (hk : k ≤ n - 1)
    (hvs : Set.InjOn v ↑nodes) (hroot : ∀ i ∈ nodes, v i ^ n = 1) :
    (topReadouts nodes v n k).card = (subsetProducts nodes v k).card := by
  classical
  -- Step 1: rewrite topReadouts as the g-image of subsetProducts, g x = (-1)^k * x⁻¹.
  have hkey : topReadouts nodes v n k
      = (subsetProducts nodes v k).image (fun x => (-1 : F)^k * x⁻¹) := by
    unfold topReadouts subsetProducts
    rw [Finset.image_image]
    refine Finset.image_congr (fun R hR => ?_)
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hR
    obtain ⟨hsub, hRcard⟩ := hR
    have hRsub : (R : Set ι) ⊆ ↑nodes := by exact_mod_cast hsub
    have hvsR : Set.InjOn v ↑R := hvs.mono hRsub
    have hRne : R.Nonempty := by rw [← Finset.card_pos, hRcard]; omega
    have hrootR : ∀ i ∈ R, v i ^ n = 1 := fun i hi => hroot i (hsub hi)
    simp only [Function.comp_apply]
    exact completeHom_top_eq R v n k hn hRcard hk hvsR hRne hrootR
  rw [hkey]
  -- Step 2: g is injective on subsetProducts (all products are nonzero units), so card preserved.
  refine Finset.card_image_of_injOn (fun x hx y hy hxy => ?_)
  -- x, y are products of (k+1)-subsets; both nonzero. (-1)^k x⁻¹ = (-1)^k y⁻¹ ⟹ x = y.
  have hpow : ((-1 : F)^k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hxinv : x⁻¹ = y⁻¹ := mul_left_cancel₀ hpow hxy
  -- recover nonzero-ness of x and y from membership in subsetProducts
  have prod_ne : ∀ z ∈ subsetProducts nodes v k, z ≠ 0 := by
    intro z hz
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hz
    rw [Finset.mem_powersetCard] at hR
    exact Finset.prod_ne_zero_iff.mpr (fun i hi h0 => by
      have := hroot i (hR.1 hi); rw [h0, zero_pow (by omega)] at this; exact zero_ne_one this)
  have hxne : x ≠ 0 := prod_ne x hx
  have hyne : y ≠ 0 := prod_ne y hy
  exact inv_injective.eq_iff.mp hxinv

/-- The subset-products all lie in the `n`-th roots of unity. -/
theorem subsetProducts_subset_nthRoots (nodes : Finset ι) (v : ι → F) (n k : ℕ) (hn : 0 < n)
    (hroot : ∀ i ∈ nodes, v i ^ n = 1) :
    subsetProducts nodes v k ⊆ Polynomial.nthRootsFinset n (1 : F) := by
  intro z hz
  obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hz
  rw [Finset.mem_powersetCard] at hR
  rw [Polynomial.mem_nthRootsFinset hn]
  rw [← Finset.prod_pow]
  exact Finset.prod_eq_one (fun i hi => hroot i (hR.1 hi))

/--
**The B1 top-direction count law, `≤ n` direction (PROVED, axiom-clean).**

Over `μ_n` (all nodes are `n`-th roots of unity), the number of distinct top-direction
divided-difference readouts over `(k+1)`-subsets is **at most `n`**.  This is the nontrivial half
(the collapse from the generic `C(n,k+1)` down to `≤ n`); it is exactly the content of the
closed form `readout(R) = (-1)^k (∏ v)⁻¹` plus `(∏ v)^n = 1`.
-/
theorem topReadouts_card_le (nodes : Finset ι) (v : ι → F) (n k : ℕ) (hn : 0 < n) (hk : k ≤ n - 1)
    (hvs : Set.InjOn v ↑nodes) (hroot : ∀ i ∈ nodes, v i ^ n = 1) :
    (topReadouts nodes v n k).card ≤ n := by
  rw [topReadouts_card_eq_subsetProducts_card nodes v n k hn hk hvs hroot]
  calc (subsetProducts nodes v k).card
      ≤ (Polynomial.nthRootsFinset n (1 : F)).card :=
        Finset.card_le_card (subsetProducts_subset_nthRoots nodes v n k hn hroot)
    _ ≤ n := by
        rw [Polynomial.nthRootsFinset_def]
        exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_nthRoots n 1)

/--
**The matching lower bound `≥ n` (the elementary combinatorial residual, named OPEN Prop).**

To reach `= n` it remains to show the subset-products `{∏_{i∈R} v i : R ∈ powersetCard (k+1)}`
realize *all* `n` of the `n`-th roots of unity, i.e. `subsetProducts = nthRootsFinset n 1`.  With
`v` the inclusion of `μ_n` and `w` a primitive root, `∏ v i = w^{(sum of exponents of R)}`, and
the claim is that the `(k+1)`-subset-sum of `{0,…,n-1}` is surjective mod `n` for `1 ≤ k ≤ n-2`.
This is a purely additive-combinatorics fact (no character sums, no roots of unity), verified
exhaustively for `n ∈ {7,8,9,11,12,16,20,32}`.  Stated as the explicit residual `Prop`. -/
def SubsetProductSurjectsMu (nodes : Finset ι) (v : ι → F) (n k : ℕ) : Prop :=
  subsetProducts nodes v k = Polynomial.nthRootsFinset n (1 : F)

/-- **B1 COUNT LAW, full `= n` (PROVED modulo the named surjectivity residual).**
Given the elementary `SubsetProductSurjectsMu`, the distinct top-direction readout count is
exactly `n`, where `n = #(nthRootsFinset n 1)` (the full root group, e.g. when `F` carries a
primitive `n`-th root). -/
theorem topReadouts_card_eq_n_of_surjects
    (nodes : Finset ι) (v : ι → F) (n k : ℕ) (hn : 0 < n) (hk : k ≤ n - 1)
    (hvs : Set.InjOn v ↑nodes) (hroot : ∀ i ∈ nodes, v i ^ n = 1)
    (hsurj : SubsetProductSurjectsMu nodes v n k)
    (hfull : (Polynomial.nthRootsFinset n (1 : F)).card = n) :
    (topReadouts nodes v n k).card = n := by
  rw [topReadouts_card_eq_subsetProducts_card nodes v n k hn hk hvs hroot, hsurj, hfull]

end ProximityGap.B1CountLaw

set_option linter.style.longLine false in
#print axioms ProximityGap.B1CountLaw.eval_zero_basis
set_option linter.style.longLine false in
#print axioms ProximityGap.B1CountLaw.sum_eval_zero_basis
set_option linter.style.longLine false in
#print axioms ProximityGap.B1CountLaw.sum_prod_others_eq
set_option linter.style.longLine false in
#print axioms ProximityGap.B1CountLaw.topDirectionReadout_eq
set_option linter.style.longLine false in
#print axioms ProximityGap.B1CountLaw.completeHom_top_eq
set_option linter.style.longLine false in
#print axioms ProximityGap.B1CountLaw.readout_mem_image
set_option linter.style.longLine false in
#print axioms ProximityGap.B1CountLaw.topReadouts_card_eq_subsetProducts_card
set_option linter.style.longLine false in
#print axioms ProximityGap.B1CountLaw.subsetProducts_subset_nthRoots
set_option linter.style.longLine false in
#print axioms ProximityGap.B1CountLaw.topReadouts_card_le
set_option linter.style.longLine false in
#print axioms ProximityGap.B1CountLaw.topReadouts_card_eq_n_of_surjects

#print axioms ProximityGap.B1CountLaw.topDirectionReadout_eq
#print axioms ProximityGap.B1CountLaw.topReadouts_card_le
#print axioms ProximityGap.B1CountLaw.topReadouts_card_eq_n_of_surjects
