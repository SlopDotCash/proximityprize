/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SchurLagrangeBridge
import ArkLib.Research.ProximityGap.Frontier.Issue407SaturatedIncidence
import ArkLib.Research.ProximityGap.Frontier._CompleteHomogeneousReadout

/-!
# B1: the `x^k` far-direction divided-difference ratio form (#407, B-count lane)

## What this file records

For RS over the `n`-th roots of unity `μ_n`, the *far-line incidence* (the EXACT `δ*`
object, `FarCosetExplosion.epsMCA_ge_far_incidence`) at the deepest scale `size = k+1`
is governed by the *divided-difference ratios*

`lambda_R(x^a) / lambda_R(x^k)`

over `(k+1)`-subsets `R ⊆ μ_n`.  The in-tree `dividedDifferencePow` is exactly
`lambda_R(x^a)`, and `completeHomReadout R v j = h_j(R) = lambda_R(x^{|R|-1+j})`
(see `_CompleteHomogeneousReadout.lean`).  Because `lambda_R(x^k) = h_0(R) = 1` for a
`(k+1)`-set, the ratio is just `h_{a-k}(R)`.

## The provable mechanism (this file proves it)

The cyclic group `Z_n` acts on `μ_n` by `z ↦ w·z` (`w` a primitive `n`-th root).  Under a
GLOBAL rescaling of every node by a scalar `c`, the readout transforms covariantly:

`completeHomReadout_smul : h_j(c • v) = c^j · h_j(v)`              (PROVED here)
`dividedDifferencePow_smul : [s](c•v) x^b = c^{b-(#s-1)} · [s]v x^b`   (PROVED here)

This is the engine behind the empirical count law below: rotating `R` by `w` multiplies
`h_{n-1-k}(R)` by `w^{n-1-k} = w^{-(k+1)}`, so the value set is closed under multiplication
by `w^{-(k+1)}`, with no value ever `0`.

## The empirical closed form (stated, NOT proved — named open Props)

Exhaustive enumeration (`probe_farline_incidence_exact`, p-independent across primes
`p ≡ 1 mod n`, verified `n ∈ {7,8,9,11,12,16,20,32}`, all `1 ≤ k ≤ n-2`, ρ ∈ {1/4,1/2,…})
established:

* **TOP direction `a = n-1`** (value `h_{n-1-k}(R)`): the number of DISTINCT ratios is
  **exactly `n`**, p-independent and k-independent.  When `gcd(n,k+1)=1` the `n` fibers are
  PERFECTLY balanced of size `C(n,k+1)/n` (the `Z_n` action on `(k+1)`-subsets is free).
* **Full ratio-vector** `(h_0,…,h_{n-1-k})(R)` is INJECTIVE in `R` (count `= C(n,k+1)`).
* **Bottom direction `a = k`** (`h_0`): the ratio is constant `= 1`.
* **Intermediate directions: no gcd-only refutation is recorded.** An earlier draft claimed the
  intermediate counts are not a function of `gcd(n,a-k)` alone, citing `n=16`, `d=4 ↦ 713` and
  `d=8 ↦ 428`. That comparison does **not** refute a gcd-only law: `gcd(16,4) = 4` and
  `gcd(16,8) = 8` are different inputs, so unequal outputs are compatible with a function of the
  gcd. The claim is retracted; a valid refutation would need two directions with the **same**
  `gcd(n,a-k)` and unequal counts. (Nor is a gcd-only law asserted.) The only clean
  single-direction closed forms recorded here are at the boundaries `a=k` (`=1`) and `a=n-1`
  (`=n`).

These are empirical observations; this file declares no `Prop` for them and no theorem here
proves a count law. (The top-direction count `= n` is proved elsewhere, on the canonical `μ_n`
domain, in `B1TopDirectionCountLaw.lean` / `B1CountLawUnconditional.lean`; see the end of this
file.)

NUMERIC ANCHOR connecting to `δ*`: at the binding scale `size = k+1` (deepest `r = n-k-1`),
`max_far_incidence` equals exactly `n` at the threshold (`n=8,k=2`: `inc=8`; `n=12,k=3`:
`inc=12`), reproducing `δ*(8,2)=3/8`, `δ*(12,3)=5/12` — the established session values.
-/

namespace ProximityGap.Frontier.B1XkIncidenceForm

open Finset
open ProximityGap.SchurLagrange
open ProximityGap.Frontier.CompleteHomogeneousReadout (completeHomReadout)

variable {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]

/-- **Rescaling covariance of the raw divided difference** (the B1 engine).
Globally scaling every node value by `c ≠ 0` multiplies each summand `[term_i]` of `[s] x^b` by
`c^b · (c^{#(s.erase i)})⁻¹ = c^b · (c^{#s-1})⁻¹`.  We state the per-term identity, which is the
content; the global power factor `c^{b-(#s-1)}` then factors out by `Finset.sum`-congruence. -/
theorem dividedDifferencePow_smul_term (s : Finset ι) (v : ι → F) (b : ℕ) (i : ι)
    (hi : i ∈ s) {c : F} (hc : c ≠ 0) :
    (c * v i) ^ b * (∏ j ∈ s.erase i, (c * v i - c * v j))⁻¹
      = c ^ b * (c ^ (#s - 1))⁻¹ * ((v i) ^ b * (∏ j ∈ s.erase i, (v i - v j))⁻¹) := by
  classical
  have hcard : #(s.erase i) = #s - 1 := Finset.card_erase_of_mem hi
  have hprod : (∏ j ∈ s.erase i, (c * v i - c * v j))
      = c ^ (#s - 1) * ∏ j ∈ s.erase i, (v i - v j) := by
    rw [← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    ring
  rw [hprod, mul_pow, mul_inv]
  ring

/-- **Global rescaling covariance of the raw divided difference.**
`[s] (c•v) x^b = c^b · (c^{#s-1})⁻¹ · [s] v x^b`, which equals `c^{b-(#s-1)} · [s]v x^b` when
`b ≥ #s-1`.  Assembles `dividedDifferencePow_smul_term` over the sum. -/
theorem dividedDifferencePow_smul (s : Finset ι) (v : ι → F) (b : ℕ) {c : F} (hc : c ≠ 0) :
    dividedDifferencePow s (fun i => c * v i) b
      = c ^ b * (c ^ (#s - 1))⁻¹ * dividedDifferencePow s v b := by
  classical
  unfold dividedDifferencePow
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  exact dividedDifferencePow_smul_term s v b i hi hc

/-! The complete-homogeneous readout `h_j(R) = λ_R(x^{|R|-1+j})` used below is the shared
adapter definition `ProximityGap.Frontier.CompleteHomogeneousReadout.completeHomReadout`
(`_CompleteHomogeneousReadout.lean`); an earlier local duplicate has been removed. -/

/-- **Readout covariance.** Globally scaling every node by `c ≠ 0` multiplies the
complete-homogeneous readout `h_j` by `c^j`: `h_j(c • v) = c^j h_j(v)`.
(Verified numerically for all sampled `j, c`.)  This is the engine behind the top-direction
count law: rotating `μ_n` by a primitive root `w` sends `h_j ↦ w^j h_j`. -/
theorem completeHomReadout_smul (s : Finset ι) (v : ι → F) (j : ℕ) {c : F} (hc : c ≠ 0)
    (hs : s.Nonempty) :
    completeHomReadout s (fun i => c * v i) j
      = c ^ j * completeHomReadout s v j := by
  classical
  unfold completeHomReadout
  rw [dividedDifferencePow_smul s v (#s - 1 + j) hc]
  have hpos : 1 ≤ #s := Finset.card_pos.mpr hs
  have hpow : c ^ (#s - 1 + j) * (c ^ (#s - 1))⁻¹ = c ^ j := by
    rw [pow_add, mul_comm (c ^ (#s - 1)) (c ^ j), mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hc), mul_one]
  rw [mul_assoc, ← mul_assoc (c ^ (#s - 1 + j)), hpow]

/-! ## The top-direction count law — now PROVED in `B1TopDirectionCountLaw.lean`.

An earlier draft of this file carried a named Prop `TopDirectionDistinctCountEqN` asserting the
distinct top-direction count is `n` for any injective `v` with `#nodes = n`.  That is **false as
stated**: over generic injective `v` the count is `C(n,k+1)`, not `n`; the value `n` genuinely
requires the roots-of-unity hypothesis `v i ^ n = 1`.  The corrected, *proved* statements live in
`ProximityGap.B1CountLaw` (`B1TopDirectionCountLaw.lean`), built on the covariance lemmas above:

* `topDirectionReadout_eq` — the closed form
  `dividedDifferencePow R v (n-1) = (-1)^{#R-1}·(∏ v_i)⁻¹`, which **requires** every node to be an
  `n`-th root of unity (`v i ^ n = 1`). The root-free ingredient is the Lagrange partition of unity
  at `x = 0` (`sum_prod_others_eq`), which gives the reciprocal readout; identifying `X^{n-1}`
  with `1/X` on the nodes uses exactly `v i ^ n = 1`. Without it the formula is false (singleton
  node `2` over `ℚ`, `n = 3`: the left side is `4`, the right side `1/2`);
* `topReadouts_card_le` — the distinct top-direction readout count is `≤ n` (under the same
  root hypothesis, via `subsetProducts_subset_nthRoots`);
* `topReadouts_card_eq_n_of_surjects` — `= n` exactly, conditional on `SubsetProductSurjectsMu`
  (the `(k+1)`-subset sums surject onto `ℤ/n`); that `Prop` is discharged for the canonical domain
  in `B1CountLawUnconditional.lean` (`topReadouts_card_eq_n_unconditional`).

The surjectivity input is additive combinatorics in `(ℤ/n,+)` — structurally distinct from the C1
character-sum wall. (No gcd-only refutation for intermediate directions is recorded: the earlier
`n=16`, `d=4 → 713` vs `d=8 → 428` comparison used different gcds and is retracted.) -/

end ProximityGap.Frontier.B1XkIncidenceForm

#print axioms ProximityGap.Frontier.B1XkIncidenceForm.dividedDifferencePow_smul
#print axioms ProximityGap.Frontier.B1XkIncidenceForm.completeHomReadout_smul
