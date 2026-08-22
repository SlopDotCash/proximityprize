/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G88CrossOrbitFirstIncidence

/-!
# G181: the dyadic antipodal kernel floor — a thinness-essential, `q`-independent lower
bound on the deep-wall kernel-class mass `S₀ = repRF g n r 0`

## Context

G88 (`_G88CrossOrbitFirstIncidence.lean`) reduces the deep prize wall to the orbit-class
`ℓ²`-profile `(S₀, (S_γ)_γ)` and proves the **kernel floor**
`kernel_sq_le_centeredShadowMass`:
`q·S₀² − n^{2r} ≤ centeredShadowMass`, so no cross-orbit reshuffling can push the centered
mass below a function of the single kernel-class mass `S₀ = repRF g n r 0` (the number of
depth-`r` root tuples that sum to `0`). G88 explicitly leaves the **size of `S₀`** as the open
arithmetic content of the wall.

This file supplies the missing arithmetic on the thinness-essential side: a **structural lower
bound on `S₀` forced purely by the 2-power torsion `g^m = -1`**, hence unavailable to a generic
(odd-order, non-antipodal) subgroup.

## The mechanism (antipodal cancellation)

For a smooth subgroup `⟨g⟩` of even order `n = 2m` the defining torsion relation is `g^m = -1`
(the unique non-identity square root of one in a field; the G180 brick `pow_half_eq_neg_one`).
Consequently the root set is closed under negation: `g^{j+m} = g^j · g^m = -g^j`. So for the
depth-`2` representation count, the `n` ordered pairs

`t_j = (j, j ⊕ m)`  (second index `j + m` reduced mod `n`),  `j ∈ Fin n`,

each satisfy `gsumR = g^j + g^{j+m} = g^j·(1 + g^m) = g^j·(1 + (-1)) = 0`, and are pairwise
distinct (distinct first coordinate). This injects `Fin n` into the depth-`2` zero-sum fiber:

`n ≤ repRF g n 2 0`  (`n_le_repRF_two_zero`) — holding in **every** characteristic.

Composed with the G88 kernel floor at `r = 2` this yields the thinness-forced, `q`-independent
wall floor

`q·n² − n⁴ ≤ centeredShadowMass g n m 2`  (`dyadic_kernel_floor_two`).

## Why this is genuinely new and thinness-essential

- **Non-Fourier, non-containment**: unlike G99/G180 (arc-containment, total-mass geometry) this
  is a lower bound on the deep-wall *representation-count* profile — the actual CORE object
  (#509), not a covering statement.
- **2-power-essential**: the antipodal injection requires `g^m = -1`. An odd-order subgroup has
  no antipodal partner (`probe_oc_kernel_formula.py`: for odd `n` the depth-`2` kernel mass is
  `q`-dependent and admits no such combinatorial floor; the analogous count is `0`). The floor
  `S₀ ≥ n` is available **only** to the 2-power smooth subgroup.
- **Sharp and scale-invariant against the prize**: at depth `r = 2` the prize target is
  `q·(2·2−1)!!·n² = 3·q·n²`, so the dyadic kernel floor `q·n²` is **exactly one third** of the
  prize ceiling for *every* dyadic `n`, production `n = 2^30` included
  (`probe_oc_dyadic_profile_rigidity.py`). This pins why the wall is genuinely present
  (a constant-fraction floor) yet not self-refuting (`1/3 < 1`): the kernel term alone cannot
  close CORE, matching doctrine v3's "the missing certificate must control the *cross-orbit*
  `ℓ²`-tail, not the kernel".

## Scope (honest)

This is an **unconditional lower bound** on `centeredShadowMass`, i.e. it certifies the wall is
at least a fixed fraction of the prize target; it does **not** provide the *upper* bound the
prize needs (`DCEnergyBound`), which is exactly the cross-orbit `Σ_γ S_γ²` tail G88 isolates and
which carries zero algebraic constraint (doctrine v2). The empirical stabilization
`S₀ = A(n,r)` (the exact antipodal count, `A(n,2)=n`, `A(n,4)=3n(n-1)`) for `p` past a
saturation threshold `p*` is measured but **not** claimed here (accidental char-`p` zero-sums
below `p*` inflate `S₀`; only the unconditional `≥` direction is proved). CORE remains OPEN /
ON-BGK. The value is the exact, kernel-checked, thinness-forced constant on the *floor* side of
the wall.

Issue #509. Target axiom set: `[propext, Classical.choice, Quot.sound]`.

Probes: `scripts/probes/probe_oc_dyadic_profile_rigidity.py`,
`scripts/probes/probe_oc_kernel_mass_dyadic.py`, `scripts/probes/probe_oc_kernel_formula.py`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Finset

namespace ArkLib.ProximityGap.Frontier.G181DyadicKernelFloor

open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.G88CrossOrbitFirstIncidence
open ArkLib.ProximityGap.Frontier.R365CenteredShadowMassWeld

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The antipodal depth-2 zero-sum tuple -/

/-- The depth-`2` root tuple `(j, j + s)` at first index `j : Fin n`, shift `s : Fin n` (second
index reduced mod `n` via `Fin` addition).  Taking `s` the half-shift `m` gives an antipodal
pair when `g^m = -1`. -/
def antipodalPair {n : ℕ} (s j : Fin n) : Fin 2 → Fin n :=
  fun i => if i = 0 then j else j + s

/-- **The antipodal pair sums to zero.**  With the half-shift `s = ⟨m % n, _⟩`,
`gsumR g n 2 (antipodalPair s j) = g^j + g^{j+m} = g^j·(1 + g^m) = 0` using `g^m = -1`.  Holds in
any characteristic. -/
theorem gsumR_antipodalPair_eq_zero
    (g : F) (n m : ℕ) (hn : n = 2 * m) (hg : g ^ m = -1)
    (j : Fin n) (hnpos : 0 < n) :
    gsumR g n 2 (antipodalPair (⟨m % n, Nat.mod_lt m hnpos⟩) j) = 0 := by
  -- g^m = -1 ⟹ g^(2m) = 1 ⟹ g^n = 1, so g^(k % n) = g^k for all k.
  have hgn : g ^ n = 1 := by
    have h2 : g ^ n = (g ^ m) ^ 2 := by rw [← pow_mul]; congr 1; omega
    rw [h2, hg]; ring
  have hperiod : ∀ k : ℕ, g ^ (k % n) = g ^ k := by
    intro k
    conv_rhs => rw [← Nat.div_add_mod k n, pow_add, pow_mul, hgn, one_pow, one_mul]
  -- second exponent: ((j + ⟨m % n, _⟩ : Fin n) : ℕ) = (↑j + m % n) % n
  have hval : ((j + (⟨m % n, Nat.mod_lt m hnpos⟩ : Fin n) : Fin n) : ℕ) = (↑j + m % n) % n := by
    rw [Fin.val_add]
  -- unfold the two-term sum
  unfold gsumR antipodalPair
  rw [Fin.sum_univ_two]
  rw [if_pos (rfl : (0 : Fin 2) = 0), if_neg (by decide : ¬((1 : Fin 2) = 0))]
  rw [hval, hperiod, pow_add, hperiod, hg]
  ring

/-- **The antipodal map is injective** (in the first index): distinct `j` give distinct tuples. -/
theorem antipodalPair_injective {n : ℕ} (s : Fin n) :
    Function.Injective (antipodalPair s) := by
  intro a b hab
  have h := congrFun hab 0
  simpa [antipodalPair] using h

/-! ## 2. The thinness-forced kernel lower bound -/

/-- **The dyadic antipodal kernel floor (depth 2), unconditional.**  For the smooth subgroup
`⟨g⟩` of even order `n = 2m` with `g^m = -1`, the depth-`2` kernel-class mass `repRF g n 2 0`
counts the tuples summing to `0`, which includes the `n` distinct antipodal pairs
`(j, j+m)`; hence `n ≤ repRF g n 2 0`.  This is the 2-power-essential lower bound the G88 kernel
floor consumes: an odd-order subgroup has no antipodal partner and admits no such `q`-independent
count. -/
theorem n_le_repRF_two_zero
    (g : F) (n m : ℕ) (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    n ≤ repRF g n 2 0 := by
  classical
  have hnpos : 0 < n := by omega
  set s : Fin n := ⟨m % n, Nat.mod_lt m hnpos⟩ with hs
  -- the antipodal pairs form an injective image inside the zero-sum fiber
  have hsub : (Finset.univ.image (antipodalPair s)) ⊆
      (Finset.univ.filter (fun t => gsumR g n 2 t = 0)) := by
    intro t ht
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨j, rfl⟩ := ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact gsumR_antipodalPair_eq_zero g n m hn hg j hnpos
  have hcard : (Finset.univ.image (antipodalPair s)).card = n := by
    rw [Finset.card_image_of_injective _ (antipodalPair_injective s),
      Finset.card_univ, Fintype.card_fin]
  calc n = (Finset.univ.image (antipodalPair s)).card := hcard.symm
    _ ≤ (Finset.univ.filter (fun t => gsumR g n 2 t = 0)).card :=
        Finset.card_le_card hsub
    _ = repRF g n 2 0 := rfl

/-! ## 3. Composition with the G88 wall: the thinness-forced wall floor -/

/-- **The dyadic wall floor (depth 2).**  Combining `n_le_repRF_two_zero` with G88's kernel
floor `kernel_sq_le_centeredShadowMass`, the deep-wall centered mass is bounded below by a
`q`-independent-shape quantity forced by the 2-power torsion:
`q·n² − n⁴ ≤ centeredShadowMass g n m 2`.  Against the depth-`2` prize target `3·q·n²` this is
exactly the constant-fraction (`1/3`) floor: the kernel term alone certifies the wall is present
but cannot close CORE. -/
theorem dyadic_kernel_floor_two
    (g : F) (n m : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    (Fintype.card F : ℝ) * (n : ℝ) ^ 2 - (n : ℝ) ^ 4 ≤
      centeredShadowMass g n m 2 := by
  have hlb : n ≤ repRF g n 2 0 := n_le_repRF_two_zero g n m hm hn hg
  have hlbR : (n : ℝ) ≤ (repRF g n 2 0 : ℝ) := by exact_mod_cast hlb
  have hg88 := kernel_sq_le_centeredShadowMass g n m 2 hg0 hord hm hn hg
  -- q·n² − n⁴ ≤ q·S₀² − n⁴ ≤ centeredShadowMass
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hstep : (Fintype.card F : ℝ) * (n : ℝ) ^ 2 - (n : ℝ) ^ 4 ≤
      (Fintype.card F : ℝ) * (repRF g n 2 0 : ℝ) ^ 2 - (n : ℝ) ^ (2 * 2) := by
    have hsq : (n : ℝ) ^ 2 ≤ (repRF g n 2 0 : ℝ) ^ 2 := by
      apply pow_le_pow_left₀ hnn hlbR
    have : (n : ℝ) ^ (2 * 2) = (n : ℝ) ^ 4 := by norm_num
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hsq hq]
  exact le_trans hstep hg88

end ArkLib.ProximityGap.Frontier.G181DyadicKernelFloor
