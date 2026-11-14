/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Bridge B35 — antipodal pairing kills odd graded moments over `μ_{2n}` (target E6, #444)

**Spec.** *Antipodal pairing kills odd graded moments: the sum over `μ_{2n}` of an
odd-degree graded weight is `0`.* **Approach:** the `−1` involution.

## Context — the odd half of the EXACT FFT-graded recursion E6

The empirical 2-adic self-similarity of the graded obstruction (E6 of
`docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`, verified exactly at
`16 ↔ 8`) has two halves:

* even half  `#bad_{2n}(k, 2m') = #bad_n(k/2, m')`  (a doubling-map fold of subsets), and
* **odd half** `#bad_{2n}(k, m) = 0` for **odd** graded degree `m`.

The odd half is forced by the antipodal element `−1 ∈ μ_{2n}` — present precisely because the
multiplicative subgroup `μ_{2n}` has *even* order `2n`. Multiplication by `−1` is a
fixed-point-free involution of `μ_{2n}`, and an **odd-degree graded weight** `g(x) = c · x^d`
(`d` odd) is *anti-invariant* under it: `g(−x) = c·(−x)^d = (−1)^d·c·x^d = −g(x)`. Pairing each
`x` with `−x` cancels the sum.

## What this file proves (LANDED, axiom-clean — closes the gap named by `_Bridge05`)

`_Bridge05_AntipodalOddVanishing.lean` proved the *abstract* core (`sum_eq_zero_of_antiInvariant`:
any anti-invariant weight sums to zero over an involution-closed fixed-point-free set) but
**explicitly left the concrete connection** "odd graded ⟹ anti-invariant under `x ↦ −x` over
`μ_{2n}`" as an unproved obligation in its docstring. This file **discharges that obligation
concretely**, over any field of characteristic `≠ 2`, on the *actual* root set
`μ_{2n} = nthRootsFinset (2n) 1`:

* `neg_mem_two_mul_nthRootsFinset`  — `μ_{2n}` is closed under `x ↦ −x` (`(−x)^{2n} = x^{2n}`);
* `graded_odd_antiInvariant`         — the odd graded weight `x ↦ c·x^d` is anti-invariant;
* **`odd_graded_moment_eq_zero`**     — `∑_{x ∈ μ_{2n}} c·x^d = 0` for odd `d`  (target X);
* `odd_power_sum_nthRootsFinset_eq_zero` — the `c = 1` special case (odd power sums vanish);
* `Complex.odd_graded_moment_eq_zero` — the prize-regime statement over `ℂ`.

These are characteristic-free identities (`char ≠ 2`); no char-`p` transfer is needed, and the
even-half doubling fold of E6 is a *separate* brick. The connection to the FFT-graded
`#bad` count (that an odd graded frequency component is exactly such a `c·x^d` weight) is the
modeling step that wires this vanishing into E6; the algebra it rests on is fully proved here.

Issue #444.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.BridgeB35

variable {F : Type*} [Field F]

/-- **`μ_{2n}` is antipodally closed.** If `x ∈ nthRootsFinset (2n) 1` then `−x ∈ nthRootsFinset
(2n) 1`, because `(−x)^{2n} = ((−1)^2)^n · x^{2n} = x^{2n} = 1` (the exponent `2n` is even). This is
the structural reason the antipodal involution acts on `μ_{2n}`. -/
theorem neg_mem_two_mul_nthRootsFinset {n : ℕ} (hn : 0 < n) {x : F}
    (hx : x ∈ nthRootsFinset (2 * n) (1 : F)) :
    -x ∈ nthRootsFinset (2 * n) (1 : F) := by
  rw [mem_nthRootsFinset (by positivity) 1] at hx ⊢
  rw [neg_pow, hx]
  have : Even (2 * n) := ⟨n, by ring⟩
  rw [this.neg_one_pow, one_mul]

/-- **`0 ∉ μ_{2n}`.** A root of unity is nonzero (`x^{2n} = 1 ≠ 0`), so `−x ≠ x` on `μ_{2n}` in
characteristic `≠ 2`: the antipodal involution is fixed-point free. -/
theorem ne_zero_of_mem_nthRootsFinset {N : ℕ} (hN : 0 < N) {x : F}
    (hx : x ∈ nthRootsFinset N (1 : F)) : x ≠ 0 := by
  rw [mem_nthRootsFinset hN 1] at hx
  rintro rfl
  rw [zero_pow hN.ne'] at hx
  exact zero_ne_one hx

/-- **Odd graded weight is anti-invariant under the antipode.** For an *odd* degree `d`, the graded
monomial weight `g(x) = c · x^d` satisfies `g(−x) = −g(x)`:
`c·(−x)^d = c·(−1)^d·x^d = −c·x^d`. This is the concrete realization of the abstract
`hanti : f (σ x) = − f x` hypothesis of `_Bridge05.sum_eq_zero_of_antiInvariant`. -/
theorem graded_odd_antiInvariant {d : ℕ} (hd : Odd d) (c : F) (x : F) :
    c * (-x) ^ d = -(c * x ^ d) := by
  rw [hd.neg_pow]; ring

/-- **Antipodal pairing kills odd graded moments (target X).** For every field of characteristic
`≠ 2`, every `n ≥ 1`, every coefficient `c`, and every **odd** graded degree `d`, the graded
moment of degree `d` over `μ_{2n}` vanishes:

  `∑_{x ∈ μ_{2n}} c · x^d = 0`.

The proof is the `−1` involution: pair each `x ∈ μ_{2n}` with `−x ∈ μ_{2n}` (antipodal closure),
which is fixed-point free (`−x ≠ x`, as `x ≠ 0` and `2 ≠ 0`) and an involution (`−(−x) = x`); the
odd weight is anti-invariant (`c·(−x)^d = −c·x^d`), so the two terms in each antipodal pair cancel.
This is the algebraic core of the **odd half** of the EXACT FFT-graded recursion E6,
`#bad_{2n}(k, odd) = 0`. -/
theorem odd_graded_moment_eq_zero (hchar : (2 : F) ≠ 0) {n : ℕ} (hn : 0 < n)
    {d : ℕ} (hd : Odd d) (c : F) :
    ∑ x ∈ nthRootsFinset (2 * n) (1 : F), c * x ^ d = 0 := by
  have h2n : 0 < 2 * n := by positivity
  refine Finset.sum_involution (fun x _ => -x) ?_ ?_ ?_ ?_
  · -- each antipodal pair cancels: (c·x^d) + (c·(−x)^d) = 0
    intro x _
    rw [graded_odd_antiInvariant hd c x, add_neg_cancel]
  · -- the involution moves every element off its own fiber: −x ≠ x
    intro x hx _ hcontra
    have hx0 : x ≠ 0 := ne_zero_of_mem_nthRootsFinset h2n hx
    -- −x = x ⟹ 2x = 0 ⟹ x = 0 (char ≠ 2), contradiction
    have : (2 : F) * x = 0 := by linear_combination -hcontra
    rcases mul_eq_zero.mp this with h | h
    · exact hchar h
    · exact hx0 h
  · -- the involution maps μ_{2n} into itself
    intro x hx
    exact neg_mem_two_mul_nthRootsFinset hn hx
  · -- it is an involution: −(−x) = x
    intro x _
    simp only [neg_neg]

/-- **Odd power sums over `μ_{2n}` vanish** (the `c = 1` special case). For odd `d`,
`∑_{x ∈ μ_{2n}} x^d = 0`. The complete graded `#bad`-recursion odd half is the `c`-weighted
version above; this is the clean power-sum corollary the antipodal pairing produces directly. -/
theorem odd_power_sum_nthRootsFinset_eq_zero (hchar : (2 : F) ≠ 0) {n : ℕ} (hn : 0 < n)
    {d : ℕ} (hd : Odd d) :
    ∑ x ∈ nthRootsFinset (2 * n) (1 : F), x ^ d = 0 := by
  have := odd_graded_moment_eq_zero (F := F) hchar hn hd (1 : F)
  simpa using this

end ArkLib.ProximityGap.BridgeB35

/-! ## Prize-regime instantiation over `ℂ` -/

namespace ArkLib.ProximityGap.BridgeB35.Complex

open ArkLib.ProximityGap.BridgeB35

/-- **Prize-regime statement (over `ℂ`).** In the prize regime the smooth domain is `μ_{2^μ} ⊂ ℂ`,
`char ℂ = 0 ≠ 2`. So for every `n ≥ 1` (the relevant `n = 2^{μ-1}`), every `c : ℂ`, and every odd
graded degree `d`, the antipodal pairing kills the moment: `∑_{x ∈ μ_{2n}} c·x^d = 0`. -/
theorem odd_graded_moment_eq_zero {n : ℕ} (hn : 0 < n) {d : ℕ} (hd : Odd d) (c : ℂ) :
    ∑ x ∈ nthRootsFinset (2 * n) (1 : ℂ), c * x ^ d = 0 :=
  BridgeB35.odd_graded_moment_eq_zero (by norm_num) hn hd c

end ArkLib.ProximityGap.BridgeB35.Complex

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only) -/
#print axioms ArkLib.ProximityGap.BridgeB35.neg_mem_two_mul_nthRootsFinset
#print axioms ArkLib.ProximityGap.BridgeB35.graded_odd_antiInvariant
#print axioms ArkLib.ProximityGap.BridgeB35.odd_graded_moment_eq_zero
#print axioms ArkLib.ProximityGap.BridgeB35.odd_power_sum_nthRootsFinset_eq_zero
#print axioms ArkLib.ProximityGap.BridgeB35.Complex.odd_graded_moment_eq_zero
