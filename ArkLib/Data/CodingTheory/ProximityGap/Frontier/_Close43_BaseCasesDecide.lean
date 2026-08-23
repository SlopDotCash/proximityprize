/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Close43 / C43 [E6] — the FFT-graded obstruction count: decidable base cases + recursion step

This file gives a **fully decidable** Lean definition of the `fhat`-graded obstruction count
`#bad_n(k,m)` from the E6 empirical recursion, and **proves the base cases and one recursion step
rigorously by `decide`** (kernel reduction only — NOT `native_decide`, which would inject the
`Lean.ofReduceBool` axiom). All theorems here are axiom-clean
(`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`).

## The object (mirrors `scripts/probes/probe_2adic_tower_recursion.py` exactly)

For `n = 2·h`, a grade `j`, and a subset `A ⊆ {0,…,n−1}`, the probe computes the **graded
frequency vector** `fhat(A, j, n, h) ∈ ℤ^h`: each `a ∈ A` lands in bin `((j·a) % n) % h` with sign
`+1` if `(j·a) % n < h` (lower half) else `−1`; sum the signed contributions per bin. Then

> `#bad_n(k, m)` := the number of **distinct nonzero** vectors `fhat(A, m, n, h)` over all
> `(k+m)`-element subsets `A` whose lower graded pieces all vanish (`fhat(A, j, n, h) = 0` for every
> `1 ≤ j < m`).

`m = s − k` is the over-determination depth; the lower-grade vanishing is the "all lower graded
pieces zero" constraint, and the top grade `m` is the obstruction the count records.

## What is proven here (the E6 anchor)

* **Base cases** (`#bad_4(1,1)=4`, `#bad_4(1,2)=0`, `#bad_8(2,1)=40`, `#bad_8(2,2)=4`,
  `#bad_8(1,1)=24`) — each by `decide`, matching the probe.
* **The recursion step `#bad_{2n}(k, 2m') = #bad_n(k/2, m')`** is verified as a *concrete
  equation between two `decide`-computed counts*, at three independent instances:
    - `#bad_16(4,2) = #bad_8(2,1) = 40`  (the instance named in the C43 target),
    - `#bad_16(2,2) = #bad_8(1,1) = 24`,
    - `#bad_16(4,4) = #bad_8(2,2) = 4`,
  and the shallower tower `#bad_8(2,2) = #bad_4(1,1) = 4` (so the recursion is checked at
  *two* tower levels, 8↔4 and 16↔8).
* **The odd half `#bad_{2n}(k, odd) = 0`** is anchored by `#bad_8(4,3) = 0` (the antipodal
  involution kills odd graded pieces — the abstract mechanism is proven in
  `_Bridge05_AntipodalOddVanishing.lean`).

These concrete decidable values **anchor the E6 recursion** (base + recursion step + odd
vanishing), all rigorously, with no `native_decide` and no axioms beyond the kernel three.

> **Honest scope.** This file proves *instances* of E6 by direct computation; it does **not** prove
> the recursion for all `(n,k,m)` — that general bijection (the doubling map folding subsets, the
> antipodal involution killing odd pieces) is the remaining E6 obligation, named in the §B/§E ledger
> of `docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`. The values here are the
> rigorous base/step anchors a general proof must reproduce.

Issue #444.
-/

namespace ArkLib.ProximityGap.Close43

/-- `ev n j a = (j·a) mod n` — the residue of the dilated index, exactly the probe's
`e = (jj*a)%n`. -/
def ev (n j a : ℕ) : ℕ := (j * a) % n

/-- The **graded frequency vector** `fhat(A, j, n, h)` as a `List ℤ` of length `h`. Bin `i` collects
the signed contributions of all `a ∈ A` with `ev n j a % h = i`; the sign is `+1` when
`ev n j a < h` (lower half) and `−1` otherwise. Mirrors the probe's `fhat`. -/
def fhatVec (n h j : ℕ) (A : List ℕ) : List ℤ :=
  (List.range h).map (fun i =>
    (A.map (fun a =>
      let e := ev n j a
      if e % h = i then (if e < h then (1 : ℤ) else -1) else 0)).sum)

/-- All `w`-element subsets of `{0,…,n−1}`, each as an ascending `List ℕ`. Standard
include/exclude-the-top recursion: a `(w+1)`-subset of `{0,…,n}` either omits `n` (a `(w+1)`-subset
of `{0,…,n−1}`) or includes `n` (a `w`-subset of `{0,…,n−1}` with `n` appended). -/
def subsetsW : ℕ → ℕ → List (List ℕ)
  | _, 0 => [[]]
  | 0, _+1 => []
  | (n+1), (w+1) =>
    (subsetsW n (w+1)) ++ (subsetsW n w).map (fun l => l ++ [n])

/-- **The FFT-graded obstruction count `#bad_n(k,m)`.** With `h = n/2`, `w = k+m`: take every
`w`-subset `A` whose lower graded pieces all vanish (`fhatVec n h j A = 0` for `1 ≤ j < m`), form the
top graded vector `fhatVec n h m A`, drop the zero vector, and count the **distinct** results. This
is exactly `cf(n,k,m)` in `probe_2adic_tower_recursion.py`. -/
def badCount (n k m : ℕ) : ℕ :=
  let h := n / 2
  let w := k + m
  let zero : List ℤ := List.replicate h 0
  let good := (subsetsW n w).filter (fun A =>
    (List.range' 1 (m - 1)).all (fun j => fhatVec n h j A = zero))
  let vals := (good.map (fun A => fhatVec n h m A)).filter (fun v => v ≠ zero)
  vals.dedup.length

/-! ## Evaluation sanity (matches the probe, `#eval`-checked) -/

-- #eval badCount 4 1 1  -- 4
-- #eval badCount 4 1 2  -- 0
-- #eval badCount 8 2 1  -- 40
-- #eval badCount 8 2 2  -- 4
-- #eval badCount 8 1 1  -- 24
-- #eval badCount 16 4 2 -- 40

/-! ## Base cases (kernel-`decide`, axiom-clean) -/

/-- Base case `#bad_4(1,1) = 4`. -/
theorem badCount_4_1_1 : badCount 4 1 1 = 4 := by decide

/-- Base case `#bad_4(1,2) = 0` (no surviving obstruction at this depth). -/
theorem badCount_4_1_2 : badCount 4 1 2 = 0 := by decide

/-- Base case `#bad_8(1,1) = 24`. -/
theorem badCount_8_1_1 : badCount 8 1 1 = 24 := by decide

/-- Base case `#bad_8(2,1) = 40` (matches the probe's edge value; cf. the E2 cascade `D*(1)=40`
at `n=8, k=2`). -/
theorem badCount_8_2_1 : badCount 8 2 1 = 40 := by decide

/-- Base case `#bad_8(2,2) = 4`. -/
theorem badCount_8_2_2 : badCount 8 2 2 = 4 := by decide

/-! ## The odd half of E6: `#bad_{2n}(k, odd) = 0` (concrete anchor) -/

/-- Odd-grade vanishing instance `#bad_8(4,3) = 0`. The antipodal involution `x ↦ −x` on the even
subgroup makes odd graded pieces anti-invariant, so they sum to zero — the abstract mechanism is
`Bridge05.sum_eq_zero_of_antiInvariant`. This is its concrete realization at `n=8, m=3`. -/
theorem badCount_8_4_3 : badCount 8 4 3 = 0 := by decide

/-! ## The even recursion step `#bad_{2n}(k, 2m') = #bad_n(k/2, m')` (concrete instances)

Each is stated as an **equation between two independently `decide`-computed counts**, so the proof
witnesses the recursion holding rather than just both sides equalling a literal. -/

/-- Tower step 8 ↔ 4: `#bad_8(2, 2) = #bad_4(1, 1)` (both `= 4`). Here `n=4, 2n=8, k=2, m'=1, m=2,
k/2=1`. -/
theorem recursion_step_8_4 : badCount 8 2 2 = badCount 4 1 1 := by decide

set_option maxRecDepth 100000 in
/-- **The C43 target recursion instance**, tower step 16 ↔ 8: `#bad_16(4, 2) = #bad_8(2, 1)`
(both `= 40`). Here `n=8, 2n=16, k=4, m'=1, m=2, k/2=2`. -/
theorem recursion_step_16_8_target : badCount 16 4 2 = badCount 8 2 1 := by decide

set_option maxRecDepth 100000 in
/-- Tower step 16 ↔ 8: `#bad_16(2, 2) = #bad_8(1, 1)` (both `= 24`). `k=2, m'=1, m=2, k/2=1`. -/
theorem recursion_step_16_8_b : badCount 16 2 2 = badCount 8 1 1 := by decide

set_option maxRecDepth 100000 in
/-- Tower step 16 ↔ 8 at depth `m=4`: `#bad_16(4, 4) = #bad_8(2, 2)` (both `= 4`). `k=4, m'=2,
m=4, k/2=2`. -/
theorem recursion_step_16_8_c : badCount 16 4 4 = badCount 8 2 2 := by decide

/-! ## Axiom audit -/

#print axioms badCount_4_1_1
#print axioms badCount_4_1_2
#print axioms badCount_8_1_1
#print axioms badCount_8_2_1
#print axioms badCount_8_2_2
#print axioms badCount_8_4_3
#print axioms recursion_step_8_4
#print axioms recursion_step_16_8_target
#print axioms recursion_step_16_8_b
#print axioms recursion_step_16_8_c

end ArkLib.ProximityGap.Close43
