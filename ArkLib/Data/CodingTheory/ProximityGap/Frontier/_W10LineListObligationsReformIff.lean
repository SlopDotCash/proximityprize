/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic

/-!
# The complement-reformulation IFF, in full (#466, thread ll:topfit-witness-successor, lane _W10)

## What this file closes

`_FloorComplementReform.lean` (lane FS1, kb `deltastar-466-floorbad64-decided-2026-07-03.md`)
proved only the *divisibility pivot* of the complement reformulation
(`floorReform_dvd : (X^N - 1) ∣ (X^D·Q - (X^D %ₘ P)·Q)`), and its module docstring says
explicitly:

> "This last degree/coefficient bookkeeping (an unfolding of the divisibility proved here) is
>  verified computationally in the probe rather than in Lean."

This file proves that bookkeeping — the **full iff** — as an axiom-clean Lean theorem, general
in the commutative ring and in all exponents:

  `remainder_natDegree_le_iff_window` :
    for monic `P, Q` with `P * Q = X^N - 1` and any `D < N`, `m`,

      `deg (X^D %ₘ P) ≤ m  ↔  Q.coeff i = 0  for all i with  m + deg Q + 1 ≤ D + i ≤ N - 1`.

The FS1 instantiation (`n = 8u`, `|A| = 5u` so `deg Q_B = 3u`, `D = 6u = 3n/4`, `m = 4u = n/2`)
is the corollary `floorReform_window_iff` / `floorReform_scanner_iff`: the scanner's floor-bad
realizability test `deg (X^{3n/4} %ₘ P_A) ≤ n/2` is **equivalent** to the vanishing of the
`n/8 - 1` middle coefficients `[X^{n/8+1} .. X^{n/4-1}]` of the complement polynomial `Q_B` —
exactly the window of the kb note, now a theorem rather than a probe-verified identity.

## Why it matters for the successor obligation (workbench §5(2), item `CandidateListExactSuccessor`)

The floor-bad(64) decision (FS1: `193 = p_min(64)` is NOT floor-bad; the uniform successor law
`floor-bad(n) = {p_min(n)}` is REFUTED at `n = 64`) rests on a complete MITM scan whose
correctness chain was: Lean divisibility + probe-verified degree bookkeeping + engine
validation.  This file upgrades the first two links into a single machine-checked equivalence:
the scan's window test is now *provably* the scanner's rank/degree test, over any field
(indeed any nontrivial commutative ring), for any pattern/complement split — removing the only
mathematical (as opposed to computational) trust step in the FS1 refutation.

## Proof shape

`X^D = P·S + r` with `r = X^D %ₘ P`, `S = X^D /ₘ P` gives `r·Q = X^D·Q - (X^N - 1)·S`.
For any `d` with `deg Q < d < N` the subtracted term has zero `d`-coefficient
(`deg S = D - deg P ≤ deg Q - 1 < d` from `D < N`, and `X^N·S` only feeds degrees `≥ N`), so

  `(r·Q).coeff d = if D ≤ d then Q.coeff (d - D) else 0`   (`remainder_mul_coeff_high`).

`deg r ≤ m` is then read off at the window degrees `d ∈ [m + deg Q + 1, N - 1]`: forward by
`deg (r·Q) ≤ m + deg Q`, backward at the top degree `d = deg r + deg Q` whose coefficient is
`leadingCoeff r ≠ 0`.

NOTE (probe `scripts/probes/probe_w10_reform_iff_fuzz.py`): the window-alignment hypothesis
`D ≤ m + deg Q + 1` used by the kb-note narration is NOT needed — the fuzz (399,888 exact
checks over GF(2,3,5,7,13,17) and ℤ, including non-squarefree `X^N - 1`, plus 2,890 adversarial
checks with the hypothesis violated, 0 mismatches) suggested the stronger statement, and the
proof confirms it: only `D < N` is load-bearing.  The i-indexed window `D + i ≥ m + deg Q + 1`
self-truncates below `X^D`.

Non-vacuity: at `n = 16`, `p = 17` the probe counts 584 realizable complements among all
`C(16,10) = 8008` (residual test ≡ window test on every one of them, and likewise at `p = 97`).

NO `sorry`, NO `axiom`, NO `native_decide`; axiom audit must show
`[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace ArkLib.ProximityGap.Frontier.W10ComplementReformIff

open Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- Degrees add across a monic factorization of `X^N - 1`. -/
theorem natDegree_add_of_mul_eq_X_pow_sub_one
    {P Q : R[X]} (hP : P.Monic) (hQ : Q.Monic) {N : ℕ}
    (hPQ : P * Q = X ^ N - 1) :
    P.natDegree + Q.natDegree = N := by
  have h := hP.natDegree_mul' hQ.ne_zero
  rw [hPQ, ← C_1, natDegree_X_pow_sub_C] at h
  exact h.symm

omit [Nontrivial R] in
/-- The split identity: `r·Q = X^D·Q - (X^N - 1)·S` with `r = X^D %ₘ P`, `S = X^D /ₘ P`.
(The divisibility form of this is `FloorComplementReform.floorReform_dvd`; here we keep the
explicit cofactor because its degree bound powers the coefficient extraction.) -/
theorem remainder_mul_split (P Q : R[X]) (D N : ℕ)
    (hPQ : P * Q = X ^ N - 1) :
    (X ^ D %ₘ P) * Q = X ^ D * Q - (X ^ N - 1) * (X ^ D /ₘ P) := by
  have h := modByMonic_add_div (X ^ D : R[X]) P
  rw [← hPQ]
  linear_combination Q * h

/-- **Coefficient extraction above `deg Q`.** For monic `P, Q` with `P * Q = X^N - 1`, `D < N`,
and any degree `d` with `deg Q < d < N`, the product `(X^D %ₘ P) * Q` has `d`-coefficient
exactly the complement coefficient `Q.coeff (d - D)` (or `0` below `X^D`).  This is the exact
content of "`r·Q` is the reduction of `X^D·Q` mod `X^N - 1`" at the window degrees. -/
theorem remainder_mul_coeff_high
    {P Q : R[X]} (hP : P.Monic) (hQ : Q.Monic) {N D d : ℕ}
    (hPQ : P * Q = X ^ N - 1)
    (hD : D < N) (hd : d < N) (hdQ : Q.natDegree < d) :
    ((X ^ D %ₘ P) * Q).coeff d = if D ≤ d then Q.coeff (d - D) else 0 := by
  have hN := natDegree_add_of_mul_eq_X_pow_sub_one hP hQ hPQ
  rw [remainder_mul_split P Q D N hPQ, coeff_sub]
  have t1 : (X ^ D * Q).coeff d = if D ≤ d then Q.coeff (d - D) else 0 := by
    rw [mul_comm]
    exact coeff_mul_X_pow' Q D d
  have hS : ((X ^ N - 1) * (X ^ D /ₘ P)).coeff d = 0 := by
    rw [sub_mul, one_mul, coeff_sub]
    have a1 : (X ^ N * (X ^ D /ₘ P)).coeff d = 0 := by
      rw [mul_comm, coeff_mul_X_pow']
      exact if_neg (by omega)
    have a2 : (X ^ D /ₘ P).coeff d = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_divByMonic _ hP, natDegree_X_pow]
      omega
    rw [a1, a2, sub_zero]
  rw [t1, hS, sub_zero]

/-- **The complement-reformulation iff (natDegree form).**  For monic `P, Q` with
`P * Q = X^N - 1` and `D < N`:

  `deg (X^D %ₘ P) ≤ m  ↔  Q.coeff i = 0  for every i with  m + deg Q + 1 ≤ D + i ≤ N - 1`.

This is the full FS1 reformulation: the floor scanner's remainder-degree test equals the
vanishing of a contiguous middle window of complement coefficients.  Note the RHS window
self-truncates (indices below `X^D` are excluded by `D + i ≥ m + deg Q + 1` being about
`D + i`), so no alignment hypothesis between `D` and `m + deg Q` is needed. -/
theorem remainder_natDegree_le_iff_window
    {P Q : R[X]} (hP : P.Monic) (hQ : Q.Monic) {N D m : ℕ}
    (hPQ : P * Q = X ^ N - 1) (hD : D < N) :
    (X ^ D %ₘ P).natDegree ≤ m ↔
      ∀ i : ℕ, m + Q.natDegree + 1 ≤ D + i → D + i < N → Q.coeff i = 0 := by
  have hN := natDegree_add_of_mul_eq_X_pow_sub_one hP hQ hPQ
  constructor
  · -- degree bound ⟹ window vanishing
    intro hle i h1 h2
    have hkey := remainder_mul_coeff_high hP hQ hPQ hD h2
      (show Q.natDegree < D + i by omega)
    rw [if_pos (Nat.le_add_right D i), Nat.add_sub_cancel_left] at hkey
    have hzero : ((X ^ D %ₘ P) * Q).coeff (D + i) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      calc ((X ^ D %ₘ P) * Q).natDegree
          ≤ (X ^ D %ₘ P).natDegree + Q.natDegree := natDegree_mul_le
        _ < D + i := by omega
    rw [hzero] at hkey
    exact hkey.symm
  · -- window vanishing ⟹ degree bound, via the nonzero top coefficient of r·Q
    intro hvan
    by_contra hgt
    push Not at hgt
    have hr0 : (X ^ D %ₘ P) ≠ 0 := by
      intro h0
      rw [h0, natDegree_zero] at hgt
      omega
    have hrP : (X ^ D %ₘ P).natDegree < P.natDegree :=
      natDegree_lt_natDegree hr0 (degree_modByMonic_lt (X ^ D) hP)
    have htop : ((X ^ D %ₘ P) * Q).coeff ((X ^ D %ₘ P).natDegree + Q.natDegree) =
        (X ^ D %ₘ P).leadingCoeff * Q.leadingCoeff :=
      coeff_mul_degree_add_degree _ Q
    rw [hQ.leadingCoeff, mul_one] at htop
    have hne : ((X ^ D %ₘ P) * Q).coeff ((X ^ D %ₘ P).natDegree + Q.natDegree) ≠ 0 := by
      rw [htop]
      exact leadingCoeff_ne_zero.mpr hr0
    have hkey := remainder_mul_coeff_high hP hQ hPQ hD
      (show (X ^ D %ₘ P).natDegree + Q.natDegree < N by omega)
      (show Q.natDegree < (X ^ D %ₘ P).natDegree + Q.natDegree by omega)
    by_cases hDd : D ≤ (X ^ D %ₘ P).natDegree + Q.natDegree
    · rw [if_pos hDd] at hkey
      have hwin : Q.coeff ((X ^ D %ₘ P).natDegree + Q.natDegree - D) = 0 :=
        hvan _ (by omega) (by omega)
      rw [hwin] at hkey
      exact hne hkey
    · rw [if_neg hDd] at hkey
      exact hne hkey

/-- The same iff in `degree` form. -/
theorem remainder_degree_le_iff_window
    {P Q : R[X]} (hP : P.Monic) (hQ : Q.Monic) {N D m : ℕ}
    (hPQ : P * Q = X ^ N - 1) (hD : D < N) :
    (X ^ D %ₘ P).degree ≤ (m : ℕ) ↔
      ∀ i : ℕ, m + Q.natDegree + 1 ≤ D + i → D + i < N → Q.coeff i = 0 := by
  rw [← natDegree_le_iff_degree_le]
  exact remainder_natDegree_le_iff_window hP hQ hPQ hD

/-- **The FS1 window corollary** (`n = 8u` parametrization).  For monic `P, Q` with
`P * Q = X^{8u} - 1` and `deg Q = 3u` (the complement of a `5u`-point pattern):

  `deg (X^{6u} %ₘ P) ≤ 4u  ↔  Q.coeff i = 0  for all i ∈ [u+1, 2u-1]`,

i.e. floor-bad realizability of the pattern equals the vanishing of the `u - 1` MIDDLE
coefficients of the degree-`3u` complement polynomial — the kb-note window
(`n=16 → i=3`; `n=32 → i∈{5,6,7}`; `n=64 → i∈{9..15}`), now a theorem. -/
theorem floorReform_window_iff {u : ℕ} (hu : 1 ≤ u)
    {P Q : R[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hPQ : P * Q = X ^ (8 * u) - 1) (hdQ : Q.natDegree = 3 * u) :
    (X ^ (6 * u) %ₘ P).natDegree ≤ 4 * u ↔
      ∀ i : ℕ, u + 1 ≤ i → i ≤ 2 * u - 1 → Q.coeff i = 0 := by
  rw [remainder_natDegree_le_iff_window hP hQ hPQ (by omega)]
  constructor
  · intro h i h1 h2
    exact h i (by omega) (by omega)
  · intro h i h1 h2
    exact h i (by omega) (by omega)

/-- **Scanner-vocabulary form.**  For `8 ∣ n`, `n ≠ 0`: the scanner's rank/degree test
`deg (X^{3n/4} %ₘ P_A) ≤ n/2` is equivalent to the vanishing of the complement coefficients
in the window `[n/8 + 1, n/4 - 1]`.  This is verbatim the reformulation of
`deltastar-466-floorbad64-decided-2026-07-03.md` §0(A). -/
theorem floorReform_scanner_iff {n : ℕ} (h8 : 8 ∣ n) (hn : n ≠ 0)
    {P Q : R[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hPQ : P * Q = X ^ n - 1) (hdQ : Q.natDegree = 3 * n / 8) :
    (X ^ (3 * n / 4) %ₘ P).natDegree ≤ n / 2 ↔
      ∀ i : ℕ, n / 8 + 1 ≤ i → i ≤ n / 4 - 1 → Q.coeff i = 0 := by
  obtain ⟨u, rfl⟩ := h8
  have hu : 1 ≤ u := by omega
  have e1 : 3 * (8 * u) / 4 = 6 * u := by omega
  have e2 : 8 * u / 2 = 4 * u := by omega
  have e3 : 3 * (8 * u) / 8 = 3 * u := by omega
  have e4 : 8 * u / 8 = u := by omega
  have e5 : 8 * u / 4 - 1 = 2 * u - 1 := by omega
  rw [e1, e2, e4, e5]
  rw [e3] at hdQ
  exact floorReform_window_iff hu hP hQ hPQ hdQ

#print axioms natDegree_add_of_mul_eq_X_pow_sub_one
#print axioms remainder_mul_split
#print axioms remainder_mul_coeff_high
#print axioms remainder_natDegree_le_iff_window
#print axioms remainder_degree_le_iff_window
#print axioms floorReform_window_iff
#print axioms floorReform_scanner_iff

end ArkLib.ProximityGap.Frontier.W10ComplementReformIff
