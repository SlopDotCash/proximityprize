/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.UnitCircleAddQuadruple
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound

/-!
# The order-4 zero-sum residual of `μ_n ⊆ ℂ` is ENTIRELY antipodal in char 0 (#444, #407)

The K1 negation-closed walk core (`NegationClosedWalkBound.zeroSumCount_le_pairings`) bounds the
zero-sum count `zeroSumCount G (2r) ≤ (#pairings)·n^r` **conditionally** on the
*no-genuine-relation residual*: every zero-sum `2r`-tuple of `G` must be antipodally paired by some
fixed-point-free involution `σ` (`c (σ i) = −c i`). That hypothesis is exactly the additive-
combinatorics content the bound cannot supply for itself — over a finite field it can FAIL (the
bad-prime cyclotomic coincidences = the open δ\* interior residual).

This file **discharges that residual unconditionally at `r = 2` over `ℂ`** for the prize subgroup
`μ_n` (`n` even, so closed under negation): every zero-sum `4`-tuple of `n`-th roots of unity is two
antipodal pairs. The mechanism is the in-tree unit-circle rigidity
`UnitCircle.unit_add_quadruple` (the *only* additive coincidences among unit-modulus complex numbers
are the trivial ones and antipodal zero-sum pairs). Consequence:

>   `zeroSumCount (μ_n : Finset ℂ) 4 ≤ 3·n²`   (`n` even),

the K1 bound `E_2(μ_n) ≤ 3·n²` made **UNCONDITIONAL** over ℂ — the `(2·2−1)!! = 3` pairings times
`n²`.

## Why this is prize-relevant (honest scope)

The order-4 (quartic) residual over ℂ has **zero** genuine (non-antipodal) content: the whole
`E_2(μ_n)` is the antipodal/diagonal part. This is the order-4 companion to the order-3 vanishing
(`CubeZeroSumCountVanishCharZero`): char 0 forbids the genuine relations, so any beyond-pairing
quartic excess (`E(μ_{2^k}) = 3n(n−1) + excess`) is a purely characteristic-`p` phenomenon — the
nontrivial signed cancellation that is the open BGK wall first appears at the deep orders
`r ≈ log q` over `F_q`, where the reduction creates the coincidences char 0 forbids. This
LOCATES the quartic prize content squarely in the finite-field reduction, not in any archimedean
obstruction.

NON-MOMENT (an exact additive-tuple structural characterization over ℂ; no `|·|` ever), an EXTEND
that discharges the K1 residual hypothesis via the in-tree unit-circle rigidity.
**NOT a CORE bound** — `CORE M(μ_n) ≤ C·√(n·log(q/n))` lives at the deep `F_q` orders. `CORE OPEN.`

Probe `probe_quartic_zerosum_charzero.py`: over `μ_n` (`n = 2,4,8,16,32,64 ⊆ ℂ`) EVERY zero-sum
ordered `4`-tuple is a union of two antipodal pairs (NON-paired = 0), and
`zeroSumCount(μ_n,4) = 3n(n−1)` exactly (the `≤ 3n²` here is the clean K1 cover).

Issues #444, #407.
-/

set_option linter.unusedDecidableInType false


open scoped BigOperators

namespace ArkLib.ProximityGap.QuarticZeroSumPairing

open Finset Complex

/-- Membership in `μ_n ⊆ ℂ` gives unit modulus. -/
theorem norm_eq_one_of_mem_nthRoots {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : z ∈ Polynomial.nthRootsFinset n (1 : ℂ)) : ‖z‖ = 1 := by
  have hzn : z ^ n = 1 := (Polynomial.mem_nthRootsFinset hn (1 : ℂ)).mp hz
  exact Complex.norm_eq_one_of_pow_eq_one hzn hn.ne'

/-- `μ_n ⊆ ℂ` is closed under negation when `n` is even. -/
theorem neg_mem_nthRoots_of_even {n : ℕ} (hn : Even n) {z : ℂ}
    (hz : z ∈ Polynomial.nthRootsFinset n (1 : ℂ)) :
    -z ∈ Polynomial.nthRootsFinset n (1 : ℂ) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hpos
  · exfalso; rw [hn0] at hz; simp [Polynomial.nthRootsFinset] at hz
  have hzn : z ^ n = 1 := (Polynomial.mem_nthRootsFinset hpos (1 : ℂ)).mp hz
  rw [Polynomial.mem_nthRootsFinset hpos]
  rw [neg_pow, hzn, hn.neg_one_pow, one_mul]

open ArkLib.ProximityGap.NegationClosedWalk in
/-- **The antipodal-pairing residual for `μ_n ⊆ ℂ` at order 4.**  Every zero-sum `2*2`-tuple of
`n`-th roots of unity (`n` even) is antipodally paired by a fixed-point-free involution `σ`
(`c (σ i) = −c i`).  Mechanism: writing the zero-sum as `c 0 + c 1 = (−c 2) + (−c 3)` with all four
terms unit-modulus, `UnitCircle.unit_add_quadruple` forces `{c 0, c 1} = {−c 2, −c 3}` (the two
cross-pairings) or `c 0 + c 1 = 0` (the split pairing). -/
theorem quartic_zeroSum_antipodal_paired {n : ℕ}
    (c : Fin (2 * 2) → ℂ)
    (hc : c ∈ Fintype.piFinset (fun _ : Fin (2 * 2) => Polynomial.nthRootsFinset n (1 : ℂ)))
    (hsum : ∑ i, c i = 0) :
    ∃ σ : Equiv.Perm (Fin (2 * 2)),
      IsPairing σ ∧ ∀ i, c (σ i) = - c i := by
  classical
  rw [Fintype.mem_piFinset] at hc
  -- handle n = 0 (μ_0 = ∅, vacuous since c 0 ∈ ∅)
  rcases Nat.eq_zero_or_pos n with hn0 | hpos
  · exfalso; have := hc 0; rw [hn0] at this; simp [Polynomial.nthRootsFinset] at this
  -- unit modulus of each coordinate
  have hnorm : ∀ i, ‖c i‖ = 1 := fun i => norm_eq_one_of_mem_nthRoots hpos (hc i)
  have hnormn : ∀ i, ‖-c i‖ = 1 := fun i => by rw [norm_neg]; exact hnorm i
  -- the zero-sum as a balanced quadruple: c0 + c1 = (-c2) + (-c3)
  have hbal : c 0 + c 1 = (-c 2) + (-c 3) := by
    have : c 0 + c 1 + c 2 + c 3 = 0 := by
      have h := hsum; rw [Fin.sum_univ_four] at h; linear_combination h
    linear_combination this
  -- apply unit-circle rigidity to (c0, c1, -c2, -c3)
  rcases ArkLib.ProximityGap.UnitCircle.unit_add_quadruple
      (hnorm 0) (hnorm 1) (hnormn 2) (hnormn 3) hbal with
      ⟨h0, h1⟩ | ⟨h0, h1⟩ | hz
  · -- c0 = -c2, c1 = -c3  →  pairing (0 2)(1 3)
    refine ⟨Equiv.swap 0 2 * Equiv.swap 1 3, ⟨?_, ?_⟩, ?_⟩
    · intro i; fin_cases i <;> decide
    · intro i; fin_cases i <;> decide
    · intro i; fin_cases i <;>
        simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.isValue] <;> norm_num <;>
        first
          | exact h0 | exact h1
          | (rw [eq_comm, neg_eq_iff_eq_neg] at h0; exact h0)
          | (rw [eq_comm, neg_eq_iff_eq_neg] at h1; exact h1)
  · -- c0 = -c3, c1 = -c2  →  pairing (0 3)(1 2)
    refine ⟨Equiv.swap 0 3 * Equiv.swap 1 2, ⟨?_, ?_⟩, ?_⟩
    · intro i; fin_cases i <;> decide
    · intro i; fin_cases i <;> decide
    · intro i; fin_cases i <;>
        simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.isValue] <;> norm_num <;>
        first
          | exact h0 | exact h1
          | (rw [eq_comm, neg_eq_iff_eq_neg] at h0; exact h0)
          | (rw [eq_comm, neg_eq_iff_eq_neg] at h1; exact h1)
  · -- c0 + c1 = 0  →  c0 = -c1, and then c2 = -c3 too; pairing (0 1)(2 3)
    have h01 : c 0 = - c 1 := by linear_combination hz
    have h23 : c 2 = - c 3 := by
      have htot : c 0 + c 1 + c 2 + c 3 = 0 := by
        have h := hsum; rw [Fin.sum_univ_four] at h; linear_combination h
      linear_combination htot - hz
    refine ⟨Equiv.swap 0 1 * Equiv.swap 2 3, ⟨?_, ?_⟩, ?_⟩
    · intro i; fin_cases i <;> decide
    · intro i; fin_cases i <;> decide
    · intro i; fin_cases i <;>
        simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.isValue] <;> norm_num <;>
        first
          | exact h01 | exact h23
          | (rw [eq_comm, neg_eq_iff_eq_neg] at h01; exact h01)
          | (rw [eq_comm, neg_eq_iff_eq_neg] at h23; exact h23)

open ArkLib.ProximityGap.NegationClosedWalk in
/-- **The K1 bound at `r = 2` is UNCONDITIONAL over `ℂ`.**  The order-4 zero-sum count of `μ_n ⊆ ℂ`
is at most `(#pairings of `Fin 4`) · n²`.  The no-genuine-relation residual hypothesis of
`zeroSumCount_le_pairings` is discharged by `quartic_zeroSum_antipodal_paired`
(unit-circle rigidity), so the bound holds with NO finite-field / cyclotomic side condition. -/
theorem zeroSumCount_four_nthRoots_le_pairings {n : ℕ} :
    zeroSumCount (Polynomial.nthRootsFinset n (1 : ℂ)) (2 * 2)
      ≤ (Finset.univ.filter
          (fun σ : Equiv.Perm (Fin (2 * 2)) => IsPairing σ)).card
        * (Polynomial.nthRootsFinset n (1 : ℂ)).card ^ 2 :=
  zeroSumCount_le_pairings (r := 2) (Polynomial.nthRootsFinset n (1 : ℂ))
    (fun c hc hsum => quartic_zeroSum_antipodal_paired c hc hsum)

open ArkLib.ProximityGap.NegationClosedWalk in
/-- The number of fixed-point-free involutions (pairings) of `Fin 4` is `3` (`= 3!!`). -/
theorem pairings_fin_four_card :
    (Finset.univ.filter
      (fun σ : Equiv.Perm (Fin (2 * 2)) => IsPairing σ)).card = 3 := by
  decide

open ArkLib.ProximityGap.NegationClosedWalk in
/-- **The clean K1 form: `zeroSumCount(μ_n, 4) ≤ 3·n²` over `ℂ`, UNCONDITIONAL.**  The order-4
additive-energy of the prize subgroup `μ_n` over `ℂ` is bounded by `3·n²` with NO finite-field side
condition — the `(2·2−1)!! = 3` antipodal pairings times `n²`.  This is the K1 negation-closed walk
bound made unconditional in char 0 (the genuine-relation residual is empty: unit-circle rigidity
forbids non-antipodal vanishing quadruples). -/
theorem zeroSumCount_four_nthRoots_le_three_mul_sq {n : ℕ} :
    zeroSumCount (Polynomial.nthRootsFinset n (1 : ℂ)) (2 * 2)
      ≤ 3 * (Polynomial.nthRootsFinset n (1 : ℂ)).card ^ 2 := by
  have h := zeroSumCount_four_nthRoots_le_pairings (n := n)
  rwa [pairings_fin_four_card] at h

end ArkLib.ProximityGap.QuarticZeroSumPairing

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.QuarticZeroSumPairing.quartic_zeroSum_antipodal_paired
#print axioms ArkLib.ProximityGap.QuarticZeroSumPairing.zeroSumCount_four_nthRoots_le_three_mul_sq
