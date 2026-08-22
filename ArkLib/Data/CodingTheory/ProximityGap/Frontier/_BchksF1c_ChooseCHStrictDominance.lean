/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BchksF1_CompleteHomogeneousFloor

/-!
# Bchks F1c — the complete-homogeneous count STRICTLY dominates the subset-sum (#444)

The F1 floor file (`_BchksF1_CompleteHomogeneousFloor`) asserts that the complete-homogeneous ceiling
`chooseCH s r = C(s+r−1, r)` is **"STRICTLY larger than the subset-sum `C(s, r)` (whence the refuted
Kambiré gap)"**, but proves only the NON-strict `subsetSum_le_chooseCH` (`C(s,r) ≤ chooseCH s r`) and
the single concrete instance `Nat.choose 8 3 < chooseCH 8 3` (56 < 120). The general STRICT statement
— the exact "Kambiré ceiling is not tight" content — was prose + one data point. This file discharges
it into a theorem with the SHARP hypothesis, EXTEND-proven on F1's `chooseCH`.

## The sharp threshold (probe-pinned)

`probe_choosech_strict.py` pins the exact boundary (0 fails / 1599):
* `r = 0`: `C(s,0) = 1 = chooseCH s 0` — EQUAL.
* `r = 1`: `C(s,1) = s = chooseCH s 1` — EQUAL (the `e_1 = h_1` degree-1 coincidence).
* `r ≥ 2`: `C(s,r) < chooseCH s r` STRICTLY, for every `s ≥ 1` — the genuine Kambiré-not-tight gap.

So the strict separation is exactly `r ≥ 2` (the complete-homogeneous and elementary symmetric
functions first split at degree 2: `h_2 = e_1² − e_2` carries the extra `C(s+1,2) − C(s,2) = s`
"repeated-index" monomials). The prize depth is `r ≈ log q ≫ 2`, so the strict gap holds throughout
the prize regime.

## What this file proves (char-free)

* `chooseCH_strict_dominance` (HEADLINE): `2 ≤ r → 1 ≤ s → Nat.choose s r < chooseCH s r`. The
  general STRICT form of F1's `subsetSum_le_chooseCH`, discharging the prose "STRICTLY larger".
* `chooseCH_eq_subsetSum_iff_lt_two` companion: at `r ≤ 1` (and `1 ≤ s`) the two counts COINCIDE
  (`Nat.choose s r = chooseCH s r`) — pinning that `r ≥ 2` is not just sufficient but the threshold.

## Honest scope (rules 1,3,6)

Pure char-free enumerative combinatorics (Pascal on the binomial). NO field/thinness content; a
`Nat.choose` inequality, NOT a `δ*`/incidence object — asymptotic-guard cliff-at-`n/2` UNTOUCHED, no
capacity / beyond-Johnson / growth-law claim. This strict gap is the reason the *char-free* ceiling is
`chooseCH` (not `C(s,r)`); it does NOT bound the OPEN spectrum count `#{distinct h_r(R)}` (which needs
the verified `poly(n)=n` factor, OPEN). CORE `M(μ_n) ≤ C√(n log(p/n))` OPEN.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.BchksF1

/-- **The complete-homogeneous count STRICTLY dominates the subset-sum count for `r ≥ 2`.**
`2 ≤ r → 1 ≤ s → Nat.choose s r < chooseCH s r`. This is the general form of F1's asserted "STRICTLY
larger than the subset-sum `C(s,r)`" — the precise sense in which the Kambiré subset-sum ceiling is
NOT tight at every depth `≥ 2` (hence throughout the prize regime `r ≈ log q`). Proven by Pascal on
the top index: `chooseCH s r = C((s+r−2)+1, r) = C(s+r−2, r) + C(s+r−2, r−1)`, with
`C(s,r) ≤ C(s+r−2, r)` (top-arg monotone, `s ≤ s+r−2` since `r ≥ 2`) and `0 < C(s+r−2, r−1)`
(`r−1 ≤ s+r−2` since `s ≥ 1`) supplying the strict slack. -/
theorem chooseCH_strict_dominance {s r : ℕ} (hr : 2 ≤ r) (hs : 1 ≤ s) :
    Nat.choose s r < chooseCH s r := by
  rw [chooseCH]
  -- s + r - 1 = (s + r - 2) + 1 and r = (r - 1) + 1, so Pascal splits the top index.
  have hidx : s + r - 1 = (s + r - 2) + 1 := by omega
  have hr1 : r = (r - 1) + 1 := by omega
  rw [hidx]
  -- rewrite ONLY the choose-index occurrence of r on the RHS via conv, then Pascal.
  rw [show (s + r - 2 + 1).choose r = (s + r - 2 + 1).choose ((r - 1) + 1) from by rw [← hr1],
     Nat.choose_succ_succ' (s + r - 2) (r - 1)]
  -- now: C(s, r) < C(s+r-2, r-1) + C(s+r-2, (r-1)+1)
  have hmono : Nat.choose s r ≤ Nat.choose (s + r - 2) ((r - 1) + 1) :=
    hr1 ▸ Nat.choose_le_choose r (by omega)
  have hpos : 0 < Nat.choose (s + r - 2) (r - 1) :=
    Nat.choose_pos (by omega)
  omega

/-- **At `r ≤ 1` the two counts COINCIDE** (`1 ≤ s`): `Nat.choose s r = chooseCH s r`. Together with
`chooseCH_strict_dominance`, this pins `r ≥ 2` as the EXACT threshold for the strict Kambiré gap
(degree 0 and 1: `h_0 = e_0 = 1`, `h_1 = e_1`; the split begins at degree 2). -/
theorem chooseCH_eq_subsetSum_of_le_one {s r : ℕ} (hr : r ≤ 1) (hs : 1 ≤ s) :
    Nat.choose s r = chooseCH s r := by
  interval_cases r
  · simp [chooseCH]
  · rw [chooseCH_one hs, Nat.choose_one_right]

/-- **Sanity (the strict gap at the F1 witness depth `r = 3`).** At `s = 8, r = 3`:
`Nat.choose 8 3 = 56 < 120 = chooseCH 8 3`, recovered from the GENERAL strict theorem (not the
hand-checked `decide` instance), confirming the threshold theorem fires at the floor's working depth. -/
theorem chooseCH_strict_concrete : Nat.choose 8 3 < chooseCH 8 3 :=
  chooseCH_strict_dominance (by norm_num) (by norm_num)

end ArkLib.ProximityGap.BchksF1

/-! ## Axiom audit (expected: ⊆ `{propext, Classical.choice, Quot.sound}`) -/
#print axioms ArkLib.ProximityGap.BchksF1.chooseCH_strict_dominance
#print axioms ArkLib.ProximityGap.BchksF1.chooseCH_eq_subsetSum_of_le_one
#print axioms ArkLib.ProximityGap.BchksF1.chooseCH_strict_concrete
