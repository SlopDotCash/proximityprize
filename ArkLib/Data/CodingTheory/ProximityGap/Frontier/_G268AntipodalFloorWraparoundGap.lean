/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum

/-!
# G268: the full antipodal alignment floor is far below the sponsor gate

G267 records an eventually-positive `n = 8` tail for the adjacent-rank alignment

```text
A_r = p * J_r - n^2 * C(n,r) * C(n,r-1),
J_r = sum_t W_G(t) R_r(t),                         r in {5,6}.
```

That fixed-order tail does not give a production mechanism.  Rewrite a contributing alignment as

```text
y + y + B + (-z) + (-A) = 0
```

among `2r+2` roots in the dyadic group.  In characteristic zero, when `2r+2 < n`, the
prime-power vanishing-sum classification reduces this positive sum to antipodal pairs.  A direct
local transfer count on one antipodal pair has imbalance polynomials

```text
P0 = 1 + Y^2 + 2XY + X^2 + X^2Y^2,
P1 = X + Y + XY^2 + X^2Y,
P2 = XY.
```

Writing `m=n/2` and fixing `y`, the complete antipodal contribution is

```text
J_r^0 = n * [X^(r-1)Y^r]
  (P1*P0^(m-1) + 2(m-1)*P2*P1*P0^(m-2)).
```

Coefficient extraction gives

```text
J_5^0 = n(m-2)(m-1)(203m^2 - 1099m + 1536) / 12,
J_6^0 = n(m-2)(m-1)(287m^3 - 2789m^2 + 9174m - 10160) / 20.
```

The companion exact probe derives these formulas from the sixteen local bit configurations,
checks them against direct antipodal enumeration at `n=8`, and recomputes the finite-field
alignment witness below.  This file kernel-checks the production arithmetic consumer.

At `n=2^30`, the entire antipodal supply is not merely insufficient:

* at P1, even `2^10 * J_5^0` remains below the rank-five mean-mass requirement;
* at P2, even `2^9 * J_5^0` remains below it;
* at P1, even `2^36 * J_6^0` remains below rank six;
* at P2, even `2^35 * J_6^0` remains below rank six.

Thus production positivity needs characteristic-`p` wraparound relation mass larger than the full
characteristic-zero antipodal contribution at both ranks.  Rank five needs more than 1024/512
baseline copies, while rank six needs more than `2^36`/`2^35`.  This explains why a positive
fixed-`n` thin tail cannot transfer to the sponsors: FS15--FS18 recover the pairing regime only off
their resultant exceptional sets, whereas the required production mechanism lives in the
exceptional wraparound excess itself.

The exact cell `(n,p)=(32,70753)` supplies the cross-scale warning: `tau=(p-1)/n^2=69.09375`, yet
`A_6=-1324791182208`.  Hence G267's `n=8` numerical cutoff is not scale-free.

Honest scope: the transfer-polynomial coefficient extraction and finite-field cell are reproducible
exact computations, not rederived as finite-set bijections in this Lean file.  The Lean payload is
the axiom-free production arithmetic and its universal count consumers.  This is a precise
wraparound-necessity theorem/no-go, not the missing positive sponsor estimate and not prize closure.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace ArkLib.ProximityGap.Frontier.G268

/-- Production subgroup order. -/
abbrev n : ℕ := 2 ^ 30

/-- Number of antipodal pairs in the production subgroup. -/
abbrev m : ℕ := 2 ^ 29

/-- First certified sponsor prime. -/
abbrev p1 : ℕ := n * (2 ^ 128 + 192) + 1

/-- Second certified sponsor prime. -/
abbrev p2 : ℕ := n * (2 ^ 129 + 13) + 1

/-- Closed small-rank formula for `C(n,4)`. -/
def choose4 : ℕ := n * (n - 1) * (n - 2) * (n - 3) / 24

/-- Closed small-rank formula for `C(n,5)`. -/
def choose5 : ℕ := n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 120

/-- Closed small-rank formula for `C(n,6)`. -/
def choose6 : ℕ := n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) / 720

/-- The rank-five centering mass `n^2*C(n,5)*C(n,4)`. -/
def mass5 : ℕ := n ^ 2 * choose5 * choose4

/-- The rank-six centering mass `n^2*C(n,6)*C(n,5)`. -/
def mass6 : ℕ := n ^ 2 * choose6 * choose5

/-- Complete characteristic-zero antipodal alignment count at rank five. -/
def antipodal5 : ℕ :=
  n * (m - 2) * (m - 1) * (203 * m ^ 2 - 1099 * m + 1536) / 12

/-- Complete characteristic-zero antipodal alignment count at rank six. -/
def antipodal6 : ℕ :=
  n * (m - 2) * (m - 1) *
      (287 * m ^ 3 - 2789 * m ^ 2 + 9174 * m - 10160) / 20

/-- At P1, even 1024 copies of the full rank-five antipodal supply remain below the gate. -/
theorem p1_rankFive_1024_antipodal_short :
    p1 * (2 ^ 10 * antipodal5) < mass5 := by
  norm_num [p1, n, m, antipodal5, mass5, choose5, choose4]

/-- At P2, even 512 copies of the full rank-five antipodal supply remain below the gate. -/
theorem p2_rankFive_512_antipodal_short :
    p2 * (2 ^ 9 * antipodal5) < mass5 := by
  norm_num [p2, n, m, antipodal5, mass5, choose5, choose4]

/-- At P1, even `2^36` copies of the full rank-six antipodal supply remain below the gate. -/
theorem p1_rankSix_twoPow36_antipodal_short :
    p1 * (2 ^ 36 * antipodal6) < mass6 := by
  norm_num [p1, n, m, antipodal6, mass6, choose6, choose5]

/-- At P2, even `2^35` copies of the full rank-six antipodal supply remain below the gate. -/
theorem p2_rankSix_twoPow35_antipodal_short :
    p2 * (2 ^ 35 * antipodal6) < mass6 := by
  norm_num [p2, n, m, antipodal6, mass6, choose6, choose5]

/-- Any P1 rank-five relation count reaching nonnegative centered alignment must exceed 1024
complete antipodal baselines. -/
theorem p1_rankFive_positive_needs_gt_1024_antipodal {J : ℕ}
    (hgate : mass5 ≤ p1 * J) : 2 ^ 10 * antipodal5 < J := by
  by_contra h
  have hle : J ≤ 2 ^ 10 * antipodal5 := Nat.le_of_not_gt h
  have hmass : mass5 ≤ p1 * (2 ^ 10 * antipodal5) :=
    hgate.trans (Nat.mul_le_mul_left p1 hle)
  exact (Nat.not_le_of_lt p1_rankFive_1024_antipodal_short) hmass

/-- Any P2 rank-five relation count reaching nonnegative centered alignment must exceed 512
complete antipodal baselines. -/
theorem p2_rankFive_positive_needs_gt_512_antipodal {J : ℕ}
    (hgate : mass5 ≤ p2 * J) : 2 ^ 9 * antipodal5 < J := by
  by_contra h
  have hle : J ≤ 2 ^ 9 * antipodal5 := Nat.le_of_not_gt h
  have hmass : mass5 ≤ p2 * (2 ^ 9 * antipodal5) :=
    hgate.trans (Nat.mul_le_mul_left p2 hle)
  exact (Nat.not_le_of_lt p2_rankFive_512_antipodal_short) hmass

/-- Any P1 rank-six relation count reaching nonnegative centered alignment must exceed `2^36`
complete antipodal baselines. -/
theorem p1_rankSix_positive_needs_gt_twoPow36_antipodal {J : ℕ}
    (hgate : mass6 ≤ p1 * J) : 2 ^ 36 * antipodal6 < J := by
  by_contra h
  have hle : J ≤ 2 ^ 36 * antipodal6 := Nat.le_of_not_gt h
  have hmass : mass6 ≤ p1 * (2 ^ 36 * antipodal6) :=
    hgate.trans (Nat.mul_le_mul_left p1 hle)
  exact (Nat.not_le_of_lt p1_rankSix_twoPow36_antipodal_short) hmass

/-- Any P2 rank-six relation count reaching nonnegative centered alignment must exceed `2^35`
complete antipodal baselines. -/
theorem p2_rankSix_positive_needs_gt_twoPow35_antipodal {J : ℕ}
    (hgate : mass6 ≤ p2 * J) : 2 ^ 35 * antipodal6 < J := by
  by_contra h
  have hle : J ≤ 2 ^ 35 * antipodal6 := Nat.le_of_not_gt h
  have hmass : mass6 ≤ p2 * (2 ^ 35 * antipodal6) :=
    hgate.trans (Nat.mul_le_mul_left p2 hle)
  exact (Nat.not_le_of_lt p2_rankSix_twoPow35_antipodal_short) hmass

/-- Exact cross-scale alignment record. -/
structure ThinCell where
  order : ℕ
  prime : ℕ
  A5 : ℤ
  A6 : ℤ

/-- A genuine order-32 cell beyond `tau=69`, recomputed exactly by the companion probe. -/
def lateNegative : ThinCell :=
  { order := 32, prime := 70753, A5 := 132970510400, A6 := -1324791182208 }

/-- The cell lies strictly beyond `tau=69` and still has negative rank-six alignment. -/
theorem late_negative_beyond_tau_69 :
    69 * lateNegative.order ^ 2 < lateNegative.prime - 1 ∧ lateNegative.A6 < 0 := by
  decide

/-- Honest status marker. -/
def isPrizeClosure : Bool := false

theorem not_prizeClosure : isPrizeClosure = false := rfl

#print axioms p1_rankFive_1024_antipodal_short
#print axioms p2_rankFive_512_antipodal_short
#print axioms p1_rankSix_twoPow36_antipodal_short
#print axioms p2_rankSix_twoPow35_antipodal_short
#print axioms p1_rankFive_positive_needs_gt_1024_antipodal
#print axioms p2_rankFive_positive_needs_gt_512_antipodal
#print axioms p1_rankSix_positive_needs_gt_twoPow36_antipodal
#print axioms p2_rankSix_positive_needs_gt_twoPow35_antipodal
#print axioms late_negative_beyond_tau_69
#print axioms not_prizeClosure

end ArkLib.ProximityGap.Frontier.G268
