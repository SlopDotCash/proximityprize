/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.C71TrinomialIncidence
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# C71 trinomial gcd obstruction (#444)

`C71BinomialIncidenceGcd` gives the sharp binomial law: a binomial on `mu_n` has a root count
controlled by the cyclic kernel `gcd(d,n)`. A tempting extension to the 3-term Conjecture-7.1
residual is to replace a trinomial `X^i - c₁ X^j - c₂ X^k` by the gcd of its exponent gaps,
`gcd(i-j, j-k, n)`. This file pins the smallest concrete obstruction.

Over `F_17`, on the proper 8-th-root subgroup, the trinomial

`X^2 - X - 2`

has two `mu_8` roots, namely `2` and `-1 = 16`, while `gcd(2-1, 1-0, 8) = 1`. Hence the
binomial cyclotomic-gcd incidence law does **not** extend to trinomials. The surviving theorem is
the already-landed gcd-with-`X^n-1` / span bound in `C71TrinomialIncidence`; no CORE closure is
claimed here.
-/

open Finset

namespace ArkLib.ProximityGap.C71TrinomialGcdObstruction

/-- The two explicit `mu_8` roots of the witness trinomial over `F_17`. -/
def witnessRoots : Finset (ZMod 17) := {2, 16}

/-- Both listed witness points lie in `mu_8(F_17)`. This is a finite-field computation,
closed by plain `decide`. -/
theorem witnessRoots_subset_mu8 : ∀ x ∈ witnessRoots, x ^ (8 : ℕ) = (1 : ZMod 17) := by
  decide

/-- Both listed witness points vanish on the trinomial `X^2 - X - 2` over `F_17`. This is a
finite-field computation, closed by plain `decide`. -/
theorem witnessRoots_vanish_trinomial :
    ∀ x ∈ witnessRoots, x ^ (2 : ℕ) - x - (2 : ZMod 17) = 0 := by
  decide

/-- The **full** `mu_8(F_17)` incidence of the witness trinomial is exactly the two listed roots.
This closes the possible loophole in the obstruction: the set `witnessRoots` is not merely a
lower-bound subset, it is the complete root set inside the proper 8-th-root subgroup. The
finite-field computation is closed by plain `decide`. -/
theorem full_mu8_trinomial_roots_eq_witness :
    (Finset.univ.filter (fun x : ZMod 17 =>
      x ^ (8 : ℕ) = 1 ∧ x ^ (2 : ℕ) - x - (2 : ZMod 17) = 0)) = witnessRoots := by
  decide

/-- The witness incidence has cardinality exactly two. This finite check is the exact two-root
obstruction; it is closed by plain `decide`. -/
theorem witness_trinomial_incidence_card :
    (witnessRoots.filter (fun x : ZMod 17 =>
      x ^ (8 : ℕ) = 1 ∧ x ^ (2 : ℕ) - x - (2 : ZMod 17) = 0)).card = 2 := by
  decide

/-- The complete `mu_8(F_17)` incidence of `X^2 - X - 2` has cardinality exactly two. This is
the caller-facing exact-count form: the obstruction is sharp on the whole subgroup, not only on the
named witness subset. -/
theorem full_mu8_trinomial_incidence_card :
    (Finset.univ.filter (fun x : ZMod 17 =>
      x ^ (8 : ℕ) = 1 ∧ x ^ (2 : ℕ) - x - (2 : ZMod 17) = 0)).card = 2 := by
  rw [full_mu8_trinomial_roots_eq_witness]
  decide

/-- The naive trinomial analog of the binomial cyclic-gcd cap gives only `1` for the witness
exponent gaps. -/
theorem witness_gap_gcd_eq_one :
    Nat.gcd (2 - 1) (Nat.gcd (1 - 0) 8) = 1 := by
  norm_num

/-- **Obstruction.** The trinomial `X^2 - X - 2` on `mu_8(F_17)` has more roots than the
`gcd(i-j,j-k,n)` cap would allow. Thus the binomial `gcd(d,n)` incidence law is genuinely
binomial and cannot be used as the 3-term C71 strata bound. -/
theorem trinomial_gap_gcd_cap_fails :
    Nat.gcd (2 - 1) (Nat.gcd (1 - 0) 8) <
      (witnessRoots.filter (fun x : ZMod 17 =>
        x ^ (8 : ℕ) = 1 ∧ x ^ (2 : ℕ) - x - (2 : ZMod 17) = 0)).card := by
  rw [witness_gap_gcd_eq_one, witness_trinomial_incidence_card]
  norm_num

/-- **Full-subgroup obstruction.** On the entire proper subgroup `mu_8(F_17)`, the trinomial
`X^2 - X - 2` has two roots, while the gap-gcd cap predicts only one. This is the exact incidence
form consumed by the C71 non-orbit residual: a binomial-style `gcd(i-j,j-k,n)` law fails even before
any sampling/subset restriction. -/
theorem trinomial_gap_gcd_cap_fails_on_full_mu8 :
    Nat.gcd (2 - 1) (Nat.gcd (1 - 0) 8) <
      (Finset.univ.filter (fun x : ZMod 17 =>
        x ^ (8 : ℕ) = 1 ∧ x ^ (2 : ℕ) - x - (2 : ZMod 17) = 0)).card := by
  rw [witness_gap_gcd_eq_one, full_mu8_trinomial_incidence_card]
  norm_num

end ArkLib.ProximityGap.C71TrinomialGcdObstruction

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.C71TrinomialGcdObstruction.witnessRoots_subset_mu8
#print axioms ArkLib.ProximityGap.C71TrinomialGcdObstruction.witnessRoots_vanish_trinomial
#print axioms ArkLib.ProximityGap.C71TrinomialGcdObstruction.full_mu8_trinomial_roots_eq_witness
#print axioms ArkLib.ProximityGap.C71TrinomialGcdObstruction.witness_trinomial_incidence_card
#print axioms ArkLib.ProximityGap.C71TrinomialGcdObstruction.full_mu8_trinomial_incidence_card
#print axioms ArkLib.ProximityGap.C71TrinomialGcdObstruction.trinomial_gap_gcd_cap_fails
#print axioms ArkLib.ProximityGap.C71TrinomialGcdObstruction.trinomial_gap_gcd_cap_fails_on_full_mu8
