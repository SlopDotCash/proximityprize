/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AssaultV2_FloorLocalizationN32

/-!
# The two RESOLVED Linnik least-prime rungs `a = 4, 5` (off-BGK floor, #444 / #464)

`_AssaultV2_FloorLocalizationN32` reduces the off-BGK floor closure to two named third-party inputs via
`floor_closes_by_linnik`:
  1. `FloorLocalizationUniform` — the realizability characterization (still open, a height/0-dim
     statement, NOT the BGK wall), and
  2. `LinnikLeastPrimeBelowPrize` — `∀ a ≥ 4, smallestPrime1ModN (2^a) (2^(5a)) < (2^a)^4`, i.e. the
     least prime `≡ 1 mod 2^a` sits below prize scale `(2^a)^4`.

Shaw's #464 Round-3 comment RESOLVED the `n=32` floor-bad set to `{97}` (= smallest prime `≡ 1 mod 32`)
with an exact scanner validated on the `n=16` ground truth, confirming the smallest-prime
characterization at BOTH verified rungs `a = 4` (`17`) and `a = 5` (`97`).

This file discharges input (2) AT THOSE TWO RESOLVED RUNGS, axiom-clean, WITHOUT a giant `decide`
over `List.range (2^(5a))` (which is kernel-infeasible). The mechanism is a small witness lemma:
`smallestPrime1ModN n bound = q` whenever `q` is a prime `≡ 1 mod n`, `q ≤ bound`, and no `m < q`
is a prime `≡ 1 mod n` — so the answer is bound-independent above the witness, and the "no `m < q`"
check is a tiny `decide` (`q ∈ {17, 97}`), not a `2^25`-sized one.

## Honesty (scope)

This proves ONLY the two concrete rung instances of input (2), exactly the rungs Shaw verified. It does
NOT prove `LinnikLeastPrimeBelowPrize` for all `a ≥ 4` (that is the unconditional Linnik/Thorner–Zaman
exponent `< 4` for powerful moduli, still open — GRH gives `2+ε`), and it does NOT touch input (1)
`FloorLocalizationUniform`, nor the BGK/Paley sup-norm wall. Pure consolidation: turns the two
"verified `17 < 16^4`, `97 < 32^4`" remarks into in-tree theorems with the EXACT `2^(5a)` search bound
the closure premise uses. CORE stays OPEN.
-/

set_option linter.style.longLine false


open ArkLib.ProximityGap.Frontier.FloorLocalization

namespace ArkLib.ProximityGap.Frontier.FloorLinnikRung

/-- **Witness characterization of `smallestPrime1ModN`.** If `q` is a prime `≡ 1 mod n`, `q ≤ bound`,
and every `m < q` fails (`¬(m % n = 1 ∧ m.Prime)`), then `smallestPrime1ModN n bound = q`,
independently of how large `bound` is above `q`. This lets us transfer the cheap small-bound `decide`
to the huge `2^(5a)` search bound the Linnik premise uses, without enumerating `range (2^(5a))`. -/
theorem smallestPrime1ModN_eq_of_witness {n bound q : ℕ}
    (hqb : q ≤ bound)
    (hqmod : q % n = 1) (hqp : q.Prime)
    (hmin : ∀ m, m < q → ¬ (m % n = 1 ∧ m.Prime)) :
    smallestPrime1ModN n bound = q := by
  unfold smallestPrime1ModN
  -- the filtered list of `range (bound+1)` has head `q`: everything before `q` is filtered out, and
  -- `q` itself is in range and passes the predicate.
  set P : ℕ → Bool := fun p => p % n == 1 && p.Prime with hP
  -- predicate truth at q
  have hPq : P q = true := by
    simp only [hP, Bool.and_eq_true, beq_iff_eq]
    exact ⟨by simpa using hqmod, decide_eq_true hqp⟩
  -- predicate falsity below q
  have hPlt : ∀ m, m < q → P m = false := by
    intro m hm
    have hno := hmin m hm
    simp only [not_and] at hno
    by_cases hmod : m % n = 1
    · have hnp : ¬ m.Prime := hno hmod
      simp only [hP, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      exact Or.inr hnp
    · simp only [hP, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      exact Or.inl (by simpa using hmod)
  -- `range (bound+1) = range q ++ (q :: range' ...)`; head of filter is q
  have hqlt : q < bound + 1 := Nat.lt_succ_of_le hqb
  -- split the range at q
  have hsplit : List.range (bound + 1)
      = List.range q ++ (List.range (bound + 1)).drop q := by
    have : List.range q = (List.range (bound + 1)).take q := by
      rw [List.take_range]; congr 1; omega
    rw [this, List.take_append_drop]
  rw [hsplit, List.filter_append]
  -- the prefix `range q` filters to empty
  have hempty : (List.range q).filter P = [] := by
    rw [List.filter_eq_nil_iff]
    intro m hm
    have := hPlt m (List.mem_range.mp hm)
    simp [this]
  rw [hempty, List.nil_append]
  -- the suffix `(range (bound+1)).drop q` starts with q
  have hdrop : (List.range (bound + 1)).drop q = q :: (List.range (bound + 1)).drop (q + 1) := by
    have hqmem : q < (List.range (bound + 1)).length := by
      rw [List.length_range]; omega
    have hgetq : (List.range (bound + 1))[q]'hqmem = q := by
      simp [List.getElem_range]
    have := List.drop_eq_getElem_cons hqmem
    rw [this, hgetq]
  rw [hdrop, List.filter_cons, hPq]
  simp

/-- **Rung `a = 4` (`n = 16`).** The least prime `≡ 1 mod 16`, searched within the closure's exact
bound `2^(5·4) = 2^20`, is `17`. (Witness lemma; the `m < 17` minimality is a tiny `decide`.) -/
theorem smallestPrime1ModN_16_pow20_eq_17 :
    smallestPrime1ModN 16 (2 ^ (5 * 4)) = 17 := by
  apply smallestPrime1ModN_eq_of_witness
  · decide          -- 17 ≤ 2^20
  · decide          -- 17 % 16 = 1
  · decide          -- 17 prime
  · decide          -- no m < 17 is a prime ≡ 1 mod 16

/-- **Rung `a = 5` (`n = 32`).** The least prime `≡ 1 mod 32`, searched within the closure's exact
bound `2^(5·5) = 2^25`, is `97` — exactly Shaw's #464 Round-3 resolution `floorBad(32) = {97}`.
(Witness lemma; the `m < 97` minimality is a tiny `decide`.) -/
theorem smallestPrime1ModN_32_pow25_eq_97 :
    smallestPrime1ModN 32 (2 ^ (5 * 5)) = 97 := by
  apply smallestPrime1ModN_eq_of_witness
  · decide          -- 97 ≤ 2^25
  · decide          -- 97 % 32 = 1
  · decide          -- 97 prime
  · decide          -- no m < 97 is a prime ≡ 1 mod 32

/-- **Input (2) discharged at `a = 4`.** `smallestPrime1ModN (2^4) (2^(5·4)) < (2^4)^4`, i.e.
`17 < 16^4 = 65536`. The Linnik premise of `floor_closes_by_linnik` holds concretely at the `n=16`
rung with the EXACT `2^(5a)` search bound. -/
theorem linnik_rung_a4 :
    smallestPrime1ModN (2 ^ 4) (2 ^ (5 * 4)) < (2 ^ 4) ^ 4 := by
  rw [show (2 ^ 4 : ℕ) = 16 from by norm_num, smallestPrime1ModN_16_pow20_eq_17]
  decide

/-- **Input (2) discharged at `a = 5`.** `smallestPrime1ModN (2^5) (2^(5·5)) < (2^5)^4`, i.e.
`97 < 32^4 = 1048576`. The Linnik premise holds concretely at the `n=32` rung (Shaw's resolved
`{97}`) with the EXACT `2^(5a)` search bound. -/
theorem linnik_rung_a5 :
    smallestPrime1ModN (2 ^ 5) (2 ^ (5 * 5)) < (2 ^ 5) ^ 4 := by
  rw [show (2 ^ 5 : ℕ) = 32 from by norm_num, smallestPrime1ModN_32_pow25_eq_97]
  decide

/-- **Two-rung Linnik harvest.** Bundles both resolved rungs of input (2) of `floor_closes_by_linnik`:
the least prime `≡ 1 mod 2^a` is below prize scale `(2^a)^4` at the two rungs `a = 4` (`17 < 16^4`)
and `a = 5` (`97 < 32^4`) that Shaw's exact scanner verified. This grounds the closure's Linnik
premise concretely at every rung resolved so far; the universal `∀ a ≥ 4` statement remains the open
analytic-NT input (Linnik/Thorner–Zaman exponent `< 4` for powerful moduli; GRH gives `2+ε`).
No CORE / BGK / cancellation / completion claim. -/
theorem linnik_two_rung_harvest :
    smallestPrime1ModN (2 ^ 4) (2 ^ (5 * 4)) < (2 ^ 4) ^ 4
      ∧ smallestPrime1ModN (2 ^ 5) (2 ^ (5 * 5)) < (2 ^ 5) ^ 4 :=
  ⟨linnik_rung_a4, linnik_rung_a5⟩

-- Axiom audits (must show only [propext, Classical.choice, Quot.sound]).
#print axioms smallestPrime1ModN_eq_of_witness
#print axioms smallestPrime1ModN_16_pow20_eq_17
#print axioms smallestPrime1ModN_32_pow25_eq_97
#print axioms linnik_rung_a4
#print axioms linnik_rung_a5
#print axioms linnik_two_rung_harvest

end ArkLib.ProximityGap.Frontier.FloorLinnikRung
