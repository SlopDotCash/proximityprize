/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FloorLinnikThornerZamanArrow
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AssaultV2_FloorLocalizationN32

/-!
# Driving the off-BGK floor closure by the unconditional Thorner–Zaman hypothesis (#444 / #464)

`_FloorLinnikRungInstances` discharged `LinnikLeastPrimeBelowPrize` at the two RESOLVED rungs `a=4,5`,
and `_FloorLinnikThornerZamanArrow` built the elementary arrow from the named TZ supply hypothesis to
"`∃ prime p ≡ 1 mod n, p ≤ n^4`" at the unconditional exponent `β = 3`. This file CONNECTS the two:
it shows the TZ supply hypothesis (held at every rung) implies the EXACT closure premise
`LinnikLeastPrimeBelowPrize` (`smallestPrime1ModN (2^a) (2^(5a)) < (2^a)^4`), and hence drives
`floor_closes_by_linnik` from the unconditional TZ input rather than the abstract Linnik `Prop`.

The bridging fact is a least-prime monotonicity companion to `_FloorLinnikRungInstances`:
`smallestPrime1ModN_le_of_witness` — the least prime `≡ 1 mod n` in range is `≤` ANY prime `≡ 1 mod n`
that lies within the search bound. TZ supplies such a witness `q ≤ 2n^β < n^4 ≤ 2^(5a)` (the search
bound), pinning `smallestPrime1ModN (2^a) (2^(5a)) ≤ q < (2^a)^4`.

## Honesty (scope)

The DEEP analytic content remains entirely inside the named `TZPrimeSupply` hypothesis (NEVER an axiom;
the [TZ24] literature statement, supplied by explicit hypothesis). This file proves only the ELEMENTARY
"least ≤ witness" + arithmetic packaging that turns a TZ supply at every `2^a` into the closure's
least-prime premise. It does NOT prove `TZPrimeSupply`, does NOT prove `FloorLocalizationUniform`
(input (1), still open), and does NOT touch the BGK/Paley sup-norm wall. CORE stays OPEN.
-/

set_option linter.style.longLine false


open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.FloorLocalization
open ArkLib.ProximityGap.Frontier.FloorLinnikTZArrow

namespace ArkLib.ProximityGap.Frontier.FloorLinnikTZClosure

/-- **Least-prime ≤ any in-range witness.** If `q` is a prime `≡ 1 mod n` with `q ≤ bound`, then
`smallestPrime1ModN n bound ≤ q`: the head of the filtered `range (bound+1)` is the minimal qualifying
element, hence `≤` any qualifying `q` in range. (Companion to `smallestPrime1ModN_eq_of_witness`; here
we need no minimality of `q`, only that it qualifies and is in range.) -/
theorem smallestPrime1ModN_le_of_witness {n bound q : ℕ}
    (hqb : q ≤ bound) (hqmod : q % n = 1) (hqp : q.Prime) :
    smallestPrime1ModN n bound ≤ q := by
  unfold smallestPrime1ModN
  set P : ℕ → Bool := fun p => p % n == 1 && p.Prime with hP
  set L : List ℕ := (List.range (bound + 1)).filter P with hL
  -- q is a member of the filtered list (in range and passes P)
  have hqmem : q ∈ L := by
    rw [hL, List.mem_filter]
    refine ⟨List.mem_range.mpr (by omega), ?_⟩
    simp only [hP, Bool.and_eq_true, beq_iff_eq]
    exact ⟨by simpa using hqmod, decide_eq_true hqp⟩
  -- the list is `≤`-pairwise (filter is a sublist of the strictly-`<`-sorted range, weakened to `≤`)
  have hpw : L.Pairwise (· ≤ ·) := by
    have hlt : L.Pairwise (· < ·) := by
      rw [hL]
      have hrange : (List.range (bound + 1)).Pairwise (· < ·) :=
        (List.sortedLT_range (bound + 1)).pairwise
      exact hrange.sublist List.filter_sublist
    exact hlt.imp (fun h => le_of_lt h)
  -- nonempty ⟹ head exists; head of a `≤`-pairwise list is `≤` every element, in particular `≤ q`
  cases hLcase : L with
  | nil => rw [hLcase] at hqmem; exact absurd hqmem (List.not_mem_nil)
  | cons hd tl =>
    have hpwc : (hd :: tl).Pairwise (· ≤ ·) := hLcase ▸ hpw
    have hheadle : ∀ x ∈ (hd :: tl), hd ≤ x := by
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · exact le_of_eq h.symm
      · exact (List.pairwise_cons.mp hpwc).1 x h
    have hhead : (hd :: tl).head?.getD 0 = hd := rfl
    rw [hhead]
    exact hheadle q (hLcase ▸ hqmem)

/-- **TZ supply at a rung ⇒ the Linnik premise at that rung.** Fix `n = 2^a` with `a ≥ 4`. If the TZ
window holds a prime (`TZPrimeSupply (2^a) β 1`) at an exponent `12/5 < β ≤ 3`, then the least prime
`≡ 1 mod 2^a` within the closure's search bound `2^(5a)` is below prize scale `(2^a)^4`. The TZ witness
`q ≤ 2n^β < n^4 = 2^(4a) ≤ 2^(5a)` lands inside the search bound, and `smallestPrime1ModN ≤ q < n^4`. -/
theorem linnik_rung_of_tzSupply {a : ℕ} {β : ℝ} (ha : 4 ≤ a) (hβ : β ≤ 3)
    (hTZ : TZPrimeSupply (2 ^ a) β 1) :
    smallestPrime1ModN (2 ^ a) (2 ^ (5 * a)) < (2 ^ a) ^ 4 := by
  -- n = 2^a ≥ 16 ≥ 2
  have hn2 : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- TZ witness: prime q ≡ 1 mod 2^a with (q:ℝ) ≤ (2^a)^4
  obtain ⟨q, hqp, hqmod, hqle⟩ := tzSupplyOne_gives_residue_prime_below_prize hn2 hβ hTZ
  -- (2^a)^4 < 2^(5a), so q ≤ (2^a)^4 ≤ 2^(5a) in ℕ
  have hq_nat_le : q ≤ (2 ^ a) ^ 4 := by
    have : ((q : ℝ)) ≤ (((2 ^ a) ^ 4 : ℕ) : ℝ) := by push_cast at hqle ⊢; exact hqle
    exact_mod_cast this
  have hpow_lt : (2 ^ a) ^ 4 < 2 ^ (5 * a) := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hq_in_bound : q ≤ 2 ^ (5 * a) := le_of_lt (lt_of_le_of_lt hq_nat_le hpow_lt)
  -- the least prime in range is ≤ q
  have hle := smallestPrime1ModN_le_of_witness hq_in_bound hqmod hqp
  -- q itself is below prize scale: need strict. We have q ≤ (2^a)^4; upgrade to <.
  -- q ≤ 2n^β and 2n^β ≤ n^4 with n ≥ 2; in fact 2n^β < n^4 strictly is not guaranteed at β=3,n=2.
  -- Use the in-range least ≤ q ≤ (2^a)^4; for the strict closure bound, note q is PRIME hence q ≠ (2^a)^4
  -- ((2^a)^4 is a perfect 4th power > 1, not prime), so q < (2^a)^4.
  have hq_ne : q ≠ (2 ^ a) ^ 4 := by
    intro hqeq
    -- (2^a)^4 is not prime: it is a 4th power (exponent 4 ≥ 2)
    have hnotprime : ¬ ((2 ^ a) ^ 4).Prime :=
      Nat.Prime.not_prime_pow (x := 2 ^ a) (n := 4) (by norm_num)
    exact hnotprime (hqeq ▸ hqp)
  have hq_lt : q < (2 ^ a) ^ 4 := lt_of_le_of_ne hq_nat_le hq_ne
  exact lt_of_le_of_lt hle hq_lt

/-- **`LinnikLeastPrimeBelowPrize` from a uniform TZ supply.** If the named TZ hypothesis holds at a
fixed exponent `β ≤ 3` for every dyadic modulus `2^a` (`a ≥ 4`) — exactly [TZ24]'s unconditional
`β > 12/5` regime for the powerful moduli `2^a` — then the closure's Linnik premise
`LinnikLeastPrimeBelowPrize` holds, with NO appeal to GRH and NO new axiom. The deep analytic input is
precisely the per-rung `TZPrimeSupply` family. -/
theorem linnikLeastPrimeBelowPrize_of_tzSupplyFamily {β : ℝ} (hβ : β ≤ 3)
    (hTZfam : ∀ a : ℕ, 4 ≤ a → TZPrimeSupply (2 ^ a) β 1) :
    LinnikLeastPrimeBelowPrize := by
  intro a ha
  exact linnik_rung_of_tzSupply ha hβ (hTZfam a ha)

/-- **The off-BGK floor closes from `FloorLocalizationUniform` + a uniform TZ supply.** Combining the
in-tree closure `floor_closes_by_linnik` with `linnikLeastPrimeBelowPrize_of_tzSupplyFamily`: given the
realizability characterization (input (1), still open) AND the unconditional TZ supply family
(input (2), now the literature hypothesis rather than an abstract `Prop`), every prize-regime prime
`p ≥ (2^a)^4` is floor-GOOD. This is the dossier's "Thorner–Zaman is the realistic unconditional
target" route, formalized to the EXACT closure interface. CORE stays OPEN — this is the FLOOR, off the
BGK sup-norm wall, and input (1) is unproven. -/
theorem floor_closes_by_tzSupplyFamily
    (FloorBad : ℕ → ℕ → Prop) (hUnif : FloorLocalizationUniform FloorBad)
    {β : ℝ} (hβ : β ≤ 3) (hTZfam : ∀ a : ℕ, 4 ≤ a → TZPrimeSupply (2 ^ a) β 1)
    (a : ℕ) (ha : 4 ≤ a) (p : ℕ) (hp : p.Prime) (hmod : p % (2 ^ a) = 1)
    (hprize : (2 ^ a) ^ 4 ≤ p) :
    ¬ FloorBad (2 ^ a) p :=
  floor_closes_by_linnik FloorBad hUnif
    (linnikLeastPrimeBelowPrize_of_tzSupplyFamily hβ hTZfam) a ha p hp hmod hprize

-- Axiom audits (must show only [propext, Classical.choice, Quot.sound]).
#print axioms smallestPrime1ModN_le_of_witness
#print axioms linnik_rung_of_tzSupply
#print axioms linnikLeastPrimeBelowPrize_of_tzSupplyFamily
#print axioms floor_closes_by_tzSupplyFamily

end ArkLib.ProximityGap.Frontier.FloorLinnikTZClosure
