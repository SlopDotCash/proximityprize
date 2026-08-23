/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PrimitiveFactorCovering

/-!
# Non-Mersenne Conj 1.12 witnesses: primitive-factor admissibility (#389)

> **`primitiveFactor_admissible`** — for odd `m ≥ 3` and a prime `q ∣ 2^m − 1` with
> `ord(2 mod q) = m` (a primitive prime factor), `(q, q, 2m)` is admissible (Def 1.11): the subgroup
> `⟨−2⟩ ⊆ F_q^×` of order `2m` has its `m`-fold distinct sumset equal to all of `F_q`.

This is the **Zsygmondy generalization of the Mersenne witness** (`mersenne_admissible`,
which is the special case `q = 2^m − 1`). By Zsygmondy such `q` exist for all `m > 6` — infinitely
many distinct primes — so with the order bound `2m ≤ 10 log₂ q` (`q ≥ 2^{m/5}`) each is a Conjecture
1.12 witness. Hence Conj 1.12 follows from "`∃^∞ m: P(2^m−1) ≥ 2^{m/5}`" (a largest-prime-factor
statement, cf. Stewart) — a broader sufficient condition than the infinitude of Mersenne primes. The
admissibility (covering + subgroup structure) is proved here unconditionally; the large-factor input
is the open half. Axiom-clean. Issue #389.
-/

open Finset
open ArkLib.ProximityGap.SubgroupSumset
open ArkLib.ProximityGap.PrimitiveFactorCovering

namespace ArkLib.ProximityGap.PrimitiveFactorCovering

variable {m : ℕ} {q : ℕ} [Fact q.Prime]

/-- **Primitive-factor admissibility.** `(q, q, 2m)` is admissible for any primitive prime factor
`q ∣ 2^m − 1` (odd `m ≥ 3`) — the Zsygmondy generalization of `mersenne_admissible`. -/
theorem primitiveFactor_admissible (hm : Odd m) (hm3 : 3 ≤ m) (hdvd : q ∣ 2 ^ m - 1)
    (hord : orderOf (2 : ZMod q) = m) :
    Admissible q q (2 * m) := by
  haveI : NeZero (2 ^ m - 1) :=
    ⟨by have : 1 < 2 ^ m := Nat.one_lt_two_pow_iff.mpr (by omega); omega⟩
  have hinj := castHom_injOn_signedPowers hm hm3 hdvd hord
  refine ⟨(signedPowers m).image (red hdvd), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- 1 ∈ G
    rw [Finset.mem_image]
    refine ⟨1, ?_, map_one _⟩
    rw [mem_signedPowers_iff hm3]; exact ⟨0, by omega, Or.inl (pow_zero _).symm⟩
  · -- 0 ∉ G
    rw [Finset.mem_image]; rintro ⟨x, hx, hx0⟩
    rw [mem_signedPowers_iff hm3] at hx
    obtain ⟨i, _, hxi⟩ := hx
    have h2u : (2 : ZMod q) ^ i ≠ 0 := pow_ne_zero _ (two_ne_zero_zmod (by omega) hdvd)
    rcases hxi with rfl | rfl
    · rw [red_two_pow] at hx0; exact h2u hx0
    · rw [map_neg, red_two_pow, neg_eq_zero] at hx0; exact h2u hx0
  · -- mul-closed
    intro a ha b hb
    rw [Finset.mem_image] at ha hb ⊢
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    refine ⟨x * y, ?_, map_mul _ _ _⟩
    rw [mem_signedPowers_iff hm3] at hx hy ⊢
    obtain ⟨i, _, hxi⟩ := hx
    obtain ⟨j, _, hyj⟩ := hy
    have hmod : (2 : ZMod (2 ^ m - 1)) ^ (i + j) = (2 : ZMod (2 ^ m - 1)) ^ ((i + j) % m) :=
      two_pow_mod hm3 (i + j)
    refine ⟨(i + j) % m, Nat.mod_lt _ (by omega), ?_⟩
    rcases hxi with rfl | rfl <;> rcases hyj with rfl | rfl
    · exact Or.inl (by rw [← pow_add]; exact hmod)
    · exact Or.inr (by rw [mul_neg, ← pow_add, hmod])
    · exact Or.inr (by rw [neg_mul, ← pow_add, hmod])
    · exact Or.inl (by rw [neg_mul_neg, ← pow_add]; exact hmod)
  · -- |G| = 2m
    rw [Finset.card_image_of_injOn hinj, signedPowers_card hm3]
  · -- the m-fold distinct sumset is everything, so q ≤ its size
    have hcov : sumsetDistinct ((signedPowers m).image (red hdvd)) (2 * m / 2) = Finset.univ := by
      rw [show 2 * m / 2 = m by omega]
      exact primitiveFactor_signedPowers_covers hm hm3 hdvd hord
    have hcard : (sumsetDistinct ((signedPowers m).image (red hdvd)) (2 * m / 2)).card = q := by
      rw [hcov, Finset.card_univ, ZMod.card]
    exact le_of_eq hcard.symm

end ArkLib.ProximityGap.PrimitiveFactorCovering

#print axioms ArkLib.ProximityGap.PrimitiveFactorCovering.primitiveFactor_admissible
