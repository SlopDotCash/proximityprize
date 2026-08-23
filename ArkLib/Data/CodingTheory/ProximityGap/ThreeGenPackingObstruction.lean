/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.TwoGenPackingCapacity

/-!
# Issue #232 — PAIRWISE CAPACITY IS NOT ENOUGH AT THREE GENERATORS: the
# chromatic triangle obstruction (O119's named next (a), resolved NO)

O119 closed the two-generator packing problem as an iff (the ceiling
capacity law).  This file proves the answer to its named question — does
PAIRWISE capacity (+ volume) determine packability for `k ≥ 3` generators? —
is **NO**, with the obstruction mechanism identified and proven in general:

* `triangle_obstruction` — **the chromatic triangle law**: for any `n` and
  three divisors `d₁, d₂, d₃` whose pairwise step-gcds all divide `2`
  (`gcd(n/dᵢ, n/dⱼ) ∣ 2`), NO choice of canonical bases makes the three
  cosets pairwise disjoint.  Mechanism: O119's CRT lemma says disjointness
  forces bases to DIFFER mod each pairwise gcd, hence (gcd ∣ 2) to differ
  mod 2 — and three values cannot be pairwise distinct in `ℤ/2`.  Packing is
  graph coloring on the class structure; a triangle is not 2-colorable.
* `three_gen_separation` — **the headline separation** at the minimal witness
  `n = 12`, `(d₁, d₂, d₃) = (2, 3, 6)` (steps `6, 4, 2`, all pairwise gcds
  `= 2`): every PAIR among `{μ_2, μ_3, μ_6}` packs (each pairwise O119
  capacity holds — `⌈1/m⌉ + ⌈1/m'⌉ = 2 ≤ 2 = G`, witnessed through
  `packable_of_capacity`), the volume `2 + 3 + 6 = 11 ≤ 12` leaves room, yet
  the triple is unpackable.

Probe (`scripts/probes/probe_three_gen_packing.py`, exit 0): exhaustive over
all volume-feasible multiplicity vectors at `n ∈ {12, 18, 24, 36}` — 629
pairwise-capacity-satisfying, volume-feasible, UNPACKABLE witnesses
(2 / 6 / 94 / 527 per modulus), the minimal being this file's
`{μ_2, μ_3, μ_6}` at `n = 12`; O119 necessity (packable ⟹ pairwise
capacity) confirmed on every packable instance, zero violations.

**Consequence for the packing program**: the `k`-generator realizability
problem is genuinely a CLASS-GRAPH COLORING / simultaneous-allocation
problem (Berger–Felzenbaum–Fraenkel disjoint-covering-systems territory),
not a pairwise-local one.  The hierarchy is now strict and machine-checked
at every level: one-sided span (O107) ⊊ two-sided span (O116) ⊊ pairwise
capacity (O119) ⊊ packability.
-/

namespace ThreeGenPackingObstruction

open Finset DeBruijnWindowedLaw TwoGenPackingCapacity

/-- **The chromatic triangle obstruction**: three divisors of `n` whose
pairwise step-gcds all divide `2` admit NO pairwise-disjoint triple of
canonical cosets — disjointness would force three pairwise-distinct parities.
The pairwise-gcd hypothesis is exactly the "all class moduli `≤ 2`" regime;
`gcd = 1` pairs are unconditionally obstructed (O116's CRT instance), and
`gcd = 2` pairs force distinct parities, of which only two exist. -/
theorem triangle_obstruction {n d₁ d₂ d₃ : ℕ} (hn : 0 < n)
    (h₁ : d₁ ∣ n) (h₂ : d₂ ∣ n) (h₃ : d₃ ∣ n)
    (g₁₂ : Nat.gcd (n / d₁) (n / d₂) ∣ 2)
    (g₁₃ : Nat.gcd (n / d₁) (n / d₃) ∣ 2)
    (g₂₃ : Nat.gcd (n / d₂) (n / d₃) ∣ 2)
    {r₁ r₂ r₃ : ℕ} (hr₁ : r₁ < n / d₁) (hr₂ : r₂ < n / d₂) (hr₃ : r₃ < n / d₃) :
    ¬ (Disjoint (cosetOf n d₁ r₁) (cosetOf n d₂ r₂)
        ∧ Disjoint (cosetOf n d₁ r₁) (cosetOf n d₃ r₃)
        ∧ Disjoint (cosetOf n d₂ r₂) (cosetOf n d₃ r₃)) := by
  rintro ⟨h12, h13, h23⟩
  -- disjointness forces bases to differ mod 2 (through each pairwise gcd)
  have key : ∀ {d d' : ℕ} {r r' : ℕ}, d ∣ n → d' ∣ n →
      r < n / d → r' < n / d' → Nat.gcd (n / d) (n / d') ∣ 2 →
      Disjoint (cosetOf n d r) (cosetOf n d' r') → r % 2 ≠ r' % 2 := by
    intro d d' r r' hdn hd'n hr hr' hg hdisj heq2
    refine cosetOf_not_disjoint_cross hn hdn hd'n hr hr' ?_ hdisj
    -- bases agree mod 2 and gcd ∣ 2 ⟹ agree mod gcd (gcd ∈ {1, 2})
    rcases (Nat.dvd_prime Nat.prime_two).mp hg with h1 | h2
    · rw [h1]
      omega
    · rw [h2]
      exact heq2
  have k12 := key h₁ h₂ hr₁ hr₂ g₁₂ h12
  have k13 := key h₁ h₃ hr₁ hr₃ g₁₃ h13
  have k23 := key h₂ h₃ hr₂ hr₃ g₂₃ h23
  -- three pairwise-distinct parities cannot exist
  have m₁ : r₁ % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have m₂ : r₂ % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have m₃ : r₃ % 2 < 2 := Nat.mod_lt _ (by norm_num)
  omega

/-- **The separation headline** at the minimal witness `n = 12`,
`(d₁, d₂, d₃) = (2, 3, 6)`:

1. each PAIR packs (the O119 capacity condition holds pairwise),
2. the volume `2 + 3 + 6 = 11 ≤ 12` leaves room,
3. yet NO triple of canonical bases is pairwise disjoint —

pairwise capacity + volume do NOT determine `k ≥ 3` packability. -/
theorem three_gen_separation :
    (Packable 12 2 3 1 1 ∧ Packable 12 2 6 1 1 ∧ Packable 12 3 6 1 1)
      ∧ 1 * 2 + 1 * 3 + 1 * 6 ≤ 12
      ∧ ∀ r₁ < 6, ∀ r₂ < 4, ∀ r₃ < 2,
          ¬ (Disjoint (cosetOf 12 2 r₁) (cosetOf 12 3 r₂)
              ∧ Disjoint (cosetOf 12 2 r₁) (cosetOf 12 6 r₃)
              ∧ Disjoint (cosetOf 12 3 r₂) (cosetOf 12 6 r₃)) := by
  refine ⟨⟨?_, ?_, ?_⟩, by norm_num, ?_⟩
  · exact packable_of_capacity (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by decide)
  · exact packable_of_capacity (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by decide)
  · exact packable_of_capacity (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by decide)
  · intro r₁ hr₁ r₂ hr₂ r₃ hr₃
    exact triangle_obstruction (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide) (by decide) (by decide) hr₁ hr₂ hr₃

/-- The G = 1 face of the triangle law, fired at the second witness family
`(4, 6, 12)` at `n = 12` (steps `3, 2, 1` — all pairwise gcds `∣ 2`, two of
them `= 1`): unpackable for every base choice. -/
example : ∀ r₁ < 3, ∀ r₂ < 2, ∀ r₃ < 1,
    ¬ (Disjoint (cosetOf 12 4 r₁) (cosetOf 12 6 r₂)
        ∧ Disjoint (cosetOf 12 4 r₁) (cosetOf 12 12 r₃)
        ∧ Disjoint (cosetOf 12 6 r₂) (cosetOf 12 12 r₃)) := by
  intro r₁ hr₁ r₂ hr₂ r₃ hr₃
  exact triangle_obstruction (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) hr₁ hr₂ hr₃

end ThreeGenPackingObstruction

#print axioms ThreeGenPackingObstruction.triangle_obstruction
#print axioms ThreeGenPackingObstruction.three_gen_separation
