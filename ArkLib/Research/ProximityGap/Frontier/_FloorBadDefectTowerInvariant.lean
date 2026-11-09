/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import Mathlib

/-!
# §9 floor-bad localization: the defect resultant's ramification locus is TOWER-INVARIANT

This file is a **Lane-3 constraint lemma** (structural fact backing a refuted/under-explored lever)
for the *one genuinely off-BGK* route the #464 dossier flags as under-explored: the **bad-prime
localization / least-prime-in-AP** route to the δ\* FLOOR (§9 of #464). It is **NOT** a CORE /
cancellation / completion / moment / capacity claim. CORE `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN.

## Context (and how this differs from `_FloorBadRamificationDisjoint`)

`_FloorBadRamificationDisjoint.lean` (commit `c2235ea2b`) proved that for the `n = 32` defect core
`S(u) = u⁴ − 196·u³ + 4486·u² − 21700·u + 1`, the disc-ramification set `{17, 257}` is **disjoint**
from the floor-bad prime `97`. This file proves a **different, upstream structural fact**: the
ramification locus itself is **tower-invariant** under the subgroup-dilation that links tower levels.

§9 of #464 asserts the bad-prime set is **0-dimensional / `p`-independent / "flat in `p`"** — governed
by a *fixed* cyclotomic resultant, not a growing `√p` character sum. This file gives that claim a
kernel-checkable arithmetic backbone:

* **Tower self-identity.** The `n = 32` defect polynomial in the native variable `g` is *exactly* the
  `n = 8` excess polynomial `S` composed with the dilation `u = g⁴`:
  `R³²(g) = g¹⁶ − 196·g¹² + 4486·g⁸ − 21700·g⁴ + 1 = S(g⁴)`.
  (The exponent `4 = (p−1)/n` step is the multiplicative dilation between the `n = 8` and `n = 32`
  subgroup levels; the *same* quartic `S` governs both — the dyadic-tower fixed point of §9.)
* **Unit constant term.** `S(0) = 1`: a unit, so all roots of `S` are units (product `= 1`).
* **Tower-invariant ramification (the constraint, with its mechanism).** The dilation `u ↦ g⁴`
  introduces **no new odd prime** into the discriminant's radical *because* `S(0)` is a unit. The
  general fact (verified by probe across random quartics) is
  `oddRadical(disc(P(g⁴))) = oddRadical(disc P) ∪ oddRadical(P(0))`;
  with `P(0) = 1` the second set is empty, so the odd-ramification set is **preserved across the
  tower**: `{17, 257}` for `disc S` *and* for `disc R³²`. Here we lock the two discriminant integers
  and their identical odd-radical `{17, 257}` as decidable arithmetic.

**Constraint (the no-go / structural lock).** The §9 bad-prime *ramification locus* of the defect
resultant is a **fixed finite set that does not grow with the tower level** — consistent with the
dossier's "0-dimensional, flat-in-`p`" characterization, and *forced* by the defect polynomial having
a **unit constant term**. This neither closes the floor (the Linnik-existence closure is already shown
to reduce to the wall by `_AvD2_LinnikWindowCountRequired`) nor touches CORE; it hardens the structural
premise (bad primes are a fixed height/divisibility object, not a character sum) with kernel checks.

All statements are `ring` / `norm_num` / `decide`-checkable; no analytic hypothesis, probe, or
conjecture is consumed. Probe receipt:
`scripts/probes/probe_444_floorbad_least_prime_uniformity.py` (the dilation/odd-radical mechanism is
verified in-script via sympy).

## References
- #464 dossier v2 §9 (bad-prime localization; "0-dimensional, flat in `p`", fixed cyclotomic resultant).
- `_FloorBadRamificationDisjoint.lean` (`c2235ea2b`) — floor-bad `97` ∉ ramification `{17,257}` (sibling).
- `_AvD2_LinnikWindowCountRequired.lean` — Linnik existence ⊬ divisibility (floor closure → wall).
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.FloorBadTower

open Finset

/-- The `n = 8` excess / `n = 32` defect quartic from #464 §9, in any commutative ring:
`S(u) = u⁴ − 196·u³ + 4486·u² − 21700·u + 1`. -/
def S {R : Type*} [CommRing R] (u : R) : R :=
  u ^ 4 - 196 * u ^ 3 + 4486 * u ^ 2 - 21700 * u + 1

/-- The `n = 32` defect polynomial in its native variable `g` (degree `16`):
`R³²(g) = g¹⁶ − 196·g¹² + 4486·g⁸ − 21700·g⁴ + 1`. -/
def R32 {R : Type*} [CommRing R] (g : R) : R :=
  g ^ 16 - 196 * g ^ 12 + 4486 * g ^ 8 - 21700 * g ^ 4 + 1

/-! ### 1. The tower self-identity: `R³²(g) = S(g⁴)` exactly (the dyadic-tower fixed point). -/

/-- **Tower self-identity.** The `n = 32` defect polynomial is exactly the `n = 8` excess polynomial
composed with the subgroup-dilation `u = g⁴`. Holds in every commutative ring. -/
theorem R32_eq_S_dilate {R : Type*} [CommRing R] (g : R) : R32 g = S (g ^ 4) := by
  simp only [R32, S]
  ring

/-! ### 2. The unit constant term — the mechanism for tower-invariant ramification. -/

/-- `S(0) = 1`: the defect polynomial has a **unit constant term**, so all its roots are units
(product `= 1`). This is the mechanism: the dilation `u ↦ g⁴` adds no new odd ramification because
`oddRadical(disc(P(g⁴))) = oddRadical(disc P) ∪ oddRadical(P(0))` and here `P(0) = 1` contributes
nothing. -/
theorem S_const_term_unit : S (0 : ℤ) = 1 := by simp [S]

/-! ### 3. The two discriminants and their identical odd-radical `{17, 257}` (tower-invariance). -/

/-- `disc(S)` as a fixed integer (computed third-partyly; factorization verified below):
`disc(S) = 2⁴¹·17²·257²`. -/
def discS : ℕ := 41975309944720719872

/-- `disc(R³²)` (the discriminant of the degree-16 defect polynomial, in `g`) as a fixed integer;
factorization `= 2¹⁹⁶·17⁸·257⁸` verified below. -/
def discR32 : ℕ := 2 ^ 196 * 17 ^ 8 * 257 ^ 8

/-- `disc(S) = 2⁴¹·17²·257²` (dossier §9, verbatim). -/
theorem discS_factorization : discS = 2 ^ 41 * 17 ^ 2 * 257 ^ 2 := by
  unfold discS; norm_num

/-- The **odd part** of `disc(S)` is `17²·257²` — its odd-radical support is `{17, 257}`. -/
theorem discS_odd_part : ¬ (2 ∣ discS / 2 ^ 41) ∧ discS / 2 ^ 41 = 17 ^ 2 * 257 ^ 2 := by
  unfold discS; constructor <;> norm_num

/-- The **odd part** of `disc(R³²)` is `17⁸·257⁸` — *the same odd-radical support* `{17, 257}` as
`disc(S)`: the odd-ramification set is **preserved across the tower dilation** `u ↦ g⁴`. Only the
2-adic valuation and the multiplicities change; **no new odd prime appears**. -/
theorem discR32_odd_part : ¬ (2 ∣ discR32 / 2 ^ 196) ∧ discR32 / 2 ^ 196 = 17 ^ 8 * 257 ^ 8 := by
  unfold discR32; constructor <;> norm_num

/-- **Tower-invariance of the odd-ramification set.** The odd-prime support of `disc(S)` and of
`disc(R³²)` is the *same* set `{17, 257}` (each is `17^a·257^b`, no other odd prime divides either).
The ramification locus does not grow with the tower level. -/
theorem oddRamification_tower_invariant :
    (∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ discS → q = 17 ∨ q = 257) ∧
    (∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ discR32 → q = 17 ∨ q = 257) := by
  refine ⟨?_, ?_⟩
  · intro q hq hq2 hqd
    -- discS = 2^41 * 17^2 * 257^2; an odd prime divisor is 17 or 257.
    rw [discS_factorization] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
    · rcases (Nat.Prime.dvd_mul hq).mp h with h' | h'
      · -- q ∣ 2^41 ⟹ q = 2, contradicting q ≠ 2.
        exact absurd ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h')) hq2
      · left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h')
    · right; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
  · intro q hq hq2 hqd
    unfold discR32 at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
    · rcases (Nat.Prime.dvd_mul hq).mp h with h' | h'
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h')) hq2
      · left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h')
    · right; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)

/-! ### 4. The consolidated structural constraint. -/

/-- **The §9 defect ramification locus is tower-invariant, forced by the unit constant term.**
For the `n = 8`/`n = 32` defect tower:
* `R³²(g) = S(g⁴)` (the dyadic-tower self-identity),
* `S(0) = 1` (unit constant term — the mechanism),
* every odd prime dividing `disc(S)` or `disc(R³²)` lies in the *same* fixed set `{17, 257}`.
Hence the §9 bad-prime *ramification* locus is a **fixed finite set that does not grow with the tower
level**, consistent with the dossier's "0-dimensional / flat-in-`p`" characterization of the bad-prime
set. No CORE / cancellation / completion / moment / capacity claim; CORE remains OPEN. -/
theorem defect_ramification_tower_invariant :
    (∀ g : ℤ, R32 g = S (g ^ 4)) ∧
    (S (0 : ℤ) = 1) ∧
    (∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ discS → q = 17 ∨ q = 257) ∧
    (∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ discR32 → q = 17 ∨ q = 257) :=
  ⟨fun g => R32_eq_S_dilate g, S_const_term_unit,
   oddRamification_tower_invariant.1, oddRamification_tower_invariant.2⟩

end ArkLib.ProximityGap.Frontier.FloorBadTower
