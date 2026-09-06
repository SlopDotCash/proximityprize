/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import Mathlib

/-!
# §9 floor-bad localization: the disc-ramification set is DISJOINT from the floor-bad prime

This file is a **Lane-3 constraint lemma** (refuted-lever / no-go) for the *one genuinely off-BGK*
route the #464 dossier flags as under-explored: the **bad-prime localization / least-prime-in-AP**
route to the δ\* FLOOR (§9 of #464). It is NOT a CORE / cancellation / completion / moment /
capacity claim. CORE `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN.

## What §9 actually claims (and the subtle conflation this file pins)

The #464 dossier §9 describes the `n = 32` defect core via a fixed integer polynomial
> `S(u) = u⁴ − 196·u³ + 4486·u² − 21700·u + 1`   (`= R^(32)(g)` with `u = g⁴`),
> `disc(S) = 2⁴¹·17²·257²`, "root-count drops exactly at `{17, 257}`",
and separately states the **FLOOR-bad** prime is "the single smallest prime `≡ 1 (mod n)`",
which for `n = 32` is `97`.

Read naïvely ("the defect/ramification set selects the floor-bad prime") these would coincide.
They DO NOT. This file proves, by fully-decidable finite arithmetic, that the two sets are
**disjoint**:

* The **disc-ramification set** of `S` (odd primes `p` with `p ∣ disc(S)`, equivalently where `S`
  acquires a repeated root mod `p` and its mod-`p` root-count drops below the generic `4`) is
  `{17, 257}` among odd primes — *verified*: `17 ∣ disc`, `257 ∣ disc`, and at each of them `S` has
  only `3` roots mod `p`.
* The **floor-bad prime** for `n = 32`, `97 = ` least prime `≡ 1 (mod 32)`, is **UNRAMIFIED**:
  `97 ∤ disc(S)`, and `S` has the *full* `4` roots mod `97`.
* `17 ≢ 1 (mod 32)` (it is not even in the arithmetic progression), and `257 ≡ 1 (mod 32)` but
  `257 ≠ 97`. So neither ramified prime is the floor-bad prime.

**Constraint (the no-go).** Any attempt to *identify* the §9 floor-bad prime from the discriminant
/ ramification of the defect resultant fails: ramification (`p ∣ disc`, root-count drop) and
floor-badness (least `p ≡ 1 mod n`, benign `M`) are governed by **different** arithmetic and are
disjoint at `n = 32`. The floor route therefore cannot be closed by a "ramified ⟹ bad / unramified
⟹ good" reading; the floor-bad selector is the *least-prime-in-AP* object, not the resultant's
ramification locus. (This is consistent with `_AvD2_LinnikWindowCountRequired`, which already proves
the *Linnik-existence* closure of the floor route reduces to the wall: existence ⊬ divisibility.)

All statements below are `decide`/`norm_num`-checkable finite arithmetic over `ℕ` / `ZMod p`; no
analytic hypothesis, no probe, no conjecture is consumed. Probe receipt:
`scripts/probes/probe_444_floorbad_ramif.py`.

## References
- #464 dossier v2 §9 (bad-prime localization, the off-BGK floor lever) and §10 (numerics).
- `_AvD2_LinnikWindowCountRequired.lean` (Linnik existence ⊬ divisibility — the floor closure trap).
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.FloorBadRamif

open Finset

/-- The `n = 32` defect core polynomial from #464 §9, evaluated in any commutative ring `R`:
`S(u) = u⁴ − 196·u³ + 4486·u² − 21700·u + 1`. -/
def S {R : Type*} [CommRing R] (u : R) : R :=
  u ^ 4 - 196 * u ^ 3 + 4486 * u ^ 2 - 21700 * u + 1

/-- The discriminant of `S`, as a fixed natural number (computed third-partyly; verified factorization
below): `disc(S) = 2⁴¹·17²·257² = 41975309944720719872`. -/
def discS : ℕ := 41975309944720719872

/-- The discriminant factors exactly as the dossier §9 states: `2⁴¹·17²·257²`. -/
theorem discS_factorization : discS = 2 ^ 41 * 17 ^ 2 * 257 ^ 2 := by
  unfold discS; norm_num

/-- The number of roots of `S` in `ZMod p`, over all `p` residues. -/
def rootCountMod (p : ℕ) [NeZero p] : ℕ :=
  (Finset.univ.filter (fun u : ZMod p => S u = 0)).card

/-! ### 1. The disc-ramification set `{17, 257}` — root-count DROPS (repeated root, `p ∣ disc`). -/

/-- `17 ∣ disc(S)`: `17` is a ramified prime of `S`. -/
theorem seventeen_dvd_disc : 17 ∣ discS := by unfold discS; norm_num

/-- `257 ∣ disc(S)`: `257` is a ramified prime of `S`. -/
theorem twoFiftySeven_dvd_disc : 257 ∣ discS := by unfold discS; norm_num

/-- At the ramified prime `17`, `S` has only `3` roots in `ZMod 17` (drop from the generic `4`). -/
theorem rootCount_17 : rootCountMod 17 = 3 := by decide

/-- At the ramified prime `257`, `S` has only `3` roots in `ZMod 257` (drop from the generic `4`). -/
theorem rootCount_257 : rootCountMod 257 = 3 := by decide

/-! ### 2. The floor-bad prime `97` — UNRAMIFIED, full `4` roots, in the AP `≡ 1 (mod 32)`. -/

/-- `97 = ` least prime `≡ 1 (mod 32)` is the §9 floor-bad prime for `n = 32`; it is `≡ 1 (mod 32)`. -/
theorem ninetySeven_in_AP : (97 : ℕ) % 32 = 1 := by decide

/-- `97 ∤ disc(S)`: the floor-bad prime is UNRAMIFIED. -/
theorem ninetySeven_not_dvd_disc : ¬ (97 ∣ discS) := by unfold discS; decide

/-- At the floor-bad prime `97`, `S` has the FULL `4` roots in `ZMod 97` (no drop). -/
theorem rootCount_97 : rootCountMod 97 = 4 := by decide

/-! ### 3. Disjointness — the ramified primes are NOT the floor-bad prime. -/

/-- `17 ≢ 1 (mod 32)`: the ramified prime `17` is not even in the floor-bad arithmetic progression. -/
theorem seventeen_not_in_AP : (17 : ℕ) % 32 ≠ 1 := by decide

/-- `257 ≡ 1 (mod 32)` but `257 ≠ 97`: the second ramified prime is in the AP yet is NOT the least
prime there, so it is not the floor-bad prime either. -/
theorem twoFiftySeven_in_AP_but_not_floorBad : (257 : ℕ) % 32 = 1 ∧ (257 : ℕ) ≠ 97 := by
  decide

/-- **Floor-bad ≠ ramification, the consolidated constraint.** For the `n = 32` defect core `S`:
neither ramified prime (`17`, `257`) coincides with the floor-bad prime `97`, the floor-bad prime is
unramified with full root count, and the ramified primes have a strict root-count drop. Hence the
discriminant / ramification locus of the defect resultant does NOT identify the §9 floor-bad prime;
the floor-bad selector is the least-prime-in-AP object, a disjoint phenomenon. No CORE / cancellation
/ completion / moment / capacity claim. -/
theorem floorBad_disjoint_from_ramification :
    -- ramified primes (root-count drop, divide disc):
    (17 ∣ discS ∧ rootCountMod 17 = 3) ∧
    (257 ∣ discS ∧ rootCountMod 257 = 3) ∧
    -- floor-bad prime 97: in the AP, UNRAMIFIED, full root count:
    ((97 : ℕ) % 32 = 1 ∧ ¬ (97 ∣ discS) ∧ rootCountMod 97 = 4) ∧
    -- disjointness witnesses: neither ramified prime is the floor-bad prime:
    ((17 : ℕ) % 32 ≠ 1) ∧ ((257 : ℕ) % 32 = 1 ∧ (257 : ℕ) ≠ 97) :=
  ⟨⟨seventeen_dvd_disc, rootCount_17⟩,
   ⟨twoFiftySeven_dvd_disc, rootCount_257⟩,
   ⟨ninetySeven_in_AP, ninetySeven_not_dvd_disc, rootCount_97⟩,
   seventeen_not_in_AP,
   twoFiftySeven_in_AP_but_not_floorBad⟩

end ArkLib.ProximityGap.Frontier.FloorBadRamif
