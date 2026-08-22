/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Fin.VecNotation
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungTwoPow

/-!
# Issue #371 — Möbius coincidence witness: the constant-6 law's lower bound

Statement layer for the char-0 lower bound `M(n) ≥ 6` of the constant-6 law (DISPROOF_LOG
O155), formalizing the census-argmax witness family verified exactly by
`scripts/probes/normalizer_gap/char0_witness_check.py` and recorded in
`scripts/probes/normalizer_gap/RESULTS-CHAR0-ANCHOR.md`.

Setting: `F` a field, `m = n/2`, and `z : F` with `z ^ m = -1` (so `z ^ (2*m) = 1` and
`z ≠ 0`). The anchor's uniform Möbius datum (integer content removed, max coefficient 2,
the SAME closed form at every census `n ∈ {8, 16, 32, 64}`):

* `c = -z^(m-1) + z - 2`
* `d = 2·z^(m-1) - z^(m-2) - z^3 + z^2 + z`
* `a = z^(m-1) - z^(m-2) - z^3 + 2·z^2 - 1`   (the anchor lists `-a`; sign flipped here)
* `b = -(z - 1)^2`                              (the anchor lists `-b = (z - 1)^2`)

with incidence relation `R(x, y) := c·x·y + d·y - a·x - b = 0`, realized at the six points
`(z^i, z^j)`, `(i, j) ∈ S(n) = {(0,0), (1,1), (2,3), (4, m+2), (m-1, 2m-3), (2m-2, 2m-1)}`.

## Exact reductions (verified in `ℤ[z]/(z^m + 1)`, exact arithmetic, `2 ≤ m ≤ 24`)

In Laurent form (`z^(m-1) = -z⁻¹`, `z^(m-2) = -z⁻²`, valid since `z ≠ 0`), every quantity
collapses to an `m`-INDEPENDENT closed form:

* `z · c = (z - 1)^2`
* `z^2 · d = -((z - 1)^2 · (z^3 + z^2 - 1))`
* `z^2 · a = -((z - 1)^2 · (z^3 - z - 1))`
* `b = -(z - 1)^2`
* `z^4 · (a·d - b·c) = (z - 1)^6 · (z + 1)^2 · (z^2 + z + 1)`   (the NONDEG factorization)

and all six incidences `R(z^i, z^j) = 0` hold as ring identities for EVERY `m ≥ 2`: the
wraparound at small `m` collapses only the *presentation* of the coefficients (`n = 8` is
the collapsed `m = 4` member of the family, per the anchor), never the identities.

## Threshold `m₀` (design decision)

The headline is stated for `m = 2^k` with `2 ≤ k`, i.e. `n = 2m = 2^(k+1) ≥ 8`:

* the six incidence identities need only `Field F`, `z ^ m = -1`, and `3 ≤ m` (stated at
  that generality below; `3 ≤ m` keeps the truncated `ℕ`-subtractions `m - 2`, `2*m - 3`
  honest);
* pairwise distinctness of the x-exponents `{0, 1, 2, 4, m-1, 2m-2}` (and y-exponents
  `{0, 1, 3, m+2, 2m-3, 2m-1}`) modulo `2m` holds iff `m = 4 ∨ 6 ≤ m`; the unique failure
  above `4` is `m = 5`, which is not a 2-power, so the 2-power hypothesis subsumes the
  threshold — `n = 8` and `n = 16` are covered PARAMETRICALLY, no separate instances;
* nonvanishing (NONDEG and NONNORM) additionally needs `CharZero F` and `z` a primitive
  `2^(k+1)`-th root of unity: each coefficient is `(unit) · (z - 1)^2 · (fixed factor)`
  with the fixed factors of support in exponents `≤ 3 < m = 2^k`, so
  `LamLeungTwoPow.nonvanishing_of_unpaired` (the complete 2-power kernel
  characterization, engine: the rational minimal polynomial `X^(2^k) + 1`) kills each
  factor at an unpaired coefficient (`s = 0`). This dictates the hypothesis shape
  `IsPrimitiveRoot z (2 ^ (k + 1))`, matching the `LamLeungTwoPow` substrate; the bridge
  to `z ^ m = -1` is `LamLeungTwoPow.pow_half_eq_neg_one`, reused verbatim.

## Main statements

* `incident_zero` … `incident_five`: the six incidences over any field with `z^m = -1`.
* `pow_four_mul_detCoeff`, `detCoeff_ne_zero`: the NONDEG factorization and conclusion.
* `not_normalizer_scaling`, `not_normalizer_inversion`: NONNORM.
* `witnessSet_card`: the six points form a `Finset (F × F)` of card exactly `6`.
* `const6_witness`: packaged headline — a nondegenerate, non-normalizer Möbius datum whose
  coincidence relation holds on a set of SIX pairwise-distinct points of
  `μ_{2^(k+1)} × μ_{2^(k+1)}`; hence `M(n) ≥ 6` at the witness layer for every
  `n = 2^(k+1) ≥ 8`.
-/

namespace MobiusCoincidenceWitness

open Finset

variable {F : Type*} [Field F] {z : F} {m k : ℕ}

/-! ## The witness datum -/

/-- The `c`-coefficient of the uniform census-argmax Möbius datum. -/
def cCoeff (z : F) (m : ℕ) : F := -z ^ (m - 1) + z - 2

/-- The `d`-coefficient of the uniform census-argmax Möbius datum. -/
def dCoeff (z : F) (m : ℕ) : F := 2 * z ^ (m - 1) - z ^ (m - 2) - z ^ 3 + z ^ 2 + z

/-- The `a`-coefficient of the uniform census-argmax Möbius datum.
The anchor records `-a = -z^(m-1) + z^(m-2) + z^3 - 2z^2 + 1`; the sign is flipped here. -/
def aCoeff (z : F) (m : ℕ) : F := z ^ (m - 1) - z ^ (m - 2) - z ^ 3 + 2 * z ^ 2 - 1

/-- The `b`-coefficient of the uniform census-argmax Möbius datum.
The anchor records `-b = (z - 1)^2`. -/
def bCoeff (z : F) : F := -(z - 1) ^ 2

/-- The determinant `a·d - b·c` of the Möbius datum (NONDEG is `detCoeff ≠ 0`). -/
def detCoeff (z : F) (m : ℕ) : F := aCoeff z m * dCoeff z m - bCoeff z * cCoeff z m

/-- The incidence relation of the witness plane: `R(x, y) = c·x·y + d·y - a·x - b = 0`,
i.e. `(x, y)` is a coincidence point of the Möbius map attached to the datum. -/
def MobiusIncident (z : F) (m : ℕ) (p : F × F) : Prop :=
  cCoeff z m * (p.1 * p.2) + dCoeff z m * p.2 - aCoeff z m * p.1 - bCoeff z = 0

/-- The x-exponents of the six witness points: `0, 1, 2, 4, m-1, 2m-2`. -/
def xExp (m : ℕ) : Fin 6 → ℕ := ![0, 1, 2, 4, m - 1, 2 * m - 2]

/-- The y-exponents of the six witness points: `0, 1, 3, m+2, 2m-3, 2m-1`. -/
def yExp (m : ℕ) : Fin 6 → ℕ := ![0, 1, 3, m + 2, 2 * m - 3, 2 * m - 1]

/-- The six witness points `(z ^ xExp m t, z ^ yExp m t)` realizing `S(n)`. -/
def witnessPoint (z : F) (m : ℕ) (t : Fin 6) : F × F := (z ^ xExp m t, z ^ yExp m t)

/-- The witness set: the six points of `S(n)`, as a `Finset` of the affine plane. -/
def witnessSet [DecidableEq F] (z : F) (m : ℕ) : Finset (F × F) :=
  univ.image (witnessPoint z m)

/-! ## Generalities for `z ^ m = -1` -/

/-- A solution of `z ^ m = -1` with `1 ≤ m` is nonzero. -/
theorem ne_zero_of_pow_eq_neg_one (hm : 1 ≤ m) (hz : z ^ m = -1) : z ≠ 0 := by
  intro h
  rw [h, zero_pow (by omega : m ≠ 0)] at hz
  exact neg_ne_zero.mpr one_ne_zero hz.symm

/-- A solution of `z ^ m = -1` is a `2m`-th root of unity. -/
theorem pow_two_mul_eq_one (hz : z ^ m = -1) : z ^ (2 * m) = 1 := by
  rw [mul_comm 2 m, pow_mul, hz, neg_one_sq]

/-- Substrate bridge (reused verbatim from `LamLeungTwoPow`): a primitive `2^(k+1)`-th
root of unity satisfies `z ^ (2^k) = -1`. -/
theorem pow_two_pow_eq_neg_one (hprim : IsPrimitiveRoot z (2 ^ (k + 1))) :
    z ^ 2 ^ k = -1 :=
  LamLeungTwoPow.pow_half_eq_neg_one hprim

/-! ## `m`-independent closed forms (the Laurent collapse)

Each coefficient of the datum, multiplied by the unit clearing its `z^(m-1)`, `z^(m-2)`
terms, equals a FIXED polynomial in `z`; exactly verified in `ℤ[z]/(z^m + 1)` for
`2 ≤ m ≤ 24` by the probe gate. These are the whole content of the `z^(m+j) = -z^j`
exponent reductions. -/

/-- `z · c = (z - 1)^2`. -/
theorem z_mul_cCoeff (hm : 3 ≤ m) (hz : z ^ m = -1) :
    z * cCoeff z m = (z - 1) ^ 2 := by
  have h1 : z ^ (m - 1) * z = -1 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    exact hz
  simp only [cCoeff]
  linear_combination -h1

/-- `z^2 · d = -((z - 1)^2 · (z^3 + z^2 - 1))`. -/
theorem sq_mul_dCoeff (hm : 3 ≤ m) (hz : z ^ m = -1) :
    z ^ 2 * dCoeff z m = -((z - 1) ^ 2 * (z ^ 3 + z ^ 2 - 1)) := by
  have h1 : z ^ (m - 1) * z = -1 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    exact hz
  have h2 : z ^ (m - 2) * z ^ 2 = -1 := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ m)]
    exact hz
  simp only [dCoeff]
  linear_combination 2 * z * h1 - h2

/-- `z^2 · a = -((z - 1)^2 · (z^3 - z - 1))`. -/
theorem sq_mul_aCoeff (hm : 3 ≤ m) (hz : z ^ m = -1) :
    z ^ 2 * aCoeff z m = -((z - 1) ^ 2 * (z ^ 3 - z - 1)) := by
  have h1 : z ^ (m - 1) * z = -1 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    exact hz
  have h2 : z ^ (m - 2) * z ^ 2 = -1 := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ m)]
    exact hz
  simp only [aCoeff]
  linear_combination z * h1 - h2

/-- The NONDEG factorization: `z^4 · (a·d - b·c) = (z-1)^6 · (z+1)^2 · (z^2 + z + 1)`. -/
theorem pow_four_mul_detCoeff (hm : 3 ≤ m) (hz : z ^ m = -1) :
    z ^ 4 * detCoeff z m = (z - 1) ^ 6 * (z + 1) ^ 2 * (z ^ 2 + z + 1) := by
  have ha := sq_mul_aCoeff hm hz
  have hd := sq_mul_dCoeff hm hz
  have hc := z_mul_cCoeff hm hz
  have expand : z ^ 4 * detCoeff z m
      = (z ^ 2 * aCoeff z m) * (z ^ 2 * dCoeff z m)
        - (z ^ 3 * bCoeff z) * (z * cCoeff z m) := by
    simp only [detCoeff]
    ring
  rw [expand, ha, hd, hc]
  simp only [bCoeff]
  ring

/-! ## The six incidences

Pure ring identities over any field with `z ^ m = -1`: no characteristic assumption and
no primitivity. Indexed by witness position; the points are `(z^i, z^j)` for `(i, j)`
running through `S(n)` with `z^0 = 1` and `z^1 = z` evaluated. -/

/-- Incidence at `(i, j) = (0, 0)`: `R(1, 1) = 0`. -/
theorem incident_zero (hm : 3 ≤ m) (hz : z ^ m = -1) :
    MobiusIncident z m (1, 1) := by
  have hz0 : z ≠ 0 := ne_zero_of_pow_eq_neg_one (by omega) hz
  have hP : z ^ (m - 2) = -1 / z ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hz0), ← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ m)]
    exact hz
  simp only [MobiusIncident, cCoeff, dCoeff, aCoeff, bCoeff]
  rw [show m - 1 = m - 2 + 1 by omega]
  simp only [pow_add, pow_one, hP]
  field_simp
  ring

/-- Incidence at `(i, j) = (1, 1)`: `R(z, z) = 0`. -/
theorem incident_one (hm : 3 ≤ m) (hz : z ^ m = -1) :
    MobiusIncident z m (z, z) := by
  have hz0 : z ≠ 0 := ne_zero_of_pow_eq_neg_one (by omega) hz
  have hP : z ^ (m - 2) = -1 / z ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hz0), ← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ m)]
    exact hz
  simp only [MobiusIncident, cCoeff, dCoeff, aCoeff, bCoeff]
  rw [show m - 1 = m - 2 + 1 by omega]
  simp only [pow_add, pow_one, hP]
  field_simp
  ring

/-- Incidence at `(i, j) = (2, 3)`: `R(z^2, z^3) = 0`. -/
theorem incident_two (hm : 3 ≤ m) (hz : z ^ m = -1) :
    MobiusIncident z m (z ^ 2, z ^ 3) := by
  have hz0 : z ≠ 0 := ne_zero_of_pow_eq_neg_one (by omega) hz
  have hP : z ^ (m - 2) = -1 / z ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hz0), ← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ m)]
    exact hz
  simp only [MobiusIncident, cCoeff, dCoeff, aCoeff, bCoeff]
  rw [show m - 1 = m - 2 + 1 by omega]
  simp only [pow_add, pow_one, hP]
  field_simp
  ring

/-- Incidence at `(i, j) = (4, m+2)`: `R(z^4, z^(m+2)) = 0` (note `z^(m+2) = -z^2`). -/
theorem incident_three (hm : 3 ≤ m) (hz : z ^ m = -1) :
    MobiusIncident z m (z ^ 4, z ^ (m + 2)) := by
  have hz0 : z ≠ 0 := ne_zero_of_pow_eq_neg_one (by omega) hz
  have hP : z ^ (m - 2) = -1 / z ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hz0), ← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ m)]
    exact hz
  simp only [MobiusIncident, cCoeff, dCoeff, aCoeff, bCoeff]
  rw [show m - 1 = m - 2 + 1 by omega, show m + 2 = m - 2 + 4 by omega]
  simp only [pow_add, pow_one, hP]
  field_simp
  ring

/-- Incidence at `(i, j) = (m-1, 2m-3)`: `R(z^(m-1), z^(2m-3)) = 0`
(note `z^(m-1) = -z⁻¹` and `z^(2m-3) = z⁻³` in Laurent form). -/
theorem incident_four (hm : 3 ≤ m) (hz : z ^ m = -1) :
    MobiusIncident z m (z ^ (m - 1), z ^ (2 * m - 3)) := by
  have hz0 : z ≠ 0 := ne_zero_of_pow_eq_neg_one (by omega) hz
  have hP : z ^ (m - 2) = -1 / z ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hz0), ← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ m)]
    exact hz
  simp only [MobiusIncident, cCoeff, dCoeff, aCoeff, bCoeff]
  rw [show 2 * m - 3 = m - 2 + (m - 2) + 1 by omega, show m - 1 = m - 2 + 1 by omega]
  simp only [pow_add, pow_one, hP]
  field_simp
  ring

/-- Incidence at `(i, j) = (2m-2, 2m-1)`: `R(z^(2m-2), z^(2m-1)) = 0`. -/
theorem incident_five (hm : 3 ≤ m) (hz : z ^ m = -1) :
    MobiusIncident z m (z ^ (2 * m - 2), z ^ (2 * m - 1)) := by
  have hz0 : z ≠ 0 := ne_zero_of_pow_eq_neg_one (by omega) hz
  have hP : z ^ (m - 2) = -1 / z ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hz0), ← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ m)]
    exact hz
  simp only [MobiusIncident, cCoeff, dCoeff, aCoeff, bCoeff]
  rw [show 2 * m - 2 = m - 2 + (m - 2) + 2 by omega,
    show 2 * m - 1 = m - 2 + (m - 2) + 3 by omega, show m - 1 = m - 2 + 1 by omega]
  simp only [pow_add, pow_one, hP]
  field_simp
  ring

/-- All six witness points are incident (packaging of `incident_zero` … `incident_five`). -/
theorem mobiusIncident_witnessPoint (hm : 3 ≤ m) (hz : z ^ m = -1) (t : Fin 6) :
    MobiusIncident z m (witnessPoint z m t) := by
  fin_cases t
  · show MobiusIncident z m (z ^ (0 : ℕ), z ^ (0 : ℕ))
    rw [pow_zero]
    exact incident_zero hm hz
  · show MobiusIncident z m (z ^ (1 : ℕ), z ^ (1 : ℕ))
    rw [pow_one]
    exact incident_one hm hz
  · exact incident_two hm hz
  · exact incident_three hm hz
  · exact incident_four hm hz
  · exact incident_five hm hz

/-- Both coordinates of every witness point lie in `μ_{2m} = {u : u^(2m) = 1}`. -/
theorem witnessPoint_pow_eq_one (hz : z ^ m = -1) (t : Fin 6) :
    (witnessPoint z m t).1 ^ (2 * m) = 1 ∧ (witnessPoint z m t).2 ^ (2 * m) = 1 := by
  have h1 : z ^ (2 * m) = 1 := pow_two_mul_eq_one hz
  constructor
  · show (z ^ xExp m t) ^ (2 * m) = 1
    rw [← pow_mul, mul_comm (xExp m t) (2 * m), pow_mul, h1, one_pow]
  · show (z ^ yExp m t) ^ (2 * m) = 1
    rw [← pow_mul, mul_comm (yExp m t) (2 * m), pow_mul, h1, one_pow]

/-- The witness set, explicitly listed. -/
theorem witnessSet_eq [DecidableEq F] (z : F) (m : ℕ) :
    witnessSet z m =
      {(1, 1), (z, z), (z ^ 2, z ^ 3), (z ^ 4, z ^ (m + 2)),
        (z ^ (m - 1), z ^ (2 * m - 3)), (z ^ (2 * m - 2), z ^ (2 * m - 1))} := by
  have huniv : (univ : Finset (Fin 6)) = {0, 1, 2, 3, 4, 5} := by decide
  have h0 : witnessPoint z m 0 = ((1 : F), (1 : F)) := by
    show (z ^ (0 : ℕ), z ^ (0 : ℕ)) = (1, 1)
    rw [pow_zero]
  have h1 : witnessPoint z m 1 = (z, z) := by
    show (z ^ (1 : ℕ), z ^ (1 : ℕ)) = (z, z)
    rw [pow_one]
  have h2 : witnessPoint z m 2 = (z ^ 2, z ^ 3) := rfl
  have h3 : witnessPoint z m 3 = (z ^ 4, z ^ (m + 2)) := rfl
  have h4 : witnessPoint z m 4 = (z ^ (m - 1), z ^ (2 * m - 3)) := rfl
  have h5 : witnessPoint z m 5 = (z ^ (2 * m - 2), z ^ (2 * m - 1)) := rfl
  unfold witnessSet
  rw [huniv]
  simp only [image_insert, image_singleton, h0, h1, h2, h3, h4, h5]

/-! ## Distinctness

The six x-exponents (resp. y-exponents) are pairwise distinct and `< 2m` whenever
`4 ≤ m` and `m ≠ 5` (`m = 5` collides `m - 1 = 4` with the exponent `4`, resp.
`m + 2 = 2m - 3`; it is the unique failure above `4` and is not a power of two).
Primitivity then separates the corresponding powers of `z`. -/

/-- The x-exponents are reduced: `xExp m t < 2m`. -/
theorem xExp_lt (hm : 3 ≤ m) (t : Fin 6) : xExp m t < 2 * m := by
  fin_cases t
  · show (0 : ℕ) < 2 * m
    omega
  · show (1 : ℕ) < 2 * m
    omega
  · show (2 : ℕ) < 2 * m
    omega
  · show (4 : ℕ) < 2 * m
    omega
  · show m - 1 < 2 * m
    omega
  · show 2 * m - 2 < 2 * m
    omega

/-- The y-exponents are reduced: `yExp m t < 2m`. -/
theorem yExp_lt (hm : 3 ≤ m) (t : Fin 6) : yExp m t < 2 * m := by
  fin_cases t
  · show (0 : ℕ) < 2 * m
    omega
  · show (1 : ℕ) < 2 * m
    omega
  · show (3 : ℕ) < 2 * m
    omega
  · show m + 2 < 2 * m
    omega
  · show 2 * m - 3 < 2 * m
    omega
  · show 2 * m - 1 < 2 * m
    omega

/-- The six x-exponents `0, 1, 2, 4, m-1, 2m-2` are pairwise distinct for `4 ≤ m ≠ 5`. -/
theorem xExp_injective (hm : 4 ≤ m) (hm5 : m ≠ 5) : Function.Injective (xExp m) := by
  rw [← List.nodup_ofFn]
  have h : List.ofFn (xExp m) = [0, 1, 2, 4, m - 1, 2 * m - 2] := rfl
  rw [h]
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true]
  omega

/-- The six y-exponents `0, 1, 3, m+2, 2m-3, 2m-1` are pairwise distinct for `4 ≤ m ≠ 5`. -/
theorem yExp_injective (hm : 4 ≤ m) (hm5 : m ≠ 5) : Function.Injective (yExp m) := by
  rw [← List.nodup_ofFn]
  have h : List.ofFn (yExp m) = [0, 1, 3, m + 2, 2 * m - 3, 2 * m - 1] := rfl
  rw [h]
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true]
  omega

/-- `4 ≤ 2^k` for `2 ≤ k` (the distinctness threshold along the 2-power family). -/
private theorem four_le_two_pow (hk : 2 ≤ k) : 4 ≤ 2 ^ k :=
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

/-- For `z` a primitive `2^(k+1)`-th root of unity, `2 ≤ k`, the six witness points are
pairwise distinct (their x-coordinates already are, via `IsPrimitiveRoot.pow_inj`). -/
theorem witnessPoint_injective (hk : 2 ≤ k) (hprim : IsPrimitiveRoot z (2 ^ (k + 1))) :
    Function.Injective (witnessPoint z (2 ^ k)) := by
  have h4 : 4 ≤ 2 ^ k := four_le_two_pow hk
  have h5 : (2 : ℕ) ^ k ≠ 5 := by
    intro h
    have hdvd : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
    rw [h] at hdvd
    omega
  have hexp : 2 * 2 ^ k = 2 ^ (k + 1) := by
    rw [pow_succ, Nat.mul_comm]
  intro s t hst
  have hx : z ^ xExp (2 ^ k) s = z ^ xExp (2 ^ k) t := congrArg Prod.fst hst
  have hs : xExp (2 ^ k) s < 2 ^ (k + 1) := by
    rw [← hexp]
    exact xExp_lt (le_trans (by norm_num) h4) s
  have ht : xExp (2 ^ k) t < 2 ^ (k + 1) := by
    rw [← hexp]
    exact xExp_lt (le_trans (by norm_num) h4) t
  exact xExp_injective h4 h5 (hprim.pow_inj hs ht hx)

/-- The witness set has exactly six points. -/
theorem witnessSet_card [DecidableEq F] (hk : 2 ≤ k)
    (hprim : IsPrimitiveRoot z (2 ^ (k + 1))) :
    (witnessSet z (2 ^ k)).card = 6 := by
  unfold witnessSet
  rw [Finset.card_image_of_injective _ (witnessPoint_injective hk hprim),
    Finset.card_univ, Fintype.card_fin]

/-! ## Nonvanishing: NONDEG and NONNORM

Characteristic zero plus 2-power primitivity. Engine: each fixed factor below is a
`ℚ`-combination of `z`-powers with support in exponents `≤ 3 < 2^k`, hence has an
unpaired coefficient at `s = 0` against the antipode `s + 2^k`, so
`LamLeungTwoPow.nonvanishing_of_unpaired` applies (its engine: the minimal polynomial of
`z` over `ℚ` is `X^(2^k) + 1`). `z ≠ 1` and `z ≠ -1` are order arguments and do not need
characteristic zero, but are stated here uniformly. -/

section CharZeroNonvanishing

variable [CharZero F]

/-- Coefficient vector of a cubic `c₀ + c₁·z + c₂·z² + c₃·z³`, as a function `ℕ → ℚ`
(the shape consumed by the `LamLeungTwoPow` kernel characterization). -/
private def coeffs (c₀ c₁ c₂ c₃ : ℚ) : ℕ → ℚ := fun e =>
  if e = 0 then c₀ else if e = 1 then c₁ else if e = 2 then c₂ else if e = 3 then c₃ else 0

/-- Workhorse: a `ℚ`-cubic in `z` with nonzero constant term does not vanish at a
primitive `2^(k+1)`-th root of unity, `2 ≤ k` (unpaired coefficient at `s = 0`, since
the antipode `2^k ≥ 4` is outside the support). -/
private theorem lowPoly_ne_zero (hk : 2 ≤ k) (hprim : IsPrimitiveRoot z (2 ^ (k + 1)))
    (c₀ c₁ c₂ c₃ : ℚ) (h0 : c₀ ≠ 0) :
    (c₀ : F) + (c₁ : F) * z + (c₂ : F) * z ^ 2 + (c₃ : F) * z ^ 3 ≠ 0 := by
  have h4 : 4 ≤ 2 ^ k := four_le_two_pow hk
  have h4' : 4 ≤ 2 ^ (k + 1) :=
    le_trans h4 (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))
  have hcz : ∀ e, 4 ≤ e → coeffs c₀ c₁ c₂ c₃ e = 0 := by
    intro e he
    simp only [coeffs]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hne : coeffs c₀ c₁ c₂ c₃ 0 ≠ coeffs c₀ c₁ c₂ c₃ (0 + 2 ^ k) := by
    have e0 : coeffs c₀ c₁ c₂ c₃ 0 = c₀ := by simp [coeffs]
    have e1 : coeffs c₀ c₁ c₂ c₃ (0 + 2 ^ k) = 0 := hcz _ (by simpa using h4)
    rw [e0, e1]
    exact h0
  have hkey := LamLeungTwoPow.nonvanishing_of_unpaired hprim (coeffs c₀ c₁ c₂ c₃)
    (Nat.two_pow_pos k) hne
  have hres : ∑ e ∈ Finset.range (2 ^ (k + 1)), ((coeffs c₀ c₁ c₂ c₃ e : ℚ) : F) * z ^ e
      = ∑ e ∈ Finset.range 4, ((coeffs c₀ c₁ c₂ c₃ e : ℚ) : F) * z ^ e := by
    refine (Finset.sum_subset (Finset.range_subset_range.mpr h4') fun x _ hx => ?_).symm
    have hx4 : 4 ≤ x := by
      rcases Nat.lt_or_ge x 4 with h | h
      · exact absurd (Finset.mem_range.mpr h) hx
      · exact h
    rw [hcz x hx4]
    norm_num
  have hval : ∑ e ∈ Finset.range 4, ((coeffs c₀ c₁ c₂ c₃ e : ℚ) : F) * z ^ e
      = (c₀ : F) + (c₁ : F) * z + (c₂ : F) * z ^ 2 + (c₃ : F) * z ^ 3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
    norm_num [coeffs]
  intro hzero
  exact hkey ((hres.trans hval).trans hzero)

/-- `z ≠ 1`, in subtraction form. -/
theorem sub_one_ne_zero (hk : 2 ≤ k) (hprim : IsPrimitiveRoot z (2 ^ (k + 1))) :
    z - 1 ≠ 0 := by
  have h := lowPoly_ne_zero hk hprim (-1) 1 0 0 (by norm_num)
  have e : ((-1 : ℚ) : F) + ((1 : ℚ) : F) * z + ((0 : ℚ) : F) * z ^ 2
      + ((0 : ℚ) : F) * z ^ 3 = z - 1 := by
    push_cast
    ring
  exact e ▸ h

/-- `z ≠ -1`, in addition form. -/
theorem add_one_ne_zero (hk : 2 ≤ k) (hprim : IsPrimitiveRoot z (2 ^ (k + 1))) :
    z + 1 ≠ 0 := by
  have h := lowPoly_ne_zero hk hprim 1 1 0 0 (by norm_num)
  have e : ((1 : ℚ) : F) + ((1 : ℚ) : F) * z + ((0 : ℚ) : F) * z ^ 2
      + ((0 : ℚ) : F) * z ^ 3 = z + 1 := by
    push_cast
    ring
  exact e ▸ h

/-- The fixed quadratic factor of the determinant does not vanish: `z^2 + z + 1 ≠ 0`
(else `z^3 = 1`, clashing with the 2-power order). -/
theorem quadratic_ne_zero (hk : 2 ≤ k) (hprim : IsPrimitiveRoot z (2 ^ (k + 1))) :
    z ^ 2 + z + 1 ≠ 0 := by
  have h := lowPoly_ne_zero hk hprim 1 1 1 0 (by norm_num)
  have e : ((1 : ℚ) : F) + ((1 : ℚ) : F) * z + ((1 : ℚ) : F) * z ^ 2
      + ((0 : ℚ) : F) * z ^ 3 = z ^ 2 + z + 1 := by
    push_cast
    ring
  exact e ▸ h

/-- The fixed cubic factor of `a` does not vanish: `z^3 - z - 1 ≠ 0` (unpaired
coefficient at `0`, since `2^k > 3`). -/
theorem cubic_a_ne_zero (hk : 2 ≤ k) (hprim : IsPrimitiveRoot z (2 ^ (k + 1))) :
    z ^ 3 - z - 1 ≠ 0 := by
  have h := lowPoly_ne_zero hk hprim (-1) (-1) 0 1 (by norm_num)
  have e : ((-1 : ℚ) : F) + ((-1 : ℚ) : F) * z + ((0 : ℚ) : F) * z ^ 2
      + ((1 : ℚ) : F) * z ^ 3 = z ^ 3 - z - 1 := by
    push_cast
    ring
  exact e ▸ h

/-- The fixed cubic factor of `d` does not vanish: `z^3 + z^2 - 1 ≠ 0`. -/
theorem cubic_d_ne_zero (hk : 2 ≤ k) (hprim : IsPrimitiveRoot z (2 ^ (k + 1))) :
    z ^ 3 + z ^ 2 - 1 ≠ 0 := by
  have h := lowPoly_ne_zero hk hprim (-1) 0 1 1 (by norm_num)
  have e : ((-1 : ℚ) : F) + ((0 : ℚ) : F) * z + ((1 : ℚ) : F) * z ^ 2
      + ((1 : ℚ) : F) * z ^ 3 = z ^ 3 + z ^ 2 - 1 := by
    push_cast
    ring
  exact e ▸ h

/-- `b ≠ 0`. -/
theorem bCoeff_ne_zero (hk : 2 ≤ k) (hprim : IsPrimitiveRoot z (2 ^ (k + 1))) :
    bCoeff z ≠ 0 := by
  simp only [bCoeff, neg_ne_zero]
  exact pow_ne_zero 2 (sub_one_ne_zero hk hprim)

/-- `c ≠ 0`. -/
theorem cCoeff_ne_zero (hk : 2 ≤ k) (hprim : IsPrimitiveRoot z (2 ^ (k + 1))) :
    cCoeff z (2 ^ k) ≠ 0 := by
  intro h
  have hz : z ^ 2 ^ k = -1 := pow_two_pow_eq_neg_one hprim
  have hcol := z_mul_cCoeff (le_trans (by norm_num) (four_le_two_pow hk)) hz
  rw [h, mul_zero] at hcol
  exact pow_ne_zero 2 (sub_one_ne_zero hk hprim) hcol.symm

/-- `a ≠ 0`. -/
theorem aCoeff_ne_zero (hk : 2 ≤ k) (hprim : IsPrimitiveRoot z (2 ^ (k + 1))) :
    aCoeff z (2 ^ k) ≠ 0 := by
  intro h
  have hz : z ^ 2 ^ k = -1 := pow_two_pow_eq_neg_one hprim
  have hcol := sq_mul_aCoeff (le_trans (by norm_num) (four_le_two_pow hk)) hz
  rw [h, mul_zero] at hcol
  rcases mul_eq_zero.mp (neg_eq_zero.mp hcol.symm) with h' | h'
  · exact pow_ne_zero 2 (sub_one_ne_zero hk hprim) h'
  · exact cubic_a_ne_zero hk hprim h'

/-- `d ≠ 0`. -/
theorem dCoeff_ne_zero (hk : 2 ≤ k) (hprim : IsPrimitiveRoot z (2 ^ (k + 1))) :
    dCoeff z (2 ^ k) ≠ 0 := by
  intro h
  have hz : z ^ 2 ^ k = -1 := pow_two_pow_eq_neg_one hprim
  have hcol := sq_mul_dCoeff (le_trans (by norm_num) (four_le_two_pow hk)) hz
  rw [h, mul_zero] at hcol
  rcases mul_eq_zero.mp (neg_eq_zero.mp hcol.symm) with h' | h'
  · exact pow_ne_zero 2 (sub_one_ne_zero hk hprim) h'
  · exact cubic_d_ne_zero hk hprim h'

/-- **NONDEG**: `a·d - b·c ≠ 0` — the Möbius datum is invertible. -/
theorem detCoeff_ne_zero (hk : 2 ≤ k) (hprim : IsPrimitiveRoot z (2 ^ (k + 1))) :
    detCoeff z (2 ^ k) ≠ 0 := by
  intro h
  have hz : z ^ 2 ^ k = -1 := pow_two_pow_eq_neg_one hprim
  have hcol := pow_four_mul_detCoeff (le_trans (by norm_num) (four_le_two_pow hk)) hz
  rw [h, mul_zero] at hcol
  rcases mul_eq_zero.mp hcol.symm with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact pow_ne_zero 6 (sub_one_ne_zero hk hprim) h''
    · exact pow_ne_zero 2 (add_one_ne_zero hk hprim) h''
  · exact quadratic_ne_zero hk hprim h'

/-- **NONNORM**, scaling type: not both `b = 0` and `c = 0`. -/
theorem not_normalizer_scaling (hk : 2 ≤ k) (hprim : IsPrimitiveRoot z (2 ^ (k + 1))) :
    ¬(bCoeff z = 0 ∧ cCoeff z (2 ^ k) = 0) := fun h =>
  bCoeff_ne_zero hk hprim h.1

/-- **NONNORM**, inversion type: not both `a = 0` and `d = 0`. -/
theorem not_normalizer_inversion (hk : 2 ≤ k) (hprim : IsPrimitiveRoot z (2 ^ (k + 1))) :
    ¬(aCoeff z (2 ^ k) = 0 ∧ dCoeff z (2 ^ k) = 0) := fun h =>
  aCoeff_ne_zero hk hprim h.1

/-! ## Headline -/

/-- **The constant-6 law's lower-bound witness** (issue #371, char-0 layer; anchor:
RESULTS-CHAR0-ANCHOR.md). For every `n = 2m = 2^(k+1) ≥ 8` and every primitive `n`-th
root of unity `z` in a characteristic-zero field, there is a Möbius datum `(a, b, c, d)`
that is nondegenerate (`a·d - b·c ≠ 0`) and non-normalizer (neither `b = c = 0` nor
`a = d = 0`) whose coincidence relation `c·x·y + d·y - a·x - b = 0` holds on a set of SIX
pairwise-distinct points of `μ_n × μ_n` — hence the maximal coincidence count satisfies
`M(n) ≥ 6`, uniformly in `n`. -/
theorem const6_witness (hk : 2 ≤ k) (hprim : IsPrimitiveRoot z (2 ^ (k + 1))) :
    ∃ a b c d : F,
      a * d - b * c ≠ 0 ∧
      ¬(b = 0 ∧ c = 0) ∧
      ¬(a = 0 ∧ d = 0) ∧
      ∃ P : Finset (F × F),
        P.card = 6 ∧
        (∀ p ∈ P, p.1 ^ 2 ^ (k + 1) = 1 ∧ p.2 ^ 2 ^ (k + 1) = 1) ∧
        ∀ p ∈ P, c * (p.1 * p.2) + d * p.2 - a * p.1 - b = 0 := by
  classical
  have hm3 : 3 ≤ 2 ^ k := le_trans (by norm_num) (four_le_two_pow hk)
  have hz : z ^ 2 ^ k = -1 := pow_two_pow_eq_neg_one hprim
  have hexp : 2 ^ (k + 1) = 2 * 2 ^ k := by
    rw [pow_succ, Nat.mul_comm]
  refine ⟨aCoeff z (2 ^ k), bCoeff z, cCoeff z (2 ^ k), dCoeff z (2 ^ k), ?_, ?_, ?_,
    witnessSet z (2 ^ k), ?_, ?_, ?_⟩
  · exact detCoeff_ne_zero hk hprim
  · exact not_normalizer_scaling hk hprim
  · exact not_normalizer_inversion hk hprim
  · exact witnessSet_card hk hprim
  · intro p hp
    simp only [witnessSet, Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨t, rfl⟩ := hp
    rw [hexp]
    exact witnessPoint_pow_eq_one hz t
  · intro p hp
    simp only [witnessSet, Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨t, rfl⟩ := hp
    exact mobiusIncident_witnessPoint hm3 hz t

/-- The collapsed base instance `n = 8` (`k = 2`, `m = 4`) of `const6_witness`: the
census argmax at `n = 8` is the same closed-form family. -/
theorem const6_witness_eight {z : F} (hprim : IsPrimitiveRoot z 8) :
    ∃ a b c d : F,
      a * d - b * c ≠ 0 ∧
      ¬(b = 0 ∧ c = 0) ∧
      ¬(a = 0 ∧ d = 0) ∧
      ∃ P : Finset (F × F),
        P.card = 6 ∧
        (∀ p ∈ P, p.1 ^ (8 : ℕ) = 1 ∧ p.2 ^ (8 : ℕ) = 1) ∧
        ∀ p ∈ P, c * (p.1 * p.2) + d * p.2 - a * p.1 - b = 0 := by
  have hprim' : IsPrimitiveRoot z (2 ^ (2 + 1)) := by
    norm_num
    exact hprim
  exact const6_witness le_rfl hprim'

end CharZeroNonvanishing

end MobiusCoincidenceWitness
