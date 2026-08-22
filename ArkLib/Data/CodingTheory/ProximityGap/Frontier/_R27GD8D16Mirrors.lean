/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# LANE D8D16MIRRORS (#466 round 27G): the `(m, J, D)` numeric mirror at `d = 8` and `d = 16`

This file mirrors sections 1–4 of `_R26D4Mirror` (the d = 4 unconditional
`TripleLinearHasseC` face) at orders `d = 8` and `d = 16`.  It lands the **machine-checked
parameter-arithmetic backbone** of both mirrors — the explicit ℕ-valued family together with
every arithmetic side condition of the r24/r25 fiber-count fold — which is the piece the
round-27G probe (`probe_r27g_family2.py`, exhaustively validated over the full residue class
up to `q = 1.2·10⁷`) was asked to certify before formalization.

## The explicit families (probe-validated, `probe_r27g_family2.py`)

* **d = 8** (`C₈ = 139`): `s = ⌊√((q−64)/66)⌋`, `m = 8s`, `J = s + 8`, `D = (q−64)/8`,
  `b = ⌊√(66q)⌋`, `B = 17b`.  Admissible for every `q ≡ 1 (mod 8)`, `q ≥ 19322`
  (`= 139² + 1`), rung constant `C₈ = 139` (`(17b)² ≤ 66·289·q = 19074q ≤ 19321q = (139√q)²`);
  `q ≤ 19321` closes by the trivial bound `‖S‖ ≤ q ≤ 139√q`.
* **d = 16** (`C₁₆ = 530`): `s = ⌊√((q−256)/229)⌋`, `m = 16s`, `J = s + 18`,
  `D = (q−256)/16`, `b = ⌊√(229q)⌋`, `B = 35b`.  Admissible for every `q ≡ 1 (mod 16)`,
  `q ≥ 280901` (`= 530² + 1`), rung constant `C₁₆ = 530`
  (`(35b)² ≤ 229·1225·q = 280525q ≤ 280900q = (530√q)²`); `q ≤ 280900` trivial.

The continuous optimum (probe `probe_r27g_d8d16params.py`, grid over admissible `(m,J,D)`
subject to the PROVEN r25 budgets) is `c* = d − 1` with asymptotic constants
`C₈* ≈ 121`, `C₁₆* ≈ 498`; the explicit families above trade a slightly larger provable
constant for a clean Nat-sqrt certificate (exactly as the d = 4 mirror used `C₄ = 45`
against its `C₄* = 2√204 ≈ 28.6` optimum).

## Scope (honest)

Landed here (axiom-clean, `propext, Classical.choice, Quot.sound`): the parameter family and
ALL of its budget arithmetic — the independence budget `dD + (d−1)(d+1) < q`, the
rank-nullity count `m(D + dm + J) < dJ(D+1)`, the fold admissibility
`d·Dtot ≤ m·(B + q − 3)`, and the square bound `B² ≤ C²q`.  These are exactly the ℕ/ℤ side
conditions consumed by `superelliptic_stepanov_fiber_bound` (r24) and `class_fold_bound`
(r24) in the d = 4 assembly.

NOT landed here (the load-bearing remaining substrate, scoped as the round-27G residual):
`dBlockIndependence_eight_sqmul` / `_sixteen_sqmul` — the non-squarefree octic/sedecic
`s²·r` block-independence bricks.  These are NOT mechanical mirrors of
`dBlockIndependence_four_sqmul`: each level needs its own `octic/sedecic_norm_forces_trivial_sqmul`
descent (the r25 `octic_descent` reduces `d = 8 → d = 4` for SQUAREFREE `g`; the `s²·r`
fold that lets the χ-fiber sit in a power-fiber of the true kernel `L₁L₂L₃^{d−1}` is the
genuinely new algebra).  With those two bricks the assembly below is the mechanical d = 4
mirror.  Issue #466, round 27G, LANE D8D16MIRRORS.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R27GD8D16Mirrors

/-! ## d = 8 family -/

/-- `s = ⌊√((q−64)/66)⌋`. -/
def s8P (q : ℕ) : ℕ := Nat.sqrt ((q - 64) / 66)
/-- `m = 8s`. -/
def m8P (q : ℕ) : ℕ := 8 * s8P q
/-- `J = s + 8`. -/
def j8P (q : ℕ) : ℕ := s8P q + 8
/-- `D = (q−64)/8`. -/
def d8P (q : ℕ) : ℕ := (q - 64) / 8
/-- `b = ⌊√(66q)⌋`. -/
def b8P (q : ℕ) : ℕ := Nat.sqrt (66 * q)
/-- `B = 17b`. -/
def bigB8 (q : ℕ) : ℕ := 17 * b8P q
/-- `Dtot = 9(m + 7e) + D + q(J−1)`, `e = (q−1)/8`. -/
def dtot8P (q : ℕ) : ℕ := 9 * (m8P q + 7 * ((q - 1) / 8)) + d8P q + q * (j8P q - 1)

theorem s8_sq_le {q : ℕ} : 66 * (s8P q * s8P q) ≤ q - 64 := by
  have h1 : s8P q * s8P q ≤ (q - 64) / 66 := Nat.sqrt_le _
  calc 66 * (s8P q * s8P q) ≤ 66 * ((q - 64) / 66) := Nat.mul_le_mul_left _ h1
    _ ≤ q - 64 := Nat.mul_div_le _ _

theorem lt_s8_succ_sq {q : ℕ} : q - 64 < 66 * ((s8P q + 1) * (s8P q + 1)) := by
  have h1 : (q - 64) / 66 < (s8P q + 1) * (s8P q + 1) := Nat.lt_succ_sqrt _
  have h2 := Nat.div_add_mod (q - 64) 66
  have h3 : (q - 64) % 66 < 66 := Nat.mod_lt _ (by norm_num)
  set dd := (q - 64) / 66
  set S := (s8P q + 1) * (s8P q + 1)
  omega

theorem b8_sq_le {q : ℕ} : b8P q * b8P q ≤ 66 * q := Nat.sqrt_le _
theorem lt_b8_succ_sq {q : ℕ} : 66 * q < (b8P q + 1) * (b8P q + 1) := Nat.lt_succ_sqrt _

/-- `s ≥ 6` in the admissible range `q ≥ 19322` (so the count budget's `(s−1)(s−6) ≥ 0`
sign hint holds). -/
theorem s8_ge_six {q : ℕ} (hq : 19322 ≤ q) : 6 ≤ s8P q := by
  have : 6 * 6 ≤ (q - 64) / 66 := by
    have : 36 ≤ (q - 64) / 66 := Nat.le_div_iff_mul_le (by norm_num) |>.mpr (by omega)
    simpa using this
  exact Nat.le_sqrt.mpr this

theorem s8_pos {q : ℕ} (hq : 19322 ≤ q) : 1 ≤ s8P q := le_trans (by norm_num) (s8_ge_six hq)

/-- **Pairing** `(s+1)(b+1) ≥ q − 33`: reciprocal radicands `(q−64)/66` and `66q`. -/
theorem pairing8 {q : ℕ} (hq : 19322 ≤ q) : q ≤ (s8P q + 1) * (b8P q + 1) + 33 := by
  have hA : q ≤ 66 * ((s8P q + 1) * (s8P q + 1)) + 63 := by
    have := lt_s8_succ_sq (q := q); omega
  have hB : 66 * q + 1 ≤ (b8P q + 1) * (b8P q + 1) := lt_b8_succ_sq
  have hA' : (q : ℤ) ≤ 66 * (((s8P q : ℤ) + 1) * ((s8P q : ℤ) + 1)) + 63 := by exact_mod_cast hA
  have hB' : 66 * (q : ℤ) + 1 ≤ ((b8P q : ℤ) + 1) * ((b8P q : ℤ) + 1) := by exact_mod_cast hB
  have hq' : (19322 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  set x : ℤ := ((s8P q : ℤ) + 1) * ((b8P q : ℤ) + 1) with hx
  have hs0 : (0 : ℤ) ≤ (s8P q : ℤ) := Int.natCast_nonneg _
  have hb0 : (0 : ℤ) ≤ (b8P q : ℤ) := Int.natCast_nonneg _
  have hx0 : (0 : ℤ) ≤ x := by positivity
  have hxsq : ((q : ℤ) - 33) ^ 2 ≤ x ^ 2 := by nlinarith [hA', hB', hq', hs0, hb0]
  have hfin : (q : ℤ) - 33 ≤ x := by
    by_contra hcon; push_neg at hcon
    have : x ^ 2 < ((q : ℤ) - 33) ^ 2 := by nlinarith
    linarith
  have hgoal : (q : ℤ) ≤ ((s8P q : ℤ) + 1) * ((b8P q : ℤ) + 1) + 33 := by rw [hx] at hfin; linarith
  exact_mod_cast hgoal

/-- **Key scale** `92s + 17b + 562 ≤ 2q` for `q ≥ 19322`. -/
theorem key_scale8 {q : ℕ} (hq : 19322 ≤ q) : 92 * s8P q + 17 * b8P q + 562 ≤ 2 * q := by
  have hs : 66 * (s8P q * s8P q) ≤ q - 64 := s8_sq_le
  have hb : b8P q * b8P q ≤ 66 * q := b8_sq_le
  have hsn : 66 * (s8P q * s8P q) + 64 ≤ q := by omega
  have hs' : 66 * ((s8P q : ℤ) * (s8P q : ℤ)) + 64 ≤ (q : ℤ) := by exact_mod_cast hsn
  have hb' : ((b8P q : ℤ)) * ((b8P q : ℤ)) ≤ 66 * (q : ℤ) := by exact_mod_cast hb
  have hq' : (19322 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  have goal' : 92 * (s8P q : ℤ) + 17 * (b8P q : ℤ) + 562 ≤ 2 * (q : ℤ) := by
    nlinarith [sq_nonneg ((b8P q : ℤ) - 561), sq_nonneg (66 * (s8P q : ℤ) - 46),
      Int.natCast_nonneg (s8P q), Int.natCast_nonneg (b8P q), hs', hb', hq']
  exact_mod_cast goal'

/-- **Budget (ii)** independence: `8D + 63 < q`. -/
theorem params8_indep {q : ℕ} (hq : 64 ≤ q) (h8 : q % 8 = 1) : 8 * d8P q + 63 < q := by
  unfold d8P; omega

/-- Order bound `m < q`. -/
theorem params8_m_lt {q : ℕ} (hq : 19322 ≤ q) : m8P q < q := by
  have hs : 66 * (s8P q * s8P q) ≤ q - 64 := s8_sq_le
  have hs1 : 1 ≤ s8P q := s8_pos hq
  have : 8 * s8P q ≤ 66 * (s8P q * s8P q) := by nlinarith
  unfold m8P; omega

/-- **Budget (i)** rank-nullity count: `m(D + 8m + J) < 8·J(D+1)`. -/
theorem params8_count {q : ℕ} (hq : 19322 ≤ q) (h8 : q % 8 = 1) :
    m8P q * (d8P q + 8 * m8P q + j8P q) < 8 * (j8P q * (d8P q + 1)) := by
  obtain ⟨t, ht⟩ : ∃ t, q = 8 * t + 1 := ⟨q / 8, by omega⟩
  have hs : 66 * (s8P q * s8P q) ≤ q - 64 := s8_sq_le
  have hs6 : 6 ≤ s8P q := s8_ge_six hq
  have hd : d8P q = t - 8 := by unfold d8P; omega
  have ht9 : 9 ≤ t := by omega
  obtain ⟨u, hu⟩ : ∃ u, t = u + 8 := ⟨t - 8, by omega⟩
  have hdu : d8P q = u := by omega
  rw [hdu]
  show 8 * s8P q * (u + 8 * (8 * s8P q) + (s8P q + 8)) < 8 * ((s8P q + 8) * (u + 1))
  have hkey : 66 * (s8P q * s8P q) ≤ 8 * u + 1 := by omega
  nlinarith [hkey, hs6, Nat.zero_le (s8P q)]

/-- The admissibility core, linear in `s, b, q, s·b`. -/
theorem admiss_core8 {s b q : ℤ}
    (hpair : q ≤ (s + 1) * (b + 1) + 33)
    (hkey : 92 * s + 17 * b + 562 ≤ 2 * q) :
    75 * s + 15 * q - 16 ≤ 17 * (s * b) := by
  have h1 : (s + 1) * (b + 1) = s * b + s + b + 1 := by ring
  nlinarith [hpair, hkey, h1]

/-- **Budget (iii)** fold admissibility: `8·Dtot ≤ m·(B + (q − 3))`. -/
theorem params8_admiss {q : ℕ} (hq : 19322 ≤ q) (h8 : q % 8 = 1) :
    8 * dtot8P q ≤ m8P q * (bigB8 q + (q - 3)) := by
  obtain ⟨t, ht⟩ : ∃ t, q = 8 * t + 1 := ⟨q / 8, by omega⟩
  have he : (q - 1) / 8 = t := by omega
  have hd : d8P q = t - 8 := by unfold d8P; omega
  have hj : j8P q - 1 = s8P q + 7 := by unfold j8P; omega
  have hpairN : q ≤ (s8P q + 1) * (b8P q + 1) + 33 := pairing8 (by omega)
  have hkeyN : 92 * s8P q + 17 * b8P q + 562 ≤ 2 * q := key_scale8 hq
  have hcore := admiss_core8 (s := (s8P q : ℤ)) (b := (b8P q : ℤ)) (q := (q : ℤ))
    (by exact_mod_cast hpairN) (by exact_mod_cast hkeyN)
  unfold dtot8P m8P bigB8
  rw [he, hd, hj]
  have ht9 : 9 ≤ t := by omega
  have hgoalZ : 8 * (9 * (8 * (s8P q : ℤ) + 7 * (t : ℤ)) + ((t : ℤ) - 8)
      + (q : ℤ) * ((s8P q : ℤ) + 7))
      ≤ 8 * (s8P q : ℤ) * (17 * (b8P q : ℤ) + ((q : ℤ) - 3)) := by
    have hqz : (q : ℤ) = 8 * (t : ℤ) + 1 := by exact_mod_cast ht
    nlinarith [hcore, hqz.le, hqz.ge]
  have hgoalZ' : 8 * (9 * (8 * (s8P q : ℤ) + 7 * (t : ℤ)) + (((t - 8 : ℕ)) : ℤ)
      + (q : ℤ) * ((s8P q : ℤ) + 7))
      ≤ 8 * (s8P q : ℤ) * (17 * (b8P q : ℤ) + (((q - 3 : ℕ)) : ℤ)) := by
    have h1 : (((t - 8 : ℕ)) : ℤ) = (t : ℤ) - 8 := by omega
    have h2 : (((q - 3 : ℕ)) : ℤ) = (q : ℤ) - 3 := by omega
    rw [h1, h2]; exact hgoalZ
  exact_mod_cast hgoalZ'

/-- The square bound `(17b)² ≤ 19321·q = (139)²q`. -/
theorem bigB8_sq_le {q : ℕ} : bigB8 q * bigB8 q ≤ 19321 * q := by
  have hb : b8P q * b8P q ≤ 66 * q := b8_sq_le
  unfold bigB8; nlinarith [hb, Nat.zero_le q]

/-! ## d = 16 family -/

/-- `s = ⌊√((q−256)/229)⌋`. -/
def s16P (q : ℕ) : ℕ := Nat.sqrt ((q - 256) / 229)
/-- `m = 16s`. -/
def m16P (q : ℕ) : ℕ := 16 * s16P q
/-- `J = s + 18`. -/
def j16P (q : ℕ) : ℕ := s16P q + 18
/-- `D = (q−256)/16`. -/
def d16P (q : ℕ) : ℕ := (q - 256) / 16
/-- `b = ⌊√(229q)⌋`. -/
def b16P (q : ℕ) : ℕ := Nat.sqrt (229 * q)
/-- `B = 35b`. -/
def bigB16 (q : ℕ) : ℕ := 35 * b16P q
/-- `Dtot = 17(m + 15e) + D + q(J−1)`, `e = (q−1)/16`. -/
def dtot16P (q : ℕ) : ℕ := 17 * (m16P q + 15 * ((q - 1) / 16)) + d16P q + q * (j16P q - 1)

theorem s16_sq_le {q : ℕ} : 229 * (s16P q * s16P q) ≤ q - 256 := by
  have h1 : s16P q * s16P q ≤ (q - 256) / 229 := Nat.sqrt_le _
  calc 229 * (s16P q * s16P q) ≤ 229 * ((q - 256) / 229) := Nat.mul_le_mul_left _ h1
    _ ≤ q - 256 := Nat.mul_div_le _ _

theorem lt_s16_succ_sq {q : ℕ} : q - 256 < 229 * ((s16P q + 1) * (s16P q + 1)) := by
  have h1 : (q - 256) / 229 < (s16P q + 1) * (s16P q + 1) := Nat.lt_succ_sqrt _
  have h2 := Nat.div_add_mod (q - 256) 229
  have h3 : (q - 256) % 229 < 229 := Nat.mod_lt _ (by norm_num)
  set dd := (q - 256) / 229
  set S := (s16P q + 1) * (s16P q + 1)
  omega

theorem b16_sq_le {q : ℕ} : b16P q * b16P q ≤ 229 * q := Nat.sqrt_le _
theorem lt_b16_succ_sq {q : ℕ} : 229 * q < (b16P q + 1) * (b16P q + 1) := Nat.lt_succ_sqrt _

/-- `s ≥ 35` in the admissible range `q ≥ 280901` (`= 530² + 1`; the count and key-scale
sign hints `(s−1)(s−27) ≥ 0` need `s ≥ 27`). -/
theorem s16_ge_thirtyfive {q : ℕ} (hq : 280901 ≤ q) : 35 ≤ s16P q := by
  have : 35 * 35 ≤ (q - 256) / 229 := by
    have : 1225 ≤ (q - 256) / 229 := Nat.le_div_iff_mul_le (by norm_num) |>.mpr (by omega)
    simpa using this
  exact Nat.le_sqrt.mpr this

theorem s16_pos {q : ℕ} (hq : 280901 ≤ q) : 1 ≤ s16P q :=
  le_trans (by norm_num) (s16_ge_thirtyfive hq)

/-- **Pairing** `(s+1)(b+1) ≥ q − 129`. -/
theorem pairing16 {q : ℕ} (hq : 280901 ≤ q) : q ≤ (s16P q + 1) * (b16P q + 1) + 129 := by
  have hA : q ≤ 229 * ((s16P q + 1) * (s16P q + 1)) + 255 := by
    have := lt_s16_succ_sq (q := q); omega
  have hB : 229 * q + 1 ≤ (b16P q + 1) * (b16P q + 1) := lt_b16_succ_sq
  have hA' : (q : ℤ) ≤ 229 * (((s16P q : ℤ) + 1) * ((s16P q : ℤ) + 1)) + 255 := by exact_mod_cast hA
  have hB' : 229 * (q : ℤ) + 1 ≤ ((b16P q : ℤ) + 1) * ((b16P q : ℤ) + 1) := by exact_mod_cast hB
  have hq' : (280901 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  set x : ℤ := ((s16P q : ℤ) + 1) * ((b16P q : ℤ) + 1) with hx
  have hs0 : (0 : ℤ) ≤ (s16P q : ℤ) := Int.natCast_nonneg _
  have hb0 : (0 : ℤ) ≤ (b16P q : ℤ) := Int.natCast_nonneg _
  have hx0 : (0 : ℤ) ≤ x := by positivity
  have hxsq : ((q : ℤ) - 129) ^ 2 ≤ x ^ 2 := by nlinarith [hA', hB', hq', hs0, hb0]
  have hfin : (q : ℤ) - 129 ≤ x := by
    by_contra hcon; push_neg at hcon
    have : x ^ 2 < ((q : ℤ) - 129) ^ 2 := by nlinarith
    linarith
  have hgoal : (q : ℤ) ≤ ((s16P q : ℤ) + 1) * ((b16P q : ℤ) + 1) + 129 := by
    rw [hx] at hfin; linarith
  exact_mod_cast hgoal

/-- **Key scale** `310s + 35b + 4518 ≤ 2q` for `q ≥ 280901`. -/
theorem key_scale16 {q : ℕ} (hq : 280901 ≤ q) :
    310 * s16P q + 35 * b16P q + 4518 ≤ 2 * q := by
  have hs : 229 * (s16P q * s16P q) ≤ q - 256 := s16_sq_le
  have hb : b16P q * b16P q ≤ 229 * q := b16_sq_le
  have hsn : 229 * (s16P q * s16P q) + 256 ≤ q := by omega
  have hs35 : 35 ≤ s16P q := s16_ge_thirtyfive hq
  have hs' : 229 * ((s16P q : ℤ) * (s16P q : ℤ)) + 256 ≤ (q : ℤ) := by exact_mod_cast hsn
  have hb' : ((b16P q : ℤ)) * ((b16P q : ℤ)) ≤ 229 * (q : ℤ) := by exact_mod_cast hb
  have hq' : (280901 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  have hs35' : (35 : ℤ) ≤ (s16P q : ℤ) := by exact_mod_cast hs35
  have hbnn : (0 : ℤ) ≤ (b16P q : ℤ) := Int.natCast_nonneg _
  -- half A: 310s + 4518 ≤ q  (from 229s² + 256 ≤ q and s ≥ 35)
  have hAh : 310 * (s16P q : ℤ) + 4518 ≤ (q : ℤ) := by nlinarith [hs', hs35']
  -- half B: 35b ≤ q  (from b² ≤ 229q, q ≥ 280525, via (q-35b)(q+35b) ≥ 0)
  have hBsq : (35 * (b16P q : ℤ)) * (35 * (b16P q : ℤ)) ≤ (q : ℤ) * q := by nlinarith [hb', hq']
  have hBh : 35 * (b16P q : ℤ) ≤ (q : ℤ) := by nlinarith [hBsq, hbnn, hq']
  have goal' : 310 * (s16P q : ℤ) + 35 * (b16P q : ℤ) + 4518 ≤ 2 * (q : ℤ) := by linarith
  exact_mod_cast goal'

/-- **Budget (ii)** independence: `16D + 255 < q`. -/
theorem params16_indep {q : ℕ} (hq : 256 ≤ q) (h16 : q % 16 = 1) :
    16 * d16P q + 255 < q := by unfold d16P; omega

/-- Order bound `m < q`. -/
theorem params16_m_lt {q : ℕ} (hq : 280901 ≤ q) : m16P q < q := by
  have hs : 229 * (s16P q * s16P q) ≤ q - 256 := s16_sq_le
  have hs1 : 1 ≤ s16P q := s16_pos hq
  have : 16 * s16P q ≤ 229 * (s16P q * s16P q) := by nlinarith
  unfold m16P; omega

/-- **Budget (i)** rank-nullity count: `m(D + 16m + J) < 16·J(D+1)`. -/
theorem params16_count {q : ℕ} (hq : 280901 ≤ q) (h16 : q % 16 = 1) :
    m16P q * (d16P q + 16 * m16P q + j16P q) < 16 * (j16P q * (d16P q + 1)) := by
  obtain ⟨t, ht⟩ : ∃ t, q = 16 * t + 1 := ⟨q / 16, by omega⟩
  have hs : 229 * (s16P q * s16P q) ≤ q - 256 := s16_sq_le
  have hs35 : 35 ≤ s16P q := s16_ge_thirtyfive hq
  have hd : d16P q = t - 16 := by unfold d16P; omega
  have ht17 : 17 ≤ t := by omega
  obtain ⟨u, hu⟩ : ∃ u, t = u + 16 := ⟨t - 16, by omega⟩
  have hdu : d16P q = u := by omega
  rw [hdu]
  show 16 * s16P q * (u + 16 * (16 * s16P q) + (s16P q + 18))
    < 16 * ((s16P q + 18) * (u + 1))
  have hkey : 229 * (s16P q * s16P q) ≤ 16 * u + 1 := by omega
  nlinarith [hkey, hs35, Nat.zero_le (s16P q)]

/-- The admissibility core, linear in `s, b, q, s·b`. -/
theorem admiss_core16 {s b q : ℤ} (hs : 0 ≤ s) (hb : 0 ≤ b)
    (hpair : q ≤ (s + 1) * (b + 1) + 129)
    (hkey : 310 * s + 35 * b + 4518 ≤ 2 * q) :
    275 * s + 33 * q - 32 ≤ 35 * (s * b) := by
  have h1 : (s + 1) * (b + 1) = s * b + s + b + 1 := by ring
  nlinarith [hpair, hkey, h1, hs, hb]

/-- **Budget (iii)** fold admissibility: `16·Dtot ≤ m·(B + (q − 3))`. -/
theorem params16_admiss {q : ℕ} (hq : 280901 ≤ q) (h16 : q % 16 = 1) :
    16 * dtot16P q ≤ m16P q * (bigB16 q + (q - 3)) := by
  obtain ⟨t, ht⟩ : ∃ t, q = 16 * t + 1 := ⟨q / 16, by omega⟩
  have he : (q - 1) / 16 = t := by omega
  have hd : d16P q = t - 16 := by unfold d16P; omega
  have hj : j16P q - 1 = s16P q + 17 := by unfold j16P; omega
  have hpairN : q ≤ (s16P q + 1) * (b16P q + 1) + 129 := pairing16 (by omega)
  have hkeyN : 310 * s16P q + 35 * b16P q + 4518 ≤ 2 * q := key_scale16 hq
  have hcore := admiss_core16 (s := (s16P q : ℤ)) (b := (b16P q : ℤ)) (q := (q : ℤ))
    (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    (by exact_mod_cast hpairN) (by exact_mod_cast hkeyN)
  unfold dtot16P m16P bigB16
  rw [he, hd, hj]
  have ht17 : 17 ≤ t := by omega
  have hgoalZ : 16 * (17 * (16 * (s16P q : ℤ) + 15 * (t : ℤ)) + ((t : ℤ) - 16)
      + (q : ℤ) * ((s16P q : ℤ) + 17))
      ≤ 16 * (s16P q : ℤ) * (35 * (b16P q : ℤ) + ((q : ℤ) - 3)) := by
    have hqz : (q : ℤ) = 16 * (t : ℤ) + 1 := by exact_mod_cast ht
    nlinarith [hcore, hqz.le, hqz.ge]
  have hgoalZ' : 16 * (17 * (16 * (s16P q : ℤ) + 15 * (t : ℤ)) + (((t - 16 : ℕ)) : ℤ)
      + (q : ℤ) * ((s16P q : ℤ) + 17))
      ≤ 16 * (s16P q : ℤ) * (35 * (b16P q : ℤ) + (((q - 3 : ℕ)) : ℤ)) := by
    have h1 : (((t - 16 : ℕ)) : ℤ) = (t : ℤ) - 16 := by omega
    have h2 : (((q - 3 : ℕ)) : ℤ) = (q : ℤ) - 3 := by omega
    rw [h1, h2]; exact hgoalZ
  exact_mod_cast hgoalZ'

/-- The square bound `(35b)² ≤ 280900·q = (530)²q`. -/
theorem bigB16_sq_le {q : ℕ} : bigB16 q * bigB16 q ≤ 280900 * q := by
  have hb : b16P q * b16P q ≤ 229 * q := b16_sq_le
  unfold bigB16; nlinarith [hb, Nat.zero_le q]

end ArkLib.ProximityGap.Frontier.R27GD8D16Mirrors

-- Honesty audit (axiom-clean target: propext, Classical.choice, Quot.sound)
#print axioms ArkLib.ProximityGap.Frontier.R27GD8D16Mirrors.params8_count
#print axioms ArkLib.ProximityGap.Frontier.R27GD8D16Mirrors.params8_admiss
#print axioms ArkLib.ProximityGap.Frontier.R27GD8D16Mirrors.pairing8
#print axioms ArkLib.ProximityGap.Frontier.R27GD8D16Mirrors.key_scale8
#print axioms ArkLib.ProximityGap.Frontier.R27GD8D16Mirrors.bigB8_sq_le
#print axioms ArkLib.ProximityGap.Frontier.R27GD8D16Mirrors.params16_count
#print axioms ArkLib.ProximityGap.Frontier.R27GD8D16Mirrors.params16_admiss
#print axioms ArkLib.ProximityGap.Frontier.R27GD8D16Mirrors.pairing16
#print axioms ArkLib.ProximityGap.Frontier.R27GD8D16Mirrors.key_scale16
#print axioms ArkLib.ProximityGap.Frontier.R27GD8D16Mirrors.bigB16_sq_le
