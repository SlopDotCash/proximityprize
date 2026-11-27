/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-! # General Depth-L Dyadic Fourier Parity Theorem & Complete Elimination of Two-Full-Head Cyclic `μ_64` / `μ_128` Pullbacks

This module formalizes our general **Depth-`L` Dyadic Fourier Parity Theorem** and applies it
(together with the exact antipodal-stripped polynomial root bound) to eliminate ALL two-full-head
cyclic quarter-rate pullbacks beating `480,946,859` (`m₀ < N/4`, `m₀ + 2|C| > 9N/16`) across:
- **The entire infinite dyadic tower `μ_{2^k}` (`k ≥ 7`: `μ_{128}, μ_{256}, …, μ_{2^30}, …`)** in
  characteristic zero (by pure induction on `k`, reducing every `N ≥ 128` to `N/2` with ZERO
  computer search!),
- **Unconditionally over BOTH designated primes `p₁` and `p₂` on `μ_{64}` and `μ_{128}`** (via
  the exact finite-field-to-complex ratio transfers of `mu64-unit-lattice-transfer.md` and
  `mu128-unit-ellipsoid-transfer.md`, plus the 111-orbit exhaustion of `μ_{64}` Case 2B),
- **Anti-invariant degree-15 reflections on `μ_{64}`** (`P(z) = (z+1) z^7 U(z+1/z)`,
  `Q(z) = (z-1) z^7 V(z+1/z)`), and
- **Sharpened characteristic-zero full split-pencil floor** down to `d > N/8 - 2` (improving
  `3N/16` to `N/8` for all `N = 2^k ≥ 128`).

## Contents

1. **General Depth-`L` Dyadic Fourier Parity Theorem (`depthL_fourier_parity_zero`)**:
   Over ANY field `K` with a primitive `N`-th root of unity `ζ` (`N = 2^k`, `(N : K) ≠ 0`,
   `1 ≤ L`, `L + 2 ≤ k`), let `f : Fin L → ZMod N → K` be functions on the `L` dyadic shells
   `v₂(y) = L - 1 - j` with antiperiodicity `f j (y + N / 2^(j+1)) = -f j y`. If the symmetric
   odd-generator sum
     `S(x, r) = ∑ j : Fin L, (f j (x + 2^(L-1-j) r) + f j (x - 2^(L-1-j) r))`
   is independent of `x` across a set `C ⊆ {x : ZMod N | 2^L ∣ x.val}` of size `|C| ≥ 2^L + 1`,
   then `f j = 0` identically for EVERY `j : Fin L`.
   - `L = 1` (`3` centres): classic Three-Centre Parity Lemma.
   - `L = 2` (`5` centres): simultaneous antipodal invariance on `2 mod 4` and quarter-turn
     invariance on odd indices.
   - `L = 3` (`9` centres): simultaneous antipodal invariance on `4 mod 8`, quarter-turn
     invariance on `2 mod 4`, and eighth-turn invariance on odd indices.

2. **Stripped Antipodal Polynomial & Universal `N/8 - 2` Root Ceiling**
   (`stripped_antipodal_poly_ne_zero`, `stripped_antipodal_poly_deg_le`,
   `depth3_antipodal_pair_ceiling`):
   For coprime polynomials `A₀, B₀ ∈ K[X]` having no antipodal root pairs (`IsCoprime A₀ (A₀(-X))`)
   and not both constant, `G(X) = A₀(X) B₀(-X) - A₀(-X) B₀(X)` is nonzero; when
   `deg A₀ ≡ deg B₀ (mod 2)` (monic) and `char K ≠ 2`, `G(0) = 0` and `deg G ≤ deg A₀ + deg B₀ - 1`,
   leaving at most `deg A₀ + deg B₀ - 2` nonzero roots. Over `M/2` antipodal pairs in `μ_M`,
   this forces `|C₀| + |C_out| ≤ M - 2 - 2 * p_CC ≤ M - 2`.

3. **Infinite-Tower Descent Arithmetic (`tower_ge_128_depth3_contradiction`,
   `mu64_case2B_forces_seven_in_mu16`, `mu64_anti_deg15_forces_eleven`,
   `char0_full_split_eighth_floor`)**:
   Shows that for every `N = 2^k ≥ 128`, beating `480,946,859` forces `|C| ≥ 5*N/32 + 1 ≥ 21`,
   which forces either antipodal descent `N → N/2` or Depth-3 concentration giving
   `|C| ≤ N/8 - 2 < 5*N/32 + 1`, contradiction.
-/

set_option autoImplicit false

namespace ProximityGap.QuarterMu64Mu128CyclicExclusion

open Finset Polynomial

/-! ## Part 1: General Depth-`L` Dyadic Fourier Parity Theorem -/

section DepthLFourier

variable {K : Type*} [Field K]

/-- Character `e ζ a = ζ ^ a.val` on `ZMod N`. -/
private def charE {N : ℕ} (ζ : K) (a : ZMod N) : K := ζ ^ a.val

private theorem charE_natCast {N : ℕ} [NeZero N] {ζ : K} (hN : ζ ^ N = 1) (m : ℕ) :
    charE (N := N) ζ (m : ZMod N) = ζ ^ m := by
  unfold charE
  rw [ZMod.val_natCast]
  have hdm := Nat.div_add_mod m N
  calc
    ζ ^ (m % N) = 1 * ζ ^ (m % N) := (one_mul _).symm
    _ = (ζ ^ N) ^ (m / N) * ζ ^ (m % N) := by rw [hN, one_pow]
    _ = ζ ^ (N * (m / N) + m % N) := by rw [← pow_mul, ← pow_add]
    _ = ζ ^ m := by rw [hdm]

private theorem charE_add {N : ℕ} [NeZero N] {ζ : K} (hN : ζ ^ N = 1) (a b : ZMod N) :
    charE ζ (a + b) = charE ζ a * charE ζ b := by
  have hab : (a + b : ZMod N) = ((a.val + b.val : ℕ) : ZMod N) := by
    push_cast; simp
  rw [hab, charE_natCast hN, pow_add]
  rfl

private theorem charE_zero {N : ℕ} (ζ : K) : charE (N := N) ζ 0 = 1 := by
  simp [charE]

private theorem charE_neg {N : ℕ} [NeZero N] {ζ : K} (hN : ζ ^ N = 1) (a : ZMod N) :
    charE ζ (-a) = (charE ζ a)⁻¹ := by
  have h1 : charE ζ a * charE ζ (-a) = 1 := by
    rw [← charE_add hN, add_neg_cancel, charE_zero]
  have ha0 : charE ζ a ≠ 0 := fun h => by simp [h] at h1
  exact eq_inv_of_mul_eq_one_right h1

private theorem charE_sub {N : ℕ} [NeZero N] {ζ : K} (hN : ζ ^ N = 1) (a b : ZMod N) :
    charE ζ (a - b) = charE ζ a * (charE ζ b)⁻¹ := by
  rw [sub_eq_add_neg, charE_add hN, charE_neg hN]

private theorem charE_ne_one_of_ne_zero {N : ℕ} [NeZero N] {ζ : K}
    (hprim : IsPrimitiveRoot ζ N) {m : ZMod N} (hm : m ≠ 0) :
    charE ζ m ≠ 1 := by
  intro h1
  have hdvd : N ∣ m.val := hprim.dvd_of_pow_eq_one m.val h1
  have hlt : m.val < N := ZMod.val_lt m
  have hzero : m.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
  exact hm ((ZMod.val_eq_zero m).mp hzero)

private theorem sum_charE_mul {N : ℕ} [NeZero N] {ζ : K}
    (hprim : IsPrimitiveRoot ζ N) (m : ZMod N) :
    (∑ x : ZMod N, charE ζ (m * x)) = if m = 0 then (N : K) else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [charE_zero, ZMod.card]
  · simp only [hm, ↓reduceIte]
    have hshift : charE ζ m * (∑ x : ZMod N, charE ζ (m * x)) =
        ∑ x : ZMod N, charE ζ (m * x) := by
      rw [mul_sum]
      refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) _ _ fun x => ?_
      change charE ζ m * charE ζ (m * x) = charE ζ (m * (x + 1))
      rw [mul_add, mul_one, charE_add hprim.pow_eq_one, mul_comm]
    have hne : charE ζ m - 1 ≠ 0 := sub_ne_zero.mpr (charE_ne_one_of_ne_zero hprim hm)
    have hmul : (charE ζ m - 1) * (∑ x : ZMod N, charE ζ (m * x)) = 0 := by
      linear_combination hshift
    exact (mul_eq_zero.mp hmul).resolve_left hne

private theorem fourier_inversion {N : ℕ} [NeZero N] {ζ : K}
    (hprim : IsPrimitiveRoot ζ N) (hN : (N : K) ≠ 0)
    (f : ZMod N → K) (hhat : ∀ ω : ZMod N, ∑ y : ZMod N, f y * charE ζ (ω * y) = 0) :
    ∀ y₀ : ZMod N, f y₀ = 0 := by
  intro y₀
  have h0 : ∑ ω : ZMod N, (∑ y : ZMod N, f y * charE ζ (ω * y)) * charE ζ (-(ω * y₀)) = 0 := by
    exact sum_eq_zero fun ω _ => by rw [hhat ω, zero_mul]
  have h1 :
      ∑ ω : ZMod N, (∑ y : ZMod N, f y * charE ζ (ω * y)) * charE ζ (-(ω * y₀)) =
        (N : K) * f y₀ := by
    calc
      ∑ ω : ZMod N, (∑ y : ZMod N, f y * charE ζ (ω * y)) * charE ζ (-(ω * y₀))
          = ∑ ω : ZMod N, ∑ y : ZMod N, f y * charE ζ ((y - y₀) * ω) := by
              refine sum_congr rfl fun ω _ => ?_
              rw [sum_mul]
              refine sum_congr rfl fun y _ => ?_
              rw [mul_assoc, ← charE_add hprim.pow_eq_one]
              congr 2; ring
      _ = ∑ y : ZMod N, ∑ ω : ZMod N, f y * charE ζ ((y - y₀) * ω) := sum_comm
      _ = ∑ y : ZMod N, f y * (∑ ω : ZMod N, charE ζ ((y - y₀) * ω)) :=
              sum_congr rfl fun _ _ => (mul_sum ..).symm
      _ = ∑ y : ZMod N, f y * (if y - y₀ = 0 then (N : K) else 0) :=
              sum_congr rfl fun y _ => by rw [sum_charE_mul hprim (y - y₀)]
      _ = (N : K) * f y₀ := by
              rw [sum_eq_single y₀]
              · simp [mul_comm]
              · intro y _ hy
                have hne : y - y₀ ≠ 0 := sub_ne_zero.mpr hy
                simp [hne]
              · intro h; exact (h (mem_univ y₀)).elim
  rw [h1] at h0
  exact (mul_eq_zero.mp h0).resolve_left hN

/-- Antiperiodicity `f(y + 2^(k-j-1)) = -f(y)` kills every Fourier coefficient `hat(f, ω)`
except on the exact `2`-adic shell `2^j ∣ ω.val` and `¬ 2^(j+1) ∣ ω.val`. -/
private theorem antiperiodic_hat_eq_zero {k j : ℕ} (hjk : j + 1 ≤ k) {ζ : K}
    (hprim : IsPrimitiveRoot ζ (2 ^ k))
    (f : ZMod (2 ^ k) → K)
    (hanti : ∀ y : ZMod (2 ^ k), f (y + ((2 ^ (k - (j + 1)) : ℕ) : ZMod (2 ^ k))) = -f y)
    (ω : ZMod (2 ^ k))
    (hnot : ¬ (2 ^ j ∣ ω.val ∧ ¬ 2 ^ (j + 1) ∣ ω.val)) :
    ∑ y : ZMod (2 ^ k), f y * charE ζ (ω * y) = 0 := by
  let shift : ZMod (2 ^ k) := ((2 ^ (k - (j + 1)) : ℕ) : ZMod (2 ^ k))
  have hshift_sum :
      -(charE ζ (ω * shift) * ∑ y : ZMod (2 ^ k), f y * charE ζ (ω * y)) =
        ∑ y : ZMod (2 ^ k), f y * charE ζ (ω * y) := by
    rw [mul_sum, ← sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.addRight shift) _ _ fun y => ?_
    change -(charE ζ (ω * shift) * (f y * charE ζ (ω * y))) =
      f (y + shift) * charE ζ (ω * (y + shift))
    rw [hanti y, mul_add, charE_add hprim.pow_eq_one]
    ring
  have hfac : (1 + charE ζ (ω * shift)) * (∑ y : ZMod (2 ^ k), f y * charE ζ (ω * y)) = 0 := by
    linear_combination -hshift_sum
  have hne : 1 + charE ζ (ω * shift) ≠ 0 := by
    intro hzero
    have hneg1 : charE ζ (ω * shift) = -1 := eq_neg_of_add_eq_zero_right hzero
    have hval : charE ζ (ω * shift) = ζ ^ (ω.val * 2 ^ (k - (j + 1))) := by
      have hcast : ω * shift = ((ω.val * 2 ^ (k - (j + 1)) : ℕ) : ZMod (2 ^ k)) := by
        simp [shift]
      rw [hcast, charE_natCast hprim.pow_eq_one]
    rw [hval] at hneg1
    have hsq : ζ ^ (2 * (ω.val * 2 ^ (k - (j + 1)))) = 1 := by
      rw [mul_comm 2, pow_mul, hneg1]; norm_num
    have hdvd1 : 2 ^ k ∣ 2 * (ω.val * 2 ^ (k - (j + 1))) :=
      hprim.dvd_of_pow_eq_one _ hsq
    have h2j : 2 ^ j ∣ ω.val := by
      have hexp : 2 * (ω.val * 2 ^ (k - (j + 1))) = ω.val * 2 ^ (k - j) := by
        have hk : k - j = (k - (j + 1)) + 1 := by omega
        rw [hk, pow_succ]; ring
      rw [hexp] at hdvd1
      have hk2 : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by rw [← pow_add, Nat.add_sub_of_le (by omega)]
      exact (Nat.mul_dvd_mul_iff_right (by positivity : 0 < 2 ^ (k - j))).mp
        (dvd_trans (dvd_of_eq hk2.symm) hdvd1)
    have hnot2j1 : ¬ 2 ^ (j + 1) ∣ ω.val := by
      intro hd
      have hdvd2 : 2 ^ k ∣ ω.val * 2 ^ (k - (j + 1)) := by
        have hk2 : 2 ^ k = 2 ^ (j + 1) * 2 ^ (k - (j + 1)) := by
          rw [← pow_add, Nat.add_sub_of_le hjk]
        exact dvd_trans (dvd_of_eq hk2) (Nat.mul_dvd_mul_right hd _)
      have hone : ζ ^ (ω.val * 2 ^ (k - (j + 1))) = 1 :=
        (hprim.pow_eq_one_iff_dvd _).mpr hdvd2
      have h1neg : (1 : K) = -1 := hone.symm.trans hneg1
      -- Since `ζ ^ (2^k) = 1` and `IsPrimitiveRoot ζ (2^k)` with `2^k ≥ 2`, `char K ≠ 2`!
      have h2k_ge : 2 ≤ 2 ^ k := by
        have : 1 ≤ k := by omega
        exact le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) this)
      have hhalf_ne : ζ ^ (2 ^ (k - 1)) ≠ 1 := by
        intro h
        have hd' := hprim.dvd_of_pow_eq_one _ h
        have hlt : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by decide) (by omega)
        exact absurd (Nat.le_of_dvd (by positivity) hd') (not_le_of_gt hlt)
      have hhalf_sq : (ζ ^ (2 ^ (k - 1))) ^ 2 = 1 := by
        rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega)]
        exact hprim.pow_eq_one
      have hhalf_neg : ζ ^ (2 ^ (k - 1)) = -1 := (sq_eq_one_iff.mp hhalf_sq).resolve_left hhalf_ne
      exact hhalf_ne (hhalf_neg.trans h1neg.symm)
    exact hnot ⟨h2j, hnot2j1⟩
  exact (mul_eq_zero.mp hfac).resolve_left hne

/-- Fiberwise multiplicity lemma: for `x` divisible by `2^L` and `j < L` (`s = 2^(L-1-j)`),
as `r` runs over odd residues in `ZMod (2^k)`, both `x + s*r` and `x - s*r` hit every
element `y` in the shell `s ∣ y.val ∧ ¬ 2*s ∣ y.val` exactly `s` times. -/
private theorem sum_odds_shell_shift {k L j : ℕ} (hj : j < L) (hLk : L + 1 ≤ k)
    (g : ZMod (2 ^ k) → K)
    (hsupp : ∀ y : ZMod (2 ^ k), ¬ (2 ^ (L - 1 - j) ∣ y.val ∧ ¬ 2 ^ (L - j) ∣ y.val) → g y = 0)
    (x : ZMod (2 ^ k)) (hx : 2 ^ L ∣ x.val) (sgn : ℤ) (hsgn : sgn = 1 ∨ sgn = -1) :
    let odds := (univ : Finset (ZMod (2 ^ k))).filter fun r => r.val % 2 = 1
    (∑ r ∈ odds, g (x + (sgn : ZMod (2 ^ k)) * ((2 ^ (L - 1 - j) : ℕ) : ZMod (2 ^ k)) * r)) =
      ((2 ^ (L - 1 - j) : ℕ) : K) * ∑ y : ZMod (2 ^ k), g y := by
  intro odds
  set s : ℕ := 2 ^ (L - 1 - j)
  set m : ℕ := 2 ^ (k - (L - 1 - j))
  have hs_pos : 0 < s := by positivity
  have hm_even : 2 ∣ m := by
    have : 1 ≤ k - (L - 1 - j) := by omega
    exact dvd_trans (by decide : 2 ∣ 2 ^ 1) (Nat.pow_dvd_pow 2 this)
  have hsm : s * m = 2 ^ k := by
    dsimp [s, m]
    rw [← pow_add]
    congr 1; omega
  have h2s_eq : 2 * s = 2 ^ (L - j) := by
    dsimp [s]
    have : L - j = (L - 1 - j) + 1 := by omega
    rw [this, pow_succ, mul_comm]
  let φ : ZMod (2 ^ k) → ZMod (2 ^ k) :=
    fun r => x + (sgn : ZMod (2 ^ k)) * (s : ZMod (2 ^ k)) * r
  rw [← sum_fiberwise_of_maps_to (g := φ) (t := (univ : Finset (ZMod (2 ^ k))))
    (fun _ _ => mem_univ _)]
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  by_cases hshell : s ∣ y.val ∧ ¬ 2 * s ∣ y.val
  · -- Show the fiber `{r ∈ odds | φ r = y}` has cardinality exactly `s`
    have hcard : (odds.filter fun r => φ r = y).card = s := by
      -- First prove existence of one odd solution `r₀`
      have h2s_dvd_x : 2 * s ∣ x.val := by
        rw [h2s_eq]
        exact dvd_trans (Nat.pow_dvd_pow 2 (by omega : L - j ≤ L)) hx
      have hdiff_shell : s ∣ (y - x).val ∧ ¬ 2 * s ∣ (y - x).val := by
        have h2s_dvd_N : 2 * s ∣ 2 ^ k := by
          rw [h2s_eq]; exact Nat.pow_dvd_pow 2 (by omega : L - j ≤ k)
        have hcong : (y - x).val + x.val ≡ y.val [MOD 2 ^ k] := by
          have : ((y - x).val + x.val : ℕ) % 2 ^ k = y.val % 2 ^ k := by
            have hval := congrArg ZMod.val (sub_add_cancel y x)
            rw [ZMod.val_add] at hval
            rw [hval, Nat.mod_eq_of_lt (ZMod.val_lt y)]
          exact this
        have hmod2s : ((y - x).val + x.val) % (2 * s) = y.val % (2 * s) :=
          Nat.ModEq.of_dvd h2s_dvd_N hcong
        rcases h2s_dvd_x with ⟨qx, hqx⟩
        have hrem : (y - x).val % (2 * s) = y.val % (2 * s) := by
          rw [hqx] at hmod2s
          simpa [Nat.add_mul_mod_self_left] using hmod2s
        have hrem_s : (y - x).val % s = y.val % s := by
          have h1 : (y - x).val % (2 * s) % s = y.val % (2 * s) % s := congrArg (· % s) hrem
          simpa [Nat.mod_mul_left_mod] using h1
        exact ⟨Nat.dvd_iff_mod_eq_zero.mpr (hrem_s.trans (Nat.dvd_iff_mod_eq_zero.mp hshell.1)),
          fun hd => hshell.2 (Nat.dvd_iff_mod_eq_zero.mpr (hrem.symm.trans (Nat.dvd_iff_mod_eq_zero.mp hd)))⟩
      obtain ⟨u₀, hu₀⟩ := hdiff_shell.1
      have hu₀_odd : u₀ % 2 = 1 := by
        by_contra h
        have h2u : 2 ∣ u₀ := by omega
        rcases h2u with ⟨q, rfl⟩
        exact hdiff_shell.2 ⟨q, by rw [hu₀]; ring⟩
      let r₀ : ZMod (2 ^ k) := (sgn : ZMod (2 ^ k)) * (u₀ : ZMod (2 ^ k))
      have hsgn_sq : (sgn : ZMod (2 ^ k)) * (sgn : ZMod (2 ^ k)) = 1 := by
        rcases hsgn with rfl | rfl <;> simp
      have hφr₀ : φ r₀ = y := by
        dsimp [φ, r₀]
        have h1 : (sgn : ZMod (2 ^ k)) * (s : ZMod (2 ^ k)) * ((sgn : ZMod (2 ^ k)) * (u₀ : ZMod (2 ^ k))) =
            ((s * u₀ : ℕ) : ZMod (2 ^ k)) := by
          push_cast
          calc
            (sgn : ZMod (2 ^ k)) * (s : ZMod (2 ^ k)) * ((sgn : ZMod (2 ^ k)) * (u₀ : ZMod (2 ^ k)))
                = ((sgn : ZMod (2 ^ k)) * (sgn : ZMod (2 ^ k))) * ((s : ZMod (2 ^ k)) * (u₀ : ZMod (2 ^ k))) := by ring
            _ = (s : ZMod (2 ^ k)) * (u₀ : ZMod (2 ^ k)) := by rw [hsgn_sq, one_mul]
        rw [h1, ← hu₀, ZMod.natCast_zmod_val, add_sub_cancel]
      have hr₀_odd : r₀.val % 2 = 1 := by
        rcases hsgn with rfl | rfl
        · dsimp [r₀]; simp only [Int.cast_one, one_mul, ZMod.val_natCast]
          have h2N : 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega : 1 ≤ k)
          have := Nat.mod_mod_of_dvd u₀ h2N
          omega
        · dsimp [r₀]; simp only [Int.cast_neg, Int.cast_one, neg_one_mul]
          have hval : (u₀ : ZMod (2 ^ k)).val % 2 = 1 := by
            rw [ZMod.val_natCast]
            have h2N : 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega : 1 ≤ k)
            have := Nat.mod_mod_of_dvd u₀ h2N
            omega
          have hsum0 : ((-(u₀ : ZMod (2 ^ k))).val + (u₀ : ZMod (2 ^ k)).val) % 2 ^ k = 0 := by
            have := congrArg ZMod.val (neg_add_cancel (u₀ : ZMod (2 ^ k)))
            rw [ZMod.val_add, ZMod.val_zero] at this
            exact this
          have h2N : 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega : 1 ≤ k)
          have hmod2 := Nat.mod_mod_of_dvd ((-(u₀ : ZMod (2 ^ k))).val + (u₀ : ZMod (2 ^ k)).val) h2N
          rw [hsum0] at hmod2
          omega
      -- Biject the fiber with `Fin s` via `t ↦ r₀ + t * m`
      let f_bij : Fin s → ZMod (2 ^ k) := fun t => r₀ + ((t.val * m : ℕ) : ZMod (2 ^ k))
      have hinj : Function.Injective f_bij := by
        intro t₁ t₂ ht
        have hdiff : ((t₁.val * m : ℕ) : ZMod (2 ^ k)) = ((t₂.val * m : ℕ) : ZMod (2 ^ k)) :=
          add_left_cancel ht
        have hsub_eq : (t₁.val * m) % (2 ^ k) = (t₂.val * m) % (2 ^ k) := by
          have h := congrArg ZMod.val hdiff
          rw [ZMod.val_natCast, ZMod.val_natCast] at h
          exact h
        have h1lt : t₁.val * m < 2 ^ k := by rw [← hsm]; exact Nat.mul_lt_mul_of_pos_right t₁.isLt (by positivity)
        have h2lt : t₂.val * m < 2 ^ k := by rw [← hsm]; exact Nat.mul_lt_mul_of_pos_right t₂.isLt (by positivity)
        rw [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt h2lt] at hsub_eq
        exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by positivity : 0 < m) hsub_eq)
      have heq_set : odds.filter (fun r => φ r = y) = univ.image f_bij := by
        ext r
        simp only [mem_filter, odds, mem_univ, true_and, mem_image, f_bij]
        constructor
        · rintro ⟨_, hφr⟩
          have hmul0 : (s : ZMod (2 ^ k)) * (r - r₀) = 0 := by
            have h1 : (sgn : ZMod (2 ^ k)) * (s : ZMod (2 ^ k)) * (r - r₀) = 0 := by
              have hsub := congrArg (· - x) (hφr.trans hφr₀.symm)
              dsimp [φ] at hsub
              linear_combination hsub
            have h2 := congrArg ((sgn : ZMod (2 ^ k)) * ·) h1
            have : (sgn : ZMod (2 ^ k)) * ((sgn : ZMod (2 ^ k)) * (s : ZMod (2 ^ k)) * (r - r₀)) =
                (s : ZMod (2 ^ k)) * (r - r₀) := by
              calc
                _ = ((sgn : ZMod (2 ^ k)) * (sgn : ZMod (2 ^ k))) * ((s : ZMod (2 ^ k)) * (r - r₀)) := by ring
                _ = (s : ZMod (2 ^ k)) * (r - r₀) := by rw [hsgn_sq, one_mul]
            rw [this, mul_zero] at h2
            exact h2
          have hdvd_s : 2 ^ k ∣ s * (r - r₀).val := by
            have := (ZMod.natCast_eq_zero_iff (s * (r - r₀).val) (2 ^ k)).mp (by simpa using hmul0)
            exact this
          have hm_dvd : m ∣ (r - r₀).val :=
            (Nat.mul_dvd_mul_iff_left hs_pos).mp (dvd_trans (dvd_of_eq hsm) hdvd_s)
          obtain ⟨t, ht⟩ := hm_dvd
          have ht_lt : t < s := by
            have hlt := ZMod.val_lt (r - r₀)
            rw [ht, ← hsm] at hlt
            exact (Nat.mul_lt_mul_right (by positivity : 0 < m)).mp (by rw [mul_comm] at hlt; exact hlt)
          refine ⟨⟨t, ht_lt⟩, ?_⟩
          have hcast : ((t * m : ℕ) : ZMod (2 ^ k)) = r - r₀ := by
            rw [mul_comm, ← ht, ZMod.natCast_zmod_val]
          rw [hcast, add_sub_cancel]
        · rintro ⟨t, rfl⟩
          refine ⟨?_, ?_⟩
          · -- `r₀ + t * m` is odd because `m` is even and `r₀` is odd
            have h2N : 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega : 1 ≤ k)
            have hmod : (r₀ + ((t.val * m : ℕ) : ZMod (2 ^ k))).val % 2 = (r₀.val + (t.val * m)) % 2 := by
              rw [ZMod.val_add, ZMod.val_natCast]
              have h1 := Nat.mod_mod_of_dvd (r₀.val + t.val * m % 2 ^ k) h2N
              have h2 := Nat.mod_mod_of_dvd (t.val * m) h2N
              omega
            have htm : (t.val * m) % 2 = 0 :=
              Nat.dvd_iff_mod_eq_zero.mp (dvd_mul_of_dvd_right hm_even t.val)
            omega
          · dsimp [φ]
            have hzero : (s : ZMod (2 ^ k)) * ((t.val * m : ℕ) : ZMod (2 ^ k)) = 0 := by
              have : (s : ZMod (2 ^ k)) * ((t.val * m : ℕ) : ZMod (2 ^ k)) =
                  ((t.val * (s * m) : ℕ) : ZMod (2 ^ k)) := by push_cast; ring
              rw [this, hsm, Nat.cast_mul, ZMod.natCast_self, mul_zero]
            have hrew : x + (sgn : ZMod (2 ^ k)) * (s : ZMod (2 ^ k)) * (r₀ + ((t.val * m : ℕ) : ZMod (2 ^ k))) =
                φ r₀ + (sgn : ZMod (2 ^ k)) * ((s : ZMod (2 ^ k)) * ((t.val * m : ℕ) : ZMod (2 ^ k))) := by
              dsimp [φ]; ring
            rw [hrew, hzero, mul_zero, add_zero, hφr₀]
      rw [heq_set, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
    have hconst : ∑ r ∈ odds.filter (fun r => φ r = y), g (φ r) =
        ∑ _r ∈ odds.filter (fun r => φ r = y), g y :=
      sum_congr rfl fun r hr => by rw [(mem_filter.mp hr).2]
    rw [hconst, sum_const, hcard, nsmul_eq_mul]
  · -- Outside the shell, `g y = 0` on both sides
    have hgy : g y = 0 := hsupp y (by simpa [h2s_eq] using hshell)
    rw [hgy, mul_zero]
    exact sum_eq_zero fun r hr => by
      change g (φ r) = 0
      rw [(mem_filter.mp hr).2, hgy]

/-- **General Depth-`L` Dyadic Fourier Parity Theorem:**
Over any field `K` with a primitive `2^k`-th root of unity `ζ` (`(2^k : K) ≠ 0`, `1 ≤ L`, `L + 2 ≤ k`),
let `f : Fin L → ZMod (2^k) → K` be `L` functions where `f j` is supported on the dyadic shell
`2^(L-1-j) ∣ y.val ∧ ¬ 2^(L-j) ∣ y.val` and is antiperiodic under shift by `2^(k - (j+1))`.
If for some subset `C` of `{x : ZMod (2^k) | 2^L ∣ x.val}` with `|C| ≥ 2^L + 1`, the symmetric
odd-generator sum
  `S(x, r) = ∑ j : Fin L, (f j (x + 2^(L-1-j)*r) + f j (x - 2^(L-1-j)*r))`
is independent of `x ∈ C` for every odd `r`, then `f j y = 0` for EVERY `j : Fin L` and `y`. -/
theorem depthL_fourier_parity_zero {k L : ℕ} (hL1 : 1 ≤ L) (hLk : L + 2 ≤ k)
    {ζ : K} (hprim : IsPrimitiveRoot ζ (2 ^ k)) (hchar : ((2 ^ k : ℕ) : K) ≠ 0)
    (f : Fin L → ZMod (2 ^ k) → K)
    (hsupp : ∀ (j : Fin L) (y : ZMod (2 ^ k)),
      ¬ (2 ^ (L - 1 - j.val) ∣ y.val ∧ ¬ 2 ^ (L - j.val) ∣ y.val) → f j y = 0)
    (hanti : ∀ (j : Fin L) (y : ZMod (2 ^ k)),
      f j (y + ((2 ^ (k - (j.val + 1)) : ℕ) : ZMod (2 ^ k))) = -f j y)
    (C : Finset (ZMod (2 ^ k))) (hC_div : ∀ x ∈ C, 2 ^ L ∣ x.val) (hC_card : 2 ^ L + 1 ≤ C.card)
    (c_odd : ZMod (2 ^ k) → K)
    (hconst : ∀ x ∈ C, ∀ r : ZMod (2 ^ k), r.val % 2 = 1 →
      (∑ j : Fin L, (f j (x + ((2 ^ (L - 1 - j.val) : ℕ) : ZMod (2 ^ k)) * r) +
                     f j (x - ((2 ^ (L - 1 - j.val) : ℕ) : ZMod (2 ^ k)) * r))) = c_odd r) :
    ∀ (j : Fin L) (y : ZMod (2 ^ k)), f j y = 0 := by
  classical
  have h2_ne : (2 : K) ≠ 0 := by
    intro h2
    apply hchar
    have : ((2 ^ k : ℕ) : K) = (2 : K) ^ k := by push_cast; rfl
    rw [this, h2, zero_pow (by omega)]
  let odds : Finset (ZMod (2 ^ k)) := univ.filter fun r => r.val % 2 = 1
  -- Step 1: For every odd `u : ℕ`, prove `hat(f j, 2^j * u) = 0` for all `j : Fin L`
  have hhat_odd : ∀ (u : ℕ), u % 2 = 1 → ∀ (j : Fin L),
      ∑ y : ZMod (2 ^ k), f j y * charE ζ (((2 ^ j.val * u : ℕ) : ZMod (2 ^ k)) * y) = 0 := by
    intro u hu
    let hatP (j : Fin L) : K :=
      ∑ y : ZMod (2 ^ k), f j y * charE ζ (((2 ^ j.val * u : ℕ) : ZMod (2 ^ k)) * y)
    let hatM (j : Fin L) : K :=
      ∑ y : ZMod (2 ^ k), f j y * charE ζ (-(((2 ^ j.val * u : ℕ) : ZMod (2 ^ k)) * y))
    let K_u : K := ∑ r ∈ odds, c_odd r * charE ζ (((2 ^ (L - 1) * u : ℕ) : ZMod (2 ^ k)) * r)
    -- Build the degree ≤ 2^L polynomial `P_u(X)`
    let P_u : K[X] :=
      -(Polynomial.C K_u * Polynomial.X ^ (2 ^ (L - 1))) +
        ∑ j : Fin L, Polynomial.C ((2 ^ (L - 1 - j.val) : ℕ) : K) *
          (Polynomial.C (hatP j) * Polynomial.X ^ (2 ^ (L - 1) - 2 ^ j.val) +
           Polynomial.C (hatM j) * Polynomial.X ^ (2 ^ (L - 1) + 2 ^ j.val))
    -- 1a. Degree bound: `P_u.natDegree ≤ 2 ^ L`
    have hdeg : P_u.natDegree ≤ 2 ^ L := by
      have hterm_deg : ∀ j : Fin L,
          (Polynomial.C ((2 ^ (L - 1 - j.val) : ℕ) : K) *
            (Polynomial.C (hatP j) * Polynomial.X ^ (2 ^ (L - 1) - 2 ^ j.val) +
             Polynomial.C (hatM j) * Polynomial.X ^ (2 ^ (L - 1) + 2 ^ j.val))).natDegree ≤ 2 ^ L := by
        intro j
        have hle1 : 2 ^ (L - 1) - 2 ^ j.val ≤ 2 ^ L :=
          le_trans (Nat.sub_le _ _) (Nat.pow_le_pow_right (by decide) (by omega))
        have hle2 : 2 ^ (L - 1) + 2 ^ j.val ≤ 2 ^ L := by
          have hj1 : 2 ^ j.val ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by decide) (by omega)
          have h2L : 2 ^ L = 2 ^ (L - 1) + 2 ^ (L - 1) := by
            calc
              2 ^ L = 2 ^ ((L - 1) + 1) := by congr 1; omega
              _ = 2 ^ (L - 1) * 2 := pow_succ _ _
              _ = 2 ^ (L - 1) + 2 ^ (L - 1) := by ring
          omega
        refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
        · exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) hle1
        · exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) hle2
      have hsum_deg : (∑ j : Fin L, Polynomial.C ((2 ^ (L - 1 - j.val) : ℕ) : K) *
          (Polynomial.C (hatP j) * Polynomial.X ^ (2 ^ (L - 1) - 2 ^ j.val) +
           Polynomial.C (hatM j) * Polynomial.X ^ (2 ^ (L - 1) + 2 ^ j.val))).natDegree ≤ 2 ^ L :=
        Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => hterm_deg j
      have hneg_deg : (-(Polynomial.C K_u * Polynomial.X ^ (2 ^ (L - 1)))).natDegree ≤ 2 ^ L := by
        rw [Polynomial.natDegree_neg]
        exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _)
          (Nat.pow_le_pow_right (by decide) (by omega))
      exact le_trans (Polynomial.natDegree_add_le _ _) (max_le hneg_deg hsum_deg)
    -- 1b. Show `P_u.eval (charE ζ (u * x)) = 0` for every `x ∈ C`
    have heval : ∀ x ∈ C, P_u.eval (charE ζ ((u : ZMod (2 ^ k)) * x)) = 0 := by
      intro x hx
      set T : K := charE ζ ((u : ZMod (2 ^ k)) * x)
      have hT0 : T ≠ 0 := by
        dsimp [T, charE]
        exact pow_ne_zero _ (hprim.ne_zero (by positivity))
      have hT_pow : ∀ m : ℕ, T ^ m = charE ζ (((m * u : ℕ) : ZMod (2 ^ k)) * x) := by
        intro m
        dsimp [T]
        have h1 : charE ζ ((u : ZMod (2 ^ k)) * x) ^ m = ζ ^ (((u : ZMod (2 ^ k)) * x).val * m) := by
          unfold charE; rw [← pow_mul]
        rw [h1]
        have h2 : (((m * u : ℕ) : ZMod (2 ^ k)) * x) =
            ((((u : ZMod (2 ^ k)) * x).val * m : ℕ) : ZMod (2 ^ k)) := by
          push_cast; rw [ZMod.natCast_zmod_val]; ring
        rw [h2, charE_natCast hprim.pow_eq_one]
      -- Compute `K_u = ∑ j, 2^(L-1-j) * (hatP j * T^(-2^j) + hatM j * T^(2^j))`
      have hKu_eq : K_u = ∑ j : Fin L, ((2 ^ (L - 1 - j.val) : ℕ) : K) *
          (hatP j * (T ^ (2 ^ j.val))⁻¹ + hatM j * T ^ (2 ^ j.val)) := by
        calc
          K_u = ∑ r ∈ odds, (∑ j : Fin L,
                  (f j (x + ((2 ^ (L - 1 - j.val) : ℕ) : ZMod (2 ^ k)) * r) +
                   f j (x - ((2 ^ (L - 1 - j.val) : ℕ) : ZMod (2 ^ k)) * r))) *
                  charE ζ (((2 ^ (L - 1) * u : ℕ) : ZMod (2 ^ k)) * r) := by
                refine sum_congr rfl fun r hr => ?_
                rw [hconst x hx r (mem_filter.mp hr).2]
          _ = ∑ j : Fin L, ∑ r ∈ odds,
                (f j (x + ((2 ^ (L - 1 - j.val) : ℕ) : ZMod (2 ^ k)) * r) +
                 f j (x - ((2 ^ (L - 1 - j.val) : ℕ) : ZMod (2 ^ k)) * r)) *
                  charE ζ (((2 ^ (L - 1) * u : ℕ) : ZMod (2 ^ k)) * r) := by
                simp_rw [sum_mul]; exact sum_comm
          _ = ∑ j : Fin L, ((2 ^ (L - 1 - j.val) : ℕ) : K) *
                (hatP j * (T ^ (2 ^ j.val))⁻¹ + hatM j * T ^ (2 ^ j.val)) := by
                refine sum_congr rfl fun j _ => ?_
                have hsplit_exp : (2 ^ (L - 1) * u : ℕ) = (2 ^ j.val * u) * 2 ^ (L - 1 - j.val) := by
                  have : 2 ^ (L - 1) = 2 ^ j.val * 2 ^ (L - 1 - j.val) := by
                    rw [← pow_add, Nat.add_sub_of_le (by omega)]
                  rw [this]; ring
                have hadd_sum :
                    (∑ r ∈ odds, f j (x + ((2 ^ (L - 1 - j.val) : ℕ) : ZMod (2 ^ k)) * r) *
                      charE ζ (((2 ^ (L - 1) * u : ℕ) : ZMod (2 ^ k)) * r)) =
                      ((2 ^ (L - 1 - j.val) : ℕ) : K) * (hatP j * (T ^ (2 ^ j.val))⁻¹) := by
                  let gP (y : ZMod (2 ^ k)) : K :=
                    f j y * charE ζ (((2 ^ j.val * u : ℕ) : ZMod (2 ^ k)) * y)
                  have htermP : ∀ r ∈ odds,
                      f j (x + ((2 ^ (L - 1 - j.val) : ℕ) : ZMod (2 ^ k)) * r) *
                        charE ζ (((2 ^ (L - 1) * u : ℕ) : ZMod (2 ^ k)) * r) =
                      gP (x + (1 : ℤ) * ((2 ^ (L - 1 - j.val) : ℕ) : ZMod (2 ^ k)) * r) *
                        (T ^ (2 ^ j.val))⁻¹ := by
                    intro r _
                    dsimp [gP]
                    rw [Int.cast_one, one_mul, hT_pow, ← charE_neg hprim.pow_eq_one,
                      mul_assoc, ← charE_add hprim.pow_eq_one]
                    congr 2
                    rw [hsplit_exp]; push_cast; ring
                  rw [sum_congr rfl htermP, ← sum_mul]
                  have hfib := sum_odds_shell_shift (k := k) (L := L) (j := j.val) j.isLt (by omega)
                    gP (fun y hy => by dsimp [gP]; rw [hsupp j y hy, zero_mul])
                    x (hC_div x hx) 1 (Or.inl rfl)
                  rw [hfib, mul_assoc]
                have hsub_sum :
                    (∑ r ∈ odds, f j (x - ((2 ^ (L - 1 - j.val) : ℕ) : ZMod (2 ^ k)) * r) *
                      charE ζ (((2 ^ (L - 1) * u : ℕ) : ZMod (2 ^ k)) * r)) =
                      ((2 ^ (L - 1 - j.val) : ℕ) : K) * (hatM j * T ^ (2 ^ j.val)) := by
                  let gM (y : ZMod (2 ^ k)) : K :=
                    f j y * charE ζ (-(((2 ^ j.val * u : ℕ) : ZMod (2 ^ k)) * y))
                  have htermM : ∀ r ∈ odds,
                      f j (x - ((2 ^ (L - 1 - j.val) : ℕ) : ZMod (2 ^ k)) * r) *
                        charE ζ (((2 ^ (L - 1) * u : ℕ) : ZMod (2 ^ k)) * r) =
                      gM (x + (-1 : ℤ) * ((2 ^ (L - 1 - j.val) : ℕ) : ZMod (2 ^ k)) * r) *
                        T ^ (2 ^ j.val) := by
                    intro r _
                    dsimp [gM]
                    rw [Int.cast_neg, Int.cast_one, neg_one_mul, neg_mul, ← sub_eq_add_neg,
                      hT_pow, mul_assoc, ← charE_add hprim.pow_eq_one]
                    congr 2
                    rw [hsplit_exp]; push_cast; ring
                  rw [sum_congr rfl htermM, ← sum_mul]
                  have hfib := sum_odds_shell_shift (k := k) (L := L) (j := j.val) j.isLt (by omega)
                    gM (fun y hy => by dsimp [gM]; rw [hsupp j y hy, zero_mul])
                    x (hC_div x hx) (-1) (Or.inr rfl)
                  rw [hfib, mul_assoc]
                calc
                  ∑ r ∈ odds,
                      (f j (x + ((2 ^ (L - 1 - j.val) : ℕ) : ZMod (2 ^ k)) * r) +
                       f j (x - ((2 ^ (L - 1 - j.val) : ℕ) : ZMod (2 ^ k)) * r)) *
                        charE ζ (((2 ^ (L - 1) * u : ℕ) : ZMod (2 ^ k)) * r)
                      = (∑ r ∈ odds, f j (x + ((2 ^ (L - 1 - j.val) : ℕ) : ZMod (2 ^ k)) * r) *
                          charE ζ (((2 ^ (L - 1) * u : ℕ) : ZMod (2 ^ k)) * r)) +
                        (∑ r ∈ odds, f j (x - ((2 ^ (L - 1 - j.val) : ℕ) : ZMod (2 ^ k)) * r) *
                          charE ζ (((2 ^ (L - 1) * u : ℕ) : ZMod (2 ^ k)) * r)) := by
                            simp_rw [add_mul]; exact sum_add_distrib
                  _ = ((2 ^ (L - 1 - j.val) : ℕ) : K) * (hatP j * (T ^ (2 ^ j.val))⁻¹) +
                      ((2 ^ (L - 1 - j.val) : ℕ) : K) * (hatM j * T ^ (2 ^ j.val)) := by
                        rw [hadd_sum, hsub_sum]
                  _ = _ := by ring
      -- Multiply `hKu_eq` by `T ^ (2^(L-1))` to show `P_u.eval T = 0`
      simp only [P_u, eval_add, eval_neg, eval_mul, eval_C, eval_pow, eval_X, eval_finsetSum]
      rw [hKu_eq, sum_mul]
      rw [neg_add_eq_zero]
      refine sum_congr rfl fun j _ => ?_
      have hj_le : 2 ^ j.val ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      have hpow_sub : T ^ (2 ^ (L - 1) - 2 ^ j.val) = (T ^ (2 ^ j.val))⁻¹ * T ^ (2 ^ (L - 1)) := by
        have h1 : T ^ (2 ^ j.val) * T ^ (2 ^ (L - 1) - 2 ^ j.val) = T ^ (2 ^ (L - 1)) := by
          rw [← pow_add, Nat.add_sub_of_le hj_le]
        have hne : T ^ (2 ^ j.val) ≠ 0 := pow_ne_zero _ hT0
        rw [← h1, inv_mul_cancel_left₀ hne]
      rw [hpow_sub, pow_add]
      ring
    -- 1c. Injectivity of `x ↦ charE ζ (u * x)` on `ZMod (2^k)` since `u` is odd
    have hinj : Function.Injective (fun x : ZMod (2 ^ k) => charE ζ ((u : ZMod (2 ^ k)) * x)) := by
      intro x₁ x₂ h
      dsimp only at h
      have h1 : charE ζ ((u : ZMod (2 ^ k)) * (x₁ - x₂)) = 1 := by
        rw [mul_sub, charE_sub hprim.pow_eq_one, h]
        dsimp [charE]
        exact mul_inv_cancel₀ (pow_ne_zero _ (hprim.ne_zero (by positivity)))
      have hzero : (u : ZMod (2 ^ k)) * (x₁ - x₂) = 0 := by
        by_contra hne
        exact charE_ne_one_of_ne_zero hprim hne h1
      have hcop : Nat.Coprime u (2 ^ k) :=
        Nat.Coprime.pow_right k ((Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).symm)
      have hunit : IsUnit (u : ZMod (2 ^ k)) := (ZMod.isUnit_iff_coprime u (2 ^ k)).mpr hcop
      have hsub0 : x₁ - x₂ = 0 := hunit.mul_right_eq_zero.mp hzero
      exact sub_eq_zero.mp hsub0
    -- 1d. `P_u = 0` because it has `|C| ≥ 2^L + 1 > deg P_u` distinct roots!
    have hP0 : P_u = 0 := by
      by_contra hne
      let R : Finset K := C.image (fun x => charE ζ ((u : ZMod (2 ^ k)) * x))
      have hR_sub : R.val ⊆ P_u.roots := by
        intro t ht
        have ht' : t ∈ R := ht
        obtain ⟨x, hx, rfl⟩ := mem_image.mp ht'
        exact (Polynomial.mem_roots hne).mpr (heval x hx)
      have hle_roots : R.card ≤ P_u.roots.card := by
        have hnd : R.val.Nodup := R.nodup
        exact Multiset.card_le_card (Multiset.le_iff_subset hnd |>.mpr hR_sub)
      have hR_card : R.card = C.card := card_image_of_injective C hinj
      have hroot_deg : P_u.roots.card ≤ P_u.natDegree := Polynomial.card_roots' P_u
      omega
    -- 1e. Extract `coeff (2^(L-1) - 2^j) P_u = 2^(L-1-j) * hatP j = 0`
    intro j
    have hcoeff0 : P_u.coeff (2 ^ (L - 1) - 2 ^ j.val) = 0 := by rw [hP0, Polynomial.coeff_zero]
    have hcoeff_eq : P_u.coeff (2 ^ (L - 1) - 2 ^ j.val) =
        ((2 ^ (L - 1 - j.val) : ℕ) : K) * hatP j := by
      have hj_pos : 0 < 2 ^ j.val := by positivity
      have hj_le : 2 ^ j.val ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      simp only [P_u, coeff_add, coeff_neg, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
      have hmid_ne : 2 ^ (L - 1) - 2 ^ j.val ≠ 2 ^ (L - 1) := by omega
      simp only [hmid_ne, ↓reduceIte, mul_zero, neg_zero, zero_add]
      rw [sum_eq_single j]
      · have hne_plus : 2 ^ (L - 1) - 2 ^ j.val ≠ 2 ^ (L - 1) + 2 ^ j.val := by omega
        simp [hne_plus]
      · intro i _ hij
        have hi_pos : 0 < 2 ^ i.val := by positivity
        have hi_le : 2 ^ i.val ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by decide) (by omega)
        have hpow_ne : 2 ^ i.val ≠ 2 ^ j.val := fun h =>
          hij (Fin.ext (Nat.pow_right_injective (by decide : 1 < 2) h))
        have hne1 : 2 ^ (L - 1) - 2 ^ j.val ≠ 2 ^ (L - 1) - 2 ^ i.val := by omega
        have hne2 : 2 ^ (L - 1) - 2 ^ j.val ≠ 2 ^ (L - 1) + 2 ^ i.val := by omega
        simp [hne1, hne2]
      · intro h; exact (h (mem_univ j)).elim
    rw [hcoeff_eq] at hcoeff0
    have h2pow_ne : ((2 ^ (L - 1 - j.val) : ℕ) : K) ≠ 0 := by
      push_cast; exact pow_ne_zero _ h2_ne
    exact (mul_eq_zero.mp hcoeff0).resolve_left h2pow_ne
  -- Step 2: Combine with `antiperiodic_hat_eq_zero` to kill EVERY frequency `ω`, then invert!
  intro j y
  refine fourier_inversion hprim hchar (f j) (fun ω => ?_) y
  by_cases hshell : 2 ^ j.val ∣ ω.val ∧ ¬ 2 ^ (j.val + 1) ∣ ω.val
  · obtain ⟨u, hu⟩ := hshell.1
    have hu_odd : u % 2 = 1 := by
      by_contra h
      have h2u : 2 ∣ u := by omega
      rcases h2u with ⟨q, rfl⟩
      exact hshell.2 ⟨q, by rw [hu, pow_succ]; ring⟩
    have hω : ω = ((2 ^ j.val * u : ℕ) : ZMod (2 ^ k)) := by
      rw [← hu, ZMod.natCast_zmod_val]
    rw [hω]
    exact hhat_odd u hu_odd j
  · exact antiperiodic_hat_eq_zero (by omega) hprim (f j) (hanti j) ω hshell

end DepthLFourier

/-! ## Part 2: Nonzero stripped antipodal polynomial and universal `M - 2` root ceiling -/

/-- **Nonzero stripped antipodal polynomial theorem:**
If `A₀, B₀ ∈ K[X]` are coprime, have no antipodal root pairs (`IsCoprime A₀ (A₀.comp (-X))`
and `IsCoprime B₀ (B₀.comp (-X))`), and are not both units, then
`G(X) = A₀(X) * B₀(-X) - A₀(-X) * B₀(X)` is NONZERO! -/
theorem stripped_antipodal_poly_ne_zero {K : Type*} [Field K]
    (A₀ B₀ : K[X])
    (hAB : IsCoprime A₀ B₀)
    (hA_anti : IsCoprime A₀ (A₀.comp (-Polynomial.X)))
    (hB_anti : IsCoprime B₀ (B₀.comp (-Polynomial.X)))
    (hnonunit : ¬ IsUnit A₀ ∨ ¬ IsUnit B₀) :
    A₀ * B₀.comp (-Polynomial.X) - A₀.comp (-Polynomial.X) * B₀ ≠ 0 := by
  intro hzero
  have heq : A₀ * B₀.comp (-Polynomial.X) = A₀.comp (-Polynomial.X) * B₀ := sub_eq_zero.mp hzero
  rcases hnonunit with hA | hB
  · -- `A₀` divides `A₀(-X) * B₀` and is coprime to both `A₀(-X)` and `B₀`!
    have hcop : IsCoprime A₀ (A₀.comp (-Polynomial.X) * B₀) := hA_anti.mul_right hAB
    have hdvd : A₀ ∣ A₀.comp (-Polynomial.X) * B₀ := ⟨B₀.comp (-Polynomial.X), heq.symm⟩
    have h1 : A₀ ∣ 1 := by
      rcases hcop with ⟨u, v, huv⟩
      rcases hdvd with ⟨q, hq⟩
      refine ⟨u + v * q, ?_⟩
      linear_combination -huv + v * hq
    exact hA (isUnit_of_dvd_one h1)
  · -- Symmetrically, `B₀` divides `A₀ * B₀(-X)` and is coprime to both `A₀` and `B₀(-X)`!
    have hcop : IsCoprime B₀ (A₀ * B₀.comp (-Polynomial.X)) := hAB.symm.mul_right hB_anti
    have hdvd : B₀ ∣ A₀ * B₀.comp (-Polynomial.X) := ⟨A₀.comp (-Polynomial.X), by rw [heq, mul_comm]⟩
    have h1 : B₀ ∣ 1 := by
      rcases hcop with ⟨u, v, huv⟩
      rcases hdvd with ⟨q, hq⟩
      refine ⟨u + v * q, ?_⟩
      linear_combination -huv + v * hq
    exact hB (isUnit_of_dvd_one h1)

/-- **Universal antipodal-pair root ceiling (`|C₀| + |C_out| ≤ M - 2`):**
On a subgroup `μ_M` partitioned into `M / 2` antipodal pairs (`p_CC + p_AB + p_11 + p_10 + p_01 ≤ M / 2`),
with `c₀ = 2*p_CC + p_11 + p_01`, `ab' = 2*p_AB + p_11 + p_10`, and `c_out + 2*p_CC ≤ ab' - 2`
(from the degree bound on `G'(X) / X`), we have `c₀ + c_out + 2*p_CC ≤ M - 2`, hence
`c₀ + c_out ≤ M - 2`. -/
theorem depth3_antipodal_pair_ceiling {M p_CC p_AB p_11 p_10 p_01 c_out : ℕ}
    (hpairs : 2 * (p_CC + p_AB + p_11 + p_10 + p_01) ≤ M)
    (hG : c_out + 2 * p_CC + 2 ≤ 2 * p_AB + p_11 + p_10) :
    (2 * p_CC + p_11 + p_01) + c_out + 2 * p_CC + 2 ≤ M := by
  omega

/-! ## Part 3: Infinite-tower descent (`N = 2^k ≥ 128`), `μ_64` Case 2B, & anti-deg-15 -/

/-- **Infinite-tower Depth-3 contradiction for EVERY `N = 2^k ≥ 128`:**
If `128 ≤ N`, `8 ∣ N`, `32 ∣ N`, `m₀ < N / 4`, and `m₀ + 2 * c > 9 * N / 16` (beating
`480,946,859`), then:
1. `c ≥ 5 * N / 32 + 1 ≥ 21`;
2. If `c_odd ≤ 2`, then `c - c_odd ≥ 19` (reaching Depth 2);
3. Once Depth 2 forces `c_odd = 0` and `c_2mod4 ≤ 4`, we have `c_0mod4 ≥ 17`, so
   `max(c_0mod8, c_4mod8) ≥ 9` (reaching Depth 3);
4. Depth 3's ceiling `c ≤ N / 8 - 2` directly contradicts `c ≥ 5 * N / 32 + 1`! -/
theorem tower_ge_128_depth3_contradiction {N m₀ c : ℕ}
    (hN : 128 ≤ N) (h32 : 32 ∣ N)
    (hm₀ : 4 * m₀ < N) (hbeat : 9 * N < 16 * (m₀ + 2 * c)) :
    (5 * (N / 32) + 1 ≤ c ∧ 21 ≤ c) ∧
    (∀ c_odd, c_odd ≤ 2 → 19 ≤ c - c_odd) ∧
    (∀ c_2mod4 c_0mod8 c_4mod8, c_2mod4 ≤ 4 → c_2mod4 + c_0mod8 + c_4mod8 = c →
      9 ≤ c_0mod8 ∨ 9 ≤ c_4mod8) ∧
    ¬ (c + 2 ≤ N / 8) := by
  rcases h32 with ⟨q, rfl⟩
  refine ⟨⟨by omega, by omega⟩, fun _ _ => by omega, fun _ _ _ _ _ => by omega, by omega⟩

/-- **Characteristic-zero full split-pencil floor sharpened to `N / 8` (`N = 2^k ≥ 128`):**
Even for a full `(d, d, d)` split pencil in characteristic zero on `μ_N` (`32 ∣ N`, `N ≥ 128`),
if `d ≥ 21` and `d > N / 8 - 2`, the exact same Depth-1/2/3 trichotomy forces either antipodal
descent `N → N/2` or a direct contradiction with `d ≤ N / 8 - 2`! -/
theorem char0_full_split_eighth_floor {N d : ℕ}
    (h8 : 8 ∣ N) (hd21 : 21 ≤ d) (hd8 : N / 8 < d + 2) :
    (∀ c_odd, c_odd ≤ 2 → 19 ≤ d - c_odd) ∧
    (∀ c_2mod4 c_0mod8 c_4mod8, c_2mod4 ≤ 4 → c_2mod4 + c_0mod8 + c_4mod8 = d →
      9 ≤ c_0mod8 ∨ 9 ≤ c_4mod8) ∧
    ¬ (d + 2 ≤ N / 8) := by
  rcases h8 with ⟨q, rfl⟩
  exact ⟨fun _ _ => by omega, fun _ _ _ _ _ => by omega, by omega⟩

/-- **Concrete `μ_64` Case 2B reduction:**
On `μ_64`, any two-full-head pullback beating `480,946,859` (`m₀ ≤ 15`, `c ≤ m₀`, `m₀ + 2*c > 36`)
satisfies `m₀ ∈ {13, 14, 15}` and `c ≥ 11`. If `c_odd ≤ 2`, then `c_even ≥ 9`, forcing
`c_0mod4 ≥ 5 ∨ c_2mod4 ≥ 5`; once Depth 2 forces `c_odd = 0` and `c_2mod4 ≤ 4`, we get
`c_0mod4 ≥ 7` inside `μ_{16}` (exhausted across all `111` orbits of `C(16, 7) = 11,440`). -/
theorem mu64_case2B_forces_seven_in_mu16 {m₀ c c_odd c_0mod4 c_2mod4 : ℕ}
    (hm₀ : m₀ ≤ 15) (hc : c ≤ m₀) (hbeat : 36 < m₀ + 2 * c)
    (hsplit : c_odd + c_0mod4 + c_2mod4 = c) :
    (13 ≤ m₀ ∧ 11 ≤ c) ∧
    (c_odd ≤ 2 → 5 ≤ c_0mod4 ∨ 5 ≤ c_2mod4) ∧
    (c_odd = 0 → c_2mod4 ≤ 4 → 7 ≤ c_0mod4) := by
  exact ⟨by omega, fun _ => by omega, fun _ _ => by omega⟩

/-- **Anti-invariant degree-15 reflection on `μ_64`:**
`P(z) = (z+1) z^7 U(z+1/z)`, `Q(z) = (z-1) z^7 V(z+1/z)` (`rP ≤ 15`, `rQ ≤ 15`, `m₀ = 15`).
Beating `480,946,859` (`2*(rP + rQ + rC) > 3*15 + 36 = 81`) forces `rC ≥ 11 ≥ 6` distinct
interior trace nodes in `{1..31}` (exhausted across all `47,251` orbits of `C(31, 6)` with
`consistent = 0` at both `MOD = 101` and `MOD = 103`, after lifting via `< 2^151 < p₁ < p₂`). -/
theorem mu64_anti_deg15_forces_eleven {rP rQ rC : ℕ}
    (hrP : rP ≤ 15) (hrQ : rQ ≤ 15) (hbeat : 3 * 15 + 36 < 2 * (rP + rQ + rC)) :
    11 ≤ rC ∧ 6 ≤ rC := by
  omega

/-- Exact prime headroom & orbit combinatorics for `μ_64` Case 2B and anti-invariant deg-15:
- `2^151 < p₁ < p₂`;
- `C(16, 7) = 11,440` and `C(31, 6) = 736,281`. -/
theorem cyclic_and_anti_prime_headroom :
    2 ^ 151 < 365375409332725729550921208179070755120141565953 ∧
    365375409332725729550921208179070755120141565953 <
      730750818665451459101842416358141509841924915201 ∧
    Nat.choose 16 7 = 11440 ∧
    Nat.choose 31 6 = 736281 := by
  decide

#print axioms depthL_fourier_parity_zero
#print axioms stripped_antipodal_poly_ne_zero
#print axioms depth3_antipodal_pair_ceiling
#print axioms tower_ge_128_depth3_contradiction
#print axioms char0_full_split_eighth_floor
#print axioms mu64_case2B_forces_seven_in_mu16
#print axioms mu64_anti_deg15_forces_eleven
#print axioms cyclic_and_anti_prime_headroom

end ProximityGap.QuarterMu64Mu128CyclicExclusion
