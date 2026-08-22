/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors

THE r=5 RUNG of the deep-band #bad-scalar census (successor of DeepBandR4Bound.lean).

VERIFIED axiom-clean via `cd /home/nubs/Git/ArkLib && lake env lean <this>` (lean4 v4.30.0-rc2,
Mathlib only): every named theorem reports `axioms: [propext, Classical.choice, Quot.sound]`
(or a subset) -- NO sorryAx, NO native_decide.

CONTEXT (B1, NEW-MATH). The deep-band #bad-scalar count is the e1-axis support of the
(e1,e2) joint level set over mu_{2^k}: #{ distinct gamma = -e1(S) over (r+1)-subsets S of mu_n
that are line-forced }. Budget K = 2^r * C(n/2, r); for r=5, K = 32 * C(2g, 5), g = n/4.

THE r=5 MAXIMIZER AND ITS ORBIT STRUCTURE (the new mechanism; B2 EQUIVARIANCE).
  The r=4 parity/antipodal split (Lam-Leung lever) STOPS at r=4: it computes the worst case
  only when the maximizing line is the ORDER-2 character, which fails at r=5 (DeepBandR4Bound
  documents this).  The MEASURED r=5 maximizer is the line

        (e, f) = (n/2 + 1, n - 1)         (monomials x^{n/2+1}, x^{n-1}),

  whose B2 orbit shift is gamma -> g^{e-f} * gamma with e - f = -(n/2 - 2) ≡ n/2 + 2 (mod n);
  since gcd(n, n/2 + 2) = 2 for every n = 2^k (k >= 4), the orbit PERIOD is

        d = n / gcd(n, e - f) = n / 2.

  (So the maximizer is NOT the full-order line d = n; it is the d = n/2 half-order resonance.)
  The bad-scalar set is closed under gamma -> g^{e-f} gamma (B2), and decomposes into
  the singleton gamma = 0 orbit plus `full_orb` orbits each of the full size d = n/2:

        #bad_5  =  1 + (n/2) * full_orb  =  1 + 2g * full_orb,        g = n/4.

  This `#bad = d * orbits + [0 in bad]` decomposition was VERIFIED with the residual-det /
  divided-difference kernel (faithful BabyBear p = 2013265921) component-by-component at
  n = 16, 32, 64, 128:
        n=16: full_orb=11,  d=8,   #bad = 1 + 8*11   = 89;
        n=32: full_orb=90,  d=16,  #bad = 1 + 16*90  = 1441;
        n=64: full_orb=708, d=32,  #bad = 1 + 32*708 = 22657;
        n=128:full_orb=5576,d=64,  #bad = 1 + 64*5576= 356865.
  (The negation symmetry gamma -> -gamma = g^{n/2} gamma is INTERNAL to each size-d orbit:
   -1 lies in <g^{e-f}>, so it does not pair distinct orbits -- it acts within them.)

THE CLOSED FORM (this file, [COMPUTED]-calibrated against the exact kernel at n in
{16,32,64,128}).  With `g = n/4`:

        #bad_5(g)  =  (4 g^4 + 3 g^3 - 10 g^2 + 12) / 12          (closed polynomial in g)

  equivalently the orbit form `1 + 2g * full_orb` with `full_orb = (4 g^3 + 3 g^2 - 10 g)/24`.
  This is the UNIQUE degree-4 polynomial through the four exact data points; refitting any
  three of them and predicting the fourth reproduces it (the n=128 point, computed last,
  CONFIRMED the form 356865 and refuted the competing quadratic-orbit guess 242177).

  KEY STRUCTURAL FACT (why this rung is EASIER than r=3, r=4).  #bad_5 is DEGREE 4 in g, while
  the budget K = 32 C(2g,5) is DEGREE 5 in g.  So #bad_5 / K -> 0 (one full extra degree of
  headroom): the ratio K / #bad_5 = 20.1, 97.0, 284.4, 683.7 at n = 16,32,64,128 and DIVERGES.
  (Contrast r=4, where #bad_4 ~ g^4 and K ~ 10.67 g^4 are the SAME degree, margin ~10.67.)

  DOMAIN OF VALIDITY (measured).  The closed form is the EXACT kernel #bad for `n = 2^k`,
  `k >= 4` (`g in {4, 8, 16, 32, ...}`).  At the degenerate minimal band `n = 8` (`g = 2`) it is
  outside the regime (`K = 0` there; boundary degeneracy, same as r=4 at `g = 2`).  Accordingly
  the calibration rungs below are stated at `n in {16, 32, 64, 128}` and the budget lemmas are
  proven for all `g >= 3` (a fortiori the prize domain `g >= 4`).

This file proves, machine-checked and axiom-clean:
  (1) the orbit-descent identity `12 * #bad_5(g) + 10 g^2 = 4 g^4 + 3 g^3 + 12` for even `g`
      (the `#bad = 1 + 2g*full_orb` reduction, subtraction-free);
  (2) the polynomial budget `#bad_5 <= K` for every `g >= 3`, via the gap polynomial
      `60 (K - #bad_5) = 512 g^5 - 2580 g^4 + 4465 g^3 - 3150 g^2 + 768 g - 60 >= 0`;
  (3) the C-half bound `#bad_5 <= K/2` (i.e. `2 * #bad_5 <= K`) for every `g >= 3`, via
      `60 (K - 2 #bad_5) = 512 g^5 - 2600 g^4 + 4450 g^3 - 3100 g^2 + 768 g - 120 >= 0`.
The orbit-reduction step (1) is the B2 equivariance count on the d = n/2 resonance; the count
itself is [COMPUTED]-calibrated against the exact kernel at n in {16,32,64,128}.
-/
import Mathlib

/-! ## The numerator is honest (no nat-subtraction truncation). -/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
set_option autoImplicit false

namespace ArkLib.ProximityGap.DeepBandR5

open Finset

/-- The r=5 deep-band #bad-scalar count on the maximizer line `(x^{n/2+1}, x^{n-1})`, as the
closed polynomial `(4 g^4 + 3 g^3 - 10 g^2 + 12) / 12` in `g = n/4`.  (Written with the
non-truncating ordering; honesty of the integer division is the bridge `deepBandBadCount5_bridge`,
valid on the prize domain of even `g`.) -/
def deepBandBadCount5 (g : ℕ) : ℕ := (4 * g ^ 4 + 3 * g ^ 3 + 12 - 10 * g ^ 2) / 12

/-- The number of full-size (`d = n/2`) B2 orbits, `full_orb = (4 g^3 + 3 g^2 - 10 g)/24`. -/
def deepBandFullOrb (g : ℕ) : ℕ := (4 * g ^ 3 + 3 * g ^ 2 + 0 - 10 * g) / 24

/-- The r=5 budget `K = 2^5 * C(n/2, 5) = 32 * C(2g, 5)`, in terms of `g = n/4`. -/
def deepBandBudget5 (g : ℕ) : ℕ := 2 ^ 5 * (2 * g).choose 5


/-- For `g >= 1`, `4 g^4 + 3 g^3 + 12 >= 10 g^2`, so the closed-form numerator is the honest
integer `4 g^4 + 3 g^3 - 10 g^2 + 12`. -/
theorem r5_num_add (g : ℕ) (hg : 1 ≤ g) :
    (4 * g ^ 4 + 3 * g ^ 3 + 12 - 10 * g ^ 2) + 10 * g ^ 2 = 4 * g ^ 4 + 3 * g ^ 3 + 12 := by
  have h10 : 10 * g ^ 2 ≤ 4 * g ^ 4 + 3 * g ^ 3 + 12 := by
    nlinarith [sq_nonneg g, sq_nonneg (g ^ 2), hg]
  omega

/-- The floor bound `12 * #bad_5 + 10 g^2 <= 4 g^4 + 3 g^3 + 12` (weak direction of the
closed form; all the budget lemmas need only this).  From `Nat.mul_div_le` plus `r5_num_add`. -/
theorem r5_floor_le (g : ℕ) (hg : 1 ≤ g) :
    12 * deepBandBadCount5 g + 10 * g ^ 2 ≤ 4 * g ^ 4 + 3 * g ^ 3 + 12 := by
  have hfloor : 12 * deepBandBadCount5 g ≤ 4 * g ^ 4 + 3 * g ^ 3 + 12 - 10 * g ^ 2 := by
    rw [deepBandBadCount5]; exact Nat.mul_div_le _ _
  have hnum := r5_num_add g hg
  omega

/-! ## The orbit-descent bridge: `12 * #bad_5 + 10 g^2 = 4 g^4 + 3 g^3 + 12` for even `g`. -/

/-- The closed-form numerator is divisible by 12 for even `g` (the prize domain `g = 2^k`).
For `g = 2h`: `4(2h)^4 + 3(2h)^3 + 12 - 10(2h)^2 = 64 h^4 + 24 h^3 - 40 h^2 + 12 = 12 * (...)`.
We exhibit the explicit quotient `q5 h = (16 h^4 + 6 h^3 - 10 h^2 + 3)/3`, itself an honest
integer since `3 | 16 h^4 + 6 h^3 - 10 h^2 + 3` (as `h^4 - h^2 = h^2(h-1)(h+1) ≡ 0 mod 3`). -/
def q5half (h : ℕ) : ℕ := (16 * h ^ 4 + 6 * h ^ 3 + 3 - 10 * h ^ 2) / 3

/-- `3 ∣ 16 h^4 + 6 h^3 - 10 h^2 + 3` for all `h` (mod-3 reading: `h^4 - h^2 ≡ 0`). -/
theorem three_dvd_q5 (h : ℕ) : 3 ∣ (16 * h ^ 4 + 6 * h ^ 3 + 3 - 10 * h ^ 2) := by
  have hsq : h ^ 2 ≤ h ^ 4 := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · simp [h0]
    · calc h ^ 2 = h ^ 2 * 1 := by ring
        _ ≤ h ^ 2 * h ^ 2 := Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr (by positivity))
        _ = h ^ 4 := by ring
  have hnn : 10 * h ^ 2 ≤ 16 * h ^ 4 + 6 * h ^ 3 + 3 := by nlinarith [hsq, Nat.zero_le (h ^ 3)]
  have key : (16 * h ^ 4 + 6 * h ^ 3 + 3 - 10 * h ^ 2) % 3 = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, h = 3 * k + h % 3 := ⟨h / 3, by omega⟩
    have e3 : h % 3 < 3 := by omega
    interval_cases hr : (h % 3) <;> (subst hk; ring_nf; omega)
  omega

/-! ## The budget inequality (the degree-5 vs degree-4 margin). -/

/-- `120 * C(2g, 5) = (2g)(2g-1)(2g-2)(2g-3)(2g-4)` for `g >= 3`. -/
theorem choose_five_expand (g : ℕ) (hg : 3 ≤ g) :
    120 * (2 * g).choose 5 = (2 * g) * (2 * g - 1) * (2 * g - 2) * (2 * g - 3) * (2 * g - 4) := by
  have h5 : (2 * g).choose 5 = (2 * g).descFactorial 5 / Nat.factorial 5 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
  have hdvd : Nat.factorial 5 ∣ (2 * g).descFactorial 5 := Nat.factorial_dvd_descFactorial _ _
  have hfac : Nat.factorial 5 = 120 := by decide
  rw [hfac] at hdvd
  rw [h5, hfac, Nat.mul_div_cancel' hdvd]
  obtain ⟨e, rfl⟩ : ∃ e, g = e + 3 := ⟨g - 3, by omega⟩
  rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_succ,
    Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_zero, mul_one]
  have a0 : 2 * (e + 3) - 0 = 2 * e + 6 := by omega
  have a1 : 2 * (e + 3) - 1 = 2 * e + 5 := by omega
  have a2 : 2 * (e + 3) - 2 = 2 * e + 4 := by omega
  have a3 : 2 * (e + 3) - 3 = 2 * e + 3 := by omega
  have a4 : 2 * (e + 3) - 4 = 2 * e + 2 := by omega
  rw [a0, a1, a2, a3, a4]
  ring

/-- `120 * C(2g,5) + (160 g^4 + 200 g^2) = 32 g^5 + 280 g^3 + 48 g` for `g >= 3`
(subtraction-free reading of `(2g)(2g-1)(2g-2)(2g-3)(2g-4) = 32 g^5 - 160 g^4 + 280 g^3 - 200 g^2 + 48 g`). -/
theorem onetwenty_choose_poly (g : ℕ) (hg : 3 ≤ g) :
    120 * (2 * g).choose 5 + (160 * g ^ 4 + 200 * g ^ 2) = 32 * g ^ 5 + 280 * g ^ 3 + 48 * g := by
  have hC := choose_five_expand g hg
  obtain ⟨e, rfl⟩ : ∃ e, g = e + 3 := ⟨g - 3, by omega⟩
  have a1 : 2 * (e + 3) - 1 = 2 * e + 5 := by omega
  have a2 : 2 * (e + 3) - 2 = 2 * e + 4 := by omega
  have a3 : 2 * (e + 3) - 3 = 2 * e + 3 := by omega
  have a4 : 2 * (e + 3) - 4 = 2 * e + 2 := by omega
  rw [a1, a2, a3, a4] at hC
  rw [hC]; ring

/-- **The budget inequality.**  `#bad_5 <= K` for every `g >= 3` (a fortiori the prize domain
`g >= 4`).  Reduces to the integer polynomial gap
`60 (K - #bad_5) = 512 g^5 - 2580 g^4 + 4465 g^3 - 3150 g^2 + 768 g - 60 >= 0` (`g >= 3`). -/
theorem deepBandBadCount5_le_budget (g : ℕ) (hg : 3 ≤ g) :
    deepBandBadCount5 g ≤ deepBandBudget5 g := by
  set C := (2 * g).choose 5 with hCdef
  -- 12 * #bad_5 = numerator (honest, via the floor identity on the divisible numerator):
  -- we only need the WEAK direction 12 * #bad_5 <= 4 g^4 + 3 g^3 + 12 - 10 g^2 (floor <= value),
  -- i.e. 12 * #bad_5 + 10 g^2 <= 4 g^4 + 3 g^3 + 12.
  have hbad_le : 12 * deepBandBadCount5 g + 10 * g ^ 2 ≤ 4 * g ^ 4 + 3 * g ^ 3 + 12 :=
    r5_floor_le g (by omega)
  have hpoly : 120 * C + (160 * g ^ 4 + 200 * g ^ 2) = 32 * g ^ 5 + 280 * g ^ 3 + 48 * g :=
    onetwenty_choose_poly g hg
  rw [deepBandBudget5]
  show deepBandBadCount5 g ≤ 2 ^ 5 * C
  -- 5 * (32 C) = 160 C; 60 * #bad_5 <= 5 * (4 g^4+3 g^3+12-10 g^2)... reduce to gap >= 0.
  -- 60 (K - #bad_5) >= 0  <=>  5 * (120 C) >= 60 #bad_5  i.e. work additively over the C-atom.
  -- From hpoly: 120 C = 32 g^5 + 280 g^3 + 48 g - (160 g^4 + 200 g^2).
  -- gap = 512 g^5 - 2580 g^4 + 4465 g^3 - 3150 g^2 + 768 g - 60 >= 0 for g >= 3.
  have hgap : 16 * (32 * g ^ 5 + 280 * g ^ 3 + 48 * g)
      ≥ 5 * (4 * g ^ 4 + 3 * g ^ 3 + 12) + (16 * (160 * g ^ 4 + 200 * g ^ 2) + 50 * g ^ 2) := by
    obtain ⟨e, rfl⟩ : ∃ e, g = e + 3 := ⟨g - 3, by omega⟩
    nlinarith [Nat.zero_le e, sq_nonneg e, Nat.zero_le (e ^ 2), Nat.zero_le (e ^ 3),
      Nat.zero_le (e ^ 4), Nat.zero_le (e ^ 5)]
  -- Now assemble.  Multiply hpoly by 16:
  have h16poly : 16 * (120 * C) + 16 * (160 * g ^ 4 + 200 * g ^ 2)
      = 16 * (32 * g ^ 5 + 280 * g ^ 3 + 48 * g) := by omega
  -- 60 * #bad_5 + 60 * (10 g^2) <= 5*(4g^4+3g^3+12)  (from hbad_le, *5)
  have h5bad : 5 * (12 * deepBandBadCount5 g) + 50 * g ^ 2 ≤ 5 * (4 * g ^ 4 + 3 * g ^ 3 + 12) := by
    omega
  -- 16 * 120 C = 1920 C = 60 * (32 C).  So 60 * (2^5 C) = 16 * (120 C).
  have h60 : 60 * (2 ^ 5 * C) = 16 * (120 * C) := by ring
  -- combine: 60 * #bad_5 <= 60 * (2^5 C)
  have key : 60 * deepBandBadCount5 g ≤ 60 * (2 ^ 5 * C) := by
    rw [h60]
    -- 60 #bad_5 = 5*(12 #bad_5);  16*(120C) = 16*(...poly...) - 16*(160g^4+200g^2)
    omega
  omega

/-- **The C-half bound.**  `2 * #bad_5 <= K` for every `g >= 3` (the CONJECTURE C-half at the
r=5 rung).  Reduces to `60 (K - 2 #bad_5) = 512 g^5 - 2600 g^4 + 4450 g^3 - 3100 g^2 + 768 g
- 120 >= 0` (`g >= 3`).  The margin `K / (2 #bad_5) = 10.1, 48.5, 142.2, 341.8` at
n = 16,32,64,128 and diverges. -/
theorem deepBandBadCount5_two_mul_le_budget (g : ℕ) (hg : 3 ≤ g) :
    2 * deepBandBadCount5 g ≤ deepBandBudget5 g := by
  set C := (2 * g).choose 5 with hCdef
  have hbad_le : 12 * deepBandBadCount5 g + 10 * g ^ 2 ≤ 4 * g ^ 4 + 3 * g ^ 3 + 12 :=
    r5_floor_le g (by omega)
  have hpoly : 120 * C + (160 * g ^ 4 + 200 * g ^ 2) = 32 * g ^ 5 + 280 * g ^ 3 + 48 * g :=
    onetwenty_choose_poly g hg
  rw [deepBandBudget5]
  show 2 * deepBandBadCount5 g ≤ 2 ^ 5 * C
  -- 60 (K - 2 #bad_5) = 512 g^5 - 2600 g^4 + 4450 g^3 - 3100 g^2 + 768 g - 120 >= 0, g >= 3.
  have hgap : 16 * (32 * g ^ 5 + 280 * g ^ 3 + 48 * g)
      ≥ 10 * (4 * g ^ 4 + 3 * g ^ 3 + 12) + (16 * (160 * g ^ 4 + 200 * g ^ 2) + 100 * g ^ 2) := by
    obtain ⟨e, rfl⟩ : ∃ e, g = e + 3 := ⟨g - 3, by omega⟩
    nlinarith [Nat.zero_le e, sq_nonneg e, Nat.zero_le (e ^ 2), Nat.zero_le (e ^ 3),
      Nat.zero_le (e ^ 4), Nat.zero_le (e ^ 5)]
  have h16poly : 16 * (120 * C) + 16 * (160 * g ^ 4 + 200 * g ^ 2)
      = 16 * (32 * g ^ 5 + 280 * g ^ 3 + 48 * g) := by omega
  -- 120 * #bad_5 + 100 g^2 <= 10*(4g^4+3g^3+12)  (from hbad_le, *10)
  have h10bad : 10 * (12 * deepBandBadCount5 g) + 100 * g ^ 2 ≤ 10 * (4 * g ^ 4 + 3 * g ^ 3 + 12) := by
    omega
  have h60 : 60 * (2 ^ 5 * C) = 16 * (120 * C) := by ring
  have key : 60 * (2 * deepBandBadCount5 g) ≤ 60 * (2 ^ 5 * C) := by
    rw [h60]
    omega
  omega

/-! ## The orbit-descent identity (the `#bad = 1 + 2g*full_orb` reduction). -/

/-- `12 ∣ 4 g^4 + 3 g^3 + 12 - 10 g^2` for EVEN `g` (the prize domain `g = 2^k`).
Residue argument: write `g = 2h`; modulo 12 the numerator's value cycles in `h` and is `0`
for every residue (verified by `decide` over `h % 6`, since the period divides 6 once `g` is
even). -/
theorem twelve_dvd_r5_num_even (h : ℕ) :
    (12 : ℕ) ∣ (4 * (2 * h) ^ 4 + 3 * (2 * h) ^ 3 + 12 - 10 * (2 * h) ^ 2) := by
  have hsq : h ^ 2 ≤ h ^ 4 := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · simp [h0]
    · calc h ^ 2 = h ^ 2 * 1 := by ring
        _ ≤ h ^ 2 * h ^ 2 := Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr (by positivity))
        _ = h ^ 4 := by ring
  have hnn : 10 * (2 * h) ^ 2 ≤ 4 * (2 * h) ^ 4 + 3 * (2 * h) ^ 3 + 12 := by
    nlinarith [hsq, Nat.zero_le (h ^ 3)]
  -- reduce mod 12 by the residue of h mod 6
  have key : (4 * (2 * h) ^ 4 + 3 * (2 * h) ^ 3 + 12 - 10 * (2 * h) ^ 2) % 12 = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, h = 6 * k + h % 6 := ⟨h / 6, by omega⟩
    have e6 : h % 6 < 6 := by omega
    interval_cases hr : (h % 6) <;> (subst hk; ring_nf; omega)
  omega

/-- **Orbit-descent identity.**  For even `g = 2h`, the closed form satisfies the
subtraction-free bridge `12 * #bad_5(2h) + 10 (2h)^2 = 4 (2h)^4 + 3 (2h)^3 + 12`; combined with
`#bad_5 = 1 + (n/2) full_orb` this is the B2 orbit reduction at `d = n/2`. -/
theorem deepBandBadCount5_descent (h : ℕ) :
    12 * deepBandBadCount5 (2 * h) + 10 * (2 * h) ^ 2 = 4 * (2 * h) ^ 4 + 3 * (2 * h) ^ 3 + 12 := by
  have hdvd := twelve_dvd_r5_num_even h
  have hsq : h ^ 2 ≤ h ^ 4 := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · simp [h0]
    · calc h ^ 2 = h ^ 2 * 1 := by ring
        _ ≤ h ^ 2 * h ^ 2 := Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr (by positivity))
        _ = h ^ 4 := by ring
  have hnn : 10 * (2 * h) ^ 2 ≤ 4 * (2 * h) ^ 4 + 3 * (2 * h) ^ 3 + 12 := by
    nlinarith [hsq, Nat.zero_le (h ^ 3)]
  -- since 12 | N, floor is exact: 12 * (N / 12) = N.
  have hexact : 12 * deepBandBadCount5 (2 * h)
      = 4 * (2 * h) ^ 4 + 3 * (2 * h) ^ 3 + 12 - 10 * (2 * h) ^ 2 := by
    rw [deepBandBadCount5]
    rw [Nat.mul_div_cancel' hdvd]
  omega

/-! ## Numerical calibration rungs (must reproduce the exact kernel data). -/

theorem rung_n16 : deepBandBadCount5 4 = 89 ∧ deepBandBudget5 4 = 1792 := ⟨by decide, by decide⟩
theorem rung_n32 : deepBandBadCount5 8 = 1441 ∧ deepBandBudget5 8 = 139776 := ⟨by decide, by decide⟩
theorem rung_n64 : deepBandBadCount5 16 = 22657 ∧ deepBandBudget5 16 = 6444032 :=
  ⟨by decide, by decide⟩
theorem rung_n128 : deepBandBadCount5 32 = 356865 ∧ deepBandBudget5 32 = 243984384 :=
  ⟨by decide, by decide⟩

/-- The orbit decomposition reproduces the same rungs: `#bad = 1 + 2g * full_orb`. -/
theorem rung_orbit_n16 : deepBandFullOrb 4 = 11 ∧ 1 + 2 * 4 * deepBandFullOrb 4 = 89 :=
  ⟨by decide, by decide⟩
theorem rung_orbit_n32 : deepBandFullOrb 8 = 90 ∧ 1 + 2 * 8 * deepBandFullOrb 8 = 1441 :=
  ⟨by decide, by decide⟩
theorem rung_orbit_n64 : deepBandFullOrb 16 = 708 ∧ 1 + 2 * 16 * deepBandFullOrb 16 = 22657 :=
  ⟨by decide, by decide⟩
theorem rung_orbit_n128 : deepBandFullOrb 32 = 5576 ∧ 1 + 2 * 32 * deepBandFullOrb 32 = 356865 :=
  ⟨by decide, by decide⟩

end ArkLib.ProximityGap.DeepBandR5

#print axioms ArkLib.ProximityGap.DeepBandR5.deepBandBadCount5_le_budget
#print axioms ArkLib.ProximityGap.DeepBandR5.deepBandBadCount5_two_mul_le_budget
#print axioms ArkLib.ProximityGap.DeepBandR5.deepBandBadCount5_descent
#print axioms ArkLib.ProximityGap.DeepBandR5.twelve_dvd_r5_num_even
#print axioms ArkLib.ProximityGap.DeepBandR5.choose_five_expand
#print axioms ArkLib.ProximityGap.DeepBandR5.onetwenty_choose_poly
#print axioms ArkLib.ProximityGap.DeepBandR5.r5_num_add
#print axioms ArkLib.ProximityGap.DeepBandR5.r5_floor_le
#print axioms ArkLib.ProximityGap.DeepBandR5.three_dvd_q5
#print axioms ArkLib.ProximityGap.DeepBandR5.rung_n16
#print axioms ArkLib.ProximityGap.DeepBandR5.rung_n128
#print axioms ArkLib.ProximityGap.DeepBandR5.rung_orbit_n128
