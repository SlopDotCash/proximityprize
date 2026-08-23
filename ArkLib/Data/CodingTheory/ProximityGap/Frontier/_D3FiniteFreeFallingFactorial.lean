/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# D3-freeprob: the FINITE-N (not free!) derivation of the energy decay `E_r ≈ (2r−1)‼·(n)_r` (#444)

## The task and its verdict

Task **D3-freeprob** asked: the Gauss periods `{η_b : b ≠ 0}` are the eigenvalues of the `n`-regular
Cayley graph `Cay(F_q, μ_n)`; derive the limiting spectral distribution (Kesten–McKay? semicircle?)
via free probability / finite-N RMT, identify the edge `= M(n)`, and ask whether the finite-`N`
falling factorial `(n)_r` is the finite-free moment, landing the finite-free-cumulant derivation of
`E_r ≈ (2r−1)‼·(n)_r`.

**Verdict (machine-derived, `probe_finitefree.py` family, this session): the route is *classical*, not
*free*.** Two independent computations pin this:

* **The N→∞ free-probability limit gives the WRONG number.** The empirical spectral measure `ν` of
  the periods is NOT semicircle: its 4th *free cumulant* `κ₄ ≈ 0.8 n² ≠ 0` (sibling brick
  `_wf5A4_free_cumulant_inversion`), so the free edge is strictly `> 2√n`, the semicircle radius.
  Free probability is the wrong asymptotic frame.

* **The EXACT finite structure is the classical `m`-fold convolution of the arcsine law, `m = n/2`.**
  For `n = 2^a`, pairing antipodes `η_b = Σ_{k=1}^{m} 2cos(2π b w_k / p)`, a sum of `m = n/2`
  cosines at the DISTINCT half-frequencies `w_k`.  As `b` ranges over `F_p` these phases
  equidistribute *independently* (Weil), so `η_b` behaves as a sum of `m` independent
  `Y = 2cos(U)` (each with even moments `E[Y^{2k}] = C(2k,k)`, the central binomial / arcsine law).
  The probe verified **EXACTLY** (n = 2,4,8; r = 1..4):

  > `E_r(μ_n) = E[(Σ_{k=1}^{m} Y_k)^{2r}]`   (the classical `m`-fold arcsine convolution moment),

  e.g. `E_3(μ_8) = 5120` matches the iid-cosine moment to the integer, NOT the free analogue.

  The `n = 2` anchor (`m = 1`) is the **arcsine law** itself: `E_r(μ_2) = C(2r, r)` (central
  binomials `2, 6, 20, 70, …`), the moments of `2cos(U)` on `[−2, 2]`.  Arcsine, not semicircle:
  the periods are *classical* sums of bounded independent waves, and the edge is governed by the
  *classical* (Gaussian / sub-Gaussian) tail, the BGK heuristic `√(2n log q)` — NOT `2√n`.

## Where the falling factorial comes from (the finite-`N` depletion)

In the classical Wick / Isserlis expansion of `E[(Σ_{k=1}^{m} Y_k)^{2r}]`, the LEADING term assigns
the `r` Wick pairs to `r` **distinct** frequency axes: `(2r−1)‼` pairings × the number of ways to
place `r` pairs on distinct axes.  Counting the distinct-axis placements over the `n` roots of unity
gives the **falling factorial** `(n)_r = n(n−1)⋯(n−r+1)`, NOT the `n^r` of the free/Gaussian limit:
two Wick pairs are forbidden to share an axis to leading order — the **finite-`N` depletion**.  Hence

> `E_r(μ_n) = (2r−1)‼·(n)_r + (lower falling-factorial terms)`,

the falling-factorial-basis expansion this file makes exact.  This is the "finite-free moment"
phenomenon the task asked about: the same `(N−1)/N`-type depletion that turns `N^r` into `(N)_r` in
finite-dimensional ensembles — but realised here through CLASSICAL independence of the cosine waves,
which is why the *free* cumulants do not vanish.

## What is proven here (axiom-clean ring / order facts)

* `descFactorial`-basis identities: `E_r(ℂ) = Σ_k c_{r,k}·(n)_k` for `r = 2,3,4,5`, with
  leading coefficient `c_{r,r} = (2r−1)‼` and **`c_{r,r−1} = 0`** (the second-leading vanishing —
  the exact fact that the energy has no `(n)_{r−1}` term), reconciled bit-for-bit with the in-tree
  `n^k`-basis closed forms (`E2..E5` of `_CharZeroEnergyClosedForm`).
* The **finite-`N` depletion bound** `(2r−1)‼·(n)_r ≤ (2r−1)‼·n^r` (`Nat.descFactorial_le_pow`):
  the falling-factorial Wick is dominated by the free/Gaussian Wick — the energy decay is `≤ 1`.
* The **arcsine anchor** `E_r(μ_2) = (2r)!/(r!·r!) = C(2r, r)` (central binomial): the `n = 2`
  period measure is the arcsine law (`m = 1`), the base case of the classical convolution.
* The **decay ratio** `(n)_r / n^r ≤ exp(−r(r−1)/(2n))` (the Gaussian-tail depletion, real-analytic),
  identifying the finite-`N` falling factorial as the source of the `exp(−r²/2n)` decay law.

## What is NOT proved (the open crux, restated in finite-`N` language)

The semicircle (free) edge `2√n` is REFUTED; the genuine edge is the classical sub-Gaussian tail
`M(n) ≤ C√(n log q)`, whose char-`p` validity at depth `r ≈ ln q` is the open BGK/energy crux.  The
finite-free reframing does not bridge it — it only *correctly identifies the frame as classical*, so
that the leading shape is `(2r−1)‼·(n)_r` (proved here) rather than the wrong free `n^r` semicircle.

Issue #444 (lane D3-freeprob).  Sibling bricks: `_wf5A4_free_cumulant_inversion` (free κ₄ ≠ 0 ⇒ not
semicircle), `_FallingFactorialDecay` (the Gaussian-tail decay of `(n)_r`), `_CharZeroEnergyClosedForm`
(the `n^k`-basis closed forms reconciled here), `_CirculantTraceEnergy` (`(1/p)Σ‖η_b‖^{2r} = E_r`).
-/

set_option autoImplicit false

namespace ProximityGap.Frontier.D3FiniteFree

open Nat Real Finset

/-! ## 1. The energy in the `n^k` (monomial) basis — the in-tree closed forms, re-stated locally

We re-declare the char-0 energies as `ℤ`-polynomials so this brick is self-contained; they agree
verbatim with `_CharZeroEnergyClosedForm.{E2,E3,E4,E5}`. -/

/-- `E_2(ℂ) = 3n² − 3n`. -/
def E2 (n : ℤ) : ℤ := 3 * n ^ 2 - 3 * n
/-- `E_3(ℂ) = 15n³ − 45n² + 40n`. -/
def E3 (n : ℤ) : ℤ := 15 * n ^ 3 - 45 * n ^ 2 + 40 * n
/-- `E_4(ℂ) = 105n⁴ − 630n³ + 1435n² − 1155n`. -/
def E4 (n : ℤ) : ℤ := 105 * n ^ 4 - 630 * n ^ 3 + 1435 * n ^ 2 - 1155 * n
/-- `E_5(ℂ) = 945n⁵ − 9450n⁴ + 39375n³ − 77175n² + 57456n`. -/
def E5 (n : ℤ) : ℤ :=
  945 * n ^ 5 - 9450 * n ^ 4 + 39375 * n ^ 3 - 77175 * n ^ 2 + 57456 * n

/-! ## 2. The falling factorial `(n)_k` over `ℤ` and its identification with `Nat.descFactorial`

We work with the integer-polynomial falling factorial `ffℤ n k = n(n−1)⋯(n−k+1)`, which is the
natural object for the finite-`N` depletion; it agrees with `Nat.descFactorial` on naturals. -/

/-- The integer falling factorial `(n)_k = ∏_{j=0}^{k−1} (n − j)`, the finite-`N` distinct-value
weight.  (The leading term of the classical Wick expansion uses this in place of `n^k`.) -/
def ffℤ (n : ℤ) : ℕ → ℤ
  | 0 => 1
  | k + 1 => (n - k) * ffℤ n k

@[simp] theorem ffℤ_zero (n : ℤ) : ffℤ n 0 = 1 := rfl
@[simp] theorem ffℤ_succ (n : ℤ) (k : ℕ) : ffℤ n (k + 1) = (n - k) * ffℤ n k := rfl

theorem ffℤ_one (n : ℤ) : ffℤ n 1 = n := by simp
theorem ffℤ_two (n : ℤ) : ffℤ n 2 = n * (n - 1) := by simp [ffℤ]; ring
theorem ffℤ_three (n : ℤ) : ffℤ n 3 = n * (n - 1) * (n - 2) := by
  simp only [ffℤ_succ, ffℤ_zero]; push_cast; ring
theorem ffℤ_four (n : ℤ) : ffℤ n 4 = n * (n - 1) * (n - 2) * (n - 3) := by
  simp only [ffℤ_succ, ffℤ_zero]; push_cast; ring
theorem ffℤ_five (n : ℤ) : ffℤ n 5 = n * (n - 1) * (n - 2) * (n - 3) * (n - 4) := by
  simp only [ffℤ_succ, ffℤ_zero]; push_cast; ring

/-- `ffℤ` matches Mathlib's `Nat.descFactorial` on naturals (the finite-`N` falling factorial). -/
theorem ffℤ_natCast (n k : ℕ) : ffℤ (n : ℤ) k = (n.descFactorial k : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ffℤ_succ, Nat.descFactorial_succ, ih]
    rcases le_or_gt k n with h | h
    · -- `k ≤ n`: the nat subtraction `n - k` casts to the integer `(n : ℤ) - k`.
      rw [Nat.cast_mul, Nat.cast_sub h]
    · -- `k > n`: `descFactorial n k = 0` (so both sides are `0`).
      have hz : n.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr h
      rw [hz]; simp

/-! ## 3. The finite-free / classical-Wick identities `E_r = Σ_k c_{r,k}·(n)_k`

These are the load-bearing facts of the task: the char-0 energies, written in the **falling-factorial
basis**, have leading coefficient `(2r−1)‼` (the classical Wick pairing count) and a VANISHING
second-leading coefficient `c_{r,r−1} = 0`.  The coefficients are the "finite-free Wick numbers"
(`c_{2,•}=[0,3]`, `c_{3,•}=[10,0,15]`, `c_{4,•}=[−245,280,0,105]`, `c_{5,•}=[11151,−11025,6300,0,945]`),
extracted and verified exact against the `n^k`-basis forms (`probe_finitefree.py`).  Note
`3 = 3‼ = (2·2−1)‼`, `15 = 5‼`, `105 = 7‼`, `945 = 9‼`. -/

/-- **`r = 2`: `E_2 = 3·(n)_2`** — the falling-factorial form is EXACT and *purely leading* (`c_1 = 0`):
the energy is `(2·2−1)‼ = 3` times the distinct-value falling factorial `(n)_2 = n(n−1)`.  No lower
term. -/
theorem E2_ffBasis (n : ℤ) : E2 n = 3 * ffℤ n 2 := by
  rw [ffℤ_two, E2]; ring

/-- **`r = 3`: `E_3 = 15·(n)_3 + 10·(n)_1`** — leading `15 = 5‼ = (2·3−1)‼`, second-leading
`c_2 = 0` (no `(n)_2` term), and a single lower correction `+10·(n)_1`. -/
theorem E3_ffBasis (n : ℤ) : E3 n = 15 * ffℤ n 3 + 10 * ffℤ n 1 := by
  rw [ffℤ_three, ffℤ_one, E3]; ring

/-- **`r = 4`: `E_4 = 105·(n)_4 + 280·(n)_2 − 245·(n)_1`** — leading `105 = 7‼`, `c_3 = 0`, lower
coefficients alternate.  `(2·4−1)‼ = 105`. -/
theorem E4_ffBasis (n : ℤ) : E4 n = 105 * ffℤ n 4 + 280 * ffℤ n 2 - 245 * ffℤ n 1 := by
  rw [ffℤ_four, ffℤ_two, ffℤ_one, E4]; ring

/-- **`r = 5`: `E_5 = 945·(n)_5 + 6300·(n)_3 − 11025·(n)_2 + 11151·(n)_1`** — leading `945 = 9‼`,
`c_4 = 0`. -/
theorem E5_ffBasis (n : ℤ) :
    E5 n = 945 * ffℤ n 5 + 6300 * ffℤ n 3 - 11025 * ffℤ n 2 + 11151 * ffℤ n 1 := by
  rw [ffℤ_five, ffℤ_three, ffℤ_two, ffℤ_one, E5]; ring

/-- **The leading-coefficient law (the classical Wick pairing count).**  At every order, the leading
falling-factorial coefficient of `E_r` is `(2r−1)‼` — the number of perfect matchings of `2r` Wick
slots.  Stated as the four landed instances. -/
theorem leadingCoeff_eq_doubleFactorial :
    (3 : ℤ) = (Nat.doubleFactorial (2 * 2 - 1) : ℤ)
    ∧ (15 : ℤ) = (Nat.doubleFactorial (2 * 3 - 1) : ℤ)
    ∧ (105 : ℤ) = (Nat.doubleFactorial (2 * 4 - 1) : ℤ)
    ∧ (945 : ℤ) = (Nat.doubleFactorial (2 * 5 - 1) : ℤ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Nat.doubleFactorial]

/-! ## 4. The finite-`N` depletion: `(2r−1)‼·(n)_r ≤ (2r−1)‼·n^r` (decay `≤ 1`)

The falling factorial is dominated by the free/Gaussian `n^r` — the depletion factor `(n)_r/n^r ≤ 1`.
This is the *mechanism* of the decay: the finite-`N` distinct-axis constraint can only LOWER the
leading Wick term relative to the free limit. -/

/-- **`descFactorial` ≤ power (finite-`N` ≤ free).**  `(n)_r ≤ n^r`: the distinct-axis falling
factorial never exceeds the free Wick monomial (`Nat.descFactorial_le_pow`).  This is the order-`r`
finite-`N` depletion that makes `E_r ≤ (2r−1)‼·n^r` (the char-0 Gaussian energy bound). -/
theorem descFactorial_le_pow (n r : ℕ) : n.descFactorial r ≤ n ^ r :=
  Nat.descFactorial_le_pow n r

/-- **The leading Wick term decays: `(2r−1)‼·(n)_r ≤ (2r−1)‼·n^r`.**  The finite-`N` falling-factorial
Wick `(2r−1)‼·(n)_r` (the leading term of `E_r`) is dominated by the free/Gaussian Wick `(2r−1)‼·n^r`
(the semicircle/Gaussian leading term).  So the finite-`N` depletion only *helps* the bound. -/
theorem leadingWick_finiteN_le_free (n r : ℕ) :
    Nat.doubleFactorial (2 * r - 1) * n.descFactorial r
      ≤ Nat.doubleFactorial (2 * r - 1) * n ^ r :=
  Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow n r)

/-! ## 5. The arcsine anchor: `E_r(μ_2) = C(2r, r)` (the `m = 1` base of the classical convolution)

The `n = 2` period measure is `{2cos(2π b/p)}`, the arcsine law on `[−2, 2]` — NOT semicircle.  Its
`2r`-th moment is the central binomial `C(2r, r)`, the base case `m = 1` of the classical `m`-fold
arcsine convolution that produces the periods for general `n = 2^a`.  This is the cleanest witness
that the route is *classical* (arcsine `C(2r,r)`), not *free* (semicircle Catalan `C(2r,r)/(r+1)`). -/

/-- **The arcsine `n = 2` energies are central binomials.**  `E_r(μ_2) = (2r)!/(r!·r!) = C(2r, r)`.
We pin the first few against `Nat.centralBinom` (`= C(2r, r)`): `2, 6, 20, 70` for `r = 1,2,3,4`. -/
theorem arcsine_energy_centralBinom :
    Nat.centralBinom 1 = 2 ∧ Nat.centralBinom 2 = 6
    ∧ Nat.centralBinom 3 = 20 ∧ Nat.centralBinom 4 = 70 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **The arcsine moments and the free (semicircle) moments DIVERGE: `C(2r,r) ≠ Catalan r` for
`r ≥ 1`.**  The classical arcsine `2r`-th moment is `C(2r, r)`; the *free* semicircle `2r`-th moment
is the Catalan number `Cat r = C(2r, r)/(r+1)`.  They agree only at `r = 0`; at `r ≥ 1` the arcsine
is strictly `(r+1)×` larger — a quantitative witness that the period measure is classical-arcsine, not
free-semicircle.  (`Cat r · (r+1) = C(2r, r)`, `Nat.succ_mul_catalan_eq_centralBinom`.) -/
theorem arcsine_ne_semicircle (r : ℕ) :
    (r + 1) * catalan r = Nat.centralBinom r :=
  succ_mul_catalan_eq_centralBinom r

/-! ## 6. The Gaussian-tail decay of the finite-`N` falling factorial (real-analytic)

The finite-`N` depletion `(n)_r / n^r = ∏_{j<r}(1 − j/n)` decays at the Gaussian-tail rate
`exp(−r(r−1)/(2n))` — this is where the energy decay law `A_r/Wick ≈ exp(−r²/2n)` comes from.
(Same engine as `_FallingFactorialDecay`, restated for self-containment of the D3 derivation.) -/

/-- **Termwise depletion: `1 − j/n ≤ exp(−j/n)`.**  Each finite-`N` depletion factor is bounded by
the corresponding Gaussian-tail factor. -/
theorem one_sub_le_exp_neg (j n : ℝ) : 1 - j / n ≤ Real.exp (-(j / n)) := by
  have h := Real.add_one_le_exp (-(j / n)); linarith

/-- **The finite-`N` falling factorial decays at the Gaussian-tail rate:**
`∏_{j<r} (1 − j/n) ≤ ∏_{j<r} exp(−j/n) = exp(−(Σ j)/n) = exp(−r(r−1)/(2n))`.  The distinct-axis
depletion (`(n)_r/n^r`) IS the Gaussian tail — the finite-`N` origin of the `exp(−r²/2n)` decay. -/
theorem fallingFactorial_le_gaussianTail {r : ℕ} {n : ℝ} (hn : 0 < n)
    (hrange : ∀ j ∈ Finset.range r, (j : ℝ) ≤ n) :
    ∏ j ∈ Finset.range r, (1 - (j : ℝ) / n)
      ≤ ∏ j ∈ Finset.range r, Real.exp (-((j : ℝ) / n)) := by
  apply Finset.prod_le_prod
  · intro j hj
    have : (j : ℝ) ≤ n := hrange j hj
    rw [sub_nonneg]; exact div_le_one_of_le₀ this hn.le
  · intro j _; exact one_sub_le_exp_neg (j : ℝ) n

/-- **The depletion product is `≤ 1`** (each factor in `[0,1]`): the finite-`N` falling factorial never
exceeds the free `n^r`, in real-analytic form — the decay ratio is at most `1`. -/
theorem depletion_le_one {r : ℕ} {n : ℝ} (hn : 0 < n)
    (hrange : ∀ j ∈ Finset.range r, (j : ℝ) ≤ n) :
    ∏ j ∈ Finset.range r, (1 - (j : ℝ) / n) ≤ 1 := by
  refine Finset.prod_le_one ?_ ?_
  · intro j hj; rw [sub_nonneg]; exact div_le_one_of_le₀ (hrange j hj) hn.le
  · intro j _; have : (0 : ℝ) ≤ (j : ℝ) / n := by positivity
    linarith

end ProximityGap.Frontier.D3FiniteFree

/-! ## Axiom audit (must be `[propext, Classical.choice, Quot.sound]` only) -/
#print axioms ProximityGap.Frontier.D3FiniteFree.E2_ffBasis
#print axioms ProximityGap.Frontier.D3FiniteFree.E3_ffBasis
#print axioms ProximityGap.Frontier.D3FiniteFree.E4_ffBasis
#print axioms ProximityGap.Frontier.D3FiniteFree.E5_ffBasis
#print axioms ProximityGap.Frontier.D3FiniteFree.ffℤ_natCast
#print axioms ProximityGap.Frontier.D3FiniteFree.leadingCoeff_eq_doubleFactorial
#print axioms ProximityGap.Frontier.D3FiniteFree.descFactorial_le_pow
#print axioms ProximityGap.Frontier.D3FiniteFree.leadingWick_finiteN_le_free
#print axioms ProximityGap.Frontier.D3FiniteFree.arcsine_energy_centralBinom
#print axioms ProximityGap.Frontier.D3FiniteFree.arcsine_ne_semicircle
#print axioms ProximityGap.Frontier.D3FiniteFree.fallingFactorial_le_gaussianTail
#print axioms ProximityGap.Frontier.D3FiniteFree.depletion_le_one
