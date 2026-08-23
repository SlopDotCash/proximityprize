/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvW0_BesselIdentity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvF1_BesselMfoldSymbolic

/-!
# The symbolic-`d` natConv↔Bessel bridge (R2) (#444, avenue CR / A2-natconv-bessel-bridge)

This brick discharges residual **(R2)** of `_AvF1_BesselMfoldSymbolic`: the bridge

  `natConv negDirCount d (2r) = AvW0.Edef r d`   for **all** `d` (and all `r`),

previously anchored only at `d = 1` (`AvF1.natConv_negDirCount_one`). Together with the symbolic-`m`
induction `AvF1.zeroSumCount_iUnion_eq_natConv` and the central-binomial base, this lands the full
char-0 `m`-fold Bessel identity `Z_r(μ_{2m}) = AvW0.Edef r m` modulo only the single clean
`MutuallyDecoupled` (Lam–Leung) input.

## The mathematics (fully proved here, axiom-clean)

`negDirCount` is the single-direction (antipodal-pair) zero-sum count: `negDirCount (2c) =
centralBinom c = (2c)!/(c!)²` and `negDirCount (odd) = 0`. The EGF-style convolution `natConv`
weights each split by `C(N,a)`. `Edef r d = (2r)! · cpow I0c d r` with `I0c c = 1/(c!)²` and `cpow`
the OGF (unweighted) convolution.

The bridge is the change of normalization EGF↔OGF. By induction on `d`:

* `d = 0`: both sides are `[r = 0]` (the `(2r)!`-factor is `0! = 1` at `r = 0`).
* `d → d+1`: in `natConv negDirCount (d+1) (2r) = Σ_{a≤2r} C(2r,a)·natConv negDirCount d a·
  negDirCount(2r-a)`, every odd-`a` term vanishes (`negDirCount` kills odd arguments). Reindex the
  surviving even `a = 2c`, set `b = r - c`. The pointwise identity
  `C(2r,2c)·(2b)!·(2c)!/(c!)² = (2r)!·(1/(c!)²)` (clearing the central-binomial and the
  binomial coefficient against the `(2·)!` normalizations) turns the EGF sum into `(2r)!` times the
  OGF convolution `Σ_{c≤r} I0c c · cpow I0c d (r-c) = cpow I0c (d+1) r`.

## What this LANDS (axiom-clean)

* `natConv_negDirCount_odd` — `natConv negDirCount d (2r+1) = 0` (kept for the reindex; odd-length
  antipodal-union tuples never sum to `0`).
* `natConv_negDirCount_eq_Edef` — **THE BRIDGE (R2), symbolic `d`**: for all `d r`,
  `(natConv negDirCount d (2r) : ℚ) = AvW0.Edef r d`.
* `bessel_mfold_symbolic_d` — corollary: the `m`-fold zero-sum count of a mutually-decoupled family
  of antipodal directions equals `AvW0.Edef r m` (the full Bessel identity, modulo `MutuallyDecoupled`).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`, no `native_decide`.
-/

set_option linter.style.longLine false
set_option autoImplicit false

open Finset
open scoped Nat

namespace ArkLib.ProximityGap.Frontier.AvCR

open ArkLib.ProximityGap.Frontier.AvF1
open ArkLib.ProximityGap.Frontier.AvW0

/-- `negDirCount` vanishes on odd arguments (an odd-length tuple of antipodal pairs cannot have a
balanced sign-multiset). -/
lemma negDirCount_odd (c : ℕ) : negDirCount (2 * c + 1) = 0 := by
  unfold negDirCount
  have h : (2 * c + 1) % 2 = 1 := by omega
  rw [h]; rfl

/-- `negDirCount` at even argument is the central binomial. -/
lemma negDirCount_two_mul (c : ℕ) : negDirCount (2 * c) = Nat.centralBinom c := by
  unfold negDirCount
  simp [Nat.mul_mod_right, Nat.mul_div_cancel_left c (by norm_num : 0 < 2)]

/-- `natConv negDirCount d` vanishes at every odd index: any union of antipodal-pair directions has
no odd-length zero-sum tuple. By induction on `d`. -/
theorem natConv_negDirCount_odd (d : ℕ) :
    ∀ r : ℕ, natConv negDirCount d (2 * r + 1) = 0 := by
  induction d with
  | zero => intro r; simp [natConv_zero]
  | succ d ih =>
      intro r
      rw [natConv_succ]
      apply Finset.sum_eq_zero
      intro a ha
      rw [Finset.mem_range, Nat.lt_succ_iff] at ha
      -- a and (2r+1 - a) have opposite parities; whichever is odd kills its factor.
      rcases Nat.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩
      · -- a = 2k even ⇒ 2r+1-a = 2(r-k)+1 odd ⇒ negDirCount factor 0
        have hsub : 2 * r + 1 - a = 2 * (r - k) + 1 := by omega
        rw [hsub, negDirCount_odd]; ring
      · -- a = 2k+1 odd ⇒ natConv negDirCount d a = 0 by IH
        have : a = 2 * k + 1 := by omega
        rw [this, ih k]; ring

/-- The central binomial as a rational quotient: `centralBinom k = (2k)!/(k!)²`. -/
lemma centralBinom_rat (k : ℕ) :
    (Nat.centralBinom k : ℚ) = ((2 * k).factorial : ℚ) / ((k.factorial : ℚ) ^ 2) := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  have key : ((2 * k).choose k : ℚ) * (k.factorial : ℚ) * (k.factorial : ℚ)
      = ((2 * k).factorial : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    have hsub : 2 * k - k = k := by omega
    rw [hsub] at h
    have h2 := congrArg (fun n : ℕ => (n : ℚ)) h
    push_cast at h2
    linarith [h2]
  have hkfac : (k.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  linarith [key]

/-- Pointwise normalization identity feeding the bridge step (with `centralBinom` on the `b = r-c`
side and `(2c)!` from the `cpow d` factor): for `c ≤ r`,
`C(2r,2c)·(2c)!·centralBinom(r-c) = (2r)!·I0c(r-c)`. -/
lemma normalization_identity (r c : ℕ) (hc : c ≤ r) :
    ((2 * r).choose (2 * c) : ℚ) * ((2 * c).factorial : ℚ)
        * (Nat.centralBinom (r - c) : ℚ)
      = ((2 * r).factorial : ℚ) * I0c (r - c) := by
  -- (2r choose 2c) * (2c)! * (2(r-c))! = (2r)!
  have hbin : ((2 * r).choose (2 * c) : ℚ) * ((2 * c).factorial : ℚ)
      * ((2 * (r - c)).factorial : ℚ) = ((2 * r).factorial : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show 2 * c ≤ 2 * r by omega)
    have hsub : 2 * r - 2 * c = 2 * (r - c) := by omega
    rw [hsub] at h
    have h2 := congrArg (fun n : ℕ => (n : ℚ)) h
    push_cast at h2
    linarith [h2]
  rw [centralBinom_rat (r - c)]
  unfold I0c
  have hfac : ((r - c).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  field_simp at hbin
  nlinarith [hbin]

/-- **THE BRIDGE (R2), symbolic `d`.** For all `d` and `r`, the integer `d`-fold convolution of the
single-direction central-binomial count equals the `_AvW0` Bessel model value
`Edef r d = (2r)!·[x^{2r}] I₀(2x)^d`. This generalizes `AvF1.natConv_negDirCount_one` (the `d = 1`
anchor) to symbolic `d`, by induction on `d` using `cpow_succ` and the OGF↔EGF normalization. -/
theorem natConv_negDirCount_eq_Edef (d : ℕ) :
    ∀ r : ℕ, (natConv negDirCount d (2 * r) : ℚ) = Edef r d := by
  induction d with
  | zero =>
      intro r
      unfold Edef
      simp only [natConv_zero, cpow]
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; norm_num
      · have h1 : 2 * r ≠ 0 := by omega
        have h2 : r ≠ 0 := by omega
        simp [h1, h2]
  | succ d ih =>
      intro r
      rw [natConv_succ]
      -- The sum over a ∈ range(2r+1); only even a = 2c survive. Reindex to range(r+1).
      -- First, push the cast over the ℕ-sum.
      rw [Nat.cast_sum]
      simp only [Nat.cast_mul]
      -- Reindex: only even a contribute. Map c ↦ 2c on range(r+1).
      have hreindex : (∑ a ∈ Finset.range (2 * r + 1),
            ((2 * r).choose a : ℚ) * ((natConv negDirCount d a : ℚ) * (negDirCount (2 * r - a) : ℚ)))
          = ∑ c ∈ Finset.range (r + 1),
              ((2 * r).choose (2 * c) : ℚ)
                * ((natConv negDirCount d (2 * c) : ℚ) * (negDirCount (2 * r - 2 * c) : ℚ)) := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (2 * r + 1)) (fun a => Even a)]
        -- odd part is zero
        have hodd : (∑ a ∈ (Finset.range (2 * r + 1)).filter (fun a => ¬ Even a),
            ((2 * r).choose a : ℚ) * ((natConv negDirCount d a : ℚ) * (negDirCount (2 * r - a) : ℚ))) = 0 := by
          apply Finset.sum_eq_zero
          intro a ha
          rw [Finset.mem_filter] at ha
          obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp ha.2
          rw [hk, natConv_negDirCount_odd]; ring
        rw [hodd, add_zero]
        -- even part: bijection c ↦ 2c from range(r+1) onto filtered evens
        apply Finset.sum_nbij' (fun a => a / 2) (fun c => 2 * c)
        · intro a ha
          rw [Finset.mem_filter, Finset.mem_range] at ha
          obtain ⟨k, hk⟩ := ha.2
          rw [Finset.mem_range]; omega
        · intro c hc
          rw [Finset.mem_range] at hc
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, ⟨c, by ring⟩⟩
        · intro a ha
          rw [Finset.mem_filter] at ha
          obtain ⟨k, hk⟩ := ha.2
          omega
        · intro c _; omega
        · intro a ha
          rw [Finset.mem_filter] at ha
          obtain ⟨k, hk⟩ := ha.2
          have : a = 2 * (a / 2) := by omega
          rw [← this]
      rw [hreindex]
      -- Now each term: negDirCount (2r - 2c) = negDirCount (2(r-c)) = centralBinom (r-c).
      -- Apply IH on natConv negDirCount d (2c), and the normalization identity.
      have hterm : ∀ c ∈ Finset.range (r + 1),
          ((2 * r).choose (2 * c) : ℚ)
              * ((natConv negDirCount d (2 * c) : ℚ) * (negDirCount (2 * r - 2 * c) : ℚ))
            = ((2 * r).factorial : ℚ) * (I0c (r - c) * cpow I0c d c) := by
        intro c hc
        rw [Finset.mem_range, Nat.lt_succ_iff] at hc
        have hcdc : (2 * r - 2 * c) = 2 * (r - c) := by omega
        rw [hcdc, negDirCount_two_mul, ih c]
        -- ih c : natConv d (2c) = Edef c d = (2c)! cpow I0c d c
        unfold Edef
        have hnorm := normalization_identity r c hc
        calc ((2 * r).choose (2 * c) : ℚ) * (((2 * c).factorial : ℚ) * cpow I0c d c
                * (Nat.centralBinom (r - c) : ℚ))
            = (((2 * r).choose (2 * c) : ℚ) * ((2 * c).factorial : ℚ)
                * (Nat.centralBinom (r - c) : ℚ)) * cpow I0c d c := by ring
          _ = (((2 * r).factorial : ℚ) * I0c (r - c)) * cpow I0c d c := by rw [hnorm]
          _ = ((2 * r).factorial : ℚ) * (I0c (r - c) * cpow I0c d c) := by ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      unfold Edef
      congr 1
      show (∑ c ∈ Finset.range (r + 1), I0c (r - c) * cpow I0c d c)
          = cpow I0c (d + 1) r
      rw [show cpow I0c (d + 1) r
            = ∑ j ∈ Finset.range (r + 1), I0c j * cpow I0c d (r - j) from rfl]
      rw [← Finset.sum_range_reflect (fun j => I0c j * cpow I0c d (r - j)) (r + 1)]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mem_range, Nat.lt_succ_iff] at hc
      have h1 : r + 1 - 1 - c = r - c := by omega
      rw [h1]
      have h2 : r - (r - c) = c := by omega
      rw [h2]

/-- Corollary: the `m`-fold antipodal zero-sum count of a mutually-decoupled family equals the
`_AvW0` Bessel model value `Edef r m`. Combines `AvF1.zeroSumCount_iUnion_eq_natConv` (the
symbolic-`m` decoupling induction) with the bridge above. This is the full char-0 Bessel identity
`Z_r(μ_{2m}) = (2r)!·[x^{2r}] I₀(2x)^m`, modulo only the `MutuallyDecoupled` (Lam–Leung) input. -/
theorem bessel_mfold_symbolic_d {F : Type*} [Field F] [DecidableEq F]
    (m : ℕ) (D : Fin m → Finset F)
    (hf : ∀ (k : ℕ) (h : k < m) (N : ℕ),
        ArkLib.ProximityGap.NegationClosedWalk.zeroSumCount (D ⟨k, h⟩) N = negDirCount N)
    (hdec : MutuallyDecoupled D) (r : ℕ) :
    (ArkLib.ProximityGap.NegationClosedWalk.zeroSumCount (unionUpto D m) (2 * r) : ℚ)
      = Edef r m := by
  rw [zeroSumCount_iUnion_eq_natConv m D negDirCount hf hdec (2 * r)]
  exact natConv_negDirCount_eq_Edef m r

#print axioms negDirCount_odd
#print axioms negDirCount_two_mul
#print axioms natConv_negDirCount_odd
#print axioms normalization_identity
#print axioms natConv_negDirCount_eq_Edef
#print axioms bessel_mfold_symbolic_d

end ArkLib.ProximityGap.Frontier.AvCR
