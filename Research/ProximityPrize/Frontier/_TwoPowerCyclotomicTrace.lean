/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: toastedtokens-design, ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Research.ProximityPrize.Frontier._BadPrimeBoundCore

/-!
# NT2 — the 2-power cyclotomic trace

`BadPrimeBound.badPrimeBound_core` and `StickelbergerDepth.stickelberger_depth_bound` prove the
AM-GM half of the Q1 bad-prime bound, taking as a hypothesis the 2-power trace identity

> **(NT2)** `Tr(ζ^m) = 0` for `0 ≠ m ∈ (−n/2, n/2)`, hence
> `∑_σ |σ(β)|² = (n/2) · ∑_k c_k²` for `β = ∑_{k < n/2} c_k ζ^k`.

The same identity is the length formula in the short-vector reading of wraparound
(`_wf7W6_shortvector_spur`, `_ThetaPoissonNormMismatchNoGo`): the Hermitian Gram matrix of the
power basis `1, ζ, …, ζ^{d-1}` is `d · I`, with `d = φ(n) = n/2`. Those files record the matrix as
a numerical check. This file proves it.

For `n = 2^μ` and a primitive `n`-th root `ζ`, the sum of `ζ^{a m}` over odd `a < n` is `φ(n)`
when `n ∣ m`, `-φ(n)` when `n/2 ∣ m` but `n ∤ m`, and `0` otherwise. Power-basis differences lie
in `(-n/2, n/2)`, so the Gram matrix is `φ(n) · I`, and

> `∑_a ‖∑_k c_k ζ^{a k}‖² = φ(n) · ∑_k c_k²`.

For `c_k ∈ {-1, 0, 1}` the right-hand side is `φ(n) · |B|`, the trace hypothesis of
`badPrimeBound_core`. `badPrime_le_sq_of_nt2` feeds that identity into the existing core, so the
full-window bound needs only the splitting lower bound on the norm (NT1).

This does not prove prime splitting, does not close the `R ~ log p` gap of the depth-parametrised
bound, and does not close `δ*`.
-/

set_option autoImplicit false

open Finset Complex

namespace ProximityGap.Frontier.TwoPowerCyclotomicTrace

/-- Odd residues in `0, …, 2^μ − 1`, i.e. `(ℤ/2^μℤ)ˣ`. -/
def oddUnits (μ : ℕ) : Finset ℕ := (Finset.range (2 ^ μ)).filter Odd

theorem oddUnits_card {μ : ℕ} (hμ : 1 ≤ μ) : (oddUnits μ).card = 2 ^ (μ - 1) := by
  classical
  let d := 2 ^ (μ - 1)
  have hn : 2 ^ μ = 2 * d := by
    rw [show μ = (μ - 1) + 1 by omega, pow_succ, Nat.mul_comm]
  have him : oddUnits μ = (Finset.range d).image (fun b => 2 * b + 1) := by
    ext a
    simp only [oddUnits, mem_filter, mem_range, mem_image, hn]
    constructor
    · intro ⟨ha, ho⟩
      refine ⟨a / 2, ?_, ?_⟩
      · have hdiv : 2 * (a / 2) + a % 2 = a := Nat.div_add_mod a 2
        have hmod : a % 2 = 1 := Nat.odd_iff.mp ho
        omega
      · have hdiv : 2 * (a / 2) + a % 2 = a := Nat.div_add_mod a 2
        have hmod : a % 2 = 1 := Nat.odd_iff.mp ho
        linarith
    · rintro ⟨b, hb, rfl⟩
      exact ⟨by omega, odd_two_mul_add_one b⟩
  have hinj : Function.Injective (fun b : ℕ => 2 * b + 1) := by
    intro x y hxy
    change 2 * x + 1 = 2 * y + 1 at hxy
    omega
  rw [him, card_image_of_injective _ hinj, card_range]

theorem sum_range_even_add_odd {n : ℕ} (f : ℕ → ℂ) :
    ∑ a ∈ Finset.range n, f a
      = ∑ a ∈ (Finset.range n).filter Even, f a
        + ∑ a ∈ (Finset.range n).filter Odd, f a := by
  classical
  simpa [Nat.not_even_iff_odd] using
    (Finset.sum_filter_add_sum_filter_not (Finset.range n) Even f).symm

theorem sum_filter_even {d : ℕ} (f : ℕ → ℂ) :
    ∑ a ∈ (Finset.range (2 * d)).filter Even, f a = ∑ b ∈ Finset.range d, f (2 * b) := by
  classical
  have him : (Finset.range (2 * d)).filter Even = (Finset.range d).image (fun b => 2 * b) := by
    ext a
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · intro ⟨ha, he⟩
      have h2 : 2 ∣ a := even_iff_two_dvd.mp he
      refine ⟨a / 2, ?_, Nat.mul_div_cancel' h2⟩
      have hmul : 2 * (a / 2) = a := Nat.mul_div_cancel' h2
      omega
    · rintro ⟨b, hb, rfl⟩
      exact ⟨by omega, even_two_mul b⟩
  have hinj : Set.InjOn (fun b : ℕ => 2 * b) (↑(Finset.range d)) := by
    intro x _ y _ hxy
    change 2 * x = 2 * y at hxy
    omega
  rw [him, sum_image hinj]

theorem geomSum_pow_eq {η : ℂ} {n t : ℕ} (_hn : 0 < n) (hη : η ^ n = 1) :
    ∑ i ∈ Finset.range n, (η ^ t) ^ i = if η ^ t = 1 then (n : ℂ) else 0 := by
  by_cases h1 : η ^ t = 1
  · simp [h1, sum_const, card_range, nsmul_eq_mul]
  · have hpow : (η ^ t) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hη, one_pow]
    rw [if_neg h1, geom_sum_eq h1, hpow, sub_self, zero_div]

theorem primitive_sq {μ : ℕ} (hμ : 1 ≤ μ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    IsPrimitiveRoot (ζ ^ 2) (2 ^ (μ - 1)) := by
  rw [IsPrimitiveRoot.iff_orderOf, orderOf_pow' ζ (by decide : (2 : ℕ) ≠ 0)]
  rw [(IsPrimitiveRoot.iff_orderOf).mp hζ]
  have hdiv : 2 ∣ 2 ^ μ := dvd_pow_self 2 (by omega)
  rw [Nat.gcd_eq_right hdiv]
  have hpow := Nat.pow_div (x := 2) (m := μ) (n := 1) hμ (by decide : 0 < 2)
  simpa [pow_one] using hpow

theorem primitive_inv {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    IsPrimitiveRoot ζ⁻¹ n := by
  have hζ0 : ζ ≠ 0 := by
    intro h0
    have := hζ.pow_eq_one
    rw [h0, zero_pow (Nat.ne_of_gt hn)] at this
    exact zero_ne_one this
  refine ⟨?_, ?_⟩
  · rw [inv_pow, hζ.pow_eq_one, inv_one]
  · intro l hl
    rw [inv_pow, inv_eq_one] at hl
    exact hζ.dvd_of_pow_eq_one l hl

/-- **NT2 for one power.** For `m < n = 2^μ`, the odd-residue sum of `ζ^{a m}` is `φ(n)`,
`-φ(n)`, or `0`, according as `m = 0`, `m = n/2`, or neither. -/
theorem oddUnitPowerSum {μ : ℕ} (hμ : 1 ≤ μ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ μ))
    (m : ℕ) (hm : m < 2 ^ μ) :
    ∑ a ∈ oddUnits μ, ζ ^ (a * m)
      = if m = 0 then (2 ^ (μ - 1) : ℂ)
        else if m = 2 ^ (μ - 1) then -((2 ^ (μ - 1) : ℂ)) else 0 := by
  classical
  set n : ℕ := 2 ^ μ
  set d : ℕ := 2 ^ (μ - 1)
  have hn : n = 2 * d := by
    dsimp [n, d]
    have hμ1 : μ = (μ - 1) + 1 := by omega
    conv_lhs => rw [hμ1, pow_succ]
    exact Nat.mul_comm _ _
  have hdpos : 0 < d := Nat.one_le_pow _ _ (by decide)
  have hfull : ∑ i ∈ Finset.range n, ζ ^ (i * m) = if n ∣ m then (n : ℂ) else 0 := by
    have hgeom := geomSum_pow_eq (η := ζ) (n := n) (t := m) (by positivity) hζ.pow_eq_one
    have hre : ∑ i ∈ Finset.range n, (ζ ^ m) ^ i = ∑ i ∈ Finset.range n, ζ ^ (i * m) := by
      refine sum_congr rfl fun i _ => ?_
      rw [← pow_mul, Nat.mul_comm]
    rw [hre] at hgeom
    simpa [hζ.pow_eq_one_iff_dvd m] using hgeom
  have hζ2 : IsPrimitiveRoot (ζ ^ 2) d := primitive_sq hμ hζ
  have heven : ∑ a ∈ (Finset.range n).filter Even, ζ ^ (a * m)
      = if d ∣ m then (d : ℂ) else 0 := by
    rw [hn, sum_filter_even]
    have hgeom := geomSum_pow_eq (η := ζ ^ 2) (n := d) (t := m) hdpos hζ2.pow_eq_one
    have hre : ∑ b ∈ Finset.range d, ((ζ ^ 2) ^ m) ^ b
        = ∑ b ∈ Finset.range d, ζ ^ ((2 * b) * m) := by
      refine sum_congr rfl fun b _ => ?_
      rw [← pow_mul, ← pow_mul]
      exact congrArg (ζ ^ ·) (by ring)
    rw [hre] at hgeom
    simpa [hζ2.pow_eq_one_iff_dvd m] using hgeom
  have hsplit := sum_range_even_add_odd (n := n) (fun a => ζ ^ (a * m))
  have hodd : ∑ a ∈ oddUnits μ, ζ ^ (a * m)
      = (if n ∣ m then (n : ℂ) else 0) - (if d ∣ m then (d : ℂ) else 0) := by
    have hsplit' : ∑ a ∈ Finset.range n, ζ ^ (a * m)
        = ∑ a ∈ (Finset.range n).filter Even, ζ ^ (a * m)
          + ∑ a ∈ oddUnits μ, ζ ^ (a * m) := by
      simpa [oddUnits] using hsplit
    rw [hfull, heven] at hsplit'
    have hA : (if n ∣ m then (n : ℂ) else 0)
        = (if d ∣ m then (d : ℂ) else 0) + ∑ a ∈ oddUnits μ, ζ ^ (a * m) := hsplit'
    calc
      ∑ a ∈ oddUnits μ, ζ ^ (a * m)
          = ((if d ∣ m then (d : ℂ) else 0) + ∑ a ∈ oddUnits μ, ζ ^ (a * m))
              - (if d ∣ m then (d : ℂ) else 0) := by ring
      _ = (if n ∣ m then (n : ℂ) else 0) - (if d ∣ m then (d : ℂ) else 0) := by rw [hA]
  have hn_dvd : n ∣ m ↔ m = 0 := by
    constructor
    · intro h
      obtain ⟨t, ht⟩ := h
      have hmlt : m < n := by simpa [n] using hm
      have hn1 : 1 ≤ n := by simpa [n] using (Nat.one_le_pow μ 2 (by decide))
      have ht0 : t = 0 := by
        cases t with
        | zero => rfl
        | succ t =>
          have hge : n ≤ n * (t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos t)
          rw [ht] at hmlt
          omega
      simp [ht, ht0]
    · rintro rfl
      exact dvd_zero _
  have hd_cases : d ∣ m → m = 0 ∨ m = d := by
    intro h
    obtain ⟨t, ht⟩ := h
    have hmlt : m < 2 * d := by simpa [n, hn] using hm
    have ht2 : t < 2 := by
      by_contra hge
      have h2 : 2 ≤ t := by omega
      have hmul : 2 * d ≤ d * t := by
        have : d * 2 ≤ d * t := Nat.mul_le_mul_left d h2
        simpa [Nat.mul_comm] using this
      rw [ht] at hmlt
      omega
    interval_cases t
    · simp [ht]
    · right
      simpa using ht
  by_cases hm0 : m = 0
  · have hnd : n ∣ m := hn_dvd.mpr hm0
    have hdd : d ∣ m := by rw [hm0]; exact dvd_zero d
    rw [hodd, if_pos hnd, if_pos hdd]
    have hsum : (n : ℂ) - (d : ℂ) = (d : ℂ) := by
      rw [hn]; push_cast; ring
    rw [hsum, hm0, if_pos rfl]
    simp [d]
  · have hnotn : ¬ n ∣ m := fun h => hm0 (hn_dvd.mp h)
    by_cases hmd : m = d
    · have hdvd : d ∣ m := by rw [hmd]
      have hd0 : d ≠ 0 := Nat.ne_of_gt hdpos
      rw [hodd, if_neg hnotn, if_pos hdvd, hmd, if_neg hd0, if_pos rfl]
      simp [d]
    · have hnotd : ¬ d ∣ m := by
        intro h
        rcases hd_cases h with h0 | hdEq
        · exact hm0 h0
        · exact hmd hdEq
      rw [hodd, if_neg hnotn, if_neg hnotd, if_neg hm0, if_neg hmd]
      ring

theorem primitiveRoot_ne_zero {n : ℕ} {ζ : ℂ} (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) : ζ ≠ 0 := by
  intro h0
  have := hζ.pow_eq_one
  rw [h0, zero_pow (Nat.ne_of_gt hn)] at this
  exact zero_ne_one this

theorem normSq_primitiveRoot {n : ℕ} {ζ : ℂ} (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    normSq ζ = 1 := by
  have hpow : normSq ζ ^ n = 1 := by
    rw [← map_pow normSq ζ n, hζ.pow_eq_one, normSq_one]
  have hpow' : normSq ζ ^ n = (1 : ℝ) ^ n := by simpa using hpow
  exact (pow_left_inj₀ (normSq_nonneg ζ) (zero_le_one) (Nat.ne_of_gt hn)).mp hpow'

theorem star_primitiveRoot {n : ℕ} {ζ : ℂ} (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    star ζ = ζ⁻¹ := by
  have hζ0 : ζ ≠ 0 := primitiveRoot_ne_zero hn hζ
  have hmul : ζ * star ζ = 1 := by
    rw [star_def, mul_conj, normSq_primitiveRoot hn hζ, ofReal_one]
  exact mul_left_cancel₀ hζ0 (by rw [hmul, mul_inv_cancel₀ hζ0])

/-- **The power-basis Gram matrix is `φ(n) · I`.** -/
theorem powerBasis_gram {μ : ℕ} (hμ : 1 ≤ μ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ μ))
    (j k : Fin (2 ^ (μ - 1))) :
    ∑ a ∈ oddUnits μ, ζ ^ (a * j.val) * star (ζ ^ (a * k.val))
      = if j = k then (2 ^ (μ - 1) : ℂ) else 0 := by
  have hζ0 : ζ ≠ 0 := primitiveRoot_ne_zero (by positivity) hζ
  have hstar : star ζ = ζ⁻¹ := star_primitiveRoot (by positivity) hζ
  by_cases hjk : j = k
  · subst hjk
    have hterm : ∀ a ∈ oddUnits μ, ζ ^ (a * j.val) * star (ζ ^ (a * j.val)) = 1 := by
      intro a _
      rw [star_pow, hstar, ← mul_pow, mul_inv_cancel₀ hζ0, one_pow]
    rw [if_pos rfl, sum_congr rfl hterm, sum_const, oddUnits_card hμ, nsmul_eq_mul, mul_one]
    norm_cast
  · rw [if_neg hjk]
    have hne : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · set e : ℕ := k.val - j.val
      have he0 : 0 < e := Nat.sub_pos_of_lt hlt
      have hk : j.val + e = k.val := Nat.add_sub_of_le (le_of_lt hlt)
      have helt : e < 2 ^ (μ - 1) := by
        have hklt := k.isLt
        have : e ≤ k.val := Nat.sub_le _ _
        omega
      have he_lt_n : e < 2 ^ μ :=
        lt_of_lt_of_le helt (Nat.pow_le_pow_right (by decide) (Nat.sub_le μ 1))
      have hterm : ∀ a ∈ oddUnits μ,
          ζ ^ (a * j.val) * star (ζ ^ (a * k.val)) = (ζ⁻¹) ^ (a * e) := by
        intro a _
        rw [star_pow, hstar, ← hk]
        calc
          ζ ^ (a * j.val) * (ζ⁻¹) ^ (a * (j.val + e))
              = ζ ^ (a * j.val) * ((ζ⁻¹) ^ (a * j.val) * (ζ⁻¹) ^ (a * e)) := by
                rw [Nat.mul_add, pow_add]
          _ = (ζ ^ (a * j.val) * (ζ⁻¹) ^ (a * j.val)) * (ζ⁻¹) ^ (a * e) := by ring
          _ = (ζ * ζ⁻¹) ^ (a * j.val) * (ζ⁻¹) ^ (a * e) := by rw [← mul_pow]
          _ = (ζ⁻¹) ^ (a * e) := by rw [mul_inv_cancel₀ hζ0, one_pow, one_mul]
      have hsum := oddUnitPowerSum hμ (primitive_inv (by positivity) hζ) e he_lt_n
      rw [sum_congr rfl hterm, hsum, if_neg (Nat.ne_of_gt he0), if_neg (ne_of_lt helt)]
    · set e : ℕ := j.val - k.val
      have he0 : 0 < e := Nat.sub_pos_of_lt hgt
      have hjv : k.val + e = j.val := Nat.add_sub_of_le (le_of_lt hgt)
      have helt : e < 2 ^ (μ - 1) := by
        have hjlt := j.isLt
        have : e ≤ j.val := Nat.sub_le _ _
        omega
      have he_lt_n : e < 2 ^ μ :=
        lt_of_lt_of_le helt (Nat.pow_le_pow_right (by decide) (Nat.sub_le μ 1))
      have hterm : ∀ a ∈ oddUnits μ,
          ζ ^ (a * j.val) * star (ζ ^ (a * k.val)) = ζ ^ (a * e) := by
        intro a _
        rw [star_pow, hstar, ← hjv]
        calc
          ζ ^ (a * (k.val + e)) * (ζ⁻¹) ^ (a * k.val)
              = (ζ ^ (a * k.val) * ζ ^ (a * e)) * (ζ⁻¹) ^ (a * k.val) := by
                rw [Nat.mul_add, pow_add]
          _ = ζ ^ (a * e) * (ζ ^ (a * k.val) * (ζ⁻¹) ^ (a * k.val)) := by ring
          _ = ζ ^ (a * e) * (ζ * ζ⁻¹) ^ (a * k.val) := by rw [← mul_pow]
          _ = ζ ^ (a * e) := by rw [mul_inv_cancel₀ hζ0, one_pow, mul_one]
      have hsum := oddUnitPowerSum hμ hζ e he_lt_n
      rw [sum_congr rfl hterm, hsum, if_neg (Nat.ne_of_gt he0), if_neg (ne_of_lt helt)]

noncomputable def galoisEval (ζ : ℂ) (a : ℕ) {d : ℕ} (c : Fin d → ℤ) : ℂ :=
  ∑ k : Fin d, (c k : ℂ) * ζ ^ (a * k.val)

theorem galois_normSq_sum {μ : ℕ} (hμ : 1 ≤ μ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ μ))
    (c : Fin (2 ^ (μ - 1)) → ℤ) :
    ∑ a ∈ oddUnits μ, normSq (galoisEval ζ a c)
      = (2 ^ (μ - 1) : ℝ) * ∑ k : Fin (2 ^ (μ - 1)), (c k : ℝ) ^ 2 := by
  classical
  have hcomplex : ∑ a ∈ oddUnits μ, galoisEval ζ a c * star (galoisEval ζ a c)
      = ((2 ^ (μ - 1) : ℕ) : ℂ) * ∑ k : Fin (2 ^ (μ - 1)), (c k : ℂ) ^ 2 := by
    have hrewrite : ∀ a ∈ oddUnits μ,
        galoisEval ζ a c * star (galoisEval ζ a c)
          = ∑ k : Fin (2 ^ (μ - 1)), ∑ j : Fin (2 ^ (μ - 1)),
              (c k : ℂ) * (c j : ℂ) * (ζ ^ (a * k.val) * star (ζ ^ (a * j.val))) := by
      intro a _
      simp only [galoisEval]
      rw [star_sum, sum_mul_sum]
      refine sum_congr rfl fun k _ => sum_congr rfl fun j _ => ?_
      rw [star_mul, star_intCast, star_pow, mul_comm]
      ring
    calc
      ∑ a ∈ oddUnits μ, galoisEval ζ a c * star (galoisEval ζ a c)
          = ∑ a ∈ oddUnits μ, ∑ k : Fin (2 ^ (μ - 1)), ∑ j : Fin (2 ^ (μ - 1)),
              (c k : ℂ) * (c j : ℂ)
                * (ζ ^ (a * k.val) * star (ζ ^ (a * j.val))) := by
            exact sum_congr rfl hrewrite
      _ = ∑ k : Fin (2 ^ (μ - 1)), ∑ j : Fin (2 ^ (μ - 1)), (c k : ℂ) * (c j : ℂ)
            * ∑ a ∈ oddUnits μ, ζ ^ (a * k.val) * star (ζ ^ (a * j.val)) := by
            rw [sum_comm]
            refine sum_congr rfl fun k _ => ?_
            rw [sum_comm]
            refine sum_congr rfl fun j _ => ?_
            rw [← mul_sum]
      _ = ∑ k : Fin (2 ^ (μ - 1)), (c k : ℂ) ^ 2 * ((2 ^ (μ - 1) : ℕ) : ℂ) := by
            refine sum_congr rfl fun k _ => ?_
            rw [sum_eq_single k]
            · rw [powerBasis_gram hμ hζ k k, if_pos rfl, pow_two]
              norm_cast
            · intro j _ hj
              rw [powerBasis_gram hμ hζ k j, if_neg (fun h => hj h.symm)]
              ring
            · intro hk
              exact absurd (mem_univ k) hk
      _ = ((2 ^ (μ - 1) : ℕ) : ℂ) * ∑ k : Fin (2 ^ (μ - 1)), (c k : ℂ) ^ 2 := by
            rw [mul_sum]
            refine sum_congr rfl fun k _ => ?_
            ring
  have hmul : ∀ a ∈ oddUnits μ,
      galoisEval ζ a c * star (galoisEval ζ a c) = (normSq (galoisEval ζ a c) : ℂ) := by
    intro a _
    rw [star_def, mul_conj]
  have hleft : (∑ a ∈ oddUnits μ, (normSq (galoisEval ζ a c) : ℂ))
      = ((2 ^ (μ - 1) : ℕ) : ℂ) * ∑ k : Fin (2 ^ (μ - 1)), (c k : ℂ) ^ 2 := by
    rw [← sum_congr rfl hmul]
    exact hcomplex
  have hcast : ((∑ a ∈ oddUnits μ, normSq (galoisEval ζ a c) : ℝ) : ℂ)
      = ∑ a ∈ oddUnits μ, (normSq (galoisEval ζ a c) : ℂ) := by
    simpa [ofRealHom_eq_coe] using
      (map_sum ofRealHom (fun a => normSq (galoisEval ζ a c)) (oddUnits μ)).symm
  apply ofReal_injective
  rw [hcast, hleft]
  push_cast
  rfl

theorem sq_sum_eq_support_card {d : ℕ} (c : Fin d → ℤ)
    (hc : ∀ k, c k = -1 ∨ c k = 0 ∨ c k = 1) :
    ∑ k : Fin d, (c k : ℝ) ^ 2
      = ((Finset.univ.filter fun k => c k ≠ 0).card : ℝ) := by
  classical
  have hterm : ∀ k, (c k : ℝ) ^ 2 = if c k ≠ 0 then (1 : ℝ) else 0 := by
    intro k
    rcases hc k with hk | hk | hk <;> simp [hk]
  simp_rw [hterm, sum_ite, sum_const_zero, sum_const, add_zero, nsmul_eq_mul, mul_one]

theorem signedIndicator_galois_normSq_sum {μ : ℕ} (hμ : 1 ≤ μ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) (c : Fin (2 ^ (μ - 1)) → ℤ)
    (hc : ∀ k, c k = -1 ∨ c k = 0 ∨ c k = 1) :
    ∑ a ∈ oddUnits μ, normSq (galoisEval ζ a c)
      = (2 ^ (μ - 1) : ℝ) * ((Finset.univ.filter fun k => c k ≠ 0).card : ℝ) := by
  rw [galois_normSq_sum hμ hζ, sq_sum_eq_support_card c hc]

/-- **Full-window bad-prime bound with NT2 discharged.** For `μ ≥ 3`, a signed coefficient vector
whose squared Galois conjugates satisfy `p^{n/8} ≤ √(∏ ‖σ_a(β)‖²)` obeys `p ≤ |B|²`. NT1 remains
an input. -/
theorem badPrime_le_sq_of_nt2 {μ : ℕ} (hμ : 3 ≤ μ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ μ))
    (c : Fin (2 ^ (μ - 1)) → ℤ) (hc : ∀ k, c k = -1 ∨ c k = 0 ∨ c k = 1) (p : ℕ) (hp : 0 < p)
    (hnorm : (p : ℝ) ^ (2 ^ (μ - 3))
      ≤ Real.sqrt (∏ a ∈ oddUnits μ, normSq (galoisEval ζ a c))) :
    (p : ℝ) ≤ ((Finset.univ.filter fun k => c k ≠ 0).card : ℝ) ^ 2 := by
  classical
  let M : ℕ := 2 ^ (μ - 1)
  let K : ℕ := 2 ^ (μ - 3)
  have hμ1 : 1 ≤ μ := by omega
  have hcard : (oddUnits μ).card = M := by simpa [M] using oddUnits_card hμ1
  have hK : 0 < K := Nat.one_le_pow _ _ (by decide)
  have hMK : M = 4 * K := by
    dsimp [M, K]
    have hsum : μ - 1 = (μ - 3) + 2 := by omega
    rw [hsum, pow_add, show (2 ^ 2 : ℕ) = 4 by norm_num, Nat.mul_comm]
  let emb : Fin M ↪o ℕ := (oddUnits μ).orderEmbOfFin hcard
  let aFun : Fin M → ℝ := fun i => normSq (galoisEval ζ (emb i) c)
  have hinj : Set.InjOn (fun i : Fin M => (emb i : ℕ)) (↑(univ : Finset (Fin M))) := by
    intro i _ j _ h
    exact emb.injective h
  have himg : (univ : Finset (Fin M)).image (fun i => (emb i : ℕ)) = oddUnits μ :=
    image_orderEmbOfFin_univ (oddUnits μ) hcard
  have hsumA : ∑ i : Fin M, aFun i = ∑ a ∈ oddUnits μ, normSq (galoisEval ζ a c) := by
    have hs := Finset.sum_image (s := (univ : Finset (Fin M)))
      (g := fun i : Fin M => (emb i : ℕ)) (f := fun a => normSq (galoisEval ζ a c)) hinj
    rw [himg] at hs
    simpa [aFun] using hs.symm
  have hprodA : ∏ i : Fin M, aFun i = ∏ a ∈ oddUnits μ, normSq (galoisEval ζ a c) := by
    have hs := Finset.prod_image (s := (univ : Finset (Fin M)))
      (g := fun i : Fin M => (emb i : ℕ)) (f := fun a => normSq (galoisEval ζ a c)) hinj
    rw [himg] at hs
    simpa [aFun] using hs.symm
  let b : ℕ := (univ.filter fun k : Fin M => c k ≠ 0).card
  have htrace : ∑ i, aFun i = (M : ℝ) * (b : ℝ) := by
    rw [hsumA]
    simpa [b, M] using signedIndicator_galois_normSq_sum hμ1 hζ c hc
  have hnorm' : (p : ℝ) ^ K ≤ Real.sqrt (∏ i, aFun i) := by
    simpa [K, hprodA] using hnorm
  have ha : ∀ i, 0 < aFun i := by
    intro i
    have hnn : 0 ≤ aFun i := normSq_nonneg _
    by_contra hle
    have hzero : aFun i = 0 := le_antisymm (not_lt.mp hle) hnn
    have hprod0 : ∏ j, aFun j = 0 := prod_eq_zero (mem_univ i) hzero
    have hpK : (0 : ℝ) < (p : ℝ) ^ K := by positivity
    have : (p : ℝ) ^ K ≤ 0 := by simpa [hprod0] using hnorm'
    linarith
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    by_contra hle
    have hb0 : b = 0 := Nat.eq_zero_of_le_zero (by exact_mod_cast (not_lt.mp hle))
    have hc0 : ∀ k, c k = 0 := by
      intro k
      by_contra hk
      have hmem : k ∈ univ.filter fun t => c t ≠ 0 := by simpa [hk] using mem_univ k
      have : 0 < b := card_pos.mpr ⟨k, hmem⟩
      omega
    have hmem : ∃ a, a ∈ oddUnits μ := card_pos.mp (by
      rw [hcard]; exact Nat.one_le_pow _ _ (by decide))
    obtain ⟨a, haU⟩ := hmem
    have heval : galoisEval ζ a c = 0 := by simp [galoisEval, hc0]
    have hprod0 : ∏ x ∈ oddUnits μ, normSq (galoisEval ζ x c) = 0 :=
      prod_eq_zero haU (by simp [heval])
    have hpK : (0 : ℝ) < (p : ℝ) ^ K := by positivity
    have : (p : ℝ) ^ K ≤ 0 := by simpa [K, hprod0] using hnorm
    linarith
  exact ProximityGap.Frontier.BadPrimeBound.badPrimeBound_core (M := M) (K := K) hK hMK aFun ha
    (b : ℝ) (p : ℝ) hbpos (by exact_mod_cast hp) htrace hnorm'

end ProximityGap.Frontier.TwoPowerCyclotomicTrace

#print axioms ProximityGap.Frontier.TwoPowerCyclotomicTrace.oddUnitPowerSum
#print axioms ProximityGap.Frontier.TwoPowerCyclotomicTrace.powerBasis_gram
#print axioms ProximityGap.Frontier.TwoPowerCyclotomicTrace.galois_normSq_sum
#print axioms ProximityGap.Frontier.TwoPowerCyclotomicTrace.signedIndicator_galois_normSq_sum
#print axioms ProximityGap.Frontier.TwoPowerCyclotomicTrace.badPrime_le_sq_of_nt2
