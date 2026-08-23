/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWeightedWindowLaw
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWindowedLaw
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungSpanTwoPrime

/-!
# Issue #232 — THE WINDOWED MASS-SPAN LAW: the t-general total-mass spectrum of
# the BCH-window code (the windowed Lam–Leung law)

O104 proved the Lam–Leung ℕ-span law at window length `1` (total mass of a
vanishing ℕ-weighted root sum lies in `ℕ·p + ℕ·q`); O107 pinned the **0/1**
weight spectrum at every window length `t` (weights are sums of divisors
`> t`).  This file proves their common generalization, the full
multiplicity-level mass spectrum at every `t` — the quantitative consumer of
O108's weighted windowed law:

* `mass_of_combination` — the **mass formula**: the total mass of an
  ℕ-combination of `μ_d`-coset indicators (`d ∣ n`, `d > t`) is
  `Σ_d c_d·d` with `c_d ∈ ℕ` — each coset of size `d` contributes `d` per unit
  of multiplicity (`sum_mod_fiber`).
* `window_mass_span_two_prime` — **the windowed span law**: for
  `n = p^a·q^b`, `ζ` primitive `n`-th (char 0), `t < n`, any window-`t`-
  vanishing `w : ℕ → ℕ` has `Σ_{e<n} w_e ∈ ℕ-span{d : d ∣ n, t < d}`.
* `window_min_mass_two_prime` — **the sharp minimum**: a window-`t`-vanishing
  weight with positive mass has mass `≥` the least divisor of `n` exceeding
  `t` (the weighted upgrade of O107's 0/1 minimum-weight law).
* `window_mass_sharp` — **sharpness at every divisor**: the canonical
  `μ_{d₀}`-coset indicator (`w₀ e = [e ≡ 0 mod n/d₀]`) vanishes on the whole
  window and has mass exactly `d₀`.
* `window_mass_in_prime_span` — the **O104 upgrade**: for every window length
  `t ≥ 1` (not just `t = 1`), the mass lies in `ℕ·p + ℕ·q` — every divisor
  `d > t ≥ 1` of `p^a·q^b` is a multiple of `p` or of `q`.
* Teeth at `n = 72 = 2³·3²`, `t = 9` (O107's BCH-beating instance, upgraded to
  all multiplicities): the mass spectrum below `24` is EXACTLY `{0, 12, 18}` —
  a kernel-checked **gap theorem**: no window-9-vanishing multiplicity vector
  has total mass in `(0,12) ∪ (12,18) ∪ (18,24)`.

Probe-verified before formalization (`scripts/probes/probe_window_mass_span.py`,
exact ℤ[x]/Φ_n, exhaustive over `{0,1,2}^12`, `{0,1}^18`, `{0,1}^20` at every
window length): span membership, sharp minima, and the full gap structure of
the observed mass spectra.
-/

namespace WindowMassSpan

open Finset DeBruijnWeightedWindowLaw

variable {L : Type*} [Field L]

/-- **The mass formula**: an ℕ-combination of `μ_d`-coset indicators
(`d ∣ n`, `d > t`) has total mass `Σ_d c_d·d` — each unit of multiplicity of a
`μ_d`-coset contributes exactly `d` (the fiber-counting identity per
divisor). -/
theorem mass_of_combination {n t : ℕ} {w : ℕ → ℕ}
    (h : IsWeightedWindowCombination n t w) :
    ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range n, w e
      = ∑ d ∈ n.divisors.filter (t < ·), c d * d := by
  obtain ⟨A, hA⟩ := h
  refine ⟨fun d => ∑ r ∈ Finset.range (n / d), A d r, ?_⟩
  calc ∑ e ∈ Finset.range n, w e
      = ∑ e ∈ Finset.range n,
          ∑ d ∈ n.divisors.filter (t < ·), A d (e % (n / d)) :=
        Finset.sum_congr rfl fun e he => hA e (Finset.mem_range.mp he)
    _ = ∑ d ∈ n.divisors.filter (t < ·),
          ∑ e ∈ Finset.range n, A d (e % (n / d)) := Finset.sum_comm
    _ = ∑ d ∈ n.divisors.filter (t < ·),
          (∑ r ∈ Finset.range (n / d), A d r) * d := by
        refine Finset.sum_congr rfl fun d hd => ?_
        obtain ⟨hmem, htd⟩ := Finset.mem_filter.mp hd
        obtain ⟨hdn, hn0⟩ := Nat.mem_divisors.mp hmem
        have hd0 : 0 < d := by omega
        have hm0 : 0 < n / d :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn) hd0
        have hsplit : (n / d) * d = n := Nat.div_mul_cancel hdn
        rw [show Finset.range n = Finset.range ((n / d) * d) from by rw [hsplit],
          LamLeungSpanTwoPrime.sum_mod_fiber (A d) (n / d) d hm0]
        exact Nat.mul_comm _ _

/-- **THE WINDOWED MASS-SPAN LAW** (two-prime): the total mass of any
window-`t`-vanishing ℕ-weighted root sum at `n = p^a·q^b` lies in the ℕ-span
of the divisors of `n` exceeding `t`.  At `t = 1` this is O104's Lam–Leung
span law; at 0/1 weights it is O107's weight spectrum; this is the common
generalization. -/
theorem window_mass_span_two_prime [CharZero L]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b)) (w : ℕ → ℕ)
    {t : ℕ} (htn : t < p ^ a * q ^ b)
    (hwin : ∀ j, 1 ≤ j → j ≤ t →
        ∑ e ∈ Finset.range (p ^ a * q ^ b), (w e : L) * ζ ^ (j * e) = 0) :
    ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range (p ^ a * q ^ b), w e
      = ∑ d ∈ (p ^ a * q ^ b).divisors.filter (t < ·), c d * d :=
  mass_of_combination
    ((weighted_windowed_two_prime hp hq hpq hζ w htn).mp hwin)

/-- **The sharp minimum mass**: a window-`t`-vanishing ℕ-weight with positive
total mass has mass at least `d₀`, for `d₀` any lower bound on the divisors of
`n = p^a·q^b` exceeding `t` — the all-multiplicities upgrade of O107's 0/1
minimum-weight law. -/
theorem window_min_mass_two_prime [CharZero L]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b)) (w : ℕ → ℕ)
    {t : ℕ} (htn : t < p ^ a * q ^ b)
    (hwin : ∀ j, 1 ≤ j → j ≤ t →
        ∑ e ∈ Finset.range (p ^ a * q ^ b), (w e : L) * ζ ^ (j * e) = 0)
    (hpos : 0 < ∑ e ∈ Finset.range (p ^ a * q ^ b), w e)
    {d₀ : ℕ} (hmin : ∀ d, d ∣ p ^ a * q ^ b → t < d → d₀ ≤ d) :
    d₀ ≤ ∑ e ∈ Finset.range (p ^ a * q ^ b), w e := by
  obtain ⟨c, hc⟩ := window_mass_span_two_prime hp hq hpq hζ w htn hwin
  rw [hc] at hpos ⊢
  have hex : ∃ d ∈ (p ^ a * q ^ b).divisors.filter (t < ·), 0 < c d * d := by
    by_contra hno
    have hzero : ∑ d ∈ (p ^ a * q ^ b).divisors.filter (t < ·), c d * d = 0 :=
      Finset.sum_eq_zero fun d hd => by
        rcases Nat.eq_zero_or_pos (c d * d) with h | h
        · exact h
        · exact absurd ⟨d, hd, h⟩ hno
    omega
  obtain ⟨d, hd, hcd⟩ := hex
  obtain ⟨hmem, htd⟩ := Finset.mem_filter.mp hd
  obtain ⟨hdn, _⟩ := Nat.mem_divisors.mp hmem
  have hc0 : 0 < c d := by
    rcases Nat.eq_zero_or_pos (c d) with h0 | h
    · rw [h0, zero_mul] at hcd
      omega
    · exact h
  calc d₀ ≤ d := hmin d hdn htd
    _ ≤ c d * d := Nat.le_mul_of_pos_left d hc0
    _ ≤ ∑ d ∈ (p ^ a * q ^ b).divisors.filter (t < ·), c d * d :=
        Finset.single_le_sum (f := fun d => c d * d)
          (fun i _ => Nat.zero_le _) hd

/-- **Sharpness at every divisor**: for any divisor `d₀ ∣ n` with `t < d₀`,
the canonical `μ_{d₀}`-coset indicator `w₀ e = [e % (n/d₀) = 0]` kills the
whole window `1 ≤ j ≤ t` and has total mass exactly `d₀` — every divisor
exceeding `t` is an achieved mass.  (Works at ANY modulus `n`; the two-prime
hypothesis is only needed for the converse direction.) -/
theorem window_mass_sharp [CharZero L] {n t d₀ : ℕ} (hn : 0 < n)
    (hd₀ : d₀ ∣ n) (htd : t < d₀) {ζ : L} (hζ : IsPrimitiveRoot ζ n) :
    (∀ j, 1 ≤ j → j ≤ t →
        ∑ e ∈ Finset.range n,
          ((if e % (n / d₀) = 0 then 1 else 0 : ℕ) : L) * ζ ^ (j * e) = 0)
      ∧ (∑ e ∈ Finset.range n, (if e % (n / d₀) = 0 then 1 else 0)) = d₀ := by
  have hd0 : 0 < d₀ := by omega
  have hm0 : 0 < n / d₀ := Nat.div_pos (Nat.le_of_dvd hn hd₀) hd0
  have hsplit : (n / d₀) * d₀ = n := Nat.div_mul_cancel hd₀
  have hmem : d₀ ∈ n.divisors.filter (t < ·) :=
    Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd₀, hn.ne'⟩, htd⟩
  have hcomb : IsWeightedWindowCombination n t
      (fun e => if e % (n / d₀) = 0 then 1 else 0) := by
    refine ⟨fun d r => if d = d₀ ∧ r = 0 then 1 else 0, fun e _ => ?_⟩
    rw [Finset.sum_eq_single d₀
      (fun d _ hne => if_neg fun hcon => hne hcon.1)
      (fun habs => absurd hmem habs)]
    by_cases h0 : e % (n / d₀) = 0
    · simp [h0]
    · simp [h0]
  refine ⟨window_vanishes_of_combination hn hζ hcomb, ?_⟩
  rw [show Finset.range n = Finset.range ((n / d₀) * d₀) from by rw [hsplit],
    LamLeungSpanTwoPrime.sum_mod_fiber (fun r => if r = 0 then 1 else 0)
      (n / d₀) d₀ hm0,
    Finset.sum_ite_eq' (Finset.range (n / d₀)) 0 (fun _ => 1),
    if_pos (Finset.mem_range.mpr hm0), mul_one]

/-- **The O104 upgrade**: at every window length `t ≥ 1` (O104 is the case
`t = 1`), the total mass of a window-`t`-vanishing ℕ-weight at `n = p^a·q^b`
lies in `ℕ·p + ℕ·q` — every divisor `d > t ≥ 1` of `n` is a multiple of `p`
or of `q`, so the divisor span refines into the prime span. -/
theorem window_mass_in_prime_span [CharZero L]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b)) (w : ℕ → ℕ)
    {t : ℕ} (ht1 : 1 ≤ t) (htn : t < p ^ a * q ^ b)
    (hwin : ∀ j, 1 ≤ j → j ≤ t →
        ∑ e ∈ Finset.range (p ^ a * q ^ b), (w e : L) * ζ ^ (j * e) = 0) :
    ∃ i j : ℕ, ∑ e ∈ Finset.range (p ^ a * q ^ b), w e = i * p + j * q := by
  obtain ⟨c, hc⟩ := window_mass_span_two_prime hp hq hpq hζ w htn hwin
  set F := (p ^ a * q ^ b).divisors.filter (t < ·) with hF
  refine ⟨∑ d ∈ F.filter (p ∣ ·), c d * (d / p),
    ∑ d ∈ F.filter (fun d => ¬ p ∣ d), c d * (d / q), ?_⟩
  rw [hc, ← Finset.sum_filter_add_sum_filter_not F (p ∣ ·) (fun d => c d * d),
    Finset.sum_mul, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun d hd => ?_
    have hpd : p ∣ d := (Finset.mem_filter.mp hd).2
    rw [mul_assoc, Nat.div_mul_cancel hpd]
  · refine Finset.sum_congr rfl fun d hd => ?_
    obtain ⟨hdF, hnpd⟩ := Finset.mem_filter.mp hd
    obtain ⟨hmem, htd⟩ := Finset.mem_filter.mp hdF
    obtain ⟨hdn, _⟩ := Nat.mem_divisors.mp hmem
    have hcop : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnpd
    have hdq : d ∣ q ^ b :=
      Nat.Coprime.dvd_of_dvd_mul_left (hcop.symm.pow_right a) hdn
    have hqd : q ∣ d := by
      obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow hq).mp hdq
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at htd
        omega
      exact dvd_pow_self q hk0
    rw [mul_assoc, Nat.div_mul_cancel hqd]

/-! ## Teeth: the mass GAP theorem at O107's BCH-beating instance

At `n = 72 = 2³·3²` with window `t = 9` the divisors exceeding `9` are
`{12, 18, 24, 36, 72}`; the span law pins the entire mass spectrum below `24`
to `{0, 12, 18}` — no window-9-vanishing multiplicity vector has total mass
`1..11`, `13..17`, or `19..23`.  (O107 gave the 0/1 minimum `12`; this is the
full gap structure at every multiplicity.)  Sharpness: masses `12` and `18`
are realized by `window_mass_sharp` at `d₀ = 12, 18`. -/

example [CharZero L] {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ 3 * 3 ^ 2))
    (w : ℕ → ℕ)
    (hwin : ∀ j, 1 ≤ j → j ≤ 9 →
        ∑ e ∈ Finset.range (2 ^ 3 * 3 ^ 2), (w e : L) * ζ ^ (j * e) = 0)
    (hmass : ∑ e ∈ Finset.range (2 ^ 3 * 3 ^ 2), w e < 24) :
    ∑ e ∈ Finset.range (2 ^ 3 * 3 ^ 2), w e = 0
      ∨ ∑ e ∈ Finset.range (2 ^ 3 * 3 ^ 2), w e = 12
      ∨ ∑ e ∈ Finset.range (2 ^ 3 * 3 ^ 2), w e = 18 := by
  obtain ⟨c, hc⟩ := window_mass_span_two_prime Nat.prime_two Nat.prime_three
    (by norm_num) hζ w (by norm_num) hwin
  have hfil : ((2 ^ 3 * 3 ^ 2 : ℕ)).divisors.filter (9 < ·)
      = {12, 18, 24, 36, 72} := by decide
  rw [hfil, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at hc
  omega

/-! ## Complement closure and the TWO-SIDED span law (0/1 packing necessity)

The full set `[0, n)` is itself window-vanishing (full geometric sums), so the
window fiber is **closed under complement** — and therefore the mass of a 0/1
window-vanishing set is constrained from BOTH ends: `|S|` AND `n − |S|` must
be sums of divisors of `n` exceeding `t`.  This is strictly stronger than
O107's one-sided spectrum: at `n = 72`, `t = 9`, the mass `66 = 12 + 18 + 36`
IS a divisor sum, yet `72 − 66 = 6` is not (the least divisor past `9` is
`12`) — so weight `66` is impossible, which no one-sided bound can see.

The matching probe (`scripts/probes/probe_window_packing_law.py`) measures
how close the two-sided law comes to characterizing the realizable mass set —
the remaining gap (the sufficiency/packing direction) is the named open
surface of O112. -/

/-- **The full range kills the window**: `Σ_{e<n} ζ^{je} = 0` for any
`1 ≤ j < n` (the full geometric sum at the nontrivial root `ζ^j`). -/
lemma full_range_pow_sum_eq_zero {n j : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hj1 : 1 ≤ j) (hjn : j < n) :
    ∑ e ∈ Finset.range n, ζ ^ (j * e) = 0 := by
  have hx1 : ζ ^ j ≠ 1 := by
    intro h1
    rw [hζ.pow_eq_one_iff_dvd] at h1
    have := Nat.le_of_dvd (by omega) h1
    omega
  have hxn : (ζ ^ j) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  calc ∑ e ∈ Finset.range n, ζ ^ (j * e)
      = ∑ e ∈ Finset.range n, (ζ ^ j) ^ e :=
        Finset.sum_congr rfl fun e _ => by rw [← pow_mul]
    _ = 0 := by rw [geom_sum_eq hx1, hxn, sub_self, zero_div]

/-- **Complement closure of the window fiber**: if `S ⊆ [0, n)` kills the
window `1 ≤ j ≤ t` (`t < n`), so does its complement `[0, n) \ S` — the
window fiber is closed under complement at every modulus. -/
theorem complement_window_vanishes {n t : ℕ} (htn : t < n) {ζ : L}
    (hζ : IsPrimitiveRoot ζ n) {S : Finset ℕ} (hsub : S ⊆ Finset.range n)
    (hwin : ∀ j, 1 ≤ j → j ≤ t → ∑ e ∈ S, ζ ^ (j * e) = 0) :
    ∀ j, 1 ≤ j → j ≤ t → ∑ e ∈ Finset.range n \ S, ζ ^ (j * e) = 0 := by
  intro j hj1 hjt
  have hsplit := Finset.sum_sdiff (f := fun e => ζ ^ (j * e)) hsub
  rw [full_range_pow_sum_eq_zero hζ hj1 (by omega), hwin j hj1 hjt,
    add_zero] at hsplit
  exact hsplit

/-- **THE TWO-SIDED SPAN LAW** (0/1 packing necessity): a window-`t`-vanishing
`S ⊆ [0, n)` at `n = p^a·q^b` has BOTH `|S|` and `n − |S|` expressible as sums
of divisors of `n` exceeding `t` — O107's spectrum applied to `S` and (via
complement closure) to `[0, n) \ S` simultaneously.  Strictly stronger than
the one-sided spectrum (see the `66`-tooth below). -/
theorem window_mass_two_sided_two_prime [CharZero L]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b))
    {S : Finset ℕ} (hsub : S ⊆ Finset.range (p ^ a * q ^ b))
    {t : ℕ} (htn : t < p ^ a * q ^ b)
    (hwin : ∀ j, 1 ≤ j → j ≤ t → ∑ e ∈ S, ζ ^ (j * e) = 0) :
    (∃ m : Multiset ℕ, (∀ d ∈ m, d ∣ p ^ a * q ^ b ∧ t < d) ∧ S.card = m.sum)
      ∧ (∃ m : Multiset ℕ, (∀ d ∈ m, d ∣ p ^ a * q ^ b ∧ t < d)
          ∧ p ^ a * q ^ b - S.card = m.sum) := by
  constructor
  · exact DeBruijnWindowedLaw.window_weight_spectrum_two_prime hp hq hpq hζ
      (fun e he => Finset.mem_range.mp (hsub he)) htn hwin
  · have hCwin := complement_window_vanishes htn hζ hsub hwin
    have hCb : ∀ e ∈ Finset.range (p ^ a * q ^ b) \ S, e < p ^ a * q ^ b :=
      fun e he => Finset.mem_range.mp (Finset.mem_sdiff.mp he).1
    obtain ⟨m, hm, hcard⟩ := DeBruijnWindowedLaw.window_weight_spectrum_two_prime
      hp hq hpq hζ hCb htn hCwin
    refine ⟨m, hm, ?_⟩
    rw [← hcard, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
      Finset.card_range]

/-- **The `66`-tooth**: at `n = 72 = 2³·3²`, `t = 9`, NO window-9-vanishing
0/1 set has exactly `66` elements — even though `66 = 12 + 18 + 36` IS a sum
of divisors exceeding `9`, so O107's one-sided spectrum cannot exclude it.
The complement has `6` elements, is nonempty, and would violate the minimum
weight `12`. -/
example [CharZero L] {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ 3 * 3 ^ 2))
    {S : Finset ℕ} (hsub : S ⊆ Finset.range (2 ^ 3 * 3 ^ 2))
    (hwin : ∀ j, 1 ≤ j → j ≤ 9 → ∑ e ∈ S, ζ ^ (j * e) = 0) :
    S.card ≠ 66 := by
  intro hcard
  have hCwin := complement_window_vanishes (by norm_num) hζ hsub hwin
  have hCb : ∀ e ∈ Finset.range (2 ^ 3 * 3 ^ 2) \ S, e < 2 ^ 3 * 3 ^ 2 :=
    fun e he => Finset.mem_range.mp (Finset.mem_sdiff.mp he).1
  have hCcard : (Finset.range (2 ^ 3 * 3 ^ 2) \ S).card = 6 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_range,
      hcard]
    norm_num
  have hCne : (Finset.range (2 ^ 3 * 3 ^ 2) \ S).Nonempty :=
    Finset.card_pos.mp (by rw [hCcard]; norm_num)
  have h12 : 12 ≤ (Finset.range (2 ^ 3 * 3 ^ 2) \ S).card := by
    refine DeBruijnWindowedLaw.window_min_weight_two_prime Nat.prime_two
      Nat.prime_three (by norm_num) hζ hCb (by norm_num) hCwin hCne ?_
    intro d hdvd hgt
    norm_num at hdvd
    have hle : d ≤ 72 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases d <;> revert hdvd <;> decide
  rw [hCcard] at h12
  omega

/-! ## The two-sided span law is NOT sufficient: the CRT packing obstruction

At `n = 36 = 2²·3²`, `t = 3`, the mass `13` passes the two-sided test —
`13 = 9 + 4` and `36 − 13 = 23 = 9 + 6 + 4 + 4` are both sums of divisors
exceeding `3` — yet NO window-3-vanishing 0/1 set has 13 elements: the only
divisor representation of `13` is `{9, 4}`, and a `μ_9`-coset (step `4`) and a
`μ_4`-coset (step `9`) have coprime steps, so by CRT they ALWAYS intersect.
The realizable mass set sits strictly between the two-sided span (necessary,
`window_mass_two_sided_two_prime`) and naive packing heuristics; its exact
characterization is the open packing surface. -/

/-- **The CRT refutation**: no window-3-vanishing 0/1 set on `[0, 36)` has
exactly `13` elements, although `13` and `36 − 13 = 23` are both sums of
divisors of `36` exceeding `3`.  The two-sided span condition is necessary
but NOT sufficient. -/
theorem two_sided_not_sufficient [CharZero L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ 2 * 3 ^ 2))
    {S : Finset ℕ} (hS : ∀ e ∈ S, e < 2 ^ 2 * 3 ^ 2)
    (hwin : ∀ j, 1 ≤ j → j ≤ 3 → ∑ e ∈ S, ζ ^ (j * e) = 0) :
    S.card ≠ 13 := by
  intro hcard13
  obtain ⟨Ps, hpk, hdisj, hSuni⟩ :=
    (DeBruijnWindowedLaw.windowed_two_prime Nat.prime_two Nat.prime_three
      (by norm_num) hζ hS (by norm_num)).mp hwin
  -- the packet sizes sum to 13
  have hsum13 : ∑ P ∈ Ps, P.card = 13 := by
    rw [← hcard13, hSuni, Finset.card_biUnion (fun x hx y hy hxy => hdisj hx hy hxy)]
    rfl
  -- each packet's card is its divisor
  have hcards : ∀ P ∈ Ps, ∃ d, d ∣ 36 ∧ 3 < d ∧ P.card = d ∧
      DeBruijnTwoPrimeAssembly.IsPacket 36 d P := by
    intro P hP
    obtain ⟨d, hdvd, hgt, hPd⟩ := hpk P hP
    have hdvd' : d ∣ 36 := by norm_num at hdvd ⊢; exact hdvd
    have hPd' : DeBruijnTwoPrimeAssembly.IsPacket 36 d P := by
      have h36 : (2 ^ 2 * 3 ^ 2 : ℕ) = 36 := by norm_num
      rwa [h36] at hPd
    have hc := hPd'.card_eq
      (Nat.div_pos (Nat.le_of_dvd (by norm_num) hdvd') (by omega))
    exact ⟨d, hdvd', hgt, hc, hPd'⟩
  -- a packet of card 9 exists (else all cards even, sum even ≠ 13)
  have h9 : ∃ P ∈ Ps, P.card = 9 := by
    by_contra hno
    have hall : ∀ P ∈ Ps, 2 ∣ P.card := by
      intro P hP
      obtain ⟨d, hdvd, hgt, hc, _⟩ := hcards P hP
      have hne : d ≠ 9 := by
        intro hcon
        exact hno ⟨P, hP, by rw [hc, hcon]⟩
      have hle : d ≤ 36 := Nat.le_of_dvd (by norm_num) hdvd
      rw [hc]
      revert hne hdvd
      interval_cases d <;> decide
    have heven : 2 ∣ ∑ P ∈ Ps, P.card := Finset.dvd_sum hall
    rw [hsum13] at heven
    norm_num at heven
  obtain ⟨P₉, hP₉, hcardP₉⟩ := h9
  -- the rest sums to 4, so it is one packet of card 4
  have hrest : ∑ P ∈ Ps.erase P₉, P.card = 4 := by
    have h := Finset.add_sum_erase Ps Finset.card hP₉
    omega
  have hne4 : (Ps.erase P₉).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hrest
    omega
  obtain ⟨P₄, hP₄⟩ := hne4
  have hP₄mem : P₄ ∈ Ps := Finset.mem_of_mem_erase hP₄
  have hcardP₄ : P₄.card = 4 := by
    obtain ⟨d, hdvd, hgt, hc, _⟩ := hcards P₄ hP₄mem
    have hle : P₄.card ≤ 4 := hrest ▸
      Finset.single_le_sum (f := Finset.card) (fun i _ => Nat.zero_le _) hP₄
    omega
  -- pin the packets' divisors and bases
  obtain ⟨d₉, hdvd₉, _, hc₉, hPd₉⟩ := hcards P₉ hP₉
  obtain ⟨d₄, hdvd₄, _, hc₄, hPd₄⟩ := hcards P₄ hP₄mem
  have hd₉ : d₉ = 9 := by omega
  have hd₄ : d₄ = 4 := by omega
  subst hd₉ hd₄
  -- disjointness, recorded before exposing the coset shapes
  have hd : Disjoint P₉ P₄ :=
    hdisj (Finset.mem_coe.mpr hP₉) (Finset.mem_coe.mpr hP₄mem)
      (Finset.ne_of_mem_erase hP₄).symm
  obtain ⟨r, hr, rfl⟩ := hPd₉
  obtain ⟨r', hr', rfl⟩ := hPd₄
  norm_num at hr hr'
  -- the CRT witness x ≡ r (mod 4), x ≡ r' (mod 9) lies in both cosets
  set x : ℕ := (9 * r + 28 * r') % 36 with hx
  have hxlt : x < 36 := Nat.mod_lt _ (by norm_num)
  have hx4 : x % 4 = r := by omega
  have hx9 : x % 9 = r' := by omega
  have hmem₉ : x ∈ DeBruijnWindowedLaw.cosetOf 36 9 r := by
    refine Finset.mem_image.mpr ⟨x / 4, Finset.mem_range.mpr (by omega), ?_⟩
    show r + x / 4 * (36 / 9) = x
    omega
  have hmem₄ : x ∈ DeBruijnWindowedLaw.cosetOf 36 4 r' := by
    refine Finset.mem_image.mpr ⟨x / 9, Finset.mem_range.mpr (by omega), ?_⟩
    show r' + x / 9 * (36 / 4) = x
    omega
  -- contradiction with disjointness
  exact Finset.disjoint_left.mp hd hmem₉ hmem₄

/-- The two-sided data for the refutation: `13` and `23` ARE both sums of
divisors of `36` exceeding `3` — the excluded mass passes the span test from
both ends. -/
example : (13 = 9 + 4 ∧ 9 ∣ 36 ∧ 4 ∣ 36 ∧ 3 < 9 ∧ 3 < 4)
    ∧ (36 - 13 = 9 + 6 + 4 + 4 ∧ 6 ∣ 36 ∧ 3 < 6) := by norm_num

end WindowMassSpan

#print axioms WindowMassSpan.mass_of_combination
#print axioms WindowMassSpan.window_mass_span_two_prime
#print axioms WindowMassSpan.window_min_mass_two_prime
#print axioms WindowMassSpan.window_mass_sharp
#print axioms WindowMassSpan.window_mass_in_prime_span
#print axioms WindowMassSpan.full_range_pow_sum_eq_zero
#print axioms WindowMassSpan.complement_window_vanishes
#print axioms WindowMassSpan.window_mass_two_sided_two_prime
#print axioms WindowMassSpan.two_sided_not_sufficient
