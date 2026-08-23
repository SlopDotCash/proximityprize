/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnIntRelations
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWeightedWindowLaw

/-!
# Issue #232 — THE ℤ-WINDOWED LAW AT EVERY MODULUS (O111)

The O106/O108 windowed laws classified window fibers at TWO-prime-smooth moduli;
their level interfaces fail at three primes over ℕ (the O105 refutation).  Over
ℤ the level classification at every modulus is the Rédei–de Bruijn–Schoenberg
theorem (O110) — and feeding it into the O108 induction yields the windowed law
with **no smoothness restriction**:

* `int_windowed_law` — **the headline iff**: for every `n`, `t < n`, `w : ℕ → ℤ`,
  and `ζ` a primitive `n`-th root of unity in characteristic zero:
  `(∀ j, 1 ≤ j ≤ t → Σ_{e<n} w_e ζ^{je} = 0)  ↔  w` is a ℤ-combination of
  `μ_d`-coset indicators with `d ∣ n`, `d > t`.

Probe-verified before formalization (`scripts/probes/probe_int_windowed_law.py`,
exact ℤ[x]/Φ_n + Smith normal form, exit 0): at `n = 12, 30, 36, 60, 105`
(two- and three-prime, squarefree and not) and 15 `(n, t)` pairs, the `d > t`
coset lattice kills the window, has rank equal to the ℚ-kernel dimension of the
window constraint system, and is saturated — hence equals the full relation
lattice of the window.

The induction step is O108's, with the kill/resonance lemmas transported to ℤ
by positive/negative-part splits and the level classifier discharged by O110 at
every divisor level.  At `t = 1` the law recovers the Rédei–de Bruijn–Schoenberg
theorem itself (`d > 1` cosets are ℕ-combinations of prime packets and
conversely); every `t > 1` at a non-two-prime-smooth modulus is new territory —
no literature statement covers the dense-window fiber there.
-/

namespace DeBruijnIntWindowedLaw

open Finset DeBruijnIntRelations

variable {L : Type*} [Field L]

/-! ## Kill and resonance for ℤ-coset combinations (pos/neg split of O108) -/

/-- Splitting a ℤ-coset-combination sum into its positive and negative parts. -/
private lemma coset_sum_split {n k : ℕ} (A : ℕ → ℤ) (f : ℕ → L) :
    ∑ e ∈ Finset.range n, (A (e % k) : L) * f e
      = (∑ e ∈ Finset.range n, (((A (e % k)).toNat : ℕ) : L) * f e)
        - ∑ e ∈ Finset.range n, ((((-(A (e % k))).toNat : ℕ)) : L) * f e := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← sub_mul]
  congr 1
  have h := Int.toNat_sub_toNat_neg (A (e % k))
  have h2 := congrArg (fun z : ℤ => (z : L)) h
  push_cast at h2
  exact h2.symm

/-- **The `u ∤ j` kill** for ℤ-coefficients. -/
lemma int_packet_pow_sum_eq_zero {n u j : ℕ} (hu : 1 < u) (hun : u ∣ n)
    (hn : 0 < n) {ζ : L} (hζ : IsPrimitiveRoot ζ n) (huj : ¬ u ∣ j) (A : ℕ → ℤ) :
    ∑ e ∈ Finset.range n, (A (e % (n / u)) : L) * ζ ^ (j * e) = 0 := by
  rw [coset_sum_split A (fun e => ζ ^ (j * e))]
  have hpos := DeBruijnWeightedWindowLaw.packet_part_pow_sum_eq_zero hu hun hn hζ
    huj (fun r => (A r).toNat)
  have hneg := DeBruijnWeightedWindowLaw.packet_part_pow_sum_eq_zero hu hun hn hζ
    huj (fun r => (-(A r)).toNat)
  rw [hpos, hneg, sub_zero]

/-- **The resonant sum** for ℤ-coefficients: at `j = u`, the coset combination
contributes `u` times its base sum one level down. -/
lemma int_packet_resonant_sum {n u : ℕ} (hu : 0 < u) (hun : u ∣ n)
    (hn : 0 < n) {ζ : L} (hζ : ζ ^ n = 1) (A : ℕ → ℤ) :
    ∑ e ∈ Finset.range n, (A (e % (n / u)) : L) * ζ ^ (u * e)
      = (u : L) * ∑ r ∈ Finset.range (n / u), (A r : L) * (ζ ^ u) ^ r := by
  rw [coset_sum_split A (fun e => ζ ^ (u * e))]
  have hpos := DeBruijnWeightedWindowLaw.packet_part_resonant_sum hu hun hn hζ
    (fun r => (A r).toNat)
  have hneg := DeBruijnWeightedWindowLaw.packet_part_resonant_sum hu hun hn hζ
    (fun r => (-(A r)).toNat)
  rw [hpos, hneg, ← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← sub_mul]
  congr 1
  have h := Int.toNat_sub_toNat_neg (A r)
  have h2 := congrArg (fun z : ℤ => (z : L)) h
  push_cast at h2
  exact h2

/-! ## The combination predicate and the easy direction -/

/-- `w` is a **ℤ-combination of `μ_d`-coset indicators with `d ∣ n`, `d > t`**
on `[0, n)`. -/
def IsIntWindowCombination (n t : ℕ) (w : ℕ → ℤ) : Prop :=
  ∃ A : ℕ → ℕ → ℤ, ∀ e < n,
    w e = ∑ d ∈ n.divisors.filter (t < ·), A d (e % (n / d))

/-- **⟸ of the ℤ-windowed law**: a `d > t` combination kills the window. -/
theorem int_window_vanishes_of_combination {n t : ℕ} (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) {w : ℕ → ℤ}
    (h : IsIntWindowCombination n t w) :
    ∀ j, 1 ≤ j → j ≤ t →
      ∑ e ∈ Finset.range n, (w e : L) * ζ ^ (j * e) = 0 := by
  intro j hj1 hjt
  obtain ⟨A, hA⟩ := h
  have hswap : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ (j * e)
      = ∑ d ∈ n.divisors.filter (t < ·),
          ∑ e ∈ Finset.range n, (A d (e % (n / d)) : L) * ζ ^ (j * e) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hA e (Finset.mem_range.mp he)]
    push_cast
    rw [Finset.sum_mul]
  rw [hswap]
  refine Finset.sum_eq_zero fun d hd => ?_
  obtain ⟨hmem, htd⟩ := Finset.mem_filter.mp hd
  have hdn : d ∣ n := (Nat.mem_divisors.mp hmem).1
  refine int_packet_pow_sum_eq_zero (by omega) hdn hn hζ ?_ (A d)
  intro hdj
  have := Nat.le_of_dvd (by omega) hdj
  omega

/-! ## The induction step (the O108 step with the O110 level classifier) -/

/-- **One upgrade step**: a window-`t` combination plus the `(t+1)`-st power sum
upgrades to a window-`(t+1)` combination — the Rédei–de Bruijn–Schoenberg
theorem classifies the resonant coefficients one level down. -/
private lemma window_step [CharZero L] {n : ℕ} {ζ : L}
    (hζ : IsPrimitiveRoot ζ n) {t : ℕ} (htn : t + 1 < n) (hdvd : t + 1 ∣ n)
    {w : ℕ → ℤ} (hprev : IsIntWindowCombination n t w)
    (hsum : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ ((t + 1) * e) = 0) :
    IsIntWindowCombination n (t + 1) w := by
  classical
  obtain ⟨A, hA⟩ := hprev
  have hnpos : 0 < n := by omega
  have hτm : (t + 1) * (n / (t + 1)) = n := Nat.mul_div_cancel' hdvd
  have hmpos : 0 < n / (t + 1) :=
    Nat.div_pos (Nat.le_of_dvd hnpos hdvd) (Nat.succ_pos t)
  have hτmem : t + 1 ∈ n.divisors.filter (t < ·) :=
    Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd, hnpos.ne'⟩, by omega⟩
  have hτnot : t + 1 ∉ n.divisors.filter (t + 1 < ·) := by
    intro hmem
    exact absurd (Finset.mem_filter.mp hmem).2 (by omega)
  have hfilter : n.divisors.filter (t < ·)
      = insert (t + 1) (n.divisors.filter (t + 1 < ·)) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_insert, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdn, hne⟩, htd⟩
      rcases Nat.lt_or_ge (t + 1) d with h | h
      · exact Or.inr ⟨⟨hdn, hne⟩, h⟩
      · exact Or.inl (by omega)
    · rintro (rfl | ⟨⟨hdn, hne⟩, htd⟩)
      · exact ⟨Nat.mem_divisors.mp (Finset.mem_filter.mp hτmem).1, by omega⟩
      · exact ⟨⟨hdn, hne⟩, by omega⟩
  -- extract the resonant base sum at level n/(t+1)
  have hswap : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ ((t + 1) * e)
      = ∑ d ∈ n.divisors.filter (t < ·),
          ∑ e ∈ Finset.range n, (A d (e % (n / d)) : L) * ζ ^ ((t + 1) * e) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hA e (Finset.mem_range.mp he)]
    push_cast
    rw [Finset.sum_mul]
  have hkill : ∀ d ∈ n.divisors.filter (t + 1 < ·),
      ∑ e ∈ Finset.range n, (A d (e % (n / d)) : L) * ζ ^ ((t + 1) * e) = 0 := by
    intro d hd
    obtain ⟨hmem, htd⟩ := Finset.mem_filter.mp hd
    have hdn : d ∣ n := (Nat.mem_divisors.mp hmem).1
    refine int_packet_pow_sum_eq_zero (by omega) hdn hnpos hζ ?_ (A d)
    intro hdj
    have := Nat.le_of_dvd (Nat.succ_pos t) hdj
    omega
  have hres : (((t + 1 : ℕ)) : L)
      * ∑ r ∈ Finset.range (n / (t + 1)),
          (A (t + 1) r : L) * (ζ ^ (t + 1)) ^ r = 0 := by
    have h0 := hsum
    rw [hswap, hfilter, Finset.sum_insert hτnot,
      Finset.sum_eq_zero hkill, add_zero,
      int_packet_resonant_sum (Nat.succ_pos t) hdvd hnpos hζ.pow_eq_one
        (A (t + 1))] at h0
    exact h0
  have hbase : ∑ r ∈ Finset.range (n / (t + 1)),
      (A (t + 1) r : L) * (ζ ^ (t + 1)) ^ r = 0 := by
    rcases mul_eq_zero.mp hres with h | h
    · exact absurd h (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero t))
    · exact h
  -- the Rédei–de Bruijn–Schoenberg classification one level down
  have hξ : IsPrimitiveRoot (ζ ^ (t + 1)) (n / (t + 1)) := hζ.pow hnpos hτm.symm
  obtain ⟨C, hC⟩ := (redei_debruijn_schoenberg hmpos hξ (A (t + 1))).mp hbase
  -- fold the level-(n/(t+1)) packets into divisors (t+1)·p of n
  refine ⟨fun d r =>
    (if t + 1 < d then A d r else 0)
      + ∑ p ∈ (n / (t + 1)).primeFactors.filter (fun p => (t + 1) * p = d),
          C p r, ?_⟩
  intro e he
  have hAe := hA e he
  rw [hfilter, Finset.sum_insert hτnot] at hAe
  have hCval : A (t + 1) (e % (n / (t + 1)))
      = ∑ p ∈ (n / (t + 1)).primeFactors,
          C p (e % (n / ((t + 1) * p))) := by
    rw [hC _ (Nat.mod_lt _ hmpos)]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpm : p ∣ n / (t + 1) := Nat.dvd_of_mem_primeFactors hp
    have hmm : n / (t + 1) / p = n / ((t + 1) * p) := Nat.div_div_eq_div_mul n _ _
    rw [← hmm, Nat.mod_mod_of_dvd e (Nat.div_dvd_of_dvd hpm)]
  rw [hCval] at hAe
  rw [hAe]
  rw [Finset.sum_add_distrib]
  have hfirst : ∑ d ∈ n.divisors.filter (t + 1 < ·),
      (if t + 1 < d then A d (e % (n / d)) else 0)
        = ∑ d ∈ n.divisors.filter (t + 1 < ·), A d (e % (n / d)) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [if_pos (Finset.mem_filter.mp hd).2]
  have hsecond : ∑ d ∈ n.divisors.filter (t + 1 < ·),
      ∑ p ∈ (n / (t + 1)).primeFactors.filter (fun p => (t + 1) * p = d),
          C p (e % (n / d))
        = ∑ p ∈ (n / (t + 1)).primeFactors,
            C p (e % (n / ((t + 1) * p))) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun p => (t + 1) * p)
      (fun p hp => ?_) (fun p => C p (e % (n / ((t + 1) * p))))]
    · refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun p hp => ?_
      rw [(Finset.mem_filter.mp hp).2]
    · have hpp := Nat.prime_of_mem_primeFactors hp
      have hpm : p ∣ n / (t + 1) := Nat.dvd_of_mem_primeFactors hp
      refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hnpos.ne'⟩, ?_⟩
      · calc (t + 1) * p ∣ (t + 1) * (n / (t + 1)) := mul_dvd_mul_left _ hpm
          _ = n := hτm
      · exact (Nat.lt_mul_iff_one_lt_right (Nat.succ_pos t)).mpr hpp.one_lt
  rw [hfirst, hsecond]
  ring

/-! ## The induction wrapper and the headline -/

/-- **The forward direction**, by induction on the window length. -/
theorem int_combination_of_window [CharZero L] {n : ℕ}
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (w : ℕ → ℤ) :
    ∀ t, t < n → (∀ j, 1 ≤ j → j ≤ t →
      ∑ e ∈ Finset.range n, (w e : L) * ζ ^ (j * e) = 0) →
      IsIntWindowCombination n t w := by
  intro t
  induction t with
  | zero =>
    intro htn _
    refine ⟨fun d r => if d = 1 then w r else 0, fun e he => ?_⟩
    have h1mem : 1 ∈ n.divisors.filter (0 < ·) :=
      Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (by omega), one_pos⟩
    rw [Finset.sum_eq_single_of_mem 1 h1mem]
    · dsimp only
      rw [if_pos rfl, Nat.div_one, Nat.mod_eq_of_lt he]
    · intro d _ hne
      dsimp only
      rw [if_neg hne]
  | succ t IH =>
    intro htn hwin
    have hprev := IH (by omega) fun j h1 h2 => hwin j h1 (by omega)
    by_cases hdvd : (t + 1) ∣ n
    · exact window_step hζ htn hdvd hprev (hwin _ (Nat.succ_pos t) le_rfl)
    · obtain ⟨A, hA⟩ := hprev
      refine ⟨A, fun e he => ?_⟩
      have hfeq : n.divisors.filter (t + 1 < ·) = n.divisors.filter (t < ·) := by
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨hdn, hne⟩, htd⟩
          exact ⟨⟨hdn, hne⟩, by omega⟩
        · rintro ⟨⟨hdn, hne⟩, htd⟩
          refine ⟨⟨hdn, hne⟩, ?_⟩
          rcases Nat.lt_or_ge (t + 1) d with h | h
          · exact h
          · have hde : d = t + 1 := by omega
            exact absurd (hde ▸ hdn) hdvd
      rw [hfeq]
      exact hA e he

/-- **THE ℤ-WINDOWED LAW AT EVERY MODULUS** (O111): for every `n`, `t < n`,
`w : ℕ → ℤ`, and `ζ` a primitive `n`-th root of unity in characteristic zero,
the power-sum window `1 ≤ j ≤ t` vanishes **iff** `w` is a ℤ-combination of
`μ_d`-coset indicators with `d ∣ n`, `d > t`.  No smoothness restriction; at
`t = 1` this recovers the Rédei–de Bruijn–Schoenberg theorem; for `t > 1` at
non-two-prime-smooth moduli the statement is new. -/
theorem int_windowed_law [CharZero L] {n : ℕ} (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (w : ℕ → ℤ) {t : ℕ} (htn : t < n) :
    (∀ j, 1 ≤ j → j ≤ t →
        ∑ e ∈ Finset.range n, (w e : L) * ζ ^ (j * e) = 0) ↔
      IsIntWindowCombination n t w :=
  ⟨int_combination_of_window hζ w t htn,
    fun h => int_window_vanishes_of_combination hn hζ h⟩

end DeBruijnIntWindowedLaw

#print axioms DeBruijnIntWindowedLaw.int_packet_pow_sum_eq_zero
#print axioms DeBruijnIntWindowedLaw.int_packet_resonant_sum
#print axioms DeBruijnIntWindowedLaw.int_window_vanishes_of_combination
#print axioms DeBruijnIntWindowedLaw.int_combination_of_window
#print axioms DeBruijnIntWindowedLaw.int_windowed_law
