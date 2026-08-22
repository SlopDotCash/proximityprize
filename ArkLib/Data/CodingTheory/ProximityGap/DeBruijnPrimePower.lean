/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PacketCombinationDivisibility
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

/-!
# Issue #232 — de Bruijn at a single prime power: vanishing indicator sums of μ_{p^a}
# are disjoint unions of rotated full μ_p-packets (an iff)

O90 (`PacketCombinationDivisibility.lean`) closed with: "what remains is WIRING: run
the recursion down the digits…".  This file is the first wiring deliverable, and a
finding: at a PURE prime power no recursion is needed — ONE application of O90's
`packet_dvd_iff_slice_replication` at the top digit settles the whole level, because
divisibility of the (degree `< p^(a+1)`) indicator polynomial by
`Φ_{p^(a+1)} = packet p p^a` already pins every digit at once.

* `indicatorPoly` + coefficient/degree/evaluation lemmas — the bridge from subset
  sums of roots of unity to the polynomial surface O90 lives on.
* `cyclotomic_dvd_indicatorPoly_of_vanishing` — vanishing at a primitive `n`-th root
  in any characteristic-zero field gives `Φ_n ∣ indicatorPoly S` over ℚ
  (`cyclotomic_eq_minpoly_rat` + `minpoly.dvd`); stated at every `n`, not just prime
  powers — the entry point any future composite-level wiring will reuse.
* `closed_add_pow_of_vanishing` — **the forward headline**: for `n = p^(a+1)` and a
  primitive `n`-th root `ζ`, every subset `S ⊆ ZMod n` with `Σ_{e∈S} ζ^e = 0` is
  closed under `e ↦ e + p^a` — i.e. `S` is a DISJOINT union of rotated full
  μ_p-packets `{s + t·p^a : t < p}`.  This is de Bruijn's ℕ-combination statement at
  a prime power, sharpened to indicators (the combination is a disjoint union); the
  classical single-prime case of Lam–Leung.
* `vanishing_of_closed_add_pow` — **the converse**: closure under `+p^a` forces the
  sum to vanish (shift-reindexing: `T = ζ^(p^a)·T` and `ζ^(p^a) ≠ 1`).
* `debruijn_prime_power` — the iff.
* `vanishing_indicator_eq_packet_combination` — the literal ℕ-combination form:
  `indicatorPoly S = Σ_{s<p^a} C(coeff s)·X^s·Φ_{p^(a+1)}` with all coefficients in
  `{0, 1}` (`indicatorPoly_coeff_mem`) — O90's `cyclotomic_dvd_combination` fired at
  a genuine vanishing subset-sum source.

Falsified first (`scripts/probes/probe_prime_power_descent.py`, exact integer
arithmetic mod `Φ_n`, exit 0): the iff EXHAUSTIVELY at `n = 4, 8, 9, 16` (all `2^n`
subsets; vanishing count is exactly `2^(p^a)`) and sampled at `n = 27, 25` (2000
random closed sets all vanish; 20000 random non-closed sets all non-vanishing — the
closure is load-bearing).  The same probe runs the full two-prime digit-descent
recursion at `n = 12, 18`: every one of the 100/1000 vanishing subsets (O87's
exhaustive census; 99/999 nonempty, O67) decomposes by thread-split + this brick's
base into disjoint genuine packets, the mixture counts 24/432 reproduce O87, and the
disjoint-packet-union family EQUALS the vanishing family (set identity, third
witness).

What remains for the full two-prime theorem (named, not claimed): the THREAD-SPLIT
lemma — for `p² ∣ n`, a vanishing sum at `ζ_n` splits into `p` vanishing thread sums
at `ζ_n^p` (ℚ(ζ_{n/p})-linear independence of `1, ζ, …, ζ^{p-1}`, i.e.
`minpoly ℚ(ζ_{n/p}) ζ_n = X^p − ζ_{n/p}`).  The probe verifies it as an exhaustive
IFF at `n = 12, 18`; no in-tree brick proves it.  With it, the two-prime assembly is
induction + this file's base + O87's squarefree dichotomy.
-/

namespace DeBruijnPrimePower

open Polynomial Finset

/-! ## The indicator polynomial of an exponent subset -/

/-- The rational indicator polynomial `Σ_{e∈S} X^(e.val)` of a subset of `ZMod n`. -/
noncomputable def indicatorPoly {n : ℕ} (S : Finset (ZMod n)) : ℚ[X] :=
  ∑ e ∈ S, X ^ (ZMod.val e)

lemma indicatorPoly_natDegree_lt {n : ℕ} [NeZero n] (S : Finset (ZMod n)) :
    (indicatorPoly S).natDegree < n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hle : (indicatorPoly S).natDegree ≤ n - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun e _ => ?_
    rw [natDegree_X_pow]
    have := ZMod.val_lt e
    omega
  omega

/-- The coefficients of the indicator polynomial are the indicator data: `1` at
`m = e.val` for `e ∈ S` (the cast of `m` lies in `S` and `m < n`), `0` elsewhere. -/
lemma indicatorPoly_coeff {n : ℕ} [NeZero n] (S : Finset (ZMod n)) (m : ℕ) :
    (indicatorPoly S).coeff m
      = if ((m : ZMod n) ∈ S ∧ m < n) then 1 else 0 := by
  classical
  rw [indicatorPoly, finset_sum_coeff]
  by_cases hm : m < n
  · by_cases hmem : ((m : ZMod n)) ∈ S
    · rw [if_pos ⟨hmem, hm⟩]
      rw [Finset.sum_eq_single_of_mem ((m : ZMod n)) hmem]
      · rw [coeff_X_pow, if_pos (ZMod.val_cast_of_lt hm).symm]
      · intro e _ hne
        rw [coeff_X_pow, if_neg]
        intro hcon
        exact hne (by rw [← ZMod.natCast_rightInverse e, ← hcon])
    · rw [if_neg (fun h => hmem h.1)]
      refine Finset.sum_eq_zero fun e he => ?_
      rw [coeff_X_pow, if_neg]
      intro hcon
      exact hmem (by rw [hcon, ZMod.natCast_rightInverse e]; exact he)
  · rw [if_neg (fun h => hm h.2)]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [coeff_X_pow, if_neg]
    intro hcon
    have := ZMod.val_lt e
    omega

/-- Indicator coefficients lie in `{0, 1}` — the formal content of "the packet
combination below is an ℕ-combination". -/
lemma indicatorPoly_coeff_mem {n : ℕ} [NeZero n] (S : Finset (ZMod n)) (m : ℕ) :
    (indicatorPoly S).coeff m ∈ ({0, 1} : Set ℚ) := by
  rw [indicatorPoly_coeff]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

lemma aeval_indicatorPoly {L : Type*} [Field L] [CharZero L] {n : ℕ}
    (S : Finset (ZMod n)) (ζ : L) :
    aeval ζ (indicatorPoly S) = ∑ e ∈ S, ζ ^ (ZMod.val e) := by
  rw [indicatorPoly, map_sum]
  exact Finset.sum_congr rfl fun e _ => by rw [map_pow, aeval_X]

/-! ## Vanishing gives cyclotomic divisibility (every level `n`) -/

/-- **The entry point**: a vanishing indicator sum at a primitive `n`-th root of
unity (any characteristic-zero field) makes the indicator polynomial divisible by
`Φ_n` over ℚ — `Φ_n` is the minimal polynomial (`cyclotomic_eq_minpoly_rat`).
Stated at every `n`; composite-level wiring can reuse it verbatim. -/
theorem cyclotomic_dvd_indicatorPoly_of_vanishing {L : Type*} [Field L] [CharZero L]
    {n : ℕ} (hn : 0 < n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    {S : Finset (ZMod n)} (hsum : ∑ e ∈ S, ζ ^ (ZMod.val e) = 0) :
    cyclotomic n ℚ ∣ indicatorPoly S := by
  rw [cyclotomic_eq_minpoly_rat hζ hn]
  exact minpoly.dvd ℚ ζ (by rw [aeval_indicatorPoly]; exact hsum)

/-! ## The headline: de Bruijn at a single prime power -/

/-- **Forward headline — de Bruijn / Lam–Leung at a prime power, disjoint-packet
form.**  For `n = p^(a+1)`, a primitive `n`-th root `ζ` in a characteristic-zero
field, and a subset `S ⊆ ZMod n` with vanishing indicator sum `Σ_{e∈S} ζ^e = 0`,
the set `S` is closed under `e ↦ e + p^a` — equivalently, `S` is a DISJOINT union
of rotated full μ_p-packets `{s + t·p^a : t < p}`.

Mechanism (the one-shot O90 application): the indicator polynomial has degree
`< p·p^a` and is divisible by `Φ_{p^(a+1)} = packet p p^a`, so by
`PacketCombinationDivisibility.packet_dvd_iff_slice_replication` its coefficients
are `p`-fold slice-replicated — the indicator value at `e` equals the value at
`e + p^a`.  No digit recursion is needed at a pure prime power. -/
theorem closed_add_pow_of_vanishing {L : Type*} [Field L] [CharZero L]
    {p a : ℕ} (hp : p.Prime) {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ (a + 1)))
    {S : Finset (ZMod (p ^ (a + 1)))} (hsum : ∑ e ∈ S, ζ ^ (ZMod.val e) = 0) :
    ∀ e ∈ S, e + ((p ^ a : ℕ) : ZMod (p ^ (a + 1))) ∈ S := by
  classical
  have hq : 0 < p ^ a := pow_pos hp.pos a
  have hn : 0 < p ^ (a + 1) := pow_pos hp.pos _
  haveI : NeZero (p ^ (a + 1)) := ⟨hn.ne'⟩
  -- divisibility by the packet
  have hdvd : PacketCombinationDivisibility.packet ℚ p (p ^ a) ∣ indicatorPoly S := by
    rw [← PacketCombinationDivisibility.cyclotomic_prime_pow_eq_packet hp]
    exact cyclotomic_dvd_indicatorPoly_of_vanishing hn hζ hsum
  have hdeg : (indicatorPoly S).natDegree < p * p ^ a := by
    have h := indicatorPoly_natDegree_lt (n := p ^ (a + 1)) S
    have h2 : p ^ (a + 1) = p * p ^ a := pow_succ' p a
    omega
  -- O90: slice replication of the indicator coefficients
  have hslice := (PacketCombinationDivisibility.packet_dvd_iff_slice_replication
      hp.pos hq hdeg).mp hdvd
  intro e he
  set q : ℕ := p ^ a with hqdef
  set m : ℕ := ZMod.val e with hm
  have hmn : m < p ^ (a + 1) := ZMod.val_lt e
  have hmlt : m < p * q := by
    have h2 : p ^ (a + 1) = p * q := by rw [hqdef, ← pow_succ']
    omega
  have ht : m / q < p := by
    by_contra h
    have h' : p ≤ m / q := Nat.le_of_not_lt h
    have h1 : p * q ≤ m / q * q := Nat.mul_le_mul_right q h'
    have h2 : m / q * q ≤ m := Nat.div_mul_le_self m q
    omega
  have hs : m % q < q := Nat.mod_lt _ hq
  have hcast : ((m : ℕ) : ZMod (p ^ (a + 1))) = e := by
    rw [hm]; exact ZMod.natCast_rightInverse e
  -- indicator value 1 at m
  have hcm : (indicatorPoly S).coeff m = 1 := by
    rw [indicatorPoly_coeff, if_pos ⟨by rw [hcast]; exact he, hmn⟩]
  -- slice down to the bottom slice and back up to the shifted digit
  have hbot : (indicatorPoly S).coeff (m % q) = 1 := by
    have h1 := hslice (m / q) ht (m % q) hs
    rw [Nat.div_add_mod' m q] at h1
    exact h1.symm.trans hcm
  set t2 : ℕ := (m / q + 1) % p with ht2def
  have ht2 : t2 < p := Nat.mod_lt _ hp.pos
  have hc2 : (indicatorPoly S).coeff (t2 * q + m % q) = 1 :=
    (hslice t2 ht2 (m % q) hs).trans hbot
  -- membership of the shifted exponent
  have hlt2 : t2 * q + m % q < p ^ (a + 1) := by
    have h1 : t2 * q + q ≤ p * q := by
      calc t2 * q + q = (t2 + 1) * q := by ring
        _ ≤ p * q := Nat.mul_le_mul_right q (by omega)
    have h2 : p ^ (a + 1) = p * q := by rw [hqdef, ← pow_succ']
    omega
  have hmem : ((t2 * q + m % q : ℕ) : ZMod (p ^ (a + 1))) ∈ S := by
    by_contra hcon
    rw [indicatorPoly_coeff, if_neg (fun h => hcon h.1)] at hc2
    norm_num at hc2
  -- the shifted exponent IS `e + p^a` in `ZMod (p^(a+1))`
  have hnat : (m / q + 1) * q + m % q = m + q := by
    calc (m / q + 1) * q + m % q = (m / q * q + m % q) + q := by ring
      _ = m + q := by rw [Nat.div_add_mod' m q]
  have hsplit : t2 * q + (m / q + 1) / p * (p * q) = (m / q + 1) * q := by
    calc t2 * q + (m / q + 1) / p * (p * q)
        = ((m / q + 1) % p + p * ((m / q + 1) / p)) * q := by rw [ht2def]; ring
      _ = (m / q + 1) * q := by rw [Nat.mod_add_div]
  have hz : (((m / q + 1) / p * (p * q) : ℕ) : ZMod (p ^ (a + 1))) = 0 := by
    have hpq : ((p * q : ℕ) : ZMod (p ^ (a + 1))) = 0 := by
      have h : (p * q : ℕ) = p ^ (a + 1) := by rw [hqdef, ← pow_succ']
      rw [h]
      exact ZMod.natCast_self _
    rw [Nat.cast_mul, hpq, mul_zero]
  have hfinal : ((t2 * q + m % q : ℕ) : ZMod (p ^ (a + 1)))
      = e + ((q : ℕ) : ZMod (p ^ (a + 1))) := by
    calc ((t2 * q + m % q : ℕ) : ZMod (p ^ (a + 1)))
        = ((t2 * q : ℕ) : ZMod (p ^ (a + 1)))
            + (((m / q + 1) / p * (p * q) : ℕ) : ZMod (p ^ (a + 1)))
            + ((m % q : ℕ) : ZMod (p ^ (a + 1))) := by
          rw [hz, add_zero, Nat.cast_add]
      _ = ((t2 * q + (m / q + 1) / p * (p * q) + m % q : ℕ) : ZMod (p ^ (a + 1))) := by push_cast; ring
      _ = (((m / q + 1) * q + m % q : ℕ) : ZMod (p ^ (a + 1))) := by rw [hsplit]
      _ = ((m + q : ℕ) : ZMod (p ^ (a + 1))) := by rw [hnat]
      _ = e + ((q : ℕ) : ZMod (p ^ (a + 1))) := by
          rw [Nat.cast_add, hcast]
  rwa [hfinal] at hmem

/-- **The converse**: closure under `e ↦ e + p^a` forces the indicator sum to
vanish — reindexing the sum by the shift bijection multiplies it by
`ζ^(p^a) ≠ 1`. -/
theorem vanishing_of_closed_add_pow {L : Type*} [Field L] [CharZero L]
    {p a : ℕ} (hp : p.Prime) {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ (a + 1)))
    {S : Finset (ZMod (p ^ (a + 1)))}
    (hclosed : ∀ e ∈ S, e + ((p ^ a : ℕ) : ZMod (p ^ (a + 1))) ∈ S) :
    ∑ e ∈ S, ζ ^ (ZMod.val e) = 0 := by
  classical
  have hq : 0 < p ^ a := pow_pos hp.pos a
  have hn : 0 < p ^ (a + 1) := pow_pos hp.pos _
  haveI : NeZero (p ^ (a + 1)) := ⟨hn.ne'⟩
  set qz : ZMod (p ^ (a + 1)) := ((p ^ a : ℕ) : ZMod (p ^ (a + 1))) with hqz
  have hinj : Function.Injective (fun e : ZMod (p ^ (a + 1)) => e + qz) :=
    add_left_injective qz
  have himg : S.image (fun e => e + qz) = S :=
    Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hclosed)
      (le_of_eq (Finset.card_image_of_injective S hinj).symm)
  have horder : orderOf ζ = p ^ (a + 1) := hζ.eq_orderOf.symm
  have hmod : ∀ k : ℕ, ζ ^ (k % p ^ (a + 1)) = ζ ^ k := by
    intro k
    rw [← horder]
    exact pow_mod_orderOf ζ k
  have hterm : ∀ e : ZMod (p ^ (a + 1)),
      ζ ^ (ZMod.val (e + qz)) = ζ ^ (ZMod.val e) * ζ ^ (p ^ a) := by
    intro e
    have h2 : ζ ^ (ZMod.val qz) = ζ ^ (p ^ a) := by
      rw [hqz, ZMod.val_natCast]
      exact hmod (p ^ a)
    rw [ZMod.val_add, hmod (ZMod.val e + ZMod.val qz), pow_add, h2]
  have hre : ∑ e ∈ S, ζ ^ (ZMod.val e)
      = (∑ e ∈ S, ζ ^ (ZMod.val e)) * ζ ^ (p ^ a) := by
    calc ∑ e ∈ S, ζ ^ (ZMod.val e)
        = ∑ e ∈ S.image (fun e => e + qz), ζ ^ (ZMod.val e) := by rw [himg]
      _ = ∑ e ∈ S, ζ ^ (ZMod.val (e + qz)) :=
          Finset.sum_image (fun x _ y _ h => hinj h)
      _ = ∑ e ∈ S, ζ ^ (ZMod.val e) * ζ ^ (p ^ a) :=
          Finset.sum_congr rfl fun e _ => hterm e
      _ = (∑ e ∈ S, ζ ^ (ZMod.val e)) * ζ ^ (p ^ a) := by
          rw [Finset.sum_mul]
  have hne : ζ ^ (p ^ a) ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt hq.ne'
      (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self a))
  by_contra hT
  apply hne
  have h1 : (∑ e ∈ S, ζ ^ (ZMod.val e)) * 1
      = (∑ e ∈ S, ζ ^ (ZMod.val e)) * ζ ^ (p ^ a) := by
    rw [mul_one]; exact hre
  exact (mul_left_cancel₀ hT h1).symm

/-- **De Bruijn at a single prime power, as an iff** (Lam–Leung single-prime case,
indicator form): a subset sum of `p^(a+1)`-th roots of unity vanishes IFF the
exponent set is closed under `e ↦ e + p^a` — i.e. iff it is a disjoint union of
rotated full μ_p-packets. -/
theorem debruijn_prime_power {L : Type*} [Field L] [CharZero L]
    {p a : ℕ} (hp : p.Prime) {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ (a + 1)))
    {S : Finset (ZMod (p ^ (a + 1)))} :
    (∑ e ∈ S, ζ ^ (ZMod.val e) = 0)
      ↔ ∀ e ∈ S, e + ((p ^ a : ℕ) : ZMod (p ^ (a + 1))) ∈ S :=
  ⟨closed_add_pow_of_vanishing hp hζ, vanishing_of_closed_add_pow hp hζ⟩

/-- **The literal ℕ-combination form** (de Bruijn 1953 at a prime power): the
indicator polynomial of a vanishing subset IS the combination
`Σ_{s<p^a} C(coeff s)·X^s·Φ_{p^(a+1)}` of rotated full packets, with combination
coefficients in `{0, 1}` (`indicatorPoly_coeff_mem`) — O90's
`cyclotomic_dvd_combination` fired at a genuine vanishing subset-sum source. -/
theorem vanishing_indicator_eq_packet_combination {L : Type*} [Field L] [CharZero L]
    {p a : ℕ} (hp : p.Prime) {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ (a + 1)))
    {S : Finset (ZMod (p ^ (a + 1)))} (hsum : ∑ e ∈ S, ζ ^ (ZMod.val e) = 0) :
    indicatorPoly S = ∑ s ∈ Finset.range (p ^ a),
      C ((indicatorPoly S).coeff s) * X ^ s * cyclotomic (p ^ (a + 1)) ℚ := by
  have hn : 0 < p ^ (a + 1) := pow_pos hp.pos _
  haveI : NeZero (p ^ (a + 1)) := ⟨hn.ne'⟩
  exact PacketCombinationDivisibility.cyclotomic_dvd_combination hp
    (cyclotomic_dvd_indicatorPoly_of_vanishing hn hζ hsum)
    (indicatorPoly_natDegree_lt S)

/-! ## Non-vacuity witnesses

Both directions fired end-to-end at `ℂ`, `n = 2^(1+1) = 4`, `ζ = exp(2πi/4)`:
`S = {1, 3}` (a rotated full μ₂-packet: `ζ + ζ³ = i − i = 0`).  The converse
produces the vanishing sum from decidable closure; the forward direction converts a
hypothetical vanishing sum of the NON-closed `S = {0, 1}` into a decidably false
closure — so `1 + i ≠ 0` falls out of the headline.  Teeth: the iff genuinely
discriminates at `n = 4`. -/

private lemma exp_quarter_primitive :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 4)) (2 ^ (1 + 1)) := by
  have h := Complex.isPrimitiveRoot_exp 4 (by norm_num)
  norm_num at h ⊢
  exact h

/-- The converse fired: `{1, 3} ⊆ ZMod 4` is decidably closed under `+2`, so its
indicator sum vanishes — a genuine nonempty vanishing sum produced by the brick. -/
example : ∑ e ∈ ({1, 3} : Finset (ZMod (2 ^ (1 + 1)))),
    (Complex.exp (2 * Real.pi * Complex.I / 4)) ^ (ZMod.val e) = 0 := by
  refine vanishing_of_closed_add_pow Nat.prime_two exp_quarter_primitive ?_
  decide

/-- The forward direction fired (with teeth): `{0, 1}` is decidably NOT closed under
`+2`, so by the headline its indicator sum cannot vanish — `1 + i ≠ 0` derived from
de Bruijn structure alone. -/
example : ¬ (∑ e ∈ ({0, 1} : Finset (ZMod (2 ^ (1 + 1)))),
    (Complex.exp (2 * Real.pi * Complex.I / 4)) ^ (ZMod.val e) = 0) := fun h =>
  absurd (closed_add_pow_of_vanishing Nat.prime_two exp_quarter_primitive h)
    (by decide)

end DeBruijnPrimePower

#print axioms DeBruijnPrimePower.indicatorPoly_natDegree_lt
#print axioms DeBruijnPrimePower.indicatorPoly_coeff
#print axioms DeBruijnPrimePower.indicatorPoly_coeff_mem
#print axioms DeBruijnPrimePower.aeval_indicatorPoly
#print axioms DeBruijnPrimePower.cyclotomic_dvd_indicatorPoly_of_vanishing
#print axioms DeBruijnPrimePower.closed_add_pow_of_vanishing
#print axioms DeBruijnPrimePower.vanishing_of_closed_add_pow
#print axioms DeBruijnPrimePower.debruijn_prime_power
#print axioms DeBruijnPrimePower.vanishing_indicator_eq_packet_combination
