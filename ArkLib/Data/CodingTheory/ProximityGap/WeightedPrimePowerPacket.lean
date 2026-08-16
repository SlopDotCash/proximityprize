/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnPrimePower
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Issue #232 — the WEIGHTED prime-power packet theorem (O95's named brick (i))

O94 closed the indicator (0/1-coefficient) de Bruijn classification at two primes;
O95 measured that the route to the `t > 1` window law — the single named gap between
`MixedRadixTower.two_prime_tower_conditional` and an unconditional mixed-radix tower —
runs through the ℕ-WEIGHTED theory (Lam–Leung, J. Algebra 1996): window exponents `j`
with `gcd(j, n) > 1` produce ℕ-weighted vanishing sums at lower levels, which the
indicator form cannot classify.  This file proves the prime-power layer of that
weighted theory, the ℕ-coefficient generalization of `DeBruijnPrimePower`:

for `n = p^(a+1)`, a primitive `n`-th root `ζ` in a characteristic-zero field, and a
weight function `w : ZMod n → ℕ`,

* `weight_replicated_of_vanishing` / `vanishing_of_weight_replicated` /
  `debruijn_prime_power_weighted` — **the headline iff**:
  `Σ_e w(e)·ζ^e = 0  ⟺  w(e + p^a) = w(e) for ALL e` — the weight function is
  `p^a`-periodic, i.e. the weighted sum is an ℕ-combination of rotated full
  μ_p-packets with multiplicities `w(s)`, `s < p^a`.  The forward direction is the
  O90/O92 machinery run verbatim on the weight polynomial (`packet_dvd_iff_slice_replication`
  is already coefficient-agnostic — the {0,1} restriction in O92 was an instantiation,
  not a hypothesis); the converse is the shift-reindexing of the full `Fintype` sum.
* `vanishing_weight_eq_packet_combination` — **the literal de Bruijn/Lam–Leung
  ℕ-combination**: `weightPoly w = Σ_{s<p^a} C(w s)·X^s·Φ_{p^(a+1)}` with combination
  coefficients literally the weights — nonnegative integers, no sign correction.
* `total_weight_eq_p_mul` / `prime_dvd_total_weight` — **the Lam–Leung weight law at a
  prime power**: `Σ_e w(e) = p · Σ_{s<p^a} w(s)`, hence `|w| ∈ ℕp` — obtained by
  evaluating the combination identity at `X = 1` (`eval_one_cyclotomic_prime_pow`).

Falsified first (`scripts/probes/probe_weighted_packets.py`, exact ℤ[X] arithmetic
mod `Φ_n`, exit 0): the iff, the ℕ-combination reconstruction, and the weight law
EXHAUSTIVELY at `n = 4` (weights ≤ 3; 16 = 4² vanishing), `n = 8` (≤ 2; 81 = 3⁴),
`n = 9` (≤ 2; 27 = 3³) — the vanishing counts are exactly `(W+1)^(p^a)`, the pure
replication freedom — and at `n = 27` by 2000 planted replicated weights (all vanish)
with single-increment toggles (all non-vanishing).  Controls: `p ∣ |w|` WITHOUT
vanishing exists at every level (the weight law is one-way and the theorem does not
over-claim it).

The two-prime weighted census also ran (same probe, Part B): at `n = 12`, ALL 2025
vanishing weight vectors (entries ≤ 2, exhaustive over `3^12`) decompose as
ℕ-combinations of rotated full prime packets — 1272 genuinely mixed, 768 forcing a
coefficient ≥ 2 — so de Bruijn's full ℕ-statement at two primes survives weighted
mixtures; that assembly (weighted thread-split + weighted squarefree base) is the
named next brick, NOT claimed here.
-/

namespace WeightedPrimePowerPacket

open Polynomial Finset

/-! ## The weight polynomial of an ℕ-weight function -/

/-- The rational weight polynomial `Σ_e w(e)·X^(e.val)` of a weight function on
`ZMod n` — the ℕ-coefficient generalization of `DeBruijnPrimePower.indicatorPoly`
(which is the special case `w = 1_S`). -/
noncomputable def weightPoly {n : ℕ} [NeZero n] (w : ZMod n → ℕ) : ℚ[X] :=
  ∑ e : ZMod n, C ((w e : ℚ)) * X ^ (ZMod.val e)

lemma weightPoly_natDegree_lt {n : ℕ} [NeZero n] (w : ZMod n → ℕ) :
    (weightPoly w).natDegree < n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hle : (weightPoly w).natDegree ≤ n - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun e _ => ?_
    refine le_trans (natDegree_C_mul_le _ _) ?_
    rw [natDegree_X_pow]
    have := ZMod.val_lt e
    omega
  omega

/-- The coefficients of the weight polynomial are the weights: `w(m)` for `m < n`,
`0` above. -/
lemma weightPoly_coeff {n : ℕ} [NeZero n] (w : ZMod n → ℕ) (m : ℕ) :
    (weightPoly w).coeff m = if m < n then ((w ((m : ℕ) : ZMod n) : ℚ)) else 0 := by
  classical
  rw [weightPoly, finset_sum_coeff]
  by_cases hm : m < n
  · rw [if_pos hm]
    rw [Finset.sum_eq_single_of_mem ((m : ℕ) : ZMod n) (Finset.mem_univ _)]
    · rw [coeff_C_mul, coeff_X_pow, if_pos (ZMod.val_cast_of_lt hm).symm, mul_one]
    · intro e _ hne
      rw [coeff_C_mul, coeff_X_pow, if_neg, mul_zero]
      intro hcon
      exact hne (by rw [← ZMod.natCast_rightInverse e, ← hcon])
  · rw [if_neg hm]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [coeff_C_mul, coeff_X_pow, if_neg, mul_zero]
    intro hcon
    have := ZMod.val_lt e
    omega

lemma weightPoly_coeff_of_lt {n : ℕ} [NeZero n] (w : ZMod n → ℕ) {m : ℕ}
    (hm : m < n) :
    (weightPoly w).coeff m = ((w ((m : ℕ) : ZMod n) : ℚ)) := by
  rw [weightPoly_coeff, if_pos hm]

lemma aeval_weightPoly {L : Type*} [Field L] [CharZero L] {n : ℕ} [NeZero n]
    (w : ZMod n → ℕ) (ζ : L) :
    aeval ζ (weightPoly w) = ∑ e : ZMod n, (w e : L) * ζ ^ (ZMod.val e) := by
  rw [weightPoly, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_mul, map_pow, aeval_X, aeval_C]
  norm_num

/-! ## Vanishing gives cyclotomic divisibility (every level `n`) -/

/-- **The weighted entry point**: a vanishing ℕ-weighted sum at a primitive `n`-th
root of unity makes the weight polynomial divisible by `Φ_n` over ℚ — the O92
`cyclotomic_dvd_indicatorPoly_of_vanishing` pattern, coefficient-agnostic.  Stated
at every `n`; composite-level weighted wiring can reuse it verbatim. -/
theorem cyclotomic_dvd_weightPoly_of_vanishing {L : Type*} [Field L] [CharZero L]
    {n : ℕ} [NeZero n] {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    {w : ZMod n → ℕ} (hsum : ∑ e : ZMod n, (w e : L) * ζ ^ (ZMod.val e) = 0) :
    cyclotomic n ℚ ∣ weightPoly w := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [cyclotomic_eq_minpoly_rat hζ hn]
  exact minpoly.dvd ℚ ζ (by rw [aeval_weightPoly]; exact hsum)

/-! ## The headline: the weighted de Bruijn iff at a single prime power -/

/-- **Forward headline — the weighted packet theorem at a prime power.**  For
`n = p^(a+1)`, a vanishing ℕ-weighted sum forces the weight function to be
`p^a`-periodic: `w(e + p^a) = w(e)` for ALL `e` — i.e. the weighted sum is an
ℕ-combination of rotated full μ_p-packets with multiplicities `w(s)`, `s < p^a`.

Mechanism (the one-shot O90 application, exactly as in
`DeBruijnPrimePower.closed_add_pow_of_vanishing` — O90's
`packet_dvd_iff_slice_replication` never assumed {0,1} coefficients): the weight
polynomial has degree `< p·p^a` and is divisible by `Φ_{p^(a+1)} = packet p p^a`,
so its coefficients are `p`-fold slice-replicated — the weight at `e` equals the
weight at `e + p^a`. -/
theorem weight_replicated_of_vanishing {L : Type*} [Field L] [CharZero L]
    {p a : ℕ} [NeZero (p ^ (a + 1))] (hp : p.Prime) {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ (a + 1)))
    {w : ZMod (p ^ (a + 1)) → ℕ}
    (hsum : ∑ e : ZMod (p ^ (a + 1)), (w e : L) * ζ ^ (ZMod.val e) = 0) :
    ∀ e : ZMod (p ^ (a + 1)),
      w (e + ((p ^ a : ℕ) : ZMod (p ^ (a + 1)))) = w e := by
  classical
  have hq : 0 < p ^ a := pow_pos hp.pos a
  have hn : 0 < p ^ (a + 1) := pow_pos hp.pos _
  -- divisibility by the packet
  have hdvd : PacketCombinationDivisibility.packet ℚ p (p ^ a) ∣ weightPoly w := by
    rw [← PacketCombinationDivisibility.cyclotomic_prime_pow_eq_packet hp]
    exact cyclotomic_dvd_weightPoly_of_vanishing hζ hsum
  have hdeg : (weightPoly w).natDegree < p * p ^ a := by
    have h := weightPoly_natDegree_lt (n := p ^ (a + 1)) w
    have h2 : p ^ (a + 1) = p * p ^ a := pow_succ' p a
    omega
  -- O90: slice replication of the WEIGHT coefficients (coefficient-agnostic)
  have hslice := (PacketCombinationDivisibility.packet_dvd_iff_slice_replication
      hp.pos hq hdeg).mp hdvd
  intro e
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
  -- weight value w(e) at coefficient m
  have hcm : (weightPoly w).coeff m = ((w e : ℚ)) := by
    rw [weightPoly_coeff_of_lt w hmn, hcast]
  -- slice down to the bottom slice and back up to the shifted digit
  have hbot : (weightPoly w).coeff (m % q) = ((w e : ℚ)) := by
    have h1 := hslice (m / q) ht (m % q) hs
    rw [Nat.div_add_mod' m q] at h1
    exact h1.symm.trans hcm
  set t2 : ℕ := (m / q + 1) % p with ht2def
  have ht2 : t2 < p := Nat.mod_lt _ hp.pos
  have hc2 : (weightPoly w).coeff (t2 * q + m % q) = ((w e : ℚ)) :=
    (hslice t2 ht2 (m % q) hs).trans hbot
  have hlt2 : t2 * q + m % q < p ^ (a + 1) := by
    have h1 : t2 * q + q ≤ p * q := by
      calc t2 * q + q = (t2 + 1) * q := by ring
        _ ≤ p * q := Nat.mul_le_mul_right q (by omega)
    have h2 : p ^ (a + 1) = p * q := by rw [hqdef, ← pow_succ']
    omega
  -- the weight at the shifted exponent equals w(e)
  have hval : ((w (((t2 * q + m % q : ℕ) : ZMod (p ^ (a + 1)))) : ℚ)) = ((w e : ℚ)) := by
    rw [← weightPoly_coeff_of_lt w hlt2]
    exact hc2
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
      _ = ((t2 * q + (m / q + 1) / p * (p * q) + m % q : ℕ)
            : ZMod (p ^ (a + 1))) := by push_cast; ring
      _ = (((m / q + 1) * q + m % q : ℕ) : ZMod (p ^ (a + 1))) := by rw [hsplit]
      _ = ((m + q : ℕ) : ZMod (p ^ (a + 1))) := by rw [hnat]
      _ = e + ((q : ℕ) : ZMod (p ^ (a + 1))) := by
          rw [Nat.cast_add, hcast]
  rw [hfinal] at hval
  exact_mod_cast hval

/-- **The converse**: `p^a`-periodicity of the weight function forces the weighted
sum to vanish — reindexing the full `Fintype` sum by the shift bijection multiplies
it by `ζ^(p^a) ≠ 1`. -/
theorem vanishing_of_weight_replicated {L : Type*} [Field L] [CharZero L]
    {p a : ℕ} [NeZero (p ^ (a + 1))] (hp : p.Prime) {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ (a + 1)))
    {w : ZMod (p ^ (a + 1)) → ℕ}
    (hrep : ∀ e : ZMod (p ^ (a + 1)),
      w (e + ((p ^ a : ℕ) : ZMod (p ^ (a + 1)))) = w e) :
    ∑ e : ZMod (p ^ (a + 1)), (w e : L) * ζ ^ (ZMod.val e) = 0 := by
  classical
  have hq : 0 < p ^ a := pow_pos hp.pos a
  have hn : 0 < p ^ (a + 1) := pow_pos hp.pos _
  set qz : ZMod (p ^ (a + 1)) := ((p ^ a : ℕ) : ZMod (p ^ (a + 1))) with hqz
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
  have hcomp := Equiv.sum_comp (Equiv.addRight qz)
    (fun x : ZMod (p ^ (a + 1)) => (w x : L) * ζ ^ (ZMod.val x))
  simp only [Equiv.coe_addRight] at hcomp
  have hre : (∑ e : ZMod (p ^ (a + 1)), (w e : L) * ζ ^ (ZMod.val e))
      = (∑ e : ZMod (p ^ (a + 1)), (w e : L) * ζ ^ (ZMod.val e)) * ζ ^ (p ^ a) := by
    calc (∑ e : ZMod (p ^ (a + 1)), (w e : L) * ζ ^ (ZMod.val e))
        = ∑ e : ZMod (p ^ (a + 1)), (w (e + qz) : L) * ζ ^ (ZMod.val (e + qz)) :=
          hcomp.symm
      _ = ∑ e : ZMod (p ^ (a + 1)), (w e : L) * (ζ ^ (ZMod.val e) * ζ ^ (p ^ a)) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [hrep e, hterm e]
      _ = (∑ e : ZMod (p ^ (a + 1)), (w e : L) * ζ ^ (ZMod.val e)) * ζ ^ (p ^ a) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun e _ => by ring
  have hne : ζ ^ (p ^ a) ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt hq.ne'
      (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self a))
  have hzero : (∑ e : ZMod (p ^ (a + 1)), (w e : L) * ζ ^ (ZMod.val e))
      * (ζ ^ (p ^ a) - 1) = 0 := by
    rw [mul_sub, mul_one, ← hre, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hne

/-- **The weighted de Bruijn / Lam–Leung iff at a single prime power**: an
ℕ-weighted sum of `p^(a+1)`-th roots of unity vanishes IFF the weight function is
`p^a`-periodic — iff the sum is an ℕ-combination of rotated full μ_p-packets. -/
theorem debruijn_prime_power_weighted {L : Type*} [Field L] [CharZero L]
    {p a : ℕ} [NeZero (p ^ (a + 1))] (hp : p.Prime) {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ (a + 1)))
    {w : ZMod (p ^ (a + 1)) → ℕ} :
    (∑ e : ZMod (p ^ (a + 1)), (w e : L) * ζ ^ (ZMod.val e) = 0)
      ↔ ∀ e : ZMod (p ^ (a + 1)),
          w (e + ((p ^ a : ℕ) : ZMod (p ^ (a + 1)))) = w e :=
  ⟨weight_replicated_of_vanishing hp hζ, vanishing_of_weight_replicated hp hζ⟩

/-! ## The literal ℕ-combination and the Lam–Leung weight law -/

/-- **The literal weighted de Bruijn ℕ-combination** (Lam–Leung structure at a prime
power): the weight polynomial of a vanishing ℕ-weighted sum IS the combination
`Σ_{s<p^a} C(w s)·X^s·Φ_{p^(a+1)}` of rotated full packets, with combination
coefficients literally the weights — nonnegative integers, the ℕ-span form. -/
theorem vanishing_weight_eq_packet_combination {L : Type*} [Field L] [CharZero L]
    {p a : ℕ} [NeZero (p ^ (a + 1))] (hp : p.Prime) {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ (a + 1)))
    {w : ZMod (p ^ (a + 1)) → ℕ}
    (hsum : ∑ e : ZMod (p ^ (a + 1)), (w e : L) * ζ ^ (ZMod.val e) = 0) :
    weightPoly w = ∑ s ∈ Finset.range (p ^ a),
      C ((w ((s : ℕ) : ZMod (p ^ (a + 1))) : ℚ)) * X ^ s
        * cyclotomic (p ^ (a + 1)) ℚ := by
  have hn : 0 < p ^ (a + 1) := pow_pos hp.pos _
  have h := PacketCombinationDivisibility.cyclotomic_dvd_combination hp
    (cyclotomic_dvd_weightPoly_of_vanishing hζ hsum)
    (weightPoly_natDegree_lt w)
  refine h.trans (Finset.sum_congr rfl fun s hs => ?_)
  have hsn : s < p ^ (a + 1) :=
    lt_of_lt_of_le (Finset.mem_range.mp hs)
      (Nat.pow_le_pow_right hp.pos (Nat.le_succ a))
  rw [weightPoly_coeff_of_lt w hsn]

/-- **The Lam–Leung weight law at a prime power, exact form**: the total weight of a
vanishing ℕ-weighted sum is `p · Σ_{s<p^a} w(s)` — evaluation of the packet
combination at `X = 1` (`Φ_{p^(a+1)}(1) = p`). -/
theorem total_weight_eq_p_mul {L : Type*} [Field L] [CharZero L]
    {p a : ℕ} [NeZero (p ^ (a + 1))] (hp : p.Prime) {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ (a + 1)))
    {w : ZMod (p ^ (a + 1)) → ℕ}
    (hsum : ∑ e : ZMod (p ^ (a + 1)), (w e : L) * ζ ^ (ZMod.val e) = 0) :
    ∑ e : ZMod (p ^ (a + 1)), w e
      = p * ∑ s ∈ Finset.range (p ^ a), w ((s : ℕ) : ZMod (p ^ (a + 1))) := by
  have hn : 0 < p ^ (a + 1) := pow_pos hp.pos _
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomb := vanishing_weight_eq_packet_combination hp hζ hsum
  have heval := congrArg (Polynomial.eval (1 : ℚ)) hcomb
  rw [eval_finset_sum] at heval
  have hL : Polynomial.eval (1 : ℚ) (weightPoly w)
      = ((∑ e : ZMod (p ^ (a + 1)), w e : ℕ) : ℚ) := by
    rw [weightPoly, eval_finset_sum, Nat.cast_sum]
    exact Finset.sum_congr rfl fun e _ => by simp
  have hR : ∀ s ∈ Finset.range (p ^ a),
      Polynomial.eval (1 : ℚ)
          (C ((w ((s : ℕ) : ZMod (p ^ (a + 1))) : ℚ)) * X ^ s
            * cyclotomic (p ^ (a + 1)) ℚ)
        = ((w ((s : ℕ) : ZMod (p ^ (a + 1))) : ℚ)) * p := by
    intro s _
    rw [eval_mul, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one,
        eval_one_cyclotomic_prime_pow]
  rw [hL, Finset.sum_congr rfl hR] at heval
  have key : ((∑ e : ZMod (p ^ (a + 1)), w e : ℕ) : ℚ)
      = ((p * ∑ s ∈ Finset.range (p ^ a),
            w ((s : ℕ) : ZMod (p ^ (a + 1))) : ℕ) : ℚ) := by
    rw [heval]
    push_cast
    rw [← Finset.sum_mul]
    ring
  exact_mod_cast key

/-- **Lam–Leung at a prime power** (the divisibility form of the weight law): the
total weight of any vanishing ℕ-weighted sum of `p^(a+1)`-th roots of unity lies in
`ℕp`. -/
theorem prime_dvd_total_weight {L : Type*} [Field L] [CharZero L]
    {p a : ℕ} [NeZero (p ^ (a + 1))] (hp : p.Prime) {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ (a + 1)))
    {w : ZMod (p ^ (a + 1)) → ℕ}
    (hsum : ∑ e : ZMod (p ^ (a + 1)), (w e : L) * ζ ^ (ZMod.val e) = 0) :
    p ∣ ∑ e : ZMod (p ^ (a + 1)), w e :=
  ⟨_, total_weight_eq_p_mul hp hζ hsum⟩

/-! ## Non-vacuity witnesses

All three faces fired end-to-end at `ℂ`, `n = 2^(1+1) = 4`, `ζ = exp(2πi/4)`, on
GENUINELY weighted data (weights ≥ 2, outside the indicator theory):

* the converse PRODUCES the vanishing weighted sum `2·1 + 2·ζ² = 0` from the
  decidably 2-periodic weight `(2, 0, 2, 0)`;
* the forward direction REFUTES vanishing of the non-replicated weight `(2, 0, 1, 0)`
  — `2 − 1 ≠ 0` falls out of weighted de Bruijn structure alone;
* the weight law REFUTES vanishing of the odd-total weight `(0, 1, 0, 0)` —
  `ζ ≠ 0` derived from `2 ∤ 1`.  Teeth: all three conclusions discriminate. -/

private def tw : ZMod (2 ^ (1 + 1)) → ℕ := fun e => if e = 0 ∨ e = 2 then 2 else 0

private def tw' : ZMod (2 ^ (1 + 1)) → ℕ := fun e =>
  if e = 0 then 2 else if e = 2 then 1 else 0

private def tw'' : ZMod (2 ^ (1 + 1)) → ℕ := fun e => if e = 1 then 1 else 0

private lemma exp_quarter_primitive :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 4)) (2 ^ (1 + 1)) := by
  have h := Complex.isPrimitiveRoot_exp 4 (by norm_num)
  norm_num at h ⊢
  exact h

/-- The converse fired: the weight `(2, 0, 2, 0)` is decidably 2-periodic, so its
weighted sum vanishes — a genuine weight-2 vanishing sum produced by the brick. -/
example : ∑ e : ZMod (2 ^ (1 + 1)),
    (tw e : ℂ) * (Complex.exp (2 * Real.pi * Complex.I / 4)) ^ (ZMod.val e) = 0 := by
  refine vanishing_of_weight_replicated Nat.prime_two exp_quarter_primitive ?_
  decide

/-- The forward direction fired (with teeth): the weight `(2, 0, 1, 0)` is decidably
NOT 2-periodic, so its weighted sum cannot vanish — `2 + ζ² ≠ 0` (i.e. `2 ≠ 1`)
derived from weighted de Bruijn structure alone. -/
example : ¬ (∑ e : ZMod (2 ^ (1 + 1)),
    (tw' e : ℂ) * (Complex.exp (2 * Real.pi * Complex.I / 4)) ^ (ZMod.val e) = 0) :=
  fun h =>
    absurd (weight_replicated_of_vanishing Nat.prime_two exp_quarter_primitive h)
      (by decide)

/-- The weight law fired (with teeth): the weight `(0, 1, 0, 0)` has odd total
weight `1`, so its weighted sum cannot vanish — `ζ ≠ 0` derived from the Lam–Leung
law `2 ∣ |w|` alone. -/
example : ¬ (∑ e : ZMod (2 ^ (1 + 1)),
    (tw'' e : ℂ) * (Complex.exp (2 * Real.pi * Complex.I / 4)) ^ (ZMod.val e) = 0) :=
  fun h => by
    have hdvd := prime_dvd_total_weight Nat.prime_two exp_quarter_primitive h
    rw [show ∑ e : ZMod (2 ^ (1 + 1)), tw'' e = 1 from by decide] at hdvd
    exact absurd hdvd (by norm_num)

end WeightedPrimePowerPacket

#print axioms WeightedPrimePowerPacket.weightPoly_natDegree_lt
#print axioms WeightedPrimePowerPacket.weightPoly_coeff
#print axioms WeightedPrimePowerPacket.aeval_weightPoly
#print axioms WeightedPrimePowerPacket.cyclotomic_dvd_weightPoly_of_vanishing
#print axioms WeightedPrimePowerPacket.weight_replicated_of_vanishing
#print axioms WeightedPrimePowerPacket.vanishing_of_weight_replicated
#print axioms WeightedPrimePowerPacket.debruijn_prime_power_weighted
#print axioms WeightedPrimePowerPacket.vanishing_weight_eq_packet_combination
#print axioms WeightedPrimePowerPacket.total_weight_eq_p_mul
#print axioms WeightedPrimePowerPacket.prime_dvd_total_weight
