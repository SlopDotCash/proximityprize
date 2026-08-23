/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.CRTDoubleSlice

/-!
# Issue #232 — the packet-combination divisibility brick (O87's prime-power recursion seed)

O87 (`DeBruijnIndicatorDisjointness.lean`) closed de Bruijn step (3) at the squarefree
level and measured exactly where it stops: at prime powers the naive dichotomy fails
(168/486 column pairs at `n = 12, 18`), while EVERY CRT column indicator difference is
divisible by `Φ_{p^a}` (probe check C6, 100% there).  The named next brick is the
**packet-combination form** of that divisibility, proven here in full:

a polynomial `d` divisible by the geometric packet
`packet p q = Σ_{t<p} X^(t·q)` (at `q = p^(a-1)` this IS `Φ_{p^a}`, by
`Polynomial.cyclotomic_prime_pow_eq_geom_sum`) with `natDegree d < p·q` satisfies:

* `quotient_natDegree_lt` — **the degree bound**: the quotient `R` (with
  `d = packet·R`) has `natDegree R < q` — degree bookkeeping forced by
  `natDegree packet = (p−1)·q`.
* `quotient_coeff_eq_bottom` + `packet_mul_coeff` — **the bottom-slice identity**:
  `R` is read off the bottom coefficient slice of `d` (`R.coeff s = d.coeff s` for
  `s < q`); the convolution against the sparse packet support never reaches down.
* `packet_dvd_combination` — **the headline**: `d` IS the combination
  `d = Σ_{s<q} C (d.coeff s) · X^s · packet` of rotated packets, with combination
  coefficients literally bottom coefficients of `d` — so any coefficient bound on `d`
  transfers verbatim.  `indicator_diff_packet_combination` instantiates this at
  indicator differences (coefficients in `{−1, 0, 1}`), the O87-named statement.
* `packet_dvd_iff_slice_replication` — the recursion-usable characterization: on
  `natDegree d < p·q`, packet divisibility is EQUIVALENT to the `p`-fold slice
  replication `d.coeff (t·q + s) = d.coeff s` — the form the `a ≥ 2` de Bruijn
  recursion consumes (column differences at level `a` become slice data at `a − 1`).
* `cyclotomic_dvd_combination` / `indicator_diff_cyclotomic_combination` — the bricks
  restated verbatim on `Φ_{p^(a+1)}`, the C6 surface.

The packet statements need NO primality (`p, q ≥ 1` arbitrary; primality only enters
in naming `packet p (p^a) = Φ_{p^(a+1)}`), and no characteristic hypothesis — any
nontrivial integral domain.

Falsified first (`scripts/probes/probe_packet_quotient_coeffs.py`, exact integer
arithmetic, exit 0): exhaustively over all vanishing subsets at `n = 12` (600 column
pairs) and `n = 18` (2000 pairs) — divisibility (O87 C6 re-verified), quotient degree
`< q`, quotient coefficients in `{−1,0,1}`, the bottom-slice identity, and the exact
reconstruction; the FULL `{−1,0,1}^q` quotient cube is realized by real indicator
differences (9/9 at 12, 27/27 at 18).  Controls: without `deg d < p^a` the
shifts-`< q` combination fails (`d = Φ·X^q`; the bottom-slice identity holds for ANY
quotient — the degree bound's job is to make the bottom slice the WHOLE quotient);
exact census: the divisible `{−1,0,1}`-vectors of length `p^a` are EXACTLY
`{Φ·R : R ∈ {−1,0,1}^q}`, count `3^q` (9 of 81; 27 of 19683) — the bijection this
file proves, with non-divisible vectors witnessing that divisibility is load-bearing.

What remains for full de Bruijn (named, not claimed): consume this brick — recurse
down the `q`-adic digits using `packet_dvd_iff_slice_replication` to descend the
column data of `MixedRadixTower` / `DeBruijnIndicatorDisjointness` from level `a` to
`a − 1`, and assemble mixed disjoint packets at composite levels.
-/

namespace PacketCombinationDivisibility

open Polynomial Finset

variable {A : Type*} [CommRing A]

/-- The geometric packet `Σ_{t<p} X^(t·q)`.  At `q = p^(a-1)` (p prime) this is the
prime-power cyclotomic `Φ_{p^a}` (`cyclotomic_prime_pow_eq_packet` below); the
statements here hold for arbitrary `p, q ≥ 1`. -/
noncomputable def packet (A : Type*) [CommRing A] (p q : ℕ) : A[X] :=
  ∑ t ∈ Finset.range p, X ^ (t * q)

/-- The packet's top coefficient (at `(p−1)·q`) is `1`. -/
lemma packet_coeff_top {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (packet A p q).coeff ((p - 1) * q) = 1 := by
  rw [packet, finset_sum_coeff]
  rw [Finset.sum_eq_single (p - 1)]
  · rw [coeff_X_pow, if_pos rfl]
  · intro t _ htne
    rw [coeff_X_pow, if_neg fun h => htne (Nat.eq_of_mul_eq_mul_right hq h.symm)]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

lemma packet_ne_zero [Nontrivial A] {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    packet A p q ≠ 0 := fun h => by
  have h1 := packet_coeff_top (A := A) hp hq
  rw [h, coeff_zero] at h1
  exact zero_ne_one h1

lemma le_natDegree_packet [Nontrivial A] {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (p - 1) * q ≤ (packet A p q).natDegree :=
  le_natDegree_of_ne_zero (by
    rw [packet_coeff_top (A := A) hp hq]; exact one_ne_zero)

lemma natDegree_packet_le [Nontrivial A] {p q : ℕ} :
    (packet A p q).natDegree ≤ (p - 1) * q := by
  refine natDegree_sum_le_of_forall_le _ _ fun t ht => ?_
  rw [natDegree_X_pow]
  exact Nat.mul_le_mul_right q (by have := Finset.mem_range.mp ht; omega)

/-- **The degree bound** (O87's named smallest honest piece): a multiple of the packet
of degree `< p·q` has quotient of degree `< q` — so the quotient lives entirely below
the packet's period and the multiple is a shifts-`< q` combination of rotated packets. -/
theorem quotient_natDegree_lt [IsDomain A] {p q : ℕ} (hq : 0 < q) {d R : A[X]}
    (hmul : d = packet A p q * R) (hdne : d ≠ 0) (hdeg : d.natDegree < p * q) :
    R.natDegree < q := by
  have hRne : R ≠ 0 := fun h => hdne (by rw [hmul, h, mul_zero])
  have hPne : packet A p q ≠ 0 := fun h => hdne (by rw [hmul, h, zero_mul])
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · exact absurd (by simp [packet, h0]) hPne
    · exact h0
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  have hdd : d.natDegree = (packet A (p' + 1) q).natDegree + R.natDegree := by
    rw [hmul, natDegree_mul hPne hRne]
  have hlow : p' * q ≤ (packet A (p' + 1) q).natDegree := by
    have h := le_natDegree_packet (A := A) (p := p' + 1) (q := q) hp hq
    simpa using h
  have h1 : p' * q + R.natDegree ≤ d.natDegree := by
    rw [hdd]; exact Nat.add_le_add_right hlow _
  have h2 : p' * q + R.natDegree < p' * q + q :=
    calc p' * q + R.natDegree ≤ d.natDegree := h1
    _ < (p' + 1) * q := hdeg
    _ = p' * q + q := by ring
  exact Nat.lt_of_add_lt_add_left h2

/-- Slices of a packet multiple (generic-ring form of
`CRTDoubleSlice.packet_slice_coeff`): if `natDegree R < q` then
`(packet p q · R).coeff (i·q + s) = R.coeff s` for `i < p`, `s < q`. -/
lemma packet_mul_coeff {p q : ℕ} {R : A[X]} (hR : R.natDegree < q)
    {i s : ℕ} (hi : i < p) (hs : s < q) :
    (packet A p q * R).coeff (i * q + s) = R.coeff s := by
  unfold packet
  exact CRTDoubleSlice.packet_slice_coeff (K := A) (p := p) (q := q) (R := R)
    hR hi hs

/-- **The bottom-slice identity**: the quotient of a packet multiple is read off the
multiple's bottom coefficient slice (`i = 0` of `packet_mul_coeff`) — the convolution
against the packet's sparse support never reaches down. -/
lemma quotient_coeff_eq_bottom {p q : ℕ} (hp : 0 < p) {R : A[X]}
    (hR : R.natDegree < q) {s : ℕ} (hs : s < q) :
    (packet A p q * R).coeff s = R.coeff s := by
  have h := packet_mul_coeff (A := A) (p := p) (q := q) hR (i := 0) hp hs
  simpa using h

/-- **The packet-combination headline** (O87's named brick): a multiple of the packet
of degree `< p·q` IS the combination `Σ_{s<q} C (d.coeff s) · X^s · packet` of rotated
packets, with combination coefficients literally the bottom coefficients of `d` — any
coefficient bound on `d` transfers verbatim to the combination. -/
theorem packet_dvd_combination [IsDomain A] {p q : ℕ} (hq : 0 < q) {d : A[X]}
    (hdvd : packet A p q ∣ d) (hdeg : d.natDegree < p * q) :
    d = ∑ s ∈ Finset.range q, C (d.coeff s) * X ^ s * packet A p q := by
  by_cases hd0 : d = 0
  · subst hd0
    rw [Finset.sum_eq_zero]
    intro s _
    rw [coeff_zero, map_zero, zero_mul, zero_mul]
  · obtain ⟨R, hR⟩ := hdvd
    have hRdeg : R.natDegree < q := quotient_natDegree_lt hq hR hd0 hdeg
    have hp : 0 < p := by
      rcases Nat.eq_zero_or_pos p with h0 | h0
      · refine absurd ?_ hd0
        rw [hR, h0]
        simp [packet]
      · exact h0
    have hcoeff : ∀ s < q, R.coeff s = d.coeff s := fun s hs => by
      rw [hR, quotient_coeff_eq_bottom hp hRdeg hs]
    have hRsum : R = ∑ s ∈ Finset.range q, C (R.coeff s) * X ^ s := by
      conv_lhs => rw [R.as_sum_range' q hRdeg]
      exact Finset.sum_congr rfl fun s _ => C_mul_X_pow_eq_monomial.symm
    calc d = packet A p q * R := hR
      _ = packet A p q * ∑ s ∈ Finset.range q, C (R.coeff s) * X ^ s := by
          rw [← hRsum]
      _ = ∑ s ∈ Finset.range q, C (R.coeff s) * X ^ s * packet A p q := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
      _ = ∑ s ∈ Finset.range q, C (d.coeff s) * X ^ s * packet A p q :=
          Finset.sum_congr rfl fun s hs => by
            rw [hcoeff s (Finset.mem_range.mp hs)]

/-- **The O87-named statement verbatim**: an indicator difference (coefficients in
`{−1, 0, 1}`) divisible by the packet, of degree `< p·q`, is a BOUNDED-coefficient
ℤ-combination of rotated packets — the combination coefficients are themselves in
`{−1, 0, 1}`. -/
theorem indicator_diff_packet_combination [IsDomain A] {p q : ℕ} (hq : 0 < q)
    {d : A[X]} (hcoeff : ∀ m, d.coeff m ∈ ({-1, 0, 1} : Set A))
    (hdvd : packet A p q ∣ d) (hdeg : d.natDegree < p * q) :
    ∃ r : ℕ → A, (∀ s, r s ∈ ({-1, 0, 1} : Set A)) ∧
      d = ∑ s ∈ Finset.range q, C (r s) * X ^ s * packet A p q :=
  ⟨fun s => d.coeff s, fun s => hcoeff s, packet_dvd_combination hq hdvd hdeg⟩

/-- **The converse**: `p`-fold slice replication (`d.coeff (t·q + s) = d.coeff s`)
below degree `p·q` produces packet divisibility — the witness is the bottom slice. -/
theorem packet_dvd_of_slice_replication [Nontrivial A] {p q : ℕ} (hp : 0 < p)
    (hq : 0 < q) {d : A[X]} (hdeg : d.natDegree < p * q)
    (hslice : ∀ t < p, ∀ s < q, d.coeff (t * q + s) = d.coeff s) :
    packet A p q ∣ d := by
  classical
  set R : A[X] := ∑ s ∈ Finset.range q, C (d.coeff s) * X ^ s with hRdef
  have hRdeg : R.natDegree < q := by
    have hle : R.natDegree ≤ q - 1 := by
      refine natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
      exact le_trans (natDegree_C_mul_X_pow_le _ _)
        (by have := Finset.mem_range.mp hs; omega)
    omega
  have hRcoeff : ∀ s < q, R.coeff s = d.coeff s := by
    intro s hs
    rw [hRdef, finset_sum_coeff]
    rw [Finset.sum_eq_single s]
    · rw [coeff_C_mul_X_pow, if_pos rfl]
    · intro j _ hj
      rw [coeff_C_mul_X_pow, if_neg fun h => hj h.symm]
    · intro h
      exact absurd (Finset.mem_range.mpr hs) h
  refine ⟨R, ?_⟩
  ext m
  by_cases hm : m < p * q
  · have hmq : m / q < p := by
      by_contra h
      push Not at h
      have h1 : p * q ≤ m / q * q := Nat.mul_le_mul_right q h
      have h2 : m / q * q ≤ m := Nat.div_mul_le_self m q
      omega
    have hmod : m % q < q := Nat.mod_lt _ hq
    have h1 : d.coeff m = d.coeff (m % q) := by
      conv_lhs => rw [← Nat.div_add_mod' m q]
      exact hslice _ hmq _ hmod
    have h2 : (packet A p q * R).coeff m = R.coeff (m % q) := by
      conv_lhs => rw [← Nat.div_add_mod' m q]
      exact packet_mul_coeff hRdeg hmq hmod
    rw [h1, h2, hRcoeff _ hmod]
  · push Not at hm
    have hd0 : d.coeff m = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg hm)
    have hprod : (packet A p q * R).natDegree < p * q := by
      have hle : (packet A p q * R).natDegree ≤ (p - 1) * q + (q - 1) :=
        le_trans natDegree_mul_le
          (Nat.add_le_add natDegree_packet_le (by omega))
      obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      have hsq : (p' + 1 - 1) * q = p' * q := by simp
      have hsplit : (p' + 1) * q = p' * q + q := by ring
      omega
    have hp0 : (packet A p q * R).coeff m = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hprod hm)
    rw [hd0, hp0]

/-- **The recursion-usable characterization**: below degree `p·q`, packet divisibility
is EQUIVALENT to `p`-fold slice replication — the form the `a ≥ 2` de Bruijn descent
consumes (column data at level `a` becomes slice data at level `a − 1`). -/
theorem packet_dvd_iff_slice_replication [IsDomain A] {p q : ℕ} (hp : 0 < p)
    (hq : 0 < q) {d : A[X]} (hdeg : d.natDegree < p * q) :
    packet A p q ∣ d ↔ ∀ t < p, ∀ s < q, d.coeff (t * q + s) = d.coeff s := by
  constructor
  · intro hdvd t ht s hs
    by_cases hd0 : d = 0
    · simp [hd0]
    obtain ⟨R, hR⟩ := hdvd
    have hRdeg : R.natDegree < q := quotient_natDegree_lt hq hR hd0 hdeg
    have h1 : d.coeff (t * q + s) = R.coeff s := by
      rw [hR]; exact packet_mul_coeff hRdeg ht hs
    have h2 : d.coeff s = R.coeff s := by
      rw [hR]; exact quotient_coeff_eq_bottom hp hRdeg hs
    rw [h1, h2]
  · exact packet_dvd_of_slice_replication hp hq hdeg

/-! ## The cyclotomic surface: `Φ_{p^(a+1)}` IS the packet at `q = p^a` -/

/-- The prime-power cyclotomic is the geometric packet (exponent-commuted form of
`Polynomial.cyclotomic_prime_pow_eq_geom_sum`). -/
theorem cyclotomic_prime_pow_eq_packet {p a : ℕ} (hp : p.Prime) :
    cyclotomic (p ^ (a + 1)) A = packet A p (p ^ a) := by
  rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hp, packet]
  exact Finset.sum_congr rfl fun t _ => by rw [← pow_mul, Nat.mul_comm]

/-- The packet-combination headline on the C6 surface: a multiple of `Φ_{p^(a+1)}` of
degree `< p^(a+1)` is the combination of rotated `Φ_{p^(a+1)}`-packets with
coefficients the bottom `p^a` coefficients. -/
theorem cyclotomic_dvd_combination [IsDomain A] {p a : ℕ} (hp : p.Prime) {d : A[X]}
    (hdvd : cyclotomic (p ^ (a + 1)) A ∣ d) (hdeg : d.natDegree < p ^ (a + 1)) :
    d = ∑ s ∈ Finset.range (p ^ a),
        C (d.coeff s) * X ^ s * cyclotomic (p ^ (a + 1)) A := by
  rw [cyclotomic_prime_pow_eq_packet hp] at hdvd ⊢
  refine packet_dvd_combination (pow_pos hp.pos a) hdvd ?_
  rwa [pow_succ'] at hdeg

/-- **O87's C6 brick verbatim**: a `{−1,0,1}`-coefficient polynomial (a CRT column
indicator difference) divisible by `Φ_{p^(a+1)}`, of degree `< p^(a+1)`, is a
bounded-coefficient combination of rotated `Φ_{p^(a+1)}`-packets — the combination
coefficients are again in `{−1, 0, 1}`. -/
theorem indicator_diff_cyclotomic_combination [IsDomain A] {p a : ℕ} (hp : p.Prime)
    {d : A[X]} (hcoeff : ∀ m, d.coeff m ∈ ({-1, 0, 1} : Set A))
    (hdvd : cyclotomic (p ^ (a + 1)) A ∣ d) (hdeg : d.natDegree < p ^ (a + 1)) :
    ∃ r : ℕ → A, (∀ s, r s ∈ ({-1, 0, 1} : Set A)) ∧
      d = ∑ s ∈ Finset.range (p ^ a),
          C (r s) * X ^ s * cyclotomic (p ^ (a + 1)) A :=
  ⟨fun s => d.coeff s, fun s => hcoeff s, cyclotomic_dvd_combination hp hdvd hdeg⟩

/-! ## Non-vacuity witnesses

The headline fired end-to-end at the probe's own surface: `p = 2`, `q = 2`
(`packet ℚ 2 2 = Φ₄ = 1 + X²`, the `n = 12` C6 packet), at a REAL measured column
difference shape (`d = 1 − X + X² − X³`, the realized quotient `(1, −1)` from the
probe's Q4 census) and at a rotated packet (`d = X + X³`).  Teeth: `1 + X` is NOT
divisible — the iff genuinely discriminates. -/

lemma packet_two_two : packet ℚ 2 2 = 1 + X ^ 2 := by
  rw [packet, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num

/-- Fired at the rotated packet `d = X·Φ₄`: combination coefficients `(0, 1)` = the
bottom slice. -/
example :
    (X + X ^ 3 : ℚ[X]) = ∑ s ∈ Finset.range 2,
      C ((X + X ^ 3 : ℚ[X]).coeff s) * X ^ s * packet ℚ 2 2 := by
  have hdvd : packet ℚ 2 2 ∣ (X + X ^ 3 : ℚ[X]) :=
    ⟨X, by rw [packet_two_two]; ring⟩
  have hdeg : (X + X ^ 3 : ℚ[X]).natDegree < 2 * 2 :=
    lt_of_le_of_lt (by compute_degree) (by norm_num)
  exact packet_dvd_combination (by norm_num) hdvd hdeg

/-- Fired at the probe's realized quotient `(1, −1)`: the alternating column
difference `1 − X + X² − X³ = (1 − X)·Φ₄` (indicator difference of `{0,2}` vs
`{1,3}`). -/
example :
    (1 - X + X ^ 2 - X ^ 3 : ℚ[X]) = ∑ s ∈ Finset.range 2,
      C ((1 - X + X ^ 2 - X ^ 3 : ℚ[X]).coeff s) * X ^ s * packet ℚ 2 2 := by
  have hdvd : packet ℚ 2 2 ∣ (1 - X + X ^ 2 - X ^ 3 : ℚ[X]) :=
    ⟨1 - X, by rw [packet_two_two]; ring⟩
  have hdeg : (1 - X + X ^ 2 - X ^ 3 : ℚ[X]).natDegree < 2 * 2 :=
    lt_of_le_of_lt (by compute_degree) (by norm_num)
  exact packet_dvd_combination (by norm_num) hdvd hdeg

/-- Teeth: `1 + X` is NOT divisible by `Φ₄` — the slice-replication iff genuinely
discriminates (the probe's Q3 census: 9 of 81 `{−1,0,1}`-vectors are divisible). -/
example : ¬ packet ℚ 2 2 ∣ (1 + X : ℚ[X]) := by
  intro hdvd
  have hdeg : (1 + X : ℚ[X]).natDegree < 2 * 2 :=
    lt_of_le_of_lt (by compute_degree) (by norm_num)
  have h := (packet_dvd_iff_slice_replication (by norm_num) (by norm_num) hdeg).mp
    hdvd 1 (by norm_num) 0 (by norm_num)
  norm_num [coeff_one, coeff_X] at h

end PacketCombinationDivisibility

#print axioms PacketCombinationDivisibility.packet_coeff_top
#print axioms PacketCombinationDivisibility.quotient_natDegree_lt
#print axioms PacketCombinationDivisibility.packet_mul_coeff
#print axioms PacketCombinationDivisibility.quotient_coeff_eq_bottom
#print axioms PacketCombinationDivisibility.packet_dvd_combination
#print axioms PacketCombinationDivisibility.indicator_diff_packet_combination
#print axioms PacketCombinationDivisibility.packet_dvd_of_slice_replication
#print axioms PacketCombinationDivisibility.packet_dvd_iff_slice_replication
#print axioms PacketCombinationDivisibility.cyclotomic_prime_pow_eq_packet
#print axioms PacketCombinationDivisibility.cyclotomic_dvd_combination
#print axioms PacketCombinationDivisibility.indicator_diff_cyclotomic_combination
