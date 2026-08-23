/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CoprimePacketMinpoly
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWeightedTwoPrime

/-!
# Issue #232 — ℤ-RELATIONS, stage 1 (O109a): the ℤ-weighted de Bruijn
# classification at two-prime moduli, by the shift trick

The Schoenberg/Rédei **relation theorem** says the lattice of ℤ-linear relations
among the `n`-th roots of unity is spanned by the rotated full prime packets —
for EVERY `n`, including 3+-prime moduli where the ℕ-cone (packet
decomposition) form is refuted (O105's witness at `n = 30`).  The ℤ-side door
into 3+-prime territory is therefore open while the ℕ-door is closed.

Probe (`scripts/probes/probe_schoenberg_z_relations.py`, exit 0): the packet
lattice is a saturated sublattice of rank `n − φ(n)` (all Smith invariants `1`)
at `n = 12, 36, 30, 60, 90, 105, 210` — two-, three-, and four-prime moduli,
squarefree and not.

This file lands the **two-prime case** as a corollary of the ℕ-classification
(O103), by the shift trick: given a vanishing ℤ-combination `w`, add `c·𝟙` for
`c` large (the all-ones vector `𝟙` is itself a vanishing combination since
`Σ_{e<n} ζ^e = 0`), classify the resulting ℕ-combination by O103, and subtract
the constant back inside a coefficient function.

* `debruijn_int_two_prime` — **the iff**: `Σ_{e<n} w_e ζ^e = 0  ↔
  ∃ A B : ℕ → ℤ, w_e = A(e % n/p) + B(e % n/q)` on `[0, n)`, `n = p^a·q^b`.
* `packet_part_eq_zero_int` — the ℤ-converse engine (positive/negative-part
  split of the ℕ-engine).

Stages 2–3 (the coprime equal-thread-sum split and the squarefree three-prime
assembly) are the named continuation.
-/

namespace DeBruijnIntRelations

open Finset

variable {L : Type*} [Field L]

/-- A ℤ-weighted root sum splits as the difference of the ℕ-sums of its
positive and negative parts. -/
lemma int_sum_split (w : ℕ → ℤ) (n : ℕ) (f : ℕ → L) :
    ∑ e ∈ Finset.range n, (w e : L) * f e
      = (∑ e ∈ Finset.range n, (((w e).toNat : ℕ) : L) * f e)
        - ∑ e ∈ Finset.range n, ((((-(w e)).toNat : ℕ)) : L) * f e := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← sub_mul]
  congr 1
  have h := Int.toNat_sub_toNat_neg (w e)
  have h2 := congrArg (fun z : ℤ => (z : L)) h
  push_cast at h2
  exact h2.symm

/-- **The ℤ-converse engine**: a ℤ-valued `μ_u`-coset combination kills the full
power sum (positive/negative split of the ℕ-engine). -/
lemma packet_part_eq_zero_int {n u : ℕ} (hu : 1 < u) (hun : u ∣ n) (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (A : ℕ → ℤ) :
    ∑ e ∈ Finset.range n, (A (e % (n / u)) : L) * ζ ^ e = 0 := by
  rw [int_sum_split (fun e => A (e % (n / u))) n (ζ ^ ·)]
  have hpos := DeBruijnWeightedTwoPrime.packet_part_eq_zero (L := L) hu hun hn hζ
    (fun r => (A r).toNat)
  have hneg := DeBruijnWeightedTwoPrime.packet_part_eq_zero (L := L) hu hun hn hζ
    (fun r => (-(A r)).toNat)
  rw [hpos, hneg, sub_zero]

/-- **THE ℤ-WEIGHTED DE BRUIJN CLASSIFICATION AT TWO-PRIME MODULI** (O109a; the
Schoenberg/Rédei relation theorem at `n = p^a·q^b`): a ℤ-combination of `n`-th
roots of unity vanishes iff it is a ℤ-combination of rotated full prime packets
— concretely, iff the weight splits as `A(e % n/p) + B(e % n/q)` with
ℤ-coefficient functions. -/
theorem debruijn_int_two_prime [CharZero L] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ha : 0 < a) (hb : 0 < b)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b)) (w : ℕ → ℤ) :
    (∑ e ∈ Finset.range (p ^ a * q ^ b), (w e : L) * ζ ^ e = 0) ↔
      ∃ A B : ℕ → ℤ, ∀ e < p ^ a * q ^ b,
        w e = A (e % (p ^ (a - 1) * q ^ b)) + B (e % (p ^ a * q ^ (b - 1))) := by
  have hnpos : 0 < p ^ a * q ^ b :=
    Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b)
  have hn1 : 1 < p ^ a * q ^ b :=
    lt_of_lt_of_le (Nat.one_lt_pow ha.ne' hp.one_lt)
      (Nat.le_mul_of_pos_right _ (pow_pos hq.pos b))
  have hdivp : (p ^ a * q ^ b) / p = p ^ (a - 1) * q ^ b := by
    have h2 : p * p ^ (a - 1) = p ^ a := by
      rw [← pow_succ']
      congr 1
      omega
    have hform : p ^ a * q ^ b = p * (p ^ (a - 1) * q ^ b) := by
      rw [← h2]; ring
    rw [hform, Nat.mul_div_cancel_left _ hp.pos]
  have hdivq : (p ^ a * q ^ b) / q = p ^ a * q ^ (b - 1) := by
    have h2 : q * q ^ (b - 1) = q ^ b := by
      rw [← pow_succ']
      congr 1
      omega
    have hform : p ^ a * q ^ b = q * (p ^ a * q ^ (b - 1)) := by
      rw [← h2]; ring
    rw [hform, Nat.mul_div_cancel_left _ hq.pos]
  constructor
  · intro hsum
    -- the shift: w + c·𝟙 is an ℕ-weight with vanishing sum
    set c : ℕ := (Finset.range (p ^ a * q ^ b)).sup (fun e => (w e).natAbs)
      with hc
    have hbound : ∀ e < p ^ a * q ^ b, 0 ≤ w e + c := by
      intro e he
      have h1 : (w e).natAbs ≤ c :=
        Finset.le_sup (f := fun e => (w e).natAbs) (Finset.mem_range.mpr he)
      omega
    have hcast : ∀ e < p ^ a * q ^ b, (((w e + c).toNat : ℕ) : ℤ) = w e + c :=
      fun e he => Int.toNat_of_nonneg (hbound e he)
    have husum : ∑ e ∈ Finset.range (p ^ a * q ^ b),
        (((w e + c).toNat : ℕ) : L) * ζ ^ e = 0 := by
      have hgeom : ∑ e ∈ Finset.range (p ^ a * q ^ b), ζ ^ e = 0 :=
        hζ.geom_sum_eq_zero hn1
      calc ∑ e ∈ Finset.range (p ^ a * q ^ b), (((w e + c).toNat : ℕ) : L) * ζ ^ e
          = ∑ e ∈ Finset.range (p ^ a * q ^ b), ((w e : L) + (c : L)) * ζ ^ e := by
            refine Finset.sum_congr rfl fun e he => ?_
            congr 1
            have h := congrArg (fun z : ℤ => (z : L))
              (hcast e (Finset.mem_range.mp he))
            push_cast at h
            exact h
        _ = (∑ e ∈ Finset.range (p ^ a * q ^ b), (w e : L) * ζ ^ e)
            + (c : L) * ∑ e ∈ Finset.range (p ^ a * q ^ b), ζ ^ e := by
            simp only [add_mul]
            rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = 0 := by rw [hsum, hgeom, mul_zero, add_zero]
    obtain ⟨A', B', hAB⟩ :=
      (DeBruijnWeightedTwoPrime.debruijn_weighted_two_prime hp hq hpq ha hb hζ
        (fun e => (w e + c).toNat)).mp husum
    refine ⟨fun r => (A' r : ℤ) - c, fun r => (B' r : ℤ), fun e he => ?_⟩
    have h1 := hAB e he
    have h2 := hcast e he
    dsimp only
    omega
  · rintro ⟨A, B, hAB⟩
    have hsplit : ∑ e ∈ Finset.range (p ^ a * q ^ b), (w e : L) * ζ ^ e
        = (∑ e ∈ Finset.range (p ^ a * q ^ b),
            (A (e % (p ^ (a - 1) * q ^ b)) : L) * ζ ^ e)
          + ∑ e ∈ Finset.range (p ^ a * q ^ b),
              (B (e % (p ^ a * q ^ (b - 1))) : L) * ζ ^ e := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [hAB e (Finset.mem_range.mp he)]
      push_cast
      ring
    have hA0 := packet_part_eq_zero_int hp.one_lt
      (dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') _) hnpos hζ A
    have hB0 := packet_part_eq_zero_int hq.one_lt
      (dvd_mul_of_dvd_right (dvd_pow_self q hb.ne') _) hnpos hζ B
    rw [hdivp] at hA0
    rw [hdivq] at hB0
    rw [hsplit, hA0, hB0, add_zero]

/-! ## Stage 2 (O109b) — the coprime cyclotomic minpoly at GENERAL orders

The two-prime descent (O93/O94) split threads at a prime whose SQUARE divides the
level; the coprime analogue needs the linear disjointness of `ℚ(ζ_M)` and
`ℚ(ζ_N)` for coprime `M, N` at arbitrary orders.  The totient-tower proof now lives
once in `CoprimePacketMinpoly`; this section keeps the integer-relations-facing theorem
names as wrappers. -/

section CoprimeMinpoly

open Polynomial IntermediateField

/-- **The coprime cyclotomic minpoly, general orders**: for coprime `M, N ≥ 1` and
primitive roots `ξ` (`M`-th), `η` (`N`-th) in a characteristic-zero field, the
minimal polynomial of `η` over `ℚ⟮ξ⟯` is `Φ_N` — linear disjointness of coprime
cyclotomic extensions, with no prime-power restriction.
(Wrapper around `CoprimePacketMinpoly.minpoly_adjoin_coprime_eq_cyclotomic`.) -/
theorem minpoly_adjoin_coprime_eq_cyclotomic [CharZero L] {M N : ℕ}
    (hM : 0 < M) (hN : 0 < N) (hco : Nat.Coprime M N)
    {ξ η : L} (hξ : IsPrimitiveRoot ξ M) (hη : IsPrimitiveRoot η N) :
    minpoly ℚ⟮ξ⟯ η = Polynomial.cyclotomic N ℚ⟮ξ⟯ := by
  exact CoprimePacketMinpoly.minpoly_adjoin_coprime_eq_cyclotomic hM hN hco hξ hη

/-- The degree extraction: `[ℚ(ζ_M)(ζ_N) : ℚ(ζ_M)] = φ(N)` for coprime orders. -/
theorem natDegree_minpoly_adjoin_coprime [CharZero L] {M N : ℕ}
    (hM : 0 < M) (hN : 0 < N) (hco : Nat.Coprime M N)
    {ξ η : L} (hξ : IsPrimitiveRoot ξ M) (hη : IsPrimitiveRoot η N) :
    (minpoly ℚ⟮ξ⟯ η).natDegree = N.totient := by
  exact CoprimePacketMinpoly.natDegree_minpoly_adjoin_coprime hM hN hco hξ hη

end CoprimeMinpoly

/-! ## Stage 3 (O109b) — the coprime thread split: EQUAL thread sums

At a coprime product `n = m·r` (`r` prime), the CRT box `[0,m) × [0,r)` carries
the exponents, and a vanishing ℤ-weighted sum forces all `r` CRT thread sums (at
level `m`) to be EQUAL — not zero, as in the non-coprime O93 split: the minpoly
of the `r`-side root over `ℚ(ζ_m)` is `Φ_r` (degree `r−1`, Stage 2), so
`1, ζ_r, …, ζ_r^{r−2}` are independent and the relation `Σ_i ζ_r^i = 0` welds
the last thread to the others. -/

section CoprimeThreadSplit

open IntermediateField

/-- The canonical CRT representative: the unique `e < m·r` with `e ≡ k [MOD m]`
and `e ≡ i [MOD r]`. -/
def crt (m r : ℕ) (hco : Nat.Coprime m r) (k i : ℕ) : ℕ :=
  (Nat.chineseRemainder hco k i : ℕ) % (m * r)

lemma crt_lt {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hco : Nat.Coprime m r)
    (k i : ℕ) : crt m r hco k i < m * r :=
  Nat.mod_lt _ (Nat.mul_pos hm hr)

lemma crt_modEq_left {m r : ℕ} (hco : Nat.Coprime m r) (k i : ℕ) :
    crt m r hco k i ≡ k [MOD m] :=
  (((Nat.mod_modEq _ (m * r)).of_dvd (dvd_mul_right m r))).trans
    (Nat.chineseRemainder hco k i).2.1

lemma crt_modEq_right {m r : ℕ} (hco : Nat.Coprime m r) (k i : ℕ) :
    crt m r hco k i ≡ i [MOD r] :=
  (((Nat.mod_modEq _ (m * r)).of_dvd (dvd_mul_left r m))).trans
    (Nat.chineseRemainder hco k i).2.2

/-- CRT uniqueness below the modulus. -/
lemma crt_unique {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hco : Nat.Coprime m r)
    {e k i : ℕ} (he : e < m * r) (hk : e ≡ k [MOD m]) (hi : e ≡ i [MOD r]) :
    crt m r hco k i = e := by
  have hmod : crt m r hco k i ≡ e [MOD m * r] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hco).mp
      ⟨(crt_modEq_left hco k i).trans hk.symm,
        (crt_modEq_right hco k i).trans hi.symm⟩
  have h1 : crt m r hco k i % (m * r) = e % (m * r) := hmod
  rwa [Nat.mod_eq_of_lt (crt_lt hm hr hco k i), Nat.mod_eq_of_lt he] at h1

/-- The CRT roundtrip: `crt (e % m) (e % r) = e` for `e < m·r`. -/
lemma crt_roundtrip {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hco : Nat.Coprime m r)
    {e : ℕ} (he : e < m * r) : crt m r hco (e % m) (e % r) = e :=
  crt_unique hm hr hco he (Nat.mod_modEq e m).symm (Nat.mod_modEq e r).symm

/-- A root of `x^n = 1` sees exponents only through their residues mod `n`. -/
lemma pow_eq_pow_of_modEq {x : L} {n a b : ℕ} (hx : x ^ n = 1)
    (h : a ≡ b [MOD n]) : x ^ a = x ^ b := by
  have hred : ∀ c : ℕ, x ^ c = x ^ (c % n) := by
    intro c
    conv_lhs => rw [← Nat.div_add_mod c n]
    rw [pow_add, pow_mul, hx, one_pow, one_mul]
  rw [hred a, hred b, h]

/-- The `r`-side CRT root `ζ^{crt 0 1}` is a primitive `r`-th root of unity. -/
lemma isPrimitiveRoot_crt_right {m r : ℕ} (_hm : 0 < m) (_hr : 0 < r)
    (hco : Nat.Coprime m r) {ζ : L} (hζ : IsPrimitiveRoot ζ (m * r)) :
    IsPrimitiveRoot (ζ ^ crt m r hco 0 1) r := by
  constructor
  · -- (ζ^u)^r = 1: m ∣ u so m·r ∣ u·r
    rw [← pow_mul, hζ.pow_eq_one_iff_dvd]
    have hmu : m ∣ crt m r hco 0 1 :=
      (Nat.modEq_zero_iff_dvd).mp (crt_modEq_left hco 0 1)
    exact mul_dvd_mul_right hmu r
  · -- order exactly r: u ≡ 1 mod r
    intro l hl
    rw [← pow_mul, hζ.pow_eq_one_iff_dvd] at hl
    have hrl : r ∣ crt m r hco 0 1 * l := dvd_trans (dvd_mul_left r m) hl
    have hu1 : crt m r hco 0 1 ≡ 1 [MOD r] := crt_modEq_right hco 0 1
    have hcong : crt m r hco 0 1 * l ≡ l [MOD r] := by
      calc crt m r hco 0 1 * l ≡ 1 * l [MOD r] := hu1.mul_right l
        _ = l := one_mul l
    exact (Nat.modEq_zero_iff_dvd).mp
      ((hcong.symm.trans (Nat.modEq_zero_iff_dvd.mpr hrl)))

/-- The `m`-side CRT root `ζ^{crt 1 0}` is a primitive `m`-th root of unity. -/
lemma isPrimitiveRoot_crt_left {m r : ℕ} (_hm : 0 < m) (_hr : 0 < r)
    (hco : Nat.Coprime m r) {ζ : L} (hζ : IsPrimitiveRoot ζ (m * r)) :
    IsPrimitiveRoot (ζ ^ crt m r hco 1 0) m := by
  constructor
  · rw [← pow_mul, hζ.pow_eq_one_iff_dvd]
    have hrv : r ∣ crt m r hco 1 0 :=
      (Nat.modEq_zero_iff_dvd).mp (crt_modEq_right hco 1 0)
    obtain ⟨c, hc⟩ := hrv
    exact ⟨c, by rw [hc]; ring⟩
  · intro l hl
    rw [← pow_mul, hζ.pow_eq_one_iff_dvd] at hl
    have hml : m ∣ crt m r hco 1 0 * l := dvd_trans (dvd_mul_right m r) hl
    have hv1 : crt m r hco 1 0 ≡ 1 [MOD m] := crt_modEq_left hco 1 0
    have hcong : crt m r hco 1 0 * l ≡ l [MOD m] := by
      calc crt m r hco 1 0 * l ≡ 1 * l [MOD m] := hv1.mul_right l
        _ = l := one_mul l
    exact (Nat.modEq_zero_iff_dvd).mp
      ((hcong.symm.trans (Nat.modEq_zero_iff_dvd.mpr hml)))

/-- The CRT power identity: `ζ^{crt k i} = (ζ^v)^k · (ζ^u)^i` with
`v = crt 1 0`, `u = crt 0 1`. -/
lemma pow_crt_eq {m r : ℕ} (_hm : 0 < m) (_hr : 0 < r) (hco : Nat.Coprime m r)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (m * r)) (k i : ℕ) :
    ζ ^ crt m r hco k i = (ζ ^ crt m r hco 1 0) ^ k * (ζ ^ crt m r hco 0 1) ^ i := by
  rw [← pow_mul, ← pow_mul, ← pow_add]
  refine pow_eq_pow_of_modEq hζ.pow_eq_one ?_
  refine (Nat.modEq_and_modEq_iff_modEq_mul hco).mp ⟨?_, ?_⟩
  · -- mod m: crt k i ≡ k, v ≡ 1, u ≡ 0
    calc crt m r hco k i ≡ k [MOD m] := crt_modEq_left hco k i
      _ = 1 * k + 0 * i := by ring
      _ ≡ crt m r hco 1 0 * k + crt m r hco 0 1 * i [MOD m] :=
          (((crt_modEq_left hco 1 0).symm.mul_right k).add
            ((crt_modEq_left hco 0 1).symm.mul_right i))
  · -- mod r: crt k i ≡ i, v ≡ 0, u ≡ 1
    calc crt m r hco k i ≡ i [MOD r] := crt_modEq_right hco k i
      _ = 0 * k + 1 * i := by ring
      _ ≡ crt m r hco 1 0 * k + crt m r hco 0 1 * i [MOD r] :=
          (((crt_modEq_right hco 1 0).symm.mul_right k).add
            ((crt_modEq_right hco 0 1).symm.mul_right i))

/-- The CRT regrouping of a ℤ-weighted root sum into `r`-side threads of
`m`-side sums. -/
lemma int_sum_crt_regroup {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (hco : Nat.Coprime m r) {ζ : L} (hζ : IsPrimitiveRoot ζ (m * r)) (w : ℕ → ℤ) :
    ∑ e ∈ Finset.range (m * r), (w e : L) * ζ ^ e
      = ∑ i ∈ Finset.range r, (ζ ^ crt m r hco 0 1) ^ i *
          ∑ k ∈ Finset.range m, (w (crt m r hco k i) : L)
            * (ζ ^ crt m r hco 1 0) ^ k := by
  have hrhs : ∑ i ∈ Finset.range r, (ζ ^ crt m r hco 0 1) ^ i *
      ∑ k ∈ Finset.range m, (w (crt m r hco k i) : L) * (ζ ^ crt m r hco 1 0) ^ k
      = ∑ x ∈ Finset.range r ×ˢ Finset.range m,
          (w (crt m r hco x.2 x.1) : L) * ζ ^ crt m r hco x.2 x.1 := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_crt_eq hm hr hco hζ k i]
    ring
  rw [hrhs]
  refine Finset.sum_nbij' (i := fun e => ((e % r, e % m) : ℕ × ℕ))
    (j := fun x => crt m r hco x.2 x.1) ?_ ?_ ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_product]
    exact ⟨Finset.mem_range.mpr (Nat.mod_lt _ hr),
      Finset.mem_range.mpr (Nat.mod_lt _ hm)⟩
  · intro x hx
    rw [Finset.mem_product] at hx
    exact Finset.mem_range.mpr (crt_lt hm hr hco _ _)
  · intro e he
    exact crt_roundtrip hm hr hco (Finset.mem_range.mp he)
  · intro x hx
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
    have h1 : crt m r hco x.2 x.1 % r = x.1 := by
      have := crt_modEq_right hco x.2 x.1
      rwa [Nat.ModEq, Nat.mod_eq_of_lt hx.1] at this
    have h2 : crt m r hco x.2 x.1 % m = x.2 := by
      have := crt_modEq_left hco x.2 x.1
      rwa [Nat.ModEq, Nat.mod_eq_of_lt hx.2] at this
    show (crt m r hco x.2 x.1 % r, crt m r hco x.2 x.1 % m) = x
    rw [h1, h2]
  · intro e he
    rw [crt_roundtrip hm hr hco (Finset.mem_range.mp he)]

/-- **O109b — the coprime equal-thread-sums split**: a vanishing ℤ-weighted sum
at a coprime product `m·r` (`r` prime) has all `r` of its CRT thread sums at
level `m` EQUAL.  (The coprime analogue of the O93 thread split, where thread
sums vanish; here `Φ_r` has degree `r−1` over `ℚ(ζ_m)` — Stage 2 — and the
missing dimension is exactly the relation `Σ_i ζ_r^i = 0` welding the threads.) -/
theorem coprime_thread_sums_eq [CharZero L] {m r : ℕ} (hr : r.Prime) (hm : 0 < m)
    (hco : Nat.Coprime m r) {ζ : L} (hζ : IsPrimitiveRoot ζ (m * r)) (w : ℕ → ℤ)
    (hsum : ∑ e ∈ Finset.range (m * r), (w e : L) * ζ ^ e = 0) :
    ∀ i < r,
      ∑ k ∈ Finset.range m, (w (crt m r hco k i) : L) * (ζ ^ crt m r hco 1 0) ^ k
        = ∑ k ∈ Finset.range m,
            (w (crt m r hco k (r - 1)) : L) * (ζ ^ crt m r hco 1 0) ^ k := by
  classical
  set ζm : L := ζ ^ crt m r hco 1 0 with hζm
  set ζr : L := ζ ^ crt m r hco 0 1 with hζr
  have hprim_m : IsPrimitiveRoot ζm m := isPrimitiveRoot_crt_left hm hr.pos hco hζ
  have hprim_r : IsPrimitiveRoot ζr r := isPrimitiveRoot_crt_right hm hr.pos hco hζ
  set S : ℕ → L := fun i => ∑ k ∈ Finset.range m,
    (w (crt m r hco k i) : L) * ζm ^ k with hS
  -- the regrouped relation and the geometric relation
  have hrel0 : ∑ i ∈ Finset.range r, ζr ^ i * S i = 0 := by
    rw [← int_sum_crt_regroup hm hr.pos hco hζ w]
    exact hsum
  have hgeom : ∑ i ∈ Finset.range r, ζr ^ i = 0 :=
    hprim_r.geom_sum_eq_zero hr.one_lt
  -- subtract the last thread from every thread
  have hdiff : ∑ i ∈ Finset.range r, ζr ^ i * (S i - S (r - 1)) = 0 := by
    have hexpand : ∑ i ∈ Finset.range r, ζr ^ i * (S i - S (r - 1))
        = (∑ i ∈ Finset.range r, ζr ^ i * S i)
          - (∑ i ∈ Finset.range r, ζr ^ i) * S (r - 1) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hexpand, hrel0, hgeom, zero_mul, sub_zero]
  -- the top term is zero; the relation lives on `i < r − 1`
  have hsplit : r = (r - 1) + 1 := (Nat.succ_pred_eq_of_pos hr.pos).symm
  have hdiff' : ∑ i ∈ Finset.range (r - 1), ζr ^ i * (S i - S (r - 1)) = 0 := by
    have h := hdiff
    rw [hsplit, Finset.sum_range_succ] at h
    simp only [Nat.add_sub_cancel] at h
    rwa [sub_self, mul_zero, add_zero] at h
  -- thread differences are `ℚ(ζ_m)`-coefficients
  set g : ℚ⟮ζm⟯ := AdjoinSimple.gen ℚ ζm with hg
  have hcoe : algebraMap ℚ⟮ζm⟯ L g = ζm := AdjoinSimple.algebraMap_gen ℚ ζm
  set D : ℕ → ℚ⟮ζm⟯ := fun i => ∑ k ∈ Finset.range m,
    ((w (crt m r hco k i) - w (crt m r hco k (r - 1)) : ℤ) : ℚ⟮ζm⟯) * g ^ k with hD
  have hmap : ∀ i, algebraMap ℚ⟮ζm⟯ L (D i) = S i - S (r - 1) := by
    intro i
    rw [hD, map_sum, hS]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_pow, hcoe, map_intCast]
    push_cast
    ring
  -- the K-linear relation on `1, ζr, …, ζr^{r−2}`
  have hdeg : (minpoly ℚ⟮ζm⟯ ζr).natDegree = r - 1 := by
    rw [natDegree_minpoly_adjoin_coprime hm hr.pos hco hprim_m hprim_r,
      Nat.totient_prime hr]
  have hLI : LinearIndependent ℚ⟮ζm⟯ fun i : Fin (r - 1) => ζr ^ (i : ℕ) := by
    have h := linearIndependent_pow (K := ℚ⟮ζm⟯) ζr
    rwa [hdeg] at h
  have hrel : ∑ i : Fin (r - 1), D i.val • ζr ^ (i : ℕ) = 0 := by
    calc ∑ i : Fin (r - 1), D i.val • ζr ^ (i : ℕ)
        = ∑ i ∈ Finset.range (r - 1), D i • ζr ^ i :=
          Fin.sum_univ_eq_sum_range (fun i => D i • ζr ^ i) (r - 1)
      _ = ∑ i ∈ Finset.range (r - 1), ζr ^ i * (S i - S (r - 1)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Algebra.smul_def, hmap, mul_comm]
      _ = 0 := hdiff'
  -- coefficient extraction
  intro i hi
  rcases Nat.lt_or_ge i (r - 1) with hilt | hige
  · have hzero : D i = 0 :=
      Fintype.linearIndependent_iff.mp hLI (fun j => D j.val) hrel ⟨i, hilt⟩
    have h := congrArg (algebraMap ℚ⟮ζm⟯ L) hzero
    rw [map_zero, hmap] at h
    have := sub_eq_zero.mp h
    rw [hS] at this
    exact this
  · have hieq : i = r - 1 := by omega
    rw [hieq]

end CoprimeThreadSplit

/-! ## Stage 4 (O109c) — the ℤ-relation theorem at squarefree three-prime moduli

The assembly: split the `r`-threads off by the coprime equal-thread-sums theorem,
classify each thread difference at the two-prime level `p·q` (Stage 1), and fold
the thread index back through the CRT mod-identities.  The ℕ-cone analogue is
FALSE here (O105's witness at `n = 30`) — the ℤ-module statement is exactly the
structure that survives past two primes (Schoenberg/Rédei). -/

section ThreePrime

/-- **O109c — THE ℤ-RELATION THEOREM AT SQUAREFREE THREE-PRIME MODULI**
(Schoenberg/Rédei at `n = p·q·r`): a ℤ-combination of `pqr`-th roots of unity
vanishes **iff** the weight is a ℤ-combination of rotated full prime packets —
`w e = A (e % qr) + B (e % pr) + C (e % pq)`. -/
theorem debruijn_int_three_prime_squarefree [CharZero L] {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p * q * r)) (w : ℕ → ℤ) :
    (∑ e ∈ Finset.range (p * q * r), (w e : L) * ζ ^ e = 0) ↔
      ∃ A B C : ℕ → ℤ, ∀ e < p * q * r,
        w e = A (e % (q * r)) + B (e % (p * r)) + C (e % (p * q)) := by
  classical
  have hm : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hn : 0 < p * q * r := Nat.mul_pos hm hr.pos
  have hco : Nat.Coprime (p * q) r :=
    Nat.coprime_mul_iff_left.mpr
      ⟨(Nat.coprime_primes hp hr).mpr hpr, (Nat.coprime_primes hq hr).mpr hqr⟩
  have hdivp : (p * q * r) / p = q * r := by
    have hform : p * q * r = p * (q * r) := by ring
    rw [hform, Nat.mul_div_cancel_left _ hp.pos]
  have hdivq : (p * q * r) / q = p * r := by
    have hform : p * q * r = q * (p * r) := by ring
    rw [hform, Nat.mul_div_cancel_left _ hq.pos]
  have hdivr : (p * q * r) / r = p * q := by
    rw [Nat.mul_div_cancel _ hr.pos]
  constructor
  · -- FORWARD: thread split + two-prime classification + reassembly
    intro hsum
    set v : ℕ := crt (p * q) r hco 1 0 with hv
    set ζm : L := ζ ^ v with hζmdef
    have hζm : IsPrimitiveRoot ζm (p * q) :=
      isPrimitiveRoot_crt_left hm hr.pos hco hζ
    -- equal thread sums
    have hth := coprime_thread_sums_eq hr hm hco hζ w hsum
    -- each thread difference vanishes at level p*q
    have hdiffsum : ∀ i < r,
        ∑ k ∈ Finset.range (p * q),
          ((w (crt (p * q) r hco k i) - w (crt (p * q) r hco k (r - 1)) : ℤ) : L)
            * ζm ^ k = 0 := by
      intro i hi
      have h := sub_eq_zero.mpr (hth i hi)
      rw [← Finset.sum_sub_distrib] at h
      calc ∑ k ∈ Finset.range (p * q),
            ((w (crt (p * q) r hco k i) - w (crt (p * q) r hco k (r - 1)) : ℤ) : L)
              * ζm ^ k
          = ∑ k ∈ Finset.range (p * q),
              ((w (crt (p * q) r hco k i) : L) * ζm ^ k
                - (w (crt (p * q) r hco k (r - 1)) : L) * ζm ^ k) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            push_cast
            ring
        _ = 0 := h
    -- classify each thread difference by the two-prime theorem (a = b = 1)
    have hζm' : IsPrimitiveRoot ζm (p ^ 1 * q ^ 1) := by
      rw [pow_one, pow_one]
      exact hζm
    have hthreads : ∀ i, ∃ Ai Bi : ℕ → ℤ, i < r →
        ∀ k < p * q,
          w (crt (p * q) r hco k i) - w (crt (p * q) r hco k (r - 1))
            = Ai (k % q) + Bi (k % p) := by
      intro i
      by_cases hi : i < r
      · obtain ⟨Ai, Bi, hABi⟩ :=
          (debruijn_int_two_prime hp hq hpq one_pos one_pos hζm'
            (fun k => w (crt (p * q) r hco k i)
              - w (crt (p * q) r hco k (r - 1)))).mp
            (by
              have h := hdiffsum i hi
              rw [pow_one, pow_one]
              exact h)
        refine ⟨Ai, Bi, fun _ k hk => ?_⟩
        have h := hABi k (by rw [pow_one, pow_one]; exact hk)
        simpa using h
      · exact ⟨0, 0, fun hcon => absurd hcon hi⟩
    choose A B hAB using hthreads
    -- the three packet-direction coefficient functions
    refine ⟨fun x => A (x % r) (x % q), fun x => B (x % r) (x % p),
      fun x => w (crt (p * q) r hco x (r - 1)), fun e he => ?_⟩
    -- the CRT coordinates of e
    have hi : e % r < r := Nat.mod_lt _ hr.pos
    have hk : e % (p * q) < p * q := Nat.mod_lt _ hm
    have hround : crt (p * q) r hco (e % (p * q)) (e % r) = e :=
      crt_roundtrip hm hr.pos hco he
    have hmain := hAB (e % r) hi (e % (p * q)) hk
    rw [hround] at hmain
    -- mod collapses
    have h1 : (e % (p * q)) % q = e % q :=
      Nat.mod_mod_of_dvd e (dvd_mul_left q p)
    have h2 : (e % (p * q)) % p = e % p :=
      Nat.mod_mod_of_dvd e (dvd_mul_right p q)
    have h3 : (e % (q * r)) % q = e % q :=
      Nat.mod_mod_of_dvd e (dvd_mul_right q r)
    have h4 : (e % (q * r)) % r = e % r :=
      Nat.mod_mod_of_dvd e (dvd_mul_left r q)
    have h5 : (e % (p * r)) % p = e % p :=
      Nat.mod_mod_of_dvd e (dvd_mul_right p r)
    have h6 : (e % (p * r)) % r = e % r :=
      Nat.mod_mod_of_dvd e (dvd_mul_left r p)
    dsimp only
    rw [h3, h4, h5, h6]
    rw [h1, h2] at hmain
    omega
  · -- CONVERSE: three coset-combination kills
    rintro ⟨A, B, C, hABC⟩
    have hsplit : ∑ e ∈ Finset.range (p * q * r), (w e : L) * ζ ^ e
        = (∑ e ∈ Finset.range (p * q * r), (A (e % (q * r)) : L) * ζ ^ e)
          + (∑ e ∈ Finset.range (p * q * r), (B (e % (p * r)) : L) * ζ ^ e)
          + ∑ e ∈ Finset.range (p * q * r), (C (e % (p * q)) : L) * ζ ^ e := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [hABC e (Finset.mem_range.mp he)]
      push_cast
      ring
    have hA0 := packet_part_eq_zero_int hp.one_lt
      (dvd_mul_of_dvd_left (dvd_mul_right p q) r) hn hζ A
    have hB0 := packet_part_eq_zero_int hq.one_lt
      (dvd_mul_of_dvd_left (dvd_mul_left q p) r) hn hζ B
    have hC0 := packet_part_eq_zero_int hr.one_lt (dvd_mul_left r (p * q)) hn hζ C
    rw [hdivp] at hA0
    rw [hdivq] at hB0
    rw [hdivr] at hC0
    rw [hsplit, hA0, hB0, hC0, add_zero, add_zero]

end ThreePrime

/-! ## Stage 5 (O110) — THE FULL RELATION THEOREM: every modulus

The Rédei–de Bruijn–Schoenberg theorem (Schoenberg 1964, *Mathematika* 11;
Rédei 1959): the lattice of ℤ-relations among the `n`-th roots of unity is
spanned by the rotated full prime packets — at EVERY `n`, with no smoothness
restriction.  Strong induction on `n`, peeling the least prime `r = minFac n`:

* `r² ∣ n` — the non-coprime descent: the ℤ-thread split (the O93/O101 split,
  transported to ℤ by the shift trick) makes all `r` threads vanish one level
  down; the O103 digit identities lift the inductive packet combinations back.
* `r ∥ n` — the coprime descent: the Stage-3 equal-thread-sums split welds the
  threads; differences vanish at level `n/r`, the inductive combinations
  reassemble through the CRT mod-identities, and the welded thread becomes the
  `μ_r`-packet direction. -/

section FullRelationTheorem

/-- The ℤ-coefficient non-coprime thread split (the O93/O101 split for ℤ
weights, by the shift trick from the ℕ-weighted version). -/
lemma int_thread_vanishing_of_vanishing [CharZero L] {r m : ℕ} (hr : r.Prime)
    (hm : 0 < m) (hrm : r ∣ m) {ζ : L} (hζ : IsPrimitiveRoot ζ (r * m))
    (w : ℕ → ℤ)
    (hsum : ∑ e ∈ Finset.range (r * m), (w e : L) * ζ ^ e = 0) :
    ∀ i < r, ∑ k ∈ Finset.range m, (w (i + r * k) : L) * (ζ ^ r) ^ k = 0 := by
  classical
  have hn : 0 < r * m := Nat.mul_pos hr.pos hm
  have hm1 : 1 < m := lt_of_lt_of_le hr.one_lt (Nat.le_of_dvd hm hrm)
  have hn1 : 1 < r * m := lt_of_lt_of_le hm1 (Nat.le_mul_of_pos_left m hr.pos)
  have hζm : IsPrimitiveRoot (ζ ^ r) m := hζ.pow hn rfl
  -- the shift
  set c : ℕ := (Finset.range (r * m)).sup (fun e => (w e).natAbs) with hc
  have hbound : ∀ e < r * m, 0 ≤ w e + c := by
    intro e he
    have h1 : (w e).natAbs ≤ c :=
      Finset.le_sup (f := fun e => (w e).natAbs) (Finset.mem_range.mpr he)
    omega
  have hcast : ∀ e < r * m, (((w e + c).toNat : ℕ) : ℤ) = w e + c :=
    fun e he => Int.toNat_of_nonneg (hbound e he)
  have husum : ∑ e ∈ Finset.range (r * m),
      (((w e + c).toNat : ℕ) : L) * ζ ^ e = 0 := by
    have hgeom : ∑ e ∈ Finset.range (r * m), ζ ^ e = 0 :=
      hζ.geom_sum_eq_zero hn1
    calc ∑ e ∈ Finset.range (r * m), (((w e + c).toNat : ℕ) : L) * ζ ^ e
        = ∑ e ∈ Finset.range (r * m), ((w e : L) + (c : L)) * ζ ^ e := by
          refine Finset.sum_congr rfl fun e he => ?_
          congr 1
          have h := congrArg (fun z : ℤ => (z : L)) (hcast e (Finset.mem_range.mp he))
          push_cast at h
          exact h
      _ = (∑ e ∈ Finset.range (r * m), (w e : L) * ζ ^ e)
          + (c : L) * ∑ e ∈ Finset.range (r * m), ζ ^ e := by
          simp only [add_mul]
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = 0 := by rw [hsum, hgeom, mul_zero, add_zero]
  -- the ℕ-weighted split fires; the shift's thread contribution is geometric, zero
  have hth := WeightedThreadSplit.weighted_thread_vanishing_of_vanishing hr hm hrm
    hζ (fun e => (w e + c).toNat) husum
  intro i hi
  have h := hth i hi
  have hthread_geom : ∑ k ∈ Finset.range m, (ζ ^ r) ^ k = 0 :=
    hζm.geom_sum_eq_zero hm1
  have hexpand : ∑ k ∈ Finset.range m, (((w (i + r * k) + c).toNat : ℕ) : L)
      * (ζ ^ r) ^ k
      = (∑ k ∈ Finset.range m, (w (i + r * k) : L) * (ζ ^ r) ^ k)
        + (c : L) * ∑ k ∈ Finset.range m, (ζ ^ r) ^ k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hlt : i + r * k < r * m := by
      have hk' := Finset.mem_range.mp hk
      calc i + r * k < r + r * k := by omega
        _ = r * (k + 1) := by ring
        _ ≤ r * m := Nat.mul_le_mul_left r (by omega)
    have hcc := congrArg (fun z : ℤ => (z : L)) (hcast _ hlt)
    push_cast at hcc
    rw [hcc]
    ring
  rw [hexpand, hthread_geom, mul_zero, add_zero] at h
  exact h

/-- **The converse half at every modulus**: a ℤ-combination of `μ_p`-packet
directions (`p` ranging over the prime factors) kills the root sum. -/
lemma int_vanishing_of_combination {n : ℕ} (hn : 0 < n) {ζ : L}
    (hζ : IsPrimitiveRoot ζ n) (A : ℕ → ℕ → ℤ) (w : ℕ → ℤ)
    (hw : ∀ e < n, w e = ∑ p ∈ n.primeFactors, A p (e % (n / p))) :
    ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0 := by
  have hswap : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e
      = ∑ p ∈ n.primeFactors,
          ∑ e ∈ Finset.range n, (A p (e % (n / p)) : L) * ζ ^ e := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hw e (Finset.mem_range.mp he)]
    push_cast
    rw [Finset.sum_mul]
  rw [hswap]
  refine Finset.sum_eq_zero fun p hp => ?_
  exact packet_part_eq_zero_int (Nat.prime_of_mem_primeFactors hp).one_lt
    (Nat.dvd_of_mem_primeFactors hp) hn hζ (A p)

/-- **The forward half at every modulus** (the strong induction): a vanishing
ℤ-weighted root sum is a ℤ-combination of prime-packet directions. -/
theorem int_combination_of_vanishing [CharZero L] :
    ∀ n, 0 < n → ∀ ζ : L, IsPrimitiveRoot ζ n → ∀ w : ℕ → ℤ,
      (∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) →
      ∃ A : ℕ → ℕ → ℤ, ∀ e < n, w e = ∑ p ∈ n.primeFactors, A p (e % (n / p)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn ζ hζ w hsum
    rcases Nat.lt_or_ge n 2 with hn1 | hn2
    · -- n = 1: the sum IS w 0
      have hne : n = 1 := by omega
      subst hne
      refine ⟨0, fun e he => ?_⟩
      interval_cases e
      have hw0 : w 0 = 0 := by
        have h := hsum
        simp at h
        exact h
      simp [hw0]
    · -- n ≥ 2: peel the least prime
      set r : ℕ := n.minFac with hrdef
      have hr : r.Prime := Nat.minFac_prime (by omega)
      have hrn : r ∣ n := Nat.minFac_dvd n
      set m : ℕ := n / r with hmdef
      have hnm : n = r * m := (Nat.mul_div_cancel' hrn).symm
      have hm : 0 < m := Nat.div_pos (Nat.le_of_dvd hn hrn) hr.pos
      have hmlt : m < n := by
        rw [hnm]
        calc m = 1 * m := (one_mul m).symm
          _ < r * m := by
              exact Nat.mul_lt_mul_of_lt_of_le hr.one_lt le_rfl hm
      by_cases hrm : r ∣ m
      · -- NON-COPRIME descent: r² ∣ n
        rw [hnm] at hζ hsum
        have hζm : IsPrimitiveRoot (ζ ^ r) m := hζ.pow (Nat.mul_pos hr.pos hm) rfl
        have hth := int_thread_vanishing_of_vanishing hr hm hrm hζ w hsum
        -- IH per thread
        have hthreads : ∀ i, ∃ Ai : ℕ → ℕ → ℤ, i < r →
            ∀ k < m, w (i + r * k)
              = ∑ p ∈ m.primeFactors, Ai p (k % (m / p)) := by
          intro i
          by_cases hi : i < r
          · obtain ⟨Ai, hAi⟩ := IH m hmlt hm (ζ ^ r) hζm
              (fun k => w (i + r * k)) (hth i hi)
            exact ⟨Ai, fun _ => hAi⟩
          · exact ⟨0, fun hcon => absurd hcon hi⟩
        choose A hA using hthreads
        -- prime factors agree: r ∣ m
        have hpf : n.primeFactors = m.primeFactors := by
          rw [hnm, Nat.primeFactors_mul hr.pos.ne' hm.ne',
            Nat.Prime.primeFactors hr]
          exact Finset.union_eq_right.mpr
            (Finset.singleton_subset_iff.mpr
              (Nat.mem_primeFactors.mpr ⟨hr, hrm, hm.ne'⟩))
        -- the O103 digit lift
        refine ⟨fun p x => A (x % r) p (x / r), fun e he => ?_⟩
        rw [hnm] at he
        have hi : e % r < r := Nat.mod_lt _ hr.pos
        have hk : e / r < m := Nat.div_lt_of_lt_mul he
        have hsplitE : e % r + r * (e / r) = e := Nat.mod_add_div e r
        have hmain := hA (e % r) hi (e / r) hk
        rw [hsplitE] at hmain
        rw [hmain, hpf]
        refine Finset.sum_congr rfl fun p hp => ?_
        have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp
        have hnp : n / p = r * (m / p) := by
          rw [hnm]
          exact Nat.mul_div_assoc r hpm
        have hd1 : (e % (r * (m / p))) % r = e % r :=
          Nat.mod_mod_of_dvd e (dvd_mul_right r (m / p))
        have hd2 : (e % (r * (m / p))) / r = (e / r) % (m / p) :=
          Nat.mod_mul_right_div_self e r (m / p)
        dsimp only
        rw [hnp, hd1, hd2]
      · -- COPRIME descent: r ∥ n
        have hco : Nat.Coprime m r := ((hr.coprime_iff_not_dvd).mpr hrm).symm
        have hnm' : n = m * r := by rw [hnm]; ring
        rw [hnm'] at hζ hsum
        have hζm : IsPrimitiveRoot (ζ ^ crt m r hco 1 0) m :=
          isPrimitiveRoot_crt_left hm hr.pos hco hζ
        have hth := coprime_thread_sums_eq hr hm hco hζ w hsum
        -- thread differences vanish at level m
        have hdiffsum : ∀ i < r,
            ∑ k ∈ Finset.range m,
              ((w (crt m r hco k i) - w (crt m r hco k (r - 1)) : ℤ) : L)
                * (ζ ^ crt m r hco 1 0) ^ k = 0 := by
          intro i hi
          have h := sub_eq_zero.mpr (hth i hi)
          rw [← Finset.sum_sub_distrib] at h
          calc ∑ k ∈ Finset.range m,
              ((w (crt m r hco k i) - w (crt m r hco k (r - 1)) : ℤ) : L)
                * (ζ ^ crt m r hco 1 0) ^ k
              = ∑ k ∈ Finset.range m,
                  ((w (crt m r hco k i) : L) * (ζ ^ crt m r hco 1 0) ^ k
                    - (w (crt m r hco k (r - 1)) : L)
                      * (ζ ^ crt m r hco 1 0) ^ k) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                push_cast
                ring
            _ = 0 := h
        -- IH per thread difference
        have hthreads : ∀ i, ∃ Ai : ℕ → ℕ → ℤ, i < r →
            ∀ k < m, w (crt m r hco k i) - w (crt m r hco k (r - 1))
              = ∑ p ∈ m.primeFactors, Ai p (k % (m / p)) := by
          intro i
          by_cases hi : i < r
          · obtain ⟨Ai, hAi⟩ := IH m hmlt hm (ζ ^ crt m r hco 1 0) hζm
              (fun k => w (crt m r hco k i) - w (crt m r hco k (r - 1)))
              (hdiffsum i hi)
            exact ⟨Ai, fun _ => hAi⟩
          · exact ⟨0, fun hcon => absurd hcon hi⟩
        choose A hA using hthreads
        -- prime factors: `n` adds the new prime `r`
        have hrnotm : r ∉ m.primeFactors :=
          fun hmem => hrm (Nat.dvd_of_mem_primeFactors hmem)
        have hpf : n.primeFactors = insert r m.primeFactors := by
          rw [hnm', Nat.primeFactors_mul hm.ne' hr.pos.ne',
            Nat.Prime.primeFactors hr, Finset.union_comm, ← Finset.insert_eq]
        have hnr : n / r = m := hmdef.symm
        -- assemble: the welded thread is the μ_r-packet direction
        refine ⟨fun p x => if p = r then w (crt m r hco x (r - 1))
          else A (x % r) p (x % (m / p)), fun e he => ?_⟩
        rw [hnm'] at he
        have hi : e % r < r := Nat.mod_lt _ hr.pos
        have hk : e % m < m := Nat.mod_lt _ hm
        have hround : crt m r hco (e % m) (e % r) = e :=
          crt_roundtrip hm hr.pos hco he
        have hmain := hA (e % r) hi (e % m) hk
        rw [hround] at hmain
        have hmain2 : w e - w (crt m r hco (e % m) (r - 1))
            = ∑ p ∈ m.primeFactors, A (e % r) p (e % (m / p)) := by
          rw [hmain]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [Nat.mod_mod_of_dvd e
            (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp))]
        rw [hpf, Finset.sum_insert hrnotm]
        have hrterm : (fun p x => if p = r then w (crt m r hco x (r - 1))
            else A (x % r) p (x % (m / p))) r (e % (n / r))
            = w (crt m r hco (e % m) (r - 1)) := by
          dsimp only
          rw [if_pos rfl, hnr]
        have hgoalsum : ∑ p ∈ m.primeFactors,
            (fun p x => if p = r then w (crt m r hco x (r - 1))
              else A (x % r) p (x % (m / p))) p (e % (n / p))
            = ∑ p ∈ m.primeFactors, A (e % r) p (e % (m / p)) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          have hpr : p ≠ r := fun h => hrnotm (h ▸ hp)
          have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp
          have hnp : n / p = m / p * r := by
            rw [hnm', mul_comm m r, Nat.mul_div_assoc r hpm, mul_comm]
          dsimp only
          rw [if_neg hpr, hnp,
            Nat.mod_mod_of_dvd e (dvd_mul_left r (m / p)),
            Nat.mod_mod_of_dvd e (dvd_mul_right (m / p) r)]
        rw [hrterm, hgoalsum]
        omega

/-- **THE RÉDEI–DE BRUIJN–SCHOENBERG RELATION THEOREM** (Schoenberg 1964,
Mathematika 11, Thm 1; Rédei 1959): for EVERY `n ≥ 1` and primitive `n`-th root
of unity `ζ` in a characteristic-zero field, a ℤ-combination of `n`-th roots of
unity vanishes **iff** the weight is a ℤ-combination of rotated full prime
packets — `w e = Σ_{p ∣ n prime} A_p(e % (n/p))`.  No smoothness restriction:
this is the full classification of vanishing integer sums of roots of unity. -/
theorem redei_debruijn_schoenberg [CharZero L] {n : ℕ} (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (w : ℕ → ℤ) :
    (∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) ↔
      ∃ A : ℕ → ℕ → ℤ, ∀ e < n,
        w e = ∑ p ∈ n.primeFactors, A p (e % (n / p)) :=
  ⟨int_combination_of_vanishing n hn ζ hζ w,
    fun ⟨A, hA⟩ => int_vanishing_of_combination hn hζ A w hA⟩

/-! ## Teeth (fired at `ℂ`, `n = 4`): a packet certificate produces the genuine
vanishing sum `1 + i² = 0`; the singleton weight `δ₀` is refuted. -/

private lemma exp_quarter_primitive :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 4)) 4 :=
  Complex.isPrimitiveRoot_exp 4 (by norm_num)

private lemma primeFactors_four : (4 : ℕ).primeFactors = {2} := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
    Nat.primeFactors_pow _ (by norm_num), Nat.Prime.primeFactors Nat.prime_two]

/-- The packet weight on `{0, 2}` at `n = 4` (the `μ_2`-packet). -/
private def wPacket : ℕ → ℤ := fun e => if e = 0 ∨ e = 2 then 1 else 0

/-- Converse fired: the `μ_2`-packet weight on `{0, 2}` at `n = 4` vanishes. -/
example : ∑ e ∈ Finset.range 4,
    (wPacket e : ℂ) * Complex.exp (2 * Real.pi * Complex.I / 4) ^ e = 0 := by
  refine (redei_debruijn_schoenberg (by norm_num) exp_quarter_primitive
    wPacket).mpr ⟨fun _ x => if x = 0 then 1 else 0, ?_⟩
  intro e he
  rw [primeFactors_four, Finset.sum_singleton]
  interval_cases e <;> decide

/-- The singleton weight `δ₀`. -/
private def wSingle : ℕ → ℤ := fun e => if e = 0 then 1 else 0

/-- Forward fired (with teeth): the singleton weight `δ₀` cannot vanish —
its packet decomposition would force `w 0 = w 2`. -/
example : ¬ (∑ e ∈ Finset.range 4,
    (wSingle e : ℂ) * Complex.exp (2 * Real.pi * Complex.I / 4) ^ e = 0) := by
  intro hcon
  obtain ⟨A, hA⟩ := (redei_debruijn_schoenberg (by norm_num)
    exp_quarter_primitive wSingle).mp hcon
  have h0 := hA 0 (by norm_num)
  have h2 := hA 2 (by norm_num)
  rw [primeFactors_four, Finset.sum_singleton] at h0 h2
  norm_num [wSingle] at h0 h2
  omega

end FullRelationTheorem

end DeBruijnIntRelations

#print axioms DeBruijnIntRelations.int_sum_split
#print axioms DeBruijnIntRelations.packet_part_eq_zero_int
#print axioms DeBruijnIntRelations.debruijn_int_two_prime
#print axioms DeBruijnIntRelations.minpoly_adjoin_coprime_eq_cyclotomic
#print axioms DeBruijnIntRelations.coprime_thread_sums_eq
#print axioms DeBruijnIntRelations.debruijn_int_three_prime_squarefree
#print axioms DeBruijnIntRelations.int_thread_vanishing_of_vanishing
#print axioms DeBruijnIntRelations.int_combination_of_vanishing
#print axioms DeBruijnIntRelations.redei_debruijn_schoenberg
