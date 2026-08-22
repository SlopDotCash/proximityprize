/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CRTPacketMinpoly
import Mathlib

/-!
# Issue #232 — the two-prime de Bruijn structure: the CRT double-slice theorems (O67–O68)

The mixed-radix continuation of the O50/O66 prime-power base cases (DISPROOF_LOG O67):
de Bruijn's structure theorem says that for `n` with at most two prime divisors, every
vanishing sum of `n`-th roots of unity is an ℕ-combination of rotated full prime packets
(`μ_p`-packets and `μ_q`-packets).  This file machine-checks the **CRT double-slice
route** to that theorem (the in-framework candidate identified in O67), delivering the
T2/T3 tiers:

* `vanishing_coeff_slices_over` — **the K-coefficient prime-power slice theorem**: for an
  arbitrary coefficient field `K` with `Algebra K F`, if `Φ_{p^(m+1)}` stays the minimal
  polynomial of a primitive `p^(m+1)`-th root `ζ` over `K` (the **linear-disjointness
  hypothesis** `hmin`, the ONE named hypothesis of the route), then any vanishing
  `K`-combination of the powers `ζ^e`, `e < p^(m+1)`, has all `p` of its length-`p^m`
  coefficient slices equal.  This generalizes `LamLeungTwoPow.vanishing_coeff_slices`
  from `ℚ` to `K`; the proof is the same Gauss engine (the prime-power cyclotomic is the
  geometric packet `Σ_{i<p} X^{i·p^m}`, and a packet multiple has all slices equal).

* `qside_slices_over` — **T2, the double-slice structure theorem**: for a finite
  `S ⊆ μ_{p^(m+1)·N}` with vanishing sum (`N` coprime to `p`, e.g. `N = q^b`), the
  q-side grouped coefficients `γ_u := Σ_v 1_S(u,v)·z_q^v ∈ K` satisfy the slice relations
  `γ_{i·p^m + s} = γ_{i'·p^m + s}` — the grouped membership data is constant along
  `μ_p`-coset directions.  Modulo `hmin`, this is unconditional and machine-checked.

* `slice_difference_vanishing` / `two_prime_double_slice` — **T3**: the slice
  differences are vanishing sums of `q^(b+1)`-th roots with coefficients in `{−1,0,1}`
  ⊆ ℚ, where the rational slice theorem (`vanishing_coeff_slices_rat`, recovered here as
  the `K = ℚ` instance of the engine) applies at the second prime: the membership
  difference pattern between two `μ_p`-coset-related rows is itself constant along
  `μ_q`-coset directions.  This is the full double-slice (two-prime de Bruijn) structure
  at the level of slice relations.

* `minpoly_qadjoin_eq_cyclotomic` — **the linear-disjointness DISCHARGE**: `Φ_{p^(a+1)}`
  IS the minimal polynomial of `ζ_p` over `ℚ⟮ζ_q⟯` (`q ≠ p` primes, `ζ_q` of order
  `q^b`).  Engine: the shared packet minimal-polynomial theorem in `CRTPacketMinpoly`.

* `two_prime_qside_slices` / `two_prime_deBruijn_double_slice` — the headline two-prime
  instantiations with `K := ℚ⟮ζ_q⟯`, now **unconditional**: no hypotheses beyond
  characteristic zero, the two primitive roots, and the vanishing sum (numerically
  cross-checked 99/99 at `n = 12` and 999/999 at `n = 18` in O67's exhaustive probe of
  the downstream decomposition; hypothesis satisfiability witnessed in-file over `ℂ`).

* `mu_p_membership_slices` — **non-vacuity of the engine**: the `K = ℚ`, `N = 1`
  instance (`hmin` discharged by `Polynomial.cyclotomic_eq_minpoly_rat`) recovers the
  membership-level O66 slice structure of `vanishing_sum_mu_p_closed` through the new
  machinery.

What is NOT here (honest map): the T1 packet decomposition — de Bruijn's ℕ-cone
extraction (disjoint rotated full packets) needs an induction with packet subtraction
on top of these slice relations (the genuinely de Bruijn positivity step, residual (3)
of the O67 program); the slice relations themselves are now hypothesis-free.

Engine provenance: the packet coefficient calculation and weighted slice engine live in
`CRTDoubleSlice`; the coprime cyclotomic minimal-polynomial discharge lives in
`CRTPacketMinpoly`.  This file keeps the de Bruijn-facing theorem names as stable wrappers
around those shared engines.
-/

set_option linter.style.longFile 3100


namespace DeBruijnTwoPrime

open Polynomial Finset

variable {F : Type*} [Field F]

/-! ## The K-coefficient slice engine

The O68 coefficient-general slice theorem, with the coefficient field generalized from
`ℚ` to an arbitrary field `K` mapping into `F`.  The price of the generalization is the
single hypothesis `hmin`: the `p^(m+1)`-th cyclotomic polynomial must remain the minimal
polynomial of the primitive root over `K` — for `K = ℚ(ζ_{q^b})` with `q ≠ p` this is
the linear disjointness of coprime cyclotomic extensions. -/

section CoefficientSlicesOver

/-- Slices of a geometric-packet multiple: if `deg R < q` then
`(Σ_{i<p} X^(iq) · R).coeff (iq + s) = R.coeff s` for `i < p`, `s < q`.
(Wrapper around `CRTDoubleSlice.packet_slice_coeff`.) -/
lemma packet_mul_coeff {K : Type*} [Field K] {p q : ℕ} (_hq : 0 < q) {R : K[X]}
    (hR : R.natDegree < q) {i s : ℕ} (hi : i < p) (hs : s < q) :
    ((∑ i ∈ Finset.range p, (Polynomial.X : K[X]) ^ (i * q)) * R).coeff (i * q + s)
      = R.coeff s := by
  exact CRTDoubleSlice.packet_slice_coeff (K := K) (p := p) (q := q) (R := R)
    hR hi hs

/-- **The K-coefficient prime-power slice theorem** (the linear-disjointness slice
engine): if `Φ_{p^(m+1)}` is still the minimal polynomial of the primitive `p^(m+1)`-th
root `ζ ∈ F` over the coefficient field `K` (hypothesis `hmin`), then any vanishing
`K`-linear combination of `ζ^e`, `e < p^(m+1)`, has all `p` of its length-`p^m`
coefficient slices equal.
(Wrapper around `CRTDoubleSlice.slice_of_packet_minpoly`, with `hmin` first rewritten
to the geometric packet form of the prime-power cyclotomic.) -/
theorem vanishing_coeff_slices_over (K : Type*) [Field K] [Algebra K F]
    {p m : ℕ} (hp : p.Prime) {ζ : F}
    (_hζ : IsPrimitiveRoot ζ (p ^ (m + 1)))
    (hmin : minpoly K ζ = Polynomial.cyclotomic (p ^ (m + 1)) K)
    (c : ℕ → K)
    (hsum : ∑ e ∈ Finset.range (p ^ (m + 1)), algebraMap K F (c e) * ζ ^ e = 0) :
    ∀ s < p ^ m, ∀ i < p, ∀ i' < p, c (i * p ^ m + s) = c (i' * p ^ m + s) := by
  classical
  intro s hs i hi i' hi'
  have hpacket :
      minpoly K ζ = ∑ t ∈ Finset.range p, (X : K[X]) ^ (t * p ^ m) := by
    rw [hmin, Polynomial.cyclotomic_prime_pow_eq_geom_sum hp]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_comm t (p ^ m), pow_mul]
  have hpow : p * p ^ m = p ^ (m + 1) := by ring
  have hsum' : ∑ e ∈ Finset.range (p * p ^ m), c e • ζ ^ e = 0 := by
    rw [hpow]
    simpa [Algebra.smul_def] using hsum
  exact CRTDoubleSlice.slice_of_packet_minpoly hpacket hsum' hi hi' hs

/-- The `K = ℚ` instance: the rational coefficient-slice theorem, with the
linear-disjointness hypothesis discharged by `Polynomial.cyclotomic_eq_minpoly_rat`.
(This recovers `LamLeungTwoPow.vanishing_coeff_slices` through the generalized engine —
the satisfiability witness for the `hmin` hypothesis shape.) -/
theorem vanishing_coeff_slices_rat [CharZero F] {p m : ℕ} (hp : p.Prime) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (p ^ (m + 1)))
    (c : ℕ → ℚ)
    (hsum : ∑ e ∈ Finset.range (p ^ (m + 1)), (c e : F) * ζ ^ e = 0) :
    ∀ s < p ^ m, ∀ i < p, ∀ i' < p, c (i * p ^ m + s) = c (i' * p ^ m + s) := by
  refine vanishing_coeff_slices_over ℚ hp hζ
    (Polynomial.cyclotomic_eq_minpoly_rat hζ (pow_pos hp.pos _)).symm c ?_
  simpa only [eq_ratCast] using hsum

end CoefficientSlicesOver

/-! ## The CRT box: parametrizing `μ_{M·N}` by `μ_M × μ_N`

For coprime `M`, `N`, the map `(u, v) ↦ x^u · y^v` (with `x`, `y` primitive `M`-th and
`N`-th roots) is a bijection from `[0,M) × [0,N)` onto the `(M·N)`-th roots of unity —
the exponent CRT coordinates that the double-slice argument groups along. -/

section CRTBox

/-- The product of primitive roots of coprime orders is a primitive root of the
product order. -/
lemma isPrimitiveRoot_mul {M N : ℕ} {x y : F} (hx : IsPrimitiveRoot x M)
    (hy : IsPrimitiveRoot y N) (hcop : Nat.Coprime M N) :
    IsPrimitiveRoot (x * y) (M * N) := by
  have hord : orderOf (x * y) = orderOf x * orderOf y :=
    (Commute.all x y).orderOf_mul_eq_mul_orderOf_of_coprime
      (by rw [← hx.eq_orderOf, ← hy.eq_orderOf]; exact hcop)
  have h := IsPrimitiveRoot.orderOf (x * y)
  rwa [hord, ← hx.eq_orderOf, ← hy.eq_orderOf] at h

/-- A primitive root of positive order is nonzero. -/
lemma prim_ne_zero {M : ℕ} {x : F} (hx : IsPrimitiveRoot x M) (hM : 0 < M) : x ≠ 0 := by
  intro h0
  have h1 := hx.pow_eq_one
  rw [h0, zero_pow hM.ne'] at h1
  exact zero_ne_one h1

/-- **Injectivity of the CRT box**: `x^u · y^v` determines `(u, v)` on
`[0,M) × [0,N)` when `M`, `N` are coprime. -/
lemma box_pair_inj {M N : ℕ} {x y : F} (hx : IsPrimitiveRoot x M) (hy : IsPrimitiveRoot y N)
    (hcop : Nat.Coprime M N) {u v u' v' : ℕ} (hu : u < M) (hv : v < N) (hu' : u' < M)
    (hv' : v' < N) (h : x ^ u * y ^ v = x ^ u' * y ^ v') : u = u' ∧ v = v' := by
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le u) hu
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le v) hv
  have hx0 : x ≠ 0 := prim_ne_zero hx hM
  have hy0 : y ≠ 0 := prim_ne_zero hy hN
  have hxu' : x ^ u' ≠ 0 := pow_ne_zero _ hx0
  have hyv : y ^ v ≠ 0 := pow_ne_zero _ hy0
  have hpowM : ∀ k : ℕ, (x ^ k) ^ M = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hx.pow_eq_one, one_pow]
  have hpowN : ∀ k : ℕ, (y ^ k) ^ N = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hy.pow_eq_one, one_pow]
  set t := x ^ u / x ^ u' with ht
  have ht2 : t = y ^ v' / y ^ v := by
    rw [ht, div_eq_div_iff hxu' hyv]
    linear_combination h
  have htM : t ^ M = 1 := by rw [ht, div_pow, hpowM u, hpowM u', div_one]
  have htN : t ^ N = 1 := by rw [ht2, div_pow, hpowN v', hpowN v, div_one]
  have hdvd1 : orderOf t ∣ 1 := by
    have hg : orderOf t ∣ Nat.gcd M N :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one htM) (orderOf_dvd_of_pow_eq_one htN)
    rwa [Nat.Coprime.gcd_eq_one hcop] at hg
  have ht1 : t = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  have hxx : x ^ u = x ^ u' := by
    rw [ht] at ht1
    calc x ^ u = x ^ u / x ^ u' * x ^ u' := (div_mul_cancel₀ _ hxu').symm
    _ = 1 * x ^ u' := by rw [ht1]
    _ = x ^ u' := one_mul _
  have huu : u = u' := hx.pow_inj hu hu' hxx
  refine ⟨huu, hy.pow_inj hv hv' ?_⟩
  have h2 := h
  rw [huu] at h2
  exact mul_left_cancel₀ hxu' h2

/-- **Surjectivity of the CRT box**: every `(M·N)`-th root of unity is `x^u · y^v` for
some `(u, v)` in the box (no Bezout needed: reduce the joint exponent mod each order). -/
lemma box_pair_surj {M N : ℕ} {x y : F} (hx : IsPrimitiveRoot x M) (hy : IsPrimitiveRoot y N)
    (hcop : Nat.Coprime M N) (hM : 0 < M) (hN : 0 < N) {z : F} (hz : z ^ (M * N) = 1) :
    ∃ u < M, ∃ v < N, x ^ u * y ^ v = z := by
  haveI : NeZero (M * N) := ⟨(Nat.mul_pos hM hN).ne'⟩
  obtain ⟨e, _, hez⟩ := (isPrimitiveRoot_mul hx hy hcop).eq_pow_of_pow_eq_one hz
  refine ⟨e % M, Nat.mod_lt _ hM, e % N, Nat.mod_lt _ hN, ?_⟩
  have hxe : x ^ (e % M) = x ^ e := by
    conv_rhs => rw [← Nat.div_add_mod e M]
    rw [pow_add, pow_mul, hx.pow_eq_one, one_pow, one_mul]
  have hye : y ^ (e % N) = y ^ e := by
    conv_rhs => rw [← Nat.div_add_mod e N]
    rw [pow_add, pow_mul, hy.pow_eq_one, one_pow, one_mul]
  rw [hxe, hye, ← mul_pow]
  exact hez

end CRTBox

/-! ## The q-side grouping and the T2 double-slice structure theorem -/

section QSideGrouping

variable [DecidableEq F] {K : Type*} [Field K]

/-- **The q-side grouped coefficient** `γ_u ∈ K`: the generating sum of the `u`-th
`x`-row of `S` against the `K`-side root `z_q` (whose image in `F` is `y`):
`γ_u = Σ_{v<N} 1_S(x^u·y^v) · z_q^v`. -/
def gammaQ (S : Finset F) (x y : F) (zq : K) (N u : ℕ) : K :=
  ∑ v ∈ Finset.range N, (if x ^ u * y ^ v ∈ S then (1 : K) else 0) * zq ^ v

variable [Algebra K F]

/-- The image of `γ_u` in `F` is the same generating sum with `y`-powers. -/
lemma map_gammaQ (S : Finset F) (x : F) {y : F} {zq : K}
    (hzq : algebraMap K F zq = y) (N u : ℕ) :
    algebraMap K F (gammaQ S x y zq N u)
      = ∑ v ∈ Finset.range N, (if x ^ u * y ^ v ∈ S then (1 : F) else 0) * y ^ v := by
  rw [gammaQ, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul, map_pow, hzq, apply_ite (algebraMap K F), map_one, map_zero]

/-- **The grouped-sum identity**: summing the `F`-side grouped row sums against `x^u`
recovers the total sum of `S` (via the CRT box bijection). -/
lemma grouped_sum {M N : ℕ} {x y : F} (hx : IsPrimitiveRoot x M) (hy : IsPrimitiveRoot y N)
    (hcop : Nat.Coprime M N) (hM : 0 < M) (hN : 0 < N) {S : Finset F}
    (hS : ∀ z ∈ S, z ^ (M * N) = 1) :
    ∑ u ∈ Finset.range M, (∑ v ∈ Finset.range N,
        (if x ^ u * y ^ v ∈ S then (1 : F) else 0) * y ^ v) * x ^ u
      = ∑ z ∈ S, z := by
  have hstep : ∀ u ∈ Finset.range M, (∑ v ∈ Finset.range N,
      (if x ^ u * y ^ v ∈ S then (1 : F) else 0) * y ^ v) * x ^ u
      = ∑ v ∈ Finset.range N, (if x ^ u * y ^ v ∈ S then x ^ u * y ^ v else 0) := by
    intro u _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs with h <;> ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_product', ← Finset.sum_filter]
  apply Finset.sum_bij (fun uv _ => x ^ uv.1 * y ^ uv.2)
  · intro uv huv
    exact (Finset.mem_filter.mp huv).2
  · intro uv1 h1 uv2 h2 heq
    have hm1 := Finset.mem_product.mp (Finset.mem_filter.mp h1).1
    have hm2 := Finset.mem_product.mp (Finset.mem_filter.mp h2).1
    obtain ⟨he1, he2⟩ := box_pair_inj hx hy hcop (Finset.mem_range.mp hm1.1)
      (Finset.mem_range.mp hm1.2) (Finset.mem_range.mp hm2.1)
      (Finset.mem_range.mp hm2.2) heq
    exact Prod.ext he1 he2
  · intro z hz
    obtain ⟨u, hu, v, hv, huv⟩ := box_pair_surj hx hy hcop hM hN (hS z hz)
    exact ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hu, Finset.mem_range.mpr hv⟩,
      (by rw [huv]; exact hz)⟩, huv⟩
  · intro uv _
    rfl

/-- **T2 — the double-slice structure theorem** (general second factor): for a finite
`S ⊆ μ_{p^(m+1)·N}` with vanishing sum, `N` coprime to `p^(m+1)`, the q-side grouped
coefficients `γ_u ∈ K` are constant along `μ_p`-coset directions of the `x`-exponent:
`γ_{i·p^m+s} = γ_{i'·p^m+s}` for all `i, i' < p`, `s < p^m`.  The ONE named hypothesis
is `hmin` (linear disjointness): `Φ_{p^(m+1)}` stays the minimal polynomial of `x`
over `K`. -/
theorem qside_slices_over {p m N : ℕ} (hp : p.Prime) (hN : 0 < N)
    {x y : F} (hx : IsPrimitiveRoot x (p ^ (m + 1))) (hy : IsPrimitiveRoot y N)
    (hcop : Nat.Coprime (p ^ (m + 1)) N)
    {zq : K} (hzq : algebraMap K F zq = y)
    (hmin : minpoly K x = Polynomial.cyclotomic (p ^ (m + 1)) K)
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (m + 1) * N) = 1)
    (hsum : ∑ z ∈ S, z = 0) :
    ∀ s < p ^ m, ∀ i < p, ∀ i' < p,
      gammaQ S x y zq N (i * p ^ m + s) = gammaQ S x y zq N (i' * p ^ m + s) := by
  refine vanishing_coeff_slices_over K hp hx hmin (fun e => gammaQ S x y zq N e) ?_
  calc ∑ e ∈ Finset.range (p ^ (m + 1)), algebraMap K F (gammaQ S x y zq N e) * x ^ e
      = ∑ e ∈ Finset.range (p ^ (m + 1)),
          (∑ v ∈ Finset.range N, (if x ^ e * y ^ v ∈ S then (1 : F) else 0) * y ^ v)
            * x ^ e :=
        Finset.sum_congr rfl fun e _ => by rw [map_gammaQ S x hzq N e]
    _ = ∑ z ∈ S, z := grouped_sum hx hy hcop (pow_pos hp.pos _) hN hS
    _ = 0 := hsum

/-- **T3a — the `{−1,0,1}`-difference lemma**: the T2 slice equalities, pushed to `F`,
say that the membership-difference pattern between two `μ_p`-coset-related rows is a
vanishing sum of `y`-powers with coefficients in `{−1,0,1} ⊆ ℚ`. -/
theorem slice_difference_vanishing [CharZero F] {p m N : ℕ} (hp : p.Prime) (hN : 0 < N)
    {x y : F} (hx : IsPrimitiveRoot x (p ^ (m + 1))) (hy : IsPrimitiveRoot y N)
    (hcop : Nat.Coprime (p ^ (m + 1)) N)
    {zq : K} (hzq : algebraMap K F zq = y)
    (hmin : minpoly K x = Polynomial.cyclotomic (p ^ (m + 1)) K)
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (m + 1) * N) = 1)
    (hsum : ∑ z ∈ S, z = 0) :
    ∀ s < p ^ m, ∀ i < p, ∀ i' < p,
      ∑ v ∈ Finset.range N,
        (((if x ^ (i * p ^ m + s) * y ^ v ∈ S then (1 : ℚ) else 0)
          - (if x ^ (i' * p ^ m + s) * y ^ v ∈ S then (1 : ℚ) else 0) : ℚ) : F)
          * y ^ v = 0 := by
  intro s hs i hi i' hi'
  have hg := qside_slices_over hp hN hx hy hcop hzq hmin hS hsum s hs i hi i' hi'
  have hgF := congrArg (algebraMap K F) hg
  rw [map_gammaQ S x hzq, map_gammaQ S x hzq] at hgF
  have hterm : ∀ v : ℕ,
      (((if x ^ (i * p ^ m + s) * y ^ v ∈ S then (1 : ℚ) else 0)
        - (if x ^ (i' * p ^ m + s) * y ^ v ∈ S then (1 : ℚ) else 0) : ℚ) : F) * y ^ v
      = (if x ^ (i * p ^ m + s) * y ^ v ∈ S then (1 : F) else 0) * y ^ v
        - (if x ^ (i' * p ^ m + s) * y ^ v ∈ S then (1 : F) else 0) * y ^ v := by
    intro v
    rw [Rat.cast_sub, apply_ite (Rat.cast : ℚ → F), apply_ite (Rat.cast : ℚ → F),
      Rat.cast_one, Rat.cast_zero, sub_mul]
  rw [Finset.sum_congr rfl fun v _ => hterm v, Finset.sum_sub_distrib, hgF, sub_self]

/-- **T3b — the full two-prime double-slice theorem** (the de Bruijn structure at the
slice level): for `S ⊆ μ_{p^(m+1)·q^(b+1)}` with vanishing sum, the membership
difference pattern between two `μ_p`-coset-related rows is constant along `μ_q`-coset
directions — the rational slice theorem applied at the second prime to the T3a
difference sums. -/
theorem two_prime_double_slice [CharZero F] {p m q b : ℕ} (hp : p.Prime) (hq : q.Prime)
    {x y : F} (hx : IsPrimitiveRoot x (p ^ (m + 1))) (hy : IsPrimitiveRoot y (q ^ (b + 1)))
    (hcop : Nat.Coprime (p ^ (m + 1)) (q ^ (b + 1)))
    {zq : K} (hzq : algebraMap K F zq = y)
    (hmin : minpoly K x = Polynomial.cyclotomic (p ^ (m + 1)) K)
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (m + 1) * q ^ (b + 1)) = 1)
    (hsum : ∑ z ∈ S, z = 0) :
    ∀ s < p ^ m, ∀ i < p, ∀ i' < p, ∀ t < q ^ b, ∀ j < q, ∀ j' < q,
      (if x ^ (i * p ^ m + s) * y ^ (j * q ^ b + t) ∈ S then (1 : ℚ) else 0)
        - (if x ^ (i' * p ^ m + s) * y ^ (j * q ^ b + t) ∈ S then (1 : ℚ) else 0)
      = (if x ^ (i * p ^ m + s) * y ^ (j' * q ^ b + t) ∈ S then (1 : ℚ) else 0)
        - (if x ^ (i' * p ^ m + s) * y ^ (j' * q ^ b + t) ∈ S then (1 : ℚ) else 0) := by
  intro s hs i hi i' hi'
  have hdiff := slice_difference_vanishing hp (pow_pos hq.pos _) hx hy hcop hzq hmin
    hS hsum s hs i hi i' hi'
  exact vanishing_coeff_slices_rat hq hy
    (fun v => (if x ^ (i * p ^ m + s) * y ^ v ∈ S then (1 : ℚ) else 0)
      - (if x ^ (i' * p ^ m + s) * y ^ v ∈ S then (1 : ℚ) else 0)) hdiff

end QSideGrouping

/-! ## Discharging the linear-disjointness hypothesis

`Φ_{p^(a+1)}` stays the minimal polynomial of `ζ_p` over the coprime cyclotomic
extension `ℚ(ζ_{q^b})`.  The totient-tower proof now lives once, in
`CRTPacketMinpoly.minpoly_adjoin_primitiveRoot_eq_packet`; this section packages the
same fact in the theorem names used by the de Bruijn double-slice layer. -/

section LinearDisjointness

open IntermediateField

/-- **The packet minimal polynomial over the coprime cyclotomic extension**: for
distinct primes `p ≠ q`, `0 < b`, a primitive `p^a`-th root `ξ` and a primitive
`q^b`-th root `η` in a characteristic-zero field `L`, the minimal polynomial of `η`
over `ℚ⟮ξ⟯ = ℚ(ζ_{p^a})` is the geometric packet `Σ_{t<q} X^(t·q^(b-1))` — i.e.
`Φ_{q^b}` remains irreducible over the coprime cyclotomic extension.
(Wrapper around `CRTPacketMinpoly.minpoly_adjoin_primitiveRoot_eq_packet`.) -/
theorem minpoly_adjoin_primitiveRoot_eq_packet
    {L : Type*} [Field L] [CharZero L] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hb : 0 < b)
    {ξ η : L} (hξ : IsPrimitiveRoot ξ (p ^ a)) (hη : IsPrimitiveRoot η (q ^ b)) :
    minpoly ℚ⟮ξ⟯ η = ∑ t ∈ Finset.range q, (X : Polynomial ℚ⟮ξ⟯) ^ (t * q ^ (b - 1)) := by
  exact CRTPacketMinpoly.minpoly_adjoin_primitiveRoot_eq_packet hp hq hpq hb hξ hη

/-- **The `hdisj` discharge in the headline's shape**: `Φ_{p^(a+1)}` IS the minimal
polynomial of `ζ_p` over `ℚ⟮ζ_q⟯` for any primitive `q^b`-th root `ζ_q`, `q ≠ p` —
the linear disjointness of coprime cyclotomic extensions as a theorem. -/
theorem minpoly_qadjoin_eq_cyclotomic {L : Type*} [Field L] [CharZero L] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ζp ζq : L} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ b)) :
    minpoly ℚ⟮ζq⟯ ζp = Polynomial.cyclotomic (p ^ (a + 1)) ℚ⟮ζq⟯ := by
  rw [minpoly_adjoin_primitiveRoot_eq_packet hq hp hpq.symm (Nat.succ_pos a) hζq hζp,
    Polynomial.cyclotomic_prime_pow_eq_geom_sum hp]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Nat.succ_sub_one, mul_comm t (p ^ a), pow_mul]

end LinearDisjointness

/-! ## The headline two-prime instantiations: `K := ℚ(ζ_q)`, unconditional

The former `hdisj` hypothesis is discharged by `minpoly_qadjoin_eq_cyclotomic`: the
headline theorems have NO hypotheses beyond characteristic zero, the two primitive
roots, and the vanishing sum. -/

section TwoPrimeHeadline

open IntermediateField

variable [DecidableEq F] [CharZero F]

/-- **The two-prime q-side slice theorem** at `K := ℚ(ζ_q)`, unconditional: for
`S ⊆ μ_{p^(a+1)·q^b}` with vanishing sum (`p ≠ q` primes), the `ℚ(ζ_q)`-valued
q-side grouped coefficients are constant along `μ_p`-coset directions. -/
theorem two_prime_qside_slices {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1))) (hζq : IsPrimitiveRoot ζq (q ^ b))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ b) = 1)
    (hsum : ∑ z ∈ S, z = 0) :
    ∀ s < p ^ a, ∀ i < p, ∀ i' < p,
      gammaQ S ζp ζq (AdjoinSimple.gen ℚ ζq) (q ^ b) (i * p ^ a + s)
        = gammaQ S ζp ζq (AdjoinSimple.gen ℚ ζq) (q ^ b) (i' * p ^ a + s) :=
  qside_slices_over hp (pow_pos hq.pos b) hζp hζq
    (Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hpq))
    (AdjoinSimple.algebraMap_gen ℚ ζq)
    (minpoly_qadjoin_eq_cyclotomic hp hq hpq hζp hζq) hS hsum

/-- **The headline two-prime de Bruijn double-slice theorem** at `K := ℚ(ζ_q)`,
unconditional: in characteristic zero, for a finite subset `S` of `μ_{p^(a+1)·q^(b+1)}`
with vanishing sum, the membership difference pattern between any two `μ_p`-coset-related
rows is constant along `μ_q`-coset directions of the column index. -/
theorem two_prime_deBruijn_double_slice {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1)
    (hsum : ∑ z ∈ S, z = 0) :
    ∀ s < p ^ a, ∀ i < p, ∀ i' < p, ∀ t < q ^ b, ∀ j < q, ∀ j' < q,
      (if ζp ^ (i * p ^ a + s) * ζq ^ (j * q ^ b + t) ∈ S then (1 : ℚ) else 0)
        - (if ζp ^ (i' * p ^ a + s) * ζq ^ (j * q ^ b + t) ∈ S then (1 : ℚ) else 0)
      = (if ζp ^ (i * p ^ a + s) * ζq ^ (j' * q ^ b + t) ∈ S then (1 : ℚ) else 0)
        - (if ζp ^ (i' * p ^ a + s) * ζq ^ (j' * q ^ b + t) ∈ S then (1 : ℚ) else 0) :=
  two_prime_double_slice hp hq hζp hζq
    (Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hpq))
    (AdjoinSimple.algebraMap_gen ℚ ζq)
    (minpoly_qadjoin_eq_cyclotomic hp hq hpq hζp hζq) hS hsum

/-- Satisfiability of the headline's hypothesis spine in a concrete field: the two
primitive roots exist in `ℂ` and the headline theorem fires (instantiated at the
empty vanishing sum) — no hypothesis hides an unsatisfiable assumption. -/
example :
    let ζp : ℂ := Complex.exp (2 * Real.pi * Complex.I / 4)
    let ζq : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
    ∀ s < 2 ^ 1, ∀ i < 2, ∀ i' < 2, ∀ t < 3 ^ 0, ∀ j < 3, ∀ j' < 3,
      (if ζp ^ (i * 2 ^ 1 + s) * ζq ^ (j * 3 ^ 0 + t) ∈ (∅ : Finset ℂ) then
          (1 : ℚ) else 0)
        - (if ζp ^ (i' * 2 ^ 1 + s) * ζq ^ (j * 3 ^ 0 + t) ∈ (∅ : Finset ℂ) then
          (1 : ℚ) else 0)
      = (if ζp ^ (i * 2 ^ 1 + s) * ζq ^ (j' * 3 ^ 0 + t) ∈ (∅ : Finset ℂ) then
          (1 : ℚ) else 0)
        - (if ζp ^ (i' * 2 ^ 1 + s) * ζq ^ (j' * 3 ^ 0 + t) ∈ (∅ : Finset ℂ) then
          (1 : ℚ) else 0) := by
  classical
  dsimp
  have he4 : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 4)) 4 := by
    have h := Complex.isPrimitiveRoot_exp 4 (by norm_num)
    norm_num at h
    exact h
  have he3 : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 3)) 3 := by
    have h := Complex.isPrimitiveRoot_exp 3 (by norm_num)
    norm_num at h
    exact h
  have h4 : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 4)) (2 ^ (1 + 1)) := by
    norm_num [he4]
  have h3 : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 3)) (3 ^ (0 + 1)) := by
    norm_num [he3]
  have h := two_prime_deBruijn_double_slice Nat.prime_two Nat.prime_three (by norm_num)
    h4 h3 (S := (∅ : Finset ℂ)) (fun z hz => absurd hz (Finset.notMem_empty z)) (by simp)
  exact h

end TwoPrimeHeadline

/-! ## Non-vacuity: the fully unconditional `K = ℚ`, `N = 1` instance

With the second factor trivial, `hmin` is discharged by
`Polynomial.cyclotomic_eq_minpoly_rat`, and the machinery recovers the membership-level
prime-power slice structure (the heart of O66's `vanishing_sum_mu_p_closed`) with NO
named hypotheses — every hypothesis of the framework is simultaneously satisfiable. -/

section NonVacuity

variable [DecidableEq F] [CharZero F]

/-- **Unconditional instance** (`K = ℚ`, `N = 1`): in characteristic zero, a finite
subset of `μ_{p^(m+1)}` with vanishing sum has membership constant along `μ_p`-coset
directions of the exponent — derived entirely through the new `K`-coefficient
double-slice machinery. -/
theorem mu_p_membership_slices {p m : ℕ} (hp : p.Prime) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (p ^ (m + 1)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (m + 1)) = 1)
    (hsum : ∑ z ∈ S, z = 0) :
    ∀ s < p ^ m, ∀ i < p, ∀ i' < p,
      (ζ ^ (i * p ^ m + s) ∈ S ↔ ζ ^ (i' * p ^ m + s) ∈ S) := by
  have h := qside_slices_over (K := ℚ) hp one_pos hζ IsPrimitiveRoot.one
    (Nat.coprime_one_right _) (map_one (algebraMap ℚ F))
    (Polynomial.cyclotomic_eq_minpoly_rat hζ (pow_pos hp.pos _)).symm
    (S := S) (fun z hz => by rw [mul_one]; exact hS z hz) hsum
  intro s hs i hi i' hi'
  have hg := h s hs i hi i' hi'
  simp only [gammaQ, Finset.sum_range_one, pow_zero, mul_one] at hg
  by_cases h1 : ζ ^ (i * p ^ m + s) ∈ S <;> by_cases h2 : ζ ^ (i' * p ^ m + s) ∈ S <;>
    simp [h1, h2] at hg ⊢

end NonVacuity

/-! ## The packet cover: de Bruijn's hard direction

From the unconditional double-slice, the structural dichotomy falls by case analysis:
**every element of a vanishing two-prime subset lies in a full `μ_p`-packet inside `S`
or a full `μ_q`-packet inside `S`.** If `x`'s `p`-fiber misses some point, the
difference row is constantly `1` along the `q`-direction — so `x`'s whole `q`-fiber is
present. This is the necessary half of de Bruijn's theorem (the O70-verified law adds
the disjoint-decomposition refinement: cover alone does not imply vanishing, since
overlapping packets break the sum — recorded honestly). -/

section PacketCover

variable [DecidableEq F] [CharZero F]

/-- **The two-prime packet cover** (de Bruijn's hard direction, unconditional): every
member of a vanishing subset of `μ_{p^(a+1)·q^(b+1)}` has its full `μ_p`-fiber in `S`
or its full `μ_q`-fiber in `S`. -/
theorem two_prime_packet_cover {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1)
    (hsum : ∑ z ∈ S, z = 0) :
    ∀ s < p ^ a, ∀ i < p, ∀ t < q ^ b, ∀ j < q,
      ζp ^ (i * p ^ a + s) * ζq ^ (j * q ^ b + t) ∈ S →
      (∀ i'' < p, ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t) ∈ S) ∨
      (∀ j'' < q, ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t) ∈ S) := by
  intro s hs i hi t ht j hj hx
  by_cases hall : ∀ i'' < p, ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t) ∈ S
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨i', hi', hx'⟩ := hall
    intro j'' hj''
    have hds := two_prime_deBruijn_double_slice hp hq hpq hζp hζq hS hsum
      s hs i hi i' hi' t ht j hj j'' hj''
    rw [if_pos hx, if_neg hx'] at hds
    by_cases h1 : ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t) ∈ S
    · exact h1
    · exfalso
      rw [if_neg h1] at hds
      by_cases h2 : ζp ^ (i' * p ^ a + s) * ζq ^ (j'' * q ^ b + t) ∈ S
      · rw [if_pos h2] at hds
        norm_num at hds
      · rw [if_neg h2] at hds
        norm_num at hds

end PacketCover

/-! ## THE FULL TWO-PRIME DE BRUIJN DECOMPOSITION: peeling induction over the cover

The complete theorem: a vanishing subset of `μ_{p^(a+1)·q^(b+1)}` IS a disjoint union of
full `μ_p`- and `μ_q`-packets. A full packet sums to zero, so peeling the packet supplied
by `two_prime_packet_cover` preserves the vanishing sum; strong induction on cardinality
finishes, with disjointness structural (each peel removes its packet before recursing).
De Bruijn's 1953 theorem at the subset level, machine-checked, hypothesis-free — the
`t = 1` instance of the O70-verified mixed-radix law. -/

section FullDecomposition

variable [DecidableEq F]

/-- `S` is a disjoint union of full `μ_p`- and `μ_q`-packets in the `(ζp, ζq)` box. -/
inductive PacketUnion (p q a b : ℕ) (ζp ζq : F) : Finset F → Prop
  | empty : PacketUnion p q a b ζp ζq ∅
  | addP {S : Finset F} (s j t : ℕ) :
      PacketUnion p q a b ζp ζq S →
      (∀ i'' < p, ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t) ∉ S) →
      PacketUnion p q a b ζp ζq
        (S ∪ (Finset.range p).image
          (fun i'' => ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t)))
  | addQ {S : Finset F} (s i t : ℕ) :
      PacketUnion p q a b ζp ζq S →
      (∀ j'' < q, ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t) ∉ S) →
      PacketUnion p q a b ζp ζq
        (S ∪ (Finset.range q).image
          (fun j'' => ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t)))

omit [DecidableEq F] in
/-- A full prime packet of roots of unity (times any constant) sums to zero. -/
lemma prime_packet_sum_zero {r : ℕ} (hr : r.Prime) {ω : F}
    (hω : IsPrimitiveRoot ω r) (z : F) :
    ∑ k ∈ Finset.range r, ω ^ k * z = 0 := by
  rw [← Finset.sum_mul]
  have hω1 : ω ≠ 1 := by
    intro h
    have h2 := hω.pow_ne_one_of_pos_of_lt (l := 1) one_ne_zero hr.one_lt
    rw [pow_one] at h2
    exact h2 h
  have hgeom : (ω - 1) * ∑ k ∈ Finset.range r, ω ^ k = ω ^ r - 1 := by
    rw [mul_comm]
    exact geom_sum_mul ω r
  rw [hω.pow_eq_one, sub_self] at hgeom
  rcases mul_eq_zero.mp hgeom with h | h
  · exact absurd (by linear_combination h) hω1
  · rw [h, zero_mul]

omit [DecidableEq F] in
/-- Box coordinate bound: `i < r → s < B → i·B + s < r·B`. -/
lemma coord_bound {i r s B : ℕ} (hi : i < r) (hs : s < B) : i * B + s < r * B := by
  have h1 : (i + 1) * B ≤ r * B := Nat.mul_le_mul_right _ (by omega)
  have h2 : i * B + B = (i + 1) * B := by ring
  omega

/-- **Packet-union sufficiency**: every `PacketUnion` certificate has vanishing total
sum.  Thus the inductive decomposition object is not just a shape witness; it is the
converse half of de Bruijn's vanishing theorem. -/
theorem packetUnion_sum_zero {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hU : PacketUnion p q a b ζp ζq S) :
    ∑ z ∈ S, z = 0 := by
  classical
  have hζp0 : ζp ≠ 0 := prim_ne_zero hζp (pow_pos hp.pos _)
  have hζq0 : ζq ≠ 0 := prim_ne_zero hζq (pow_pos hq.pos _)
  have hωp : IsPrimitiveRoot (ζp ^ (p ^ a)) p :=
    hζp.pow (pow_pos hp.pos _) (by rw [pow_succ])
  have hωq : IsPrimitiveRoot (ζq ^ (q ^ b)) q :=
    hζq.pow (pow_pos hq.pos _) (by rw [pow_succ])
  induction hU with
  | empty =>
      simp
  | addP s j t hU hdisj ih =>
      rename_i S₀
      set P : Finset F := (Finset.range p).image
        (fun i'' => ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t)) with hPdef
      have hdis : Disjoint S₀ P := by
        rw [Finset.disjoint_left]
        intro y hyS hyP
        obtain ⟨i'', hi'', rfl⟩ := Finset.mem_image.mp (hPdef ▸ hyP)
        exact hdisj i'' (Finset.mem_range.mp hi'') hyS
      have hinj : ∀ x1 ∈ Finset.range p, ∀ x2 ∈ Finset.range p,
          ζp ^ (x1 * p ^ a + s) * ζq ^ (j * q ^ b + t)
            = ζp ^ (x2 * p ^ a + s) * ζq ^ (j * q ^ b + t) → x1 = x2 := by
        intro x1 hx1 x2 hx2 hxe
        have hconst0 : ζq ^ (j * q ^ b + t) ≠ 0 := pow_ne_zero _ hζq0
        have hs0 : ζp ^ s ≠ 0 := pow_ne_zero _ hζp0
        have hpow : ζp ^ (x1 * p ^ a) = ζp ^ (x2 * p ^ a) := by
          have hcancel := mul_right_cancel₀ hconst0 hxe
          rw [pow_add, pow_add] at hcancel
          exact mul_right_cancel₀ hs0 hcancel
        have hpow' : (ζp ^ (p ^ a)) ^ x1 = (ζp ^ (p ^ a)) ^ x2 := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm (p ^ a) x1, Nat.mul_comm (p ^ a) x2]
          exact hpow
        exact hωp.pow_inj (Finset.mem_range.mp hx1) (Finset.mem_range.mp hx2) hpow'
      have hPsum : ∑ y ∈ P, y = 0 := by
        rw [hPdef, Finset.sum_image hinj]
        have hterm : ∀ i'' ∈ Finset.range p,
            ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t)
              = (ζp ^ (p ^ a)) ^ i'' * (ζp ^ s * ζq ^ (j * q ^ b + t)) := by
          intro i'' _
          rw [pow_add, ← pow_mul, Nat.mul_comm (p ^ a) i'']
          ring
        rw [Finset.sum_congr rfl hterm]
        exact prime_packet_sum_zero hp hωp _
      rw [Finset.sum_union hdis, ih, hPsum, add_zero]
  | addQ s i t hU hdisj ih =>
      rename_i S₀
      set P : Finset F := (Finset.range q).image
        (fun j'' => ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t)) with hPdef
      have hdis : Disjoint S₀ P := by
        rw [Finset.disjoint_left]
        intro y hyS hyP
        obtain ⟨j'', hj'', rfl⟩ := Finset.mem_image.mp (hPdef ▸ hyP)
        exact hdisj j'' (Finset.mem_range.mp hj'') hyS
      have hinj : ∀ x1 ∈ Finset.range q, ∀ x2 ∈ Finset.range q,
          ζp ^ (i * p ^ a + s) * ζq ^ (x1 * q ^ b + t)
            = ζp ^ (i * p ^ a + s) * ζq ^ (x2 * q ^ b + t) → x1 = x2 := by
        intro x1 hx1 x2 hx2 hxe
        have hconst0 : ζp ^ (i * p ^ a + s) ≠ 0 := pow_ne_zero _ hζp0
        have ht0 : ζq ^ t ≠ 0 := pow_ne_zero _ hζq0
        have hpow : ζq ^ (x1 * q ^ b) = ζq ^ (x2 * q ^ b) := by
          have hcancel := mul_left_cancel₀ hconst0 hxe
          rw [pow_add, pow_add] at hcancel
          exact mul_right_cancel₀ ht0 hcancel
        have hpow' : (ζq ^ (q ^ b)) ^ x1 = (ζq ^ (q ^ b)) ^ x2 := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm (q ^ b) x1, Nat.mul_comm (q ^ b) x2]
          exact hpow
        exact hωq.pow_inj (Finset.mem_range.mp hx1) (Finset.mem_range.mp hx2) hpow'
      have hPsum : ∑ y ∈ P, y = 0 := by
        rw [hPdef, Finset.sum_image hinj]
        have hterm : ∀ j'' ∈ Finset.range q,
            ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t)
              = (ζq ^ (q ^ b)) ^ j'' * (ζp ^ (i * p ^ a + s) * ζq ^ t) := by
          intro j'' _
          rw [pow_add (a := ζq), ← pow_mul, Nat.mul_comm (q ^ b) j'']
          ring
        rw [Finset.sum_congr rfl hterm]
        exact prime_packet_sum_zero hq hωq _
      rw [Finset.sum_union hdis, ih, hPsum, add_zero]

variable [CharZero F]

/-- **THE FULL TWO-PRIME DE BRUIJN DECOMPOSITION** (unconditional, characteristic zero):
a finite subset of `μ_{p^(a+1)·q^(b+1)}` with vanishing sum is a disjoint union of full
`μ_p`- and `μ_q`-packets. -/
theorem two_prime_packet_decomposition {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1)
    (hsum : ∑ z ∈ S, z = 0) :
    PacketUnion p q a b ζp ζq S := by
  classical
  have hcop : Nat.Coprime (p ^ (a + 1)) (q ^ (b + 1)) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hpq)
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  have hqb : 0 < q ^ b := pow_pos hq.pos b
  have hsuccp : p ^ (a + 1) = p * p ^ a := by rw [pow_succ']
  have hsuccq : q ^ (b + 1) = q * q ^ b := by rw [pow_succ']
  have hωp : IsPrimitiveRoot (ζp ^ (p ^ a)) p :=
    hζp.pow (pow_pos hp.pos _) (by rw [pow_succ])
  have hωq : IsPrimitiveRoot (ζq ^ (q ^ b)) q :=
    hζq.pow (pow_pos hq.pos _) (by rw [pow_succ])
  suffices H : ∀ n (T : Finset F), T.card = n →
      (∀ z ∈ T, z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1) → (∑ z ∈ T, z = 0) →
      PacketUnion p q a b ζp ζq T from H S.card S rfl hS hsum
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro T hcard hT hsumT
    rcases Finset.eq_empty_or_nonempty T with rfl | ⟨z, hz⟩
    · exact PacketUnion.empty
    obtain ⟨u, hu, v, hv, huv⟩ := box_pair_surj hζp hζq hcop
      (pow_pos hp.pos _) (pow_pos hq.pos _) (hT z hz)
    obtain ⟨i, s, rfl, hs⟩ : ∃ i' s', u = i' * p ^ a + s' ∧ s' < p ^ a :=
      ⟨u / p ^ a, u % p ^ a, (Nat.div_add_mod' u (p ^ a)).symm, Nat.mod_lt _ hpa⟩
    obtain ⟨j, t, rfl, ht⟩ : ∃ j' t', v = j' * q ^ b + t' ∧ t' < q ^ b :=
      ⟨v / q ^ b, v % q ^ b, (Nat.div_add_mod' v (q ^ b)).symm, Nat.mod_lt _ hqb⟩
    rw [hsuccp] at hu
    rw [hsuccq] at hv
    have hi : i < p := by
      by_contra hge
      push Not at hge
      have := Nat.mul_le_mul_right (p ^ a) hge
      omega
    have hj : j < q := by
      by_contra hge
      push Not at hge
      have := Nat.mul_le_mul_right (q ^ b) hge
      omega
    have hzmem : ζp ^ (i * p ^ a + s) * ζq ^ (j * q ^ b + t) ∈ T := by rwa [huv]
    rcases two_prime_packet_cover hp hq hpq hζp hζq hT hsumT s hs i hi t ht j hj hzmem
      with hFull | hFull
    · -- peel the μ_p-packet
      set P : Finset F := (Finset.range p).image
        (fun i'' => ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t)) with hPdef
      have hPsub : P ⊆ T := by
        intro y hy
        obtain ⟨i'', hi'', rfl⟩ := Finset.mem_image.mp hy
        exact hFull i'' (Finset.mem_range.mp hi'')
      have hinj : ∀ x1 ∈ Finset.range p, ∀ x2 ∈ Finset.range p,
          ζp ^ (x1 * p ^ a + s) * ζq ^ (j * q ^ b + t)
            = ζp ^ (x2 * p ^ a + s) * ζq ^ (j * q ^ b + t) → x1 = x2 := by
        intro x1 hx1 x2 hx2 hxe
        have h1 := coord_bound (Finset.mem_range.mp hx1) hs
        have h2 := coord_bound (Finset.mem_range.mp hx2) hs
        have h3 := coord_bound hj ht
        have heq := (box_pair_inj hζp hζq hcop (by omega) (by omega) (by omega) (by omega)
          hxe).1
        have hmul : x1 * p ^ a = x2 * p ^ a := by omega
        exact Nat.eq_of_mul_eq_mul_right hpa hmul
      have hPcard : P.card = p := by
        rw [hPdef, Finset.card_image_of_injOn (fun x1 hx1 x2 hx2 h =>
          hinj x1 (Finset.mem_coe.mp hx1) x2 (Finset.mem_coe.mp hx2) h),
          Finset.card_range]
      have hPsum : ∑ y ∈ P, y = 0 := by
        rw [hPdef, Finset.sum_image hinj]
        have hterm : ∀ i'' ∈ Finset.range p,
            ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t)
              = (ζp ^ (p ^ a)) ^ i'' * (ζp ^ s * ζq ^ (j * q ^ b + t)) := by
          intro i'' _
          rw [pow_add, ← pow_mul, mul_comm i'' (p ^ a), pow_mul]
          ring
        rw [Finset.sum_congr rfl hterm]
        exact prime_packet_sum_zero hp hωp _
      have hT'sum : ∑ y ∈ T \ P, y = 0 := by
        have hsd := Finset.sum_sdiff (f := fun y : F => y) hPsub
        rw [hPsum, add_zero] at hsd
        rw [hsd]
        exact hsumT
      have hT'card : (T \ P).card < n := by
        have hPT : P ∩ T = P := Finset.inter_eq_left.mpr hPsub
        rw [Finset.card_sdiff, hPT, hPcard, ← hcard]
        have hple : p ≤ T.card := by
          rw [← hPcard]
          exact Finset.card_le_card hPsub
        have := hp.pos
        omega
      have hIH := IH (T \ P).card hT'card (T \ P) rfl
        (fun y hy => hT y (Finset.mem_sdiff.mp hy).1) hT'sum
      have hnotmem : ∀ i'' < p,
          ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t) ∉ T \ P := by
        intro i'' hi'' hmem
        exact (Finset.mem_sdiff.mp hmem).2
          (Finset.mem_image.mpr ⟨i'', Finset.mem_range.mpr hi'', rfl⟩)
      have hassemble := PacketUnion.addP (S := T \ P) s j t hIH hnotmem
      rwa [← hPdef, Finset.sdiff_union_of_subset hPsub] at hassemble
    · -- peel the μ_q-packet (mirror)
      set P : Finset F := (Finset.range q).image
        (fun j'' => ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t)) with hPdef
      have hPsub : P ⊆ T := by
        intro y hy
        obtain ⟨j'', hj'', rfl⟩ := Finset.mem_image.mp hy
        exact hFull j'' (Finset.mem_range.mp hj'')
      have hinj : ∀ x1 ∈ Finset.range q, ∀ x2 ∈ Finset.range q,
          ζp ^ (i * p ^ a + s) * ζq ^ (x1 * q ^ b + t)
            = ζp ^ (i * p ^ a + s) * ζq ^ (x2 * q ^ b + t) → x1 = x2 := by
        intro x1 hx1 x2 hx2 hxe
        have h1 := coord_bound (Finset.mem_range.mp hx1) ht
        have h2 := coord_bound (Finset.mem_range.mp hx2) ht
        have h3 := coord_bound hi hs
        have heq := (box_pair_inj hζp hζq hcop (by omega) (by omega) (by omega) (by omega)
          hxe).2
        have hmul : x1 * q ^ b = x2 * q ^ b := by omega
        exact Nat.eq_of_mul_eq_mul_right hqb hmul
      have hPcard : P.card = q := by
        rw [hPdef, Finset.card_image_of_injOn (fun x1 hx1 x2 hx2 h =>
          hinj x1 (Finset.mem_coe.mp hx1) x2 (Finset.mem_coe.mp hx2) h),
          Finset.card_range]
      have hPsum : ∑ y ∈ P, y = 0 := by
        rw [hPdef, Finset.sum_image hinj]
        have hterm : ∀ j'' ∈ Finset.range q,
            ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t)
              = (ζq ^ (q ^ b)) ^ j'' * (ζp ^ (i * p ^ a + s) * ζq ^ t) := by
          intro j'' _
          rw [pow_add (a := ζq), ← pow_mul, mul_comm j'' (q ^ b), pow_mul]
          ring
        rw [Finset.sum_congr rfl hterm]
        exact prime_packet_sum_zero hq hωq _
      have hT'sum : ∑ y ∈ T \ P, y = 0 := by
        have hsd := Finset.sum_sdiff (f := fun y : F => y) hPsub
        rw [hPsum, add_zero] at hsd
        rw [hsd]
        exact hsumT
      have hT'card : (T \ P).card < n := by
        have hPT : P ∩ T = P := Finset.inter_eq_left.mpr hPsub
        rw [Finset.card_sdiff, hPT, hPcard, ← hcard]
        have hqle : q ≤ T.card := by
          rw [← hPcard]
          exact Finset.card_le_card hPsub
        have := hq.pos
        omega
      have hIH := IH (T \ P).card hT'card (T \ P) rfl
        (fun y hy => hT y (Finset.mem_sdiff.mp hy).1) hT'sum
      have hnotmem : ∀ j'' < q,
          ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t) ∉ T \ P := by
        intro j'' hj'' hmem
        exact (Finset.mem_sdiff.mp hmem).2
          (Finset.mem_image.mpr ⟨j'', Finset.mem_range.mpr hj'', rfl⟩)
      have hassemble := PacketUnion.addQ (S := T \ P) s i t hIH hnotmem
      rwa [← hPdef, Finset.sdiff_union_of_subset hPsub] at hassemble

/-- **Two-prime de Bruijn iff, certificate form**: for subsets of
`μ_{p^(a+1)·q^(b+1)}`, vanishing is equivalent to possessing a `PacketUnion`
decomposition into disjoint full prime packets. -/
theorem two_prime_packet_decomposition_iff {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1) :
    (∑ z ∈ S, z = 0) ↔ PacketUnion p q a b ζp ζq S := by
  constructor
  · exact two_prime_packet_decomposition hp hq hpq hζp hζq hS
  · exact packetUnion_sum_zero hp hq hζp hζq

end FullDecomposition

/-! ## Structural corollary: small vanishing sets are `μ_p`-closed

The bridge from `PacketUnion` toward the O73 base-hypothesis format. The sum-only
closure hypothesis is FALSE at genuinely two-prime levels (a rotated `μ_q`-packet is a
vanishing set that is not `μ_p`-closed — exactly what the decomposition predicts), so
the discharge is necessarily sectoral. Here: the cardinality sector `|T| < q`, where no
`μ_q`-packet fits, the decomposition is forced pure-`p`, and `μ_p`-closure follows —
with O77, an UNCONDITIONAL closure theorem for small vanishing sets
(`small_vanishing_mu_p_closed`). The windowed sectors are the remaining induction. -/

section StructuralCorollaries

variable [DecidableEq F]

/-- **Pure-`p` forcing in the small sector**: a `PacketUnion` of cardinality `< q`
contains no `μ_q`-packet, hence is closed under every `p`-th root of unity. -/
theorem packetUnion_mu_p_closed_of_card_lt {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {T : Finset F} (hPU : PacketUnion p q a b ζp ζq T) (hcard : T.card < q) :
    ∀ x ∈ T, ∀ g : F, g ^ p = 1 → g * x ∈ T := by
  classical
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hωp : IsPrimitiveRoot (ζp ^ (p ^ a)) p :=
    hζp.pow (pow_pos hp.pos _) (by rw [pow_succ])
  have hωq : IsPrimitiveRoot (ζq ^ (q ^ b)) q :=
    hζq.pow (pow_pos hq.pos _) (by rw [pow_succ])
  revert hcard
  induction hPU with
  | empty =>
    intro _ x hx
    exact absurd hx (Finset.notMem_empty x)
  | @addP S s j t hsub hnot IH =>
    intro hcard x hx g hg
    have hScard : S.card < q :=
      lt_of_le_of_lt (Finset.card_le_card Finset.subset_union_left) hcard
    rcases Finset.mem_union.mp hx with hxS | hxP
    · exact Finset.mem_union_left _ (IH hScard x hxS g hg)
    · obtain ⟨i'', hi'', rfl⟩ := Finset.mem_image.mp hxP
      obtain ⟨k, hk, hkg⟩ := hωp.eq_pow_of_pow_eq_one hg
      refine Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(k + i'') % p, Finset.mem_range.mpr (Nat.mod_lt _ hp.pos), ?_⟩)
      have hgz : g * ζp ^ (i'' * p ^ a + s)
          = ζp ^ (((k + i'') % p) * p ^ a + s) := by
        rw [← hkg, ← pow_mul, ← pow_add]
        have hdecomp : p ^ a * k + (i'' * p ^ a + s)
            = p ^ (a + 1) * ((k + i'') / p) + (((k + i'') % p) * p ^ a + s) := by
          have hsplit : k + i'' = p * ((k + i'') / p) + (k + i'') % p :=
            (Nat.div_add_mod _ p).symm
          calc p ^ a * k + (i'' * p ^ a + s) = (k + i'') * p ^ a + s := by ring
          _ = (p * ((k + i'') / p) + (k + i'') % p) * p ^ a + s := by rw [← hsplit]
          _ = (p * p ^ a) * ((k + i'') / p) + (((k + i'') % p) * p ^ a + s) := by ring
          _ = p ^ (a + 1) * ((k + i'') / p) + (((k + i'') % p) * p ^ a + s) := by
              rw [← pow_succ']
        rw [hdecomp, pow_add, pow_mul, hζp.pow_eq_one, one_pow, one_mul]
      rw [← mul_assoc, hgz]
  | @addQ S s i t hsub hnot IH =>
    intro hcard
    exfalso
    set P : Finset F := (Finset.range q).image
      (fun j'' => ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t)) with hPdef
    have hPcard : P.card = q := by
      rw [hPdef, Finset.card_image_of_injOn, Finset.card_range]
      intro x1 hx1 x2 hx2 hxe
      have hx1q := Finset.mem_range.mp (Finset.mem_coe.mp hx1)
      have hx2q := Finset.mem_range.mp (Finset.mem_coe.mp hx2)
      have hzp0 : ζp ^ (i * p ^ a + s) ≠ 0 :=
        pow_ne_zero _ (prim_ne_zero hζp (pow_pos hp.pos _))
      have hzt0 : ζq ^ t ≠ 0 := pow_ne_zero _ (prim_ne_zero hζq (pow_pos hq.pos _))
      have hcancel : ζq ^ (x1 * q ^ b) = ζq ^ (x2 * q ^ b) := by
        have h1 : ζq ^ (x1 * q ^ b + t) = ζq ^ (x2 * q ^ b + t) :=
          mul_left_cancel₀ hzp0 hxe
        rw [pow_add, pow_add] at h1
        exact mul_right_cancel₀ hzt0 h1
      have hω : (ζq ^ (q ^ b)) ^ x1 = (ζq ^ (q ^ b)) ^ x2 := by
        rw [← pow_mul, ← pow_mul, mul_comm (q ^ b) x1, mul_comm (q ^ b) x2]
        exact hcancel
      exact hωq.pow_inj hx1q hx2q hω
    have hPsub : P ⊆ S ∪ P := Finset.subset_union_right
    have : q ≤ (S ∪ P).card := by
      rw [← hPcard]
      exact Finset.card_le_card hPsub
    omega

variable [CharZero F]

omit [DecidableEq F] in
/-- **Unconditional small-sector closure**: a vanishing subset of
`μ_{p^(a+1)·q^(b+1)}` with fewer than `q` elements is closed under every `p`-th root of
unity — O77 + pure-`p` forcing, no hypotheses. -/
theorem small_vanishing_mu_p_closed {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1)
    (hsum : ∑ z ∈ S, z = 0) (hcard : S.card < q) :
    ∀ x ∈ S, ∀ g : F, g ^ p = 1 → g * x ∈ S := by
  classical
  exact packetUnion_mu_p_closed_of_card_lt hp hq hζp hζq
    (two_prime_packet_decomposition hp hq hpq hζp hζq hS hsum) hcard

end StructuralCorollaries

/-! ## The q-power descent: the q-packet spectrum drops one level

The key lemma of the windowed program. On a `PacketUnion`, the `q`-th power sum sees
only the `μ_q`-packets — each `μ_p`-packet contributes zero at exponent `q` (the twisted
packet sum, `p ∤ q`), while each `μ_q`-packet contributes `q · z^q` (its common rep
power). The spectrum `R` of rep powers is collision-free by the orbit argument: equal
`q`-th powers differ by a `q`-th root of unity, which would place a new rep inside an
old packet. Hence `Σ_{y∈S} y^q = q · Σ_{r∈R} r` with `R` a genuine SUBSET one `q`-level
down — a window condition at exponent `q` forces `Σ_R r = 0` (characteristic zero) and
the recursion closes onto level `b`. -/

section QPowerDescent

variable [DecidableEq F]

/-- **The q-power descent**: the `q`-th power sum of a packet union is `q` times the sum
of a collision-free spectrum `R`, each of whose members is the common `q`-th power of a
full `μ_q`-orbit inside `S`. -/
theorem packetUnion_qpow_descent {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hPU : PacketUnion p q a b ζp ζq S) :
    ∃ R : Finset F,
      (∀ r ∈ R, ∃ w ∈ S, w ^ q = r ∧ ∀ g : F, g ^ q = 1 → g * w ∈ S) ∧
      ∑ y ∈ S, y ^ q = (q : F) * ∑ r ∈ R, r := by
  classical
  have hζp0 : ζp ≠ 0 := prim_ne_zero hζp (pow_pos hp.pos _)
  have hζq0 : ζq ≠ 0 := prim_ne_zero hζq (pow_pos hq.pos _)
  have hωp : IsPrimitiveRoot (ζp ^ (p ^ a)) p :=
    hζp.pow (pow_pos hp.pos _) (by rw [pow_succ])
  have hωq : IsPrimitiveRoot (ζq ^ (q ^ b)) q :=
    hζq.pow (pow_pos hq.pos _) (by rw [pow_succ])
  have hωpq : IsPrimitiveRoot ((ζp ^ (p ^ a)) ^ q) p :=
    hωp.pow_of_coprime q ((Nat.coprime_primes hq hp).mpr (Ne.symm hpq))
  induction hPU with
  | empty =>
    exact ⟨∅, fun r hr => absurd hr (Finset.notMem_empty r), by simp⟩
  | @addP S₀ s j t hsub hnot IH =>
    obtain ⟨R, hRorbit, hRsum⟩ := IH
    set P : Finset F := (Finset.range p).image
      (fun i'' => ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t)) with hPdef
    have hdis : Disjoint S₀ P := by
      rw [Finset.disjoint_left]
      intro y hyS hyP
      obtain ⟨i'', hi'', rfl⟩ := Finset.mem_image.mp (hPdef ▸ hyP)
      exact hnot i'' (Finset.mem_range.mp hi'') hyS
    have hinj : ∀ x1 ∈ Finset.range p, ∀ x2 ∈ Finset.range p,
        ζp ^ (x1 * p ^ a + s) * ζq ^ (j * q ^ b + t)
          = ζp ^ (x2 * p ^ a + s) * ζq ^ (j * q ^ b + t) → x1 = x2 := by
      intro x1 hx1 x2 hx2 hxe
      have hconst0 : ζq ^ (j * q ^ b + t) ≠ 0 := pow_ne_zero _ hζq0
      have hs0 : ζp ^ s ≠ 0 := pow_ne_zero _ hζp0
      have hpow : ζp ^ (x1 * p ^ a) = ζp ^ (x2 * p ^ a) := by
        have hcancel := mul_right_cancel₀ hconst0 hxe
        rw [pow_add, pow_add] at hcancel
        exact mul_right_cancel₀ hs0 hcancel
      have hpow' : (ζp ^ (p ^ a)) ^ x1 = (ζp ^ (p ^ a)) ^ x2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (p ^ a) x1, Nat.mul_comm (p ^ a) x2]
        exact hpow
      exact hωp.pow_inj (Finset.mem_range.mp hx1) (Finset.mem_range.mp hx2) hpow'
    have hPsum : ∑ y ∈ P, y ^ q = 0 := by
      rw [hPdef, Finset.sum_image hinj]
      have hterm : ∀ i'' ∈ Finset.range p,
          (ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t)) ^ q
            = ((ζp ^ (p ^ a)) ^ q) ^ i''
              * ((ζp ^ s) ^ q * (ζq ^ (j * q ^ b + t)) ^ q) := by
        intro i'' _
        ring
      rw [Finset.sum_congr rfl hterm]
      exact prime_packet_sum_zero hp hωpq _
    refine ⟨R, ?_, ?_⟩
    · intro r hr
      obtain ⟨w, hw, hwq, horbit⟩ := hRorbit r hr
      exact ⟨w, Finset.mem_union_left _ hw, hwq,
        fun g hg => Finset.mem_union_left _ (horbit g hg)⟩
    · rw [Finset.sum_union hdis, hRsum, hPsum, add_zero]
  | @addQ S₀ s i t hsub hnot IH =>
    obtain ⟨R, hRorbit, hRsum⟩ := IH
    set P : Finset F := (Finset.range q).image
      (fun j'' => ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t)) with hPdef
    set z₀ : F := ζp ^ (i * p ^ a + s) * ζq ^ t with hz₀
    have hz₀P : z₀ ∈ P := by
      rw [hPdef]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hq.pos, by
        rw [hz₀, Nat.zero_mul, Nat.zero_add]⟩
    have hdis : Disjoint S₀ P := by
      rw [Finset.disjoint_left]
      intro y hyS hyP
      obtain ⟨j'', hj'', rfl⟩ := Finset.mem_image.mp (hPdef ▸ hyP)
      exact hnot j'' (Finset.mem_range.mp hj'') hyS
    have hinj : ∀ x1 ∈ Finset.range q, ∀ x2 ∈ Finset.range q,
        ζp ^ (i * p ^ a + s) * ζq ^ (x1 * q ^ b + t)
          = ζp ^ (i * p ^ a + s) * ζq ^ (x2 * q ^ b + t) → x1 = x2 := by
      intro x1 hx1 x2 hx2 hxe
      have hconst0 : ζp ^ (i * p ^ a + s) ≠ 0 := pow_ne_zero _ hζp0
      have ht0 : ζq ^ t ≠ 0 := pow_ne_zero _ hζq0
      have hpow : ζq ^ (x1 * q ^ b) = ζq ^ (x2 * q ^ b) := by
        have hcancel := mul_left_cancel₀ hconst0 hxe
        rw [pow_add, pow_add] at hcancel
        exact mul_right_cancel₀ ht0 hcancel
      have hpow' : (ζq ^ (q ^ b)) ^ x1 = (ζq ^ (q ^ b)) ^ x2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (q ^ b) x1, Nat.mul_comm (q ^ b) x2]
        exact hpow
      exact hωq.pow_inj (Finset.mem_range.mp hx1) (Finset.mem_range.mp hx2) hpow'
    -- every element of the q-packet has q-th power z₀^q
    have hcommon : ∀ y ∈ P, y ^ q = z₀ ^ q := by
      intro y hy
      obtain ⟨j'', _, rfl⟩ := Finset.mem_image.mp (hPdef ▸ hy)
      have hone : ((ζq ^ (j'' * q ^ b)) : F) ^ q = 1 := by
        rw [← pow_mul, show j'' * q ^ b * q = q ^ (b + 1) * j'' from by ring,
          pow_mul, hζq.pow_eq_one, one_pow]
      calc (ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t)) ^ q
          = (ζp ^ (i * p ^ a + s)) ^ q
            * ((ζq ^ (j'' * q ^ b)) ^ q * (ζq ^ t) ^ q) := by
            rw [pow_add (a := ζq)]
            ring
        _ = (ζp ^ (i * p ^ a + s)) ^ q * (ζq ^ t) ^ q := by rw [hone, one_mul]
        _ = z₀ ^ q := by rw [hz₀]; ring
    have hPsum : ∑ y ∈ P, y ^ q = (q : F) * z₀ ^ q := by
      rw [Finset.sum_congr rfl hcommon, Finset.sum_const]
      have hPcard : P.card = q := by
        rw [hPdef, Finset.card_image_of_injOn (fun x1 hx1 x2 hx2 h =>
          hinj x1 (Finset.mem_coe.mp hx1) x2 (Finset.mem_coe.mp hx2) h),
          Finset.card_range]
      rw [hPcard, nsmul_eq_mul]
    -- the new spectrum point is fresh: the orbit argument
    have hfresh : z₀ ^ q ∉ R := by
      intro hmem
      obtain ⟨w, hwS, hwq, horbit⟩ := hRorbit (z₀ ^ q) hmem
      have hz₀0 : z₀ ≠ 0 := by
        rw [hz₀]
        exact mul_ne_zero (pow_ne_zero _ hζp0) (pow_ne_zero _ hζq0)
      have hw0 : w ≠ 0 := by
        intro h0
        rw [h0] at hwq
        exact pow_ne_zero q hz₀0 (by rw [← hwq, zero_pow hq.pos.ne'])
      have hg : (z₀ / w) ^ q = 1 := by
        rw [div_pow, hwq, div_self (pow_ne_zero q hz₀0)]
      have hz₀S : z₀ ∈ S₀ := by
        have := horbit (z₀ / w) hg
        rwa [div_mul_cancel₀ z₀ hw0] at this
      exact (Finset.disjoint_left.mp hdis hz₀S) hz₀P
    refine ⟨insert (z₀ ^ q) R, ?_, ?_⟩
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hrR
      · refine ⟨z₀, Finset.mem_union_right _ hz₀P, rfl, ?_⟩
        intro g hg
        haveI : NeZero q := ⟨hq.pos.ne'⟩
        obtain ⟨k, hk, hkg⟩ := hωq.eq_pow_of_pow_eq_one hg
        refine Finset.mem_union_right _ ?_
        rw [hPdef]
        refine Finset.mem_image.mpr ⟨k % q, Finset.mem_range.mpr (Nat.mod_lt _ hq.pos), ?_⟩
        symm
        rw [← hkg, hz₀]
        have hsplit : k = q * (k / q) + k % q := (Nat.div_add_mod _ q).symm
        have hdecomp : q ^ b * k + t = q ^ (b + 1) * (k / q) + ((k % q) * q ^ b + t) := by
          calc q ^ b * k + t = q ^ b * (q * (k / q) + k % q) + t := by rw [← hsplit]
          _ = (q ^ b * q) * (k / q) + ((k % q) * q ^ b + t) := by ring
          _ = q ^ (b + 1) * (k / q) + ((k % q) * q ^ b + t) := by rw [← pow_succ]
        have hqeq : ζq ^ (q ^ b * k) * ζq ^ t = ζq ^ ((k % q) * q ^ b + t) := by
          rw [← pow_add, hdecomp, pow_add, pow_mul, hζq.pow_eq_one, one_pow, one_mul]
        calc (ζq ^ (q ^ b)) ^ k * (ζp ^ (i * p ^ a + s) * ζq ^ t)
            = ζp ^ (i * p ^ a + s) * (ζq ^ (q ^ b * k) * ζq ^ t) := by
              rw [← pow_mul]
              ring
          _ = ζp ^ (i * p ^ a + s) * ζq ^ ((k % q) * q ^ b + t) := by
              rw [hqeq]
      · obtain ⟨w, hw, hwq, horbit⟩ := hRorbit r hrR
        exact ⟨w, Finset.mem_union_left _ hw, hwq,
          fun g hg => Finset.mem_union_left _ (horbit g hg)⟩
    · rw [Finset.sum_union hdis, hRsum, hPsum, Finset.sum_insert hfresh, mul_add]
      ring

end QPowerDescent

/-! ## The spectral syndrome transfer: the full window descends to the spectrum

The complete generalization of the q-power descent: ONE spectrum `R` carries the entire
syndrome window — for EVERY exponent `e` not divisible by `p`,
`Σ_{y∈S} y^{q·e} = q · Σ_{r∈R} r^e`. The `μ_p`-packets die at every such exponent
(`ω_p^{qe}` is still primitive since `p ∤ qe`), each `μ_q`-packet contributes
`q·z^{qe} = q·r^e`, and the spectrum is the same for all `e`. Consequence: a window of
`S` at the exponents `{q·e : e ≤ w, p ∤ e}` becomes a window of `R` at `{e ≤ w, p ∤ e}`
one `q`-level down — the recursion step of the windowed two-prime law, in full. -/

section SpectralTransfer

variable [DecidableEq F]

/-- **The spectral syndrome transfer**: one spectrum carries every exponent `p ∤ e`. -/
theorem packetUnion_spectral_transfer {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hPU : PacketUnion p q a b ζp ζq S) :
    ∃ R : Finset F,
      (∀ r ∈ R, ∃ w ∈ S, w ^ q = r ∧ ∀ g : F, g ^ q = 1 → g * w ∈ S) ∧
      ∀ e : ℕ, ¬ p ∣ e →
        ∑ y ∈ S, y ^ (q * e) = (q : F) * ∑ r ∈ R, r ^ e := by
  classical
  have hζp0 : ζp ≠ 0 := prim_ne_zero hζp (pow_pos hp.pos _)
  have hζq0 : ζq ≠ 0 := prim_ne_zero hζq (pow_pos hq.pos _)
  have hωp : IsPrimitiveRoot (ζp ^ (p ^ a)) p :=
    hζp.pow (pow_pos hp.pos _) (by rw [pow_succ])
  have hωq : IsPrimitiveRoot (ζq ^ (q ^ b)) q :=
    hζq.pow (pow_pos hq.pos _) (by rw [pow_succ])
  induction hPU with
  | empty =>
    exact ⟨∅, fun r hr => absurd hr (Finset.notMem_empty r), by simp⟩
  | @addP S₀ s j t hsub hnot IH =>
    obtain ⟨R, hRorbit, hRsum⟩ := IH
    set P : Finset F := (Finset.range p).image
      (fun i'' => ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t)) with hPdef
    have hdis : Disjoint S₀ P := by
      rw [Finset.disjoint_left]
      intro y hyS hyP
      obtain ⟨i'', hi'', rfl⟩ := Finset.mem_image.mp (hPdef ▸ hyP)
      exact hnot i'' (Finset.mem_range.mp hi'') hyS
    have hinj : ∀ x1 ∈ Finset.range p, ∀ x2 ∈ Finset.range p,
        ζp ^ (x1 * p ^ a + s) * ζq ^ (j * q ^ b + t)
          = ζp ^ (x2 * p ^ a + s) * ζq ^ (j * q ^ b + t) → x1 = x2 := by
      intro x1 hx1 x2 hx2 hxe
      have hconst0 : ζq ^ (j * q ^ b + t) ≠ 0 := pow_ne_zero _ hζq0
      have hs0 : ζp ^ s ≠ 0 := pow_ne_zero _ hζp0
      have hpow : ζp ^ (x1 * p ^ a) = ζp ^ (x2 * p ^ a) := by
        have hcancel := mul_right_cancel₀ hconst0 hxe
        rw [pow_add, pow_add] at hcancel
        exact mul_right_cancel₀ hs0 hcancel
      have hpow' : (ζp ^ (p ^ a)) ^ x1 = (ζp ^ (p ^ a)) ^ x2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (p ^ a) x1, Nat.mul_comm (p ^ a) x2]
        exact hpow
      exact hωp.pow_inj (Finset.mem_range.mp hx1) (Finset.mem_range.mp hx2) hpow'
    refine ⟨R, ?_, ?_⟩
    · intro r hr
      obtain ⟨w, hw, hwq, horbit⟩ := hRorbit r hr
      exact ⟨w, Finset.mem_union_left _ hw, hwq,
        fun g hg => Finset.mem_union_left _ (horbit g hg)⟩
    · intro e hpe
      have hωpe : IsPrimitiveRoot ((ζp ^ (p ^ a)) ^ (q * e)) p := by
        refine hωp.pow_of_coprime _ ?_
        have hqp : Nat.Coprime q p := (Nat.coprime_primes hq hp).mpr (Ne.symm hpq)
        have hep : Nat.Coprime e p := by
          rcases Nat.coprime_or_dvd_of_prime hp e with h | h
          · exact h.symm
          · exact absurd h hpe
        exact Nat.Coprime.mul_left hqp hep
      have hPsum : ∑ y ∈ P, y ^ (q * e) = 0 := by
        rw [hPdef, Finset.sum_image hinj]
        have hterm : ∀ i'' ∈ Finset.range p,
            (ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t)) ^ (q * e)
              = ((ζp ^ (p ^ a)) ^ (q * e)) ^ i''
                * ((ζp ^ s) ^ (q * e) * (ζq ^ (j * q ^ b + t)) ^ (q * e)) := by
          intro i'' _
          ring
        rw [Finset.sum_congr rfl hterm]
        exact prime_packet_sum_zero hp hωpe _
      rw [Finset.sum_union hdis, hRsum e hpe, hPsum, add_zero]
  | @addQ S₀ s i t hsub hnot IH =>
    obtain ⟨R, hRorbit, hRsum⟩ := IH
    set P : Finset F := (Finset.range q).image
      (fun j'' => ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t)) with hPdef
    set z₀ : F := ζp ^ (i * p ^ a + s) * ζq ^ t with hz₀
    have hz₀P : z₀ ∈ P := by
      rw [hPdef]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hq.pos, by
        rw [hz₀, Nat.zero_mul, Nat.zero_add]⟩
    have hdis : Disjoint S₀ P := by
      rw [Finset.disjoint_left]
      intro y hyS hyP
      obtain ⟨j'', hj'', rfl⟩ := Finset.mem_image.mp (hPdef ▸ hyP)
      exact hnot j'' (Finset.mem_range.mp hj'') hyS
    have hinj : ∀ x1 ∈ Finset.range q, ∀ x2 ∈ Finset.range q,
        ζp ^ (i * p ^ a + s) * ζq ^ (x1 * q ^ b + t)
          = ζp ^ (i * p ^ a + s) * ζq ^ (x2 * q ^ b + t) → x1 = x2 := by
      intro x1 hx1 x2 hx2 hxe
      have hconst0 : ζp ^ (i * p ^ a + s) ≠ 0 := pow_ne_zero _ hζp0
      have ht0 : ζq ^ t ≠ 0 := pow_ne_zero _ hζq0
      have hpow : ζq ^ (x1 * q ^ b) = ζq ^ (x2 * q ^ b) := by
        have hcancel := mul_left_cancel₀ hconst0 hxe
        rw [pow_add, pow_add] at hcancel
        exact mul_right_cancel₀ ht0 hcancel
      have hpow' : (ζq ^ (q ^ b)) ^ x1 = (ζq ^ (q ^ b)) ^ x2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (q ^ b) x1, Nat.mul_comm (q ^ b) x2]
        exact hpow
      exact hωq.pow_inj (Finset.mem_range.mp hx1) (Finset.mem_range.mp hx2) hpow'
    have hfresh : z₀ ^ q ∉ R := by
      intro hmem
      obtain ⟨w, hwS, hwq, horbit⟩ := hRorbit (z₀ ^ q) hmem
      have hz₀0 : z₀ ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hζp0) (pow_ne_zero _ hζq0)
      have hw0 : w ≠ 0 := by
        intro h0
        rw [h0] at hwq
        exact pow_ne_zero q hz₀0 (by rw [← hwq, zero_pow hq.pos.ne'])
      have hg : (z₀ / w) ^ q = 1 := by
        rw [div_pow, hwq, div_self (pow_ne_zero q hz₀0)]
      have hz₀S : z₀ ∈ S₀ := by
        have := horbit (z₀ / w) hg
        rwa [div_mul_cancel₀ z₀ hw0] at this
      exact (Finset.disjoint_left.mp hdis hz₀S) hz₀P
    refine ⟨insert (z₀ ^ q) R, ?_, ?_⟩
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hrR
      · refine ⟨z₀, Finset.mem_union_right _ hz₀P, rfl, ?_⟩
        intro g hg
        haveI : NeZero q := ⟨hq.pos.ne'⟩
        obtain ⟨k, hk, hkg⟩ := hωq.eq_pow_of_pow_eq_one hg
        refine Finset.mem_union_right _ ?_
        rw [hPdef]
        refine Finset.mem_image.mpr ⟨k % q, Finset.mem_range.mpr (Nat.mod_lt _ hq.pos), ?_⟩
        symm
        rw [← hkg, hz₀]
        have hsplit : k = q * (k / q) + k % q := (Nat.div_add_mod _ q).symm
        have hdecomp : q ^ b * k + t = q ^ (b + 1) * (k / q) + ((k % q) * q ^ b + t) := by
          calc q ^ b * k + t = q ^ b * (q * (k / q) + k % q) + t := by rw [← hsplit]
          _ = (q ^ b * q) * (k / q) + ((k % q) * q ^ b + t) := by ring
          _ = q ^ (b + 1) * (k / q) + ((k % q) * q ^ b + t) := by rw [← pow_succ]
        have hqeq : ζq ^ (q ^ b * k) * ζq ^ t = ζq ^ ((k % q) * q ^ b + t) := by
          rw [← pow_add, hdecomp, pow_add, pow_mul, hζq.pow_eq_one, one_pow, one_mul]
        calc (ζq ^ (q ^ b)) ^ k * (ζp ^ (i * p ^ a + s) * ζq ^ t)
            = ζp ^ (i * p ^ a + s) * (ζq ^ (q ^ b * k) * ζq ^ t) := by
              rw [← pow_mul]
              ring
          _ = ζp ^ (i * p ^ a + s) * ζq ^ ((k % q) * q ^ b + t) := by rw [hqeq]
      · obtain ⟨w, hw, hwq, horbit⟩ := hRorbit r hrR
        exact ⟨w, Finset.mem_union_left _ hw, hwq,
          fun g hg => Finset.mem_union_left _ (horbit g hg)⟩
    · intro e hpe
      have hcommon : ∀ y ∈ P, y ^ (q * e) = (z₀ ^ q) ^ e := by
        intro y hy
        obtain ⟨j'', _, rfl⟩ := Finset.mem_image.mp (hPdef ▸ hy)
        have hone : ((ζq ^ (j'' * q ^ b)) : F) ^ (q * e) = 1 := by
          rw [← pow_mul, show j'' * q ^ b * (q * e) = q ^ (b + 1) * (j'' * e) from by
            ring, pow_mul, hζq.pow_eq_one, one_pow]
        calc (ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t)) ^ (q * e)
            = (ζp ^ (i * p ^ a + s)) ^ (q * e)
              * ((ζq ^ (j'' * q ^ b)) ^ (q * e) * (ζq ^ t) ^ (q * e)) := by
              rw [pow_add (a := ζq)]
              ring
          _ = (ζp ^ (i * p ^ a + s)) ^ (q * e) * (ζq ^ t) ^ (q * e) := by
              rw [hone, one_mul]
          _ = (z₀ ^ q) ^ e := by rw [hz₀]; ring
      have hPsum : ∑ y ∈ P, y ^ (q * e) = (q : F) * (z₀ ^ q) ^ e := by
        rw [Finset.sum_congr rfl hcommon, Finset.sum_const]
        have hPcard : P.card = q := by
          rw [hPdef, Finset.card_image_of_injOn (fun x1 hx1 x2 hx2 h =>
            hinj x1 (Finset.mem_coe.mp hx1) x2 (Finset.mem_coe.mp hx2) h),
            Finset.card_range]
        rw [hPcard, nsmul_eq_mul]
      rw [Finset.sum_union hdis, hRsum e hpe, hPsum, Finset.sum_insert hfresh, mul_add]
      ring

end SpectralTransfer

/-! ## The iterated spectral transfer: the full descent chain in one theorem

Stacking O77 (decompose) and O80 (transfer) `m` times: given the `q`-power window
`Σ_S y^{q^c} = 0` for `1 ≤ c ≤ b`, the `m`-th spectrum `R_m` exists at level
`μ_{p^(a+1)·q^(b+1−m)}` — every element a `q^m`-th power of an element of `S` — and
carries the entire window with factor `q^m`:
`(q:F)^m · Σ_{r∈R_m} r^e = Σ_{y∈S} y^{q^m·e}` for every `p ∤ e`. At `m = b+1` the chain
bottoms out in the prime-power level `μ_{p^(a+1)}`, where the Lam–Leung machinery
applies. This is the windowed two-prime law's descent half, fully assembled. -/

section IteratedDescent

variable [DecidableEq F] [CharZero F]

/-- **The iterated spectral transfer**: the descent chain to depth `m`. -/
theorem iterated_spectral_transfer {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1)
    (hsum : ∑ z ∈ S, z = 0)
    (hwin : ∀ c, 1 ≤ c → c ≤ b → ∑ z ∈ S, z ^ (q ^ c) = 0) :
    ∀ m, m ≤ b + 1 →
      ∃ R : Finset F,
        (∀ r ∈ R, ∃ w ∈ S, w ^ (q ^ m) = r) ∧
        (∀ r ∈ R, r ^ (p ^ (a + 1) * q ^ (b + 1 - m)) = 1) ∧
        (∀ e : ℕ, ¬ p ∣ e →
          ((q : F)) ^ m * ∑ r ∈ R, r ^ e = ∑ y ∈ S, y ^ (q ^ m * e)) := by
  classical
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨S, fun r hr => ⟨r, hr, by rw [pow_zero, pow_one]⟩, ?_, ?_⟩
    · intro r hr
      rw [Nat.sub_zero]
      exact hS r hr
    · intro e _
      rw [pow_zero, one_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [pow_zero, one_mul]
  | succ m IH =>
    intro hm1
    have hm : m ≤ b := by omega
    obtain ⟨R, hRpow, hRtor, hRtransfer⟩ := IH (by omega)
    -- R vanishes: e = 1 of the carried transfer + the window at c = m (or hsum at m = 0)
    have hRsum : ∑ r ∈ R, r = 0 := by
      have h1 := hRtransfer 1 (by
        intro hdvd
        exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd))
      rw [mul_one] at h1
      have hwm : ∑ y ∈ S, y ^ (q ^ m) = 0 := by
        rcases Nat.eq_zero_or_pos m with rfl | hmpos
        · rw [pow_zero]
          simpa using hsum
        · exact hwin m hmpos hm
      have hq0 : ((q : F)) ^ m ≠ 0 := pow_ne_zero _ (by
        exact_mod_cast hq.pos.ne')
      have := h1.trans hwm
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hq0
      · simpa using h
    -- the level-(a, b−m) primitive root and torsion for R
    have hlevel : b + 1 - m = (b - m) + 1 := by omega
    have hζq' : IsPrimitiveRoot (ζq ^ (q ^ m)) (q ^ ((b - m) + 1)) := by
      have : IsPrimitiveRoot (ζq ^ (q ^ m)) (q ^ (b + 1 - m)) := by
        refine hζq.pow (pow_pos hq.pos _) ?_
        rw [← pow_add]
        congr 1
        omega
      rwa [hlevel] at this
    have hRtor' : ∀ r ∈ R, r ^ (p ^ (a + 1) * q ^ ((b - m) + 1)) = 1 := by
      intro r hr
      have := hRtor r hr
      rwa [hlevel] at this
    -- decompose R and apply the spectral transfer one level down
    have hPU := two_prime_packet_decomposition (a := a) (b := b - m) hp hq hpq
      hζp hζq' hRtor' hRsum
    obtain ⟨R', hR'orbit, hR'transfer⟩ :=
      packetUnion_spectral_transfer (a := a) (b := b - m) hp hq hpq hζp hζq' hPU
    refine ⟨R', ?_, ?_, ?_⟩
    · -- q^(m+1)-th powers of S elements
      intro r' hr'
      obtain ⟨w, hwR, hwq, _⟩ := hR'orbit r' hr'
      obtain ⟨w₀, hw₀S, hw₀pow⟩ := hRpow w hwR
      refine ⟨w₀, hw₀S, ?_⟩
      rw [← hwq, ← hw₀pow, ← pow_mul, pow_succ]
    · -- torsion one level further down
      intro r' hr'
      obtain ⟨w, hwR, hwq, _⟩ := hR'orbit r' hr'
      have hwtor := hRtor' w hwR
      have hbm : b + 1 - (m + 1) = b - m := by omega
      rw [hbm, ← hwq, ← pow_mul]
      calc w ^ (q * (p ^ (a + 1) * q ^ (b - m)))
          = (w ^ (p ^ (a + 1) * q ^ ((b - m) + 1))) := by
            congr 1
            rw [pow_succ]
            ring
        _ = 1 := hwtor
    · -- the carried transfer composes
      intro e hpe
      have hqe : ¬ p ∣ q * e := by
        intro hdvd
        rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).mp h) hpq
        · exact hpe h
      have hstep := hR'transfer e hpe
      have hcarry := hRtransfer (q * e) hqe
      calc ((q : F)) ^ (m + 1) * ∑ r ∈ R', r ^ e
          = ((q : F)) ^ m * ((q : F) * ∑ r ∈ R', r ^ e) := by ring
        _ = ((q : F)) ^ m * ∑ r ∈ R, r ^ (q * e) := by rw [← hstep]
        _ = ∑ y ∈ S, y ^ (q ^ m * (q * e)) := hcarry
        _ = ∑ y ∈ S, y ^ (q ^ (m + 1) * e) := by
            refine Finset.sum_congr rfl fun y _ => ?_
            congr 1
            rw [pow_succ]
            ring

end IteratedDescent

/-! ## The symmetric p-side chain and the chain endpoint

The `p`-side descent is the same theorem with the prime roles swapped (the
decomposition object is symmetric). And at the bottom of the `q`-side chain
(`m = b + 1`) the spectrum lives in the pure prime-power level `μ_{p^(a+1)}`, where the
membership-slice machinery closes it under `μ_p` — the chain's endpoint structure. -/

section ChainEndpoint

variable [DecidableEq F] [CharZero F]

/-- **The symmetric `p`-side iterated transfer**: swap the prime roles. -/
theorem iterated_spectral_transfer_p {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1)
    (hsum : ∑ z ∈ S, z = 0)
    (hwin : ∀ c, 1 ≤ c → c ≤ a → ∑ z ∈ S, z ^ (p ^ c) = 0) :
    ∀ m, m ≤ a + 1 →
      ∃ R : Finset F,
        (∀ r ∈ R, ∃ w ∈ S, w ^ (p ^ m) = r) ∧
        (∀ r ∈ R, r ^ (q ^ (b + 1) * p ^ (a + 1 - m)) = 1) ∧
        (∀ e : ℕ, ¬ q ∣ e →
          ((p : F)) ^ m * ∑ r ∈ R, r ^ e = ∑ y ∈ S, y ^ (p ^ m * e)) :=
  iterated_spectral_transfer hq hp (Ne.symm hpq) hζq hζp
    (fun z hz => by rw [mul_comm]; exact hS z hz) hsum hwin

/-- **The chain endpoint**: with the full `q`-power window (through `q^(b+1)`), the
deepest spectrum is a vanishing subset of the prime-power level `μ_{p^(a+1)}`, closed
under every `p`-th root of unity. -/
theorem deep_spectrum_mu_p_closed {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1)
    (hsum : ∑ z ∈ S, z = 0)
    (hwin : ∀ c, 1 ≤ c → c ≤ b + 1 → ∑ z ∈ S, z ^ (q ^ c) = 0) :
    ∃ R : Finset F,
      (∀ r ∈ R, ∃ w ∈ S, w ^ (q ^ (b + 1)) = r) ∧
      (∀ r ∈ R, r ^ (p ^ (a + 1)) = 1) ∧
      (∑ r ∈ R, r = 0) ∧
      (∀ x ∈ R, ∀ g : F, g ^ p = 1 → g * x ∈ R) := by
  classical
  obtain ⟨R, hRpow, hRtor, hRtransfer⟩ :=
    iterated_spectral_transfer hp hq hpq hζp hζq hS hsum
      (fun c hc1 hcb => hwin c hc1 (by omega)) (b + 1) le_rfl
  have hRtor' : ∀ r ∈ R, r ^ (p ^ (a + 1)) = 1 := by
    intro r hr
    have := hRtor r hr
    rwa [Nat.sub_self, pow_zero, mul_one] at this
  have hRsum : ∑ r ∈ R, r = 0 := by
    have h1 := hRtransfer 1 (fun hdvd => hp.one_lt.ne' (Nat.dvd_one.mp hdvd))
    rw [mul_one] at h1
    have hwm := hwin (b + 1) (by omega) le_rfl
    have hq0 : ((q : F)) ^ (b + 1) ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast hq.pos.ne')
    have := h1.trans hwm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hq0
    · simpa using h
  refine ⟨R, hRpow, hRtor', hRsum, ?_⟩
  -- μ_p-closure from the membership slices at the prime-power level
  have hslices := mu_p_membership_slices (m := a) hp hζp hRtor' hRsum
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hωp : IsPrimitiveRoot (ζp ^ (p ^ a)) p :=
    hζp.pow (pow_pos hp.pos _) (by rw [pow_succ])
  intro x hx g hg
  obtain ⟨k, hk, hkg⟩ := hωp.eq_pow_of_pow_eq_one hg
  -- box coordinates of x at the prime-power level
  obtain ⟨u, hu, hux⟩ := hζp.eq_pow_of_pow_eq_one (hRtor' x hx)
  obtain ⟨i, s, rfl, hs⟩ : ∃ i' s', u = i' * p ^ a + s' ∧ s' < p ^ a :=
    ⟨u / p ^ a, u % p ^ a, (Nat.div_add_mod' u (p ^ a)).symm,
      Nat.mod_lt _ (pow_pos hp.pos a)⟩
  have hi : i < p := by
    by_contra hge
    push Not at hge
    have h1 : p * p ^ a ≤ i * p ^ a := Nat.mul_le_mul_right _ hge
    have h2 : i * p ^ a + s < p ^ (a + 1) := hu
    rw [pow_succ'] at h2
    omega
  set i2 := (k + i) % p with hi2
  have hi2p : i2 < p := Nat.mod_lt _ hp.pos
  have hgx : g * x = ζp ^ (i2 * p ^ a + s) := by
    rw [← hkg, ← hux, ← pow_mul, ← pow_add]
    have hsplit : k + i = p * ((k + i) / p) + (k + i) % p := (Nat.div_add_mod _ p).symm
    have hdecomp : p ^ a * k + (i * p ^ a + s)
        = p ^ (a + 1) * ((k + i) / p) + (i2 * p ^ a + s) := by
      calc p ^ a * k + (i * p ^ a + s) = (k + i) * p ^ a + s := by ring
      _ = (p * ((k + i) / p) + (k + i) % p) * p ^ a + s := by rw [← hsplit]
      _ = (p * p ^ a) * ((k + i) / p) + (((k + i) % p) * p ^ a + s) := by ring
      _ = p ^ (a + 1) * ((k + i) / p) + (i2 * p ^ a + s) := by
          rw [← pow_succ', hi2]
    rw [hdecomp, pow_add, pow_mul, hζp.pow_eq_one, one_pow, one_mul]
  rw [hgx]
  exact (hslices s hs i2 hi2p i hi).mpr (by rwa [hux])

end ChainEndpoint

/-! ## The upward rung: coset structure lifts through the q-th power map

The reconstruction move of the windowed law: if every point of the `μ_A`-orbit of `x^q`
(one level down) is covered by a full `μ_q`-orbit inside `S` mapping onto it, then `x`
itself is `μ_{q·A}`-closed in `S` — the coset order MULTIPLIES up the chain. The proof
is three lines of arithmetic: for `h^{qA} = 1`, the point `(h·x)^q = h^q·x^q` lies over
the `μ_A`-orbit point `h^q·x^q` (since `(h^q)^A = 1`), the lift gives `w ∈ S` with the
same `q`-th power up to nothing — `(h·x/w)^q = 1` — and the lifted `μ_q`-orbit absorbs
the discrepancy. Iterating this rung up the O81 chain against the O82 endpoint is the
assembly of the full windowed law. -/

section UpwardRung

/-- **The coset lift**: spectrum-level `μ_A`-orbit coverage at `x^q` gives
`μ_{q·A}`-closure at `x`. Characteristic-free and root-free: pure arithmetic of the
power map. -/
theorem coset_lift {q A : ℕ} (hq : 0 < q) (hA : 0 < A) {S : Finset F} {x : F}
    (hx0 : x ≠ 0)
    (hlift : ∀ g : F, g ^ A = 1 →
      ∃ w ∈ S, w ^ q = g * x ^ q ∧ (∀ g' : F, g' ^ q = 1 → g' * w ∈ S)) :
    ∀ h : F, h ^ (q * A) = 1 → h * x ∈ S := by
  intro h hh
  have hgA : (h ^ q) ^ A = 1 := by
    rw [← pow_mul]
    exact hh
  obtain ⟨w, hwS, hwq, horbit⟩ := hlift (h ^ q) hgA
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, zero_pow hq.ne'] at hwq
    have hx0q : x ^ q ≠ 0 := pow_ne_zero _ hx0
    have hh0 : h ≠ 0 := by
      intro hh0
      rw [hh0, zero_pow (by positivity : q * A ≠ 0)] at hh
      exact zero_ne_one hh
    exact (mul_ne_zero (pow_ne_zero _ hh0) hx0q) hwq.symm
  have hg' : ((h * x) / w) ^ q = 1 := by
    rw [div_pow, mul_pow, ← hwq, div_self (pow_ne_zero _ hw0)]
  have := horbit ((h * x) / w) hg'
  rwa [div_mul_cancel₀ (h * x) hw0] at this

/-- The first iteration: spectrum `μ_q`-orbit coverage gives `μ_{q²}`-closure — the
window-kills-`μ_q`, `μ_{q²}`-replaces-it reassembly that the verified mixed-radix law
(O70) describes at `t ≥ q`. -/
theorem coset_lift_sq {q : ℕ} (hq : 0 < q) {S : Finset F} {x : F} (hx0 : x ≠ 0)
    (hlift : ∀ g : F, g ^ q = 1 →
      ∃ w ∈ S, w ^ q = g * x ^ q ∧ (∀ g' : F, g' ^ q = 1 → g' * w ∈ S)) :
    ∀ h : F, h ^ (q ^ 2) = 1 → h * x ∈ S := by
  intro h hh
  refine coset_lift hq hq hx0 hlift h ?_
  rwa [← pow_two]

end UpwardRung

/-! ## The dichotomy–spectrum export and the first reassembly trichotomy

The wiring of descent + cover + rung into the first full windowed-law statement: the
export lemma strengthens the spectral construction with a membership dichotomy — every
element of `S` is `μ_p`-closed in `S` (it sits in a `μ_p`-packet) or its `q`-th power
lies in the spectrum. The trichotomy theorem then assembles: with window `{1, q}`, the
spectrum vanishes, the COVER (O76) applies to it one level down, and the upward rung
(O83) converts spectrum-level `μ_p`/`μ_q`-coverage of `x^q` into `μ_{pq}`/`μ_{q²}`
closure at `x` — the `d`-coset reassembly (`d ∈ {p, q², pq}`: the divisors exceeding
`q`) that the exhaustively-verified O70 law displays at `t = q`. -/

section DichotomySpectrum

variable [DecidableEq F]

/-- **The dichotomy–spectrum export**: every element is `μ_p`-closed in `S` or maps
into the spectrum; the spectrum keeps the orbit property and the `e = 1` transfer. -/
theorem packetUnion_dichotomy_spectrum {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hPU : PacketUnion p q a b ζp ζq S) :
    ∃ R : Finset F,
      (∀ r ∈ R, ∃ w ∈ S, w ^ q = r ∧ ∀ g : F, g ^ q = 1 → g * w ∈ S) ∧
      (∀ x ∈ S, (∀ g : F, g ^ p = 1 → g * x ∈ S) ∨ x ^ q ∈ R) ∧
      (∑ y ∈ S, y ^ q = (q : F) * ∑ r ∈ R, r) := by
  classical
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hζp0 : ζp ≠ 0 := prim_ne_zero hζp (pow_pos hp.pos _)
  have hζq0 : ζq ≠ 0 := prim_ne_zero hζq (pow_pos hq.pos _)
  have hωp : IsPrimitiveRoot (ζp ^ (p ^ a)) p :=
    hζp.pow (pow_pos hp.pos _) (by rw [pow_succ])
  have hωq : IsPrimitiveRoot (ζq ^ (q ^ b)) q :=
    hζq.pow (pow_pos hq.pos _) (by rw [pow_succ])
  have hωpq : IsPrimitiveRoot ((ζp ^ (p ^ a)) ^ q) p :=
    hωp.pow_of_coprime q ((Nat.coprime_primes hq hp).mpr (Ne.symm hpq))
  induction hPU with
  | empty =>
    exact ⟨∅, fun r hr => absurd hr (Finset.notMem_empty r),
      fun x hx => absurd hx (Finset.notMem_empty x), by simp⟩
  | @addP S₀ s j t hsub hnot IH =>
    obtain ⟨R, hRorbit, hRdich, hRsum⟩ := IH
    set P : Finset F := (Finset.range p).image
      (fun i'' => ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t)) with hPdef
    have hdis : Disjoint S₀ P := by
      rw [Finset.disjoint_left]
      intro y hyS hyP
      obtain ⟨i'', hi'', rfl⟩ := Finset.mem_image.mp (hPdef ▸ hyP)
      exact hnot i'' (Finset.mem_range.mp hi'') hyS
    have hPclosed : ∀ y ∈ P, ∀ g : F, g ^ p = 1 → g * y ∈ P := by
      intro y hy g hg
      obtain ⟨i'', hi'', rfl⟩ := Finset.mem_image.mp (hPdef ▸ hy)
      obtain ⟨k, hk, hkg⟩ := hωp.eq_pow_of_pow_eq_one hg
      refine hPdef ▸ Finset.mem_image.mpr
        ⟨(k + i'') % p, Finset.mem_range.mpr (Nat.mod_lt _ hp.pos), ?_⟩
      have hgz : g * ζp ^ (i'' * p ^ a + s)
          = ζp ^ (((k + i'') % p) * p ^ a + s) := by
        rw [← hkg, ← pow_mul, ← pow_add]
        have hsplit : k + i'' = p * ((k + i'') / p) + (k + i'') % p :=
          (Nat.div_add_mod _ p).symm
        have hdecomp : p ^ a * k + (i'' * p ^ a + s)
            = p ^ (a + 1) * ((k + i'') / p) + (((k + i'') % p) * p ^ a + s) := by
          calc p ^ a * k + (i'' * p ^ a + s) = (k + i'') * p ^ a + s := by ring
          _ = (p * ((k + i'') / p) + (k + i'') % p) * p ^ a + s := by rw [← hsplit]
          _ = (p * p ^ a) * ((k + i'') / p) + (((k + i'') % p) * p ^ a + s) := by ring
          _ = p ^ (a + 1) * ((k + i'') / p) + (((k + i'') % p) * p ^ a + s) := by
              rw [← pow_succ']
        rw [hdecomp, pow_add, pow_mul, hζp.pow_eq_one, one_pow, one_mul]
      rw [← mul_assoc]
      exact congrArg (· * ζq ^ (j * q ^ b + t)) hgz.symm
    have hinj : ∀ x1 ∈ Finset.range p, ∀ x2 ∈ Finset.range p,
        ζp ^ (x1 * p ^ a + s) * ζq ^ (j * q ^ b + t)
          = ζp ^ (x2 * p ^ a + s) * ζq ^ (j * q ^ b + t) → x1 = x2 := by
      intro x1 hx1 x2 hx2 hxe
      have hconst0 : ζq ^ (j * q ^ b + t) ≠ 0 := pow_ne_zero _ hζq0
      have hs0 : ζp ^ s ≠ 0 := pow_ne_zero _ hζp0
      have hpow : ζp ^ (x1 * p ^ a) = ζp ^ (x2 * p ^ a) := by
        have hcancel := mul_right_cancel₀ hconst0 hxe
        rw [pow_add, pow_add] at hcancel
        exact mul_right_cancel₀ hs0 hcancel
      have hpow' : (ζp ^ (p ^ a)) ^ x1 = (ζp ^ (p ^ a)) ^ x2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (p ^ a) x1, Nat.mul_comm (p ^ a) x2]
        exact hpow
      exact hωp.pow_inj (Finset.mem_range.mp hx1) (Finset.mem_range.mp hx2) hpow'
    have hPsum : ∑ y ∈ P, y ^ q = 0 := by
      rw [hPdef, Finset.sum_image hinj]
      have hterm : ∀ i'' ∈ Finset.range p,
          (ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t)) ^ q
            = ((ζp ^ (p ^ a)) ^ q) ^ i''
              * ((ζp ^ s) ^ q * (ζq ^ (j * q ^ b + t)) ^ q) := by
        intro i'' _
        ring
      rw [Finset.sum_congr rfl hterm]
      exact prime_packet_sum_zero hp hωpq _
    refine ⟨R, ?_, ?_, ?_⟩
    · intro r hr
      obtain ⟨w, hw, hwq, horbit⟩ := hRorbit r hr
      exact ⟨w, Finset.mem_union_left _ hw, hwq,
        fun g hg => Finset.mem_union_left _ (horbit g hg)⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hxS | hxP
      · rcases hRdich x hxS with hcl | hsp
        · exact Or.inl fun g hg => Finset.mem_union_left _ (hcl g hg)
        · exact Or.inr hsp
      · exact Or.inl fun g hg => Finset.mem_union_right _ (hPclosed x hxP g hg)
    · rw [Finset.sum_union hdis, hRsum, hPsum, add_zero]
  | @addQ S₀ s i t hsub hnot IH =>
    obtain ⟨R, hRorbit, hRdich, hRsum⟩ := IH
    set P : Finset F := (Finset.range q).image
      (fun j'' => ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t)) with hPdef
    set z₀ : F := ζp ^ (i * p ^ a + s) * ζq ^ t with hz₀
    have hz₀P : z₀ ∈ P := by
      rw [hPdef]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hq.pos, by
        rw [hz₀, Nat.zero_mul, Nat.zero_add]⟩
    have hdis : Disjoint S₀ P := by
      rw [Finset.disjoint_left]
      intro y hyS hyP
      obtain ⟨j'', hj'', rfl⟩ := Finset.mem_image.mp (hPdef ▸ hyP)
      exact hnot j'' (Finset.mem_range.mp hj'') hyS
    have hinj : ∀ x1 ∈ Finset.range q, ∀ x2 ∈ Finset.range q,
        ζp ^ (i * p ^ a + s) * ζq ^ (x1 * q ^ b + t)
          = ζp ^ (i * p ^ a + s) * ζq ^ (x2 * q ^ b + t) → x1 = x2 := by
      intro x1 hx1 x2 hx2 hxe
      have hconst0 : ζp ^ (i * p ^ a + s) ≠ 0 := pow_ne_zero _ hζp0
      have ht0 : ζq ^ t ≠ 0 := pow_ne_zero _ hζq0
      have hpow : ζq ^ (x1 * q ^ b) = ζq ^ (x2 * q ^ b) := by
        have hcancel := mul_left_cancel₀ hconst0 hxe
        rw [pow_add, pow_add] at hcancel
        exact mul_right_cancel₀ ht0 hcancel
      have hpow' : (ζq ^ (q ^ b)) ^ x1 = (ζq ^ (q ^ b)) ^ x2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (q ^ b) x1, Nat.mul_comm (q ^ b) x2]
        exact hpow
      exact hωq.pow_inj (Finset.mem_range.mp hx1) (Finset.mem_range.mp hx2) hpow'
    -- the q-packet is the full μ_q-orbit of z₀, and all members share the q-th power
    have hPorbit : ∀ g : F, g ^ q = 1 → g * z₀ ∈ P := by
      intro g hg
      obtain ⟨k, hk, hkg⟩ := hωq.eq_pow_of_pow_eq_one hg
      refine hPdef ▸ Finset.mem_image.mpr
        ⟨k % q, Finset.mem_range.mpr (Nat.mod_lt _ hq.pos), ?_⟩
      symm
      rw [← hkg, hz₀]
      have hsplit : k = q * (k / q) + k % q := (Nat.div_add_mod _ q).symm
      have hdecomp : q ^ b * k + t = q ^ (b + 1) * (k / q) + ((k % q) * q ^ b + t) := by
        calc q ^ b * k + t = q ^ b * (q * (k / q) + k % q) + t := by rw [← hsplit]
        _ = (q ^ b * q) * (k / q) + ((k % q) * q ^ b + t) := by ring
        _ = q ^ (b + 1) * (k / q) + ((k % q) * q ^ b + t) := by rw [← pow_succ]
      have hqeq : ζq ^ (q ^ b * k) * ζq ^ t = ζq ^ ((k % q) * q ^ b + t) := by
        rw [← pow_add, hdecomp, pow_add, pow_mul, hζq.pow_eq_one, one_pow, one_mul]
      calc (ζq ^ (q ^ b)) ^ k * (ζp ^ (i * p ^ a + s) * ζq ^ t)
          = ζp ^ (i * p ^ a + s) * (ζq ^ (q ^ b * k) * ζq ^ t) := by
            rw [← pow_mul]
            ring
        _ = ζp ^ (i * p ^ a + s) * ζq ^ ((k % q) * q ^ b + t) := by rw [hqeq]
    have hcommon : ∀ y ∈ P, y ^ q = z₀ ^ q := by
      intro y hy
      obtain ⟨j'', _, rfl⟩ := Finset.mem_image.mp (hPdef ▸ hy)
      have hone : ((ζq ^ (j'' * q ^ b)) : F) ^ q = 1 := by
        rw [← pow_mul, show j'' * q ^ b * q = q ^ (b + 1) * j'' from by ring,
          pow_mul, hζq.pow_eq_one, one_pow]
      calc (ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t)) ^ q
          = (ζp ^ (i * p ^ a + s)) ^ q
            * ((ζq ^ (j'' * q ^ b)) ^ q * (ζq ^ t) ^ q) := by
            rw [pow_add (a := ζq)]
            ring
        _ = (ζp ^ (i * p ^ a + s)) ^ q * (ζq ^ t) ^ q := by rw [hone, one_mul]
        _ = z₀ ^ q := by rw [hz₀]; ring
    have hfresh : z₀ ^ q ∉ R := by
      intro hmem
      obtain ⟨w, hwS, hwq, horbit⟩ := hRorbit (z₀ ^ q) hmem
      have hz₀0 : z₀ ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hζp0) (pow_ne_zero _ hζq0)
      have hw0 : w ≠ 0 := by
        intro h0
        rw [h0] at hwq
        exact pow_ne_zero q hz₀0 (by rw [← hwq, zero_pow hq.pos.ne'])
      have hg : (z₀ / w) ^ q = 1 := by
        rw [div_pow, hwq, div_self (pow_ne_zero q hz₀0)]
      have hz₀S : z₀ ∈ S₀ := by
        have := horbit (z₀ / w) hg
        rwa [div_mul_cancel₀ z₀ hw0] at this
      exact (Finset.disjoint_left.mp hdis hz₀S) hz₀P
    have hPsum : ∑ y ∈ P, y ^ q = (q : F) * z₀ ^ q := by
      rw [Finset.sum_congr rfl hcommon, Finset.sum_const]
      have hPcard : P.card = q := by
        rw [hPdef, Finset.card_image_of_injOn (fun x1 hx1 x2 hx2 h =>
          hinj x1 (Finset.mem_coe.mp hx1) x2 (Finset.mem_coe.mp hx2) h),
          Finset.card_range]
      rw [hPcard, nsmul_eq_mul]
    refine ⟨insert (z₀ ^ q) R, ?_, ?_, ?_⟩
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hrR
      · exact ⟨z₀, Finset.mem_union_right _ hz₀P, rfl,
          fun g hg => Finset.mem_union_right _ (hPorbit g hg)⟩
      · obtain ⟨w, hw, hwq, horbit⟩ := hRorbit r hrR
        exact ⟨w, Finset.mem_union_left _ hw, hwq,
          fun g hg => Finset.mem_union_left _ (horbit g hg)⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hxS | hxP
      · rcases hRdich x hxS with hcl | hsp
        · exact Or.inl fun g hg => Finset.mem_union_left _ (hcl g hg)
        · exact Or.inr (Finset.mem_insert_of_mem hsp)
      · refine Or.inr ?_
        rw [hcommon x hxP]
        exact Finset.mem_insert_self _ _
    · rw [Finset.sum_union hdis, hRsum, hPsum, Finset.sum_insert hfresh, mul_add]
      ring

end DichotomySpectrum

/-! ## THE FIRST REASSEMBLY: the window-{1,q} trichotomy

The wiring of decomposition (O77), the dichotomy–spectrum export, the cover (O76), and
the upward rung (O83): with window `{1, q}`, every element of a two-prime vanishing set
is `μ_p`-, `μ_{q²}`-, or `μ_{pq}`-covered inside `S` — the `d`-coset reassembly over the
divisors `d ∈ {p, q², pq}` exceeding `q`, exactly the shape of the exhaustively-verified
mixed-radix law at `t = q`: the window kills bare `μ_q`-packets, and their mass can
reappear only inside the two larger coset types, reconstructed here by lifting the
spectrum-level cover through the power map. -/

section Trichotomy

variable [DecidableEq F] [CharZero F]

/-- **The window-`{1,q}` trichotomy**: every element is `μ_p`-, `μ_{q²}`-, or
`μ_{pq}`-covered. -/
theorem two_prime_window_trichotomy {p q a b' : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b' + 2)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ (b' + 2)) = 1)
    (hsum : ∑ z ∈ S, z = 0) (hsumq : ∑ z ∈ S, z ^ q = 0) :
    ∀ x ∈ S,
      (∀ h : F, h ^ p = 1 → h * x ∈ S) ∨
      (∀ h : F, h ^ (q * q) = 1 → h * x ∈ S) ∨
      (∀ h : F, h ^ (q * p) = 1 → h * x ∈ S) := by
  classical
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hζqb : IsPrimitiveRoot ζq (q ^ ((b' + 1) + 1)) := hζq
  have hSb : ∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ ((b' + 1) + 1)) = 1 := hS
  have hPU := two_prime_packet_decomposition hp hq hpq hζp hζqb hSb hsum
  obtain ⟨R, hRorbit, hRdich, hRsum⟩ :=
    packetUnion_dichotomy_spectrum hp hq hpq hζp hζqb hPU
  have hRsum0 : ∑ r ∈ R, r = 0 := by
    have hq0 : ((q : F)) ≠ 0 := by exact_mod_cast hq.pos.ne'
    have := hRsum.symm.trans hsumq
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hq0
    · exact h
  have hRtor : ∀ r ∈ R, r ^ (p ^ (a + 1) * q ^ (b' + 1)) = 1 := by
    intro r hr
    obtain ⟨w, hwS, hwq, _⟩ := hRorbit r hr
    rw [← hwq, ← pow_mul]
    calc w ^ (q * (p ^ (a + 1) * q ^ (b' + 1)))
        = w ^ (p ^ (a + 1) * q ^ (b' + 2)) := by
          congr 1
          rw [pow_succ]
          ring
      _ = 1 := hS w hwS
  have hζq' : IsPrimitiveRoot (ζq ^ q) (q ^ (b' + 1)) := by
    refine hζq.pow (pow_pos hq.pos _) ?_
    rw [pow_succ']
  have hcover := two_prime_packet_cover (a := a) (b := b') hp hq hpq hζp hζq'
    hRtor hRsum0
  intro x hx
  rcases hRdich x hx with hP | hR1
  · exact Or.inl hP
  have hx0 : x ≠ 0 := by
    intro h0
    have := hS x hx
    rw [h0, zero_pow (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)).ne'] at this
    exact zero_ne_one this
  have hcop' : Nat.Coprime (p ^ (a + 1)) (q ^ (b' + 1)) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hpq)
  obtain ⟨u, hu, v, hv, huv⟩ := box_pair_surj hζp hζq' hcop'
    (pow_pos hp.pos _) (pow_pos hq.pos _) (hRtor _ hR1)
  obtain ⟨i, s, rfl, hs⟩ : ∃ i' s', u = i' * p ^ a + s' ∧ s' < p ^ a :=
    ⟨u / p ^ a, u % p ^ a, (Nat.div_add_mod' u (p ^ a)).symm,
      Nat.mod_lt _ (pow_pos hp.pos a)⟩
  obtain ⟨j, t, rfl, ht⟩ : ∃ j' t', v = j' * q ^ b' + t' ∧ t' < q ^ b' :=
    ⟨v / q ^ b', v % q ^ b', (Nat.div_add_mod' v (q ^ b')).symm,
      Nat.mod_lt _ (pow_pos hq.pos b')⟩
  have hi : i < p := by
    by_contra hge
    push Not at hge
    have h1 : p * p ^ a ≤ i * p ^ a := Nat.mul_le_mul_right _ hge
    have h2 : i * p ^ a + s < p ^ (a + 1) := hu
    rw [pow_succ'] at h2
    omega
  have hj : j < q := by
    by_contra hge
    push Not at hge
    have h1 : q * q ^ b' ≤ j * q ^ b' := Nat.mul_le_mul_right _ hge
    have h2 : j * q ^ b' + t < q ^ (b' + 1) := hv
    rw [pow_succ'] at h2
    omega
  have hxqmem : ζp ^ (i * p ^ a + s) * (ζq ^ q) ^ (j * q ^ b' + t) ∈ R := by
    rwa [huv]
  rcases hcover s hs i hi t ht j hj hxqmem with hProw | hQcol
  · -- μ_p-row of x^q ⊆ R ⟹ μ_{q·p}-closure of x
    refine Or.inr (Or.inr ?_)
    have hωp : IsPrimitiveRoot (ζp ^ (p ^ a)) p :=
      hζp.pow (pow_pos hp.pos _) (by rw [pow_succ])
    refine coset_lift hq.pos hp.pos hx0 ?_
    intro g hg
    obtain ⟨k, hk, hkg⟩ := hωp.eq_pow_of_pow_eq_one hg
    have hrow := hProw ((k + i) % p) (Nat.mod_lt _ hp.pos)
    have hgz : g * ζp ^ (i * p ^ a + s) = ζp ^ (((k + i) % p) * p ^ a + s) := by
      rw [← hkg, ← pow_mul, ← pow_add]
      have hsplit : k + i = p * ((k + i) / p) + (k + i) % p := (Nat.div_add_mod _ p).symm
      have hdecomp : p ^ a * k + (i * p ^ a + s)
          = p ^ (a + 1) * ((k + i) / p) + (((k + i) % p) * p ^ a + s) := by
        calc p ^ a * k + (i * p ^ a + s) = (k + i) * p ^ a + s := by ring
        _ = (p * ((k + i) / p) + (k + i) % p) * p ^ a + s := by rw [← hsplit]
        _ = (p * p ^ a) * ((k + i) / p) + (((k + i) % p) * p ^ a + s) := by ring
        _ = p ^ (a + 1) * ((k + i) / p) + (((k + i) % p) * p ^ a + s) := by
            rw [← pow_succ']
      rw [hdecomp, pow_add, pow_mul, hζp.pow_eq_one, one_pow, one_mul]
    have hgxq : g * x ^ q
        = ζp ^ (((k + i) % p) * p ^ a + s) * (ζq ^ q) ^ (j * q ^ b' + t) := by
      rw [← huv, ← mul_assoc, hgz]
    obtain ⟨w, hwS, hwq, horbit⟩ := hRorbit _ hrow
    exact ⟨w, hwS, by rw [hwq, hgxq], horbit⟩
  · -- μ_q-column of x^q ⊆ R ⟹ μ_{q·q}-closure of x
    refine Or.inr (Or.inl ?_)
    have hωq' : IsPrimitiveRoot ((ζq ^ q) ^ (q ^ b')) q :=
      hζq'.pow (pow_pos hq.pos _) (by rw [pow_succ])
    refine coset_lift hq.pos hq.pos hx0 ?_
    intro g hg
    obtain ⟨k, hk, hkg⟩ := hωq'.eq_pow_of_pow_eq_one hg
    have hcol := hQcol ((k + j) % q) (Nat.mod_lt _ hq.pos)
    have hgz : g * (ζq ^ q) ^ (j * q ^ b' + t)
        = (ζq ^ q) ^ (((k + j) % q) * q ^ b' + t) := by
      rw [← hkg, ← pow_mul, ← pow_add]
      have hsplit : k + j = q * ((k + j) / q) + (k + j) % q := (Nat.div_add_mod _ q).symm
      have hdecomp : q ^ b' * k + (j * q ^ b' + t)
          = q ^ (b' + 1) * ((k + j) / q) + (((k + j) % q) * q ^ b' + t) := by
        calc q ^ b' * k + (j * q ^ b' + t) = (k + j) * q ^ b' + t := by ring
        _ = (q * ((k + j) / q) + (k + j) % q) * q ^ b' + t := by rw [← hsplit]
        _ = (q * q ^ b') * ((k + j) / q) + (((k + j) % q) * q ^ b' + t) := by ring
        _ = q ^ (b' + 1) * ((k + j) / q) + (((k + j) % q) * q ^ b' + t) := by
            rw [← pow_succ']
      rw [hdecomp, pow_add, pow_mul, hζq'.pow_eq_one, one_pow, one_mul]
    have hgxq : g * x ^ q
        = ζp ^ (i * p ^ a + s) * (ζq ^ q) ^ (((k + j) % q) * q ^ b' + t) := by
      rw [← huv]
      calc g * (ζp ^ (i * p ^ a + s) * (ζq ^ q) ^ (j * q ^ b' + t))
          = ζp ^ (i * p ^ a + s) * (g * (ζq ^ q) ^ (j * q ^ b' + t)) := by ring
        _ = ζp ^ (i * p ^ a + s) * (ζq ^ q) ^ (((k + j) % q) * q ^ b' + t) := by
            rw [hgz]
    obtain ⟨w, hwS, hwq, horbit⟩ := hRorbit _ hcol
    exact ⟨w, hwS, by rw [hwq, hgxq], horbit⟩

end Trichotomy

/-! ## The full export: one spectrum with orbit + dichotomy + complete transfer

The merge of the dichotomy export and the spectral transfer: a SINGLE spectrum `R`
simultaneously carries the orbit property, the membership dichotomy, and the full
syndrome transfer at every exponent `p ∤ e` — the package the general-`t` reassembly
induction consumes. -/

section FullExport

variable [DecidableEq F]

/-- **The full spectrum export**: orbit property + membership dichotomy + complete
transfer, one `R`. -/
theorem packetUnion_full_export {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hPU : PacketUnion p q a b ζp ζq S) :
    ∃ R : Finset F,
      (∀ r ∈ R, ∃ w ∈ S, w ^ q = r ∧ ∀ g : F, g ^ q = 1 → g * w ∈ S) ∧
      (∀ x ∈ S, (∀ g : F, g ^ p = 1 → g * x ∈ S) ∨ x ^ q ∈ R) ∧
      (∀ e : ℕ, ¬ p ∣ e →
        ∑ y ∈ S, y ^ (q * e) = (q : F) * ∑ r ∈ R, r ^ e) := by
  classical
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hζp0 : ζp ≠ 0 := prim_ne_zero hζp (pow_pos hp.pos _)
  have hζq0 : ζq ≠ 0 := prim_ne_zero hζq (pow_pos hq.pos _)
  have hωp : IsPrimitiveRoot (ζp ^ (p ^ a)) p :=
    hζp.pow (pow_pos hp.pos _) (by rw [pow_succ])
  have hωq : IsPrimitiveRoot (ζq ^ (q ^ b)) q :=
    hζq.pow (pow_pos hq.pos _) (by rw [pow_succ])
  induction hPU with
  | empty =>
    exact ⟨∅, fun r hr => absurd hr (Finset.notMem_empty r),
      fun x hx => absurd hx (Finset.notMem_empty x), fun e _ => by simp⟩
  | @addP S₀ s j t hsub hnot IH =>
    obtain ⟨R, hRorbit, hRdich, hRsum⟩ := IH
    set P : Finset F := (Finset.range p).image
      (fun i'' => ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t)) with hPdef
    have hdis : Disjoint S₀ P := by
      rw [Finset.disjoint_left]
      intro y hyS hyP
      obtain ⟨i'', hi'', rfl⟩ := Finset.mem_image.mp (hPdef ▸ hyP)
      exact hnot i'' (Finset.mem_range.mp hi'') hyS
    have hPclosed : ∀ y ∈ P, ∀ g : F, g ^ p = 1 → g * y ∈ P := by
      intro y hy g hg
      obtain ⟨i'', hi'', rfl⟩ := Finset.mem_image.mp (hPdef ▸ hy)
      obtain ⟨k, hk, hkg⟩ := hωp.eq_pow_of_pow_eq_one hg
      refine hPdef ▸ Finset.mem_image.mpr
        ⟨(k + i'') % p, Finset.mem_range.mpr (Nat.mod_lt _ hp.pos), ?_⟩
      have hgz : g * ζp ^ (i'' * p ^ a + s)
          = ζp ^ (((k + i'') % p) * p ^ a + s) := by
        rw [← hkg, ← pow_mul, ← pow_add]
        have hsplit : k + i'' = p * ((k + i'') / p) + (k + i'') % p :=
          (Nat.div_add_mod _ p).symm
        have hdecomp : p ^ a * k + (i'' * p ^ a + s)
            = p ^ (a + 1) * ((k + i'') / p) + (((k + i'') % p) * p ^ a + s) := by
          calc p ^ a * k + (i'' * p ^ a + s) = (k + i'') * p ^ a + s := by ring
          _ = (p * ((k + i'') / p) + (k + i'') % p) * p ^ a + s := by rw [← hsplit]
          _ = (p * p ^ a) * ((k + i'') / p) + (((k + i'') % p) * p ^ a + s) := by ring
          _ = p ^ (a + 1) * ((k + i'') / p) + (((k + i'') % p) * p ^ a + s) := by
              rw [← pow_succ']
        rw [hdecomp, pow_add, pow_mul, hζp.pow_eq_one, one_pow, one_mul]
      rw [← mul_assoc]
      exact congrArg (· * ζq ^ (j * q ^ b + t)) hgz.symm
    have hinj : ∀ x1 ∈ Finset.range p, ∀ x2 ∈ Finset.range p,
        ζp ^ (x1 * p ^ a + s) * ζq ^ (j * q ^ b + t)
          = ζp ^ (x2 * p ^ a + s) * ζq ^ (j * q ^ b + t) → x1 = x2 := by
      intro x1 hx1 x2 hx2 hxe
      have hconst0 : ζq ^ (j * q ^ b + t) ≠ 0 := pow_ne_zero _ hζq0
      have hs0 : ζp ^ s ≠ 0 := pow_ne_zero _ hζp0
      have hpow : ζp ^ (x1 * p ^ a) = ζp ^ (x2 * p ^ a) := by
        have hcancel := mul_right_cancel₀ hconst0 hxe
        rw [pow_add, pow_add] at hcancel
        exact mul_right_cancel₀ hs0 hcancel
      have hpow' : (ζp ^ (p ^ a)) ^ x1 = (ζp ^ (p ^ a)) ^ x2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (p ^ a) x1, Nat.mul_comm (p ^ a) x2]
        exact hpow
      exact hωp.pow_inj (Finset.mem_range.mp hx1) (Finset.mem_range.mp hx2) hpow'
    refine ⟨R, ?_, ?_, ?_⟩
    · intro r hr
      obtain ⟨w, hw, hwq, horbit⟩ := hRorbit r hr
      exact ⟨w, Finset.mem_union_left _ hw, hwq,
        fun g hg => Finset.mem_union_left _ (horbit g hg)⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hxS | hxP
      · rcases hRdich x hxS with hcl | hsp
        · exact Or.inl fun g hg => Finset.mem_union_left _ (hcl g hg)
        · exact Or.inr hsp
      · exact Or.inl fun g hg => Finset.mem_union_right _ (hPclosed x hxP g hg)
    · intro e hpe
      have hωpe : IsPrimitiveRoot ((ζp ^ (p ^ a)) ^ (q * e)) p := by
        refine hωp.pow_of_coprime _ ?_
        have hqp : Nat.Coprime q p := (Nat.coprime_primes hq hp).mpr (Ne.symm hpq)
        have hep : Nat.Coprime e p := by
          rcases Nat.coprime_or_dvd_of_prime hp e with h | h
          · exact h.symm
          · exact absurd h hpe
        exact Nat.Coprime.mul_left hqp hep
      have hPsum : ∑ y ∈ P, y ^ (q * e) = 0 := by
        rw [hPdef, Finset.sum_image hinj]
        have hterm : ∀ i'' ∈ Finset.range p,
            (ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t)) ^ (q * e)
              = ((ζp ^ (p ^ a)) ^ (q * e)) ^ i''
                * ((ζp ^ s) ^ (q * e) * (ζq ^ (j * q ^ b + t)) ^ (q * e)) := by
          intro i'' _
          ring
        rw [Finset.sum_congr rfl hterm]
        exact prime_packet_sum_zero hp hωpe _
      rw [Finset.sum_union hdis, hRsum e hpe, hPsum, add_zero]
  | @addQ S₀ s i t hsub hnot IH =>
    obtain ⟨R, hRorbit, hRdich, hRsum⟩ := IH
    set P : Finset F := (Finset.range q).image
      (fun j'' => ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t)) with hPdef
    set z₀ : F := ζp ^ (i * p ^ a + s) * ζq ^ t with hz₀
    have hz₀P : z₀ ∈ P := by
      rw [hPdef]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hq.pos, by
        rw [hz₀, Nat.zero_mul, Nat.zero_add]⟩
    have hdis : Disjoint S₀ P := by
      rw [Finset.disjoint_left]
      intro y hyS hyP
      obtain ⟨j'', hj'', rfl⟩ := Finset.mem_image.mp (hPdef ▸ hyP)
      exact hnot j'' (Finset.mem_range.mp hj'') hyS
    have hinj : ∀ x1 ∈ Finset.range q, ∀ x2 ∈ Finset.range q,
        ζp ^ (i * p ^ a + s) * ζq ^ (x1 * q ^ b + t)
          = ζp ^ (i * p ^ a + s) * ζq ^ (x2 * q ^ b + t) → x1 = x2 := by
      intro x1 hx1 x2 hx2 hxe
      have hconst0 : ζp ^ (i * p ^ a + s) ≠ 0 := pow_ne_zero _ hζp0
      have ht0 : ζq ^ t ≠ 0 := pow_ne_zero _ hζq0
      have hpow : ζq ^ (x1 * q ^ b) = ζq ^ (x2 * q ^ b) := by
        have hcancel := mul_left_cancel₀ hconst0 hxe
        rw [pow_add, pow_add] at hcancel
        exact mul_right_cancel₀ ht0 hcancel
      have hpow' : (ζq ^ (q ^ b)) ^ x1 = (ζq ^ (q ^ b)) ^ x2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (q ^ b) x1, Nat.mul_comm (q ^ b) x2]
        exact hpow
      exact hωq.pow_inj (Finset.mem_range.mp hx1) (Finset.mem_range.mp hx2) hpow'
    -- the q-packet is the full μ_q-orbit of z₀, and all members share the q-th power
    have hPorbit : ∀ g : F, g ^ q = 1 → g * z₀ ∈ P := by
      intro g hg
      obtain ⟨k, hk, hkg⟩ := hωq.eq_pow_of_pow_eq_one hg
      refine hPdef ▸ Finset.mem_image.mpr
        ⟨k % q, Finset.mem_range.mpr (Nat.mod_lt _ hq.pos), ?_⟩
      symm
      rw [← hkg, hz₀]
      have hsplit : k = q * (k / q) + k % q := (Nat.div_add_mod _ q).symm
      have hdecomp : q ^ b * k + t = q ^ (b + 1) * (k / q) + ((k % q) * q ^ b + t) := by
        calc q ^ b * k + t = q ^ b * (q * (k / q) + k % q) + t := by rw [← hsplit]
        _ = (q ^ b * q) * (k / q) + ((k % q) * q ^ b + t) := by ring
        _ = q ^ (b + 1) * (k / q) + ((k % q) * q ^ b + t) := by rw [← pow_succ]
      have hqeq : ζq ^ (q ^ b * k) * ζq ^ t = ζq ^ ((k % q) * q ^ b + t) := by
        rw [← pow_add, hdecomp, pow_add, pow_mul, hζq.pow_eq_one, one_pow, one_mul]
      calc (ζq ^ (q ^ b)) ^ k * (ζp ^ (i * p ^ a + s) * ζq ^ t)
          = ζp ^ (i * p ^ a + s) * (ζq ^ (q ^ b * k) * ζq ^ t) := by
            rw [← pow_mul]
            ring
        _ = ζp ^ (i * p ^ a + s) * ζq ^ ((k % q) * q ^ b + t) := by rw [hqeq]
    have hcommon : ∀ e' : ℕ, ∀ y ∈ P, y ^ (q * e') = (z₀ ^ q) ^ e' := by
      intro e' y hy
      obtain ⟨j'', _, rfl⟩ := Finset.mem_image.mp (hPdef ▸ hy)
      have hone : ((ζq ^ (j'' * q ^ b)) : F) ^ (q * e') = 1 := by
        rw [← pow_mul, show j'' * q ^ b * (q * e') = q ^ (b + 1) * (j'' * e') from by
          ring, pow_mul, hζq.pow_eq_one, one_pow]
      calc (ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t)) ^ (q * e')
          = (ζp ^ (i * p ^ a + s)) ^ (q * e')
            * ((ζq ^ (j'' * q ^ b)) ^ (q * e') * (ζq ^ t) ^ (q * e')) := by
            rw [pow_add (a := ζq)]
            ring
        _ = (ζp ^ (i * p ^ a + s)) ^ (q * e') * (ζq ^ t) ^ (q * e') := by
            rw [hone, one_mul]
        _ = (z₀ ^ q) ^ e' := by rw [hz₀]; ring
    have hcommon1 : ∀ y ∈ P, y ^ q = z₀ ^ q := by
      intro y hy
      have := hcommon 1 y hy
      rwa [mul_one, pow_one] at this
    have hfresh : z₀ ^ q ∉ R := by
      intro hmem
      obtain ⟨w, hwS, hwq, horbit⟩ := hRorbit (z₀ ^ q) hmem
      have hz₀0 : z₀ ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hζp0) (pow_ne_zero _ hζq0)
      have hw0 : w ≠ 0 := by
        intro h0
        rw [h0] at hwq
        exact pow_ne_zero q hz₀0 (by rw [← hwq, zero_pow hq.pos.ne'])
      have hg : (z₀ / w) ^ q = 1 := by
        rw [div_pow, hwq, div_self (pow_ne_zero q hz₀0)]
      have hz₀S : z₀ ∈ S₀ := by
        have := horbit (z₀ / w) hg
        rwa [div_mul_cancel₀ z₀ hw0] at this
      exact (Finset.disjoint_left.mp hdis hz₀S) hz₀P
    refine ⟨insert (z₀ ^ q) R, ?_, ?_, ?_⟩
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hrR
      · exact ⟨z₀, Finset.mem_union_right _ hz₀P, rfl,
          fun g hg => Finset.mem_union_right _ (hPorbit g hg)⟩
      · obtain ⟨w, hw, hwq, horbit⟩ := hRorbit r hrR
        exact ⟨w, Finset.mem_union_left _ hw, hwq,
          fun g hg => Finset.mem_union_left _ (horbit g hg)⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hxS | hxP
      · rcases hRdich x hxS with hcl | hsp
        · exact Or.inl fun g hg => Finset.mem_union_left _ (hcl g hg)
        · exact Or.inr (Finset.mem_insert_of_mem hsp)
      · refine Or.inr ?_
        rw [hcommon1 x hxP]
        exact Finset.mem_insert_self _ _
    · intro e hpe
      have hPsum : ∑ y ∈ P, y ^ (q * e) = (q : F) * (z₀ ^ q) ^ e := by
        rw [Finset.sum_congr rfl (hcommon e), Finset.sum_const]
        have hPcard : P.card = q := by
          rw [hPdef, Finset.card_image_of_injOn (fun x1 hx1 x2 hx2 h =>
            hinj x1 (Finset.mem_coe.mp hx1) x2 (Finset.mem_coe.mp hx2) h),
            Finset.card_range]
        rw [hPcard, nsmul_eq_mul]
      rw [Finset.sum_union hdis, hRsum e hpe, hPsum, Finset.sum_insert hfresh, mul_add]
      ring

end FullExport

/-! ## THE GENERAL-t WINDOWED LAW (q-direction): the full reassembly induction

The capstone of the reassembly arc: with the `q`-power window of depth `m`, every
element of a two-prime vanishing set is `μ_{q^c·p}`-covered for some `c ≤ m` or
`μ_{q^{m+1}}`-covered — the complete `d`-coset reassembly in the `q`-direction, for
EVERY window depth, by induction: each level of window kills one more `μ_{q^c}`-packet
tier, the spectrum inherits the shallower window (full export), the inductive
hypothesis reassembles the spectrum one level down, and the upward rung multiplies the
recovered coset order by `q`. At the floor (`b = 0`) the spectrum lives in `μ_{p^{a+1}}`
and the prime-power slice machinery closes it. This is the O70-verified law's
`q`-direction in full generality — `m = 0` is de Bruijn (O77-cover form), `m = 1` is the
trichotomy. -/

section GeneralWindowedLaw

variable [DecidableEq F] [CharZero F]

/-- **The general-`t` windowed coset cover, `q`-direction**. -/
theorem windowed_coset_cover_q {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {a : ℕ} {ζp : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1))) :
    ∀ m : ℕ, ∀ b : ℕ, m ≤ b + 1 → ∀ ζq : F, IsPrimitiveRoot ζq (q ^ (b + 1)) →
      ∀ S : Finset F, (∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1) →
      (∀ c, c ≤ m → ∑ z ∈ S, z ^ (q ^ c) = 0) →
      ∀ x ∈ S,
        (∃ c, c ≤ m ∧ ∀ h : F, h ^ (q ^ c * p) = 1 → h * x ∈ S) ∨
        (∀ h : F, h ^ (q ^ (m + 1)) = 1 → h * x ∈ S) := by
  classical
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hqF0 : ((q : F)) ≠ 0 := by exact_mod_cast hq.pos.ne'
  intro m
  induction m with
  | zero =>
    intro b _ ζq hζq S hS hwin x hx
    have hsum : ∑ z ∈ S, z = 0 := by
      have := hwin 0 le_rfl
      simpa using this
    have hPU := two_prime_packet_decomposition hp hq hpq hζp hζq hS hsum
    obtain ⟨R, hRorbit, hRdich, _⟩ :=
      packetUnion_full_export hp hq hpq hζp hζq hPU
    rcases hRdich x hx with hP | hR1
    · exact Or.inl ⟨0, le_rfl, fun h hh => hP h (by simpa using hh)⟩
    · refine Or.inr ?_
      obtain ⟨w, hwS, hwq, horbit⟩ := hRorbit _ hR1
      have hx0 : x ≠ 0 := by
        intro h0
        have := hS x hx
        rw [h0, zero_pow (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)).ne']
          at this
        exact zero_ne_one this
      have hw0 : w ≠ 0 := by
        intro h0
        rw [h0, zero_pow hq.pos.ne'] at hwq
        exact pow_ne_zero q hx0 hwq.symm
      intro h hh
      have hhq : h ^ q = 1 := by
        rw [← pow_one (q : ℕ)] at hh ⊢
        simpa [pow_one] using hh
      have hgx : ((h * x) / w) ^ q = 1 := by
        rw [div_pow, mul_pow, hhq, one_mul, ← hwq, div_self (pow_ne_zero _ hw0)]
      have := horbit ((h * x) / w) hgx
      rwa [div_mul_cancel₀ (h * x) hw0] at this
  | succ m IH =>
    intro b hm1 ζq hζq S hS hwin x hx
    have hsum : ∑ z ∈ S, z = 0 := by
      have := hwin 0 (Nat.zero_le _)
      simpa using this
    have hPU := two_prime_packet_decomposition hp hq hpq hζp hζq hS hsum
    obtain ⟨R, hRorbit, hRdich, hRtransfer⟩ :=
      packetUnion_full_export hp hq hpq hζp hζq hPU
    rcases hRdich x hx with hP | hR1
    · exact Or.inl ⟨0, Nat.zero_le _, fun h hh => hP h (by simpa using hh)⟩
    have hx0 : x ≠ 0 := by
      intro h0
      have := hS x hx
      rw [h0, zero_pow (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)).ne'] at this
      exact zero_ne_one this
    -- the spectrum's window, one level shallower
    have hpqc : ∀ c : ℕ, ¬ p ∣ q ^ c := by
      intro c hdvd
      rcases Nat.Prime.dvd_of_dvd_pow hp hdvd with h
      exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
    have hRwin : ∀ c, c ≤ m → ∑ r ∈ R, r ^ (q ^ c) = 0 := by
      intro c hc
      have htr := hRtransfer (q ^ c) (hpqc c)
      have hSwin := hwin (c + 1) (by omega)
      have hexp : q * q ^ c = q ^ (c + 1) := by rw [pow_succ']
      rw [hexp] at htr
      rw [hSwin] at htr
      rcases mul_eq_zero.mp htr.symm with h | h
      · exact absurd h hqF0
      · exact h
    -- the spectrum's torsion
    rcases Nat.eq_zero_or_pos b with rfl | hbpos
    · -- floor case: b = 0, so m = 0 and R ⊆ μ_{p^(a+1)} is μ_p-closed
      have hm0 : m = 0 := by omega
      subst hm0
      have hRtor : ∀ r ∈ R, r ^ (p ^ (a + 1)) = 1 := by
        intro r hr
        obtain ⟨w, hwS, hwq, _⟩ := hRorbit r hr
        have hw := hS w hwS
        rw [← hwq, ← pow_mul]
        calc w ^ (q * p ^ (a + 1)) = (w ^ (p ^ (a + 1) * q ^ (0 + 1))) := by
              congr 1
              ring
          _ = 1 := hw
      have hRsum0 : ∑ r ∈ R, r = 0 := by
        have := hRwin 0 le_rfl
        simpa using this
      -- μ_p-closure of R at the prime-power floor
      have hslices := mu_p_membership_slices (m := a) hp hζp hRtor hRsum0
      have hωp : IsPrimitiveRoot (ζp ^ (p ^ a)) p :=
        hζp.pow (pow_pos hp.pos _) (by rw [pow_succ])
      have hRclosed : ∀ r ∈ R, ∀ g : F, g ^ p = 1 → g * r ∈ R := by
        intro r hr g hg
        obtain ⟨k, hk, hkg⟩ := hωp.eq_pow_of_pow_eq_one hg
        obtain ⟨u, hu, hur⟩ := hζp.eq_pow_of_pow_eq_one (hRtor r hr)
        obtain ⟨i, s, rfl, hs⟩ : ∃ i' s', u = i' * p ^ a + s' ∧ s' < p ^ a :=
          ⟨u / p ^ a, u % p ^ a, (Nat.div_add_mod' u (p ^ a)).symm,
            Nat.mod_lt _ (pow_pos hp.pos a)⟩
        have hi : i < p := by
          by_contra hge
          push Not at hge
          have h1 : p * p ^ a ≤ i * p ^ a := Nat.mul_le_mul_right _ hge
          have h2 : i * p ^ a + s < p ^ (a + 1) := hu
          rw [pow_succ'] at h2
          omega
        set i2 := (k + i) % p with hi2
        have hi2p : i2 < p := Nat.mod_lt _ hp.pos
        have hgr : g * r = ζp ^ (i2 * p ^ a + s) := by
          rw [← hkg, ← hur, ← pow_mul, ← pow_add]
          have hsplit : k + i = p * ((k + i) / p) + (k + i) % p :=
            (Nat.div_add_mod _ p).symm
          have hdecomp : p ^ a * k + (i * p ^ a + s)
              = p ^ (a + 1) * ((k + i) / p) + (i2 * p ^ a + s) := by
            calc p ^ a * k + (i * p ^ a + s) = (k + i) * p ^ a + s := by ring
            _ = (p * ((k + i) / p) + (k + i) % p) * p ^ a + s := by rw [← hsplit]
            _ = (p * p ^ a) * ((k + i) / p) + (((k + i) % p) * p ^ a + s) := by ring
            _ = p ^ (a + 1) * ((k + i) / p) + (i2 * p ^ a + s) := by
                rw [← pow_succ', hi2]
          rw [hdecomp, pow_add, pow_mul, hζp.pow_eq_one, one_pow, one_mul]
        rw [hgr]
        exact (hslices s hs i2 hi2p i hi).mpr (by rwa [hur])
      -- rung at A := p
      refine Or.inl ⟨1, le_rfl, ?_⟩
      have hcov := coset_lift (S := S) hq.pos hp.pos hx0 (fun g hg =>
        let hgR := hRclosed _ hR1 g hg
        let ⟨w, hwS, hwq, horbit⟩ := hRorbit _ hgR
        ⟨w, hwS, by rw [hwq], horbit⟩)
      intro h hh
      exact hcov h (by rwa [pow_one] at hh)
    · -- descent case: b = b'' + 1
      obtain ⟨b'', rfl⟩ : ∃ b'', b = b'' + 1 := ⟨b - 1, by omega⟩
      have hRtor : ∀ r ∈ R, r ^ (p ^ (a + 1) * q ^ (b'' + 1)) = 1 := by
        intro r hr
        obtain ⟨w, hwS, hwq, _⟩ := hRorbit r hr
        have hw := hS w hwS
        rw [← hwq, ← pow_mul]
        calc w ^ (q * (p ^ (a + 1) * q ^ (b'' + 1)))
            = w ^ (p ^ (a + 1) * q ^ (b'' + 1 + 1)) := by
              congr 1
              rw [pow_succ]
              ring
          _ = 1 := hw
      have hζq' : IsPrimitiveRoot (ζq ^ q) (q ^ (b'' + 1)) := by
        refine hζq.pow (pow_pos hq.pos _) ?_
        rw [pow_succ']
      have hIH := IH (b'') (by omega) (ζq ^ q) hζq' R hRtor hRwin _ hR1
      rcases hIH with ⟨c, hc, hcov⟩ | hcov
      · -- rung at A := q^c · p
        refine Or.inl ⟨c + 1, by omega, ?_⟩
        have hlift := coset_lift (S := S) hq.pos
          (Nat.mul_pos (pow_pos hq.pos c) hp.pos) hx0 (fun g hg =>
            let hgR := hcov g hg
            let ⟨w, hwS, hwq, horbit⟩ := hRorbit _ hgR
            ⟨w, hwS, by rw [hwq], horbit⟩)
        intro h hh
        refine hlift h ?_
        rw [show q * (q ^ c * p) = q ^ (c + 1) * p from by rw [pow_succ']; ring]
        exact hh
      · -- rung at A := q^{m+1}
        refine Or.inr ?_
        have hlift := coset_lift (S := S) hq.pos (pow_pos hq.pos (m + 1)) hx0
          (fun g hg =>
            let hgR := hcov g hg
            let ⟨w, hwS, hwq, horbit⟩ := hRorbit _ hgR
            ⟨w, hwS, by rw [hwq], horbit⟩)
        intro h hh
        refine hlift h ?_
        rw [show q * q ^ (m + 1) = q ^ (m + 1 + 1) from by
          rw [pow_succ', pow_succ']
          ring]
        exact hh

/-- **The general-`t` windowed coset cover, `p`-direction** — the role-swap
instantiation: with `p`-power window of depth `m`, every element is
`μ_{p^c·q}`-covered (some `c ≤ m`) or `μ_{p^{m+1}}`-covered. -/
theorem windowed_coset_cover_p {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {b : ℕ} {ζq : F} (hζq : IsPrimitiveRoot ζq (q ^ (b + 1))) :
    ∀ m : ℕ, ∀ a : ℕ, m ≤ a + 1 → ∀ ζp : F, IsPrimitiveRoot ζp (p ^ (a + 1)) →
      ∀ S : Finset F, (∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1) →
      (∀ c, c ≤ m → ∑ z ∈ S, z ^ (p ^ c) = 0) →
      ∀ x ∈ S,
        (∃ c, c ≤ m ∧ ∀ h : F, h ^ (p ^ c * q) = 1 → h * x ∈ S) ∨
        (∀ h : F, h ^ (p ^ (m + 1)) = 1 → h * x ∈ S) := by
  intro m a hm ζp hζp S hS hwin x hx
  exact windowed_coset_cover_q hq hp (Ne.symm hpq) hζq m a hm ζp hζp S
    (fun z hz => by rw [mul_comm]; exact hS z hz) hwin x hx

end GeneralWindowedLaw

/-! ## The designated-first-peel export: decomposition choice puts a chosen orbit in the spectrum

The enabling lemma of the joint (mixed-window) law: if `x ∈ S` has its full `μ_q`-orbit
inside `S`, then there is a decomposition of `S` whose spectrum CONTAINS `x^q` (with all
export properties) — peel `x`'s `q`-packet first; the remainder still vanishes (packets
sum to zero) and decomposes by O77; the export of the extended derivation inserts `x^q`
into the spectrum. This converts "x is `μ_q`-closed" (a dead end when `q ≤ t`) into "the
`q`-side recursion applies to `x`" — the move the joint induction needs in its
both-closed case. -/

section FirstPeel

variable [DecidableEq F] [CharZero F]

/-- **The designated-first-peel export**: a full `μ_q`-orbit can be sent into the
spectrum. -/
theorem first_peel_export {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1)
    (hsum : ∑ z ∈ S, z = 0)
    {x : F} (hx : x ∈ S) (hxorb : ∀ g : F, g ^ q = 1 → g * x ∈ S) :
    ∃ R : Finset F,
      (∀ r ∈ R, ∃ w ∈ S, w ^ q = r ∧ ∀ g : F, g ^ q = 1 → g * w ∈ S) ∧
      (∀ e : ℕ, ¬ p ∣ e →
        ∑ y ∈ S, y ^ (q * e) = (q : F) * ∑ r ∈ R, r ^ e) ∧
      x ^ q ∈ R := by
  classical
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hζq0 : ζq ≠ 0 := prim_ne_zero hζq (pow_pos hq.pos _)
  have hωq : IsPrimitiveRoot (ζq ^ (q ^ b)) q :=
    hζq.pow (pow_pos hq.pos _) (by rw [pow_succ])
  -- x's μ_q-orbit as a Finset
  set P : Finset F := S.filter (fun y => ∃ g : F, g ^ q = 1 ∧ y = g * x) with hPdef
  have hxP : x ∈ P := by
    rw [hPdef]
    exact Finset.mem_filter.mpr ⟨hx, 1, one_pow q, (one_mul x).symm⟩
  have hPsub : P ⊆ S := Finset.filter_subset _ _
  have hPmem : ∀ g : F, g ^ q = 1 → g * x ∈ P := by
    intro g hg
    rw [hPdef]
    exact Finset.mem_filter.mpr ⟨hxorb g hg, g, hg, rfl⟩
  have hx0 : x ≠ 0 := by
    intro h0
    have := hS x hx
    rw [h0, zero_pow (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)).ne'] at this
    exact zero_ne_one this
  -- P = image of μ_q-roots; card q; common q-th power x^q; sum zero
  have hPimg : P = (Finset.range q).image (fun k => (ζq ^ (q ^ b)) ^ k * x) := by
    apply Finset.Subset.antisymm
    · intro y hy
      obtain ⟨-, g, hg, rfl⟩ := Finset.mem_filter.mp (hPdef ▸ hy)
      obtain ⟨k, hk, hkg⟩ := hωq.eq_pow_of_pow_eq_one hg
      exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, by rw [hkg]⟩
    · intro y hy
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
      refine hPdef ▸ Finset.mem_filter.mpr ⟨?_, (ζq ^ (q ^ b)) ^ k, ?_, rfl⟩
      · refine hxorb _ ?_
        rw [← pow_mul, ← pow_mul,
          show q ^ b * (k * q) = q ^ (b + 1) * k from by rw [pow_succ']; ring,
          pow_mul, hζq.pow_eq_one, one_pow]
      · rw [← pow_mul, ← pow_mul,
          show q ^ b * (k * q) = q ^ (b + 1) * k from by rw [pow_succ']; ring,
          pow_mul, hζq.pow_eq_one, one_pow]
  have hPcommon : ∀ y ∈ P, y ^ q = x ^ q := by
    intro y hy
    obtain ⟨-, g, hg, rfl⟩ := Finset.mem_filter.mp (hPdef ▸ hy)
    rw [mul_pow, hg, one_mul]
  have hPinj : Set.InjOn (fun k => (ζq ^ (q ^ b)) ^ k * x) (Finset.range q : Set ℕ) := by
    intro k1 hk1 k2 hk2 hke
    have hke' : (ζq ^ (q ^ b)) ^ k1 = (ζq ^ (q ^ b)) ^ k2 :=
      mul_right_cancel₀ hx0 hke
    exact hωq.pow_inj (Finset.mem_range.mp (Finset.mem_coe.mp hk1))
      (Finset.mem_range.mp (Finset.mem_coe.mp hk2)) hke'
  have hPcard : P.card = q := by
    rw [hPimg, Finset.card_image_of_injOn hPinj, Finset.card_range]
  have hPsum : ∑ y ∈ P, y = 0 := by
    rw [hPimg, Finset.sum_image (fun k1 hk1 k2 hk2 h =>
      hPinj (Finset.mem_coe.mpr hk1) (Finset.mem_coe.mpr hk2) h)]
    exact prime_packet_sum_zero hq hωq x
  -- the remainder vanishes and is torsion
  set S' : Finset F := S \ P with hS'def
  have hS'sum : ∑ z ∈ S', z = 0 := by
    have hsd := Finset.sum_sdiff (f := fun y : F => y) hPsub
    rw [hPsum, add_zero] at hsd
    rw [hS'def, hsd]
    exact hsum
  have hS'tor : ∀ z ∈ S', z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1 :=
    fun z hz => hS z (Finset.mem_sdiff.mp hz).1
  -- decompose the remainder and export it
  have hPU' := two_prime_packet_decomposition hp hq hpq hζp hζq hS'tor hS'sum
  obtain ⟨R', hR'orbit, hR'dich, hR'transfer⟩ :=
    packetUnion_full_export hp hq hpq hζp hζq hPU'
  -- the assembled spectrum: insert x^q
  have hfresh : x ^ q ∉ R' := by
    intro hmem
    obtain ⟨w, hwS', hwq, horbit⟩ := hR'orbit (x ^ q) hmem
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0, zero_pow hq.pos.ne'] at hwq
      exact pow_ne_zero q hx0 hwq.symm
    have hg : (x / w) ^ q = 1 := by
      rw [div_pow, hwq, div_self (pow_ne_zero q hx0)]
    have hxS' : x ∈ S' := by
      have := horbit (x / w) hg
      rwa [div_mul_cancel₀ x hw0] at this
    exact (Finset.mem_sdiff.mp hxS').2 hxP
  refine ⟨insert (x ^ q) R', ?_, ?_, Finset.mem_insert_self _ _⟩
  · intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hrR
    · exact ⟨x, hx, rfl, hxorb⟩
    · obtain ⟨w, hwS', hwq, horbit⟩ := hR'orbit r hrR
      exact ⟨w, (Finset.mem_sdiff.mp hwS').1, hwq,
        fun g hg => (Finset.mem_sdiff.mp (horbit g hg)).1⟩
  · intro e hpe
    have hPsume : ∑ y ∈ P, y ^ (q * e) = (q : F) * (x ^ q) ^ e := by
      have hPcommon' : ∀ y ∈ P, y ^ (q * e) = (x ^ q) ^ e := by
        intro y hy
        rw [pow_mul, hPcommon y hy]
      rw [Finset.sum_congr rfl hPcommon', Finset.sum_const, hPcard, nsmul_eq_mul]
    have hsplit : ∑ y ∈ S, y ^ (q * e)
        = ∑ y ∈ S', y ^ (q * e) + ∑ y ∈ P, y ^ (q * e) := by
      rw [hS'def]
      exact (Finset.sum_sdiff (f := fun y : F => y ^ (q * e)) hPsub).symm
    rw [hsplit, hR'transfer e hpe, hPsume, Finset.sum_insert hfresh, mul_add]
    ring

end FirstPeel

/-! ## The full divisor-form law below `p`: window `t < p` ⟹ `μ_d`-covered, `d ∣ n`, `d > t`

In the regime `t < p` the `q`-direction law alone already yields the complete
O70/divisor form: the left case's coset order `q^c·p ≥ p` clears the window for free,
and the right case's `q^{m+1}` clears it by the window-depth choice. This is the full
mixed-radix law on the half of the parameter space where one prime exceeds the window —
hypothesis: only the `q`-power window, conclusion: a genuine divisor of `n` above `t`
whose full coset covers each element. -/

section BelowP

variable [DecidableEq F] [CharZero F]

/-- **The divisor-form windowed law below `p`**. -/
theorem windowed_coset_cover_below_p {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {a b m t : ℕ} (hm : m ≤ b) (htp : t < p) (htq : t < q ^ (m + 1))
    {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1)
    (hwin : ∀ c, c ≤ m → ∑ z ∈ S, z ^ (q ^ c) = 0) :
    ∀ x ∈ S, ∃ d : ℕ, d ∣ p ^ (a + 1) * q ^ (b + 1) ∧ t < d ∧
      (∀ h : F, h ^ d = 1 → h * x ∈ S) := by
  intro x hx
  rcases windowed_coset_cover_q hp hq hpq hζp m b (by omega) ζq hζq S hS hwin x hx
    with ⟨c, hc, hcov⟩ | hcov
  · refine ⟨q ^ c * p, ?_, ?_, hcov⟩
    · rw [mul_comm (q ^ c) p]
      exact Nat.mul_dvd_mul (dvd_pow_self p (by omega)) (pow_dvd_pow q (by omega))
    · calc t < p := htp
      _ ≤ q ^ c * p := Nat.le_mul_of_pos_left p (pow_pos hq.pos c)
  · refine ⟨q ^ (m + 1), ?_, htq, hcov⟩
    exact Dvd.dvd.mul_left (pow_dvd_pow q (by omega)) _

end BelowP

/-! ## The bilateral export and the mixed identity: O118's first brick

One decomposition, BOTH spectra: `R` (the `μ_q`-packet `q`-th-power spectrum) and `T`
(the `μ_p`-packet `p`-th-power spectrum), each collision-free with its orbit property —
and the **mixed identity** coupling them at the punctured exponents:
`Σ_S y^{q·e} = q·Σ_R r^e + p·Σ_T τ^{q·e/p}` for `p ∣ e` (at such exponents BOTH packet
types survive: `μ_q`-packets contribute `q·r^e`, `μ_p`-packets contribute `p·τ^{qe/p}`
through their common `p`-th power). This is the equation the valuation induction (O118)
resolves; with it, every nested spectrum inherits the full scaled window. -/

section BilateralExport

variable [DecidableEq F]

/-- **The bilateral export**: both spectra, both orbit properties, the clean transfer
on the `R`-side, and the mixed identity at `p ∣ e`. -/
theorem packetUnion_bilateral_export {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hPU : PacketUnion p q a b ζp ζq S) :
    ∃ R T : Finset F,
      (∀ r ∈ R, ∃ w ∈ S, w ^ q = r ∧ ∀ g : F, g ^ q = 1 → g * w ∈ S) ∧
      (∀ τ ∈ T, ∃ w ∈ S, w ^ p = τ ∧ ∀ g : F, g ^ p = 1 → g * w ∈ S) ∧
      (∀ e : ℕ, ¬ p ∣ e →
        ∑ y ∈ S, y ^ (q * e) = (q : F) * ∑ r ∈ R, r ^ e) ∧
      (∀ e : ℕ, p ∣ e →
        ∑ y ∈ S, y ^ (q * e)
          = (q : F) * ∑ r ∈ R, r ^ e + (p : F) * ∑ τ ∈ T, τ ^ (q * e / p)) ∧
      (∀ e : ℕ, ¬ q ∣ e →
        ∑ y ∈ S, y ^ (p * e) = (p : F) * ∑ τ ∈ T, τ ^ e) := by
  classical
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hζp0 : ζp ≠ 0 := prim_ne_zero hζp (pow_pos hp.pos _)
  have hζq0 : ζq ≠ 0 := prim_ne_zero hζq (pow_pos hq.pos _)
  have hωp : IsPrimitiveRoot (ζp ^ (p ^ a)) p :=
    hζp.pow (pow_pos hp.pos _) (by rw [pow_succ])
  have hωq : IsPrimitiveRoot (ζq ^ (q ^ b)) q :=
    hζq.pow (pow_pos hq.pos _) (by rw [pow_succ])
  induction hPU with
  | empty =>
    exact ⟨∅, ∅, fun r hr => absurd hr (Finset.notMem_empty r),
      fun τ hτ => absurd hτ (Finset.notMem_empty τ),
      fun e _ => by simp, fun e _ => by simp, fun e _ => by simp⟩
  | @addP S₀ s j t hsub hnot IH =>
    obtain ⟨R, T, hRorb, hTorb, hRtr, hMix, hTtr⟩ := IH
    set P : Finset F := (Finset.range p).image
      (fun i'' => ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t)) with hPdef
    set τ₀ : F := (ζp ^ s * ζq ^ (j * q ^ b + t)) ^ p with hτ₀
    have hdis : Disjoint S₀ P := by
      rw [Finset.disjoint_left]
      intro y hyS hyP
      obtain ⟨i'', hi'', rfl⟩ := Finset.mem_image.mp (hPdef ▸ hyP)
      exact hnot i'' (Finset.mem_range.mp hi'') hyS
    -- every member of the p-packet has p-th power τ₀
    have hcommon : ∀ y ∈ P, y ^ p = τ₀ := by
      intro y hy
      obtain ⟨i'', _, rfl⟩ := Finset.mem_image.mp (hPdef ▸ hy)
      have hone : ((ζp ^ (i'' * p ^ a)) : F) ^ p = 1 := by
        rw [← pow_mul, show i'' * p ^ a * p = p ^ (a + 1) * i'' from by
          rw [pow_succ]; ring, pow_mul, hζp.pow_eq_one, one_pow]
      calc (ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t)) ^ p
          = (ζp ^ (i'' * p ^ a)) ^ p * ((ζp ^ s * ζq ^ (j * q ^ b + t)) ^ p) := by
            rw [pow_add (a := ζp)]
            ring
        _ = τ₀ := by rw [hone, one_mul, hτ₀]
    -- the packet is x₀'s full μ_p-orbit (x₀ := the i'' = 0 member)
    set x₀ : F := ζp ^ s * ζq ^ (j * q ^ b + t) with hx₀
    have hx₀P : x₀ ∈ P := by
      rw [hPdef]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hp.pos, by
        rw [hx₀, Nat.zero_mul, Nat.zero_add]⟩
    have hPorbit : ∀ g : F, g ^ p = 1 → g * x₀ ∈ P := by
      intro g hg
      obtain ⟨k, hk, hkg⟩ := hωp.eq_pow_of_pow_eq_one hg
      refine hPdef ▸ Finset.mem_image.mpr
        ⟨k % p, Finset.mem_range.mpr (Nat.mod_lt _ hp.pos), ?_⟩
      symm
      rw [← hkg, hx₀]
      have hdecomp : p ^ a * k + s = p ^ (a + 1) * (k / p) + ((k % p) * p ^ a + s) := by
        calc p ^ a * k + s
            = p ^ a * (p * (k / p) + k % p) + s := by rw [Nat.div_add_mod]
        _ = (p ^ a * p) * (k / p) + ((k % p) * p ^ a + s) := by ring
        _ = p ^ (a + 1) * (k / p) + ((k % p) * p ^ a + s) := by rw [← pow_succ]
      calc (ζp ^ (p ^ a)) ^ k * (ζp ^ s * ζq ^ (j * q ^ b + t))
          = ζp ^ (p ^ a * k + s) * ζq ^ (j * q ^ b + t) := by
            rw [← pow_mul, pow_add]
            ring
        _ = ζp ^ ((k % p) * p ^ a + s) * ζq ^ (j * q ^ b + t) := by
            rw [hdecomp, pow_add, pow_mul, hζp.pow_eq_one, one_pow, one_mul]
    -- freshness of τ₀ in T by the p-side orbit argument
    have hfresh : τ₀ ∉ T := by
      intro hmem
      obtain ⟨w, hwS, hwp, horbit⟩ := hTorb τ₀ hmem
      have hx₀0 : x₀ ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hζp0) (pow_ne_zero _ hζq0)
      have hw0 : w ≠ 0 := by
        intro h0
        rw [h0, zero_pow hp.pos.ne'] at hwp
        have : τ₀ ≠ 0 := by
          rw [hτ₀]
          exact pow_ne_zero _ hx₀0
        exact this hwp.symm
      have hg : (x₀ / w) ^ p = 1 := by
        rw [div_pow, hwp, hτ₀, div_self (pow_ne_zero _ hx₀0)]
      have hx₀S : x₀ ∈ S₀ := by
        have := horbit (x₀ / w) hg
        rwa [div_mul_cancel₀ x₀ hw0] at this
      exact (Finset.disjoint_left.mp hdis hx₀S) hx₀P
    -- packet injectivity and cardinality
    have hinj : ∀ x1 ∈ Finset.range p, ∀ x2 ∈ Finset.range p,
        ζp ^ (x1 * p ^ a + s) * ζq ^ (j * q ^ b + t)
          = ζp ^ (x2 * p ^ a + s) * ζq ^ (j * q ^ b + t) → x1 = x2 := by
      intro x1 hx1 x2 hx2 hxe
      have hconst0 : ζq ^ (j * q ^ b + t) ≠ 0 := pow_ne_zero _ hζq0
      have hs0 : ζp ^ s ≠ 0 := pow_ne_zero _ hζp0
      have hpow : ζp ^ (x1 * p ^ a) = ζp ^ (x2 * p ^ a) := by
        have hcancel := mul_right_cancel₀ hconst0 hxe
        rw [pow_add, pow_add] at hcancel
        exact mul_right_cancel₀ hs0 hcancel
      have hpow' : (ζp ^ (p ^ a)) ^ x1 = (ζp ^ (p ^ a)) ^ x2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (p ^ a) x1, Nat.mul_comm (p ^ a) x2]
        exact hpow
      exact hωp.pow_inj (Finset.mem_range.mp hx1) (Finset.mem_range.mp hx2) hpow'
    have hPcard : P.card = p := by
      rw [hPdef, Finset.card_image_of_injOn (fun x1 hx1 x2 hx2 h =>
        hinj x1 (Finset.mem_coe.mp hx1) x2 (Finset.mem_coe.mp hx2) h),
        Finset.card_range]
    refine ⟨R, insert τ₀ T, ?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      obtain ⟨w, hw, hwq, horbit⟩ := hRorb r hr
      exact ⟨w, Finset.mem_union_left _ hw, hwq,
        fun g hg => Finset.mem_union_left _ (horbit g hg)⟩
    · intro τ hτ
      rcases Finset.mem_insert.mp hτ with rfl | hτT
      · exact ⟨x₀, Finset.mem_union_right _ hx₀P, (hcommon x₀ hx₀P).symm ▸ rfl,
          fun g hg => Finset.mem_union_right _ (hPorbit g hg)⟩
      · obtain ⟨w, hw, hwp, horbit⟩ := hTorb τ hτT
        exact ⟨w, Finset.mem_union_left _ hw, hwp,
          fun g hg => Finset.mem_union_left _ (horbit g hg)⟩
    · -- clean R-transfer: p-packet dies at q·e with p ∤ e
      intro e hpe
      have hωpe : IsPrimitiveRoot ((ζp ^ (p ^ a)) ^ (q * e)) p := by
        refine hωp.pow_of_coprime _ ?_
        have hqp : Nat.Coprime q p := (Nat.coprime_primes hq hp).mpr (Ne.symm hpq)
        have hep : Nat.Coprime e p := by
          rcases Nat.coprime_or_dvd_of_prime hp e with h | h
          · exact h.symm
          · exact absurd h hpe
        exact Nat.Coprime.mul_left hqp hep
      have hPsum : ∑ y ∈ P, y ^ (q * e) = 0 := by
        rw [hPdef, Finset.sum_image hinj]
        have hterm : ∀ i'' ∈ Finset.range p,
            (ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t)) ^ (q * e)
              = ((ζp ^ (p ^ a)) ^ (q * e)) ^ i''
                * ((ζp ^ s) ^ (q * e) * (ζq ^ (j * q ^ b + t)) ^ (q * e)) := by
          intro i'' _
          ring
        rw [Finset.sum_congr rfl hterm]
        exact prime_packet_sum_zero hp hωpe _
      rw [Finset.sum_union hdis, hRtr e hpe, hPsum, add_zero]
    · -- the mixed identity at p ∣ e: the p-packet contributes p·τ₀^{qe/p}
      intro e hpe
      obtain ⟨e', rfl⟩ := hpe
      have hPsum : ∑ y ∈ P, y ^ (q * (p * e')) = (p : F) * τ₀ ^ (q * e') := by
        have hcom : ∀ y ∈ P, y ^ (q * (p * e')) = τ₀ ^ (q * e') := by
          intro y hy
          rw [show q * (p * e') = p * (q * e') from by ring, pow_mul, hcommon y hy]
        rw [Finset.sum_congr rfl hcom, Finset.sum_const, hPcard, nsmul_eq_mul]
      have hdiv : q * (p * e') / p = q * e' := by
        rw [show q * (p * e') = p * (q * e') from by ring]
        exact Nat.mul_div_cancel_left _ hp.pos
      rw [Finset.sum_union hdis, hMix (p * e') ⟨e', rfl⟩, hPsum, hdiv,
        Finset.sum_insert hfresh, mul_add]
      have hdiv2 : q * (p * e') / p = q * e' := hdiv
      ring
    · -- the mirror T-transfer: the new p-packet contributes p·τ₀^e
      intro e hqe
      have hPsum : ∑ y ∈ P, y ^ (p * e) = (p : F) * τ₀ ^ e := by
        have hcom : ∀ y ∈ P, y ^ (p * e) = τ₀ ^ e := by
          intro y hy
          rw [pow_mul, hcommon y hy]
        rw [Finset.sum_congr rfl hcom, Finset.sum_const, hPcard, nsmul_eq_mul]
      rw [Finset.sum_union hdis, hTtr e hqe, hPsum, Finset.sum_insert hfresh, mul_add]
      ring
  | @addQ S₀ s i t hsub hnot IH =>
    obtain ⟨R, T, hRorb, hTorb, hRtr, hMix, hTtr⟩ := IH
    set P : Finset F := (Finset.range q).image
      (fun j'' => ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t)) with hPdef
    set z₀ : F := ζp ^ (i * p ^ a + s) * ζq ^ t with hz₀
    have hz₀P : z₀ ∈ P := by
      rw [hPdef]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hq.pos, by
        rw [hz₀, Nat.zero_mul, Nat.zero_add]⟩
    have hdis : Disjoint S₀ P := by
      rw [Finset.disjoint_left]
      intro y hyS hyP
      obtain ⟨j'', hj'', rfl⟩ := Finset.mem_image.mp (hPdef ▸ hyP)
      exact hnot j'' (Finset.mem_range.mp hj'') hyS
    have hinj : ∀ x1 ∈ Finset.range q, ∀ x2 ∈ Finset.range q,
        ζp ^ (i * p ^ a + s) * ζq ^ (x1 * q ^ b + t)
          = ζp ^ (i * p ^ a + s) * ζq ^ (x2 * q ^ b + t) → x1 = x2 := by
      intro x1 hx1 x2 hx2 hxe
      have hconst0 : ζp ^ (i * p ^ a + s) ≠ 0 := pow_ne_zero _ hζp0
      have ht0 : ζq ^ t ≠ 0 := pow_ne_zero _ hζq0
      have hpow : ζq ^ (x1 * q ^ b) = ζq ^ (x2 * q ^ b) := by
        have hcancel := mul_left_cancel₀ hconst0 hxe
        rw [pow_add, pow_add] at hcancel
        exact mul_right_cancel₀ ht0 hcancel
      have hpow' : (ζq ^ (q ^ b)) ^ x1 = (ζq ^ (q ^ b)) ^ x2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (q ^ b) x1, Nat.mul_comm (q ^ b) x2]
        exact hpow
      exact hωq.pow_inj (Finset.mem_range.mp hx1) (Finset.mem_range.mp hx2) hpow'
    have hPcard : P.card = q := by
      rw [hPdef, Finset.card_image_of_injOn (fun x1 hx1 x2 hx2 h =>
        hinj x1 (Finset.mem_coe.mp hx1) x2 (Finset.mem_coe.mp hx2) h),
        Finset.card_range]
    have hcommon : ∀ e' : ℕ, ∀ y ∈ P, y ^ (q * e') = (z₀ ^ q) ^ e' := by
      intro e' y hy
      obtain ⟨j'', _, rfl⟩ := Finset.mem_image.mp (hPdef ▸ hy)
      have hone : ((ζq ^ (j'' * q ^ b)) : F) ^ (q * e') = 1 := by
        rw [← pow_mul, show j'' * q ^ b * (q * e') = q ^ (b + 1) * (j'' * e') from by
          ring, pow_mul, hζq.pow_eq_one, one_pow]
      calc (ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t)) ^ (q * e')
          = (ζp ^ (i * p ^ a + s)) ^ (q * e')
            * ((ζq ^ (j'' * q ^ b)) ^ (q * e') * (ζq ^ t) ^ (q * e')) := by
            rw [pow_add (a := ζq)]
            ring
        _ = (ζp ^ (i * p ^ a + s)) ^ (q * e') * (ζq ^ t) ^ (q * e') := by
            rw [hone, one_mul]
        _ = (z₀ ^ q) ^ e' := by rw [hz₀]; ring
    have hPorbit : ∀ g : F, g ^ q = 1 → g * z₀ ∈ P := by
      intro g hg
      obtain ⟨k, hk, hkg⟩ := hωq.eq_pow_of_pow_eq_one hg
      refine hPdef ▸ Finset.mem_image.mpr
        ⟨k % q, Finset.mem_range.mpr (Nat.mod_lt _ hq.pos), ?_⟩
      symm
      rw [← hkg, hz₀]
      have hdecomp : q ^ b * k + t = q ^ (b + 1) * (k / q) + ((k % q) * q ^ b + t) := by
        calc q ^ b * k + t
            = q ^ b * (q * (k / q) + k % q) + t := by rw [Nat.div_add_mod]
        _ = (q ^ b * q) * (k / q) + ((k % q) * q ^ b + t) := by ring
        _ = q ^ (b + 1) * (k / q) + ((k % q) * q ^ b + t) := by rw [← pow_succ]
      calc (ζq ^ (q ^ b)) ^ k * (ζp ^ (i * p ^ a + s) * ζq ^ t)
          = ζp ^ (i * p ^ a + s) * ζq ^ (q ^ b * k + t) := by
            rw [← pow_mul, pow_add]
            ring
        _ = ζp ^ (i * p ^ a + s) * ζq ^ ((k % q) * q ^ b + t) := by
            rw [hdecomp, pow_add (a := ζq), pow_mul (a := ζq), hζq.pow_eq_one, one_pow, one_mul]
    have hfresh : z₀ ^ q ∉ R := by
      intro hmem
      obtain ⟨w, hwS, hwq, horbit⟩ := hRorb (z₀ ^ q) hmem
      have hz₀0 : z₀ ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hζp0) (pow_ne_zero _ hζq0)
      have hw0 : w ≠ 0 := by
        intro h0
        rw [h0, zero_pow hq.pos.ne'] at hwq
        exact pow_ne_zero q hz₀0 hwq.symm
      have hg : (z₀ / w) ^ q = 1 := by
        rw [div_pow, hwq, div_self (pow_ne_zero q hz₀0)]
      have hz₀S : z₀ ∈ S₀ := by
        have := horbit (z₀ / w) hg
        rwa [div_mul_cancel₀ z₀ hw0] at this
      exact (Finset.disjoint_left.mp hdis hz₀S) hz₀P
    refine ⟨insert (z₀ ^ q) R, T, ?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hrR
      · exact ⟨z₀, Finset.mem_union_right _ hz₀P, rfl,
          fun g hg => Finset.mem_union_right _ (hPorbit g hg)⟩
      · obtain ⟨w, hw, hwq, horbit⟩ := hRorb r hrR
        exact ⟨w, Finset.mem_union_left _ hw, hwq,
          fun g hg => Finset.mem_union_left _ (horbit g hg)⟩
    · intro τ hτ
      obtain ⟨w, hw, hwp, horbit⟩ := hTorb τ hτ
      exact ⟨w, Finset.mem_union_left _ hw, hwp,
        fun g hg => Finset.mem_union_left _ (horbit g hg)⟩
    · intro e hpe
      have hPsum : ∑ y ∈ P, y ^ (q * e) = (q : F) * (z₀ ^ q) ^ e := by
        rw [Finset.sum_congr rfl (hcommon e), Finset.sum_const, hPcard, nsmul_eq_mul]
      rw [Finset.sum_union hdis, hRtr e hpe, hPsum, Finset.sum_insert hfresh, mul_add]
      ring
    · intro e hpe
      obtain ⟨e', rfl⟩ := hpe
      have hPsum : ∑ y ∈ P, y ^ (q * (p * e')) = (q : F) * (z₀ ^ q) ^ (p * e') := by
        rw [Finset.sum_congr rfl (hcommon (p * e')), Finset.sum_const, hPcard,
          nsmul_eq_mul]
      rw [Finset.sum_union hdis, hMix (p * e') ⟨e', rfl⟩, hPsum,
        Finset.sum_insert hfresh, mul_add]
      ring
    · -- the mirror T-transfer: the q-packet dies at p·e when q ∤ e
      intro e hqe
      have hωqe : IsPrimitiveRoot ((ζq ^ (q ^ b)) ^ (p * e)) q := by
        refine hωq.pow_of_coprime _ ?_
        have hpq' : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
        have heq' : Nat.Coprime e q := by
          rcases Nat.coprime_or_dvd_of_prime hq e with h | h
          · exact h.symm
          · exact absurd h hqe
        exact Nat.Coprime.mul_left hpq' heq'
      have hPsum : ∑ y ∈ P, y ^ (p * e) = 0 := by
        rw [hPdef, Finset.sum_image hinj]
        have hterm : ∀ j'' ∈ Finset.range q,
            (ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t)) ^ (p * e)
              = ((ζq ^ (q ^ b)) ^ (p * e)) ^ j''
                * ((ζp ^ (i * p ^ a + s)) ^ (p * e) * (ζq ^ t) ^ (p * e)) := by
          intro j'' _
          ring
        rw [Finset.sum_congr rfl hterm]
        exact prime_packet_sum_zero hq hωqe _
      rw [Finset.sum_union hdis, hTtr e hqe, hPsum, add_zero]

end BilateralExport

/-! ## The set-form law and the two-prime budget below `p`

From the divisor-form coverage (O117): a windowed set IS the union of its members'
alive covering cosets — the set-level law — and is therefore DETERMINED by which alive
cosets it contains: the windowed family injects into the power set of alive cosets,
giving the two-prime analogue of the 2-power budget (`tower_count`/O55) in the
below-`p` regime. -/

section BelowPBudget

variable [DecidableEq F] [CharZero F]

open Classical in
/-- **The set-form law below `p`**: a windowed set equals the union of the alive full
cosets it contains. -/
theorem windowed_eq_union_alive_below_p {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {a b m t : ℕ} (hm : m ≤ b) (htp : t < p) (htq : t < q ^ (m + 1))
    {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1)
    (hwin : ∀ c, c ≤ m → ∑ z ∈ S, z ^ (q ^ c) = 0) :
    ∀ x ∈ S, ∃ d : ℕ, d ∣ p ^ (a + 1) * q ^ (b + 1) ∧ t < d ∧
      x ∈ S.filter (fun y => ∀ h : F, h ^ d = 1 → h * y ∈ S) := by
  intro x hx
  obtain ⟨d, hdvd, htd, hcov⟩ :=
    windowed_coset_cover_below_p hp hq hpq hm htp htq hζp hζq hS hwin x hx
  exact ⟨d, hdvd, htd, Finset.mem_filter.mpr ⟨hx, hcov⟩⟩

/-- **The recovery injection**: a windowed set is determined by its trace on the alive
cosets — concretely, `S` is recovered from the data `x ↦ (d_x, coset of x)`; the
counting consequence is that the windowed family injects into the set of functions from
the (finite) alive-coset family to `Bool`. We package the budget as: two windowed sets
with the same alive-coset trace are equal. -/
theorem windowed_determined_by_alive_trace {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {a b m t : ℕ} (hm : m ≤ b) (htp : t < p) (htq : t < q ^ (m + 1))
    {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S₁ S₂ : Finset F}
    (hS₁ : ∀ z ∈ S₁, z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1)
    (hS₂ : ∀ z ∈ S₂, z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1)
    (hwin₁ : ∀ c, c ≤ m → ∑ z ∈ S₁, z ^ (q ^ c) = 0)
    (hwin₂ : ∀ c, c ≤ m → ∑ z ∈ S₂, z ^ (q ^ c) = 0)
    -- equal traces: for every alive divisor d and every point y, the full μ_d-coset of
    -- y lies in S₁ iff it lies in S₂
    (htrace : ∀ d : ℕ, d ∣ p ^ (a + 1) * q ^ (b + 1) → t < d → ∀ y : F,
      ((∀ h : F, h ^ d = 1 → h * y ∈ S₁) ↔ (∀ h : F, h ^ d = 1 → h * y ∈ S₂))) :
    S₁ = S₂ := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨d, hdvd, htd, hcov⟩ :=
      windowed_coset_cover_below_p hp hq hpq hm htp htq hζp hζq hS₁ hwin₁ x hx
    have hcov₂ := (htrace d hdvd htd x).mp hcov
    have := hcov₂ 1 (one_pow d)
    rwa [one_mul] at this
  · intro x hx
    obtain ⟨d, hdvd, htd, hcov⟩ :=
      windowed_coset_cover_below_p hp hq hpq hm htp htq hζp hζq hS₂ hwin₂ x hx
    have hcov₁ := (htrace d hdvd htd x).mpr hcov
    have := hcov₁ 1 (one_pow d)
    rwa [one_mul] at this

end BelowPBudget

/-! ## Coverage monotonicity and the upgrade question

Coverage is divisor-monotone (`μ_d`-coverage implies `μ_{d'}`-coverage for every
`d' ∣ d`), so the directional laws' existentials certify a coverage IDEAL; the all-`t`
law asks whether the window forces this ideal to reach above `t`. The missing engine is
the UPGRADE: small certified coverage + full window ⟹ alive coverage — with the
contracted-fold (valued, general-radix) route as the mapped candidate. -/

section CoverageMono

/-- Coverage is divisor-monotone: a full `μ_d`-coset inside `S` contains the full
`μ_{d'}`-coset for every divisor `d' ∣ d`. -/
theorem coverage_mono {S : Finset F} {x : F} {d d' : ℕ} (hdvd : d' ∣ d)
    (hcov : ∀ h : F, h ^ d = 1 → h * x ∈ S) :
    ∀ h : F, h ^ d' = 1 → h * x ∈ S := by
  intro h hh
  obtain ⟨k, rfl⟩ := hdvd
  refine hcov h ?_
  rw [pow_mul, hh, one_pow]

end CoverageMono

end DeBruijnTwoPrime
