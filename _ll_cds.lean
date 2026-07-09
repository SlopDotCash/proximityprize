/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic

/-!
# Issue #232 — the CRT double-slice engine for the de Bruijn two-prime base case

The O67 program (DISPROOF_LOG): vanishing subset sums of `n`-th roots of unity for
two-prime-smooth `n = p^a · q^b` decompose into disjoint rotated full prime packets
(de Bruijn 1953). The mapped formalization route is the *elementary double-slice
argument*: apply the O66 packet-slice engine (`LamLeungTwoPow.packet_mul_coeff`) at
BOTH primes via CRT exponent coordinates `ZMod n ≃ ZMod p^a × ZMod q^b`.

This file machine-checks the engine of that route, in three strictly increasing layers:

* `packet_slice_coeff` — the O66 slice lemma over an arbitrary semiring of
  coefficients (O66 stated it for `ℚ` only): every multiple `G·R` of the geometric
  packet `G = Σ_{t<p} X^{t·q}` with `deg R < q` has all `p` of its `q`-length
  coefficient slices equal to `R`.
* `slice_of_packet_minpoly` — the weighted slice engine over an ARBITRARY base field
  `K`: if `minpoly K η` is the geometric packet `Σ_{t<p} X^{t·q}`, then any vanishing
  `K`-weighted sum `Σ_{e<p·q} a_e · η^e = 0` has μ-shift invariant coefficient slices
  `a_{i·q+s} = a_{i'·q+s}`. This strictly generalizes the O66 mechanism from `0/1`
  indicator weights over `ℚ` to arbitrary weights over any base field — the form the
  CRT assembly needs (base field `ℚ(ζ_{p^a})`, weights = fiber sums).
* `weighted_vanishing_slice_rat` — instantiation at `K = ℚ`: rational-weighted
  vanishing sums of `p^(m+1)`-th roots of unity (char 0) slice. The O66 closure
  theorem is the `0/1` special case.
* `crt_fiber_slice` — the CRT double-slice itself, fiber-sum form: a vanishing double
  sum `Σ_{(j,c)∈I} ξ^j · η^c = 0` over a coprime exponent grid (ξ from the base field
  `K`, η with packet minimal polynomial over `K`) has μ_q-shift invariant fiber sums
  `A(c) = Σ_{(j,c)∈I} ξ^j ∈ K`: `A(i·q^{b-1}+s)` is independent of `i < q`.
  Falsified-first: `scripts/probes/probe_crt_double_slice.py` verifies both claims
  exactly (integer arithmetic mod cyclotomics) — the weighted-slice ⟺ vanishing
  equivalence at `n = 8, 9` (20 000 samples each, 0 mismatches), and the fiber-sum
  invariance exhaustively over ALL vanishing subset sums at `n = 12` (100/100) and
  `n = 18` (1000/1000), at both primes, with non-vanishing controls all violating.

What remains for full de Bruijn (named, not claimed): (1) discharging the packet
minimal-polynomial hypothesis over `K = ℚ(ζ_{p^a})` (cyclotomic irreducibility over a
coprime cyclotomic extension, via `φ(p^a q^b) = φ(p^a)·φ(q^b)` and the tower formula);
(2) the exponent bijection `μ_{p^a} × μ_{q^b} ≃ μ_n` converting subset sums of `μ_n`
into double sums over the grid; (3) the positivity step (indicator fiber sums force
DISJOINT rotated packets) — the genuinely de Bruijn part.
-/

namespace CRTDoubleSlice

open Polynomial Finset

/-- **Packet slice lemma over any semiring** (the O66 engine, coefficients
generalized from `ℚ`): if `deg R < q` then
`((Σ_{t<p} X^(t·q)) · R).coeff (i·q + s) = R.coeff s` for `i < p`, `s < q`. -/
lemma packet_slice_coeff {K : Type*} [Semiring K] {p q : ℕ} {R : K[X]}
    (hR : R.natDegree < q) {i s : ℕ} (hi : i < p) (hs : s < q) :
    ((∑ t ∈ Finset.range p, (Polynomial.X : K[X]) ^ (t * q)) * R).coeff (i * q + s)
      = R.coeff s := by
  rw [Finset.sum_mul, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single i]
  · rw [show i * q + s = s + i * q from by ring, Polynomial.coeff_X_pow_mul]
  · intro j hj hji
    rw [Polynomial.coeff_X_pow_mul']
    rcases lt_or_ge (i * q + s) (j * q) with hlt | hge
    · rw [if_neg (by omega)]
    · rw [if_pos hge]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rcases lt_or_ge j i with hji' | hji'
      · have : i * q + s - j * q ≥ q := by
          have h1 : (j + 1) * q ≤ i * q := Nat.mul_le_mul_right q (by omega)
          have h2 : j * q + q ≤ i * q := by
            calc j * q + q = (j + 1) * q := by ring
            _ ≤ i * q := h1
          omega
        omega
      · have hj1 : i + 1 ≤ j := by omega
        have : i * q + q ≤ j * q := by
          calc i * q + q = (i + 1) * q := by ring
          _ ≤ j * q := Nat.mul_le_mul_right q hj1
        omega
  · intro hnotin
    exact absurd (Finset.mem_range.mpr hi) hnotin

/-- **The weighted slice engine over an arbitrary base field** — the CRT-ready form of
O66's `vanishing_sum_mu_p_closed`. If the minimal polynomial of `η` over `K` is the
geometric packet `Σ_{t<p} X^(t·q)`, then the coefficients of ANY vanishing `K`-weighted
combination of `1, η, …, η^(pq−1)` are invariant under exponent shifts by `q`:
`a (i·q + s) = a (i'·q + s)` for all `i, i' < p`, `s < q`.

Instantiating `K = ℚ` recovers (and strengthens to arbitrary weights) the O66 prime-power
Lam–Leung closure; instantiating `K = ℚ(ζ_{p^a})` (once the packet minimal-polynomial
hypothesis is discharged there) is the two-prime de Bruijn step. -/
theorem slice_of_packet_minpoly {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p q : ℕ} {η : L}
    (hmin : minpoly K η = ∑ t ∈ Finset.range p, (X : K[X]) ^ (t * q))
    {a : ℕ → K}
    (hsum : ∑ e ∈ Finset.range (p * q), a e • η ^ e = 0)
    {i i' s : ℕ} (hi : i < p) (hi' : i' < p) (hs : s < q) :
    a (i * q + s) = a (i' * q + s) := by
  classical
  have hppos : 0 < p := by omega
  have hqpos : 0 < q := by omega
  set n := p * q with hn
  set P : K[X] := ∑ e ∈ Finset.range n, C (a e) * X ^ e with hP
  have hPcoeff : ∀ j, P.coeff j = if j ∈ Finset.range n then a j else 0 := by
    intro j
    rw [hP, Polynomial.finset_sum_coeff]
    rw [Finset.sum_congr rfl fun e _ => by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]]
    exact Finset.sum_ite_eq (Finset.range n) j a
  have hPη : Polynomial.aeval η P = 0 := by
    rw [hP, map_sum]
    rw [Finset.sum_congr rfl fun e _ => by
      rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, ← Algebra.smul_def]]
    exact hsum
  have hdvd : (∑ t ∈ Finset.range p, (X : K[X]) ^ (t * q)) ∣ P := by
    rw [← hmin]
    exact minpoly.dvd K η hPη
  -- bounds on the two slice positions
  have hb1 : i * q + s < n := by
    have h' : (i + 1) * q ≤ p * q := Nat.mul_le_mul_right q (by omega)
    have : i * q + q ≤ p * q := by
      calc i * q + q = (i + 1) * q := by ring
      _ ≤ p * q := h'
    omega
  have hb2 : i' * q + s < n := by
    have h' : (i' + 1) * q ≤ p * q := Nat.mul_le_mul_right q (by omega)
    have : i' * q + q ≤ p * q := by
      calc i' * q + q = (i' + 1) * q := by ring
      _ ≤ p * q := h'
    omega
  by_cases hP0 : P = 0
  · have h1 := hPcoeff (i * q + s)
    have h2 := hPcoeff (i' * q + s)
    simp only [hP0, Polynomial.coeff_zero] at h1 h2
    rw [if_pos (Finset.mem_range.mpr hb1)] at h1
    rw [if_pos (Finset.mem_range.mpr hb2)] at h2
    rw [← h1, ← h2]
  obtain ⟨R, hR⟩ := hdvd
  have hG : (∑ t ∈ Finset.range p, (X : K[X]) ^ (t * q)) ≠ 0 := by
    intro h
    have := congrArg (fun Q : K[X] => Q.coeff 0) h
    simp only [Polynomial.finset_sum_coeff] at this
    rw [Finset.sum_eq_single 0 (fun j _ hj => by
      rw [Polynomial.coeff_X_pow]
      rw [if_neg (by
        intro h0
        rcases Nat.mul_eq_zero.mp h0.symm with h | h
        · exact hj h
        · omega)]) (fun h0 => absurd (Finset.mem_range.mpr hppos) h0)] at this
    simp at this
  have hR0 : R ≠ 0 := fun h => hP0 (by rw [hR, h, mul_zero])
  have hdegP : P.natDegree < n := by
    rw [hP]
    have hle : (∑ e ∈ Finset.range n, C (a e) * X ^ e).natDegree ≤ n - 1 :=
      Polynomial.natDegree_sum_le_of_forall_le _ _ fun e he => by
        refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        rw [Polynomial.natDegree_X_pow]
        have := Finset.mem_range.mp he
        omega
    have hnpos : 0 < n := by rw [hn]; positivity
    omega
  have hdegR : R.natDegree < q := by
    have hmul := Polynomial.natDegree_mul hG hR0
    rw [← hR] at hmul
    have hGlow : (p - 1) * q ≤ (∑ t ∈ Finset.range p, (X : K[X]) ^ (t * q)).natDegree := by
      apply Polynomial.le_natDegree_of_ne_zero
      rw [Polynomial.finset_sum_coeff]
      rw [Finset.sum_eq_single (p - 1) (fun j hj hjne => by
        rw [Polynomial.coeff_X_pow, if_neg (fun h => hjne (by
          have := Nat.eq_of_mul_eq_mul_right hqpos h
          omega))]) (fun h0 => absurd (Finset.mem_range.mpr (by omega)) h0)]
      rw [Polynomial.coeff_X_pow, if_pos rfl]
      norm_num
    have hcount : (p - 1) * q + q = n := by
      rw [hn]
      calc (p - 1) * q + q = ((p - 1) + 1) * q := by ring
      _ = p * q := by congr 1; omega
    omega
  have e1 : P.coeff (i * q + s) = R.coeff s := by
    rw [hR]
    exact packet_slice_coeff hdegR hi hs
  have e2 : P.coeff (i' * q + s) = R.coeff s := by
    rw [hR]
    exact packet_slice_coeff hdegR hi' hs
  have h1 := hPcoeff (i * q + s)
  have h2 := hPcoeff (i' * q + s)
  rw [if_pos (Finset.mem_range.mpr hb1)] at h1
  rw [if_pos (Finset.mem_range.mpr hb2)] at h2
  rw [← h1, ← h2, e1, e2]

/-- **Rational-weighted Lam–Leung slices at prime powers**: in characteristic zero, any
vanishing ℚ-weighted sum of `p^(m+1)`-th roots of unity has μ_p-shift invariant
coefficient slices. The O66 indicator theorem (`vanishing_sum_mu_p_closed`) is the
`a ∈ {0,1}` special case; this is the full linear statement. -/
theorem weighted_vanishing_slice_rat {F : Type*} [Field F] [CharZero F]
    {p m : ℕ} (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ (m + 1)))
    {a : ℕ → ℚ}
    (hsum : ∑ e ∈ Finset.range (p ^ (m + 1)), a e • ζ ^ e = 0)
    {i i' s : ℕ} (hi : i < p) (hi' : i' < p) (hs : s < p ^ m) :
    a (i * p ^ m + s) = a (i' * p ^ m + s) := by
  have hmin : minpoly ℚ ζ = ∑ t ∈ Finset.range p, (X : ℚ[X]) ^ (t * p ^ m) := by
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ (pow_pos hp.pos _),
        Polynomial.cyclotomic_prime_pow_eq_geom_sum hp]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_comm t (p ^ m), pow_mul]
  have hpow : p * p ^ m = p ^ (m + 1) := by ring
  refine slice_of_packet_minpoly hmin ?_ hi hi' hs
  rw [hpow]
  exact hsum

/-- **The CRT double-slice, fiber-sum form** (the de Bruijn route's per-prime half,
assembled): let `I` be a set of CRT exponent pairs `(j, c)` inside the coprime grid
`range Pn × range (q·Q')`, `ξ ∈ K` the base-field root coordinate, and `η` with packet
minimal polynomial over `K`. If the double sum `Σ_{(j,c)∈I} ξ^j · η^c` vanishes, then
the `K`-valued fiber sums `A(c) = Σ_{(j,c)∈I} ξ^j` are invariant under μ_q-shifts of
the `η`-coordinate: `A(i·Q' + s) = A(i'·Q' + s)` for `i, i' < q`, `s < Q'`.

For a vanishing subset sum of `μ_n` (`n = p^a·q^b`, `Pn = p^a`, `Q' = q^{b-1}`) in CRT
coordinates this says: the `ℤ[ζ_{p^a}]`-valued fiber sums over the `q`-side are constant
on μ_q-cosets — the exact statement verified exhaustively by the probe at `n = 12, 18`. -/
theorem crt_fiber_slice {K L : Type*} [Field K] [Field L] [Algebra K L]
    {q Q' : ℕ} {η : L}
    (hmin : minpoly K η = ∑ t ∈ Finset.range q, (X : K[X]) ^ (t * Q'))
    {Pn : ℕ} (ξ : K) (I : Finset (ℕ × ℕ))
    (hI : I ⊆ Finset.range Pn ×ˢ Finset.range (q * Q'))
    (hsum : ∑ x ∈ I, (algebraMap K L ξ) ^ x.1 * η ^ x.2 = 0)
    {i i' s : ℕ} (hi : i < q) (hi' : i' < q) (hs : s < Q') :
    (∑ j ∈ Finset.range Pn, if (j, i * Q' + s) ∈ I then ξ ^ j else 0)
      = ∑ j ∈ Finset.range Pn, if (j, i' * Q' + s) ∈ I then ξ ^ j else 0 := by
  classical
  set A : ℕ → K := fun c => ∑ j ∈ Finset.range Pn, if (j, c) ∈ I then ξ ^ j else 0 with hA
  have hsum' : ∑ c ∈ Finset.range (q * Q'), A c • η ^ c = 0 := by
    have step1 : ∑ c ∈ Finset.range (q * Q'), A c • η ^ c
        = ∑ c ∈ Finset.range (q * Q'), ∑ j ∈ Finset.range Pn,
            (if (j, c) ∈ I then (algebraMap K L ξ) ^ j * η ^ c else 0) := by
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [hA]
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : (j, c) ∈ I
      · rw [if_pos h, if_pos h, Algebra.smul_def, map_pow]
      · rw [if_neg h, if_neg h, zero_smul]
    have step2 : ∑ x ∈ Finset.range Pn ×ˢ Finset.range (q * Q'),
        (if x ∈ I then (algebraMap K L ξ) ^ x.1 * η ^ x.2 else 0)
        = ∑ j ∈ Finset.range Pn, ∑ c ∈ Finset.range (q * Q'),
            (if (j, c) ∈ I then (algebraMap K L ξ) ^ j * η ^ c else 0) := by
      rw [Finset.sum_product]
    rw [step1, Finset.sum_comm, ← step2, Finset.sum_ite_mem,
        Finset.inter_eq_right.mpr hI]
    exact hsum
  exact slice_of_packet_minpoly hmin hsum' hi hi' hs

/-- Non-vacuity witness: the hypotheses of `crt_fiber_slice` are jointly satisfiable —
`K = L = ℚ`, `η = −1` whose minimal polynomial is the `q = 2`, `Q' = 1` packet
`X^0 + X^1`, with the empty exponent set. -/
example : (∑ j ∈ Finset.range 1, if (j, 0 * 1 + 0) ∈ (∅ : Finset (ℕ × ℕ))
        then (1 : ℚ) ^ j else 0)
      = ∑ j ∈ Finset.range 1, if (j, 1 * 1 + 0) ∈ (∅ : Finset (ℕ × ℕ))
        then (1 : ℚ) ^ j else 0 :=
  crt_fiber_slice (q := 2) (Q' := 1) (η := (-1 : ℚ))
    (by
      rw [minpoly.eq_X_sub_C', Finset.sum_range_succ, Finset.sum_range_one]
      simp only [Nat.mul_one, pow_zero, pow_one, map_neg, map_one]
      ring)
    1 ∅ (Finset.empty_subset _) (by simp) (by norm_num) (by norm_num) (by norm_num)

end CRTDoubleSlice

#print axioms CRTDoubleSlice.packet_slice_coeff
#print axioms CRTDoubleSlice.slice_of_packet_minpoly
#print axioms CRTDoubleSlice.weighted_vanishing_slice_rat
#print axioms CRTDoubleSlice.crt_fiber_slice
