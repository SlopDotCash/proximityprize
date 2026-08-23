/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ThreadSplit

/-!
# Issue #232 — ℤ-coefficient thread-split: the digit-descent engine with signs

The weighted (ℕ-coefficient) thread-split `WeightedThreadSplit.weighted_thread_split_iff`
(O101) is the digit-descent engine of the weighted de Bruijn program.  Its proof — the
minpoly degree pinch `natDegree (minpoly ℚ⟮ζ^p⟯ ζ) = p` (the load-bearing `p² ∣ n`)
plus `K`-linear independence of `1, ζ, …, ζ^{p−1}` — is coefficient-agnostic.  This file
exports the ℤ-coefficient version verbatim: for a prime `p` with `p² ∣ n` (`n = p·m`,
`p ∣ m`), a primitive `n`-th root `ζ` (char 0), and `w : ℕ → ℤ`,

    `∑_{e<n} w_e·ζ^e = 0   ⟺   ∀ r < p,  ∑_{e'<m} w_{r+p·e'}·(ζ^p)^{e'} = 0`

(`int_thread_split_iff`).  The ℤ form is the descent engine the three-plus-prime
program needs: past two primes the ℕ-classification fails (O105) and the surviving
structure (the ℤ-grid law, `DeBruijnThreePrimeIntGrid`) is genuinely signed, so its
digit descent must carry signs as well.

The proof is the O101 proof with `Int.cast` in place of `Nat.cast` (`map_intCast` in
place of `map_natCast`); the converse is pure linearity over any commutative ring.

Teeth: a genuinely SIGNED vanishing — the alternating weights `w_e = (−1)^e` at
`n = 4` vanish (`1 − ζ + ζ² − ζ³ = 0` since `ζ² = −1`), and the forward direction
splits the vanishing into its `r = 0` thread `1 + ζ₄² = 0` at level `2`.  No ℕ-weight
reaches this vector.
-/

namespace IntegerThreadSplit

open Polynomial Finset IntermediateField

/-- **The ℤ-weighted digit decomposition** (any commutative ring): a ℤ-weighted
power sum over `[0, p·m)` regroups as `p` threads at `ζ^p`. -/
lemma int_sum_eq_thread_sum {L : Type*} [CommRing L] {p m : ℕ} (hp : 0 < p)
    (ζ : L) (w : ℕ → ℤ) :
    ∑ e ∈ Finset.range (p * m), (w e : L) * ζ ^ e
      = ∑ r ∈ Finset.range p,
          ζ ^ r * ∑ e' ∈ Finset.range m, (w (r + p * e') : L) * (ζ ^ p) ^ e' := by
  classical
  calc ∑ e ∈ Finset.range (p * m), (w e : L) * ζ ^ e
      = ∑ x ∈ Finset.range p ×ˢ Finset.range m,
          (w (x.1 + p * x.2) : L) * ζ ^ (x.1 + p * x.2) := by
        refine (Finset.sum_nbij' (fun x : ℕ × ℕ => x.1 + p * x.2)
          (fun e => (e % p, e / p)) ?_ ?_ ?_ ?_ ?_).symm
        · rintro ⟨r, c⟩ hx
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
          rw [Finset.mem_range]
          calc r + p * c < p + p * c := by omega
            _ = p * (c + 1) := by ring
            _ ≤ p * m := Nat.mul_le_mul_left p (by omega)
        · intro e he
          rw [Finset.mem_range] at he
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
          refine ⟨Nat.mod_lt _ hp, ?_⟩
          rw [Nat.div_lt_iff_lt_mul hp, Nat.mul_comm m p]
          exact he
        · rintro ⟨r, c⟩ hx
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
          have h1 : (r + p * c) % p = r := by
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx.1]
          have h2 : (r + p * c) / p = c := by
            rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx.1, Nat.zero_add]
          exact Prod.ext h1 h2
        · intro e _
          exact Nat.mod_add_div e p
        · rintro ⟨r, c⟩ _
          rfl
    _ = ∑ r ∈ Finset.range p, ∑ e' ∈ Finset.range m,
          (w (r + p * e') : L) * ζ ^ (r + p * e') := Finset.sum_product _ _ _
    _ = ∑ r ∈ Finset.range p,
          ζ ^ r * ∑ e' ∈ Finset.range m, (w (r + p * e') : L) * (ζ ^ p) ^ e' := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e' _ => ?_
        rw [pow_add, pow_mul]
        ring

/-- **ℤ THREAD-SPLIT, forward** (the O93/O101 engine with ℤ-multiplicities): for a
prime `p` with `p² ∣ n` (`n = p·m`, `p ∣ m`) and a primitive `n`-th root `ζ`
(char 0), a vanishing ℤ-weighted power sum splits into `p` vanishing ℤ-weighted
thread sums at the primitive `(n/p)`-th root `ζ^p`. -/
theorem int_thread_vanishing_of_vanishing {L : Type*} [Field L] [CharZero L]
    {p m : ℕ} (hp : p.Prime) (hm : 0 < m) (hpm : p ∣ m)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p * m)) (w : ℕ → ℤ)
    (hsum : ∑ e ∈ Finset.range (p * m), (w e : L) * ζ ^ e = 0) :
    ∀ r < p, ∑ e' ∈ Finset.range m, (w (r + p * e') : L) * (ζ ^ p) ^ e' = 0 := by
  classical
  intro r hr
  set g : ℚ⟮ζ ^ p⟯ := IntermediateField.AdjoinSimple.gen ℚ (ζ ^ p) with hg
  have hcoe : algebraMap ℚ⟮ζ ^ p⟯ L g = ζ ^ p :=
    IntermediateField.AdjoinSimple.algebraMap_gen ℚ (ζ ^ p)
  set c : ℕ → ℚ⟮ζ ^ p⟯ :=
    fun r => ∑ e' ∈ Finset.range m, (w (r + p * e') : ℚ⟮ζ ^ p⟯) * g ^ e' with hc
  have hmap : ∀ r : ℕ, algebraMap ℚ⟮ζ ^ p⟯ L (c r)
      = ∑ e' ∈ Finset.range m, (w (r + p * e') : L) * (ζ ^ p) ^ e' := by
    intro r
    rw [hc, map_sum]
    refine Finset.sum_congr rfl fun e' _ => ?_
    rw [map_mul, map_intCast, map_pow, hcoe]
  have hrel : ∑ i : Fin p, c i.val • ζ ^ (i : ℕ) = 0 := by
    calc ∑ i : Fin p, c i.val • ζ ^ (i : ℕ)
        = ∑ r ∈ Finset.range p, c r • ζ ^ r :=
          Fin.sum_univ_eq_sum_range (fun r => c r • ζ ^ r) p
      _ = ∑ r ∈ Finset.range p, ζ ^ r *
            ∑ e' ∈ Finset.range m, (w (r + p * e') : L) * (ζ ^ p) ^ e' := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Algebra.smul_def, hmap, mul_comm]
      _ = ∑ e ∈ Finset.range (p * m), (w e : L) * ζ ^ e :=
          (int_sum_eq_thread_sum hp.pos ζ w).symm
      _ = 0 := hsum
  have hLI : LinearIndependent ℚ⟮ζ ^ p⟯ fun i : Fin p => ζ ^ (i : ℕ) := by
    have h := linearIndependent_pow (K := ℚ⟮ζ ^ p⟯) ζ
    rwa [ThreadSplit.natDegree_minpoly_adjoin_pow_prime hp hm hpm hζ] at h
  have hzero : c r = 0 :=
    Fintype.linearIndependent_iff.mp hLI (fun i => c i.val) hrel ⟨r, hr⟩
  have hfin := congrArg (algebraMap ℚ⟮ζ ^ p⟯ L) hzero
  rwa [map_zero, hmap] at hfin

/-- **The trivial converse** (pure linearity, any commutative ring). -/
theorem int_vanishing_of_thread_vanishing {L : Type*} [CommRing L] {p m : ℕ}
    (hp : 0 < p) (ζ : L) (w : ℕ → ℤ)
    (h : ∀ r < p, ∑ e' ∈ Finset.range m, (w (r + p * e') : L) * (ζ ^ p) ^ e' = 0) :
    ∑ e ∈ Finset.range (p * m), (w e : L) * ζ ^ e = 0 := by
  rw [int_sum_eq_thread_sum hp ζ w]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [h r (Finset.mem_range.mp hr), mul_zero]

/-- **ℤ thread-split as an iff**: for `p² ∣ n`, a ℤ-weighted power sum vanishes at
`ζ` iff all `p` ℤ-weighted thread sums vanish at `ζ^p`. -/
theorem int_thread_split_iff {L : Type*} [Field L] [CharZero L] {p m : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hpm : p ∣ m)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p * m)) (w : ℕ → ℤ) :
    (∑ e ∈ Finset.range (p * m), (w e : L) * ζ ^ e = 0)
      ↔ ∀ r < p, ∑ e' ∈ Finset.range m, (w (r + p * e') : L) * (ζ ^ p) ^ e' = 0 :=
  ⟨int_thread_vanishing_of_vanishing hp hm hpm hζ w,
    int_vanishing_of_thread_vanishing hp.pos ζ w⟩

/-! ## Teeth (fired at `ℂ`, `n = 4`, genuinely SIGNED weights) -/

/-- The forward direction FIRED on a genuinely signed weight vector: the
alternating weights `w_e = (−1)^e` at `n = 4` vanish (`1 − ζ + ζ² − ζ³ = 0` since
`ζ² = −1`) — a vector no ℕ-weight reaches — and ℤ thread-split decomposes that
vanishing into its `r = 0` thread at level `2`: `1 + ζ₄² = 0` falls out of the
theorem. -/
example : ∑ e' ∈ Finset.range 2,
    ((if (0 + 2 * e') % 2 = 0 then 1 else -1 : ℤ) : ℂ)
      * (Complex.exp (2 * Real.pi * Complex.I / (4 : ℕ)) ^ 2) ^ e' = 0 := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (4 : ℕ)) with hζdef
  have hζ22 : IsPrimitiveRoot ζ (2 * 2) := by
    have h := Complex.isPrimitiveRoot_exp 4 (by norm_num)
    rw [hζdef]
    norm_num at h ⊢
    exact h
  have hζsq : ζ ^ 2 = -1 := by
    rw [hζdef, ← Complex.exp_nat_mul]
    rw [show ((2 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / ((4 : ℕ) : ℂ))
        = Real.pi * Complex.I from by push_cast; ring]
    exact Complex.exp_pi_mul_I
  have hvan : ∑ e ∈ Finset.range (2 * 2),
      ((if e % 2 = 0 then 1 else -1 : ℤ) : ℂ) * ζ ^ e = 0 := by
    rw [show (2 * 2 : ℕ) = 4 from rfl, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have h3 : ζ ^ 3 = -ζ := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, hζsq, pow_one]
      ring
    norm_num [hζsq, h3]
  exact int_thread_vanishing_of_vanishing Nat.prime_two (by norm_num)
    ⟨1, rfl⟩ hζ22 (fun e => if e % 2 = 0 then 1 else -1) hvan 0 (by norm_num)

end IntegerThreadSplit

#print axioms IntegerThreadSplit.int_sum_eq_thread_sum
#print axioms IntegerThreadSplit.int_thread_vanishing_of_vanishing
#print axioms IntegerThreadSplit.int_vanishing_of_thread_vanishing
#print axioms IntegerThreadSplit.int_thread_split_iff
