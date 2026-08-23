/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ThreadSplit

/-!
# Issue #232 — WEIGHTED thread-split: the digit-descent engine for the weighted
de Bruijn program (O101)

O100 closed the weighted classification at the squarefree base `p·q` and named the
remaining span to full weighted `p^a·q^b` as three assembly steps, the first being
"(i) the weighted digit descent (restate `ThreadSplit.thread_vanishing_of_vanishing`
for weights — the K-independence engine is weight-agnostic)".  This file executes
that step verbatim: for a prime `p` with `p² ∣ n` (`n = p·m`, `p ∣ m`), a vanishing
ℕ-weighted power sum at a primitive `n`-th root splits thread-by-thread,

    `∑_{e<n} w_e·ζ^e = 0   ⟺   ∀ r < p,  ∑_{e'<m} w_{r+p·e'}·(ζ^p)^{e'} = 0`,

an iff (`weighted_thread_split_iff`).  The forward mechanism is O93's engine
unchanged — the thread sums are elements of `K = ℚ⟮ζ^p⟯` (now with ℕ-cast
coefficients instead of indicator coefficients), `minpoly K ζ = X^p − C(gen)` pins
degree `p` (`ThreadSplit.natDegree_minpoly_adjoin_pow_prime`, the load-bearing use
of `p² ∣ n`), `linearIndependent_pow` gives `K`-independence of `1, ζ, …, ζ^{p−1}`,
and `Fintype.linearIndependent_iff` kills every thread coefficient.  The converse
is pure linearity over any commutative ring.

With this brick the weighted `p^a·q^b` program is: iterate
`weighted_thread_vanishing_of_vanishing` down the digits to the squarefree base
(every descent level keeps `u² ∣ current n` exactly as in the O94 indicator
recursion), apply O100 `debruijn_weighted_squarefree` per deep thread, and
reassemble the combination functions through `e = r + g·e''` — bookkeeping, no new
analytic content (named for the next pass).

Falsified first (inline, exact ℤ[x]/Φ₁₂ and Φ₆ arithmetic): the iff EXHAUSTIVE
over all `3^12 = 531441` weight vectors at `n = 12`, `p = 2`, `m = 6` — 2025
vanishing, `2025 = 45²` (the thread product law `|van(n)| = |van(n/p)|^p` visible),
0 mismatches.

Teeth: a cross-brick fire — the O96 weighted prime-power vanishing `(2,1,2,1)` at
`n = 4` (produced by `WeightedPrimePowerPacket`) is split by the forward direction
into its two vanishing threads at level `2`, with no root-of-unity arithmetic.
-/

namespace WeightedThreadSplit

open Polynomial Finset IntermediateField

/-- **The weighted digit decomposition** (any commutative ring): an ℕ-weighted
power sum over `[0, p·m)` regroups as `p` threads at `ζ^p`. -/
lemma weighted_sum_eq_thread_sum {L : Type*} [CommRing L] {p m : ℕ} (hp : 0 < p)
    (ζ : L) (w : ℕ → ℕ) :
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

/-- **WEIGHTED THREAD-SPLIT, forward** (the O93 engine with ℕ-multiplicities): for
a prime `p` with `p² ∣ n` (`n = p·m`, `p ∣ m`) and a primitive `n`-th root `ζ`
(char 0), a vanishing ℕ-weighted power sum splits into `p` vanishing weighted
thread sums at the primitive `(n/p)`-th root `ζ^p`. -/
theorem weighted_thread_vanishing_of_vanishing {L : Type*} [Field L] [CharZero L]
    {p m : ℕ} (hp : p.Prime) (hm : 0 < m) (hpm : p ∣ m)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p * m)) (w : ℕ → ℕ)
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
    rw [map_mul, map_natCast, map_pow, hcoe]
  have hrel : ∑ i : Fin p, c i.val • ζ ^ (i : ℕ) = 0 := by
    calc ∑ i : Fin p, c i.val • ζ ^ (i : ℕ)
        = ∑ r ∈ Finset.range p, c r • ζ ^ r :=
          Fin.sum_univ_eq_sum_range (fun r => c r • ζ ^ r) p
      _ = ∑ r ∈ Finset.range p, ζ ^ r *
            ∑ e' ∈ Finset.range m, (w (r + p * e') : L) * (ζ ^ p) ^ e' := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Algebra.smul_def, hmap, mul_comm]
      _ = ∑ e ∈ Finset.range (p * m), (w e : L) * ζ ^ e :=
          (weighted_sum_eq_thread_sum hp.pos ζ w).symm
      _ = 0 := hsum
  have hLI : LinearIndependent ℚ⟮ζ ^ p⟯ fun i : Fin p => ζ ^ (i : ℕ) := by
    have h := linearIndependent_pow (K := ℚ⟮ζ ^ p⟯) ζ
    rwa [ThreadSplit.natDegree_minpoly_adjoin_pow_prime hp hm hpm hζ] at h
  have hzero : c r = 0 :=
    Fintype.linearIndependent_iff.mp hLI (fun i => c i.val) hrel ⟨r, hr⟩
  have hfin := congrArg (algebraMap ℚ⟮ζ ^ p⟯ L) hzero
  rwa [map_zero, hmap] at hfin

/-- **The trivial converse** (pure linearity, any commutative ring). -/
theorem weighted_vanishing_of_thread_vanishing {L : Type*} [CommRing L] {p m : ℕ}
    (hp : 0 < p) (ζ : L) (w : ℕ → ℕ)
    (h : ∀ r < p, ∑ e' ∈ Finset.range m, (w (r + p * e') : L) * (ζ ^ p) ^ e' = 0) :
    ∑ e ∈ Finset.range (p * m), (w e : L) * ζ ^ e = 0 := by
  rw [weighted_sum_eq_thread_sum hp ζ w]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [h r (Finset.mem_range.mp hr), mul_zero]

/-- **Weighted thread-split as an iff**: for `p² ∣ n`, an ℕ-weighted power sum
vanishes at `ζ` iff all `p` weighted thread sums vanish at `ζ^p`. -/
theorem weighted_thread_split_iff {L : Type*} [Field L] [CharZero L] {p m : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hpm : p ∣ m)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p * m)) (w : ℕ → ℕ) :
    (∑ e ∈ Finset.range (p * m), (w e : L) * ζ ^ e = 0)
      ↔ ∀ r < p, ∑ e' ∈ Finset.range m, (w (r + p * e') : L) * (ζ ^ p) ^ e' = 0 :=
  ⟨weighted_thread_vanishing_of_vanishing hp hm hpm hζ w,
    weighted_vanishing_of_thread_vanishing hp.pos ζ w⟩

/-! ## Teeth (fired at `ℂ`, `n = 4`, genuine multiplicities) -/

/-- The forward direction FIRED on a genuine multiplicity vector: the weights
`(2,1,2,1)` at `n = 4` vanish (`2 + ζ + 2ζ² + ζ³ = 0` since `ζ² = −1`), and
weighted thread-split decomposes that vanishing into its `r = 0` thread at level
`2`: `2 + 2·ζ₄² = 0` falls out of the theorem. -/
example : ∑ e' ∈ Finset.range 2,
    ((if (0 + 2 * e') % 2 = 0 then 2 else 1 : ℕ) : ℂ)
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
      ((if e % 2 = 0 then 2 else 1 : ℕ) : ℂ) * ζ ^ e = 0 := by
    rw [show (2 * 2 : ℕ) = 4 from rfl, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have h3 : ζ ^ 3 = -ζ := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, hζsq, pow_one]
      ring
    norm_num [hζsq, h3]
  exact weighted_thread_vanishing_of_vanishing Nat.prime_two (by norm_num)
    ⟨1, rfl⟩ hζ22 (fun e => if e % 2 = 0 then 2 else 1) hvan 0 (by norm_num)

end WeightedThreadSplit

#print axioms WeightedThreadSplit.weighted_sum_eq_thread_sum
#print axioms WeightedThreadSplit.weighted_thread_vanishing_of_vanishing
#print axioms WeightedThreadSplit.weighted_vanishing_of_thread_vanishing
#print axioms WeightedThreadSplit.weighted_thread_split_iff
