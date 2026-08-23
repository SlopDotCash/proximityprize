/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWeightedTwoPrime

/-!
# Issue #232 — the general-arity packet combination ALWAYS vanishes (O109a)

The general-`k` classification of vanishing ℚ-weighted sums (the arity induction
of the O107 pattern) has two halves.  This file proves the easy half at FULL
generality — every modulus `n`, every weight ring, no squarefree hypothesis:

    `w e = Σ_{p ∈ primeFactors n} A p (e % (n/p))   ⟹   Σ_{e<n} w_e·ζ^e = 0`

— a sum of prime-fiber components (each constant along its own `μ_p`-packet
direction) always kills the power sum: every component factors its prime's full
geometric sum (`DeBruijnWeightedTwoPrime.packet_part_eq_zero`, already
modulus-general).

The HARD half (the converse — vanishing ⟹ such components exist, ℚ-valued, at
squarefree `n`) is the arity induction whose `k = 2` case is O102 and `k = 3`
case is O107; its full peel design (minFac peel through the O106 gate at base
`m = n/p`, fiber differences to the inductive level, component decode
`A_q(y) := B^{y%p}_q(y % (m/q))`) is recorded in the DISPROOF_LOG O109 entry —
gated, not claimed.
-/

namespace GeneralPacketCombination

open Finset

variable {L : Type*} [Field L] [CharZero L]

omit [CharZero L] in
/-- **General packet combinations vanish** (every modulus, every arity): if the
weight function is a sum over the prime divisors of `n` of fiber components
`A p (e % (n/p))`, the weighted power sum at any primitive `n`-th root is zero —
each component carries its prime's full geometric sum. -/
theorem packet_combination_vanishes {n : ℕ} (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (A : ℕ → ℕ → ℕ)
    (w : ℕ → ℕ)
    (hw : ∀ e < n, w e = ∑ p ∈ n.primeFactors, A p (e % (n / p))) :
    ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0 := by
  have hstep : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e
      = ∑ p ∈ n.primeFactors, ∑ e ∈ Finset.range n,
          (A p (e % (n / p)) : L) * ζ ^ e := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hw e (Finset.mem_range.mp he), Nat.cast_sum, Finset.sum_mul]
  rw [hstep]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  exact DeBruijnWeightedTwoPrime.packet_part_eq_zero hpp.one_lt hpn hn hζ
    (A p)

/-- The ℚ-weighted form (the shape of the open forward direction's converse). -/
theorem rat_packet_combination_vanishes {n : ℕ} (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (A : ℕ → ℕ → ℚ)
    (w : ℕ → ℚ)
    (hw : ∀ e < n, w e = ∑ p ∈ n.primeFactors, A p (e % (n / p))) :
    ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0 := by
  have hstep : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e
      = ∑ p ∈ n.primeFactors, ∑ e ∈ Finset.range n,
          (A p (e % (n / p)) : L) * ζ ^ e := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hw e (Finset.mem_range.mp he), Rat.cast_sum, Finset.sum_mul]
  rw [hstep]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  -- the ℚ-coefficient packet death: regroup along the `p`-packet direction
  have hk : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hpp.pos
  have hsplit : (n / p) * p = n := Nat.div_mul_cancel hpn
  rw [show Finset.range n = Finset.range ((n / p) * p) from by rw [hsplit]]
  have hregroup : ∑ e ∈ Finset.range ((n / p) * p),
      (A p (e % (n / p)) : L) * ζ ^ e
      = ∑ r ∈ Finset.range (n / p), ζ ^ r *
          ∑ e' ∈ Finset.range p, (A p ((r + (n / p) * e') % (n / p)) : L)
            * (ζ ^ (n / p)) ^ e' := by
    calc ∑ e ∈ Finset.range ((n / p) * p), (A p (e % (n / p)) : L) * ζ ^ e
        = ∑ x ∈ Finset.range (n / p) ×ˢ Finset.range p,
            (A p ((x.1 + (n / p) * x.2) % (n / p)) : L)
              * ζ ^ (x.1 + (n / p) * x.2) := by
          refine (Finset.sum_nbij' (fun x : ℕ × ℕ => x.1 + (n / p) * x.2)
            (fun e => (e % (n / p), e / (n / p))) ?_ ?_ ?_ ?_ ?_).symm
          · rintro ⟨r, c⟩ hx
            rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
            rw [Finset.mem_range]
            calc r + (n / p) * c < (n / p) + (n / p) * c := by omega
              _ = (n / p) * (c + 1) := by ring
              _ ≤ (n / p) * p := Nat.mul_le_mul_left _ (by omega)
          · intro e he
            rw [Finset.mem_range] at he
            rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
            refine ⟨Nat.mod_lt _ hk, ?_⟩
            rw [Nat.div_lt_iff_lt_mul hk, Nat.mul_comm p (n / p)]
            exact he
          · rintro ⟨r, c⟩ hx
            rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
            have h1 : (r + (n / p) * c) % (n / p) = r := by
              rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx.1]
            have h2 : (r + (n / p) * c) / (n / p) = c := by
              rw [Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hx.1,
                Nat.zero_add]
            exact Prod.ext h1 h2
          · intro e _
            exact Nat.mod_add_div e (n / p)
          · rintro ⟨r, c⟩ _
            rfl
      _ = ∑ r ∈ Finset.range (n / p), ∑ e' ∈ Finset.range p,
            (A p ((r + (n / p) * e') % (n / p)) : L)
              * ζ ^ (r + (n / p) * e') := Finset.sum_product _ _ _
      _ = ∑ r ∈ Finset.range (n / p), ζ ^ r *
            ∑ e' ∈ Finset.range p, (A p ((r + (n / p) * e') % (n / p)) : L)
              * (ζ ^ (n / p)) ^ e' := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun e' _ => ?_
          rw [pow_add, pow_mul]
          ring
  rw [hregroup]
  refine Finset.sum_eq_zero fun r hr => ?_
  have hconst : ∀ e' ∈ Finset.range p,
      (A p ((r + (n / p) * e') % (n / p)) : L) * (ζ ^ (n / p)) ^ e'
        = (A p r : L) * (ζ ^ (n / p)) ^ e' := by
    intro e' _
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
  rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum,
    (hζ.pow hn hsplit.symm).geom_sum_eq_zero hpp.one_lt, mul_zero, mul_zero]

end GeneralPacketCombination

#print axioms GeneralPacketCombination.packet_combination_vanishes
#print axioms GeneralPacketCombination.rat_packet_combination_vanishes
