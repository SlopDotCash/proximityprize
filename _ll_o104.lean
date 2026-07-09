/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWeightedTwoPrime

/-!
# Issue #232 — LAM–LEUNG'S ℕ-SPAN THEOREM at two-prime moduli (O104)

The post-O103 residue named "the Lam–Leung ℕ-span theorem" as the honest target
of the span program (it is the form that survives past two primes, where de
Bruijn's packet conjecture fails).  At two-prime moduli it is now a COROLLARY of
O103: this file derives it.

    `∑_{e<n} w_e·ζ^e = 0   ⟹   ∑_e w_e ∈ ℕ·p + ℕ·q`     (`n = p^a·q^b`)

— the total weight of any vanishing ℕ-combination of `n`-th roots of unity is a
nonnegative combination of the two primes (Lam–Leung, J. Algebra 224 (2000),
Thm 4.1 specialized to two primes; the indicator case is O95
`vanishing_card_two_prime`).

Mechanism: O103 gives `w e = A (e % (n/p)) + B (e % (n/q))`; the fiber-counting
identity `∑_{e<m·u} f(e % m) = u·∑_{s<m} f s` (each packet base is hit exactly
`u` times) is extracted from O101 `weighted_sum_eq_thread_sum` at `ζ = 1` over ℚ
and cast back to ℕ — no new summation machinery.
-/

namespace LamLeungSpanTwoPrime

open Finset

/-- **The fiber-counting identity**: summing `f (e % m)` over `[0, m·u)` counts
each residue exactly `u` times — O101's digit decomposition at `ζ = 1`. -/
lemma sum_mod_fiber (f : ℕ → ℕ) (m u : ℕ) (hm : 0 < m) :
    ∑ e ∈ Finset.range (m * u), f (e % m) = u * ∑ s ∈ Finset.range m, f s := by
  have h := WeightedThreadSplit.weighted_sum_eq_thread_sum (L := ℚ) (p := m) (m := u) hm 1
    (fun e => f (e % m))
  simp only [one_pow, mul_one, one_mul] at h
  have hconst : ∀ r ∈ Finset.range m,
      ∑ e' ∈ Finset.range u, ((f ((r + m * e') % m) : ℚ))
        = (u : ℚ) * (f r : ℚ) := by
    intro r hr
    have hterm : ∀ e' ∈ Finset.range u,
        ((f ((r + m * e') % m) : ℚ)) = (f r : ℚ) := by
      intro e' _
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum] at h
  have hcast : ((∑ e ∈ Finset.range (m * u), f (e % m) : ℕ) : ℚ)
      = ((u * ∑ s ∈ Finset.range m, f s : ℕ) : ℚ) := by
    push_cast
    exact h
  exact_mod_cast hcast

/-- **LAM–LEUNG ℕ-SPAN AT TWO-PRIME MODULI** (the weighted form, O103 corollary):
the total weight of a vanishing ℕ-weighted sum of `p^a·q^b`-th roots of unity
lies in `ℕ·p + ℕ·q`. -/
theorem lam_leung_span_two_prime {L : Type*} [Field L] [CharZero L]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha : 0 < a) (hb : 0 < b)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b)) (w : ℕ → ℕ)
    (hvan : ∑ e ∈ Finset.range (p ^ a * q ^ b), (w e : L) * ζ ^ e = 0) :
    ∃ cA cB : ℕ, ∑ e ∈ Finset.range (p ^ a * q ^ b), w e = p * cA + q * cB := by
  obtain ⟨A, B, hAB⟩ :=
    (DeBruijnWeightedTwoPrime.debruijn_weighted_two_prime hp hq hpq ha hb hζ
      w).mp hvan
  have hmp : 0 < p ^ (a - 1) * q ^ b :=
    Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)
  have hmq : 0 < p ^ a * q ^ (b - 1) :=
    Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)
  -- the two factorizations of `n` along its packet directions
  have hfacp : (p ^ (a - 1) * q ^ b) * p = p ^ a * q ^ b := by
    have h2 : p * p ^ (a - 1) = p ^ a := by
      rw [← pow_succ']
      congr 1
      omega
    rw [← h2]
    ring
  have hfacq : (p ^ a * q ^ (b - 1)) * q = p ^ a * q ^ b := by
    have h2 : q * q ^ (b - 1) = q ^ b := by
      rw [← pow_succ']
      congr 1
      omega
    rw [← h2]
    ring
  refine ⟨∑ s ∈ Finset.range (p ^ (a - 1) * q ^ b), A s,
    ∑ s ∈ Finset.range (p ^ a * q ^ (b - 1)), B s, ?_⟩
  have hsplit : ∑ e ∈ Finset.range (p ^ a * q ^ b), w e
      = (∑ e ∈ Finset.range (p ^ a * q ^ b), A (e % (p ^ (a - 1) * q ^ b)))
        + ∑ e ∈ Finset.range (p ^ a * q ^ b), B (e % (p ^ a * q ^ (b - 1))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e he => hAB e (Finset.mem_range.mp he)
  have hA : ∑ e ∈ Finset.range (p ^ a * q ^ b), A (e % (p ^ (a - 1) * q ^ b))
      = p * ∑ s ∈ Finset.range (p ^ (a - 1) * q ^ b), A s := by
    rw [show Finset.range (p ^ a * q ^ b)
        = Finset.range ((p ^ (a - 1) * q ^ b) * p) from by rw [hfacp]]
    exact sum_mod_fiber A _ p hmp
  have hB : ∑ e ∈ Finset.range (p ^ a * q ^ b), B (e % (p ^ a * q ^ (b - 1)))
      = q * ∑ s ∈ Finset.range (p ^ a * q ^ (b - 1)), B s := by
    rw [show Finset.range (p ^ a * q ^ b)
        = Finset.range ((p ^ a * q ^ (b - 1)) * q) from by rw [hfacq]]
    exact sum_mod_fiber B _ q hmq
  rw [hsplit, hA, hB]

end LamLeungSpanTwoPrime

#print axioms LamLeungSpanTwoPrime.sum_mod_fiber
#print axioms LamLeungSpanTwoPrime.lam_leung_span_two_prime
