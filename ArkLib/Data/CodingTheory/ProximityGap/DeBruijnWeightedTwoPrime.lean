/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWeightedSquarefreeExp

/-!
# Issue #232 — DE BRUIJN 1953 WEIGHTED, TWO-PRIME CASE, IN FULL (O103)

The last named bookkeeping step of the weighted program executed: the descent
induction.  For `n = p^a·q^b` (`a, b ≥ 1`, `p ≠ q` primes), `ζ` a primitive
`n`-th root of unity in characteristic zero, and multiplicities `w : ℕ → ℕ`:

    `∑_{e<n} w_e·ζ^e = 0   ⟺   ∃ A B : ℕ → ℕ, ∀ e < n,
        w e = A (e % (n/p)) + B (e % (n/q))`

— **de Bruijn's 1953 theorem with ℕ-multiplicities at every two-prime modulus**:
every vanishing nonnegative-integer combination of `n`-th roots of unity is an
ℕ-combination of rotated full `μ_p`- and `μ_q`-packets (`e % (n/p)` is the base of
`e`'s `μ_p`-packet, `e % (n/q)` of its `μ_q`-packet), and conversely.

Assembly (the O94 recursion shape, now with weights — no new analytic content):
* descent: O101 `weighted_thread_vanishing_of_vanishing` strips the low digit
  (`u ∈ {p, q}`, `u² ∣` current level, exactly as in the indicator recursion);
* base: O102 `debruijn_weighted_squarefree_exp` at `p·q`;
* reassembly: the combination functions lift uniformly through `e = r + u·e'` by
  `A(s) := A_{s % u}(s / u)`, justified by the digit identities
  `(e % (u·k)) % u = e % u` and `(e % (u·k)) / u = (e / u) % k`;
* converse: each packet part dies along its own direction
  (`packet_part_eq_zero`, the O101 regrouping plus a full geometric sum) — valid
  at EVERY modulus `n` with `u ∣ n`, not just two-prime ones.

With O96 (prime powers), O100/O102 (squarefree base), O101 (descent engine) and
this file, the weighted two-prime de Bruijn program is CLOSED.  Past two primes
the ℕ-span theorem is genuinely open mathematics (Lam–Leung; de Bruijn's
conjecture is false there).
-/

namespace DeBruijnWeightedTwoPrime

open Polynomial Finset

variable {L : Type*} [Field L] [CharZero L]

/-- The two digit identities of the lift `e = r + u·e'`. -/
private lemma digit_mod {u k e : ℕ} :
    (e % (u * k)) % u = e % u ∧ (e % (u * k)) / u = (e / u) % k :=
  ⟨Nat.mod_mod_of_dvd e ⟨k, rfl⟩, Nat.mod_mul_right_div_self e u k⟩

omit [CharZero L] in
/-- **The generic converse**: an ℕ-combination supported on the `μ_u`-packet
direction kills the full power sum at any primitive `n`-th root with `u ∣ n` —
each packet carries a full geometric sum. -/
lemma packet_part_eq_zero {n u : ℕ} (hu : 1 < u) (hun : u ∣ n) (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (A : ℕ → ℕ) :
    ∑ e ∈ Finset.range n, (A (e % (n / u)) : L) * ζ ^ e = 0 := by
  have hk : 0 < n / u := Nat.div_pos (Nat.le_of_dvd hn hun) (by omega)
  have hsplit : (n / u) * u = n := Nat.div_mul_cancel hun
  rw [show Finset.range n = Finset.range ((n / u) * u) from by rw [hsplit]]
  rw [WeightedThreadSplit.weighted_sum_eq_thread_sum hk ζ (fun e => A (e % (n / u)))]
  refine Finset.sum_eq_zero fun r hr => ?_
  have hconst : ∀ e' ∈ Finset.range u,
      (A ((r + (n / u) * e') % (n / u)) : L) * (ζ ^ (n / u)) ^ e'
        = (A r : L) * (ζ ^ (n / u)) ^ e' := by
    intro e' _
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
  rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum,
    (hζ.pow hn hsplit.symm).geom_sum_eq_zero hu, mul_zero, mul_zero]

/-- **The forward descent induction**: a vanishing ℕ-weighted sum at
`n = p^a·q^b` is an ℕ-combination of full prime packets — O101 strips digits to
the O102 squarefree base, and the combination functions lift through
`A(s) := A_{s%u}(s/u)`. -/
theorem weighted_combination_of_vanishing {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    ∀ a, 0 < a → ∀ b, 0 < b → ∀ ζ : L, IsPrimitiveRoot ζ (p ^ a * q ^ b) →
      ∀ w : ℕ → ℕ, (∑ e ∈ Finset.range (p ^ a * q ^ b), (w e : L) * ζ ^ e = 0) →
      ∃ A B : ℕ → ℕ, ∀ e < p ^ a * q ^ b,
        w e = A (e % (p ^ (a - 1) * q ^ b)) + B (e % (p ^ a * q ^ (b - 1))) := by
  intro a
  induction a with
  | zero => exact fun h => absurd h (lt_irrefl 0)
  | succ a iha =>
    intro _ b
    induction b with
    | zero => exact fun h => absurd h (lt_irrefl 0)
    | succ b ihb =>
      intro _ ζ hζ w hsum
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · subst ha0
        rcases Nat.eq_zero_or_pos b with hb0 | hbpos
        · -- BASE: `n = p·q` — O102
          subst hb0
          have hn1 : p ^ (0 + 1) * q ^ (0 + 1) = p * q := by ring
          rw [hn1] at hζ hsum ⊢
          obtain ⟨A, B, hAB⟩ :=
            (DeBruijnWeightedSquarefreeExp.debruijn_weighted_squarefree_exp
              hp hq hpq hζ w).mp hsum
          refine ⟨A, B, fun e he => ?_⟩
          have h := hAB e he
          have h1 : p ^ (0 + 1 - 1) * q ^ (0 + 1) = q := by ring
          have h2 : p ^ (0 + 1) * q ^ (0 + 1 - 1) = p := by ring
          rw [h1, h2]
          exact h
        · -- DESCEND `q` (`a = 0`, `b ≥ 1`): `n = p·q^(b+1) = q·m`, `m = p·q^b`
          have hm : 0 < p ^ (0 + 1) * q ^ b :=
            Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)
          have hqm : q ∣ p ^ (0 + 1) * q ^ b :=
            dvd_mul_of_dvd_right (dvd_pow_self q hbpos.ne') _
          have hn_eq : p ^ (0 + 1) * q ^ (b + 1) = q * (p ^ (0 + 1) * q ^ b) := by
            ring
          rw [hn_eq] at hζ hsum
          have hth := WeightedThreadSplit.weighted_thread_vanishing_of_vanishing
            hq hm hqm hζ w hsum
          have hζq : IsPrimitiveRoot (ζ ^ q) (p ^ (0 + 1) * q ^ b) :=
            hζ.pow (Nat.mul_pos hq.pos hm) rfl
          have hthreads : ∀ r : ℕ, ∃ AB : (ℕ → ℕ) × (ℕ → ℕ), r < q →
              ∀ e' < p ^ (0 + 1) * q ^ b,
                w (r + q * e') = AB.1 (e' % (p ^ (0 + 1 - 1) * q ^ b))
                  + AB.2 (e' % (p ^ (0 + 1) * q ^ (b - 1))) := by
            intro r
            by_cases hr : r < q
            · obtain ⟨A, B, hAB⟩ := ihb hbpos (ζ ^ q) hζq (fun e' => w (r + q * e'))
                (hth r hr)
              exact ⟨(A, B), fun _ => hAB⟩
            · exact ⟨(fun _ => 0, fun _ => 0), fun h => absurd h hr⟩
          choose AB hAB using hthreads
          refine ⟨fun s => (AB (s % q)).1 (s / q), fun s => (AB (s % q)).2 (s / q),
            fun e he => ?_⟩
          have hep : e / q < p ^ (0 + 1) * q ^ b := by
            rw [Nat.div_lt_iff_lt_mul hq.pos]
            calc e < p ^ (0 + 1) * q ^ (b + 1) := he
              _ = p ^ (0 + 1) * q ^ b * q := by ring
          have hkey := hAB (e % q) (Nat.mod_lt _ hq.pos) (e / q) hep
          have hw : w (e % q + q * (e / q)) = w e := by rw [Nat.mod_add_div]
          rw [hw] at hkey
          -- transport the two indices through the digit identities
          have hidx1 : (e % (p ^ (0 + 1 - 1) * q ^ (b + 1))) % q = e % q ∧
              (e % (p ^ (0 + 1 - 1) * q ^ (b + 1))) / q
                = (e / q) % (p ^ (0 + 1 - 1) * q ^ b) := by
            have hform : p ^ (0 + 1 - 1) * q ^ (b + 1)
                = q * (p ^ (0 + 1 - 1) * q ^ b) := by ring
            rw [hform]
            exact digit_mod
          have hidx2 : (e % (p ^ (0 + 1) * q ^ (b + 1 - 1))) % q = e % q ∧
              (e % (p ^ (0 + 1) * q ^ (b + 1 - 1))) / q
                = (e / q) % (p ^ (0 + 1) * q ^ (b - 1)) := by
            have hform : p ^ (0 + 1) * q ^ (b + 1 - 1)
                = q * (p ^ (0 + 1) * q ^ (b - 1)) := by
              have : b + 1 - 1 = (b - 1) + 1 := by omega
              rw [this]
              ring
            rw [hform]
            exact digit_mod
          show w e = (AB ((e % (p ^ (0 + 1 - 1) * q ^ (b + 1))) % q)).1
              ((e % (p ^ (0 + 1 - 1) * q ^ (b + 1))) / q)
            + (AB ((e % (p ^ (0 + 1) * q ^ (b + 1 - 1))) % q)).2
              ((e % (p ^ (0 + 1) * q ^ (b + 1 - 1))) / q)
          rw [hidx1.1, hidx1.2, hidx2.1, hidx2.2]
          exact hkey
      · -- DESCEND `p` (`a ≥ 1`): `n = p^(a+1)·q^(b+1) = p·m`, `m = p^a·q^(b+1)`
        have hm : 0 < p ^ a * q ^ (b + 1) :=
          Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)
        have hpm : p ∣ p ^ a * q ^ (b + 1) :=
          dvd_mul_of_dvd_left (dvd_pow_self p hapos.ne') _
        have hn_eq : p ^ (a + 1) * q ^ (b + 1) = p * (p ^ a * q ^ (b + 1)) := by
          ring
        rw [hn_eq] at hζ hsum
        have hth := WeightedThreadSplit.weighted_thread_vanishing_of_vanishing
          hp hm hpm hζ w hsum
        have hζp : IsPrimitiveRoot (ζ ^ p) (p ^ a * q ^ (b + 1)) :=
          hζ.pow (Nat.mul_pos hp.pos hm) rfl
        have hthreads : ∀ r : ℕ, ∃ AB : (ℕ → ℕ) × (ℕ → ℕ), r < p →
            ∀ e' < p ^ a * q ^ (b + 1),
              w (r + p * e') = AB.1 (e' % (p ^ (a - 1) * q ^ (b + 1)))
                + AB.2 (e' % (p ^ a * q ^ (b + 1 - 1))) := by
          intro r
          by_cases hr : r < p
          · obtain ⟨A, B, hAB⟩ := iha hapos (b + 1) (Nat.succ_pos b) (ζ ^ p) hζp
              (fun e' => w (r + p * e')) (hth r hr)
            exact ⟨(A, B), fun _ => hAB⟩
          · exact ⟨(fun _ => 0, fun _ => 0), fun h => absurd h hr⟩
        choose AB hAB using hthreads
        refine ⟨fun s => (AB (s % p)).1 (s / p), fun s => (AB (s % p)).2 (s / p),
          fun e he => ?_⟩
        have hep : e / p < p ^ a * q ^ (b + 1) := by
          rw [Nat.div_lt_iff_lt_mul hp.pos]
          calc e < p ^ (a + 1) * q ^ (b + 1) := he
            _ = p ^ a * q ^ (b + 1) * p := by ring
        have hkey := hAB (e % p) (Nat.mod_lt _ hp.pos) (e / p) hep
        have hw : w (e % p + p * (e / p)) = w e := by rw [Nat.mod_add_div]
        rw [hw] at hkey
        have hidx1 : (e % (p ^ (a + 1 - 1) * q ^ (b + 1))) % p = e % p ∧
            (e % (p ^ (a + 1 - 1) * q ^ (b + 1))) / p
              = (e / p) % (p ^ (a - 1) * q ^ (b + 1)) := by
          have hform : p ^ (a + 1 - 1) * q ^ (b + 1)
              = p * (p ^ (a - 1) * q ^ (b + 1)) := by
            have h1 : a + 1 - 1 = (a - 1) + 1 := by omega
            rw [h1]
            ring
          rw [hform]
          exact digit_mod
        have hidx2 : (e % (p ^ (a + 1) * q ^ (b + 1 - 1))) % p = e % p ∧
            (e % (p ^ (a + 1) * q ^ (b + 1 - 1))) / p
              = (e / p) % (p ^ a * q ^ (b + 1 - 1)) := by
          have hform : p ^ (a + 1) * q ^ (b + 1 - 1)
              = p * (p ^ a * q ^ (b + 1 - 1)) := by ring
          rw [hform]
          exact digit_mod
        show w e = (AB ((e % (p ^ (a + 1 - 1) * q ^ (b + 1))) % p)).1
            ((e % (p ^ (a + 1 - 1) * q ^ (b + 1))) / p)
          + (AB ((e % (p ^ (a + 1) * q ^ (b + 1 - 1))) % p)).2
            ((e % (p ^ (a + 1) * q ^ (b + 1 - 1))) / p)
        rw [hidx1.1, hidx1.2, hidx2.1, hidx2.2]
        exact hkey

/-- **DE BRUIJN 1953, WEIGHTED TWO-PRIME CASE, the iff**: at `n = p^a·q^b`
(`a, b ≥ 1`, `p ≠ q` primes, char 0), an ℕ-weighted power sum vanishes **iff**
the weight function is an ℕ-combination of rotated full prime packets,
`w e = A (e % (n/p)) + B (e % (n/q))` in explicit exponent form. -/
theorem debruijn_weighted_two_prime {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (ha : 0 < a) (hb : 0 < b)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b)) (w : ℕ → ℕ) :
    (∑ e ∈ Finset.range (p ^ a * q ^ b), (w e : L) * ζ ^ e = 0) ↔
      ∃ A B : ℕ → ℕ, ∀ e < p ^ a * q ^ b,
        w e = A (e % (p ^ (a - 1) * q ^ b)) + B (e % (p ^ a * q ^ (b - 1))) := by
  have hnpos : 0 < p ^ a * q ^ b :=
    Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b)
  constructor
  · exact weighted_combination_of_vanishing hp hq hpq a ha b hb ζ hζ w
  · rintro ⟨A, B, hAB⟩
    have hdivp : (p ^ a * q ^ b) / p = p ^ (a - 1) * q ^ b := by
      have h2 : p * p ^ (a - 1) = p ^ a := by
        rw [← pow_succ']
        congr 1
        omega
      have hform : p ^ a * q ^ b = p * (p ^ (a - 1) * q ^ b) := by
        rw [← h2]
        ring
      rw [hform, Nat.mul_div_cancel_left _ hp.pos]
    have hdivq : (p ^ a * q ^ b) / q = p ^ a * q ^ (b - 1) := by
      have h2 : q * q ^ (b - 1) = q ^ b := by
        rw [← pow_succ']
        congr 1
        omega
      have hform : p ^ a * q ^ b = q * (p ^ a * q ^ (b - 1)) := by
        rw [← h2]
        ring
      rw [hform, Nat.mul_div_cancel_left _ hq.pos]
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
    have hA0 := packet_part_eq_zero hp.one_lt
      (dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') _) hnpos hζ A
    have hB0 := packet_part_eq_zero hq.one_lt
      (dvd_mul_of_dvd_right (dvd_pow_self q hb.ne') _) hnpos hζ B
    rw [hdivp] at hA0
    rw [hdivq] at hB0
    rw [hsplit, hA0, hB0, add_zero]

/-! ## Teeth (fired at `ℂ`, `n = 12 = 2²·3`, past the squarefree level) -/

/-- The converse FIRED at a genuinely non-squarefree level: the all-ones weight on
`[0, 12)` vanishes against `ζ₁₂` — produced from the packet split `1 = 1 + 0`. -/
example : ∑ e ∈ Finset.range (2 ^ 2 * 3 ^ 1), ((1 : ℕ) : ℂ)
    * Complex.exp (2 * Real.pi * Complex.I / (12 : ℕ)) ^ e = 0 := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (12 : ℕ)))
      (2 ^ 2 * 3 ^ 1) := by
    have h := Complex.isPrimitiveRoot_exp 12 (by norm_num)
    norm_num at h ⊢
    exact h
  exact (debruijn_weighted_two_prime Nat.prime_two Nat.prime_three (by norm_num)
    (by norm_num) (by norm_num) hζ (fun _ => 1)).mpr
    ⟨fun _ => 1, fun _ => 0, fun e _ => rfl⟩

end DeBruijnWeightedTwoPrime

#print axioms DeBruijnWeightedTwoPrime.packet_part_eq_zero
#print axioms DeBruijnWeightedTwoPrime.weighted_combination_of_vanishing
#print axioms DeBruijnWeightedTwoPrime.debruijn_weighted_two_prime
