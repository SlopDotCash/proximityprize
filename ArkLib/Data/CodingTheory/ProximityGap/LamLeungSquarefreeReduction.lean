/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WeightedThreadSplit

/-!
# Issue #232 — LAM–LEUNG REDUCED TO THE SQUAREFREE BASE (O110)

Lam–Leung's ℕ-span theorem (`W(n) = ℕp₁ + … + ℕp_k`, J. Algebra 224 (2000)) is
published mathematics awaiting formalization, not open research.  This file
executes its SQUARE-DESCENT half: the weighted thread-split (O101) makes the
`p² ∣ n` inductive step a theorem, so the whole span theorem REDUCES to its
squarefree base —

* `nat_digit_sum` — the ℕ-valued digit decomposition
  `Σ_{e<p·m} g e = Σ_{r<p} Σ_{e'<m} g (r + p·e')`;
* `lam_leung_span_descent` — **one square stripped**: if `p ∣ m` and the span
  conclusion holds for all vanishing weights at level `m` (root `ζ^p`), it holds
  at level `p·m`: each of the `p` weighted threads vanishes
  (O101 `weighted_thread_vanishing_of_vanishing`), its weight lies in the span
  by hypothesis, and the total is the sum of the thread weights — with
  `primeFactors (p·m) = primeFactors m`;
* `lam_leung_of_squarefree` — **the reduction**: if the ℕ-span law holds at
  every squarefree level, it holds at EVERY level (strong induction stripping
  prime squares via `Nat.squarefree_iff_prime_squarefree`).

Consequences for the ledger: combined with O104 (the squarefree two-prime span
law) this CLOSES Lam–Leung at every `n` with at most two distinct primes —
including all prime powers `p^a` and all `p^a·q^b` — by composition.  The open
formalization residue of Lam–Leung is now EXACTLY the squarefree base with
`≥ 3` distinct primes (where the packet route is dead by O105 and the published
proof's minimal-sum induction is the route — its linear scaffolding is O109).
-/

namespace LamLeungSquarefreeReduction

open Finset

variable {L : Type*} [Field L] [CharZero L]

/-- The ℕ-valued digit decomposition of a sum over `[0, p·m)`. -/
lemma nat_digit_sum (p m : ℕ) (hp : 0 < p) (g : ℕ → ℕ) :
    ∑ e ∈ Finset.range (p * m), g e
      = ∑ r ∈ Finset.range p, ∑ e' ∈ Finset.range m, g (r + p * e') := by
  classical
  rw [← Finset.sum_product']
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

/-- **One square stripped** (the `p² ∣ n` Lam–Leung step, unconditional given the
level below): if every vanishing ℕ-weight at level `m` (root `ζ^p`) has weight in
the ℕ-span of `m`'s primes, then so does every vanishing ℕ-weight at level
`p·m` (`p ∣ m`) — thread-split, sum the thread spans. -/
theorem lam_leung_span_descent {p m : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hpm : p ∣ m) {ζ : L} (hζ : IsPrimitiveRoot ζ (p * m))
    (IH : ∀ w' : ℕ → ℕ,
      (∑ e ∈ Finset.range m, (w' e : L) * (ζ ^ p) ^ e = 0) →
      ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range m, w' e
        = ∑ q ∈ m.primeFactors, c q * q)
    (w : ℕ → ℕ)
    (hvan : ∑ e ∈ Finset.range (p * m), (w e : L) * ζ ^ e = 0) :
    ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range (p * m), w e
      = ∑ q ∈ (p * m).primeFactors, c q * q := by
  classical
  -- the prime sets agree (`p` already divides `m`)
  have hfac : (p * m).primeFactors = m.primeFactors := by
    rw [Nat.primeFactors_mul hp.pos.ne' hm.ne', hp.primeFactors,
      Finset.singleton_union,
      Finset.insert_eq_self.mpr (Nat.mem_primeFactors.mpr ⟨hp, hpm, hm.ne'⟩)]
  -- the threads vanish
  have hth := WeightedThreadSplit.weighted_thread_vanishing_of_vanishing
    hp hm hpm hζ w hvan
  -- per-thread spans, with guarded choice
  have hchoice : ∀ r : ℕ, ∃ c : ℕ → ℕ, r < p →
      ∑ e' ∈ Finset.range m, w (r + p * e')
        = ∑ q ∈ m.primeFactors, c q * q := by
    intro r
    by_cases hr : r < p
    · obtain ⟨c, hc⟩ := IH (fun e' => w (r + p * e')) (hth r hr)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨fun _ => 0, fun h => absurd h hr⟩
  choose c hc using hchoice
  refine ⟨fun q => ∑ r ∈ Finset.range p, c r q, ?_⟩
  rw [hfac, nat_digit_sum p m hp.pos w]
  calc ∑ r ∈ Finset.range p, ∑ e' ∈ Finset.range m, w (r + p * e')
      = ∑ r ∈ Finset.range p, ∑ q ∈ m.primeFactors, c r q * q := by
        refine Finset.sum_congr rfl fun r hr => ?_
        exact hc r (Finset.mem_range.mp hr)
    _ = ∑ q ∈ m.primeFactors, (∑ r ∈ Finset.range p, c r q) * q := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_mul]

/-- **LAM–LEUNG REDUCED TO THE SQUAREFREE BASE**: if the ℕ-span law holds at
every squarefree level, it holds at every level — strong induction stripping
prime squares.  Combined with O104 this closes Lam–Leung at every modulus with
at most two distinct primes; the remaining formalization residue is exactly the
squarefree base with `≥ 3` primes. -/
theorem lam_leung_of_squarefree
    (hsf : ∀ ν : ℕ, Squarefree ν → ∀ ζ : L, IsPrimitiveRoot ζ ν →
      ∀ w : ℕ → ℕ, (∑ e ∈ Finset.range ν, (w e : L) * ζ ^ e = 0) →
      ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range ν, w e
        = ∑ q ∈ ν.primeFactors, c q * q) :
    ∀ n : ℕ, 0 < n → ∀ ζ : L, IsPrimitiveRoot ζ n →
      ∀ w : ℕ → ℕ, (∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) →
      ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range n, w e
        = ∑ q ∈ n.primeFactors, c q * q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn0 ζ hζ w hvan
    by_cases hsq : Squarefree n
    · exact hsf n hsq ζ hζ w hvan
    · -- a prime square divides: strip it
      rw [Nat.squarefree_iff_prime_squarefree] at hsq
      push Not at hsq
      obtain ⟨p, hp, hppn⟩ := hsq
      obtain ⟨m', hm'⟩ := hppn
      have hpm' : p ∣ p * m' := ⟨m', rfl⟩
      have hn_eq : n = p * (p * m') := by rw [hm']; ring
      have hm0 : 0 < p * m' := by
        rcases Nat.eq_zero_or_pos (p * m') with h0 | h
        · rw [hn_eq, h0, Nat.mul_zero] at hn0
          exact absurd hn0 (lt_irrefl 0)
        · exact h
      have hmn : p * m' < n := by
        rw [hn_eq]
        calc p * m' = 1 * (p * m') := (Nat.one_mul _).symm
          _ < p * (p * m') := by
              exact (Nat.mul_lt_mul_right hm0).mpr hp.one_lt
      rw [hn_eq] at hζ hvan ⊢
      have hζp : IsPrimitiveRoot (ζ ^ p) (p * m') :=
        hζ.pow (Nat.mul_pos hp.pos hm0) rfl
      exact lam_leung_span_descent hp hm0 hpm' hζ
        (fun w' hv' => ih (p * m') (hn_eq ▸ hmn) hm0 (ζ ^ p) hζp w' hv')
        w hvan

end LamLeungSquarefreeReduction

#print axioms LamLeungSquarefreeReduction.nat_digit_sum
#print axioms LamLeungSquarefreeReduction.lam_leung_span_descent
#print axioms LamLeungSquarefreeReduction.lam_leung_of_squarefree
