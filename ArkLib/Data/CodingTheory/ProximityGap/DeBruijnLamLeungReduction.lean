/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WeightedThreadSplit

/-!
# Issue #232 — THE LAM–LEUNG REDUCTION TO SQUAREFREE LEVELS (O112)

The Lam–Leung ℕ-span theorem (J. Algebra 224 (2000), Thm 4.1/5.2) — the total
weight of a vanishing ℕ-combination of `n`-th roots of unity lies in
`ℕp₁ + ⋯ + ℕp_k` — is in-tree at prime powers (O96) and two-prime moduli
(O104), and genuinely open at 3+ primes.  This file pins the open core exactly:

* `lam_leung_reduction_to_squarefree` — **the reduction**: if the span law holds
  at every SQUAREFREE divisor level of `n`, it holds at `n`.

Mechanism: strong induction on `n`.  At a non-squarefree level some prime has
`r² ∣ n`, so the O101 weighted thread split applies — all `r` threads vanish
individually (with ℕ-weights!) one level down at `n/r`, which has the SAME
prime set; the total weight is the sum of the thread totals, and the inductive
span memberships add.  The recursion strictly descends and bottoms out at the
squarefree radical.

Consequence: the Lam–Leung ℕ-span theorem is open **exactly at squarefree
`n = p₁⋯p_k` with `k ≥ 3`** (first case `n = 30`) — everything above the
radical is bookkeeping, machine-checked here.  This is the precise residual
left between the refuted ℕ-cone rows (O105) and the proven ℤ-module rows
(O110/O111) of the windowed-law lattice.
-/

namespace DeBruijnLamLeungReduction

open Finset

variable {L : Type*} [Field L]

/-- The total-weight regrouping along the low digit: `Σ_{e<r·m} w e` equals the
sum of the `r` thread totals (O101's digit decomposition at `ζ = 1`). -/
lemma total_eq_thread_totals (w : ℕ → ℕ) {r m : ℕ} (hr : 0 < r) :
    ∑ e ∈ Finset.range (r * m), w e
      = ∑ t ∈ Finset.range r, ∑ k ∈ Finset.range m, w (t + r * k) := by
  have h := WeightedThreadSplit.weighted_sum_eq_thread_sum (L := ℚ) (p := r)
    (m := m) hr 1 w
  simp only [one_pow, mul_one, one_mul] at h
  exact_mod_cast h

/-- **THE LAM–LEUNG REDUCTION TO SQUAREFREE LEVELS** (O112): if the ℕ-span law
holds at every squarefree divisor level of `n`, it holds at `n`.  Strong
induction: a repeated prime `r² ∣ n` lets the O101 weighted thread split break
the sum into `r` individually-vanishing ℕ-threads one level down (same prime
set), whose span memberships add. -/
theorem lam_leung_reduction_to_squarefree [CharZero L] :
    ∀ n, 0 < n →
    (∀ m, m ∣ n → Squarefree m → ∀ ξ : L, IsPrimitiveRoot ξ m → ∀ v : ℕ → ℕ,
      (∑ e ∈ Finset.range m, (v e : L) * ξ ^ e = 0) →
      ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range m, v e
        = ∑ p ∈ m.primeFactors, c p * p) →
    ∀ ζ : L, IsPrimitiveRoot ζ n → ∀ w : ℕ → ℕ,
      (∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) →
      ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range n, w e
        = ∑ p ∈ n.primeFactors, c p * p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn H ζ hζ w hsum
    by_cases hsq : Squarefree n
    · exact H n dvd_rfl hsq ζ hζ w hsum
    · -- a repeated prime exists
      rw [Nat.squarefree_iff_prime_squarefree] at hsq
      push Not at hsq
      obtain ⟨r, hrp, hrr⟩ := hsq
      have hr : r.Prime := hrp
      have hrn : r ∣ n := dvd_trans (dvd_mul_left r r) hrr
      set m : ℕ := n / r with hmdef
      have hnm : n = r * m := (Nat.mul_div_cancel' hrn).symm
      have hm : 0 < m := Nat.div_pos (Nat.le_of_dvd hn hrn) hr.pos
      have hmlt : m < n := by
        rw [hnm]
        calc m = 1 * m := (one_mul m).symm
          _ < r * m := (Nat.mul_lt_mul_right hm).mpr hr.one_lt
      have hrm : r ∣ m := by
        have h := hrr
        rw [hnm] at h
        exact (mul_dvd_mul_iff_left hr.pos.ne').mp h
      -- the O101 split: all r threads vanish individually with ℕ-weights
      rw [hnm] at hζ hsum
      have hth := WeightedThreadSplit.weighted_thread_vanishing_of_vanishing
        hr hm hrm hζ w hsum
      have hζm : IsPrimitiveRoot (ζ ^ r) m := hζ.pow (Nat.mul_pos hr.pos hm) rfl
      -- the hypothesis restricts to divisor levels of m
      have hmn : m ∣ n := ⟨r, by rw [hnm]; ring⟩
      have H' : ∀ m', m' ∣ m → Squarefree m' → ∀ ξ : L, IsPrimitiveRoot ξ m' →
          ∀ v : ℕ → ℕ, (∑ e ∈ Finset.range m', (v e : L) * ξ ^ e = 0) →
          ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range m', v e
            = ∑ p ∈ m'.primeFactors, c p * p :=
        fun m' hm' => H m' (hm'.trans hmn)
      -- IH per thread
      have hthreads : ∀ t, ∃ ct : ℕ → ℕ, t < r →
          ∑ k ∈ Finset.range m, w (t + r * k)
            = ∑ p ∈ m.primeFactors, ct p * p := by
        intro t
        by_cases ht : t < r
        · obtain ⟨ct, hct⟩ := IH m hmlt hm H' (ζ ^ r) hζm
            (fun k => w (t + r * k)) (hth t ht)
          exact ⟨ct, fun _ => hct⟩
        · exact ⟨0, fun hcon => absurd hcon ht⟩
      choose c hc using hthreads
      -- prime sets agree one level down
      have hpf : n.primeFactors = m.primeFactors := by
        rw [hnm, Nat.primeFactors_mul hr.pos.ne' hm.ne',
          Nat.Prime.primeFactors hr]
        exact Finset.union_eq_right.mpr
          (Finset.singleton_subset_iff.mpr
            (Nat.mem_primeFactors.mpr ⟨hr, hrm, hm.ne'⟩))
      -- totals add
      refine ⟨fun p => ∑ t ∈ Finset.range r, c t p, ?_⟩
      dsimp only
      rw [hpf, hnm, total_eq_thread_totals w hr.pos]
      calc ∑ t ∈ Finset.range r, ∑ k ∈ Finset.range m, w (t + r * k)
          = ∑ t ∈ Finset.range r, ∑ p ∈ m.primeFactors, c t p * p := by
            refine Finset.sum_congr rfl fun t ht => ?_
            exact hc t (Finset.mem_range.mp ht)
        _ = ∑ p ∈ m.primeFactors, ∑ t ∈ Finset.range r, c t p * p :=
            Finset.sum_comm
        _ = ∑ p ∈ m.primeFactors, (∑ t ∈ Finset.range r, c t p) * p := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.sum_mul]

end DeBruijnLamLeungReduction

#print axioms DeBruijnLamLeungReduction.total_eq_thread_totals
#print axioms DeBruijnLamLeungReduction.lam_leung_reduction_to_squarefree
