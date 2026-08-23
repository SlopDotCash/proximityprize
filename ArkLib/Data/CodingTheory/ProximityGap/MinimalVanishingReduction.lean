/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Issue #232 — LAM–LEUNG REDUCED TO MINIMAL VANISHING SUMS (O116)

The positivity item sharpened once more.  O110 reduced Lam–Leung's ℕ-span
theorem to the squarefree base; this file reduces the base to its true kernel —
the weights of MINIMAL vanishing sums:

* `exists_minimal_vanishing_subweight` — every nonzero vanishing ℕ-weight
  dominates a MINIMAL one (nonzero, vanishing, with no proper nonzero vanishing
  sub-weight): strong induction on the total weight;
* `span_of_minimal_span` — **the reduction**: if every minimal vanishing weight
  at level `n` has total in `ℕ`-span `S` (any additively closed target containing
  `0`), then EVERY vanishing weight does — peel one minimal sum at a time
  (the difference of vanishing weights is vanishing; totals strictly drop);
* `lam_leung_iff_minimal` — the span theorem at level `n` holds iff it holds for
  minimal weights.

Consequence for the ledger: combined with O110 (squarefree reduction) and O104
(two-prime base), Lam–Leung's theorem is now equivalent to the single statement
*"minimal vanishing sums at squarefree `n` with ≥ 3 prime factors have weight in
`ℕp₁ + … + ℕp_k`"* — which is exactly the Conway–Jones/Lam–Leung minimal-sum
structure theory (J. Algebra 224 (2000) §3–5; Acta Arith. 30 (1976)), the last
unformalized ingredient.  The O105 witness is such a minimal sum (weight
`6 = 3 + 3` at `n = 30` — in the span, as the theory predicts).
-/

namespace MinimalVanishingReduction

open Finset

variable {L : Type*} [Field L] [CharZero L]

omit [CharZero L] in
/-- Pointwise difference of vanishing ℕ-weights is vanishing (when dominated). -/
lemma vanishing_sub {n : ℕ} {ζ : L} {w v : ℕ → ℕ}
    (hle : ∀ e < n, v e ≤ w e)
    (hw : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0)
    (hv : ∑ e ∈ Finset.range n, (v e : L) * ζ ^ e = 0) :
    ∑ e ∈ Finset.range n, ((w e - v e : ℕ) : L) * ζ ^ e = 0 := by
  have hterm : ∀ e ∈ Finset.range n,
      ((w e - v e : ℕ) : L) * ζ ^ e
        = (w e : L) * ζ ^ e - (v e : L) * ζ ^ e := by
    intro e he
    rw [Nat.cast_sub (hle e (Finset.mem_range.mp he)), sub_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hw, hv, sub_self]

omit [CharZero L] in
/-- **Every nonzero vanishing weight dominates a minimal one** (strong induction
on the total): minimal means nonzero, vanishing, and admitting no proper nonzero
vanishing sub-weight on `[0, n)`. -/
theorem exists_minimal_vanishing_subweight {n : ℕ} {ζ : L} :
    ∀ N : ℕ, ∀ w : ℕ → ℕ, (∑ e ∈ Finset.range n, w e ≤ N) →
    (∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) →
    (∃ e < n, 0 < w e) →
    ∃ v : ℕ → ℕ, (∀ e < n, v e ≤ w e)
      ∧ (∑ e ∈ Finset.range n, (v e : L) * ζ ^ e = 0)
      ∧ (∃ e < n, 0 < v e)
      ∧ ∀ u : ℕ → ℕ, (∀ e < n, u e ≤ v e) →
          (∑ e ∈ Finset.range n, (u e : L) * ζ ^ e = 0) →
          (∃ e < n, 0 < u e) → ∀ e < n, u e = v e := by
  intro N
  induction N with
  | zero =>
    intro w hN hvan hne
    obtain ⟨e, he, hpos⟩ := hne
    have h0 : w e = 0 := by
      have h1 : w e ≤ ∑ e' ∈ Finset.range n, w e' :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr he)
      omega
    omega
  | succ N ih =>
    intro w hN hvan hne
    by_cases hmin : ∀ u : ℕ → ℕ, (∀ e < n, u e ≤ w e) →
        (∑ e ∈ Finset.range n, (u e : L) * ζ ^ e = 0) →
        (∃ e < n, 0 < u e) → ∀ e < n, u e = w e
    · exact ⟨w, fun e _ => le_rfl, hvan, hne, hmin⟩
    · push Not at hmin
      obtain ⟨u, hule, huvan, hune, e₀, he₀, hne₀⟩ := hmin
      have hult : ∑ e ∈ Finset.range n, u e < ∑ e ∈ Finset.range n, w e := by
        have hle' : ∀ e ∈ Finset.range n, u e ≤ w e :=
          fun e he => hule e (Finset.mem_range.mp he)
        have hlt : u e₀ < w e₀ :=
          lt_of_le_of_ne (hule e₀ he₀) hne₀
        exact Finset.sum_lt_sum hle' ⟨e₀, Finset.mem_range.mpr he₀, hlt⟩
      obtain ⟨v, hv1, hv2, hv3, hv4⟩ := ih u (by omega) huvan hune
      exact ⟨v, fun e he => le_trans (hv1 e he) (hule e he), hv2, hv3, hv4⟩

omit [CharZero L] in
/-- **THE MINIMAL-SUM REDUCTION** (Lam–Leung's kernel isolated): if every MINIMAL
vanishing weight at level `n` has total in the span `S` (here: representable as
`∑_{p ∈ primeFactors n} c p · p`), then every vanishing weight does — peel
minimal sums; totals strictly decrease. -/
theorem span_of_minimal_span {n : ℕ} {ζ : L}
    (hmin : ∀ v : ℕ → ℕ,
      (∑ e ∈ Finset.range n, (v e : L) * ζ ^ e = 0) →
      (∃ e < n, 0 < v e) →
      (∀ u : ℕ → ℕ, (∀ e < n, u e ≤ v e) →
        (∑ e ∈ Finset.range n, (u e : L) * ζ ^ e = 0) →
        (∃ e < n, 0 < u e) → ∀ e < n, u e = v e) →
      ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range n, v e
        = ∑ p ∈ n.primeFactors, c p * p) :
    ∀ w : ℕ → ℕ,
      (∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) →
      ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range n, w e
        = ∑ p ∈ n.primeFactors, c p * p := by
  -- strong induction on the total weight
  suffices h : ∀ N : ℕ, ∀ w : ℕ → ℕ, (∑ e ∈ Finset.range n, w e ≤ N) →
      (∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) →
      ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range n, w e
        = ∑ p ∈ n.primeFactors, c p * p by
    intro w hvan
    exact h (∑ e ∈ Finset.range n, w e) w le_rfl hvan
  intro N
  induction N with
  | zero =>
    intro w hN _
    refine ⟨fun _ => 0, ?_⟩
    have h0 : ∑ e ∈ Finset.range n, w e = 0 := by omega
    rw [h0]
    simp
  | succ N ih =>
    intro w hN hvan
    by_cases hne : ∃ e < n, 0 < w e
    · -- peel a minimal vanishing sub-weight
      obtain ⟨v, hvle, hvvan, hvne, hvmin⟩ :=
        exists_minimal_vanishing_subweight (∑ e ∈ Finset.range n, w e) w
          le_rfl hvan hne
      obtain ⟨cv, hcv⟩ := hmin v hvvan hvne hvmin
      have hvpos : 0 < ∑ e ∈ Finset.range n, v e := by
        obtain ⟨e, he, hpos⟩ := hvne
        have h1 : v e ≤ ∑ e' ∈ Finset.range n, v e' :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.mpr he)
        omega
      have hvtot : ∑ e ∈ Finset.range n, v e ≤ ∑ e ∈ Finset.range n, w e :=
        Finset.sum_le_sum fun e he => hvle e (Finset.mem_range.mp he)
      have hwvan' := vanishing_sub hvle hvan hvvan
      have hwtot' : ∑ e ∈ Finset.range n, (w e - v e)
          = ∑ e ∈ Finset.range n, w e - ∑ e ∈ Finset.range n, v e := by
        rw [eq_tsub_iff_add_eq_of_le hvtot, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun e he => ?_
        have := hvle e (Finset.mem_range.mp he)
        omega
      obtain ⟨cw, hcw⟩ := ih (fun e => w e - v e)
        (by rw [hwtot']; omega) hwvan'
      refine ⟨fun p => cw p + cv p, ?_⟩
      have htotal : ∑ e ∈ Finset.range n, w e
          = (∑ e ∈ Finset.range n, (w e - v e)) + ∑ e ∈ Finset.range n, v e := by
        rw [hwtot']
        omega
      rw [htotal, hcw, hcv, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    · -- zero weight on the window
      push Not at hne
      refine ⟨fun _ => 0, ?_⟩
      have h0 : ∑ e ∈ Finset.range n, w e = 0 := by
        refine Finset.sum_eq_zero fun e he => ?_
        have := hne e (Finset.mem_range.mp he)
        omega
      rw [h0]
      simp

omit [CharZero L] in
/-- **Lam–Leung ⟺ minimal weights in the span** (at any fixed level): the ℕ-span
law for all vanishing weights is equivalent to its restriction to MINIMAL
vanishing weights — the open content of the positivity theorem is exactly the
minimal-sum structure theory. -/
theorem lam_leung_iff_minimal {n : ℕ} {ζ : L} :
    (∀ w : ℕ → ℕ, (∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) →
      ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range n, w e
        = ∑ p ∈ n.primeFactors, c p * p)
    ↔ (∀ v : ℕ → ℕ,
        (∑ e ∈ Finset.range n, (v e : L) * ζ ^ e = 0) →
        (∃ e < n, 0 < v e) →
        (∀ u : ℕ → ℕ, (∀ e < n, u e ≤ v e) →
          (∑ e ∈ Finset.range n, (u e : L) * ζ ^ e = 0) →
          (∃ e < n, 0 < u e) → ∀ e < n, u e = v e) →
        ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range n, v e
          = ∑ p ∈ n.primeFactors, c p * p) := by
  constructor
  · intro h v hvan _ _
    exact h v hvan
  · exact span_of_minimal_span

end MinimalVanishingReduction

#print axioms MinimalVanishingReduction.vanishing_sub
#print axioms MinimalVanishingReduction.exists_minimal_vanishing_subweight
#print axioms MinimalVanishingReduction.span_of_minimal_span
#print axioms MinimalVanishingReduction.lam_leung_iff_minimal
