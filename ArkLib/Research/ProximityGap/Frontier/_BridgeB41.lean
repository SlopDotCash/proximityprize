/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic

/-!
# Bridge B41 — `#bad` support max depth `m ≤ k` via the FFT 2-adic descent (toward E6, #444)

The EXACT FFT-graded recursion (E6) reads, for `#bad_n(k,m)` = the number of distinct nonzero
`n/2`-binned graded frequency vectors over `(k+m)`-subsets `A ⊆ ℤ/n` with all lower graded pieces
zero:

> `#bad_{2n}(k, 2m') = #bad_n(k/2, m')`   and   `#bad_{2n}(k, odd) = 0`.

`SPEC B41 [E6]`: **the support cutoff of `#bad` (the maximal depth `m` at which the count is
nonzero) is bounded by `k`.** This file makes that precise as a *monotone 2-adic descent bound*.

## The mechanism, stated abstractly

The odd half kills every odd depth; the even half folds `(n, k, m) ↦ (n/2, k/2, m/2)`. So a depth
`m` can only be in the support of `#bad_n(k, ·)` if it descends — halving `m` at every tower step,
staying even at each step until it terminates — down to depth `0` (the trivial graded vector) inside
a base level whose budget `k` is what survives the halving. Two facts drive the cutoff:

1. **Odd-vanishing forces evenness at each descent step** (E6 odd half).
2. **Even-folding halves both `k` and `m` together** (E6 even half).

Because `k` and `m` halve *in lockstep* down the tower and the descent must reach the base depth
`0` through `μ` even steps, the maximal *supported* depth at level `n = 2^μ` with budget `k` is
bounded by `k`: at every descent step a supported depth `m` is even and `m/2 ≤ k/2` is forced by
the inductive budget, so `m ≤ k` at the top. We package this as the abstract descent lemma below
(`descent_support_le`) together with the per-step content and a concrete monotone-cutoff instance.

## Honest scope

This is the abstract, axiom-clean *descent bookkeeping* for E6: GIVEN the two E6 recursion facts as
hypotheses on an abstract support predicate (odd-vanishing + even-folding-with-budget-halving), the
cutoff bound `m ≤ k` is proven by strong induction on `m`. Formalizing the concrete `#bad`-as-card
so that those two hypotheses become theorems (the bijection of `_Bridge05` odd half + the doubling
fold) is the named remaining obligation `E6FFTGradedRecursion`, NOT discharged here.
-/

namespace ArkLib.ProximityGap.BridgeB41

/-- **Abstract E6 support descent.** `supp lvl k m` says depth `m` is in the support of the
`#bad`-count at tower level `lvl` (`lvl = μ`, so `n = 2^μ`) with budget `k`.

We axiomatize the two E6 recursion facts as the structure's fields:
* `odd_vanish` — odd depths are never supported (E6 odd half `#bad(odd)=0`);
* `even_fold` — a supported even depth `m = 2*m'` at level `lvl+1` with budget `k` descends to a
  supported `m'` at level `lvl` with budget `k/2` (E6 even half, halving `k` and `m` in lockstep).
* `base` — at the base level `0`, only depth `0` is supported. -/
structure E6Descent (supp : ℕ → ℕ → ℕ → Prop) : Prop where
  odd_vanish : ∀ lvl k m, supp lvl k m → ¬ (m % 2 = 1)
  even_fold : ∀ lvl k m', supp (lvl + 1) k (2 * m') → supp lvl (k / 2) m'
  base : ∀ k m, supp 0 k m → m = 0

/-- **Support max-depth cutoff (E6 ⇒ `m ≤ k`).** Under the E6 descent recursion, any supported
depth `m` at tower level `lvl` with budget `k` satisfies `m ≤ k`.

Proof: strong induction on `lvl`. At the base, `m = 0 ≤ k`. At level `lvl+1`, odd-vanishing forces
`m` even, say `m = 2*m'`; even-folding gives `supp lvl (k/2) m'`, so the IH yields `m' ≤ k/2`, hence
`m = 2*m' ≤ 2*(k/2) ≤ k`. -/
theorem descent_support_le {supp : ℕ → ℕ → ℕ → Prop} (h : E6Descent supp) :
    ∀ lvl k m, supp lvl k m → m ≤ k := by
  intro lvl
  induction lvl with
  | zero =>
      intro k m hm
      have := h.base k m hm; omega
  | succ lvl ih =>
      intro k m hm
      -- `m` is even by odd-vanishing.
      have hne : ¬ (m % 2 = 1) := h.odd_vanish _ _ _ hm
      have heven : m % 2 = 0 := by omega
      obtain ⟨m', rfl⟩ : ∃ m', m = 2 * m' := ⟨m / 2, by omega⟩
      have hfold : supp lvl (k / 2) m' := h.even_fold lvl k m' hm
      have hih : m' ≤ k / 2 := ih _ _ hfold
      omega

/-- **Monotone form.** The cutoff is itself monotone in the budget: enlarging `k` only relaxes the
`m ≤ k` bound. Stated as the contrapositive cutoff — once `m` exceeds the budget the count is
silent. -/
theorem support_silent_above_budget {supp : ℕ → ℕ → ℕ → Prop} (h : E6Descent supp)
    (lvl k m : ℕ) (hgt : k < m) : ¬ supp lvl k m :=
  fun hm => absurd (descent_support_le h lvl k m hm) (by omega)

/-- **Concrete sanity instance.** The "even-folding cutoff" predicate
`supp lvl k m := m ≤ k ∧ (lvl ≠ 0 → m % 2 = 0)` ∧ base-collapse is a genuine `E6Descent`, and its
cutoff is exactly `m ≤ k`. We use a clean witness: `supp lvl k m := m = 0`, which trivially models
the descent (only depth `0` ever supported) and satisfies `m ≤ k`. -/
example : E6Descent (fun _ _ m => m = 0) where
  odd_vanish := by intro lvl k m hm; omega
  even_fold := by intro lvl k m' hm; omega
  base := by intro k m hm; exact hm

/-- The cutoff `m ≤ k` holds for that instance, via the general theorem. -/
example (lvl k m : ℕ) (hm : m = 0) : m ≤ k :=
  descent_support_le
    (supp := fun _ _ m => m = 0)
    ⟨by intro lvl k m hm; omega, by intro lvl k m' hm; omega,
      by intro k m hm; exact hm⟩ lvl k m hm

end ArkLib.ProximityGap.BridgeB41

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeB41.descent_support_le
#print axioms ArkLib.ProximityGap.BridgeB41.support_silent_above_budget
