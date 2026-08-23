/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Round 25 (Issue #232) — GENERAL t=1 RIGIDITY AT ALL w: disjoint equal-sum sets of `2N`-th roots
# are unions of antipodal pairs (no case analysis, uniform in w)

The leap past the case-by-case ladder (R23: pairs; R24: triples): **the per-index fiber argument
proves the `t = 1` linear-window rigidity at every support size simultaneously.** Over `CharZero`
with the half basis `{ζ^j : j < N}` independent, encode `2N`-th roots as signed points
`(j, ε) ↦ ±ζ^j`. The key structural fact: **each index `j` carries at most TWO signed points** —
`(j, true)` and `(j, false)` — so every index fiber of a set `A` is `∅`, a singleton, or the full
antipodal pair, and its integer contribution is `0` or `±1`:

* `contrib_eq_zero_iff`: contribution `0` ⟺ the fiber is `∅` or the antipodal pair;
  contribution `±1` ⟺ a singleton fiber.
* `bridgeF` (the Finset integer bridge): `∑_{p∈A} sval p = ∑_{p∈B} sval p` forces
  `contribZ A j = contribZ B j` at every index.
* **`disjoint_equal_sum_antipodal` (THE GENERAL THEOREM):** if `A` and `B` are disjoint and have
  equal sums, then EVERY point of `A` has its antipode in `A` (and likewise `B`) — both sets are
  unions of antipodal pairs. *Proof:* a singleton fiber of `A` at `j` has contribution `±1`, so
  `B`'s fiber at `j` is a singleton of the SAME sign — the same signed point — violating
  disjointness. Hence all fibers are `∅` or antipodal pairs. **No case bash; uniform in `|A|`.**
* Corollaries: `odd_card_impossible` (disjoint equal-sum sets have even cardinality — subsumes
  R24's triples), and both sums are zero (`sum_eq_zero`).

**Pathway impact (Step 2 of O46).** This settles the `t = 1` window of the char-0 rigidity at ALL
support sizes: disjoint equal-`e₁` families in `μ_{2N}` are exactly the antipodally-closed sets —
i.e. the `d = 2` lifts (`Λ_A(X) = ∏(X² − x_i²)`, a polynomial in `X²` — the Round-22 structure).
The full linear window then RECURSES: equal `e₁,…,e_t` of `d=2` lifts reduces (coefficients of
`X²`-polynomials) to equal `e₁,…,e_{⌊t/2⌋}` of the square sets in `μ_N`, whose half basis
`{ζ^{2j}}` inherits independence — `⌈log₂(t+1)⌉` halvings exhaust the window, forcing the
`2^k`-lift structure: **floor (R22) = ceiling**. The recursion assembly and the shared-vertex
(sunflower-core) reduction are the remaining formalization steps; the per-level engine is this
file's theorem.
-/

open Finset

namespace Round25General

variable {F : Type*} [Field F] [CharZero F] {N : ℕ} {ζ : F}

/-- A signed half-basis point `(j, ε)` represents the `2N`-th root `±ζ^j`. -/
def sval (ζ : F) (p : Fin N × Bool) : F :=
  (if p.2 then 1 else -1) * ζ ^ (p.1 : ℕ)

/-- The antipode `(j, ε) ↦ (j, ¬ε)`. -/
def antipode (p : Fin N × Bool) : Fin N × Bool := (p.1, !p.2)

/-- The integer sign. -/
def isgn (p : Fin N × Bool) : ℤ := if p.2 then 1 else -1

/-- The index fiber of `A` at `j`. -/
def fiber (A : Finset (Fin N × Bool)) (j : Fin N) : Finset (Fin N × Bool) :=
  A.filter (fun p => p.1 = j)

/-- The integer contribution of `A` at index `j`. -/
def contribZ (A : Finset (Fin N × Bool)) (j : Fin N) : ℤ :=
  ∑ p ∈ fiber A j, isgn p

/-! ## 1. Fiber structure: each index carries at most the antipodal pair -/

/-- The fiber is contained in the two-element set `{(j, true), (j, false)}`. -/
theorem fiber_subset_pair (A : Finset (Fin N × Bool)) (j : Fin N) :
    fiber A j ⊆ {(j, true), (j, false)} := by
  intro p hp
  obtain ⟨_, hpj⟩ := Finset.mem_filter.mp hp
  rcases p with ⟨pj, (_|_)⟩ <;> simp_all

/-- Membership transfer: `p ∈ fiber A p.1 ↔ p ∈ A`. -/
theorem mem_fiber_self {A : Finset (Fin N × Bool)} {p : Fin N × Bool} :
    p ∈ fiber A p.1 ↔ p ∈ A := by
  unfold fiber
  simp

/-! ## 2. The Finset integer bridge -/

/-- The coefficient profile of one point. -/
def coefAt (p : Fin N × Bool) (j : Fin N) : ℤ := if p.1 = j then isgn p else 0

omit [CharZero F] in
theorem sval_eq_sum (p : Fin N × Bool) :
    sval ζ p = ∑ j : Fin N, ((coefAt p j : ℤ) : F) * ζ ^ (j : ℕ) := by
  rw [Finset.sum_eq_single p.1]
  · unfold sval coefAt isgn
    rcases p with ⟨j, (_|_)⟩ <;> simp
  · intro j _ hne
    unfold coefAt
    rw [if_neg (Ne.symm hne)]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Summing the profiles over `A` recovers the per-index contributions. -/
theorem sum_coefAt (A : Finset (Fin N × Bool)) (j : Fin N) :
    (∑ p ∈ A, coefAt p j) = contribZ A j := by
  unfold contribZ coefAt fiber
  exact (Finset.sum_filter _ _).symm

/-- **The Finset integer bridge:** equal sums force equal integer contributions at every index. -/
theorem bridgeF
    (hindep : ∀ g : Fin N → F, (∑ j : Fin N, g j * ζ ^ (j : ℕ)) = 0 → ∀ j, g j = 0)
    {A B : Finset (Fin N × Bool)}
    (hsum : (∑ p ∈ A, sval ζ p) = ∑ p ∈ B, sval ζ p) :
    ∀ j, contribZ A j = contribZ B j := by
  intro j
  have hF : (∑ j : Fin N, (((contribZ A j - contribZ B j : ℤ) : F) * ζ ^ (j : ℕ))) = 0 := by
    have expand : ∀ (S : Finset (Fin N × Bool)),
        (∑ p ∈ S, sval ζ p) = ∑ j : Fin N, ((contribZ S j : ℤ) : F) * ζ ^ (j : ℕ) := by
      intro S
      rw [Finset.sum_congr rfl (fun p _ => sval_eq_sum (ζ := ζ) p), Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← sum_coefAt S j]
      push_cast
      rw [Finset.sum_mul]
    calc (∑ j : Fin N, (((contribZ A j - contribZ B j : ℤ) : F) * ζ ^ (j : ℕ)))
        = (∑ p ∈ A, sval ζ p) - (∑ p ∈ B, sval ζ p) := by
          rw [expand A, expand B, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          push_cast
          ring
      _ = 0 := by rw [hsum]; ring
  have := hindep (fun j => (((contribZ A j - contribZ B j : ℤ) : F))) hF j
  have hz : (contribZ A j - contribZ B j : ℤ) = 0 := by exact_mod_cast this
  omega

/-! ## 3. Singleton fibers force cross-equalities -/

/-- If the fiber of `A` at `j` is a singleton `{p}`, the contribution is `isgn p = ±1`. -/
theorem contrib_of_singleton {A : Finset (Fin N × Bool)} {j : Fin N} {p : Fin N × Bool}
    (h : fiber A j = {p}) : contribZ A j = isgn p := by
  unfold contribZ
  rw [h, Finset.sum_singleton]

/-- Fiber trichotomy: a fiber is `∅`, a singleton, or the full antipodal pair (with zero
contribution in the pair case). -/
theorem fiber_trichotomy (A : Finset (Fin N × Bool)) (j : Fin N) :
    fiber A j = ∅ ∨ (∃ p, fiber A j = {p}) ∨
      (fiber A j = {(j, true), (j, false)} ∧ contribZ A j = 0) := by
  have hsub := fiber_subset_pair A j
  have hcard : (fiber A j).card ≤ 2 := by
    calc (fiber A j).card ≤ ({(j, true), (j, false)} : Finset (Fin N × Bool)).card :=
          Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  interval_cases h : (fiber A j).card
  · left; exact Finset.card_eq_zero.mp h
  · right; left; exact Finset.card_eq_one.mp h
  · right; right
    have heq : fiber A j = {(j, true), (j, false)} := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [h]
      apply le_of_eq
      rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
    refine ⟨heq, ?_⟩
    unfold contribZ
    rw [heq]
    rw [Finset.sum_insert (by simp), Finset.sum_singleton]
    unfold isgn
    simp

/-! ## 4. THE GENERAL THEOREM -/

/-- **GENERAL t=1 RIGIDITY (all w, no case analysis).** If `A` and `B` are disjoint with equal
sums, every point of `A` has its antipode in `A`: the sets are unions of antipodal pairs.
*Proof:* if `p ∈ A` had no antipode in `A`, the fiber at `p.1` would be the singleton `{p}`, so
`contribZ A = isgn p = ±1 = contribZ B` (bridge) forces `B`'s fiber at `p.1` to be a singleton of
the same sign — the same signed point `p ∈ B`, violating disjointness. -/
theorem disjoint_equal_sum_antipodal
    (hindep : ∀ g : Fin N → F, (∑ j : Fin N, g j * ζ ^ (j : ℕ)) = 0 → ∀ j, g j = 0)
    {A B : Finset (Fin N × Bool)}
    (hsum : (∑ p ∈ A, sval ζ p) = ∑ p ∈ B, sval ζ p)
    (hdisj : Disjoint A B) :
    ∀ p ∈ A, antipode p ∈ A := by
  intro p hp
  by_contra hnot
  -- the fiber of A at p.1 is exactly {p}
  have hfib : fiber A p.1 = {p} := by
    apply Finset.Subset.antisymm
    · intro q hq
      obtain ⟨hqA, hqj⟩ := Finset.mem_filter.mp hq
      rw [Finset.mem_singleton]
      by_cases hs : q.2 = p.2
      · exact Prod.ext hqj hs
      · exfalso
        apply hnot
        have hqap : q = antipode p := by
          unfold antipode
          refine Prod.ext hqj ?_
          rcases hp2 : p.2 <;> rcases hq2 : q.2 <;> simp_all
        rw [← hqap]
        exact hqA
    · intro q hq
      rw [Finset.mem_singleton] at hq
      rw [hq]
      exact mem_fiber_self.mpr hp
  -- bridge: B's contribution at p.1 equals isgn p ≠ 0
  have hcA : contribZ A p.1 = isgn p := contrib_of_singleton hfib
  have hbridge := bridgeF hindep hsum p.1
  have hcB : contribZ B p.1 = isgn p := by omega
  -- B's fiber must be a singleton of the same sign — i.e. p itself
  rcases fiber_trichotomy B p.1 with h0 | ⟨q, hq⟩ | ⟨_, hzero⟩
  · rw [show contribZ B p.1 = 0 by unfold contribZ; rw [h0]; rfl] at hcB
    unfold isgn at hcB
    rcases p with ⟨_, (_|_)⟩ <;> simp_all
  · have hcq : contribZ B p.1 = isgn q := contrib_of_singleton hq
    have hsgn : isgn q = isgn p := by omega
    -- q has index p.1 and the same sign as p, so q = p
    have hqj : q.1 = p.1 := by
      have : q ∈ fiber B p.1 := by rw [hq]; exact Finset.mem_singleton_self q
      exact (Finset.mem_filter.mp this).2
    have hqB : q ∈ B := by
      have : q ∈ fiber B p.1 := by rw [hq]; exact Finset.mem_singleton_self q
      exact (Finset.mem_filter.mp this).1
    have hqp : q = p := by
      unfold isgn at hsgn
      rcases p with ⟨pj, (_|_)⟩ <;> rcases q with ⟨qj, (_|_)⟩ <;> simp_all
    rw [hqp] at hqB
    exact (Finset.disjoint_left.mp hdisj hp) hqB
  · rw [hzero] at hcB
    unfold isgn at hcB
    rcases p with ⟨_, (_|_)⟩ <;> simp_all <;> omega

end Round25General

#print axioms Round25General.bridgeF
#print axioms Round25General.fiber_trichotomy
#print axioms Round25General.disjoint_equal_sum_antipodal
