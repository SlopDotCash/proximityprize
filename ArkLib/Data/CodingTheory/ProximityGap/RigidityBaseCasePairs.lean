/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Round 23 (Issue #232) — RIGIDITY BASE CASE: equal-sum pairs of `2N`-th roots are antipodal

The first case of the rigidity pathway's open Step 2 (O46): over a characteristic-zero field, with
the half-basis `{ζ^j : j < N}` linearly independent (`ζ^N = −1`; dischargeable in-tree at
`N = 2^{m−1}` via the Round-12 cyclotomic machinery), **the `(w=2, t=1)` linear-window rigidity
holds**: if two pairs of `2N`-th roots of unity have equal sums, then either the pairs coincide,
or BOTH are antipodal (both sums zero):

  `a + b = c + d`,  `{a,b} ≠ {c,d}`   ⟹   `b = −a ∧ d = −c`.

Encoding: a `2N`-th root is a signed half-basis element `(j, ε) ↦ ±ζ^j` (`ζ^{j+N} = −ζ^j`). The
sum equation becomes an **integer-coefficient** vanishing combination on the independent half
basis; independence + `Int.cast_injective` push every per-index equation into `ℤ`, where the sign
case analysis is mechanical (`omega`).

**Pathway placement.** This is the floor of Step 2 (char-0 linear-window rigidity): at `w = 2` the
only equal-`e₁` families in `μ_{2N}` are the `d = 2` lifts (antipodal pairs `X² − a` form), exactly
matching the Round-22 constructive floor — the rigidity conjecture is TRUE in its base case.
Extending to `w ≥ 3` windows (Conway–Jones/Mann territory) is the remaining open content.
-/

open Finset

namespace Round23Rigidity

variable {F : Type*} [Field F] [CharZero F] {N : ℕ} {ζ : F}

/-- A signed half-basis point `(j, ε)` represents the `2N`-th root `±ζ^j`. -/
def sval (ζ : F) (p : Fin N × Bool) : F :=
  (if p.2 then 1 else -1) * ζ ^ (p.1 : ℕ)

omit [CharZero F] in
/-- The antipode: `(j, ε) ↦ (j, ¬ε)` represents `∓ζ^j = −(±ζ^j)`. -/
def antipode (p : Fin N × Bool) : Fin N × Bool := (p.1, !p.2)

omit [CharZero F] in
theorem sval_antipode (p : Fin N × Bool) : sval ζ (antipode p) = -sval ζ p := by
  unfold sval antipode
  rcases p with ⟨j, (_|_)⟩ <;> simp

/-- The integer sign of a point. -/
def isgn (p : Fin N × Bool) : ℤ := if p.2 then 1 else -1

/-- The integer coefficient function of the 4-point combination `x + y − z − w`. -/
def gZ (x y z w : Fin N × Bool) (j : Fin N) : ℤ :=
  (if x.1 = j then isgn x else 0) + (if y.1 = j then isgn y else 0)
    - (if z.1 = j then isgn z else 0) - (if w.1 = j then isgn w else 0)

omit [CharZero F] in
/-- Each `sval` is the basis expansion of its (single-index, signed) coefficient. -/
theorem sval_eq_sum (p : Fin N × Bool) :
    sval ζ p = ∑ j : Fin N, ((if p.1 = j then isgn p else 0 : ℤ) : F) * ζ ^ (j : ℕ) := by
  rw [Finset.sum_eq_single p.1]
  · unfold sval isgn
    rcases p with ⟨j, (_|_)⟩ <;> simp
  · intro j _ hne
    rw [if_neg (Ne.symm hne)]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The bridge to ℤ:** the equal-sum equation forces every integer coefficient to vanish. -/
theorem gZ_eq_zero
    (hindep : ∀ g : Fin N → F, (∑ j : Fin N, g j * ζ ^ (j : ℕ)) = 0 → ∀ j, g j = 0)
    {x y z w : Fin N × Bool}
    (hsum : sval ζ x + sval ζ y = sval ζ z + sval ζ w) :
    ∀ j, gZ x y z w j = 0 := by
  intro j
  have hF : (∑ j : Fin N, ((gZ x y z w j : ℤ) : F) * ζ ^ (j : ℕ)) = 0 := by
    have hexp : ∀ p : Fin N × Bool, sval ζ p
        = ∑ j : Fin N, ((if p.1 = j then isgn p else 0 : ℤ) : F) * ζ ^ (j : ℕ) :=
      sval_eq_sum
    calc (∑ j : Fin N, ((gZ x y z w j : ℤ) : F) * ζ ^ (j : ℕ))
        = (sval ζ x + sval ζ y) - (sval ζ z + sval ζ w) := by
          rw [hexp x, hexp y, hexp z, hexp w]
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          unfold gZ
          push_cast
          ring
      _ = 0 := by rw [hsum]; ring
  have := hindep (fun j => ((gZ x y z w j : ℤ) : F)) hF j
  exact_mod_cast this

/-- `sval` is injective (given independence): distinct signed points have distinct values. -/
theorem sval_injective
    (hindep : ∀ g : Fin N → F, (∑ j : Fin N, g j * ζ ^ (j : ℕ)) = 0 → ∀ j, g j = 0)
    {p q : Fin N × Bool} (h : sval ζ p = sval ζ q) : p = q := by
  -- p + q' − q − q' form: use the 4-point bridge with y = w := q (x + y − z − w with x=p,y=q,z=q,w=q
  -- gives p − q = 0 pattern); simpler: direct 2-point version.
  have hF : (∑ j : Fin N, (((if p.1 = j then isgn p else 0 : ℤ)
      - (if q.1 = j then isgn q else 0) : ℤ) : F) * ζ ^ (j : ℕ)) = 0 := by
    calc (∑ j : Fin N, (((if p.1 = j then isgn p else 0 : ℤ)
          - (if q.1 = j then isgn q else 0) : ℤ) : F) * ζ ^ (j : ℕ))
        = sval ζ p - sval ζ q := by
          rw [sval_eq_sum p, sval_eq_sum q, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          push_cast
          ring
      _ = 0 := by rw [h]; ring
  have hz : ∀ j, ((if p.1 = j then isgn p else 0 : ℤ) - (if q.1 = j then isgn q else 0)) = 0 := by
    intro j
    have := hindep (fun j => (((if p.1 = j then isgn p else 0 : ℤ)
        - (if q.1 = j then isgn q else 0) : ℤ) : F)) hF j
    exact_mod_cast this
  -- read off at j = p.1
  have hp := hz p.1
  rw [if_pos rfl] at hp
  by_cases hpq : p.1 = q.1
  · -- same index: signs must agree
    rw [hpq, if_pos rfl] at hp  -- careful: condition is q.1 = p.1; adjust below
    rcases p with ⟨jp, (_|_)⟩ <;> rcases q with ⟨jq, (_|_)⟩ <;>
      simp_all [isgn]
  · -- distinct indices: coefficient ±1 = 0, impossible
    rw [if_neg (fun h' => hpq h'.symm)] at hp
    rcases p with ⟨jp, (_|_)⟩ <;> simp_all [isgn]

set_option maxHeartbeats 1000000 in
/-- The key step: the coefficient at `x.1` alone forces `y = antipode x` (given signed-disjointness
of `x` from `{z, w}`). Eight index-branches; each closes by integer sign arithmetic. -/
theorem antipode_of_gZ
    (hindep : ∀ g : Fin N → F, (∑ j : Fin N, g j * ζ ^ (j : ℕ)) = 0 → ∀ j, g j = 0)
    {x y z w : Fin N × Bool}
    (hsum : sval ζ x + sval ζ y = sval ζ z + sval ζ w)
    (hxz : x ≠ z) (hxw : x ≠ w) :
    y = antipode x := by
  have hgx := gZ_eq_zero hindep hsum x.1
  unfold gZ isgn at hgx
  rw [if_pos rfl] at hgx
  obtain ⟨jx, sx⟩ := x
  obtain ⟨jy, sy⟩ := y
  obtain ⟨jz, sz⟩ := z
  obtain ⟨jw, sw⟩ := w
  simp only [ne_eq, Prod.mk.injEq, not_and] at hxz hxw
  unfold antipode
  simp only [Prod.mk.injEq]
  by_cases e1 : jy = jx <;> by_cases e2 : jz = jx <;> by_cases e3 : jw = jx <;>
    rcases sx <;> rcases sy <;> rcases sz <;> rcases sw <;>
    simp_all

/-- **THE BASE-CASE RIGIDITY THEOREM.** Over a `CharZero` field with the half basis independent:
if `sval x + sval y = sval z + sval w` with the pairs signed-disjoint, then **both pairs are
antipodal**: `y = antipode x` and `w = antipode z` (both sums are zero). Combined with the
cancellation direction (a shared element forces the pairs to coincide, via `sval_injective`),
this is the full `(w=2, t=1)` linear-window rigidity: equal-sum pairs of `2N`-th roots are either
identical or both antipodal. -/
theorem pair_rigidity
    (hindep : ∀ g : Fin N → F, (∑ j : Fin N, g j * ζ ^ (j : ℕ)) = 0 → ∀ j, g j = 0)
    {x y z w : Fin N × Bool}
    (hsum : sval ζ x + sval ζ y = sval ζ z + sval ζ w)
    (hxz : x ≠ z) (hxw : x ≠ w) :
    y = antipode x ∧ w = antipode z := by
  have hy := antipode_of_gZ hindep hsum hxz hxw
  refine ⟨hy, ?_⟩
  -- with y = antipode x the left side vanishes; so sval w = −sval z = sval (antipode z)
  have hzero : sval ζ x + sval ζ y = 0 := by
    rw [hy, sval_antipode]; ring
  have hw : sval ζ w = sval ζ (antipode z) := by
    rw [sval_antipode]
    have h0 := hsum
    rw [hzero] at h0
    linear_combination -h0
  exact sval_injective hindep hw

end Round23Rigidity

#print axioms Round23Rigidity.gZ_eq_zero
#print axioms Round23Rigidity.sval_injective
#print axioms Round23Rigidity.pair_rigidity
