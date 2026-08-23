/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Multiset.Powerset
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# The balanced four-set law: the O145 antipodal ansatz is COMPLETE

Campaign #357. The characteristic-zero layer of the depth-1 window census at `a = 4` (the
even rows, where the parity law is silent) is the set of 4-element exponent sets whose six
pair sums are **antipodally balanced** — every residue fiber matched by its `+h` translate
(`foldedSum_eq_zero_iff_balanced`, `h` = half the group order). Probe O145 found that all
such sets satisfy the *antipodal ansatz* and counted them (`N₄(n) = n(n−3)/4`,
blind-verified at `n = 64`; re-verified for this file at `n = 4, 8, 16, 32` together with
both directions of the classification). This file proves the ansatz **complete, as a
structure theorem, in any abelian group whose doubling kernel is `{0, h}`** — so
`ZMod (2^m)` and the exponent groups of all smooth domains at once:

> **`balanced_pairSums_iff`** — a 4-element multiset `{a,b,c,d}` has antipodally balanced
> pair sums **iff** it has the form `{x, x+h, y, z}` with `y + z = x + x`: an antipodal
> pair plus two points symmetric about it.

Mechanism (two count instantiations + the doubling kernel):
* a balance witness for the fiber of `a+b` either directly produces an antipodal pair
  inside `{a,b,c,d}` or forces `c+d = a+b+h`; a second witness at `a+c` then either
  produces a pair or forces `b+d = a+c+h`, and subtracting the two residual equations
  gives `2(c−b) = 0`, which the doubling kernel resolves into the pair;
* given the pair `{x, x+h}`, four of the six sums balance unconditionally, so balance is
  equivalent to balance of the residual two-element multiset `{y+z, x+(x+h)}` — and a
  two-element multiset balances iff its elements differ by `h` (`balanced_two_iff`),
  i.e. iff `y + z = x + x`.

## Consequences

With the two-sided depth-1 dictionary (`depthOne_badScalar_iff_char0`) this classifies the
`a = 4` row of the adjacent-pair bad-scalar census at every smooth scale and every prime
above the threshold: bad scalars come exactly from `{x, x+h, y, 2x−y}` configurations. The
exact count `N₄(n) = n(n−3)/4` (inclusion–exclusion over this classification: `n(n−2)/4`
pair-plus-couple choices minus the `n/4` doubly-antipodal configurations counted twice) is
the named follow-up.

## References

* Probe O145 (`DISPROOF_LOG`), issue #357; `scripts/probes/probe_balanced_four_law.py`.
* The in-tree Lam–Leung/antipodal multiset laws (`KKH26CharZeroCollisionLaw.lean`) are the
  field-side shadow of this group-side law.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.WindowTwoLayer

open Multiset

/-! ## Pair sums and balance -/

section Monoid

variable {G : Type*} [AddCommMonoid G] [DecidableEq G]

/-- The multiset of pairwise sums of a multiset (sums of its 2-element sub-multisets). -/
def pairSums (s : Multiset G) : Multiset G :=
  (s.powersetCard 2).map Multiset.sum

/-- A multiset is `h`-balanced when every fiber is matched by its `+h` translate. -/
def Balanced (h : G) (M : Multiset G) : Prop :=
  ∀ t : G, M.count t = M.count (t + h)

theorem pairSums_cons (a : G) (s : Multiset G) :
    pairSums (a ::ₘ s) = pairSums s + s.map (a + ·) := by
  unfold pairSums
  rw [powersetCard_cons, Multiset.map_add]
  congr 1
  rw [Multiset.powersetCard_one, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun x _ => ?_
  simp

theorem pairSums_pair (c d : G) : pairSums {c, d} = {c + d} := by
  rw [show ({c, d} : Multiset G) = c ::ₘ {d} from rfl, pairSums_cons]
  have h1 : pairSums ({d} : Multiset G) = 0 := by
    unfold pairSums
    rw [show ({d} : Multiset G) = d ::ₘ 0 from rfl, powersetCard_cons]
    simp
  rw [h1]
  simp

/-- The explicit six pair sums of a four-element multiset. -/
theorem pairSums_four (a b c d : G) :
    pairSums {a, b, c, d}
      = {a + b} + {a + c} + {a + d} + {b + c} + {b + d} + {c + d} := by
  rw [show ({a, b, c, d} : Multiset G) = a ::ₘ b ::ₘ ({c, d} : Multiset G) from rfl,
    pairSums_cons, pairSums_cons, pairSums_pair]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
  ext t
  simp only [Multiset.count_add, Multiset.insert_eq_cons, Multiset.count_cons,
    Multiset.count_singleton]
  ring

end Monoid

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-! ## Balance toolkit -/

theorem balanced_add {h : G} {M N : Multiset G} (hM : Balanced h M) (hN : Balanced h N) :
    Balanced h (M + N) := fun t => by
  rw [Multiset.count_add, Multiset.count_add, hM t, hN t]

theorem balanced_residual {h : G} {M N : Multiset G} (hM : Balanced h M)
    (hMN : Balanced h (M + N)) : Balanced h N := fun t => by
  have h1 := hMN t
  rw [Multiset.count_add, Multiset.count_add, hM t] at h1
  omega

/-- The two indicator flips of an antipodal fiber. -/
private theorem flip_iff_left {h : G} (hh2 : h + h = 0) (t s : G) :
    t = s ↔ t + h = s + h :=
  ⟨fun e => by rw [e], fun e => add_right_cancel e⟩

private theorem flip_iff_right {h : G} (hh2 : h + h = 0) (t s : G) :
    t = s + h ↔ t + h = s := by
  constructor
  · rintro rfl
    rw [add_assoc, hh2, add_zero]
  · intro e
    rw [← e, add_assoc, hh2, add_zero]

/-- A two-element antipodal fiber is balanced. -/
theorem balanced_antipodal_pair {h : G} (hh2 : h + h = 0) (s : G) :
    Balanced h ({s, s + h} : Multiset G) := by
  intro t
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton,
    Multiset.count_zero]
  rw [if_congr (flip_iff_left hh2 t s) rfl rfl,
    if_congr (flip_iff_right hh2 t s) rfl rfl]
  ring

/-- A two-element multiset balances **iff** its elements differ by `h`. -/
theorem balanced_two_iff {h : G} (hh2 : h + h = 0) (hh0 : h ≠ 0) (u v : G) :
    Balanced h ({u, v} : Multiset G) ↔ v = u + h := by
  constructor
  · intro hbal
    have hu := hbal u
    simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton,
      Multiset.count_zero, if_pos rfl] at hu
    have huu : ¬ u + h = u := fun hc => hh0 (by simpa using hc)
    by_cases hvh : u + h = v
    · exact hvh.symm
    · -- the fiber of `u` cannot balance: count u ≥ 1 but count (u+h) = 0
      by_cases huv : u = v
      · subst huv
        simp [huu, Ne.symm huu] at hu
      · simp [huv, huu, hvh] at hu
  · rintro rfl
    exact balanced_antipodal_pair hh2 u

/-! ## The structured half: ansatz configurations are balanced -/

/-- An antipodal pair plus a symmetric couple is balanced. -/
theorem balanced_of_structured {h : G} (hh2 : h + h = 0) (x y z : G)
    (hyz : y + z = x + x) : Balanced h (pairSums {x, x + h, y, z}) := by
  rw [pairSums_four]
  have e1 : x + (x + h) = (y + z) + h := by rw [hyz]; abel
  have e2 : (x + h) + y = (x + y) + h := by abel
  have e3 : (x + h) + z = (x + z) + h := by abel
  rw [e1, e2, e3]
  have hre : ({(y + z) + h} : Multiset G) + {x + y} + {x + z} + {(x + y) + h}
        + {(x + z) + h} + {y + z}
      = (({x + y, (x + y) + h} : Multiset G) + {x + z, (x + z) + h})
        + {y + z, (y + z) + h} := by
    ext t
    simp only [Multiset.count_add, Multiset.insert_eq_cons, Multiset.count_cons,
      Multiset.count_singleton, Multiset.count_zero]
    ring
  rw [hre]
  exact balanced_add (balanced_add (balanced_antipodal_pair hh2 _)
    (balanced_antipodal_pair hh2 _)) (balanced_antipodal_pair hh2 _)

/-! ## The completeness half -/

/-- Given the antipodal pair in place, balance forces the symmetric-couple condition. -/
theorem sum_eq_of_balanced_structured {h : G} (hh2 : h + h = 0) (hh0 : h ≠ 0) (x y z : G)
    (hbal : Balanced h (pairSums {x, x + h, y, z})) : y + z = x + x := by
  rw [pairSums_four] at hbal
  have e2 : (x + h) + y = (x + y) + h := by abel
  have e3 : (x + h) + z = (x + z) + h := by abel
  rw [e2, e3] at hbal
  have hre : ({x + (x + h)} : Multiset G) + {x + y} + {x + z} + {(x + y) + h}
        + {(x + z) + h} + {y + z}
      = (({x + y, (x + y) + h} : Multiset G) + {x + z, (x + z) + h})
        + {y + z, x + (x + h)} := by
    ext t
    simp only [Multiset.count_add, Multiset.insert_eq_cons, Multiset.count_cons,
      Multiset.count_singleton, Multiset.count_zero]
    ring
  rw [hre] at hbal
  have hres : Balanced h ({y + z, x + (x + h)} : Multiset G) :=
    balanced_residual (balanced_add (balanced_antipodal_pair hh2 _)
      (balanced_antipodal_pair hh2 _)) hbal
  have hkey := (balanced_two_iff hh2 hh0 _ _).mp hres
  -- `x + (x + h) = (y + z) + h` cancels to the claim
  have hxx : x + (x + h) = (x + x) + h := by abel
  rw [hxx] at hkey
  exact (add_right_cancel hkey).symm

/-- **A balanced four-multiset contains an antipodal pair.** Two balance witnesses plus
the doubling kernel; no distinctness assumptions needed. -/
theorem antipodal_pair_of_balanced {h : G} (hh2 : h + h = 0) (hh0 : h ≠ 0)
    (hker : ∀ y : G, y + y = 0 → y = 0 ∨ y = h) {a b c d : G}
    (hbal : Balanced h (pairSums {a, b, c, d})) :
    ∃ p q, p ∈ ({a, b, c, d} : Multiset G) ∧ q ∈ ({a, b, c, d} : Multiset G)
      ∧ q = p + h := by
  rw [pairSums_four] at hbal
  have mema : a ∈ ({a, b, c, d} : Multiset G) := by simp
  have memb : b ∈ ({a, b, c, d} : Multiset G) := by simp
  have memc : c ∈ ({a, b, c, d} : Multiset G) := by simp
  have memd : d ∈ ({a, b, c, d} : Multiset G) := by simp
  -- positivity of a fiber count forces membership among the six sums
  have count_mem : ∀ s : G,
      0 < (({a + b} : Multiset G) + {a + c} + {a + d} + {b + c} + {b + d}
          + {c + d}).count s
      → s = a + b ∨ s = a + c ∨ s = a + d ∨ s = b + c ∨ s = b + d ∨ s = c + d := by
    intro s hpos
    have hmem := Multiset.count_pos.mp hpos
    simpa [Multiset.mem_add] using hmem
  -- first witness: the fiber of a + b
  have hab := hbal (a + b)
  have habpos : 0 < (({a + b} : Multiset G) + {a + c} + {a + d} + {b + c} + {b + d}
      + {c + d}).count (a + b + h) := by
    rw [← hab]
    exact Multiset.count_pos.mpr (by simp [Multiset.mem_add])
  rcases count_mem _ habpos with h1 | h2 | h3 | h4 | h5 | h6
  · exact absurd (by simpa using h1) hh0
  · -- a + c = a + b + h ⟹ c = b + h
    exact ⟨b, c, memb, memc,
      add_left_cancel (a := a) (show a + c = a + (b + h) by rw [← add_assoc]; exact h2.symm)⟩
  · -- a + d = a + b + h ⟹ d = b + h
    exact ⟨b, d, memb, memd,
      add_left_cancel (a := a) (show a + d = a + (b + h) by rw [← add_assoc]; exact h3.symm)⟩
  · -- b + c = a + b + h ⟹ c = a + h
    exact ⟨a, c, mema, memc,
      add_left_cancel (a := b) (show b + c = b + (a + h) by
        rw [← add_assoc, add_comm b a]; exact h4.symm)⟩
  · -- b + d = a + b + h ⟹ d = a + h
    exact ⟨a, d, mema, memd,
      add_left_cancel (a := b) (show b + d = b + (a + h) by
        rw [← add_assoc, add_comm b a]; exact h5.symm)⟩
  · -- residual: c + d = a + b + h; second witness at the fiber of a + c
    have hac := hbal (a + c)
    have hacpos : 0 < (({a + b} : Multiset G) + {a + c} + {a + d} + {b + c} + {b + d}
        + {c + d}).count (a + c + h) := by
      rw [← hac]
      exact Multiset.count_pos.mpr (by simp [Multiset.mem_add])
    rcases count_mem _ hacpos with g1 | g2 | g3 | g4 | g5 | g6
    · -- a + b = a + c + h ⟹ b = c + h
      exact ⟨c, b, memc, memb,
        add_left_cancel (a := a) (show a + b = a + (c + h) by
          rw [← add_assoc]; exact g1.symm)⟩
    · exact absurd (by simpa using g2) hh0
    · -- a + d = a + c + h ⟹ d = c + h
      exact ⟨c, d, memc, memd,
        add_left_cancel (a := a) (show a + d = a + (c + h) by
          rw [← add_assoc]; exact g3.symm)⟩
    · -- b + c = a + c + h ⟹ b = a + h
      exact ⟨a, b, mema, memb,
        add_left_cancel (a := c) (show c + b = c + (a + h) by
          rw [add_comm c b, ← add_assoc, add_comm c a]
          exact g4.symm)⟩
    · -- second residual: b + d = a + c + h; subtract to get 2(c − b) = 0
      have hsum : (c - b) + (c - b) = 0 := by
        have key : (c - b) + (c - b)
            = ((c + d) - (b + d)) + ((a + c + h) - (a + b + h)) := by abel
        rw [key, h6.symm, g5.symm]
        abel
      rcases hker _ hsum with hzero | hhalf
      · -- c = b: the first residual collapses to d = a + h
        have hcb : c = b := by rwa [sub_eq_zero] at hzero
        refine ⟨a, d, mema, memd, ?_⟩
        rw [hcb] at h6
        exact add_left_cancel (a := b) (show b + d = b + (a + h) by
          rw [← add_assoc, add_comm b a]; exact h6.symm)
      · -- c − b = h: c = b + h
        refine ⟨b, c, memb, memc, ?_⟩
        have : c = h + b := sub_eq_iff_eq_add.mp hhalf
        rwa [add_comm] at this
    · -- c + d = a + c + h ⟹ d = a + h
      exact ⟨a, d, mema, memd,
        add_left_cancel (a := c) (show c + d = c + (a + h) by
          rw [← add_assoc, add_comm c a]; exact g6.symm)⟩

/-! ## The headline -/

/-- **THE BALANCED FOUR-SET LAW (O145 ansatz completeness).** In any abelian group whose
doubling kernel is `{0, h}`: a four-element multiset has antipodally balanced pair sums
**iff** it is an antipodal pair plus a couple symmetric about it. -/
theorem balanced_pairSums_iff {h : G} (hh2 : h + h = 0) (hh0 : h ≠ 0)
    (hker : ∀ y : G, y + y = 0 → y = 0 ∨ y = h) (a b c d : G) :
    Balanced h (pairSums {a, b, c, d}) ↔
      ∃ x y z, ({a, b, c, d} : Multiset G) = {x, x + h, y, z} ∧ y + z = x + x := by
  constructor
  · intro hbal
    obtain ⟨p, q, hp, hq, hqp⟩ := antipodal_pair_of_balanced hh2 hh0 hker hbal
    have hpq : p ≠ q := fun hc => hh0 (by simpa using (hc ▸ hqp : p = p + h).symm)
    have hqmem : q ∈ ({a, b, c, d} : Multiset G).erase p :=
      (Multiset.mem_erase_of_ne (Ne.symm hpq)).mpr hq
    have hcard2 : ((({a, b, c, d} : Multiset G).erase p).erase q).card = 2 := by
      rw [Multiset.card_erase_of_mem hqmem, Multiset.card_erase_of_mem hp]
      rfl
    obtain ⟨y, z, hyz⟩ := Multiset.card_eq_two.mp hcard2
    have hset : ({a, b, c, d} : Multiset G) = {p, p + h, y, z} := by
      rw [show ({p, p + h, y, z} : Multiset G) = p ::ₘ (p + h) ::ₘ {y, z} from rfl,
        ← hyz, ← hqp, Multiset.cons_erase hqmem, Multiset.cons_erase hp]
    refine ⟨p, y, z, hset, ?_⟩
    rw [hset] at hbal
    exact sum_eq_of_balanced_structured hh2 hh0 p y z hbal
  · rintro ⟨x, y, z, hset, hyz⟩
    rw [hset]
    exact balanced_of_structured hh2 x y z hyz

/-! ## The smooth-scale instantiation: `ZMod (2^m)` -/

section ZModInstance

variable {m : ℕ}

theorem zmod_half_add_half (hm : 1 ≤ m) :
    ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = 0 := by
  have hsplit : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel hm] at h
    omega
  rw [← Nat.cast_add, hsplit, ZMod.natCast_self]

theorem zmod_half_ne_zero (hm : 1 ≤ m) :
    ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have h1 : 2 ^ m ≤ 2 ^ (m - 1) := Nat.le_of_dvd (pow_pos (by norm_num) _) hdvd
  have h2 : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- The doubling kernel of `ZMod (2^m)` is `{0, 2^(m−1)}`. -/
theorem zmod_double_kernel (hm : 1 ≤ m) (y : ZMod (2 ^ m)) (hy : y + y = 0) :
    y = 0 ∨ y = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hsplit : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel hm] at h
    omega
  have hv : y.val < 2 ^ m := ZMod.val_lt y
  have hcast : ((y.val + y.val : ℕ) : ZMod (2 ^ m)) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hy
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hcast
  rcases k with _ | _ | k
  · -- k = 0: y.val = 0
    left
    have : y.val = 0 := by omega
    rw [← ZMod.natCast_zmod_val y, this, Nat.cast_zero]
  · -- k = 1: y.val = 2^(m−1)
    right
    have : y.val = 2 ^ (m - 1) := by omega
    rw [← ZMod.natCast_zmod_val y, this]
  · -- k ≥ 2: y.val + y.val ≥ 2·2^m, impossible
    exfalso
    have hge : 2 ^ m * 2 ≤ 2 ^ m * (k + 2) := Nat.mul_le_mul_left _ (by omega)
    obtain ⟨w, hw⟩ : ∃ w, 2 ^ m * (k + 2) = w := ⟨_, rfl⟩
    rw [hw] at hk hge
    omega

/-- **The balanced four-set law over the smooth scale `2^m`** — the directly consumable
form for the window census: `h = 2^(m−1)` (the antipode of the exponent group). -/
theorem balanced_pairSums_iff_zmod (hm : 1 ≤ m) (a b c d : ZMod (2 ^ m)) :
    Balanced ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) (pairSums {a, b, c, d}) ↔
      ∃ x y z, ({a, b, c, d} : Multiset (ZMod (2 ^ m)))
          = {x, x + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)), y, z} ∧ y + z = x + x :=
  balanced_pairSums_iff (zmod_half_add_half hm) (zmod_half_ne_zero hm)
    (zmod_double_kernel hm) a b c d

end ZModInstance

/-! ## Source audit -/

#print axioms balanced_of_structured
#print axioms sum_eq_of_balanced_structured
#print axioms antipodal_pair_of_balanced
#print axioms balanced_pairSums_iff
#print axioms balanced_pairSums_iff_zmod

end ArkLib.ProximityGap.WindowTwoLayer
