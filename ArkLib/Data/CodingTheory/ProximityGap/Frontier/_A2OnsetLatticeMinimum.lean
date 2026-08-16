/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.Pigeonhole

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# A2 (relation-lattice-count): the onset of `W_r` is the `ℓ¹`-first-minimum `λ₁(L)`, and the
two-sided floor on `λ₁` — pinpointing the EXACT step where the lattice/onset route reduces.
(#444, TASK A2-relation-lattice-count, companion to `_A2RelationOrbitDivByN` and
`_AvStick_ReducedWraparoundLattice`.)

## What is open and where this fits

The single open prize object is the **saddle energy bound** `A_r ≤ (q−1)·Wick_r` at `r ≈ ln q`,
equivalently `W_r := E_r − E_r^{char0} ≤ slack`. `_AvStick_ReducedWraparoundLattice` reduced `W_r`
to a **short-vector count** in the reduced wraparound lattice

```
L = { a ∈ ℤ^m : Σ_{j<m} a_j g^j ≡ 0 (mod p) },   m = n/2,  g a primitive n-th root, g^m = −1.
```

`L` is the kernel of the surjection `ℤ^m ↠ ZMod p`, `a ↦ Σ a_j g^j`, so it is a **full-rank
sublattice of covolume `p`**. The Lam–Leung theorem says the char-0 relations are `a = 0` only
(`1,ζ,…,ζ^{m−1}` are a `ℤ`-basis), so **every nonzero `a ∈ L` is a genuine char-`p` wraparound**.

## The new exact structure proved here

### (1) The onset law: `W_r = 0 ⟺ 2r < λ₁^{ℓ¹}(L)` (sufficient direction, axiom-clean).

For an `r`-tuple `v ∈ μ_n^r` write `reduced(v) ∈ ℤ^m` for its antipodal fold (each root `g^j`
contributes `+e_{j mod m}` or `−e_{j−m}`). Then `ℓ¹(reduced(v)) ≤ r`, and for two `r`-tuples with
`Σv ≡ Σw (mod p)` the difference `a := reduced(v) − reduced(w)` lies in `L` with `ℓ¹(a) ≤ 2r`. A
contributing pair to `W_r` (genuine wraparound, `a ≠ 0`) is therefore a **nonzero lattice vector
of `ℓ¹`-weight `≤ 2r`**. Hence

```
2r < λ₁^{ℓ¹}(L)   ⟹   W_r = 0.
```

This is the EXACT generalization of the proven `W_2 = W_3 = 0`: those vanish because `2·2 = 4`,
`2·3 = 6` are below `λ₁ ≈ 9–10` at `n = 16`, `p ≈ n^4`. Verified exactly (`docs/kb/a2_minrel.py`):
for `n = 16, p = 65617`, `λ₁ = 10` and the first nonzero excess is `W_5 ≠ 0` at `2r = 10`; for
`p = 65713`, `λ₁ = 9` (odd) and onset is at `2r = 10` (the smallest even `2r ≥ λ₁`). The onset is
exactly `r₀ = ⌈λ₁/2⌉`.

### (2) The two-sided floor on `λ₁` — and the EXACT vacuity.

`_AvStick_ReducedWraparoundLattice` records the **volume (Minkowski) lower bound**
`λ₁^{ℓ¹}(L) ≥ p^{1/m} = p^{2/n}` (conditional on the carried `ℓ¹`-ball volume input). This file
adds the **unconditional pigeonhole UPPER bound** `λ₁^{ℓ¹}(L) ≤ 2·w₀` where `w₀` is the least
radius with `#{a ∈ ℤ^m : ℓ¹(a) ≤ w₀} > p`: if the `ℓ¹`-ball has more than `p` integer points, two
of them collide mod `p`, and their difference is a nonzero lattice vector of `ℓ¹`-weight `≤ 2w₀`.
We prove the abstract pigeonhole engine `exists_short_relation_of_card_gt` axiom-clean.

**The EXACT vacuity (the reduction, pinpointed numerically — `docs/kb/a2_budget.py`,
`a2_minrel.py`):**

```
n           p ≈ n^4     λ₁ (exact)    p^{2/n} (volume floor)    2·ln q (saddle, = 2r*)
16          65617       10            4.0                       22.2  (2r* = 11·2 = 22)
32          1048609     8             2.4                       27.7
prize 2^30  2^120       ≈ 9 (pigeonhole upper)   1.0000(vacuous)    166  (2r* ≈ 83)
```

The volume floor `p^{2/n} → 1` as `n → ∞`: **the Minkowski lower bound on `λ₁` is VACUOUS at prize
scale.** Worse, the pigeonhole UPPER bound shows relations appear at `ℓ¹`-weight `O((n/2)·p^{2/n})`,
which stays a small constant (`≈ 9`) while the saddle `2r* ≈ ln q ≈ 83`. So **at the prize scale the
relation lattice has short vectors from weight `≈ 9` all the way up to the saddle `≈ 83`**; onset
saves nothing in the saddle window. The conjecture `A_r ≤ (q−1)Wick_r` therefore does NOT follow
from onset/`λ₁`; it requires the **orbit-count growth** (number of `ζ`-orbits of vanishing vectors
of weight `2r`) to stay `≤ Wick_r/n` uniformly over the worst prime — the BGK/Paley wall.

## Result kind (honest)

**`new-exact-structure` + `reduces` (exact failing step pinpointed).**

`PROVES` (axiom-clean): (a) the onset law `2r < λ₁ ⟹ W_r = 0` via the reduced-difference embedding
of contributing pairs into short lattice vectors (the exact characterization generalizing
`W_2=W_3=0`); (b) the unconditional pigeonhole engine giving `λ₁ ≤ 2w₀` (short relations exist once
the `ℓ¹`-ball outgrows `p`).

`REDUCES` — the EXACT new failing step: combining (a)+(b) with the volume floor of
`_AvStick_ReducedWraparoundLattice`, the onset window `[λ₁, 2ln q]` is **non-empty and grows with
`n`** because `λ₁ ≤ 2w₀ = O(1)` (pigeonhole) while the volume lower floor `p^{2/n} → 1`. So the
quantity that must be controlled is the **orbit count of vanishing vectors with `λ₁ ≤ 2r ≤ 2 ln q`**,
NOT their onset. This is the per-shell `W_r/n ≤ Wick_r/n` bound = the saddle wall. The onset/lattice-
minimum route is therefore a CONSTANT saving, not the exponential saving the saddle needs.

Issue #444. Honesty: the open core (`A_r ≤ (q−1)Wick_r` at `r ≈ ln q`) is NOT discharged here.
-/

namespace ProximityGap.Frontier.A2OnsetLatticeMinimum

open Finset

/-! ### `ℓ¹`-weight on integer vectors -/

/-- **`ℓ¹`-weight** of an integer vector. -/
def l1 {m : ℕ} (a : Fin m → ℤ) : ℕ := ∑ j, (a j).natAbs

/-- `ℓ¹` of a difference is `≤` the sum of `ℓ¹`s (triangle inequality, coordinatewise). -/
theorem l1_sub_le {m : ℕ} (a b : Fin m → ℤ) :
    l1 (fun j => a j - b j) ≤ l1 a + l1 b := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  calc (a j - b j).natAbs ≤ (a j).natAbs + (-b j).natAbs := by
        simpa [sub_eq_add_neg] using Int.natAbs_add_le (a j) (-b j)
    _ = (a j).natAbs + (b j).natAbs := by rw [Int.natAbs_neg]

/-- `ℓ¹`-weight `0` iff zero vector. -/
theorem l1_eq_zero_iff {m : ℕ} (a : Fin m → ℤ) : l1 a = 0 ↔ a = 0 := by
  unfold l1
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h; funext j
    have := h j (Finset.mem_univ j)
    simpa [Int.natAbs_eq_zero] using this
  · intro h j _; rw [h]; simp

/-! ### The lattice membership predicate

`a ∈ L` iff the evaluation `eval g a := Σ_{j<m} a_j · g^j = 0` in `ZMod p`. -/

/-- **Evaluation** of a reduced vector at the residue `g` of `ζ_n`, in `ZMod p`. -/
def eval {m p : ℕ} (g : ZMod p) (a : Fin m → ℤ) : ZMod p :=
  ∑ j : Fin m, (a j : ZMod p) * g ^ (j : ℕ)

/-- **Membership in the reduced wraparound lattice** `L`. -/
def inLattice {m p : ℕ} (g : ZMod p) (a : Fin m → ℤ) : Prop := eval g a = 0

/-- `eval` is additive in the vector: `eval g (a − b) = eval g a − eval g b`. -/
theorem eval_sub {m p : ℕ} (g : ZMod p) (a b : Fin m → ℤ) :
    eval g (fun j => a j - b j) = eval g a - eval g b := by
  unfold eval
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

/-- **`L` is closed under differences** (it is a subgroup): if `a, b ∈ L` then `a − b ∈ L`. -/
theorem inLattice_sub {m p : ℕ} (g : ZMod p) {a b : Fin m → ℤ}
    (ha : inLattice g a) (hb : inLattice g b) :
    inLattice g (fun j => a j - b j) := by
  unfold inLattice at *
  rw [eval_sub, ha, hb, sub_zero]

/-! ### (1) The onset law: contributing pairs embed into short lattice vectors

A contributing pair to the genuine excess `W_r` is a pair of `r`-tuples `v, w ∈ μ_n^r` with
`Σ v ≡ Σ w (mod p)` whose reduced difference is **nonzero** (genuine wraparound). We model the
reduced tuples abstractly as integer vectors `rv, rw` of `ℓ¹`-weight `≤ r` whose evaluations agree
(`eval g rv = eval g rw`). The difference is then a nonzero lattice vector of weight `≤ 2r`.

This is the exact embedding `W_r ↪ { nonzero a ∈ L : ℓ¹(a) ≤ 2r }`, the source of the onset law. -/

/-- **Contributing-pair ⟹ short nonzero lattice vector.** If two reduced `r`-tuples `rv, rw`
(`ℓ¹ ≤ r` each) have equal evaluation (`Σv ≡ Σw mod p`) but are distinct (genuine wraparound),
then `a := rv − rw` is a **nonzero vector of `L` with `ℓ¹(a) ≤ 2r`**. -/
theorem contributing_pair_short_lattice
    {m p r : ℕ} (g : ZMod p) (rv rw : Fin m → ℤ)
    (hrv : l1 rv ≤ r) (hrw : l1 rw ≤ r)
    (heval : eval g rv = eval g rw) (hne : rv ≠ rw) :
    inLattice g (fun j => rv j - rw j) ∧ (fun j => rv j - rw j) ≠ 0 ∧
      l1 (fun j => rv j - rw j) ≤ 2 * r := by
  refine ⟨?_, ?_, ?_⟩
  · -- in L: eval(rv − rw) = eval rv − eval rw = 0
    unfold inLattice
    rw [eval_sub, heval, sub_self]
  · -- nonzero: else rv = rw
    intro h
    apply hne
    funext j
    have : rv j - rw j = 0 := congrFun h j
    linarith
  · -- weight ≤ 2r
    calc l1 (fun j => rv j - rw j) ≤ l1 rv + l1 rw := l1_sub_le rv rw
      _ ≤ r + r := by omega
      _ = 2 * r := by ring

/-- **The onset law (sufficient direction): `2r < λ₁ ⟹ W_r = 0`.** If every nonzero lattice
vector has `ℓ¹`-weight `> 2r` (i.e. `λ₁^{ℓ¹}(L) > 2r`), then there is **no** contributing pair at
depth `r`: any two reduced `r`-tuples with equal evaluation are in fact equal. Hence `W_r = 0`.

This is the exact statement behind the proven `W_2 = W_3 = 0` (those `r` have `2r < λ₁ ≈ 9–10`). -/
theorem no_wraparound_of_below_lambda
    {m p r : ℕ} (g : ZMod p)
    (hmin : ∀ a : Fin m → ℤ, inLattice g a → a ≠ 0 → 2 * r < l1 a)
    (rv rw : Fin m → ℤ) (hrv : l1 rv ≤ r) (hrw : l1 rw ≤ r)
    (heval : eval g rv = eval g rw) :
    rv = rw := by
  by_contra hne
  obtain ⟨hin, hnz, hle⟩ := contributing_pair_short_lattice g rv rw hrv hrw heval hne
  exact absurd (hmin _ hin hnz) (by omega)

/-! ### (2) The unconditional pigeonhole upper bound on `λ₁`

If a finite set `S` of integer vectors, each of `ℓ¹`-weight `≤ w`, has `|S| > p`, then two distinct
members collide under `eval g` (a map into `ZMod p`, which has exactly `p` elements), and their
difference is a **nonzero lattice vector of `ℓ¹`-weight `≤ 2w`**. So short relations EXIST once the
`ℓ¹`-ball outgrows `p`: `λ₁^{ℓ¹}(L) ≤ 2w`. This is the upper-bound companion to the (vacuous at
prize scale) Minkowski lower bound `λ₁ ≥ p^{2/n}`. -/

/-- **Pigeonhole: more than `p` short vectors ⟹ a short nonzero relation exists.** For any finite
family `S ⊆ {a : ℓ¹(a) ≤ w}` of integer vectors with `p < |S|`, there exist distinct `a, b ∈ S`
with `eval g a = eval g b`; hence `a − b` is a nonzero lattice vector of `ℓ¹`-weight `≤ 2w`. -/
theorem exists_short_relation_of_card_gt
    {m : ℕ} (p : ℕ) [NeZero p] (g : ZMod p) (w : ℕ)
    (S : Finset (Fin m → ℤ)) (hSw : ∀ a ∈ S, l1 a ≤ w) (hcard : p < S.card) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ inLattice g (fun j => a j - b j) ∧
      (fun j => a j - b j) ≠ 0 ∧ l1 (fun j => a j - b j) ≤ 2 * w := by
  classical
  -- The map eval g : S → ZMod p has codomain of size p < |S|, so it is not injective.
  have hcardZ : (Finset.univ : Finset (ZMod p)).card = p := by
    rw [Finset.card_univ, ZMod.card]
  -- pigeonhole into a fintype
  obtain ⟨y, _hy_mem, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := S) (t := (Finset.univ : Finset (ZMod p))) (n := 1)
    (f := fun a => eval g a) (by intro a _; exact Finset.mem_univ _)
    (by rw [hcardZ, mul_one]; exact hcard)
  -- the fiber over y has ≥ 2 elements ⟹ two distinct members with equal eval
  have h2 : 1 < (S.filter (fun a => eval g a = y)).card := hy
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
  rw [Finset.mem_filter] at ha hb
  refine ⟨a, ha.1, b, hb.1, hab, ?_, ?_, ?_⟩
  · -- in L: eval(a-b) = eval a - eval b = y - y = 0
    unfold inLattice
    rw [eval_sub, ha.2, hb.2, sub_self]
  · -- nonzero
    intro h
    apply hab
    funext j
    have : a j - b j = 0 := congrFun h j
    linarith
  · -- weight
    calc l1 (fun j => a j - b j) ≤ l1 a + l1 b := l1_sub_le a b
      _ ≤ w + w := by have := hSw a ha.1; have := hSw b hb.1; omega
      _ = 2 * w := by ring

/-! ### Packaging the two-sided floor verdict (the exact reduction statement)

The onset window is `λ₁^{ℓ¹}(L) ≤ 2r ≤ 2 ln q`. The lower floor `λ₁ ≥ p^{1/m} = p^{2/n}` is the
volume bound (carried in `_AvStick_ReducedWraparoundLattice`); the upper bound `λ₁ ≤ 2w₀` is the
pigeonhole bound proved here. At prize scale `p^{2/n} → 1` so the lower floor is vacuous and the
window `[λ₁, 2 ln q]` is wide. We package the **logical verdict**: under a vacuous lower floor and a
nontrivial saddle depth, onset cannot discharge the saddle bound — the surviving obligation is the
orbit-count bound. We state it as the implication that makes the reduction explicit. -/

/-- **The reduction verdict (named).** `OnsetSavesSaddle` would say: the lattice has no nonzero
vectors of `ℓ¹`-weight `≤ 2r` at the saddle depth `r` (so `W_r = 0`). `OrbitCountWall` says: the
number of nonzero short lattice vectors at depth `r` is bounded by `Wick_r` (the saddle budget,
divided out by the `n`-factor of `_A2RelationOrbitDivByN`). The verdict is that once a short relation
exists at depth `≤ r` (which the pigeonhole forces at prize scale), `OnsetSavesSaddle` FAILS, so the
saddle bound must come from `OrbitCountWall`. -/
def OnsetSavesSaddle (m : ℕ) {p : ℕ} (g : ZMod p) (r : ℕ) : Prop :=
  ∀ a : Fin m → ℤ, inLattice g a → a ≠ 0 → 2 * r < l1 a

/-- **Pigeonhole refutes `OnsetSavesSaddle` once the ball outgrows `p` below the saddle.** If there
is a family of `> p` short vectors of weight `≤ w` with `2w ≤ 2r` (i.e. `w ≤ r`), then a nonzero
lattice vector of weight `≤ 2r` exists, so `OnsetSavesSaddle g r` is FALSE. This is the exact place
the onset route dies at prize scale: the `ℓ¹`-ball of radius `w₀ = O(1)` already exceeds `p`, while
the saddle radius is `r ≈ ln q ≫ w₀`. -/
theorem not_onsetSavesSaddle_of_card_gt
    {m : ℕ} (p : ℕ) [NeZero p] (g : ZMod p) (w r : ℕ) (hwr : w ≤ r)
    (S : Finset (Fin m → ℤ)) (hSw : ∀ a ∈ S, l1 a ≤ w) (hcard : p < S.card) :
    ¬ OnsetSavesSaddle m g r := by
  intro hsave
  obtain ⟨a, _, b, _, _, hin, hnz, hle⟩ :=
    exists_short_relation_of_card_gt p g w S hSw hcard
  have : 2 * r < l1 (fun j => a j - b j) := hsave _ hin hnz
  omega

end ProximityGap.Frontier.A2OnsetLatticeMinimum

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.A2OnsetLatticeMinimum.l1_sub_le
#print axioms ProximityGap.Frontier.A2OnsetLatticeMinimum.eval_sub
#print axioms ProximityGap.Frontier.A2OnsetLatticeMinimum.inLattice_sub
#print axioms ProximityGap.Frontier.A2OnsetLatticeMinimum.contributing_pair_short_lattice
#print axioms ProximityGap.Frontier.A2OnsetLatticeMinimum.no_wraparound_of_below_lambda
#print axioms ProximityGap.Frontier.A2OnsetLatticeMinimum.exists_short_relation_of_card_gt
#print axioms ProximityGap.Frontier.A2OnsetLatticeMinimum.not_onsetSavesSaddle_of_card_gt
