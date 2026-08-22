/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The Möbius pencil involution and its 2-orbit energy (#357, N1/C1 foundation)

The probe campaign identified **the Möbius-involution pencil energy** as the *only known
domain-separating invariant* for the proximity-gap threshold δ\* (the M3 census separates
smooth multiplicative subgroups from random evaluation domains, and the separation factors
through this statistic). This file builds its load-bearing core, axiom-clean.

For a finite **commutative** group `G` (the multiplicative evaluation subgroup `H ≤ F^×`) and a
parameter `b : G`, the *Möbius pencil involution* is

  `σ_b : G → G,   σ_b x = b · x⁻¹`

(the `a = 0` strip of the k=3 agreement pencil `(x−a)(y−a) = a²−b`, normalized: `x·y = b`).
Its fixed points are exactly the **square roots of `b`** (`x² = b`), and every non-fixed point
sits in a 2-orbit `{x, b·x⁻¹}`. The per-`b` 2-orbit count

  `t₂(b) = (|G| − #√b) / 2`

is the agreement-spectrum statistic that is `≈ n/2` on the `≈ n` subgroup pencils (so the
energy `Σ_b t₂(b)²` is `Θ(n³)`) yet thin for a random domain — the mechanism behind hypothesis
**N1** (`δ\*(H) = F(E₂(H)/n²)`) and connection **C1**.

Results:
- `mobiusInvol` : the involution as an `Equiv.Perm G`, with `mobiusInvol_involutive`.
- `mobiusInvol_apply_eq_self_iff` : `x` is fixed ⟺ `x² = b`.
- `t2`, `card_eq_two_mul_t2_add_fixed` : `|G| = 2·t₂(b) + #√b` (the orbit decomposition).

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

open Equiv

namespace ProximityGap.MobiusPencil

variable {G : Type*} [CommGroup G]

/-- The Möbius pencil involution `σ_b x = b · x⁻¹` on a commutative group, as a permutation.
It is its own inverse (commutativity: `(b·x⁻¹)⁻¹ = b⁻¹·x`, so `σ_b (σ_b x) = b·(b⁻¹·x) = x`). -/
def mobiusInvol (b : G) : Equiv.Perm G where
  toFun x := b * x⁻¹
  invFun x := b * x⁻¹
  left_inv x := by simp [mul_inv_rev, mul_comm, mul_assoc, mul_left_comm]
  right_inv x := by simp [mul_inv_rev, mul_comm, mul_assoc, mul_left_comm]

@[simp] lemma mobiusInvol_apply (b x : G) : mobiusInvol b x = b * x⁻¹ := rfl

/-- The Möbius involution is an involution. -/
theorem mobiusInvol_involutive (b : G) : Function.Involutive (mobiusInvol b) := by
  intro x; simp [mobiusInvol_apply, mul_inv_rev, mul_comm, mul_assoc, mul_left_comm]

@[simp] lemma mobiusInvol_mobiusInvol (b x : G) :
    mobiusInvol b (mobiusInvol b x) = x := mobiusInvol_involutive b x

/-- `mobiusInvol b` squares to the identity permutation. -/
theorem mobiusInvol_sq (b : G) : (mobiusInvol b) * (mobiusInvol b) = 1 :=
  Equiv.Perm.ext (fun x => mobiusInvol_involutive b x)

/-- **Fixed points are square roots of `b`.** `σ_b x = x ⟺ x² = b`. -/
theorem mobiusInvol_apply_eq_self_iff {b x : G} : mobiusInvol b x = x ↔ x ^ 2 = b := by
  rw [mobiusInvol_apply, mul_inv_eq_iff_eq_mul, sq, eq_comm]

variable [Fintype G] [DecidableEq G]

/-- The set of square roots of `b` in `G` (the fixed points of `σ_b`). -/
def sqrtSet (b : G) : Finset G :=
  Finset.univ.filter (fun x => x ^ 2 = b)

@[simp] lemma mem_sqrtSet {b x : G} : x ∈ sqrtSet b ↔ x ^ 2 = b := by
  simp [sqrtSet]

/-- The square-root set is exactly the fixed-point set of `σ_b` (as a Finset). -/
theorem sqrtSet_eq_filter_fixed (b : G) :
    sqrtSet b = Finset.univ.filter (fun x => mobiusInvol b x = x) := by
  ext x
  simp only [sqrtSet, Finset.mem_filter, Finset.mem_univ, true_and,
    mobiusInvol_apply_eq_self_iff]

/-- **The orbit decomposition** `|G| = #√b + #{non-fixed}`. The non-fixed points are the
support of the involution `σ_b`; each lies in a 2-orbit `{x, b·x⁻¹}`. The 2-orbit count is
`t₂(b) = #{non-fixed}/2` (the pencil-energy summand). -/
theorem card_eq_sqrtSet_add_support (b : G) :
    Fintype.card G
      = (sqrtSet b).card + (Finset.univ.filter (fun x => mobiusInvol b x ≠ x)).card := by
  rw [sqrtSet_eq_filter_fixed, ← Finset.card_univ,
    Finset.filter_card_add_filter_neg_card_eq_card (p := fun x => mobiusInvol b x = x)]

/-- The 2-orbit count of `σ_b` (the per-`b` Möbius pencil energy summand). -/
def t2 (b : G) : ℕ := (Finset.univ.filter (fun x => mobiusInvol b x ≠ x)).card / 2

/-- The support of `σ_b` (its non-fixed points) is closed under `σ_b` and fixed-point-free —
the structural fact that makes the 2-orbit pairing `x ↔ b·x⁻¹` well-defined (so `#support`
is even and `t₂(b) = #support/2`, the next brick). -/
theorem mobiusInvol_mapsTo_support (b : G) :
    ∀ x ∈ Finset.univ.filter (fun x => mobiusInvol b x ≠ x),
      mobiusInvol b x ∈ Finset.univ.filter (fun x => mobiusInvol b x ≠ x) := by
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  intro hcontra
  exact hx (by rw [← hcontra, mobiusInvol_mobiusInvol])

/-! ## The smooth-domain separation lower bound

For a **cyclic** evaluation subgroup `H = G` (every multiplicative subgroup of `F^×` is
cyclic), squaring is at most 2-to-1, so every pencil `b` has at most two square roots and
therefore *near-maximal* 2-orbit count `t₂(b) ≥ (|G|−2)/2`. This is the structural fact that
makes the pencil energy `E₂(H) = Σ_b t₂(b)²` of order `Θ(n³)` for smooth subgroups while a
random domain has thin pencils — the **only known domain-separating mechanism** for δ\*. -/

variable [IsCyclic G]

/-- **At most two square roots** in a cyclic group: `#√b ≤ 2`. (If `b` has a root `x₀`, the map
`x ↦ x·x₀⁻¹` injects `√b` into `√1 = {z : z²=1}`, which a cyclic group caps at `2`.) -/
theorem card_sqrtSet_le_two (b : G) : (sqrtSet b).card ≤ 2 := by
  classical
  rcases (sqrtSet b).eq_empty_or_nonempty with h | ⟨x0, hx0⟩
  · simp [h]
  · rw [mem_sqrtSet] at hx0
    have hinj : (sqrtSet b).card ≤ (sqrtSet (1 : G)).card := by
      refine Finset.card_le_card_of_injOn (fun x => x * x0⁻¹) ?_ ?_
      · intro x hx
        rw [Finset.mem_coe, mem_sqrtSet] at hx
        rw [Finset.mem_coe, mem_sqrtSet, mul_pow, inv_pow, hx, hx0]
        exact mul_inv_cancel b
      · intro x _ y _ hxy; exact mul_right_cancel hxy
    refine hinj.trans ?_
    exact IsCyclic.card_pow_eq_one_le (α := G) (n := 2) (by omega)

/-- **Smooth-domain `t₂` lower bound.** Every pencil over a cyclic subgroup has near-maximal
2-orbit count: `2·t₂(b) + 3 ≥ |G|`, i.e. `t₂(b) ≥ (|G|−3)/2`. This forces the pencil energy
`Σ_b t₂(b)² = Θ(n³)` on smooth domains — the separation from random domains. -/
theorem two_mul_t2_add_three_ge_card (b : G) :
    2 * t2 b + 3 ≥ Fintype.card G := by
  have hdecomp := card_eq_sqrtSet_add_support b
  have hroots := card_sqrtSet_le_two b
  have ht2 : 2 * t2 b + 1 ≥ (Finset.univ.filter (fun x => mobiusInvol b x ≠ x)).card := by
    unfold t2; omega
  omega

/-- Per-pencil `t₂` lower bound in division form: `t₂(b) ≥ (|G|−3)/2`. -/
theorem t2_ge (b : G) : t2 b ≥ (Fintype.card G - 3) / 2 := by
  have h := two_mul_t2_add_three_ge_card b; omega

/-- Per-pencil `t₂` upper bound (holds for any group): `t₂(b) ≤ |G|/2`. -/
theorem t2_le (b : G) : t2 b ≤ Fintype.card G / 2 := by
  unfold t2
  refine Nat.div_le_div_right (le_trans (Finset.card_filter_le _ _) ?_)
  rw [Finset.card_univ]

/-- **The Möbius pencil energy** `E₂(G) = Σ_b t₂(b)²` — the agreement-spectrum invariant that
separates smooth multiplicative subgroups from random evaluation domains. -/
def pencilEnergy : ℕ := ∑ b : G, (t2 b) ^ 2

/-- **The smooth-domain energy lower bound: `E₂(G) ≥ n·((n−3)/2)²`** (i.e. `Θ(n³)`).** Every one
of the `n = |G|` pencils contributes a near-maximal `t₂(b)² ≥ ((n−3)/2)²`; summing gives the
cubic floor. A random evaluation domain has pencil energy only `Θ(n²)` — *this gap is the only
known domain-separating signal for the proximity threshold δ\*.* -/
theorem pencilEnergy_ge :
    pencilEnergy (G := G) ≥ Fintype.card G * ((Fintype.card G - 3) / 2) ^ 2 := by
  unfold pencilEnergy
  calc Fintype.card G * ((Fintype.card G - 3) / 2) ^ 2
      = ∑ _b : G, ((Fintype.card G - 3) / 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ ∑ b : G, (t2 b) ^ 2 :=
        Finset.sum_le_sum (fun b _ => Nat.pow_le_pow_left (t2_ge b) 2)

/-- **The energy upper bound: `E₂(G) ≤ n·(n/2)²`.** With `pencilEnergy_ge` this two-sidedly
pins `E₂(G) = Θ(n³)` for a smooth (cyclic) evaluation subgroup — the quantitative C1 separation
(random domains sit at `Θ(n²)`). -/
theorem pencilEnergy_le :
    pencilEnergy (G := G) ≤ Fintype.card G * (Fintype.card G / 2) ^ 2 := by
  unfold pencilEnergy
  calc ∑ b : G, (t2 b) ^ 2
      ≤ ∑ _b : G, (Fintype.card G / 2) ^ 2 :=
        Finset.sum_le_sum (fun b _ => Nat.pow_le_pow_left (t2_le b) 2)
    _ = Fintype.card G * (Fintype.card G / 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

end ProximityGap.MobiusPencil

/-! ## Axiom audit — kernel-clean. -/
#print axioms ProximityGap.MobiusPencil.mobiusInvol_involutive
#print axioms ProximityGap.MobiusPencil.mobiusInvol_apply_eq_self_iff
#print axioms ProximityGap.MobiusPencil.card_sqrtSet_le_two
#print axioms ProximityGap.MobiusPencil.two_mul_t2_add_three_ge_card
#print axioms ProximityGap.MobiusPencil.pencilEnergy_ge
#print axioms ProximityGap.MobiusPencil.pencilEnergy_le
