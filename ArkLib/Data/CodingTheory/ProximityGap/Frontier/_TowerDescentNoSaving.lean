/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._TwoPowerRootDescent

/-!
# The antipodal-tower descent gives NO list saving by itself (#444 / #407)

`_TwoPowerRootDescent.rootCount_descent_two_pow` proved the **exact** prime-independent root-count
descent for the off-BGK antipodal-tower list route: over a field `F` with a primitive `2^μ`-th root,
for any octave `s ≤ μ` and any base polynomial `Q`,

  `rootCount(Q.comp (X^{2^s}), μ_{2^μ})  =  2^s · rootCount(Q, μ_{2^{μ-s}})`.        (★)

The off-BGK list route's hope (#444 c.97) is that this antipodal self-similarity *converts* into a
sub-trivial sup/list bound on the thin group `μ_{2^μ}`. This file proves the precise **constraint
lemma** — the EXACT amplification factor `2^s` cancels the degree-halving, so the descent is a
*saving-preserving identity, not a saving-creating mechanism*:

* `natDegree_comp_X_pow` : `(Q.comp (X^m)).natDegree = m · Q.natDegree` (the degree-`m` substitution
  multiplies the degree by `m`). At `m = 2^s` this is the degree side of (★).
* `card_filter_isRoot_le_natDegree` : the **trivial bound** — on any finite evaluation set `S`, a
  nonzero polynomial has at most `natDegree` roots (the agreement-Fisher single-codeword ceiling).
* `towerDescent_no_saving` : the descent transfers the trivial base bound to the trivial tower
  bound **with equality of scale**: for `Q ≠ 0`,
  `rootCount(Q.comp(X^{2^s}), μ_{2^μ}) ≤ 2^s · Q.natDegree = (Q.comp(X^{2^s})).natDegree`.
  The `2^s` fiber amplification of (★) *exactly equals* the degree multiplier, so the descent never
  beats the polynomial's own trivial degree bound — it manufactures **no** list saving.
* `towerDescent_saving_iff` : the **sharp dichotomy** (the mechanism). For `Q ≠ 0`, the tower root
  count is *strictly* below its trivial degree bound on `μ_{2^μ}` **iff** the base root count is
  strictly below `Q.natDegree` on `μ_{2^{μ-s}}`:
  `rootCount(tower, μ_{2^μ}) < (tower).natDegree  ↔  rootCount(Q, base) < Q.natDegree`.
  Any list saving on the thin group is *equivalent* to a saving already present at the base rung —
  the descent neither creates nor destroys sub-triviality. So the open core of the off-BGK route is
  EXACTLY the **base-rung** list bound (the deepest rung `μ_1`/`μ_2` is a fixed finite cyclotomic
  object, `p`-independent and constant in `n` at fixed dyadic ratio); antipodal symmetry alone buys
  nothing past the base.

## Honest scope (rules 1, 3, 4, 6)

This is a **refutation-with-mechanism** (rule 4 win): it precisely walls the hope that the antipodal
tower self-similarity *itself* yields a sub-trivial `μ_n` list. It does NOT close CORE — it sharpens
the off-BGK route to its true residual (the base-rung list), proving the descent step is
saving-neutral. NOT thinness-essential (the descent identity holds for the `2`-power map on any
`2^μ`-th roots of unity, char-free); thinness enters only through *which* base bound holds, exactly
as in the rest of the campaign. CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN.

Probe `scripts/probes/probe_tower_listdescent_amplification.py`: (★) holds exactly on PROPER `μ_n`
(`n = 2^a`, `n | p−1`, `p ≫ n^3`, multi-prime, never `n = q−1`) at every octave, and the `2^s`
fiber factor is observed to exactly cancel the degree halving.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issues #444, #407.
-/

open Polynomial

namespace ProximityGap.Frontier.TowerDescentNoSaving

/-! ## Degree of the tower substitution -/

variable {R : Type*}

/-- **The degree of the `X^m` substitution.** `(Q.comp (X^m)).natDegree = m · Q.natDegree`.
The degree-`m` substitution `X ↦ X^m` multiplies every degree by `m`; this is the degree side of the
antipodal-tower descent (the `2^s`-fold octave is `m = 2^s`). -/
theorem natDegree_comp_X_pow [Semiring R] [NoZeroDivisors R] [Nontrivial R] (Q : R[X]) (m : ℕ) :
    (Q.comp (X ^ m)).natDegree = m * Q.natDegree := by
  rw [natDegree_comp, natDegree_X_pow, Nat.mul_comm]

/-! ## The trivial (single-codeword) root bound on any evaluation set -/

variable {F : Type*} [Field F]

open Classical in
/-- **The trivial root bound.** A nonzero polynomial has at most `natDegree` roots in any finite
evaluation set `S` (the agreement set of a single codeword embeds into the roots of the difference;
`card_roots'`). This is the bound the antipodal-tower descent must *beat* to produce a saving. -/
theorem card_filter_isRoot_le_natDegree {p : F[X]} (hp : p ≠ 0) (S : Finset F) :
    (S.filter fun x => p.IsRoot x).card ≤ p.natDegree := by
  have hss : (S.filter fun x => p.IsRoot x) ⊆ p.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    exact (Finset.mem_filter.mp hx).2
  calc (S.filter fun x => p.IsRoot x).card
      ≤ p.roots.toFinset.card := Finset.card_le_card hss
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' _

/-! ## The no-saving constraint lemma -/

open Classical in
/-- **The antipodal-tower descent gives no saving by itself.** For a nonzero base polynomial `Q`
over a field `F` with a primitive `2^μ`-th root of unity, and any octave `s ≤ μ`, the tower root
count on the thin group `μ_{2^μ}` is bounded by the **trivial degree bound of the tower polynomial
itself**:

  `rootCount(Q.comp(X^{2^s}), μ_{2^μ})  ≤  2^s · Q.natDegree  =  (Q.comp(X^{2^s})).natDegree`.

The exact `2^s` fiber amplification of the descent equality (★) *equals* the degree multiplier of
the `X^{2^s}` substitution — so the descent transfers the trivial base bound back to the trivial
tower bound, beating nothing. Antipodal self-similarity alone manufactures no list saving. -/
theorem towerDescent_no_saving {μ s : ℕ} (hs : s ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) {Q : F[X]} (hQ : Q ≠ 0) :
    ((nthRootsFinset (2 ^ μ) (1 : F)).filter
        (fun α => (Q.comp (X ^ (2 ^ s))).IsRoot α)).card
      ≤ (Q.comp (X ^ (2 ^ s))).natDegree := by
  -- (★): the tower root count is exactly `2^s ·` the base root count.
  have hstar : ((nthRootsFinset (2 ^ μ) (1 : F)).filter
        (fun α => (Q.comp (X ^ (2 ^ s))).IsRoot α)).card
      = 2 ^ s * ((nthRootsFinset (2 ^ (μ - s)) (1 : F)).filter (fun β => Q.IsRoot β)).card :=
    TwoPowerRootDescent.rootCount_descent_two_pow hs hζ Q
  -- The base root count is at most `Q.natDegree` (trivial bound on the base group).
  have hbase : ((nthRootsFinset (2 ^ (μ - s)) (1 : F)).filter (fun β => Q.IsRoot β)).card
      ≤ Q.natDegree := card_filter_isRoot_le_natDegree hQ _
  -- Multiply by `2^s` and identify with the tower degree.
  calc ((nthRootsFinset (2 ^ μ) (1 : F)).filter
          (fun α => (Q.comp (X ^ (2 ^ s))).IsRoot α)).card
      = 2 ^ s * ((nthRootsFinset (2 ^ (μ - s)) (1 : F)).filter (fun β => Q.IsRoot β)).card :=
        hstar
    _ ≤ 2 ^ s * Q.natDegree := Nat.mul_le_mul_left _ hbase
    _ = (Q.comp (X ^ (2 ^ s))).natDegree := (natDegree_comp_X_pow Q (2 ^ s)).symm

open Classical in
/-- **The sharp dichotomy (the mechanism).** For a nonzero base `Q`, the tower root count is
*strictly* below its own trivial degree bound on the thin group `μ_{2^μ}` **iff** the base count
is *strictly* below `Q.natDegree` on the base group `μ_{2^{μ−s}}`:

  `rootCount(tower, μ_{2^μ}) < (tower).natDegree  ↔  rootCount(Q, μ_{2^{μ−s}}) < Q.natDegree`.

Both sides scale by the same factor `2^s` (the fiber amplification = the degree multiplier), so the
descent is *saving-preserving*: any sub-trivial list on the thin group is equivalent to a saving
already present at the base rung. The descent neither creates nor destroys it — the entire open
content of the off-BGK route is the **base-rung** list bound. -/
theorem towerDescent_saving_iff {μ s : ℕ} (hs : s ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) {Q : F[X]} (hQ : Q ≠ 0) (hpos : 0 < 2 ^ s) :
    ((nthRootsFinset (2 ^ μ) (1 : F)).filter
        (fun α => (Q.comp (X ^ (2 ^ s))).IsRoot α)).card < (Q.comp (X ^ (2 ^ s))).natDegree
      ↔ ((nthRootsFinset (2 ^ (μ - s)) (1 : F)).filter (fun β => Q.IsRoot β)).card
          < Q.natDegree := by
  have hstar : ((nthRootsFinset (2 ^ μ) (1 : F)).filter
        (fun α => (Q.comp (X ^ (2 ^ s))).IsRoot α)).card
      = 2 ^ s * ((nthRootsFinset (2 ^ (μ - s)) (1 : F)).filter (fun β => Q.IsRoot β)).card :=
    TwoPowerRootDescent.rootCount_descent_two_pow hs hζ Q
  rw [hstar, natDegree_comp_X_pow Q (2 ^ s)]
  exact Nat.mul_lt_mul_left hpos

end ProximityGap.Frontier.TowerDescentNoSaving

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.Frontier.TowerDescentNoSaving.natDegree_comp_X_pow
#print axioms ProximityGap.Frontier.TowerDescentNoSaving.card_filter_isRoot_le_natDegree
#print axioms ProximityGap.Frontier.TowerDescentNoSaving.towerDescent_no_saving
#print axioms ProximityGap.Frontier.TowerDescentNoSaving.towerDescent_saving_iff
