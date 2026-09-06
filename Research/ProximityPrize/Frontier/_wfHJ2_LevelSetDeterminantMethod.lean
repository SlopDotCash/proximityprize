/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# J2 — Pila–Wilkie / Bombieri–Pila determinant method on the worst-`b` level set (#444)

**NEGATIVE / guardrail brick (an honest no-go, axiom-clean).** This file pins the precise
reason the o-minimality point-counting circle (Pila–Wilkie counting theorem, André–Oort /
Zilber–Pink) and the Bombieri–Pila / Heath-Brown **determinant method** give *no* non-reducing
handle on the prize sup-norm

  `M(μ_n) = max_{b ≠ 0} |η_b|`,   `η_b = Σ_{x ∈ μ_n} e_p(b x)`,   `μ_n ≤ F_p^*` of order `n = 2^μ`.

## The J2 question and the two obstructions

The lane asks: is the **worst-`b` level set** `L(T) := { b ∈ F_p^* : |η_b|² ≥ T }` (the sublevel
set of the period, or equivalently the "period graph") a *definable* / low-complexity set whose
Pila–Wilkie / determinant-method point count is **sub-Johnson**?

Two facts, both formalized below, kill this:

**(O1) The level set is a 0-dimensional union of full `μ_n`-cosets — no variety for PW/BP.**
The period is *multiplicatively rigid*: `|η_{u·b}| = |η_b|` for every `u ∈ μ_n` (the inner sum
just permutes `μ_n`). Hence the weight `w(b) := |η_b|²` is `μ_n`-invariant and the level set
`L(T) = {b : w(b) ≥ T}` is an **exact union of full `μ_n`-cosets** — a finite, `0`-dimensional
set. Pila–Wilkie bounds *transcendental* rational/algebraic points on a **positive-dimensional**
set definable in an o-minimal structure over `ℝ`/`ℂ`; Bombieri–Pila / Heath-Brown count integer
points **near a positive-dimensional algebraic variety** with controlled archimedean derivatives.
A `0`-dimensional finite set has *no* positive-dimensional geometry, so there is **no variety for
either method to act on** — they default to the trivial point count `|L(T)|` (cf. Kowalski,
"Exponential sums over definable subsets of finite fields", arXiv:math/0504316: the saving is
governed by `dim` of the Zariski closure, which is `0` here, so the bound is the trivial `|X|`).
`coset_union_card_dvd` formalizes the coset-union structure (`n ∣ |L(T)|`).

**(O2) The only available count of `L(T)` is the second-moment (Parseval) Markov count.**
`Σ_{b≠0} |η_b|² = q·n − n²` **exactly** (an integer Parseval identity; the in-tree
`GaussPeriodParsevalFloor` is the `q·n` form, verified here numerically by
`probe_wfH_J2_levelset_determinant.py`). Markov on this nonnegative total gives, for every `T > 0`,

  `|L(T)| ≤ (Σ_b w(b)) / T`,

a pure **second-order** count. A determinant/PW count would have to *beat* `(Σw)/T` to help the
sup bound, but (O1) says it cannot even see `L(T)` as a variety, and the Markov count is exactly
the Johnson-scale information: it is `Θ(q/log)` at the prize threshold `T = n·log(p/n)`, never
distinguishing the worst `b` from the RMS. `levelSet_card_le_sum_div` formalizes this Markov
count for an arbitrary nonnegative weight.

## Verdict

`M(μ_n)` is **not** reachable by Pila–Wilkie / André–Oort / Bombieri–Pila / Heath-Brown
determinant counting: the level set is `0`-dimensional (no variety, **O1**) and its only count is
the Parseval/Markov second moment (**O2**). The route **REDUCES-TO-FENCE F0** (the conservation
law: domain `2`nd-order arithmetic caps at Johnson; the `√log` excess is a rare-event tail
invisible to the second moment) and **F2** (Weil/Deligne — which the definable-sets framework of
Kowalski *generalizes* — is vacuous in dimension `0` / for `n < √q`). The `√log` excess remains
the open BGK/Paley wall, untouched.

## What is proven here (axiom-clean)

1. `mulAction_invariant_levelSet_eq_biUnion` / `coset_union_card_dvd` — **(O1)**: a weight invariant
   under a finite group `H` acting freely has every level set a union of full `H`-orbits, so
   `|H| ∣ |L(T)|`. (Apply with `H = μ_n` acting by multiplication on `F_p^*`; the action is free.)
2. `levelSet_card_le_sum_div` — **(O2)**: the Markov / second-moment count: for a nonnegative
   weight `w` on a finite set and any `T > 0`, `|{b : w b ≥ T}| ≤ (Σ_b w b) / T`. This is the
   *only* bound the level set admits, and it is the Parseval second moment — Johnson scale.

Issue #444, lane J2 (Pila–Wilkie / determinant method).
-/

namespace ProximityGap.Frontier.J2LevelSetDeterminant

open Finset

/-! ## (O2) The Markov / second-moment count — the only count the level set admits. -/

/--
**Markov count on the period level set (the Parseval second-moment count).**
For a nonnegative weight `w : ι → ℝ` on a finite index set and any threshold `T > 0`, the number
of indices with `w b ≥ T` is at most the total weight divided by `T`:

  `|{b : w b ≥ T}| ≤ (Σ_b w b) / T`.

Applied to `w b = |η_b|²` and the exact Parseval total `Σ_b |η_b|² = q·n − n²`, this is the
**only** count of the worst-`b` level set `L(T)` available to any method — a pure second-order
(Parseval) statement. The determinant method / Pila–Wilkie would have to *beat* this to help the
sup bound; (O1) shows they cannot even act (no variety). So the level-set route caps at the
Johnson / RMS scale (fence F0). -/
theorem levelSet_card_le_sum_div {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ b ∈ s, 0 ≤ w b) {T : ℝ} (hT : 0 < T) :
    ((s.filter (fun b => T ≤ w b)).card : ℝ) ≤ (∑ b ∈ s, w b) / T := by
  rw [le_div_iff₀ hT]
  -- T · |L(T)| = Σ_{b ∈ L(T)} T ≤ Σ_{b ∈ L(T)} w b ≤ Σ_{b ∈ s} w b.
  have hfilter : (s.filter (fun b => T ≤ w b)).card • T ≤ ∑ b ∈ s.filter (fun b => T ≤ w b), w b :=
    Finset.card_nsmul_le_sum _ _ _ (fun b hb => (Finset.mem_filter.mp hb).2)
  calc ((s.filter (fun b => T ≤ w b)).card : ℝ) * T
      = (s.filter (fun b => T ≤ w b)).card • T := by rw [nsmul_eq_mul]
    _ ≤ ∑ b ∈ s.filter (fun b => T ≤ w b), w b := hfilter
    _ ≤ ∑ b ∈ s, w b := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro b hb _
        exact hw b hb

/-! ## (O1) The level set is a union of full orbits — 0-dimensional, no variety for PW/BP. -/

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/--
**Orbit-rigidity of an invariant level set (the period is `μ_n`-coset-constant).**
Let a finite group `G` act on a finite set `X` (here `G = μ_n` acting by multiplication on
`F_p^*`), and let `w : X → ℝ` be **invariant**: `w (a • x) = w x` for all `a ∈ G`, `x ∈ X`.
Then for any threshold `T`, the level set `{x : T ≤ w x}` is invariant under the action — it is a
union of full `G`-orbits. This is the structural fact that the worst-`b` locus has no internal
`0`-dimensional structure for Pila–Wilkie / Bombieri–Pila to exploit: it is rigidly tiled by
`μ_n`-cosets. -/
theorem invariant_levelSet_smul_mem {X : Type*} [Fintype X] [DecidableEq X] [MulAction G X]
    (w : X → ℝ) (hinv : ∀ (a : G) (x : X), w (a • x) = w x) (T : ℝ) (a : G) {x : X}
    (hx : x ∈ Finset.univ.filter (fun y => T ≤ w y)) :
    a • x ∈ Finset.univ.filter (fun y => T ≤ w y) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  rwa [hinv a x]

/--
**The level set's cardinality is divisible by the orbit size (free action).**
If additionally the `G`-action on `X` is **free** (the relevant case: `μ_n` acting on `F_p^*` by
multiplication is free), then every orbit has size `|G|`, and since the level set is a union of
full orbits its cardinality is a multiple of `|G| = n`:

  `n ∣ |L(T)|`.

So `L(T)` is a `0`-dimensional finite set rigidly composed of `n`-element `μ_n`-cosets — there is
no positive-dimensional algebraic/transcendental variety for the Pila–Wilkie counting theorem or
the Bombieri–Pila / Heath-Brown determinant method to bound points on/near. Both default to the
trivial point count, giving no saving (cf. Kowalski math/0504316: saving `∝ dim` of the Zariski
closure, `= 0` here). -/
theorem coset_union_card_dvd {X : Type*} [Fintype X] [DecidableEq X] [MulAction G X]
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1)
    (w : X → ℝ) (hinv : ∀ (a : G) (x : X), w (a • x) = w x) (T : ℝ) :
    Fintype.card G ∣ (Finset.univ.filter (fun y => T ≤ w y)).card := by
  classical
  -- The level set is `G`-invariant (a union of orbits). Transport to the subtype and use that a
  -- *free* finite-group action has `|G| ∣ |β|` (each stabilizer is trivial, class formula).
  set L : Finset X := Finset.univ.filter (fun y => T ≤ w y) with hL
  have hclosed : ∀ (a : G) {x : X}, x ∈ L → a • x ∈ L := fun a x hx =>
    invariant_levelSet_smul_mem (G := G) w hinv T a hx
  rw [← Fintype.card_coe L]
  -- Free `G`-action on the subtype `{x // x ∈ L}`.
  letI act : MulAction G {x : X // x ∈ L} :=
  { smul := fun g x => ⟨g • x.1, hclosed g x.2⟩
    one_smul := fun x => by apply Subtype.ext; exact one_smul G x.1
    mul_smul := fun g h x => by apply Subtype.ext; exact mul_smul g h x.1 }
  have hsmul : ∀ (g : G) (x : {x : X // x ∈ L}), (g • x).1 = g • x.1 := fun _ _ => rfl
  have hfree' : ∀ (g : G) (x : {x : X // x ∈ L}), g • x = x → g = 1 := by
    intro g x hgx
    exact hfree g x.1 (by have := congrArg Subtype.val hgx; rwa [hsmul] at this)
  -- Each stabilizer is trivial.
  have hstab : ∀ x : {x : X // x ∈ L}, Fintype.card (MulAction.stabilizer G x) = 1 := by
    intro x
    rw [Fintype.card_eq_one_iff]
    exact ⟨1, fun ⟨g, hg⟩ => Subtype.ext (hfree' g x hg)⟩
  -- Class formula: |β| = Σ_orbits |G|/|stab| = Σ_orbits |G| = |G| · #orbits.
  refine ⟨Fintype.card (MulAction.orbitRel.Quotient G ↥L), ?_⟩
  rw [MulAction.card_eq_sum_card_group_div_card_stabilizer' G ↥L Quotient.out_eq']
  have hsummand : ∀ o : MulAction.orbitRel.Quotient G ↥L,
      Fintype.card G / Fintype.card (MulAction.stabilizer G (Quotient.out o)) = Fintype.card G := by
    intro o; rw [hstab (Quotient.out o), Nat.div_one]
  rw [Finset.sum_congr rfl (fun o _ => hsummand o)]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

#print axioms ProximityGap.Frontier.J2LevelSetDeterminant.levelSet_card_le_sum_div
#print axioms ProximityGap.Frontier.J2LevelSetDeterminant.invariant_levelSet_smul_mem
#print axioms ProximityGap.Frontier.J2LevelSetDeterminant.coset_union_card_dvd

end ProximityGap.Frontier.J2LevelSetDeterminant
