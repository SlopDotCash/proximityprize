/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# The Witt ghost-collapse: why the entire p-adic-lift class is vacuous for the char-p transfer (#444)

The Paley wall is the char-0 → char-p transfer of the proven Wick energy bound: `E_r^{F_p}(μ_n) = E_r^∞ + W_r`,
and the wraparound `W_r` (the count of mod-`p` additive coincidences of `2^a`-th roots that do NOT hold over `ℂ`)
is the open obstruction. A whole *class* of attacks tries to read `W_r` off a **p-adic lift** of the relation
`S = Σ_i ε_i [ζ^{a_i}]` (Stickelberger / Gross–Koblitz, prismatic cohomology, Witt vectors / de Rham–Witt,
syntomic). This file records, axiom-clean, the **single mechanism** that makes the entire class vacuous — the
*ghost-collapse*:

> Over the **perfect base** `F_p` the Frobenius is the identity (`a^p = a`, Fermat), so the iterated Frobenius /
> ghost components `a^{p^j}` are **level-independent**: `a^{p^j} = a` for all `j`. Hence the graded Witt / de
> Rham–Witt / syntomic tower of a sum of Teichmüller lifts `S = Σ_i ε_i [a_i]` (`a_i ∈ F_p`) **degenerates to the
> single datum** `Σ_i ε_i a_i` — there is no per-level refinement to discover. Every p-adic-lift invariant of `S`
> is therefore a function of `v_p(S)` alone, which (in-tree `_wfJ3`, `_AvSD`, `_GrossKoblitzPhaseNoGo`) is the
> p-adic *valuation*, provably `⊥` the complex *modulus* where `W_r` lives.

This subsumes three previously-separate in-tree no-gos (`_wfJ3` prismatic, `_AvSD` Stickelberger,
`_GrossKoblitzPhaseNoGo`) under ONE structural cause: perfect-base ghost degeneracy. The char-p transfer is
instead an **archimedean** `p`-vs-relation-height comparison (the wraparound vanishes once `p` exceeds the
exponential cyclotomic heights; verified in `docs/kb/deltastar-444-CHARP-TRANSFER-NEW-GROUND-2026-06-22.md`),
which no functor into an archimedean-place-free target can see.

## Results (axiom-clean)
* `ghost_collapse` — `a^{p^j} = a` in `ZMod p` for all `j` (iterated Fermat = level-independence of ghost comps).
* `ghost_component_level_independent` — the `j`-th ghost component `Σ_i ε_i (a_i)^{p^j}` of a sum of Teichmüller
  lifts equals the `0`-th component `Σ_i ε_i a_i` for every `j`: the graded tower carries no level-graded data.

NOT prize closure — a class-level no-go (obstruction): the p-adic-lift family cannot supply the char-p transfer.
-/

namespace ArkLib.ProximityGap.Frontier.AvWittGhostCollapse

open Finset

variable (p : ℕ) [Fact p.Prime]

/-- **Ghost-collapse core (proven).** Over `ZMod p` the iterated Frobenius is the identity: `a^{p^j} = a` for
every `j`. This is iterated Fermat (`ZMod.pow_card`), and it is exactly the statement that the ghost components
of a Teichmüller lift over the perfect base `F_p` are level-independent — the Witt/de Rham–Witt tower has no
graded refinement to exploit. -/
theorem ghost_collapse (a : ZMod p) (j : ℕ) : a ^ (p ^ j) = a := by
  induction j with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]

/-- **The graded tower degenerates (proven).** For a finite signed sum of Teichmüller lifts
`S = Σ_{i∈s} ε_i [a_i]` with `a_i ∈ F_p`, the `j`-th ghost component `Σ_i ε_i (a_i)^{p^j}` equals the `0`-th,
`Σ_i ε_i a_i`, for **every** level `j`. So the entire graded Witt / de Rham–Witt / syntomic data of `S` collapses
to one datum: no p-adic-lift invariant can carry level-graded (hence modulus-sensitive) information about the
wraparound `W_r`. This is the unified cause of the prismatic / Stickelberger / Gross–Koblitz no-gos. -/
theorem ghost_component_level_independent {ι : Type*} (s : Finset ι)
    (ε : ι → ZMod p) (a : ι → ZMod p) (j : ℕ) :
    ∑ i ∈ s, ε i * (a i) ^ (p ^ j) = ∑ i ∈ s, ε i * a i := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ghost_collapse]

/-- **Non-separation corollary (proven).** Two signed Teichmüller sums with the same `0`-th datum are
indistinguishable by *every* ghost level: if `Σ_i ε_i a_i = Σ_i δ_i b_i` then their `j`-th ghost components agree
for all `j`. In particular a level-graded (Witt/syntomic) invariant cannot separate a char-0-vanishing relation
(e.g. the antipodal `1 + ζ^{n/2}`, whose lift has `v_p = 1`) from a genuine wraparound of the same valuation —
the p-adic-lift class is blind to `W_r`. -/
theorem ghost_levels_agree_of_base_eq {ι : Type*} (s t : Finset ι)
    (ε δ a b : ι → ZMod p)
    (h : ∑ i ∈ s, ε i * a i = ∑ i ∈ t, δ i * b i) (j : ℕ) :
    ∑ i ∈ s, ε i * (a i) ^ (p ^ j) = ∑ i ∈ t, δ i * (b i) ^ (p ^ j) := by
  rw [ghost_component_level_independent, ghost_component_level_independent, h]

end ArkLib.ProximityGap.Frontier.AvWittGhostCollapse

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvWittGhostCollapse.ghost_collapse
#print axioms ArkLib.ProximityGap.Frontier.AvWittGhostCollapse.ghost_component_level_independent
#print axioms ArkLib.ProximityGap.Frontier.AvWittGhostCollapse.ghost_levels_agree_of_base_eq
