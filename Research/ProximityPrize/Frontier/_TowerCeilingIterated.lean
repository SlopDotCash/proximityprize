/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.TowerCeiling

/-!
# The iterated tower ceiling — `V_μ ≤ 4^μ · V_0` as a THEOREM (not prose) (#407/#444)

`TowerCeiling.eta_sq_le_four` proves the **one-level** unconditional cap: if both sub-periods are
bounded by `V`, the level-up squared period satisfies `‖η_G(b)‖² ≤ 4V`.  Its docstring then says, AS
PROSE ONLY: *"Iterating from the bottom (`V_0 = 1`, the trivial subgroup) gives only
`V_μ ≤ 4^μ = n²`, the trivial `M ≤ n` — no cancellation."*  No file turns that iteration into a
theorem.  This file does, closing the same prose-vs-theorem gap that `OrbitSizeR5HalfOrder` /
`_PhaseAlignmentReality` flagged for their own faces.

## What is proved (axiom-clean, no `sorry`)

Given a **dyadic chain** `H : ℕ → Finset F` with, at every level `i`, a non-zero dilation parameter
`ω i ≠ 0` such that `H (i+1) = H i ∪ (ω i) • H i` is the *disjoint* coset doubling, and a *uniform*
base sup-norm bound `∀ c, ‖η_{H 0}(c)‖² ≤ V`:

> **`tower_ceiling_iterated`** — `∀ b, ‖η_{H μ}(b)‖² ≤ 4^μ · V` for every level `μ`.

The proof is induction on `μ` through the one-level cap `eta_sq_le_four`.  The bound must be carried
*uniformly in the frequency* `c` (not just at one `b`), because each level pulls in the parent period
at the *shifted* frequency `ω·b`; the induction hypothesis is therefore phrased `∀ c`.

> **`tower_ceiling_base_one`** — the canonical instance `V = 1`: a *singleton* base subgroup
> (`H 0 = {z}`, so `‖η_{H 0}(c)‖ ≤ 1` for every `c`) gives `‖η_{H μ}(b)‖² ≤ 4^μ`, i.e. `‖η‖ ≤ 2^μ = n`.
> This is the explicit trivial `M ≤ n` ceiling, no cancellation — exactly the structural cap the
> descent program (`TowerCeiling`, `_DyadicParallelogramInvariant`) keeps citing in prose.

## Honest scope (rules 1, 3, 4, 6 + ASYMPTOTIC/cliff GUARD)

This is the **trivial deterministic ceiling**, NOT a cancellation result.  It says nothing about the
prize `√n`-cancellation: the iterated cap is `4^μ = n²`, i.e. `M ≤ n`, the no-cancellation bound that
needs no BGK/Weil input.  As `TowerCeiling`'s docstring records, the *only* source of improvement is
the per-level twist `‖η_H(b) − η_H(ωb)‖²` at the worst frequency, whose uniform-in-`μ` positivity is
itself one-level BGK — this theorem drops that twist (the `eta_sq_le_four` step is the dropped-twist
inequality) and therefore *cannot* and *does not* see any cancellation.  Thinness is irrelevant to it
(it holds for any disjoint dyadic coset chain, thick or thin), so it makes NO thinness-essential,
capacity, beyond-Johnson, sub-linear, or cliff-at-n/2 claim.  It is a NON-MOMENT structural-cardinality
brick, EXTEND-proven on the in-tree one-level cap (`eta_sq_le_four`), giving the citable iterated form
of a fact previously stated only as prose.  CORE `M(μ_n) ≤ C·√(n·log(p/n))` is UNCHANGED / OPEN.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.  Issue #407 / #444.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.TowerCeiling

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The iterated tower ceiling.**  A dyadic chain `H` with disjoint coset-doubling at every level
(`H (i+1) = H i ∪ (ω i)•H i`, `ω i ≠ 0`) and a *uniform* base sup-norm bound `‖η_{H 0}(c)‖² ≤ V` for
all `c` satisfies the unconditional `4^μ`-cap at every level:

> `‖η_{H μ}(b)‖² ≤ 4^μ · V`  for all `b`.

Induction on `μ` via the one-level dropped-twist cap `eta_sq_le_four`.  No cancellation — `4^μ` is the
trivial ceiling. -/
theorem tower_ceiling_iterated {ψ : AddChar F ℂ} {H : ℕ → Finset F} {ω : ℕ → F} {V : ℝ}
    (hω : ∀ i, ω i ≠ 0)
    (hchain : ∀ i, H (i + 1) = H i ∪ (H i).image (fun x => ω i * x))
    (hdisj : ∀ i, Disjoint (H i) ((H i).image (fun x => ω i * x)))
    (hbase : ∀ c, ‖eta ψ (H 0) c‖ ^ 2 ≤ V) :
    ∀ μ : ℕ, ∀ b : F, ‖eta ψ (H μ) b‖ ^ 2 ≤ 4 ^ μ * V := by
  intro μ
  induction μ with
  | zero => intro b; simpa using hbase b
  | succ k ih =>
      intro b
      -- one level up: η_{H (k+1)} bounded by 4·(level-k bound), uniformly in the frequency
      have hcap := eta_sq_le_four (ψ := ψ) (G := H (k + 1)) (H := H k) (ω := ω k)
        (hω k) (hchain k) (hdisj k) b (V := 4 ^ k * V) (ih b) (ih (ω k * b))
      calc ‖eta ψ (H (k + 1)) b‖ ^ 2
          ≤ 4 * (4 ^ k * V) := hcap
        _ = 4 ^ (k + 1) * V := by ring

/-- **Canonical base-`1` instance (the explicit `M ≤ n` trivial ceiling).**  If the base of the chain
is bounded by `1` at every frequency — e.g. `H 0` a singleton, where `‖η_{H 0}(c)‖ = ‖ψ(c·z)‖ = 1` —
then `‖η_{H μ}(b)‖² ≤ 4^μ` for all `b`, i.e. `‖η_{H μ}(b)‖ ≤ 2^μ = |H μ|`.  This is the
no-cancellation structural cap the dyadic descent program cites in prose. -/
theorem tower_ceiling_base_one {ψ : AddChar F ℂ} {H : ℕ → Finset F} {ω : ℕ → F}
    (hω : ∀ i, ω i ≠ 0)
    (hchain : ∀ i, H (i + 1) = H i ∪ (H i).image (fun x => ω i * x))
    (hdisj : ∀ i, Disjoint (H i) ((H i).image (fun x => ω i * x)))
    (hbase : ∀ c, ‖eta ψ (H 0) c‖ ^ 2 ≤ 1) :
    ∀ μ : ℕ, ∀ b : F, ‖eta ψ (H μ) b‖ ^ 2 ≤ 4 ^ μ := by
  intro μ b
  have := tower_ceiling_iterated (ψ := ψ) (V := 1) hω hchain hdisj hbase μ b
  simpa using this

end ArkLib.ProximityGap.TowerCeiling

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only). -/
#print axioms ArkLib.ProximityGap.TowerCeiling.tower_ceiling_iterated
#print axioms ArkLib.ProximityGap.TowerCeiling.tower_ceiling_base_one
