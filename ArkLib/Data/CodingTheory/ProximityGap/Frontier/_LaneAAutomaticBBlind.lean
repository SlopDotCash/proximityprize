/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvCP_WrEqMomentIdentity

/-!
# Lane A (#466 round 10): the wraparound solution set is b-blind — the collapse identity

## The refuted lane (automatic-sequence / substitutive Fourier analysis)

For `n = 2^μ`, index the `n`-th roots of unity mod `p` by `k ∈ ℤ/2^μ` via `x = ζ^k`. The wraparound
count `W_r = E_r^{F_p} − E_∞` counts the collision tuples `(k_1,…,k_{2r})` with
`∑_{i≤r} ζ^{k_i} ≡ ∑_{i>r} ζ^{k_i} (mod p)` that are NOT char-0 relations. Lane A hoped that the
phase sequence `k ↦ e_p(b·ζ^k)`, governed by the 2-adic digit structure of `k`, is 2-automatic, so
that an Allouche–Shallit / Byszewski–Konieczny–Müllner Gowers-norm uniformity bound would force
`W_r` below its mean-field DC value `n^{2r}/p` — i.e. give the wall.

## Probe verdict (`scripts/probes/probe_466r10_automatic.py` → `_out_466r10_automatic.txt`)

Exact enumeration over `≥2` primes (distinct `v₂(p−1)`) and two octaves `n = 8, 16` (validated
tuple-for-tuple against the `Wr_eq_moment_transfer` level engine) shows the wraparound solution set
carries **genuine, robust 2-adic digit structure**: the pairwise-exponent valuation statistic
`v₂(k_i − k_j)` deviates from the digit-uniform null with `χ²/dof` in the hundreds-to-thousands, and
the set is NOT closed under the odd-unit dilation `k ↦ u·k` (a previously-unrecorded observation).
Yet the angle collapses by three independent mechanisms:

* **(A) count-neutral** — `W_r` already sits at/below its digit-uniform DC mean `n^{2r}/p`
  (`W_r/DC ∈ [0.49, 0.98]`); a uniformity bound can only push the total toward a null it already
  matches, so there is no total to save;
* **(B) sign-unstable** — the deviation direction flips with `p`, so no fixed-direction Gowers bias;
* **(C) b-blind** — *formalized here*.

Task 1 (automaticity): `k ↦ ζ^k mod p` obeys `a(2k) = a(k)²` but its 2-kernel base root `ζ^{2^i}`
has order `n/2^i` (shrinking), so there is **no `μ`-uniform finite automaton** — the automatic-
sequence asymptotics do not apply (reconfirming the dead-ledger `[wf-NC / NC1]` digit-sum no-go).

## The collapse identity (mechanism C, axiom-clean)

The load-bearing fact is that the wraparound solution set is the **equal-sum (collision) locus**
`{(x,y) : S x = S y}`, and on that locus the per-frequency additive-character weight
`χ_b(S x − S y) = χ_b(0) = 1` is **independent of `b`**. Consequently the count of the solution set
(and any statistic of it) is a function of the `b`-*summed* moment `∑_b η_b·conj(η_b)`, not of any
single frequency `η_b`. This is exactly the C1/Meta-Theorem b-blindness for this object. We record
it as the two facts that carry the collapse, reusing the `#444` master identity verbatim.

Issue #466 (round 10, Lane A).
-/

open Finset

namespace ProximityGap.Frontier.LaneAAutomaticBBlind

open ProximityGap.Frontier.WrEqMomentIdentity

variable {p : ℕ} [Fact p.Prime] {T : Type*} [Fintype T] [DecidableEq T]

/-- **The per-frequency weight is trivial on the equal-sum locus (the b-blindness kernel).**
When `S x = S y` (i.e. the pair lies in the wraparound/collision solution set), the additive
character weight `χ_b(S x − S y) = χ_b(0) = 1` for **every** frequency `b`. So the indicator of the
solution set carries no `b`-dependence: the 2-adic digit structure of the solution set is identical
across all frequencies `b`, and cannot select or exclude the worst frequency `b*`. -/
theorem char_weight_trivial_on_solset (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p) (b : ZMod p)
    {S : T → ZMod p} {x y : T} (hxy : S x = S y) : chi ζ b (S x - S y) = 1 := by
  rw [hxy, sub_self]
  simp [chi]

/-- **The collapse identity (Lane A, mechanism C).** The wraparound/collision solution count is the
fully `b`-SUMMED moment `∑_b η_b·conj(η_b)` (up to the `1/p` normalization) — this is the `#444`
master identity `collision_count_eq_moment`, restated as the Lane-A no-go: because the solution set
count equals a sum OVER all `b`, every statistic of that set is a property of the aggregate moment
`E_r`, never of a single `η_b`. Any automatic-sequence / substitutive uniformity bound on the phase
sequence therefore bounds only the `b`-summed count `W_r` — which already sits at its mean-field DC
value (probe) — and can produce no per-frequency (b-sensitive) saving. The Meta-Theorem's
second-order cap applies: this is the `b`-summed `2r`-th moment, so the lane is dead. -/
theorem solset_count_is_b_summed (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p) (S : T → ZMod p) :
    (p : ℂ) * (Finset.univ.filter (fun xy : T × T => S xy.1 = S xy.2)).card
      = ∑ b : ZMod p, eta ζ S b * (starRingEnd ℂ) (eta ζ S b) :=
  collision_count_eq_moment ζ hζ S

end ProximityGap.Frontier.LaneAAutomaticBBlind

#print axioms ProximityGap.Frontier.LaneAAutomaticBBlind.char_weight_trivial_on_solset
#print axioms ProximityGap.Frontier.LaneAAutomaticBBlind.solset_count_is_b_summed
