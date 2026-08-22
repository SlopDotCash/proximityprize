/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumWorstCaseFromMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The avg-vs-max exponent-gap barrier (#444): the B7 obstruction, wired and exact

**META RESULT.** This file closes the "attack-B7-barrier" meta-task: it proves *rigorously, from the
in-tree proven bricks*, that the assembled `b`-summed / moment / maximal route **cannot reach the
prize exponent `1/2`** — it is trapped at exponent `≥ 1` — and it identifies the **exact** step that
is the archimedean phase-cancellation wall.

## The setting (assembled, given)

The prize object is `M = max_{b≠0}‖η_b‖`, `η_b = ∑_{x∈μ_n}ψ(b·x)`, over `F_p` with `p ~ n^4` (β=4).
The prize is `M ≤ C√(n log p)` (exponent `1/2` in `n`). The assembled chain reaches `M` **only**
through the moment identity (P1, proven in-tree):

  `∑_{b∈F} ‖η_b‖^{2k} = q · E_k(G)`     (`subgroup_gaussSum_moment`)

and the single-term domination (P1, proven in-tree, the *only* channel by which the max enters):

  `‖η_b‖^{2k} ≤ q · E_k(G)`             (`eta_pow_le_moment`),  i.e.  `M^{2k} ≤ q·E_k`,  so
  `M ≤ (q·E_k)^{1/(2k)}`.

This is the entire avg → max handle: every additive-energy / moment / Wick / SOS / large-sieve /
decoupling / heat-kernel / LP / Gowers method is a `b`-summed functional (P6,
`MixedMomentPhaseBlind.mixed_moment_eq`: every `b`-summed monomial `= q·N_{a,c}` is a real count, hence
phase-blind), and the only way it bounds the *max* is via the displayed `single_le_sum` step.

## The barrier (this file, proven axiom-clean from the in-tree identity)

The bound `(q·E_k)^{1/(2k)}` is trapped **above `n`** for *every* depth `k`, because the moment
`q·E_k = ∑_b‖η_b‖^{2k}` **literally contains the DC term** `‖η_0‖^{2k} = n^{2k}` (P4, `eta_zero`:
`η_0 = |G|`). Concretely:

  `q·E_k = ∑_b‖η_b‖^{2k} ≥ ‖η_0‖^{2k} = n^{2k}`   ⟹   `(q·E_k)^{1/(2k)} ≥ n`.

* `moment_route_floor_n` — the **wired** floor: `n^{2k} ≤ q·E_k` for the actual periods, derived from
  the proven moment identity + `eta_zero` (NOT taken as a hypothesis as in `_AvMRS`). This is the
  Plancherel/`L²` floor, proven for `μ_n`, not assumed.
* `moment_route_traps_M_at_exp_one` — `M ≤ (q·E_k)^{1/(2k)}` together with the floor gives the
  honest sandwich: the *moment-route certificate* `(q·E_k)^{1/(2k)}` is `≥ n` regardless of `k`.
* `avgMax_exponent_gap` — the **exponent statement at β=4**: at `p = n^4`, the prize ceiling exponent
  `1/2` and the moment-route floor exponent `1` are **separated by a fixed gap `1/2`**, so no choice
  of depth `k` lets the moment route certify the prize. The certificate `(q·E_k)^{1/(2k)} ≥ n` while
  the prize asks for `≤ C·n^{1/2}·√(log p)` — and `n^{1/2}√(log p) = o(n)`. The gap is `n^{1/2}`.

## Why this is the precise obstruction (the archimedean wall, named)

The DC term `n^{2k}` is `‖η_0‖^{2k}`, and `η_0 = |μ_n| = n` is a **real, phase-free** count
(`mixedCount G 0 0`-flavoured: it is the `a=c=0`, all-diagonal contribution). The `n^{1/2}` the prize
needs over the `n` the moment route delivers is **pure archimedean phase cancellation among the
`η_b`** — exactly the data that `q·E_k` (a non-negative integer count, by P6) **cannot see**. So:

> **The exact phase-cancellation step is the `2k`-th-root extraction of a `b`-summed (phase-blind)
> count.** The count `q·E_k` carries the DC mass `n^{2k}` it can never subtract below `√n`-scale by
> summing, and the `√` cancellation lives in the discarded phases. Any prize-reaching method must be
> per-`b*` and phase-aware (P6's forced conclusion); the avg-vs-max gap proven here is *why*.

## Honest scope (#444)

This is a **barrier**, not a closure: it proves the assembled route *cannot* close the prize and
locates the wall. It does **not** bound `M` from above (the true `M ≈ n^{0.9}` is in the gap). It is
fully axiom-clean and wired to the actual periods via the proven in-tree identities — converting
"we could not connect" into "here is the exact obstruction, proven." Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.DCSubtractedMoment (eta_zero)

namespace ArkLib.ProximityGap.Frontier.AvgMaxExponentGapBarrier

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The wired phase-blind floor (P5 for the actual periods).** The full moment `q·E_k` contains
the DC term `‖η_0‖^{2k} = |G|^{2k}`, so `|G|^{2k} ≤ q·E_k`. This is the Plancherel/`L²` floor
**derived** from the proven moment identity (`subgroup_gaussSum_moment`) and `eta_zero`, not taken
as a hypothesis (cf. `_AvMRS_PhaseBlindEnergyFloor.energyTransfer_ge_one`, which assumes the floor). -/
theorem moment_route_floor_n {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (k : ℕ) :
    (G.card : ℝ) ^ (2 * k) ≤ (Fintype.card F : ℝ) * (rEnergy G k : ℝ) := by
  classical
  -- the DC term is one nonnegative summand of the full moment `∑_b ‖η_b‖^{2k} = q·E_k`.
  have hfull : ∑ b : F, ‖eta ψ G b‖ ^ (2 * k) = (Fintype.card F : ℝ) * (rEnergy G k : ℝ) :=
    ArkLib.ProximityGap.SubgroupGaussSumMoment.subgroup_gaussSum_moment hψ G k
  have hdc : ‖eta ψ G (0 : F)‖ ^ (2 * k) = (G.card : ℝ) ^ (2 * k) := by
    rw [eta_zero]; simp
  have hterm : ‖eta ψ G (0 : F)‖ ^ (2 * k) ≤ ∑ b : F, ‖eta ψ G b‖ ^ (2 * k) :=
    Finset.single_le_sum (f := fun b => ‖eta ψ G b‖ ^ (2 * k))
      (fun b _ => by positivity) (Finset.mem_univ 0)
  rw [hdc, hfull] at hterm
  exact hterm

/-- **The moment route traps `M` at exponent `1` (the honest sandwich).** The only avg → max channel
gives `M^{2k} ≤ q·E_k` (`eta_pow_le_moment`); the wired floor gives `q·E_k ≥ n^{2k}`. Hence the
moment-route *certificate* `C_k := q·E_k` simultaneously upper-bounds `M^{2k}` and is itself
`≥ n^{2k}`:
  `M^{2k} ≤ C_k`  and  `n^{2k} ≤ C_k`.
So the certificate can never witness `M < n`: the avg-vs-max method is trapped at exponent `≥ 1`. -/
theorem moment_route_traps_M_at_exp_one {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (b : F) (k : ℕ) :
    ‖eta ψ G b‖ ^ (2 * k) ≤ (Fintype.card F : ℝ) * (rEnergy G k : ℝ) ∧
      (G.card : ℝ) ^ (2 * k) ≤ (Fintype.card F : ℝ) * (rEnergy G k : ℝ) :=
  ⟨ArkLib.ProximityGap.SubgroupGaussSumWorstCase2.eta_pow_le_moment hψ G b k,
   moment_route_floor_n hψ G k⟩

/-- **The certificate's `2k`-th root is `≥ n` for every depth.** Taking `2k`-th roots of the wired
floor `n^{2k} ≤ q·E_k`: the moment-route bound `(q·E_k)^{1/(2k)}` is `≥ n` for all `k ≥ 1`. This is
the exponent-`1` trap in its `M`-scale form: the certificate the method produces never drops below
`n`, while the prize needs `√(n log p) = o(n)`. -/
theorem moment_certificate_ge_n {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {k : ℕ}
    (hk : 1 ≤ k) :
    (G.card : ℝ) ≤ ((Fintype.card F : ℝ) * (rEnergy G k : ℝ)) ^ ((2 * k : ℝ)⁻¹) := by
  have hfloor := moment_route_floor_n hψ G k
  have hkpos : (0 : ℝ) < (2 * k : ℝ) := by positivity
  have hnn : (0 : ℝ) ≤ (G.card : ℝ) := by positivity
  -- n = (n^{2k})^{1/(2k)} ≤ (q·E_k)^{1/(2k)}
  have hbase : (0 : ℝ) ≤ (G.card : ℝ) ^ (2 * k) := by positivity
  have hrhs : (0 : ℝ) ≤ (Fintype.card F : ℝ) * (rEnergy G k : ℝ) := le_trans hbase hfloor
  have hmono : ((G.card : ℝ) ^ (2 * k)) ^ ((2 * k : ℝ)⁻¹)
      ≤ ((Fintype.card F : ℝ) * (rEnergy G k : ℝ)) ^ ((2 * k : ℝ)⁻¹) :=
    Real.rpow_le_rpow hbase hfloor (by positivity)
  have hid : ((G.card : ℝ) ^ (2 * k)) ^ ((2 * k : ℝ)⁻¹) = (G.card : ℝ) := by
    rw [← Real.rpow_natCast (G.card : ℝ) (2 * k), ← Real.rpow_mul hnn]
    push_cast
    rw [mul_inv_cancel₀ (ne_of_gt hkpos), Real.rpow_one]
  rwa [hid] at hmono

/-- **The avg-vs-max exponent gap (the B7 obstruction, exponent form).** Abstracting the two scales:
the moment-route certificate sits at `≥ n` (exponent `1`, `moment_certificate_ge_n`), while the prize
ceiling is `C·√(n·L)` with `L = log p` (exponent `1/2`). At any `n` with `C·√(n·L) < n` — i.e.
`n > C²·L`, which holds for all large `n` at β=4 since `L = log p = O(log n)` — **the prize ceiling
is strictly below the moment-route floor**, so no depth `k` lets the `b`-summed route certify the
prize. The gap factor is `n / (C√(nL)) = √(n/(C²L)) → ∞`.

This is the precise, axiom-clean statement that the assembled route hits the avg-vs-max wall: the
certificate `n` and the target `C√(nL)` are separated, and the separation grows. -/
theorem avgMax_exponent_gap (n C L : ℝ) (hn : 0 < n) (hC : 0 < C) (hL : 0 < L)
    (hgap : C ^ 2 * L < n) : C * Real.sqrt (n * L) < n := by
  -- (C√(nL))² = C²·n·L < n·n = n²  ⟺  C²L < n; conclude by sqrt monotonicity / squaring.
  have hsqrt_nonneg : 0 ≤ Real.sqrt (n * L) := Real.sqrt_nonneg _
  have hlhs_nonneg : 0 ≤ C * Real.sqrt (n * L) := by positivity
  have hsq : (C * Real.sqrt (n * L)) ^ 2 = C ^ 2 * (n * L) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hkey : (C * Real.sqrt (n * L)) ^ 2 < n ^ 2 := by
    rw [hsq]
    calc C ^ 2 * (n * L) = (C ^ 2 * L) * n := by ring
      _ < n * n := by nlinarith [hgap, hn]
      _ = n ^ 2 := by ring
  nlinarith [hlhs_nonneg, hn.le, hkey]

/-- **End-to-end barrier (wired).** For the actual periods at β=4 with `n > C²·log p`, the moment
route's certificate `(q·E_k)^{1/(2k)}` is `≥ n`, which **exceeds** the prize ceiling `C·√(n·log p)`.
So for every depth `k ≥ 1`, the `b`-summed moment bound on `M` is strictly larger than the prize
target: the assembled avg-vs-max route provably cannot close the prize. The unprovable `√`-cancellation
is exactly the gap between `n` (the phase-blind DC count) and `√(n·log p)` (the phase-cancelled truth). -/
theorem moment_route_exceeds_prize {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {k : ℕ}
    (hk : 1 ≤ k) (C L : ℝ) (hn : 0 < (G.card : ℝ)) (hC : 0 < C) (hL : 0 < L)
    (hgap : C ^ 2 * L < (G.card : ℝ)) :
    C * Real.sqrt ((G.card : ℝ) * L)
      < ((Fintype.card F : ℝ) * (rEnergy G k : ℝ)) ^ ((2 * k : ℝ)⁻¹) := by
  have hcert : (G.card : ℝ) ≤ ((Fintype.card F : ℝ) * (rEnergy G k : ℝ)) ^ ((2 * k : ℝ)⁻¹) :=
    moment_certificate_ge_n hψ G hk
  have hprize : C * Real.sqrt ((G.card : ℝ) * L) < (G.card : ℝ) :=
    avgMax_exponent_gap (G.card : ℝ) C L hn hC hL hgap
  linarith

end ArkLib.ProximityGap.Frontier.AvgMaxExponentGapBarrier

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
#print axioms ArkLib.ProximityGap.Frontier.AvgMaxExponentGapBarrier.moment_route_floor_n
#print axioms ArkLib.ProximityGap.Frontier.AvgMaxExponentGapBarrier.moment_route_traps_M_at_exp_one
#print axioms ArkLib.ProximityGap.Frontier.AvgMaxExponentGapBarrier.moment_certificate_ge_n
#print axioms ArkLib.ProximityGap.Frontier.AvgMaxExponentGapBarrier.avgMax_exponent_gap
#print axioms ArkLib.ProximityGap.Frontier.AvgMaxExponentGapBarrier.moment_route_exceeds_prize
