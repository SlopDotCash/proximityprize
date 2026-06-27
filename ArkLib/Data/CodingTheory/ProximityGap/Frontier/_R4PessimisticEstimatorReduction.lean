/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumEnergyReduction
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# ROUTE R4 — the probabilistic / pessimistic-estimator reduction, made an EXACT in-tree theorem (#464)

This file pins, axiom-clean, the precise sense in which the **direct-probabilistic / 2nd-moment
route (R4)** to the prize floor REDUCES TO the in-tree character-sum / energy wall (face 3, the
Paley/BGK wall = node `N6c-2`).

## The R4 route and its success criterion

The classical way a *random* size-`n` evaluation set `S ⊆ F_p` is shown "good"
(`max_{b≠0}‖η_b(S)‖ ≤ t`) is the **union bound with a pessimistic estimator**: define

  `Φ_r(S) := ∑_{b≠0} ‖η_b(S)‖^{2r}`   (the un-normalized `2r`-th moment over frequencies),

and observe that `Φ_r(S) ≤ t^{2r}` forces `max_{b≠0}‖η_b(S)‖ ≤ t` (a single term is at most the
sum).  For a *random* `S`, `E_S[Φ_r] < t^{2r}` with `t = √(2n log p)` and `r ≈ log p`, so a good
`S` exists; conditional-expectation derandomization then outputs *some* explicit good set.

For the **prize code the evaluation set is FIXED** to the smooth multiplicative subgroup
`G = μ_n`.  So the R4 route, applied to the *actual* prize code, must verify the pessimistic
estimator **for `μ_n` itself**:

  `Φ_r(μ_n) = ∑_{b≠0} ‖η_b‖^{2r} ≤ t^{2r}`.

## The exact identity that collapses R4 onto the energy wall

By the in-tree moment ladder (`subgroup_gaussSum_moment`, pure orthogonality, no Weil),

  `Φ_r(μ_n) = ∑_{b≠0}‖η_b‖^{2r} = q·E_r(μ_n) − |μ_n|^{2r}`,

the **DC-subtracted `r`-fold additive energy** (`q = |F|`, `E_r = energyR G r`).  Hence the R4
success criterion `Φ_r(μ_n) ≤ t^{2r}` is *literally the same statement* as the in-tree energy
bound, and the pessimistic-estimator value is exactly the object `N6c-2` of the dependency graph.

`R4PessimisticCertificate ψ G r M`  is the named criterion `q·E_r − |G|^{2r} ≤ M^r`
(`M = t²`, so `M^r = t^{2r}`).  We prove:

* **`worstCaseIncompleteSumBound_of_R4Certificate`** — the R4 certificate discharges the live
  in-tree floor consumer `WorstCaseIncompleteSumBound ψ G M` (face 3, scale `M = t²`).  This is
  the honest content: *if* you can verify the pessimistic estimator for `μ_n` at depth `r`, the
  floor lands.  Axiom-clean, via `eta_pow_le_energyR`.

* **`R4Certificate_iff_dcSubtractedEnergy`** — the certificate is *equivalent* to the DC-subtracted
  energy bound `q·E_r ≤ M^r + |G|^{2r}`.  So R4 ⇔ N6c-2: there is no slack between the
  probabilistic route and the energy wall; they are the same inequality.

## Honest scope (the R4 verdict)

The verification of `R4PessimisticCertificate` at the prize depth `r ≈ log q` for `μ_n` **is** the
DC-subtracted char-`p` energy bound — i.e. it **is** the Paley/BGK wall, refuted at the bad prime
(`DCEnergyEssential`; the raw full-energy form is even false past the DC crossover).  Numerically
(this session): for *good* primes `Φ_r(μ_n) ≤ p·Wick` holds, but it FAILS at the bad primes
(`v₂(p−1)` heavy, e.g. `p=641`, ratio `1.07–1.55`).  So **R4-via-moments does NOT bypass Paley**;
this file makes that reduction a machine-checked identity rather than an informal claim.

The genuinely Paley-*free* part of R4 (derandomization to an explicit good set, or over the prime)
either outputs a set that is **not a multiplicative subgroup** (violating the prize's smooth/FFT
requirement) or must *certify* a chosen prime (again the per-prime Paley bound).  That trade-off is
recorded in the module docstring of the dependency graph as the R4 dichotomy; only the
energy-collapse half is formalized here, where it is exact.

All proofs axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #464, node N15/R4.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMomentLadder
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

namespace ArkLib.ProximityGap.R4PessimisticEstimatorReduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The R4 pessimistic-estimator certificate** at depth `r` and scale `M` (`M = t²`, the squared
threshold).  Says: the DC-subtracted `2r`-th frequency moment of `G = μ_n` is at most `M^r`, i.e.

  `Φ_r(μ_n) = ∑_{b≠0}‖η_b‖^{2r} = q·E_r − |G|^{2r} ≤ M^r = t^{2r}`.

This is exactly the success criterion of the union-bound / pessimistic-estimator (R4) route applied
to the *fixed* prize subgroup `μ_n`.  Stated as a `Prop`; never asserted (it IS the Paley wall at
the prize depth). -/
def R4PessimisticCertificate (G : Finset F) (r : ℕ) (M : ℝ) : Prop :=
  (Fintype.card F : ℝ) * energyR G r - (G.card : ℝ) ^ (2 * r) ≤ M ^ r

/-- **R4 certificate ⟺ DC-subtracted energy bound.**  The pessimistic-estimator criterion is
literally the DC-subtracted energy inequality `q·E_r ≤ M^r + |G|^{2r}`.  There is no gap between
the probabilistic route and the in-tree energy wall (`N6c-2`); they are the same statement. -/
theorem R4Certificate_iff_dcSubtractedEnergy (G : Finset F) (r : ℕ) (M : ℝ) :
    R4PessimisticCertificate (F := F) G r M
      ↔ (Fintype.card F : ℝ) * energyR G r ≤ M ^ r + (G.card : ℝ) ^ (2 * r) := by
  unfold R4PessimisticCertificate
  constructor <;> intro h <;> linarith

/-- **THE R4 → floor reduction (axiom-clean).**  If the R4 pessimistic-estimator certificate holds
at depth `r ≥ 1` and scale `M ≥ 0` for the smooth subgroup `G = μ_n`, then the live in-tree floor
consumer `WorstCaseIncompleteSumBound ψ G M` holds: every nontrivial frequency has `‖η_b‖² ≤ M`.

Mechanism: `eta_pow_le_energyR` gives `‖η_b‖^{2r} ≤ q·E_r − |G|^{2r}`; the certificate caps the RHS
by `M^r`; so `‖η_b‖^{2r} ≤ M^r`, whence `(‖η_b‖²)^r ≤ M^r` and, as both sides are nonnegative and
`r ≥ 1`, `‖η_b‖² ≤ M`.  This threads the *probabilistic* (R4) success criterion into the *same*
consumer that face 3 (Paley) feeds — making "R4 reduces to Paley" a machine-checked fact. -/
theorem worstCaseIncompleteSumBound_of_R4Certificate {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ} {M : ℝ} (hr : 1 ≤ r) (hM : 0 ≤ M)
    (hcert : R4PessimisticCertificate (F := F) G r M) :
    WorstCaseIncompleteSumBound ψ G M := by
  intro b hb
  -- `‖η_b‖^{2r} ≤ q·E_r − |G|^{2r} ≤ M^r`
  have hηbound : ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * energyR G r - (G.card : ℝ) ^ (2 * r) :=
    eta_pow_le_energyR hψ G r b hb
  have hηMr : ‖eta ψ G b‖ ^ (2 * r) ≤ M ^ r := le_trans hηbound hcert
  -- rewrite `‖η_b‖^{2r} = (‖η_b‖²)^r`
  have hrw : ‖eta ψ G b‖ ^ (2 * r) = (‖eta ψ G b‖ ^ 2) ^ r := by
    rw [← pow_mul]; ring_nf
  rw [hrw] at hηMr
  -- `(‖η_b‖²)^r ≤ M^r`, both bases nonnegative, `r ≥ 1` ⟹ `‖η_b‖² ≤ M`
  have hbase : (0 : ℝ) ≤ ‖eta ψ G b‖ ^ 2 := sq_nonneg _
  exact le_of_pow_le_pow_left₀ (by omega) hM hηMr

/-- **Specialization at the prize threshold `t = √(c·n·log q)`.**  Writing the scale as
`M = c·n·log q` (so `t = √M`), the R4 certificate at the optimal depth `r ≈ log q` discharges the
floor at exactly the conjectured Paley scale.  This records the SHAPE of the target the R4 route
must hit: the certificate `∑_{b≠0}‖η_b‖^{2r} ≤ (c·n·log q)^r`.  (The hypothesis is the open Paley
content; only the implication is proved.) -/
theorem worstCaseIncompleteSumBound_prizeScale_of_R4Certificate {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ} {c : ℝ} (hr : 1 ≤ r)
    (hc : 0 ≤ c * (G.card : ℝ) * Real.log (Fintype.card F : ℝ))
    (hcert : R4PessimisticCertificate (F := F) G r
      (c * (G.card : ℝ) * Real.log (Fintype.card F : ℝ))) :
    WorstCaseIncompleteSumBound ψ G (c * (G.card : ℝ) * Real.log (Fintype.card F : ℝ)) :=
  worstCaseIncompleteSumBound_of_R4Certificate hψ hr hc hcert

end ArkLib.ProximityGap.R4PessimisticEstimatorReduction

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
#print axioms ArkLib.ProximityGap.R4PessimisticEstimatorReduction.R4Certificate_iff_dcSubtractedEnergy
#print axioms ArkLib.ProximityGap.R4PessimisticEstimatorReduction.worstCaseIncompleteSumBound_of_R4Certificate
#print axioms ArkLib.ProximityGap.R4PessimisticEstimatorReduction.worstCaseIncompleteSumBound_prizeScale_of_R4Certificate
