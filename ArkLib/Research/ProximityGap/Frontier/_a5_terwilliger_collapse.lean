/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real


/-!
# A5 — Terwilliger-algebra operator norm of the Krawtchouk-weighted subcode sum (#444, route 85)

**Target (the angle).** Relocate the δ* cancellation locus from the domain `μ_n` to the
*association-scheme operator*: the reduced far-line incidence sum
`𝒮(u₀) = Σ_{ξ∈D} K_w(wt ξ) e_p(ξ·u₀)`, `D = C⊥ ∩ u₁⊥`, is a Terwilliger-algebra module
object of the Hamming scheme `H(N,p)`.  The hoped-for new lemma: `D` sits in a *low-dim*
Terwilliger module, so the operator norm of the `K_w`-weighted action bounds `|𝒮| ≤ C√(n log)`.

**What this file records (the honest finding).** The Krawtchouk-weighting, viewed as the
Bose–Mesner element `W := Σ_i K_w(i) Aᵢ`, is **diagonal in the additive-character basis** with
*Krawtchouk eigenvalues* `λ_j = Σ_i K_w(i) Kᵢ(j)` (Delsarte / MacWilliams duality; verified
in-tree as `λ_j = q^N·[j=w]`, the Krawtchouk orthogonality relation, probe
`probe_a5_terwilliger_exact`).  The *heuristic* claim of this route was that, restricted to a
subconstituent module supported on the multiplicative domain `μ_n`, the per-frequency value of
this operator is the **incomplete Gauss period** `η_b = Σ_{y∈μ_n} e_p(b y)`, so that the
Terwilliger operator norm would be `max_{b≠0} |η_b| = M(μ_n)` — the BGK/Paley wall.

**Scope (audit R-026/R-001 extension, 2026-10-28).**  That operator identification is **not
proved here, and is not an in-tree verified fact**: the file defines no concrete operator,
invariant/compressed subspace, or norm.  `TerwilligerDiagonalizes` is merely the equality of two
unconstrained real parameters, and the checked Krawtchouk identity (eigenvalues `0` or `q^N`)
does not establish it.  Indeed, for ordinary coordinate-support compression the naive reading is
false: with `N = 1`, `p = 5`, `w = 0` the operator is the all-ones matrix, whose compression to
`μ_2` has norm `2`, while the nonzero Gauss-period maximum for `μ_2 ⊂ F₅` is
`(1+√5)/2 < 2`.  So the bridge is missing or misidentified; this is not a contradiction in the
scalar `iff` below, which is a trivial rewrite.

What the file records is therefore only a **conditional collapse**: *if* some operator norm
equals the wall (`TerwilligerDiagonalizes`), then bounding it is equivalent to the wall bound.
Excluding the association-scheme route requires the concrete operator, compressed space and an
identification theorem, which are open.  Axiom-clean; no `sorry`.
-/

namespace ProximityGap.A5Terwilliger


/-- The per-frequency Gauss-period wall `M(μ_n) = max_{b≠0} |η_b|`, abstracted as a real
parameter `wallM`.  This is the BGK/Paley object the prize must bound by `C√(n log(p/n))`. -/
structure WallData where
  /-- the per-frequency Gauss period magnitude `M(μ_n) = max_{b≠0}|Σ_{y∈μ_n} e_p(by)|`. -/
  wallM : ℝ
  /-- the conjectured floor scale `C√(n log(p/n))`. -/
  floor : ℝ
  wallM_nonneg : 0 ≤ wallM
  floor_nonneg : 0 ≤ floor

/-- The Terwilliger-module operator norm of the `K_w`-weighted dual-code action, abstracted
as a real parameter `terwNorm`. -/
structure TerwData where
  /-- operator norm of `W = Σ_i K_w(i) Aᵢ` restricted to the `μ_n`-subconstituent module. -/
  terwNorm : ℝ
  terwNorm_nonneg : 0 ≤ terwNorm

/-- **The (hypothesized) operator/wall identification.**
The Krawtchouk-weighted Bose–Mesner operator is diagonal in the additive-character basis with
Krawtchouk eigenvalues (`λ_j = q^N·[j=w]`, probe `probe_a5_terwilliger_exact`).  The route
*hypothesizes* that its norm on a suitable `μ_n`-subconstituent equals the Gauss-period wall;
here that is only the bare equality of two real parameters.  It is NOT an in-tree verified fact
(no concrete operator or subspace is defined; see the header for a naive-compression
counterexample). -/
def TerwilligerDiagonalizes (W : WallData) (T : TerwData) : Prop :=
  T.terwNorm = W.wallM

/-- The Terwilliger angle's *desired* output: the operator norm is at most the floor. -/
def TerwillingerOperatorBound (T : TerwData) (W : WallData) : Prop :=
  T.terwNorm ≤ W.floor

/-- The wall bound the prize actually needs: `M(μ_n) ≤ C√(n log)`. -/
def WallBound (W : WallData) : Prop :=
  W.wallM ≤ W.floor

/-- **Conditional collapse (route 85 ⇒ the wall, under the hypothesized identification).**
Given `TerwilligerDiagonalizes` (an unproved hypothesis, not a verified fact), the operator-norm
bound is *logically equivalent* to the Gauss-period wall bound — a one-line rewrite.  It shows
route 85 cannot relocate the locus *if* the identification holds; it does not prove that. -/
theorem terwilliger_reduces_to_wall
    (W : WallData) (T : TerwData) (hdiag : TerwilligerDiagonalizes W T) :
    TerwillingerOperatorBound T W ↔ WallBound W := by
  unfold TerwillingerOperatorBound WallBound TerwilligerDiagonalizes at *
  rw [hdiag]

/-- Consequence (conditional on `hdiag`): under the hypothesized identification the operator norm
carries no information beyond the wall.  Without a proved identification this says nothing about
a concrete Terwilliger operator. -/
theorem terwilliger_no_independent_gain
    (W : WallData) (T : TerwData) (hdiag : TerwilligerDiagonalizes W T) :
    (TerwillingerOperatorBound T W → WallBound W) ∧
    (WallBound W → TerwillingerOperatorBound T W) :=
  ⟨(terwilliger_reduces_to_wall W T hdiag).mp,
   (terwilliger_reduces_to_wall W T hdiag).mpr⟩

end ProximityGap.A5Terwilliger

-- axiom audit
#print axioms ProximityGap.A5Terwilliger.terwilliger_reduces_to_wall
#print axioms ProximityGap.A5Terwilliger.terwilliger_no_independent_gain
