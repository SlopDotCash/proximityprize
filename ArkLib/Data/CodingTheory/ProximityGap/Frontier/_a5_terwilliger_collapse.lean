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
`probe_a5_terwilliger_exact`).  Restricted to the subconstituent module supported on the
multiplicative domain `μ_n`, the per-frequency value of this operator is the **incomplete
Gauss period** `η_b = Σ_{y∈μ_n} e_p(b y)`.  Hence the Terwilliger operator norm is
`max_{b≠0} |η_b| = M(μ_n)` — the BGK/Paley wall.  The "low-dim module" controls only the
*number of irreducible summands*, never the *per-summand operator norm*, which is the wall.

We encode this as a **collapse theorem**: under the Delsarte diagonalization identity
(`TerwilligerDiagonalizes`), the Terwilliger operator-norm bound is logically *equivalent* to
the Gauss-period wall bound.  So route 85 **reduces to the wall** — it does not relocate the
locus.  (This matches catalogue route 88: "association-scheme eigenvalue = Krawtchouk = the
same".)  Axiom-clean; no `sorry`.
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

/-- **The Delsarte diagonalization identity (the structural collapse).**
The Krawtchouk-weighted Bose–Mesner operator is diagonal in the additive-character basis with
Krawtchouk eigenvalues; restricted to the `μ_n`-subconstituent its operator norm is *exactly*
the Gauss-period wall.  This is the in-tree-verified fact (`λ_j = q^N·[j=w]`,
`probe_a5_terwilliger_exact`), here stated as the hypothesis that pins the two numbers equal. -/
def TerwilligerDiagonalizes (W : WallData) (T : TerwData) : Prop :=
  T.terwNorm = W.wallM

/-- The Terwilliger angle's *desired* output: the operator norm is at most the floor. -/
def TerwillingerOperatorBound (T : TerwData) (W : WallData) : Prop :=
  T.terwNorm ≤ W.floor

/-- The wall bound the prize actually needs: `M(μ_n) ≤ C√(n log)`. -/
def WallBound (W : WallData) : Prop :=
  W.wallM ≤ W.floor

/-- **Collapse theorem (route 85 ⇒ the wall).**  Given the Delsarte diagonalization identity
(`TerwilligerDiagonalizes`, the verified structural fact), the Terwilliger operator-norm bound
is *logically equivalent* to the Gauss-period wall bound.  Therefore route 85 does **not**
relocate the cancellation locus: proving it is *exactly as hard* as the wall.  No `sorry`. -/
theorem terwilliger_reduces_to_wall
    (W : WallData) (T : TerwData) (hdiag : TerwilligerDiagonalizes W T) :
    TerwillingerOperatorBound T W ↔ WallBound W := by
  unfold TerwillingerOperatorBound WallBound TerwilligerDiagonalizes at *
  rw [hdiag]

/-- Consequence: the Terwilliger operator norm carries **no information beyond the wall**.
If the operator bound holds it is *because* the wall bound holds, and conversely.  The
"low-dimensional module" hypothesis is silent on the per-summand norm. -/
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
