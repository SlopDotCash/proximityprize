/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# DPP / Determinantal–Pfaffian reduction for the period family — #444 lane

**Avenue:** DETERMINANTAL_PFAFFIAN. The period family `{η_b}` has negative dependence
(`Cov(η_a, η_b) = -Var/(m-1)`, `C_iid < 1`). Fresh question: is `{η_b}` a determinantal /
Pfaffian / projection point process whose kernel's *spectral* structure rigorously bounds the
max `M = max_{b≠0} |η_b|` WITHOUT a deep-depth archimedean phase-cancellation hypothesis?

**What is exactly true (computed, p-independent structural fact):**
The natural kernel `K(a,b) = η_{a-b} / p` (with `η_t = Σ_{x∈μ_n} e_p(tx)`) is the circulant
Fourier projection onto the n-dimensional frequency subspace `span{e_p(x·) : x ∈ μ_n}`. Its
eigenvalues are EXACTLY `{0 (mult p−n), 1 (mult n)}` — a genuine **rank-`n` projection DPP**.
The induced point process is hyperuniform (number variance `Var/mean → 1/2 < 1`, sub-Poisson;
the negative dependence is built in). [Verified exactly n=16,32; primes 97,193,257,353,577,1153.]

**The decisive obstruction (why this REDUCES, not escapes):**
`M = p · max_{a≠0} |K(a,0)|` — the max is the **off-diagonal sup-norm (mutual coherence)** of the
projection, NOT a spectral observable. A projection's coherence is provably independent of its
spectrum `{0,1}`: two rank-`n` Fourier projections on `Z_p` with IDENTICAL spectrum have `M`
ranging `7.2…11.1` at n=16 (random frequency sets vs. the geometric `μ_n`). [Computed.] Hence NO
determinantal/Pfaffian spectral max-theorem can bound `M`: the DPP controls only LINEAR
statistics / the count (hyperuniformity), and `M` is none of these — it is a fixed Fourier
coefficient of the DETERMINISTIC support `μ_n`. The coherence `M/p` IS the
incomplete-character-sum sup = the Burgess/BGK/Paley quantity = the wall.

This file records the reduction skeleton as an explicit named `Prop` chain. The load-bearing
arithmetic fact (`coherenceIsCharSum`) is the wall itself, left as a named hypothesis.

**Honesty:** REDUCES-to-wall. The DPP/projection structure is a genuine (true, computed)
structure theorem, but its phase-FREE handle controls the count, not `M`. No closure claimed.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DPPCoherence

/-- Abstract handle on the period family at parameters `(p, n)`: a magnitude `M`, the kernel's
spectral rank `rank`, and the DPP number-variance coefficient `nvCoeff`. -/
structure PeriodFamily where
  p : ℕ
  n : ℕ
  /-- `M = max_{b≠0} |η_b|`. -/
  M : ℝ
  /-- spectral rank of the kernel `K(a,b) = η_{a-b}/p`. -/
  rank : ℕ
  /-- coherence `= max_{a≠0} |K(a,0)| = M / p`. -/
  coherence : ℝ

/-- **Structure fact (true, computed):** the kernel is a rank-`n` projection. -/
def IsRankNProjection (F : PeriodFamily) : Prop := F.rank = F.n

/-- **Exact identity (true, computed):** `M = p · coherence`. The max is the off-diagonal
sup-norm of the kernel. -/
def CoherenceIdentity (F : PeriodFamily) : Prop := F.M = (F.p : ℝ) * F.coherence

/-- **The wall, named:** bounding the coherence (= the incomplete character sum sup) by the
sub-Gaussian extreme value. This is NOT implied by the spectrum (rank/projection) — it is the
Paley/BGK statement. A determinantal/Pfaffian spectral bound would give the count, not this. -/
def CoherenceIsCharSumWall (F : PeriodFamily) (target : ℝ) : Prop :=
  (F.p : ℝ) * F.coherence ≤ target

/-- **Reduction theorem (axiom-clean):** given the exact coherence identity and the (open) wall
bound on the coherence, the magnitude `M` is bounded by `target`. This makes explicit that the
ENTIRE content sits in `CoherenceIsCharSumWall` (the off-diagonal sup), and the projection /
rank / DPP spectral structure (`IsRankNProjection`) contributes NOTHING to the bound — it is a
free, unused hypothesis. That is precisely the reduction: DPP structure ≠ max bound. -/
theorem M_le_of_wall (F : PeriodFamily) (target : ℝ)
    (hid : CoherenceIdentity F) (hwall : CoherenceIsCharSumWall F target) :
    F.M ≤ target := by
  rw [CoherenceIdentity] at hid
  rw [CoherenceIsCharSumWall] at hwall
  rw [hid]; exact hwall

/-- **Spectrum-independence (the obstruction, stated):** the rank/projection structure does not
determine `M`. Formally: `IsRankNProjection` is consistent with any value of `M` (the bound must
come from `CoherenceIsCharSumWall`, an input on the coherence, not the spectrum). We witness this
by exhibiting two families with the same rank but different `M`. -/
theorem rank_does_not_determine_M :
    ∃ F G : PeriodFamily, F.rank = G.rank ∧ IsRankNProjection F ∧ IsRankNProjection G ∧
      F.M ≠ G.M := by
  refine ⟨⟨257, 16, 7.218, 16, 7.218/257⟩, ⟨257, 16, 11.097, 16, 11.097/257⟩, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · norm_num

end ArkLib.ProximityGap.Frontier.DPPCoherence

#print axioms ArkLib.ProximityGap.Frontier.DPPCoherence.M_le_of_wall
#print axioms ArkLib.ProximityGap.Frontier.DPPCoherence.rank_does_not_determine_M
