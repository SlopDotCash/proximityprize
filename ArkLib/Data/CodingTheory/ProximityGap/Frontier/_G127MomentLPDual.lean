/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G124MomentLPDepthConstraints

/-!
# G127: the moment-LP dual — a systematic no-go generator

G124 gave the primal LP rows.  This file proves the Farkas-style dual combination: any
nonnegative multipliers `lam m` whose weighted descFactorial columns dominate a cost vector
`c` transfer the full LP bound to `c`:

```text
(∀ s ≤ r, c s ≤ Σ_m lam m · (r−s)_m)
  ⟹ Σ_s c s · depthFiber A r s ≤ Σ_m lam m · (r)_m² · #A^m · E_{r−m}(A).
```

Row `m = 0` is included (`(r−s)_0 = 1`, bound `E_r`), so the dual is complete: every cost
vector can be dominated, and the quality of the certificate is the choice of multipliers.

**Use as a no-go generator.**  Any proposed deep-sector counterexample family comes with a
claimed lower bound `B ≤ Σ_s c s · fiber_s` for some cost vector `c` supported below full
depth.  Exhibiting multipliers `lam` that dominate `c` while keeping the dual value below `B`
refutes the family — mechanically, per prime, using only lower-rung energies.  Refutations of
this shape are kernel-checkable arithmetic once `lam` is chosen; no new combinatorics is
needed per candidate.

**Honest scope.**  A transfer schema; it generates no bound on the fully-disjoint sector
itself (every row `m ≥ 1` has weight `0` there, and row `0` costs the full `E_r`).  CORE
remains OPEN.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G127MomentLPDual

open Finset Fintype
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G124MomentLPDepthConstraints

variable {α : Type*} [DecidableEq α] [AddCancelCommMonoid α]

/-- **The moment-LP dual.**  Multipliers dominating the cost vector transfer the LP bounds. -/
theorem moment_LP_dual (A : Finset α) (r : ℕ) (lam c : ℕ → ℕ)
    (hdom : ∀ s ∈ Finset.range (r + 1),
      c s ≤ ∑ m ∈ Finset.range (r + 1), lam m * (r - s).descFactorial m) :
    ∑ s ∈ Finset.range (r + 1), c s * depthFiber A r s
      ≤ ∑ m ∈ Finset.range (r + 1),
          lam m * ((r.descFactorial m) ^ 2 *
            (A.card ^ m * Finset.addREnergy (r - m) A)) := by
  calc
    ∑ s ∈ Finset.range (r + 1), c s * depthFiber A r s
        ≤ ∑ s ∈ Finset.range (r + 1),
            (∑ m ∈ Finset.range (r + 1), lam m * (r - s).descFactorial m)
              * depthFiber A r s :=
      Finset.sum_le_sum (fun s hs =>
        Nat.mul_le_mul_right _ (hdom s hs))
    _ = ∑ m ∈ Finset.range (r + 1), lam m *
          ∑ s ∈ Finset.range (r + 1),
            (r - s).descFactorial m * depthFiber A r s := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      refine Finset.sum_congr rfl (fun s _ => ?_)
      ring
    _ ≤ ∑ m ∈ Finset.range (r + 1),
          lam m * ((r.descFactorial m) ^ 2 *
            (A.card ^ m * Finset.addREnergy (r - m) A)) :=
      Finset.sum_le_sum (fun m hm =>
        Nat.mul_le_mul_left _
          (moment_LP_row A (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))))

/-- **No-go schema.**  A claimed census lower bound `B ≤ Σ c_s · fiber_s` is refuted by any
dominating multipliers whose dual value stays below `B`. -/
theorem census_claim_refuted (A : Finset α) (r : ℕ) (lam c : ℕ → ℕ) (B : ℕ)
    (hdom : ∀ s ∈ Finset.range (r + 1),
      c s ≤ ∑ m ∈ Finset.range (r + 1), lam m * (r - s).descFactorial m)
    (hdual : ∑ m ∈ Finset.range (r + 1),
        lam m * ((r.descFactorial m) ^ 2 *
          (A.card ^ m * Finset.addREnergy (r - m) A)) < B) :
    ¬ (B ≤ ∑ s ∈ Finset.range (r + 1), c s * depthFiber A r s) := by
  intro hclaim
  exact absurd (hclaim.trans (moment_LP_dual A r lam c hdom))
    (Nat.not_le_of_lt hdual)

end ArkLib.ProximityGap.Frontier.G127MomentLPDual

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G127MomentLPDual.moment_LP_dual
#print axioms ArkLib.ProximityGap.Frontier.G127MomentLPDual.census_claim_refuted
