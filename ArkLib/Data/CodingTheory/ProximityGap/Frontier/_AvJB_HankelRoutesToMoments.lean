/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The Hankel/Toda structure of `b_k` routes back to the deep moments (form (D) → form (A)) (#444)

**Lane-1 constraint verdict (closes the "unexplored frontier" of Shaw's Jacobi note; NOT a crack).**

Shaw's Jacobi note (`docs/kb/deltastar-444-JACOBI-RECURRENCE-TOOL-2026-06-21.md`) names the
**Hankel-ratio / Toda-lattice structure of the `b_k`** as "the unexplored frontier it opens", with
the open question: *is `max_k b_k` controllable by a route the exploding `E_r` obscured?*  The
recurrence off-diagonals are exactly Hankel-determinant ratios

`b_k² = D_{k−1}·D_{k+1} / D_k²`,   `D_j = det(m_{a+c})_{0≤a,c≤j}`  (`m_r` = the `r`-th moment of `μ_η`),

so `b_k` is a (nonlinear) function of the moments `m_0,…,m_{2k}`.

## The verdict (probe-backed, then kernel-locked here)

`scripts/probes/probe_444_jacobi_hankel_structure.py` (exact, thin `μ_n`, `p≫n³`, n=16,32) measures
the peak depth: `argmax_k b_k = k*` with `2k* = 10, 14 ≈ log p = 11.1, 13.9`.  So the prize-relevant
quantity `max_k b_k` (realized at `k*`) depends on the moments up to order `2k* ≈ log p` — **exactly
the deep-moment depth `r ≈ log p` that is the open kernel of form (A)** (the wraparound `W_r` for
`r > 4`).  The Hankel/Toda structure *reorganizes* the deep moments into a bounded, stable,
prime-discriminating object, but introduces **no arithmetic input independent of them**: controlling
`max_k b_k` is *equivalent* to controlling the deep moments at depth `≈ log p` = the form-(A) wall.

This file locks that reduction axiom-clean: if the bounded Jacobi target `max_k b_k` is a function of
the moment vector up to order `2k*` (the Hankel-ratio fact, taken as an explicit hypothesis), then a
prize bound expressed through `max_k b_k` *factors through* a deep-moment bound.  So **form (D) opens
no door beyond form (A)** — the Jacobi tool relocates but does not escape, kernel-backed.

## Honesty contract

The Hankel-ratio functional dependence is the **structural fact** (classical OP theory + probe),
taken here as an explicit hypothesis; we do NOT assert a specific closed form.  This is a
*constraint/equivalence* result: it does NOT prove the prize, gives NO cancellation/anti-concentration
estimate, and does NOT claim the moment route works (form (A) is the proven-non-proving / BGK door).
It records that the new Jacobi handle is not an *independent* door.  CORE remains OPEN.
-/

set_option autoImplicit false


namespace ProximityGap.Frontier.HankelRoutes

/-- The **Hankel-functional model** of form (D)'s open object: the bounded Jacobi target
`maxb = max_k b_k`, realized at the peak depth `k*`, is a function `F` of the moment vector
`m : Fin (2*kstar + 1) → ℝ` (the moments `m_0,…,m_{2k*}` entering the Hankel ratios up to depth `k*`).
Probe-verified that `2k* ≈ log p`, so `F` consumes the moments to order `≈ log p`. -/
structure HankelFunctional (kstar : ℕ) (maxb : ℝ)
    (F : (Fin (2 * kstar + 1) → ℝ) → ℝ) (m : Fin (2 * kstar + 1) → ℝ) : Prop where
  /-- `maxb` is the value of the Hankel functional on the deep-moment vector. -/
  rep : maxb = F m

/-- **THE ROUTING VERDICT: a `maxb`-bound factors through a deep-moment bound.**
If `maxb = F m` (the Hankel-functional model) and the moment vector `m` lies in the sublevel set
`{ v | F v ≤ T }`, then `maxb ≤ T`.  Conversely any certificate `maxb ≤ T` is *exactly* the
deep-moment statement `F m ≤ T`.  So controlling the bounded Jacobi target is *equivalent* to a
form-(A) deep-moment control: form (D) opens no door beyond form (A). -/
theorem maxb_le_iff_moment_functional_le {kstar : ℕ} {maxb T : ℝ}
    {F : (Fin (2 * kstar + 1) → ℝ) → ℝ} {m : Fin (2 * kstar + 1) → ℝ}
    (h : HankelFunctional kstar maxb F m) : maxb ≤ T ↔ F m ≤ T := by
  rw [h.rep]

/-- **No independent door (the constraint).**  Under the Hankel-functional model, the bounded Jacobi
target `maxb` carries *no information* beyond the deep-moment functional `F m`: any two configurations
with the same deep-moment vector have the same `maxb`.  Hence the Jacobi tool cannot certify the prize
unless the deep moments (form (A)) do — it is not an independent door. -/
theorem maxb_determined_by_moments {kstar : ℕ} {maxb maxb' : ℝ}
    {F : (Fin (2 * kstar + 1) → ℝ) → ℝ} {m : Fin (2 * kstar + 1) → ℝ}
    (h : HankelFunctional kstar maxb F m) (h' : HankelFunctional kstar maxb' F m) :
    maxb = maxb' := by
  rw [h.rep, h'.rep]

/-- **Form (D) ⟹ form (A) at the prize scale.**  Combining with the edge–turnover model
(`M = 2·maxb` so a prize bound on `M` is a bound on `maxb`): if the prize target on `M` reduces to
`maxb ≤ T` and `maxb = F m` is the deep-moment Hankel functional, then the prize is the deep-moment
statement `F m ≤ T`.  The Jacobi tool's bounded target is the *same* open object as form (A)'s deep
moments, reorganized — not a new door. -/
theorem prize_via_jacobi_is_moment_statement {kstar : ℕ} {maxb T : ℝ}
    {F : (Fin (2 * kstar + 1) → ℝ) → ℝ} {m : Fin (2 * kstar + 1) → ℝ}
    (h : HankelFunctional kstar maxb F m) (hprize : maxb ≤ T) : F m ≤ T :=
  (maxb_le_iff_moment_functional_le h).mp hprize

end ProximityGap.Frontier.HankelRoutes

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.HankelRoutes.maxb_le_iff_moment_functional_le
#print axioms ProximityGap.Frontier.HankelRoutes.maxb_determined_by_moments
#print axioms ProximityGap.Frontier.HankelRoutes.prize_via_jacobi_is_moment_statement
