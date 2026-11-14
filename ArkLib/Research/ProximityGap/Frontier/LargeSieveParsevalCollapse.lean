/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# wf-NB: the additive large sieve on `{η_b}` collapses to Parseval (#407)

**Lane wf-NB (subconvexity / spectral, additive large sieve).** A genuinely new packaging of
the deep-moment object: the depth-`r` power-sum `∑_b ‖η_b‖^{2r} = q·E_r` is the Fourier `L²`
mass of the `r`-fold sumset measure `f = 1_{μ_n}^{*r}`, so the family `{η_b^r}_b` is the
additive-character family of `f`. The additive **large sieve** (Montgomery–Vaughan / Gallagher)
bounds, for frequencies `b/q` that are `δ`-separated mod 1 and `f` supported on `M` residues,

  `∑_b ‖∑_s f(s) e(b s/q)‖² ≤ (M + δ⁻¹) · ∑_s ‖f(s)‖².`

For the prize family the frequencies `b/q` (b over all of `F_q`) form the **full** residue
system, separated by exactly `δ = 1/q`, and `f` is supported on `M = q` residues. So the
large-sieve RHS is `(q + q)·‖f‖₂² = 2q·E_r`. But Parseval/orthogonality gives the **exact**
value `∑_b ‖η_b‖^{2r} = q·E_r` (proven in `SubgroupGaussSumRawMoment`). Therefore the additive
large sieve produces a bound that is exactly `2×` the exact moment — it strictly *loses* a
factor 2 relative to the Parseval equality and supplies **no** sub-trivial control. This file
is the axiom-clean guardrail recording that collapse abstractly: with the true separation
`δ⁻¹ = q`, the large-sieve constant `q + δ⁻¹ = 2q` and the resulting moment bound `2·(q·E)` is
never below the exact moment `q·E`. The lane is **pinned to the §6 `L²` wall** (the moment
inequality is second-order and cannot beat the diagonal it is built from).

Numerics (`scripts/probes/probe_wf2NB_largesieve.py`, `probe_wf2NB_sparsesieve.py`): the
Parseval identity `q·E_r = ∑‖η‖^{2r}` holds to machine precision at every prize prime; the
large-sieve sup bound is uniformly the Parseval bound scaled by `2^{1/2r} > 1`; and at the
prize point `(n=16, β=4, m=4096)` the Parseval sup bound reaches the floor
`√(2n log(q/n))/√n ≈ 4.08` only at `r ≈ log₂ m = 12`, while the extra large-sieve factor keeps
it strictly above the floor at every finite `r`. No closure; an honest pin with a countproof.

Issue #407, lane wf-NB.
-/

namespace ProximityGap.Frontier.LargeSieveParsevalCollapse

/-- The additive large-sieve constant for `M` support points and frequency separation `δ`:
`M + δ⁻¹`. For the prize family `M = q` and the true separation is `δ = 1/q`, so `δ⁻¹ = q`. -/
noncomputable def largeSieveConst (M deltaInv : ℝ) : ℝ := M + deltaInv

/-- The large-sieve moment bound on `∑_b ‖η_b^r‖²` with support `M`, separation `δ`, and
`L²`-mass `E` of the `r`-fold sumset measure. -/
noncomputable def largeSieveBound (M deltaInv E : ℝ) : ℝ := largeSieveConst M deltaInv * E

/-- The **exact** Parseval value of the same moment for the prize family:
`∑_b ‖η_b‖^{2r} = q · E_r` (proven axiom-clean in `SubgroupGaussSumRawMoment`). -/
noncomputable def parsevalExact (q E : ℝ) : ℝ := q * E

/--
**The collapse, exact form.** With the *true* separation `δ⁻¹ = q` of the full residue
frequency system and support `M = q`, the additive large-sieve bound is exactly `2·(q·E)`,
i.e. exactly twice the Parseval-exact moment.
-/
theorem largeSieve_eq_two_parseval (q E : ℝ) :
    largeSieveBound q q E = 2 * parsevalExact q E := by
  unfold largeSieveBound largeSieveConst parsevalExact
  ring

/--
**Vacuity barrier (the §6 `L²` wall).** For nonnegative field size `q` and moment mass `E`,
the additive large-sieve bound is never below the exact Parseval moment: it loses (here, by a
factor 2 with the true separation). Hence the large sieve supplies no sub-trivial improvement
over the diagonal/Parseval equality it is built from.
-/
theorem parseval_le_largeSieve {q E : ℝ} (hq : 0 ≤ q) (hE : 0 ≤ E) :
    parsevalExact q E ≤ largeSieveBound q q E := by
  rw [largeSieve_eq_two_parseval]
  have hpe : 0 ≤ parsevalExact q E := by
    unfold parsevalExact; exact mul_nonneg hq hE
  linarith

/--
**Sup-tool vacuity.** Taking `(2r)`-th roots, the large-sieve sup bound on `M(n) = max_b ‖η_b‖`
is `(2 q E)^{1/(2r)}`, never below the Parseval sup bound `(q E)^{1/(2r)}`. The large-sieve
packaging is strictly the wrong side of the exact moment for every `r`; in particular it
cannot dip below the floor at any finite depth where Parseval itself only *touches* it.
-/
theorem largeSieve_sup_ge_parseval_sup {q E : ℝ} (r : ℕ) (hr : 0 < r)
    (hq : 0 ≤ q) (hE : 0 ≤ E) :
    (parsevalExact q E) ^ ((1 : ℝ) / (2 * r)) ≤
      (largeSieveBound q q E) ^ ((1 : ℝ) / (2 * r)) := by
  have hpe : 0 ≤ parsevalExact q E := mul_nonneg hq hE
  have hmono := parseval_le_largeSieve hq hE
  have hexp : 0 ≤ (1 : ℝ) / (2 * r) := by positivity
  exact Real.rpow_le_rpow hpe hmono hexp

end ProximityGap.Frontier.LargeSieveParsevalCollapse
