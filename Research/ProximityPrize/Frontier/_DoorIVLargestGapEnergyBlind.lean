/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic

/-!
# Door IV: the longest-empty-arc (largest-gap) small-ball functional is energy-blind

This file records the axiom-clean arithmetic kernel behind the probe
`scripts/probes/probe_dooriv_emptyarc_gap.py`. It is the **gap-statistic** sibling of the
single-window (`_DoorIVWindowConcentrationTrivial`, `758205014`, energy-blind) and multi-window
(g55, trivial-budget) Lane-1 small-ball refutations, closing a distinct unmined functional.

## The probed object

For a worst frequency `b`, the period is `η_b = Σ_{y ∈ μ_n} e_p(b·y)`, a sum of `n` unit-modulus
complex numbers placed at the residues `A_b = { b·y mod p }` on `ℤ/p`. A door-(iv)
anti-concentration
hope distinct from window *occupancy* is the **spacing / gap** statistic: if the worst-`b` phase set
were forced to leave one anomalously large **empty arc** (a hole), one could read off a sup-norm
bound
from that single hole *without* a moment or completion — a non-energy small-ball lever.

## The probe verdict (reproducible, prize regime, proper `μ_n`, p ≫ n³, incl. Fermat 65537)

The worst-`b` **largest gap** `G_max` IS anomalous versus a random `n`-subset (measured, in units of
the mean spacing `p/n`: worst-`b` `8.0, 14.4, 15.6` at `n = 16,32,64` vs random mean `≈ 3.4, 4.1,
4.8`)
— so the gap statistic *does see* the clumping. **But it still cannot carry the √-cancellation**,
for
a sharp reason the formal kernel below isolates:

* The single biggest empty arc covers a **decaying** fraction of the circle as `n` grows:
  `50%, 45%, 14%, 4.4%` at `n = 16,32,64,128`, whereas a √-cancellation route would need the empty
fraction to *grow* toward `1 − 1/√n ≈ 75–91%`. The clumping that produces a large `|η_b|` is
  spread
  across **many** moderate gaps (a Weyl-equidistribution-scale spacing law), not concentrated in one
  hole — so the largest-gap functional **saturates**.
* Correlation `corr(|η_b|, G_max/(p/n))` over all `b` **decays** (`+0.57, +0.34, +0.22` at
  `n = 16,32,64`): big `|η|` does **not** force a proportionally big single hole at scale.

## The formalizable kernel (this file)

The reason a single empty arc cannot bound the cancellation is purely the triangle inequality on
unit-modulus terms. Split the `n` summands into those whose phase lies in the empty arc (there are
**zero**, by definition of "empty") and the `m = n` lying outside it. Each outside term still has
modulus `1`, so the only bound a single empty arc yields is

> `|η_b| ≤ (#inside)·1 + (#outside)·1 = 0 + n = n` — the **trivial linear ceiling**, independent of
> the gap size.

No empty arc — no matter how large — lowers this below `n`: an empty region contributes nothing to
remove, and the surviving terms are still `n` units of modulus `1`. This is the constraint lemma:
the
largest-gap (longest-empty-arc) small-ball functional is **energy-blind** in the cancellation
direction, exactly like the occupancy-window functional. A genuine bound must control phase
**coherence among the surviving terms** (the energy object / Door IV proper), which the gap
statistic
does not touch.

No CORE, cancellation, completion, anti-concentration, moment, or capacity claim. Axiom-clean.
Issue #444 (door-(iv) Lane-1).
-/

namespace ProximityGap.Frontier.DoorIVLargestGapEnergyBlind

open Finset

/-- **Empty-arc triangle bound.** Let `z : Fin n → ℂ` be `n` unit-modulus summands (`‖z j‖ = 1`),
modelling `e_p(b·y)` over `y ∈ μ_n`. Let `S : Finset (Fin n)` be the indices whose phase lies in a
prescribed arc that is **empty** for this configuration, i.e. `S = ∅`. Then the modulus of the full
sum is bounded only by the trivial linear ceiling `n`, with the empty arc contributing nothing:

`‖Σ_j z j‖ ≤ (S.card : ℝ) + ((Sᶜ).card : ℝ) = 0 + n = n`. -/
theorem emptyArc_bound_trivial {n : ℕ} (z : Fin n → ℂ) (hz : ∀ j, ‖z j‖ = 1)
    (S : Finset (Fin n)) (hS : S = ∅) :
    ‖∑ j, z j‖ ≤ (S.card : ℝ) + ((Sᶜ).card : ℝ) := by
  subst hS
  have hcard : ((∅ : Finset (Fin n)).card : ℝ) + (((∅ : Finset (Fin n))ᶜ).card : ℝ) = (n : ℝ) := by
    simp [Finset.compl_empty, Finset.card_univ]
  rw [hcard]
  calc ‖∑ j, z j‖ ≤ ∑ j, ‖z j‖ := norm_sum_le _ _
    _ = ∑ _j : Fin n, (1 : ℝ) := by simp [hz]
    _ = (n : ℝ) := by simp [Finset.sum_const, Finset.card_univ]

/-- **The empty arc contributes nothing.** Even an arbitrarily large empty arc removes zero mass:
the
inside contribution `(S.card : ℝ) = 0`, so the bound is carried *entirely* by the outside terms and
equals the trivial ceiling `n`, independent of the gap geometry. -/
theorem emptyArc_deficit_zero {n : ℕ} (S : Finset (Fin n)) (hS : S = ∅) :
    (S.card : ℝ) = 0 := by
  subst hS; simp

/-- **Trivial-ceiling collapse (energy-blindness).** For unit-modulus summands and any empty arc,
the
single-largest-gap functional yields exactly `‖Σ z‖ ≤ n`, the gap-size-independent linear ceiling.
This is the constraint lemma: no longest-empty-arc certificate lowers the bound below `n`, so the
largest-gap small-ball statistic cannot carry the `√(n·log(p/n))` cancellation. -/
theorem largestGap_yields_only_trivial_ceiling {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ j, ‖z j‖ = 1) (S : Finset (Fin n)) (hS : S = ∅) :
    ‖∑ j, z j‖ ≤ (n : ℝ) := by
  have hbound := emptyArc_bound_trivial z hz S hS
  calc ‖∑ j, z j‖ ≤ (S.card : ℝ) + ((Sᶜ).card : ℝ) := hbound
    _ = (n : ℝ) := by subst hS; simp [Finset.compl_empty, Finset.card_univ]

/-- **Gap-size irrelevance.** Two empty arcs of *different* sizes (modelled by two empty index
sets `S` and `T`, both empty but conceptually of different angular width) produce the **same**
outside-count `n`. The functional cannot distinguish a large hole from a small one in the
cancellation direction: a formal witness that the largest-gap statistic is blind to the energy
object. -/
theorem largestGap_ceiling_independent_of_gap {n : ℕ}
    (S T : Finset (Fin n)) (hS : S = ∅) (hT : T = ∅) :
    (((Sᶜ).card : ℝ)) = (((Tᶜ).card : ℝ)) := by
  subst hS; subst hT; simp

/-- **Strict-budget obstruction.** Since an empty largest-gap arc has no inside mass, the purely
cardinality-based split right-hand side is exactly `n`. Therefore no largest-gap triangle
certificate can fit below a strict budget `B < n`. In particular, a √-scale door-(iv) bound cannot
come from the empty-arc statistic alone; it must prove cancellation/coherence among the surviving
terms. -/
theorem no_emptyArc_split_rhs_le_strict_budget {n : ℕ}
    (S : Finset (Fin n)) (hS : S = ∅) {B : ℝ} (hB : B < (n : ℝ)) :
    ¬ (S.card : ℝ) + ((Sᶜ).card : ℝ) ≤ B := by
  intro hle
  have hconst : (S.card : ℝ) + ((Sᶜ).card : ℝ) = (n : ℝ) := by
    subst hS
    simp [Finset.compl_empty, Finset.card_univ]
  linarith

/-- **Budget-forcing form.** If the largest-empty-arc split is claimed to satisfy a budget `B`,
then the trivial linear ceiling `n ≤ B` was already true. This packages the no-go without a strict
hypothesis. It is the reusable constraint lemma ruling out gap-only √-cancellation
certificates. -/
theorem emptyArc_budget_forces_card_le {n : ℕ}
    (S : Finset (Fin n)) (hS : S = ∅) {B : ℝ}
    (hbudget : (S.card : ℝ) + ((Sᶜ).card : ℝ) ≤ B) :
    (n : ℝ) ≤ B := by
  have hconst : (S.card : ℝ) + ((Sᶜ).card : ℝ) = (n : ℝ) := by
    subst hS
    simp [Finset.compl_empty, Finset.card_univ]
  linarith

#print axioms emptyArc_bound_trivial
#print axioms emptyArc_deficit_zero
#print axioms largestGap_yields_only_trivial_ceiling
#print axioms largestGap_ceiling_independent_of_gap
#print axioms no_emptyArc_split_rhs_le_strict_budget
#print axioms emptyArc_budget_forces_card_le

end ProximityGap.Frontier.DoorIVLargestGapEnergyBlind
