/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Real.Basic

/-!
# Door-(iv) constraint: the worst-`b` halves are coherent but STRICTLY IMBALANCED — the symmetric "÷2" descent is non-tight (#444)

The prize is localized (`_DoorIVHalfMassFactorization`, `_DoorIVHalfMassEquivalence`) to the
worst-frequency half-mass `H(n) = max_b (‖A_b‖ + ‖B_b‖)`, where `η_b = A_b + B_b` splits along the
index-2 subgroup `μ_{n/2} < μ_n` into the subgroup half `A_b` and the coset half `B_b`.

It is already in-tree (`_DoorIVHalfMassBalanceAtArgmax`, same-ray at worst-`b`) that at the worst
frequency the two halves are **collinear** (`ρ(b*) = 1`, `‖A + B‖ = ‖A‖ + ‖B‖`).  That file's
conditional theorems further assume *perfect balance* (`‖A‖ = ‖B‖`) and conclude `‖A + B‖ = 2‖A‖`,
the symmetric "÷2" descent step.

**This file pins the missing fact: the balance hypothesis is NOT met at the TRUE worst frequency.**

PROBE (`scripts/probes/probe_dooriv_worstb_coherence_deficit_law.py` + a FULL coset-space scan
reconciliation; proper `μ_n`, `p ≫ n³`, odd `m`, never `n = q-1`; the coset space `F_p^* / μ_n ≅ ℤ_m`
is scanned EXHAUSTIVELY over all `m` cosets via `g^t`, not sampled):
- The deficit `1 − ρ(b*)` is **identically `0`** at every `n = 16..256` (angle `∠(A_{b*}, B_{b*}) = 0`
  to machine precision): the worst frequency is exactly the one that phase-aligns the two halves, so
  door-(iv) coset-half *coherence* supplies **zero** destructive interference (route confirmed dead).
- But the balance ratio at the **TRUE** worst-`b` (full coset scan, no sampling) is
  `r(b*) = 0.8907` (`n=16`), `0.6088` (`n=32`), `0.7853` (`n=64`) — bounded **strictly away from `1`**
  and *non-monotone*.  This CORRECTS the earlier *sampled* probe's "balance-enriched, `r → 0.93..0.9996`"
  reading, which was a **sampling artifact**: scanning only `~4000` random cosets lands on a
  near-max coset that is *more* balanced than the true argmax.  The true worst-`b` halves are coherent
  but genuinely **unequal in magnitude** (`‖A‖ ≠ ‖B‖`).

CONSEQUENCE (this file, axiom-clean).  Under coherence with **strict** imbalance `‖A‖ ≠ ‖B‖`, the
period norm is **strictly below** the symmetric ceiling `2·max(‖A‖,‖B‖)`:
    `‖A + B‖ < 2 · max(‖A‖, ‖B‖)`  with a *quantified* gap `(max − min)`.
Equivalently `‖A + B‖ = 2·max − (max − min)`, so the symmetric "÷2" descent over-counts by exactly the
half-mass imbalance `(max − min) > 0`.  Therefore any dyadic descent that *assumes* `‖A‖ = ‖B‖` (the
balanced-symmetric simplification) is **inapplicable at the true worst frequency**: the recursion the
prize reduces to is genuinely **asymmetric**, and `‖A‖ = ‖B‖` may not be invoked as a hypothesis.

This is a **refutation with mechanism** (a precisely-mapped non-tightness of the symmetric descent), not
a CORE/cancellation/completion/capacity claim: it does not bound `M(n)`; it forbids the balanced-descent
shortcut by exhibiting the strict imbalance that holds at the worst frequency.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVWorstBCoherentImbalance

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **Coherent peak in heavier/lighter form.**  At full coherence (`‖A + B‖ = ‖A‖ + ‖B‖`) the period
norm equals the heavier half-norm plus the lighter one: `‖A + B‖ = max ‖A‖ ‖B‖ + min ‖A‖ ‖B‖`. -/
theorem coherent_norm_eq_max_add_min {A B : E} (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) :
    ‖A + B‖ = max ‖A‖ ‖B‖ + min ‖A‖ ‖B‖ := by
  rw [hcoh]
  rcases le_total ‖A‖ ‖B‖ with h | h
  · rw [max_eq_right h, min_eq_left h, add_comm]
  · rw [max_eq_left h, min_eq_right h]

/-- **Symmetric "÷2" descent over-counts by exactly the imbalance.**  At full coherence,
`2·max(‖A‖,‖B‖) − ‖A + B‖ = max(‖A‖,‖B‖) − min(‖A‖,‖B‖)`: the gap between the symmetric ceiling and the
true period norm is precisely the half-mass imbalance. -/
theorem two_mul_max_sub_norm_eq_imbalance {A B : E} (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) :
    2 * max ‖A‖ ‖B‖ - ‖A + B‖ = max ‖A‖ ‖B‖ - min ‖A‖ ‖B‖ := by
  rw [coherent_norm_eq_max_add_min hcoh]; ring

/-- **Strict imbalance ⇒ strictly positive descent gap.**  If the two half-norms differ
(`‖A‖ ≠ ‖B‖`) then `min < max`, so the symmetric-descent over-count is strictly positive. -/
theorem imbalance_pos_of_ne {A B : E} (hne : ‖A‖ ≠ ‖B‖) :
    0 < max ‖A‖ ‖B‖ - min ‖A‖ ‖B‖ := by
  have hlt : min ‖A‖ ‖B‖ < max ‖A‖ ‖B‖ := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h
  linarith

/-- **At a coherent but strictly imbalanced worst frequency, the symmetric ceiling is NOT tight.**
If the halves are collinear (`‖A + B‖ = ‖A‖ + ‖B‖`, proven at the worst `b`) but unequal in magnitude
(`‖A‖ ≠ ‖B‖`, the *true*-worst-`b` empirical fact this file pins), then the period norm is **strictly
below** twice the heavier half-norm:
    `‖A + B‖ < 2 · max(‖A‖, ‖B‖)`.
Hence the symmetric "÷2" descent step `‖A + B‖ = 2‖A‖` (which needs `‖A‖ = ‖B‖`) is inapplicable, and
the dyadic recursion is genuinely asymmetric. -/
theorem norm_lt_two_mul_max_of_coherent_imbalanced {A B : E}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hne : ‖A‖ ≠ ‖B‖) :
    ‖A + B‖ < 2 * max ‖A‖ ‖B‖ := by
  have hgap : 0 < max ‖A‖ ‖B‖ - min ‖A‖ ‖B‖ := imbalance_pos_of_ne hne
  have hid : 2 * max ‖A‖ ‖B‖ - ‖A + B‖ = max ‖A‖ ‖B‖ - min ‖A‖ ‖B‖ :=
    two_mul_max_sub_norm_eq_imbalance hcoh
  linarith

/-- **Normalized imbalance identity.**  At full coherence, the ratio of the true period norm to the
balanced symmetric ceiling `2·max(‖A‖,‖B‖)` is exactly the average of `1` and the lighter/heavier ratio:
`‖A+B‖/(2 max) = (1 + min/max)/2`.  This is the scale-free form of the probe mechanism: any strict
half-mass imbalance creates a concrete deficit below the balanced `÷2` descent ceiling. -/
theorem coherent_norm_div_two_mul_max_eq_avg_ratio {A B : E}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hmax : 0 < max ‖A‖ ‖B‖) :
    ‖A + B‖ / (2 * max ‖A‖ ‖B‖) =
      (1 + min ‖A‖ ‖B‖ / max ‖A‖ ‖B‖) / 2 := by
  have hmax_ne : max ‖A‖ ‖B‖ ≠ 0 := ne_of_gt hmax
  rw [coherent_norm_eq_max_add_min hcoh]
  field_simp [hmax_ne]

/-- **Strict imbalance gives a strict normalized deficit.**  Under coherence and a positive heavier
half, unequal half-norms force the normalized period norm below `1` relative to the balanced symmetric
ceiling `2·max(‖A‖,‖B‖)`.  This is the dimensionless no-go for any descent that silently replaces the
asymmetric split by a perfectly balanced one. -/
theorem coherent_imbalanced_ratio_lt_one {A B : E}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hmax : 0 < max ‖A‖ ‖B‖) (hne : ‖A‖ ≠ ‖B‖) :
    ‖A + B‖ / (2 * max ‖A‖ ‖B‖) < 1 := by
  have hlt := norm_lt_two_mul_max_of_coherent_imbalanced hcoh hne
  exact (div_lt_one (mul_pos (by norm_num) hmax)).2 hlt

/-- **The balanced-symmetric descent hypothesis is falsified at the true worst frequency.**  Contrapositive
packaging for the probe interface: if a descent argument relies on the symmetric identity
`‖A + B‖ = 2 · max(‖A‖,‖B‖)` while the halves are coherent, then it has implicitly assumed perfect
balance `‖A‖ = ‖B‖`.  Since the *true* worst-`b` halves are strictly imbalanced (empirical, full coset
scan), no such symmetric descent is available there. -/
theorem coherent_norm_eq_two_mul_max_forces_balance {A B : E}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hsym : ‖A + B‖ = 2 * max ‖A‖ ‖B‖) :
    ‖A‖ = ‖B‖ := by
  by_contra hne
  exact absurd hsym (ne_of_lt (norm_lt_two_mul_max_of_coherent_imbalanced hcoh hne))

end ArkLib.ProximityGap.Frontier.DoorIVWorstBCoherentImbalance

-- Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}).
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCoherentImbalance.norm_lt_two_mul_max_of_coherent_imbalanced
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCoherentImbalance.two_mul_max_sub_norm_eq_imbalance
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCoherentImbalance.coherent_norm_div_two_mul_max_eq_avg_ratio
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCoherentImbalance.coherent_imbalanced_ratio_lt_one
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCoherentImbalance.coherent_norm_eq_two_mul_max_forces_balance
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBCoherentImbalance.coherent_norm_eq_max_add_min
