/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Real.Basic

/-!
# Door-(iv) constraint: the worst-frequency half-mass is BALANCED — no "drop-a-half" descent (#444)

The prize is localized (`_DoorIVHalfMassFactorization`, `_DoorIVHalfMassEquivalence`) to bounding the
worst-frequency half-mass `H(n) = max_b (‖A_b‖ + ‖B_b‖)`, where `η_b = Σ_{y∈μ_n} e_p(b·y) = A_b + B_b`
splits along the index-2 subgroup `μ_{n/2} < μ_n` into the subgroup half `A_b` and the coset half `B_b`.

A natural **dyadic-descent lever** would try to throw away the *lighter* of the two half-sums and bound
`‖A_b + B_b‖` by (a function of) the *heavier* half alone — reducing `H(n)` to a sum over the thinner
`μ_{n/2}`.  For that lever to gain a `√`-factor it needs the worst-`b` halves to be **imbalanced**
(one half dominant, the other negligible).

PROBE (`scripts/probes/probe_dooriv_halfmass_balance{,2}.py`; proper `μ_n`, `p ≫ n³`, structured
primes, never `n = q-1`; FULL `F_p*` scan at `n = 16` over two distinct primes, sampled for larger `n`):
define the balance ratio `r(b) = min(‖A_b‖,‖B_b‖) / max(‖A_b‖,‖B_b‖) ∈ [0,1]` (`1` = perfectly
balanced).  Over all frequencies the mean is `r̄ ≈ 0.44`, but **at the worst frequency `b*` it is
`r(b*) ≈ 0.78–0.80`** (full scans), a `~1.75–1.80×` *enrichment* toward balance; in the deeper-`β`
sampled regime `r(b*) ≈ 0.93–0.9996` (even more balanced).  The worst-`b` orbit is systematically
**balance-enriched**: the two coset-halves carry comparable mass.

CONSEQUENCE (this file, axiom-clean).  At the worst `b` the coherence is full (`ρ(b*) = 1`,
`_DoorIVCoherenceSlackVacuousAtArgmax` / same-ray `_DoorIVCosetHalfCoherence`), so the two halves are
collinear and `‖A + B‖ = ‖A‖ + ‖B‖`.  If in addition the halves are *balanced* (`‖A‖ = ‖B‖`), the
period norm is **exactly twice either single half-norm**: `‖A + B‖ = 2‖A‖ = 2‖B‖`.  Therefore a lever
that bounds `‖A + B‖` using only one half-norm can never improve on the trivial constant-2 factor — it
cannot supply a `√`-saving, because no half is negligible.  Quantitatively, dropping the lighter half
loses at most the *constant* factor `1 + r ≤ 2` (and at worst-`b`, where `r → 1`, exactly `2`), never a
factor that grows with `n`.  The "drop-a-half" descent is a DEAD door-(iv) lever.

This is a **refutation with mechanism** (a precisely-mapped dead lever), not a CORE/cancellation/capacity
claim: it does not bound `M(n)`; it shows the dyadic-imbalance descent shape cannot.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVHalfMassBalanceAtArgmax

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The **balance ratio** of the two coset-half sums: `min(‖A‖,‖B‖) / max(‖A‖,‖B‖)`.  Equals `1` iff
the two half-norms agree (perfect balance), and is small when one half dominates. -/
noncomputable def balance (A B : E) : ℝ := min ‖A‖ ‖B‖ / max ‖A‖ ‖B‖

/-- The balance ratio lies in `[0,1]`. -/
theorem balance_nonneg (A B : E) : 0 ≤ balance A B := by
  unfold balance
  exact div_nonneg (le_min (norm_nonneg _) (norm_nonneg _)) (le_max_of_le_left (norm_nonneg _))

theorem balance_le_one (A B : E) : balance A B ≤ 1 := by
  unfold balance
  rcases eq_or_lt_of_le (le_max_of_le_left (norm_nonneg A) : (0:ℝ) ≤ max ‖A‖ ‖B‖) with h | h
  · simp [← h]
  · rw [div_le_one h]; exact min_le_max

/-- **Balance is symmetric** in the two halves. -/
theorem balance_comm (A B : E) : balance A B = balance B A := by
  unfold balance; rw [min_comm, max_comm]

/-- **Perfect balance ⇔ equal half-norms.**  When both halves are nonzero, `balance = 1` exactly when
`‖A‖ = ‖B‖`. -/
theorem balance_eq_one_iff {A B : E} (hA : 0 < ‖A‖) (_hB : 0 < ‖B‖) :
    balance A B = 1 ↔ ‖A‖ = ‖B‖ := by
  unfold balance
  have hmax : 0 < max ‖A‖ ‖B‖ := lt_max_of_lt_left hA
  rw [div_eq_one_iff_eq (ne_of_gt hmax)]
  constructor
  · intro h
    -- min = max forces equality
    rcases le_total ‖A‖ ‖B‖ with hle | hle
    · rw [min_eq_left hle, max_eq_right hle] at h; exact h
    · rw [min_eq_right hle, max_eq_left hle] at h; exact h.symm
  · intro h; rw [h, min_self, max_self]

/-- **At full coherence and perfect balance, the peak is exactly twice either half.**  If the two
halves are collinear (`‖A + B‖ = ‖A‖ + ‖B‖`, the proven same-ray fact at the worst frequency) and
balanced (`‖A‖ = ‖B‖`), then `‖A + B‖ = 2‖A‖`.  Hence the full peak mass is carried *equally* by the
two halves; neither is negligible. -/
theorem norm_eq_two_mul_of_coherent_balanced {A B : E}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hbal : ‖A‖ = ‖B‖) :
    ‖A + B‖ = 2 * ‖A‖ := by
  rw [hcoh, hbal]; ring

/-- **A single-half bound cannot beat the constant factor 2 at the balanced worst frequency.**  Suppose
a "drop-a-half" lever bounds the period norm by a function `g` of the heavier half-norm only, of the
shape `‖A + B‖ ≤ g (max ‖A‖ ‖B‖)`.  At the worst frequency the halves are collinear and balanced, so
`max ‖A‖ ‖B‖ = ‖A‖` and the true period norm is `2‖A‖`.  Therefore the lever is forced to satisfy
`g (max ‖A‖ ‖B‖) ≥ 2 · (max ‖A‖ ‖B‖)`: it must *already* pay the full doubled mass — it gets no
`√`-saving from discarding the (equally heavy) other half. -/
theorem single_half_bound_pays_full_at_balanced {A B : E} {g : ℝ → ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hbal : ‖A‖ = ‖B‖)
    (hbound : ‖A + B‖ ≤ g (max ‖A‖ ‖B‖)) :
    2 * max ‖A‖ ‖B‖ ≤ g (max ‖A‖ ‖B‖) := by
  have hmax : max ‖A‖ ‖B‖ = ‖A‖ := by rw [hbal, max_self]
  have htwo : ‖A + B‖ = 2 * ‖A‖ := norm_eq_two_mul_of_coherent_balanced hcoh hbal
  calc 2 * max ‖A‖ ‖B‖ = 2 * ‖A‖ := by rw [hmax]
    _ = ‖A + B‖ := htwo.symm
    _ ≤ g (max ‖A‖ ‖B‖) := hbound

/-- **The constant factor lost by dropping the lighter half is `1 + balance`, hence at most `2`.**  In
the collinear (full-coherence) regime the true period norm `‖A‖ + ‖B‖` equals the heavier half-norm
times `(1 + balance A B)`.  Since `balance ≤ 1`, dropping the lighter half loses at most a factor of
`2` — a *constant*, never a factor growing with `n`.  At the balanced worst frequency `balance → 1`, so
the loss is exactly the full factor `2`; there is no thin/heavy asymmetry to exploit. -/
theorem coherent_norm_eq_max_mul_one_add_balance {A B : E}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) :
    ‖A + B‖ = max ‖A‖ ‖B‖ * (1 + balance A B) := by
  unfold balance
  rcases le_total ‖A‖ ‖B‖ with hle | hle
  · rw [min_eq_left hle, max_eq_right hle, hcoh]
    rcases eq_or_lt_of_le (norm_nonneg B) with hB | hB
    · -- ‖B‖ = 0 forces ‖A‖ = 0
      have hA : ‖A‖ = 0 := le_antisymm (by rw [← hB] at hle; exact hle) (norm_nonneg _)
      rw [hA, ← hB]; ring
    · field_simp; ring
  · rw [min_eq_right hle, max_eq_left hle, hcoh]
    rcases eq_or_lt_of_le (norm_nonneg A) with hA | hA
    · have hB : ‖B‖ = 0 := le_antisymm (by rw [← hA] at hle; exact hle) (norm_nonneg _)
      rw [hB, ← hA]; ring
    · field_simp

/-- **Any positive balance floor forces the single-half certificate to pay `1 + r`.**  In the
full-coherence regime, if the lighter half is at least an `r`-fraction of the heavier half
(`r ≤ balance A B`), then any bound using only the heavier half must already allow
`(1+r)·max(‖A‖,‖B‖)`.  The probed worst frequencies have `r` close to `1`, so this descent lever pays
an order-one factor near `2`, not a shrinking factor that could supply square-root cancellation. -/
theorem single_half_bound_pays_balance_floor {A B : E} {g : ℝ → ℝ} {r : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hr : r ≤ balance A B)
    (hbound : ‖A + B‖ ≤ g (max ‖A‖ ‖B‖)) :
    (1 + r) * max ‖A‖ ‖B‖ ≤ g (max ‖A‖ ‖B‖) := by
  have hmax_nonneg : 0 ≤ max ‖A‖ ‖B‖ := le_max_of_le_left (norm_nonneg A)
  have hfactor : 1 + r ≤ 1 + balance A B := by linarith
  have hmul : (1 + r) * max ‖A‖ ‖B‖ ≤ (1 + balance A B) * max ‖A‖ ‖B‖ := by
    exact mul_le_mul_of_nonneg_right hfactor hmax_nonneg
  have hmul' : (1 + r) * max ‖A‖ ‖B‖ ≤ max ‖A‖ ‖B‖ * (1 + balance A B) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  calc
    (1 + r) * max ‖A‖ ‖B‖ ≤ max ‖A‖ ‖B‖ * (1 + balance A B) := hmul'
    _ = ‖A + B‖ := (coherent_norm_eq_max_mul_one_add_balance hcoh).symm
    _ ≤ g (max ‖A‖ ‖B‖) := hbound

/-- **The descent loss factor is bounded by `2`, uniformly.**  At any full-coherence frequency, the
ratio of the true period norm to the heavier half-norm is `1 + balance ≤ 2`.  So no dyadic
drop-a-half step can lose more than a constant factor `2`, and (by the probe) at the worst frequency it
loses essentially the full `2`: the descent buys no `√`-cancellation. -/
theorem descent_loss_le_two {A B : E} (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖)
    (h : 0 < max ‖A‖ ‖B‖) :
    ‖A + B‖ ≤ 2 * max ‖A‖ ‖B‖ := by
  rw [coherent_norm_eq_max_mul_one_add_balance hcoh]
  have : (1 : ℝ) + balance A B ≤ 2 := by linarith [balance_le_one A B]
  calc max ‖A‖ ‖B‖ * (1 + balance A B) ≤ max ‖A‖ ‖B‖ * 2 := by
        exact mul_le_mul_of_nonneg_left this (le_of_lt h)
    _ = 2 * max ‖A‖ ‖B‖ := by ring

/-- **At coherent perfect balance, the single-half loss ratio is exactly `2`.**  This is the sharp
endpoint behind `descent_loss_le_two`: when the two halves are same-ray and equally large, normalizing
by the heavier half gives precisely a factor of two.  Thus a dyadic descent that keeps only one half is
not hiding any shrinking `n`-dependent gain at the probed balanced worst frequencies; the obstruction is
already saturated at the constant endpoint. -/
theorem descent_loss_eq_two_of_coherent_balanced {A B : E}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hbal : ‖A‖ = ‖B‖)
    (hpos : 0 < max ‖A‖ ‖B‖) :
    ‖A + B‖ / max ‖A‖ ‖B‖ = 2 := by
  have hnorm : ‖A + B‖ = 2 * max ‖A‖ ‖B‖ := by
    calc
      ‖A + B‖ = 2 * ‖A‖ := norm_eq_two_mul_of_coherent_balanced hcoh hbal
      _ = 2 * max ‖A‖ ‖B‖ := by rw [hbal, max_self]
  rw [hnorm]
  field_simp [ne_of_gt hpos]

end ArkLib.ProximityGap.Frontier.DoorIVHalfMassBalanceAtArgmax

-- Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}).
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassBalanceAtArgmax.single_half_bound_pays_full_at_balanced
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassBalanceAtArgmax.single_half_bound_pays_balance_floor
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassBalanceAtArgmax.descent_loss_le_two
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassBalanceAtArgmax.descent_loss_eq_two_of_coherent_balanced
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassBalanceAtArgmax.coherent_norm_eq_max_mul_one_add_balance
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassBalanceAtArgmax.balance_eq_one_iff
