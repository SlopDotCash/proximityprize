/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# The Chapman-Mudgal anti-resonance DICHOTOMY reduces to the BGK wall (#466)

This file formalizes the theorem-level no-go established by the thin-dyadic worst-frequency probe
`scripts/probes/probe_466_antiresonance_tower_worstb.py` (+ `_tower_only.py`): the Chapman-Mudgal
anti-resonance / dichotomy route (dossier v3 §16(D) / lines 981, 1122), stated in the W8/A
coset-SET quarter-arc language, is an **exact re-encoding of the open sup bound**, not an
independent lever.

## The dichotomy, stated on the worst frequency

The anti-resonant envelope for the worst Gauss period `M = max_{b != 0} ‖η_b‖` is
`M ~ R * sqrt(n * A)`, where `A = A2q(C_{b*})` is the worst-coset quarter-arc L2 energy and `R`
is the envelope ratio (a fitted `O(1)` constant). A prize bound
`M <= C * sqrt(n * L)`  (`L := log(p/n)`, `C` the wall constant) follows **from** the dichotomy
ONLY IF the worst-coset arc-excess is itself bounded, `A <= c * L / n` (equivalently
`A / L = O(1/n)`).

## What the probe measured (β = 4 thin `μ_n`, `n = 8..128`, exact `η`, Parseval-checked)

* The envelope value equals `R * sqrt(n * A)` at worst-b by construction, and `R := M/sqrt(nA)` is
  **`O(1)`**: `R ∈ [1.08, 1.68]` across all `(n, p)` (mean `1.45`), slowly decreasing in `n`.
* Hence the exact identity `A = M^2 / (n * R^2)` gives `A / L = C^2 / R^2` (verified to machine
  precision), and `A / L` **grows** with `n` (`0.41, 0.50, 0.71, 0.99, 1.40` at `n = 8..128`).
  The dichotomy's sufficient condition `A / L = O(1/n)` is therefore FALSE — the arc-excess free
  variable itself scales like `M^2/n` = the wall.
* Tower (Q3): the worst-b arc-excess ratio `A(μ_{2n})/A(μ_n)` has mean `1.57` (sub-`2`), but `R`
  stays pinned `≈ const` at every tower level, so the ratio only reflects the wall's own `M^2`
  growth, not a spectral gap. Combined with the non-nested worst-b (`466-r1` residue-blindness /
  worst-b-non-nested), the tower map supplies **no descent lever** (matches the wf-F4
  dyadic-descent refutation).

## This file (axiom-clean, BGK-free real algebra)

The load-bearing facts are pure real-number identities/inequalities over the envelope model, with
NO character-sum content — exactly why they are honest and why they cannot help: they show the
arc-excess certification IS the sup certification.

Let `M >= 0`, `n > 0`, `A > 0`, `L > 0`, and set the wall constant `C := M / sqrt(n*L)` and the
envelope ratio `R := M / sqrt(n*A)`.

* `antiResonanceEnvelope_ratio_sq` : `A / L = C^2 / R^2` (the exact identity; the arc-excess,
  normalized by `L`, is the squared wall constant divided by the squared envelope ratio).
* `arcExcess_ge_of_ratio_le` : if `R <= Rmax` then `A >= M^2 / (n * Rmax^2)` (a bounded envelope
  ratio forces the arc-excess to carry the full `M^2/n` mass).
* `sup_bound_of_arcExcess_bound` : the dichotomy's own implication — if `A <= c*L/n` (arc-excess
  sufficient condition) and `R <= Rmax`, then `M <= Rmax*sqrt c*sqrt(n*L)` (the prize bound), so an
  arc-excess bound with bounded envelope ratio yields the sup bound with the SAME `sqrt(n*L)` scale.
* `arcExcess_bound_reduces_to_sup_bound` : the packaging — an arc-excess bound gives the sup bound
  at the same scale, AND the exact identity shows `A` is determined by `M` and the `O(1)` ratio `R`.
  So bounding the arc-excess is EQUIVALENT to bounding `M` (no shortcut).

This is a constraint / no-go brick (rule 4): it pins the anti-resonance dichotomy as a re-encoding
of the wall. It does NOT close CORE — the open object (the worst-b quarter-arc energy `A`, equal
to `M^2/(n*R^2)` with `R = O(1)`) is exactly the sup `M` the prize needs. CORE
`M(μ_n) <= C*sqrt(n*log(p/n))` UNCHANGED/OPEN.
-/

namespace ArkLib.ProximityGap.Frontier.AntiResonanceDichotomy

open Real

/-- **The exact anti-resonance identity (probe-verified to machine precision).**
With wall constant `C := M/sqrt(nL)` and envelope ratio `R := M/sqrt(nA)`, the `L`-normalized
worst-coset arc-excess equals the squared wall constant over the squared envelope ratio:
`A / L = C^2 / R^2`. Because `R` is measured `O(1)`, this says the arc-excess (the dichotomy's free
variable) IS an `R^2`-multiple of `M^2/(nL) = C^2` — bounding it is bounding the wall. -/
theorem antiResonanceEnvelope_ratio_sq
    (M n A L : ℝ) (hn : 0 < n) (hA : 0 < A) (hL : 0 < L) (hM : 0 < M) :
    A / L = (M / Real.sqrt (n * L)) ^ 2 / (M / Real.sqrt (n * A)) ^ 2 := by
  have hnL : (0 : ℝ) < n * L := mul_pos hn hL
  have hnA : (0 : ℝ) < n * A := mul_pos hn hA
  have hsqL : Real.sqrt (n * L) ^ 2 = n * L := Real.sq_sqrt hnL.le
  have hsqA : Real.sqrt (n * A) ^ 2 = n * A := Real.sq_sqrt hnA.le
  rw [div_pow, div_pow, hsqL, hsqA]
  have hM2 : M ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hM)
  field_simp

/-- **A bounded envelope ratio forces the arc-excess to carry the full `M^2/n` mass.**
If the fitted envelope ratio `R = M/sqrt(nA) <= Rmax`, then `A >= M^2/(n*Rmax^2)`. So the arc-excess
cannot be small while `M` is large: any `Rmax`-bounded-ratio regime pins `A` at the sup scale. -/
theorem arcExcess_ge_of_ratio_le
    (M n A Rmax : ℝ) (hn : 0 < n) (hA : 0 < A) (hM : 0 ≤ M) (hRmax : 0 < Rmax)
    (hratio : M / Real.sqrt (n * A) ≤ Rmax) :
    M ^ 2 / (n * Rmax ^ 2) ≤ A := by
  have hnA : (0 : ℝ) < n * A := mul_pos hn hA
  have hsqrtpos : 0 < Real.sqrt (n * A) := Real.sqrt_pos.mpr hnA
  have hM_le : M ≤ Rmax * Real.sqrt (n * A) := by
    rw [div_le_iff₀ hsqrtpos] at hratio; linarith [hratio]
  have hsq : M ^ 2 ≤ Rmax ^ 2 * (n * A) := by
    have hR_nonneg : 0 ≤ Rmax * Real.sqrt (n * A) := mul_nonneg hRmax.le hsqrtpos.le
    have hmul := mul_le_mul hM_le hM_le hM hR_nonneg
    have hsqA : Real.sqrt (n * A) * Real.sqrt (n * A) = n * A :=
      Real.mul_self_sqrt hnA.le
    calc M ^ 2 = M * M := by ring
      _ ≤ (Rmax * Real.sqrt (n * A)) * (Rmax * Real.sqrt (n * A)) := hmul
      _ = Rmax ^ 2 * (n * A) := by
            rw [show (Rmax * Real.sqrt (n * A)) * (Rmax * Real.sqrt (n * A))
                  = Rmax ^ 2 * (Real.sqrt (n * A) * Real.sqrt (n * A)) by ring, hsqA]
  have hden : (0 : ℝ) < n * Rmax ^ 2 := mul_pos hn (pow_pos hRmax 2)
  rw [div_le_iff₀ hden]
  nlinarith [hsq]

/-- **The dichotomy's own implication is a wall statement.** If the arc-excess sufficient
condition `A <= c*L/n` holds AND the envelope ratio is bounded `R = M/sqrt(nA) <= Rmax`, then the
sup bound `M <= Rmax*sqrt c*sqrt(n*L)` follows — the SAME `sqrt(n*L)` scale the prize needs, with
the `O(1)` constant `Rmax*sqrt c`. So an arc-excess bound is not weaker than the sup bound: it
delivers it. (The mild `1 <= n` is automatic in the prize regime `n = 2^a >= 2`.) -/
theorem sup_bound_of_arcExcess_bound
    (M n A L c Rmax : ℝ) (hn : 1 ≤ n) (hA : 0 < A) (hL : 0 < L) (_hM : 0 ≤ M)
    (hc : 0 ≤ c) (hRmax : 0 < Rmax)
    (harc : A ≤ c * L / n)
    (hratio : M / Real.sqrt (n * A) ≤ Rmax) :
    M ≤ Rmax * Real.sqrt c * Real.sqrt (n * L) := by
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le one_pos hn
  have hnA : (0 : ℝ) < n * A := mul_pos hn0 hA
  have hsqrtpos : 0 < Real.sqrt (n * A) := Real.sqrt_pos.mpr hnA
  have hM_le : M ≤ Rmax * Real.sqrt (n * A) := by
    rw [div_le_iff₀ hsqrtpos] at hratio; linarith [hratio]
  have hL0 : (0 : ℝ) ≤ L := hL.le
  have hnA_le : n * A ≤ c * (n * L) := by
    rw [le_div_iff₀ hn0] at harc
    have hcL : c * L ≤ c * (n * L) := by nlinarith [mul_nonneg hc hL0]
    nlinarith [harc, hcL]
  have hsqrt_mono : Real.sqrt (n * A) ≤ Real.sqrt (c * (n * L)) := Real.sqrt_le_sqrt hnA_le
  have hsplit : Real.sqrt (c * (n * L)) = Real.sqrt c * Real.sqrt (n * L) :=
    Real.sqrt_mul hc (n * L)
  calc M ≤ Rmax * Real.sqrt (n * A) := hM_le
    _ ≤ Rmax * Real.sqrt (c * (n * L)) := mul_le_mul_of_nonneg_left hsqrt_mono hRmax.le
    _ = Rmax * Real.sqrt c * Real.sqrt (n * L) := by rw [hsplit]; ring

/-- **No shortcut: an arc-excess bound reduces to the sup bound (the theorem-level REDUCES-TO-WALL
statement).** From an arc-excess bound `A <= c*L/n` with bounded envelope ratio `R <= Rmax`:
(i) the sup bound `M <= (Rmax*sqrt c)*sqrt(n*L)` holds at the SAME `sqrt(n*L)` scale, and
(ii) the exact identity `A/L = C^2/R^2` shows the worst-coset arc-excess is determined by `M` and
the `O(1)` ratio `R`. Hence bounding the worst-coset quarter-arc energy `A` is EQUIVALENT (up to the
bounded envelope ratio) to bounding the sup `M` — the anti-resonance dichotomy supplies no
independent lever. -/
theorem arcExcess_bound_reduces_to_sup_bound
    (M n A L c Rmax : ℝ) (hn : 1 ≤ n) (hA : 0 < A) (hL : 0 < L) (hM : 0 < M)
    (hc : 0 ≤ c) (hRmax : 0 < Rmax)
    (harc : A ≤ c * L / n)
    (hratio : M / Real.sqrt (n * A) ≤ Rmax) :
    M ≤ Rmax * Real.sqrt c * Real.sqrt (n * L)
      ∧ A / L = (M / Real.sqrt (n * L)) ^ 2 / (M / Real.sqrt (n * A)) ^ 2 := by
  refine ⟨sup_bound_of_arcExcess_bound M n A L c Rmax hn hA hL hM.le hc hRmax harc hratio, ?_⟩
  exact antiResonanceEnvelope_ratio_sq M n A L (lt_of_lt_of_le one_pos hn) hA hL hM

end ArkLib.ProximityGap.Frontier.AntiResonanceDichotomy
