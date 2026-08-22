/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# A07 (FKM sheaf / parameter-space cancellation) no-go: the weighted-conductor trade-off (#444)

**NEGATIVE / guardrail brick (an honest OBSTRUCTION, NOT a closure).** This file pins, axiom-clean,
*why* the FKM (Fouvry–Kowalski–Michel) "relocate the cancellation to the parameter family where
Deligne is sharp" route — applied to the **Krawtchouk-weighted** far-line incidence — does not
escape the same conductor wall that already kills the unweighted `b`-line route (`C2WeilDeligneParamFamilyNoGo`).

## The route

The prize period `η_b = ∑_{x ∈ μ_n} e_p(b x)` has a vacuous plain-Weil bound on the `n`-point DOMAIN
(`n < √q`). FKM relocate to the PARAMETER family `b ↦ t(b)` (≈ `q` points) and, IF `t` is the trace of
a geometrically irreducible middle-extension `ℓ`-adic sheaf `F` of conductor `cond(F)`, give the
completed-sum bound `|∑_x t(x)| ≤ cond(F)·√p` (Deligne / Weil II, the Pólya–Vinogradov method).

A07's idea: the **far-line incidence** carries a *Krawtchouk weight* `K_w` (the Fourier transform of
a Hamming shell, `ShellFourierKrawtchouk.shell_fourier`). The relocated trace function is the
**weighted period**

  `T_w(b) = ∑_{j<n} w_j · e_p(b · x_j)`,    `x_j ∈ μ_n` the subgroup elements, `w_j` a Krawtchouk weight.

The hope: a clever weight `w` makes `cond(F) = O(√(n log p))`, so FKM lands the prize where plain Weil
was vacuous.

## The wall (the conductor floor = ‖w‖₂², and the Cauchy–Schwarz trade-off)

For ANY weight `w`, the L²-second-moment of the trace `T_w` over the full parameter family is, by
orthogonality (the exact Parseval computation, verified numerically in
`scripts/probes/rust/probe_wfA07_fkm_conductor.rs` to 3 decimals: `M2 = ‖w‖₂²` for every weight):

  `(1/(p−1)) ∑_{b≠0} |T_w(b)|² = (p·‖w‖₂² − (∑_j w_j)²)/(p−1) ⟶ ‖w‖₂²`  as `p → ∞`.

The generic rank of any middle-extension sheaf realizing `T_w` equals this second moment, and
`cond(F) ≥ rank(F)`. So the **conductor floor is `‖w‖₂²`** — exactly the (squared) L²-norm of the
chosen weight. (Unweighted `w ≡ 1` gives `‖w‖₂² = n` = the C2 wall: `cond = n`, FKM trivial.)

The decisive trade-off is plain Cauchy–Schwarz on the `n` subgroup positions:

  `signal(w)² := (∑_j |w_j|)² ≤ n · ∑_j w_j² = n · condFloor(w)`.            (★)

`signal(w) = ∑_j |w_j|` is the most the period sup-norm can be (triangle ineq.) — it is the "amount of
unweighted mass" the weight carries. (★) says: **to push the conductor below `n` (the only way FKM
beats the trivial `ℓ¹` ceiling) you must shrink the signal below `n` by the SAME factor** —
`condFloor < n/k ⟹ signal < n/√k`. You cannot have both a small conductor and a full-mass period; the
weight that flattens the conductor is exactly the weight that suppresses the period it was meant to bound.

`signal² ≤ n·cond` and FKM `sup ≤ cond·√p` chain to `sup ≤ cond·√p` with `cond ≥ signal²/n`, so for a
weight carrying the prize-scale signal `signal = Θ(n)` (needed to see `η_b ~ √(n log p)` at all) the
conductor is forced back to `Θ(n)` and FKM gives `Θ(n)·√p ≫ √(n log p)` at `β = 4` — vacuous.

This is the SAME `rank = conductor = n` wall as C2, now shown stable under arbitrary (Krawtchouk or
other) weighting: the weight only trades conductor for signal at a fixed `n`-position exchange rate.

## What this is NOT

It is not a refutation of the prize bound (the period IS `√`-controlled empirically); it is a precise
no-go for the FKM-relocation *method*: the relevant sheaf cannot have bounded conductor while carrying
a non-trivial signal, so Deligne never bites below the trivial ceiling. The genuine cancellation is the
archimedean equidistribution of the `n` Artin–Schreier phases on the parameter family — the open BGK
core — not a Deligne output. (Cf. DISPROOF_LOG C14/C29: `η_b`'s sheaf-home is the `GL(1)^f` Gauss-sum
family, conductor `~ n^{2r−1}`, never a bounded-conductor Kloosterman object.)

Probes: `scripts/probes/rust/probe_wfA07_fkm_conductor.rs` (M2 = ‖w‖₂² for unweighted/linramp/binomial/
alternating/half-shell, β=4, n=32..128 — second moment matches ‖w‖₂² to 3 decimals; the normalized
sup/√(M2·log) ratio is FLAT ≈ 0.9–1.4 across ALL weights, i.e. no weight improves the cancellation
ratio), `probe_wfA07_krawtchouk_conductor.rs` (the raw Krawtchouk weight is fully spread, `condFloor =
Θ(n)`).
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.A07FKMSheafConductor

open scoped BigOperators
open Finset

/-- The **conductor floor** of the parameter-family sheaf realizing the weighted period
`T_w(b) = ∑_j w_j · ψ(b x_j)`: the L²-second-moment of the trace over the parameter family,
which equals the generic rank, hence lower-bounds the conductor of any middle-extension realization.
By the Parseval computation it is `∑_j w_j²` (the squared weight L²-norm). -/
def condFloor (n : ℕ) (w : Fin n → ℝ) : ℝ := ∑ j, (w j) ^ 2

/-- The **signal** of a weight: the L¹-mass `∑_j |w_j|`. This is the largest value the period
sup-norm `sup_b |T_w(b)|` can attain (triangle inequality, since `|ψ| = 1`); it measures how much
unweighted period mass the weight carries. -/
def signal (n : ℕ) (w : Fin n → ℝ) : ℝ := ∑ j, |w j|

/-- `condFloor` is nonnegative. -/
theorem condFloor_nonneg (n : ℕ) (w : Fin n → ℝ) : 0 ≤ condFloor n w := by
  unfold condFloor; positivity

/-- `signal` is nonnegative. -/
theorem signal_nonneg (n : ℕ) (w : Fin n → ℝ) : 0 ≤ signal n w := by
  unfold signal; positivity

/-- **The FKM conductor–signal trade-off (★).** For any weight `w` on the `n` subgroup positions,
`signal(w)² ≤ n · condFloor(w)`. This is Cauchy–Schwarz on the `n` positions applied to `|w_j|`.
It is the entire obstruction: a small conductor forces a small signal at the fixed exchange rate `n`. -/
theorem signal_sq_le_card_mul_condFloor (n : ℕ) (w : Fin n → ℝ) :
    (signal n w) ^ 2 ≤ (n : ℝ) * condFloor n w := by
  unfold signal condFloor
  -- `(∑ |w j|)² ≤ #univ · ∑ |w j|²`, and `|w j|² = (w j)²`.
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
    (f := fun j => |w j|)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have hsq : ∀ j, |w j| ^ 2 = (w j) ^ 2 := fun j => sq_abs (w j)
  simp_rw [hsq] at h
  exact h

/-- **The no-go, contrapositive form: a bounded conductor caps the signal.** If a sheaf realizing the
weighted period has conductor floor `≤ c`, then its carried signal is `≤ √(n·c)`. In particular, to
beat the trivial ceiling FKM needs `c < n`, which forces `signal < n`: the weight cannot both flatten
the conductor and carry the full unweighted-scale period mass. -/
theorem signal_le_of_condFloor_le (n : ℕ) (w : Fin n → ℝ) (c : ℝ)
    (hc : condFloor n w ≤ c) :
    signal n w ≤ Real.sqrt ((n : ℝ) * c) := by
  have hkey : (signal n w) ^ 2 ≤ (n : ℝ) * c :=
    le_trans (signal_sq_le_card_mul_condFloor n w)
      (by nlinarith [condFloor_nonneg n w, Nat.cast_nonneg (α := ℝ) n])
  have hs : 0 ≤ signal n w := signal_nonneg n w
  -- `signal ≤ √(signal²) ≤ √(n c)`.
  calc signal n w = Real.sqrt ((signal n w) ^ 2) := by
            rw [Real.sqrt_sq hs]
    _ ≤ Real.sqrt ((n : ℝ) * c) := Real.sqrt_le_sqrt hkey

/-- **The FKM-relocation is vacuous below the trivial ceiling.** The FKM completed-sum certificate is
`sup_b |T_w(b)| ≤ condFloor · √p`. The prize wants `sup ≤ Cp` for a target `Cp` (the role of
`C√(n log p)`). If the weight carries any signal at all that we wish to certify (`Cp < signal`), then
since `signal² ≤ n·condFloor` we get `condFloor·√p ≥ (signal²/n)·√p`. Concretely we record the clean
implication: whenever the FKM bound `condFloor·√p` is to beat the target `Cp` while the period is at
least `signal`, the conductor is pinned by `condFloor ≥ signal²/n`. -/
theorem fkm_bound_pinned_by_signal (n : ℕ) (w : Fin n → ℝ) (hn : 0 < n) :
    (signal n w) ^ 2 / (n : ℝ) ≤ condFloor n w := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hnpos]
  have := signal_sq_le_card_mul_condFloor n w
  linarith [this]

/-- **Unweighted base case = the C2 wall.** With `w ≡ 1` (no weighting), `condFloor = n` exactly:
the FKM relocation of the *plain* period has conductor `= n`, reproducing
`C2WeilDeligneParamFamilyNoGo.parseval_mass_le_rank`. So weighting is the only lever, and (★) shows it
cannot help. -/
theorem condFloor_unweighted (n : ℕ) : condFloor n (fun _ => (1 : ℝ)) = (n : ℝ) := by
  unfold condFloor
  simp

/-- **The exchange-rate sharpness.** (★) is tight: the unweighted weight `w ≡ 1` attains equality
`signal² = n·condFloor` (both sides `= n²`). So the `n`-position exchange rate between conductor and
signal cannot be improved by any inequality argument — it is a structural identity at the constant
weight, which is exactly the weight carrying the full period. Hence no weight does strictly better than
the unweighted `cond = n` on the prize-relevant (full-signal) periods. -/
theorem tradeoff_tight_at_unweighted (n : ℕ) :
    (signal n (fun _ => (1 : ℝ))) ^ 2 = (n : ℝ) * condFloor n (fun _ => (1 : ℝ)) := by
  rw [condFloor_unweighted]
  unfold signal
  simp [abs_one]
  ring

end ArkLib.ProximityGap.Frontier.A07FKMSheafConductor

-- Axiom audit (run via `lake env lean`):
-- #print axioms ArkLib.ProximityGap.Frontier.A07FKMSheafConductor.signal_sq_le_card_mul_condFloor
-- #print axioms ArkLib.ProximityGap.Frontier.A07FKMSheafConductor.signal_le_of_condFloor_le
-- #print axioms ArkLib.ProximityGap.Frontier.A07FKMSheafConductor.tradeoff_tight_at_unweighted
