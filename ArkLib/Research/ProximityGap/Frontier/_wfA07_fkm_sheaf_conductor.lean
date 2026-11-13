/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# A07 (FKM sheaf / parameter-space cancellation): a Cauchy–Schwarz weight inequality (#444)

**Scope (audit-corrected).** This file was intended as a guardrail explaining why the FKM
(Fouvry–Kowalski–Michel) "relocate the cancellation to the parameter family" route, applied to the
**Krawtchouk-weighted** far-line incidence, does not escape the conductor wall of the unweighted
`b`-line route (`C2WeilDeligneParamFamilyNoGo`).  Its formal content is only the Cauchy–Schwarz
inequality (★) below; the sheaf-theoretic reading is NOT established (see the correction section).

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

## What is actually proven: plain Cauchy–Schwarz (audit correction, 2026-10-28)

An earlier version of this note identified `condFloor(w) := ∑_j w_j²` with the generic rank of a
sheaf realizing `T_w`, and hence with a lower bound for its conductor.  **That identification is
wrong** and has been withdrawn:

* rank and conductor are invariant under scaling `w ↦ ε·w`, while `∑_j w_j²` scales by `ε²`
  (for `w ≡ ε`, `condFloor = n·ε²` is arbitrarily small, yet the natural realizing sheaf
  `⊕_j L_ψ(x_j ·)` still has rank `n`);
* the FKM certificate shape `condFloor·√p` scales like `ε²` while `T_w` scales like `ε`, so any
  "trade-off" comparing them is a dimensional artefact;
* `⊕_j L_ψ(x_j ·)` is not geometrically irreducible, so the FKM theorem does not apply to it as stated.

The L²-mean of `T_w` over the parameter family is a genuine Parseval fact
(`(1/(p−1)) ∑_{b≠0} |T_w(b)|² = (p·‖w‖₂² − (∑_j w_j)²)/(p−1)`, not formalized here), but it is a
second moment, not a rank or conductor.

The only Lean content is the Cauchy–Schwarz inequality on the `n` positions,

  `signal(w)² := (∑_j |w_j|)² ≤ n · ∑_j w_j² = n · condFloor(w)`,            (★)

together with trivial corollaries and its equality case `w ≡ 1`.  No FKM/conductor no-go is proven;
whether a weighted FKM relocation can help is NOT settled by this file.

## What this is NOT

It is not a refutation of the prize bound, and (after the correction above) it is NOT a proven no-go
for the FKM-relocation method either. Heuristically the genuine cancellation is the
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

/-- The squared weight L²-norm `∑_j w_j²` (named `condFloor` for historical reasons).  It is the
asymptotic L²-mean of `T_w(b) = ∑_j w_j · ψ(b x_j)` over the parameter family, but it is NOT a
rank or conductor bound: rank/conductor are scale-invariant in `w`, while `∑_j w_j²` is not. -/
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

/-- **Cauchy–Schwarz (★).** For any weight `w` on the `n` subgroup positions,
`signal(w)² ≤ n · ∑_j w_j²`.  This is Cauchy–Schwarz on the `n` positions applied to `|w_j|`; it
carries no sheaf/conductor content. -/
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

/-- **Cauchy–Schwarz, square-root form.** If `∑_j w_j² ≤ c` then `∑_j |w_j| ≤ √(n·c)`.  (No
conductor interpretation: `∑_j w_j²` is not a conductor, see the module note.) -/
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

/-- **Cauchy–Schwarz, divided form:** `(∑_j |w_j|)²/n ≤ ∑_j w_j²` for `n > 0`.  (Historically named
for an FKM reading; it is NOT an FKM statement, since `∑_j w_j²` is not a conductor.) -/
theorem fkm_bound_pinned_by_signal (n : ℕ) (w : Fin n → ℝ) (hn : 0 < n) :
    (signal n w) ^ 2 / (n : ℝ) ≤ condFloor n w := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hnpos]
  have := signal_sq_le_card_mul_condFloor n w
  linarith [this]

/-- **Unweighted base case.** With `w ≡ 1`, `∑_j w_j² = n` exactly (numerically matching the
rank-`n` count of `C2WeilDeligneParamFamilyNoGo`; for other weights no such match holds). -/
theorem condFloor_unweighted (n : ℕ) : condFloor n (fun _ => (1 : ℝ)) = (n : ℝ) := by
  unfold condFloor
  simp

/-- **Equality case of (★).** The constant weight `w ≡ 1` attains `signal² = n·∑_j w_j²` (both
sides `= n²`), so the Cauchy–Schwarz constant `n` is sharp.  No statement about conductors or FKM
is made. -/
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
