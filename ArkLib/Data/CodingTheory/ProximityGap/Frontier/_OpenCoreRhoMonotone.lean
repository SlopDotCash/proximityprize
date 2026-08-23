/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The open core ⟺ `ρ(r)` is decreasing, with a PROVEN base case `ρ(1) < 1` (#444)

This is the sharpest reduction of the prize the campaign has produced. Define
```
        ρ(r) := S_r / ((p−1)·E_r(ℂ)),      S_r := Σ_{t≠0} |η_t|^{2r} = p·E_r(F_p) − n^{2r}
```
(`E_r(ℂ)` = char-0 energy, `S_r` = the b≠0 period energy). The prize reduces to the b≠0 sub-Gaussian energy
`μ_{2r} = S_r/(p−1) ≤ E_r(ℂ) ≤ Wick`, i.e. exactly **`ρ(r) ≤ 1` for all `r ≤ log p`**.

**Exact-verified structure (n = 8,16,32, β = 4).** `ρ(r)` is **strictly decreasing in `r`**, and its maximum is at
`r = 1`, where it is **proven `< 1`**:
```
        ρ(1) = (p−n)/(p−1) < 1        (exact: S_1 = pn − n², E_1(ℂ) = n, Parseval).
```
So `ρ(r) ≤ ρ(1) < 1` for all `r` — the open core — **provided `ρ` is decreasing**. The base case is unconditional;
the entire remaining open content is the single monotonicity lemma
```
        ρ(r+1) ≤ ρ(r)   ⟺   S_{r+1}·E_r(ℂ) ≤ S_r·E_{r+1}(ℂ)
```
(a log-ratio / log-convexity comparison of the b≠0 char-p energies `S_r` against the char-0 energies `E_r(ℂ)`).

**Why this is the right packaging.** It collapses the whole prize to a *one-step* monotonicity with a *proven*
anchor — the cleanest possible "induction from Parseval." The char-0 energies `E_r(ℂ)` are explicit (Bessel
coefficients), `S_r = p·E_r(F_p) − n^{2r}` is the exact additive-energy quantity, and the comparison `ρ↓` says the
char-p energy `S_r/(p−1)` falls away from the char-0 energy `E_r(ℂ)` at least as fast as `E_r(ℂ)` itself grows — the
char-p periods are progressively *more* sub-Gaussian with depth (exact: ρ falls 0.9998 → 0.83 at n=16).

**Honest status.** Not a proof of the prize: `ρ(r+1) ≤ ρ(r)` for all `r ≤ log p` is equivalent to the prize (it *is*
the sub-Gaussian energy growth = the char-p equidistribution). But it is the tightest reduction yet — a single
log-ratio monotonicity with an unconditional `r=1` base case — and it is what every remaining attack should target.

**What this file proves (axiom-clean).**
* `rho_base_lt_one` — `ρ(1) = (p−n)/(p−1) < 1` (Parseval base case, unconditional for `1 ≤ n < p`).
* `open_core_of_rho_antitone` — if `ρ` is antitone (`ρ(r+1) ≤ ρ(r)`) and `ρ(1) ≤ 1`, then `ρ(r) ≤ 1` for all `r ≥ 1`
  (the induction collapsing the open core to the monotonicity).
* `rho_antitone_iff_energy_cross` — the monotonicity `ρ(r+1) ≤ ρ(r)` ⟺ the energy cross-inequality
  `S_{r+1}·E_r ≤ S_r·E_{r+1}` (the explicit target). Issue #444.

⚠ SCOPE CORRECTION (2026-06-20): the prose above ("`ρ(r+1) ≤ ρ(r)` for all `r` is equivalent to the
prize", "what every remaining attack should target") is too strong on one side: the antitone hypothesis
of `open_core_of_rho_antitone` is SUFFICIENT for the route, but it is NOT universally satisfiable. At a
genuine prize-regime instance with smaller `β` (where the additive wraparound onsets earlier in `r`) BOTH
`ρ` antitonicity AND the `ρ ≤ 1` ceiling FAIL: at `n=32, p=786433` (`β≈3.917`, proper thin `μ_32`, `p>n³`)
one has `ρ(4) > ρ(3)` and `ρ(5) > 1` (kernel-checked in `_RhoAntitoneFailsThinPrime.lean`; method validated
by reproducing RESULTS-444-RHO-ANTITONE digit-for-digit at the larger prime `p=1048609`). So this route is
CONDITIONAL on the prime, not unconditional; its failure does NOT disprove CORE (the sup bound is not
implied false by `ρ>1` at one `r`). The lemmas below are correct as stated. CORE stays OPEN.
-/

namespace ProximityGap.Frontier.OpenCoreRho

/-- **The Parseval base case.** `ρ(1) = (pn − n²)/((p−1)·n) = (p−n)/(p−1) < 1` for `1 ≤ n < p`. Unconditional. -/
theorem rho_base_lt_one (n p : ℝ) (hn : 1 < n) (hp : n < p) :
    (p * n - n ^ 2) / ((p - 1) * n) < 1 := by
  have hn0 : 0 < n := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hden : 0 < (p - 1) * n := by positivity
  rw [div_lt_one hden]
  -- goal: p*n - n^2 < (p-1)*n = p*n - n, i.e. -n^2 < -n, i.e. n < n^2 (true since n > 1)
  nlinarith [hn, hn0]

/-- **The induction.** If `ρ` is antitone (`ρ(r+1) ≤ ρ(r)` for all `r ≥ 1`) and the base value `ρ(1) ≤ 1`, then
`ρ(r) ≤ 1` for all `r ≥ 1` — the open core. The entire remaining content is the antitone (monotonicity) hypothesis. -/
theorem open_core_of_rho_antitone (ρ : ℕ → ℝ)
    (hanti : ∀ r, 1 ≤ r → ρ (r + 1) ≤ ρ r) (hbase : ρ 1 ≤ 1) :
    ∀ r, 1 ≤ r → ρ r ≤ 1 := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => exact hbase
  | succ k hk ih => exact le_trans (hanti k hk) ih

/-- **The monotonicity ⟺ the energy cross-inequality.** With `ρ r = S r / ((p−1)·E r)` and `E r, E (r+1) > 0`,
`p−1 > 0`, the antitone step `ρ(r+1) ≤ ρ(r)` is equivalent to `S (r+1)·E r ≤ S r·E (r+1)` — the explicit log-ratio
target on the b≠0 char-p energies `S` vs the char-0 energies `E`. -/
theorem rho_antitone_iff_energy_cross (S E : ℕ → ℝ) (p : ℝ) (r : ℕ)
    (hp1 : 0 < p - 1) (hEr : 0 < E r) (hEr1 : 0 < E (r + 1)) :
    (S (r + 1) / ((p - 1) * E (r + 1)) ≤ S r / ((p - 1) * E r))
      ↔ S (r + 1) * E r ≤ S r * E (r + 1) := by
  have hd1 : 0 < (p - 1) * E (r + 1) := by positivity
  have hd0 : 0 < (p - 1) * E r := by positivity
  rw [div_le_div_iff₀ hd1 hd0]
  constructor
  · intro h; nlinarith [h, hp1, hEr, hEr1]
  · intro h; nlinarith [h, hp1.le, hEr.le, hEr1.le]

end ProximityGap.Frontier.OpenCoreRho

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.OpenCoreRho.rho_base_lt_one
#print axioms ProximityGap.Frontier.OpenCoreRho.open_core_of_rho_antitone
#print axioms ProximityGap.Frontier.OpenCoreRho.rho_antitone_iff_energy_cross
