/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DyadicJacobiCocycleNonContraction
import Mathlib.Tactic

/-!
# Fermat-corner EXCLUSION: the prize regime is disjoint from the closed-form Gauss-sum corner

**Door (iv), Lane 3 — frontier-movement, extends `_DyadicJacobiCocycleNonContraction`.**

`odd_factor_of_not_two_pow` recorded the arithmetic guardrail that the classical 2-power Gauss-sum
evaluation requires the dual character orders to be powers of two, i.e. the index `m = (p−1)/n` to be a
power of two (`p` a Fermat prime when `n` is a 2-power). What was MISSING is the *forward* prize-regime
exclusion: that the genuine thin prize regime — where `n = 2^a` is a 2-power but the index `m` carries
an odd prime factor `r` (the generic dyadic prime, `q ≈ n^4..n^5`) — is STRUCTURALLY DISJOINT from that
Fermat corner. This file locks that dichotomy as kernel statements:

* `oddFactor_dvd_pSub` — an odd prime factor `r ∣ m` divides `p − 1 = n·m`, so a multiplicative
  character of order `r` (odd, `> 1`) genuinely exists.
* `not_two_pow_of_odd_factor` — once an odd `r > 1` divides `p − 1`, then `p − 1` is NOT a power of two
  (a 2-power has no odd prime factor `> 1`).
* `prizeRegime_not_fermat_corner` — combining: in the prize regime (`p − 1 = n·m`, `n = 2^a`, `m` with an
  odd factor `> 1`), `p − 1` is not a 2-power — `p` is NOT a Fermat prime, so the closed-form 2-power
  Gauss-sum evaluation does NOT apply. The explicit-evaluation route is unavailable exactly here.

## HONEST SCOPE
This is a structural EXCLUSION (an arithmetic class-restriction guardrail): it shows the closed-form
corner is unreachable in the prize regime, consistent with the §6/c.146 monomial-extremality and
good-prime refutations. It does NOT bound any character sum and proves NOTHING toward CORE. NO CORE /
cancellation / completion / anti-concentration / moment-saving / capacity claim. Prize CORE stays OPEN.
The point: the Door-IV cocycle cannot be evaluated in closed form via the Fermat-prime route — the
genuinely-new dispersion estimate (the open `JacobiCocycleDispersion`) is the only door, as Shaw's
tetrachotomy demands.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace ArkLib.ProximityGap.Frontier.JacobiCocycleFermatCornerExclusion

open ProximityGap.Frontier.DyadicJacobiCocycleNonContraction

/-- **An odd factor of the index divides `p − 1`.** If `pSub = n · m` (the prize factorization
`p − 1 = n·m`) and `r ∣ m`, then `r ∣ pSub`. So an odd prime factor of the index `m` is a genuine
divisor of `p − 1`, giving a multiplicative character of that order. -/
theorem oddFactor_dvd_pSub {pSub n m r : ℕ} (hfac : pSub = n * m) (hr : r ∣ m) :
    r ∣ pSub := by
  rw [hfac]
  exact Dvd.dvd.mul_left hr n

/-- **An odd factor `> 1` forbids a 2-power.** If `N` is a power of two and `r ∣ N` with `r` odd and
`r > 1`, contradiction: a 2-power has no odd prime factor exceeding one. Hence the contrapositive — an
odd `r > 1` dividing `N` certifies `N` is NOT a 2-power. -/
theorem not_two_pow_of_odd_factor {N r : ℕ} (hr_odd : Odd r) (hr1 : 1 < r) (hdvd : r ∣ N) :
    ∀ k, N ≠ 2 ^ k := by
  intro k hN
  subst hN
  obtain ⟨j, hj, hrj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases Nat.eq_zero_or_pos j with hj0 | hjp
  · rw [hj0, pow_zero] at hrj; omega
  · have hdvd2 : (2 : ℕ) ∣ r := hrj ▸ dvd_pow_self 2 hjp.ne'
    rw [Nat.odd_iff] at hr_odd
    omega

/-- **Prize regime ⟹ NOT the Fermat corner (the door-(iv) exclusion).** In the prize regime
`p − 1 = n·m` with `n = 2^a` a 2-power and the index `m` carrying an odd prime factor `r` (`1 < r`,
`r` odd, `r ∣ m`), the order `p − 1` is NOT a power of two. Consequently `p` is not a Fermat prime and
the classical closed-form 2-power Gauss-sum evaluation does not apply: the explicit route is structurally
unavailable exactly in the prize regime. -/
theorem prizeRegime_not_fermat_corner
    {pSub n m r a : ℕ} (hfac : pSub = n * m) (hn : n = 2 ^ a)
    (hr_odd : Odd r) (hr1 : 1 < r) (hr_dvd : r ∣ m) :
    ∀ k, pSub ≠ 2 ^ k :=
  not_two_pow_of_odd_factor hr_odd hr1 (oddFactor_dvd_pSub hfac hr_dvd)

/-- **Bridge to the in-tree guardrail.** Combining with `odd_factor_of_not_two_pow`: the prize-regime
index `m` (not a 2-power) yields an explicit odd factor `> 1`, which by `prizeRegime_not_fermat_corner`
forces `p − 1` off the 2-power corner. This packages the round trip "`m` not 2-power ⟹ Fermat corner
excluded" entirely on `(pSub, n, m, a)` data. -/
theorem index_not_two_pow_excludes_fermat_corner
    {pSub n m a : ℕ} (hfac : pSub = n * m) (hn : n = 2 ^ a)
    (hm : 2 ≤ m) (hm_npow : ∀ j, m ≠ 2 ^ j) :
    ∀ k, pSub ≠ 2 ^ k := by
  obtain ⟨r, hr1, hr_odd, hr_dvd⟩ := odd_factor_of_not_two_pow hm hm_npow
  exact prizeRegime_not_fermat_corner hfac hn hr_odd hr1 hr_dvd

end ArkLib.ProximityGap.Frontier.JacobiCocycleFermatCornerExclusion

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleFermatCornerExclusion.oddFactor_dvd_pSub
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleFermatCornerExclusion.not_two_pow_of_odd_factor
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleFermatCornerExclusion.prizeRegime_not_fermat_corner
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleFermatCornerExclusion.index_not_two_pow_excludes_fermat_corner
