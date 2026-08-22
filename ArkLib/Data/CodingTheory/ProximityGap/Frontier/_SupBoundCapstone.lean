/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The corrected central conditional: prize ⟸ a SUP/existence wraparound bound (#444)

The thesis's first capstone (`_ThesisCapstone.subPoisson_variance_implies_prizeFloor`) reduced the
prize to a **variance** hypothesis (sub-Poisson wraparound over the prime family).  This session
refuted that hypothesis empirically (`_OverdispersionObstructsVariance`: the wraparound is heavily
over-dispersed, `Var/mean = 14 … 407000`) — *but* showed the over-dispersion is **benign**
(`overdispersion_is_benign`): the prize needs only a **sup / existence** bound on the wraparound at
the *chosen* prime, a different statistic that over-dispersion never violates.  The thin-and-above-onset
probe confirms it: every computable prime is good with `> 99.4 %` margin, including the Fermat prime.

This brick records the *corrected* central conditional, axiom-clean and self-contained: the prize floor
follows from a **single good prime** — `W_r(p*) ≤ slack` at one admissible prime (existence), or
uniformly over the family (sup) — with **no variance hypothesis at all**.  This is the honest version of
the thesis's central positive claim (§7.6(iii)): the reduction is to the supremum of the wraparound,
not its variance.

The chain is the one already carried by `_ProveAssemblyConcrete`: a good prime gives the char-`p`
energy `≤ Wick`, which the monotone saddle turns into `M ≤ prize floor`.  Here we abstract the saddle
as a hypothesis `hsaddle` and the energy split `E = E0 + W` so the logical core — *existence of one good
prime suffices* — is exposed cleanly and is manifestly independent of any second-moment behaviour.

`#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/

namespace ProximityGap.SupBoundCapstone

variable {ι : Type*}

/-- Per-prime char-`p` energy of `μ_n` = char-0 energy `E0` plus the wraparound surplus `W i` at the
`i`-th prime. (`E0` is prime-independent; the whole prize lives in `W`.) -/
def energy (E0 : ℝ) (W : ι → ℝ) (i : ι) : ℝ := E0 + W i

/-- **The corrected capstone (pointwise form).**  At any prime `i` whose wraparound clears the slack
(`W i ≤ slack`), the saddle value `M (energy …)` is `≤` the prize floor — **provided only** the
budget `E0 + slack ≤ Wick` and the monotone saddle `hsaddle`.  No variance, no averaging: a single
good prime suffices.  This is exactly the reduction `_ProveAssemblyConcrete` performs, with the
energy-vs-Wick gap exposed as the `slack`. -/
theorem prizeFloor_of_good_prime
    (E0 Wick slack floor : ℝ) (W : ι → ℝ) (M : ℝ → ℝ)
    (hsaddle : ∀ e : ℝ, e ≤ Wick → M e ≤ floor)
    (hbudget : E0 + slack ≤ Wick)
    {i : ι} (hgood : W i ≤ slack) :
    M (energy E0 W i) ≤ floor := by
  apply hsaddle
  unfold energy
  linarith

/-- **The corrected capstone (existence form).**  Because the prize is free to *choose* `p`, one good
prime anywhere in the admissible family discharges the prize floor.  This is the precise sense in
which the over-dispersion is benign: the family may be arbitrarily over-dispersed, yet a *single*
prime under the slack closes the prize. -/
theorem prizeFloor_of_exists_good_prime
    (s : Finset ι) (E0 Wick slack floor : ℝ) (W : ι → ℝ) (M : ℝ → ℝ)
    (hsaddle : ∀ e : ℝ, e ≤ Wick → M e ≤ floor)
    (hbudget : E0 + slack ≤ Wick)
    (hexists : ∃ i ∈ s, W i ≤ slack) :
    ∃ i ∈ s, M (energy E0 W i) ≤ floor := by
  obtain ⟨i, hi, hgood⟩ := hexists
  exact ⟨i, hi, prizeFloor_of_good_prime E0 Wick slack floor W M hsaddle hbudget hgood⟩

/-- **The uniform-sup form** (what the thin-above-onset data supports: *every* admissible prime good).
A uniform sup bound over a nonempty family trivially yields the existence form, hence the floor.  The
hypothesis here — `∀ i ∈ s, W i ≤ slack` — is the corrected open core: the worst-case wraparound at
deep `r ≈ log p` in the thin regime, for which the worst *computable* prime clears the bar by `> 99 %`. -/
theorem prizeFloor_of_uniform_sup
    (s : Finset ι) (E0 Wick slack floor : ℝ) (W : ι → ℝ) (M : ℝ → ℝ)
    (hsaddle : ∀ e : ℝ, e ≤ Wick → M e ≤ floor)
    (hbudget : E0 + slack ≤ Wick)
    (hne : s.Nonempty)
    (huniform : ∀ i ∈ s, W i ≤ slack) :
    ∃ i ∈ s, M (energy E0 W i) ≤ floor := by
  obtain ⟨i, hi⟩ := hne
  exact ⟨i, hi, prizeFloor_of_good_prime E0 Wick slack floor W M hsaddle hbudget (huniform i hi)⟩

/-- **Independence from the variance (the benign fact, restated at the capstone level).**  The
hypotheses of `prizeFloor_of_exists_good_prime` mention only the *pointwise* values `W i` and the
budget — never a second moment.  Concretely: the conclusion holds for the maximally over-dispersed
family `W = ![slack, 0]` (which has `Var > mean` once `slack > 2`, by
`_OverdispersionObstructsVariance.overdispersion_is_benign`) exactly as it holds for any other family,
because index `0` is good (`W 0 = slack ≤ slack`).  Over-dispersion is irrelevant to the prize. -/
theorem prizeFloor_robust_to_overdispersion
    (E0 Wick slack floor : ℝ) (M : ℝ → ℝ)
    (hsaddle : ∀ e : ℝ, e ≤ Wick → M e ≤ floor)
    (hbudget : E0 + slack ≤ Wick) :
    ∃ i ∈ (Finset.univ : Finset (Fin 2)), M (energy E0 ![slack, 0] i) ≤ floor := by
  refine prizeFloor_of_exists_good_prime Finset.univ E0 Wick slack floor ![slack, 0] M
    hsaddle hbudget ⟨0, Finset.mem_univ 0, ?_⟩
  simp

end ProximityGap.SupBoundCapstone
