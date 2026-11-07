/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ActionOrbitGeneralF

/-!
# Conjecture 7.1 (Chai-Fan 2026/861) sparse-worst-case localization: multi-term directions escape
  the action-orbit eigenvector pin (#444)

## Ground-truth pivot context
The June-2026 literature pivot (commit `231b0ec9c`,
`docs/kb/prize-groundtruth-pivot-2026-action-orbit-2026-06-16.md`) relocated the prize from the
(disproven) capacity sqrt-cancellation to the
ABOVE-JOHNSON `O(1)/|F|` regime, which Chai-Fan 2026/861 reduces to a single closed combinatorial
conjecture that does **not** reduce to BGK:

> **Conjecture 7.1 (sparse-worst-case dominance).** FRI commit-phase soundness on plain RS is
> dominated by its **3-position sparse** witnesses (the worst-case adversary direction lies in an
> action-non-stabilised admissibility class supported on `<= 3` monomial positions).

## The sharp question this file answers
The in-tree action-orbit producer derives per-line `gamma`-orbit closure of the bad set (the source
of the `O(1)/|F|` action-orbit count) from the **sufficient** condition that the direction `f` is a
dilation eigenvector `f.comp (C mu * X) = C c * f`. `ActionOrbitGeneralF.eigen_forces_monomial`
shows that (when `mu` has large multiplicative order, the prize regime `deg f < n` on `mu_n`) only
monomials satisfy that eigenvector identity. So the eigenvector *producer* of orbit closure is a
**1-sparse** mechanism, not a 3-sparse one.

**Correction (audit 2026-10-28, PG-105).** An earlier version of this header said that
orbit-closure *requires* `f` to be a dilation eigenvector, and concluded that a multi-term
direction's bad set "is not a union of `gamma`-orbits" and that "no" orbit compression can apply.
That is a converse error: the coefficient lemmas below only refute the eigenvector identity; they
do not show the identity is *necessary* for bad-set invariance. Concrete counterexample: over
`mu_4 ⊆ F_5` with the constant code, exact agreement `delta = 0`, offset `u_0 = 0` and direction
`f = X + X^2` (evaluations `2, 1, 2, 0` on `1, 2, 3, 4`), the scalar bad set is `{0}` (`gamma = 0`
is explainable while the rows are not jointly codewords; every nonzero multiple of `f` stays
nonconstant). `{0}` is invariant under every multiplicative scalar action, yet `f` is not a
dilation eigenvector for the primitive 4th root `mu = 2` (its two support eigenvalues `2 ≠ 4`
differ). The conclusions below are therefore restricted to the **inapplicability of the eigenvector
producer**, not impossibility of orbit closure or orbit counting.

A probe (`scripts/probes/probe_c71_sparse_orbit_gap.py`, EXACT full-`alpha`-sweep bad-set strength
on the thin domain `mu_n`, `n = 2^a`, `k = n/4`, three primes `p in {17, 41, 521}` spanning
`p <= n^3` and `p > n^3`, NEVER `n = q-1`) decides the dichotomy:
  * `s1max` (max bad-set adversary strength over 1-sparse / monomial directions) `= 8`,
  * `s23max` (max over genuine 2- and 3-term directions) `= 9`,
uniformly across all three primes -- so the worst-case `<=3`-sparse adversary is **strictly
multi-term** (`s23max > s1max`), NOT a monomial. (Route **B** of the probe.)

**Consequence (gap-localization, producer-level only).** Even granting Conjecture 7.1 ("worst case
is `<=3`-sparse"), the probe's worst case is a *genuine* 2- or 3-term direction, which by the
eigenvector pin is **not** a dilation eigenvector. Hence the eigenvector-based action-orbit producer
does **not** supply orbit closure (and so does not supply its `O(1)/|F|` compression) for that
direction. Whether the bad set of such a direction is nevertheless orbit-closed, or admits some
other orbit-counting argument, is **not decided here** (see the PG-105 counterexample above).
Closing the prize through the in-tree machinery therefore needs either a different orbit-closure
producer or a non-orbit incidence argument on the 2- or 3-term strata.

## What is formalized here (axiom-clean, no new analytic content)
The structural half of that statement -- the contrapositive of the pin, packaged as a usable
constraint lemma:

* `not_eigen_of_two_distinct_support` : if `f` has two distinct support exponents `i != j` whose
  dilation values differ (`mu^i != mu^j`, automatic when `mu` has order `> deg f`), then `f` is
  **not** a dilation eigenvector -- there is no scalar `c` with `f.comp (C mu * X) = C c * f`.
* `multiterm_not_orbit_eligible` : a direction `f` with `>= 2` support terms (under the same
  dilation-distinctness as the pin) is not a dilation eigenvector; i.e. the eigenvector hypothesis
  used by the action-orbit producer fails on every genuinely multi-term direction. This is the
  formal statement that the probe's Route-B worst case (a 2- or 3-term direction) escapes
  the eigenvector producer. (It does not prove the bad set fails to be orbit-closed.)

These extend the PROVEN `ActionOrbitGeneralF` pin
(`dilation_eigen_coeff` / `eigen_forces_monomial`); they add no character-sum / incidence content.
The residual incidence bound on the 2- or 3-term strata (the actual Conjecture-7.1 content) is
**open** and NOT claimed here.

Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.C71SparseOrbitGap

open ArkLib.ProximityGap.ActionOrbitGeneralF

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Two dilation-distinct support terms obstruct the eigenvector identity.**
If `f` has two support exponents `i, j` with `mu^i != mu^j`, then `f` is **not** a dilation
eigenvector: there is no scalar `c` with `f.comp (C mu * X) = C c * f`. (Contrapositive of
`dilation_eigen_coeff`, which forces `mu^j = c` for every support exponent `j`; two distinct
dilation values can't both equal the single `c`.) -/
theorem not_eigen_of_two_distinct_support (μ : F) (f : F[X])
    {i j : ℕ} (hi : f.coeff i ≠ 0) (hj : f.coeff j ≠ 0) (hne : μ ^ i ≠ μ ^ j) :
    ¬ ∃ c : F, f.comp (C μ * X) = C c * f := by
  rintro ⟨c, hc⟩
  have hci : μ ^ i = c := dilation_eigen_coeff μ c f hc i hi
  have hcj : μ ^ j = c := dilation_eigen_coeff μ c f hc j hj
  exact hne (hci.trans hcj.symm)

/-- **Genuinely multi-term directions are not orbit-eligible (the probe's Route-B obstruction,
formal).** Under the same dilation-distinctness hypothesis used by `eigen_forces_monomial`
(guaranteed when `orderOf μ > f.natDegree`, the prize regime `deg f < n` on `μ_n`), a direction `f`
with `2 ≤ f.support.card` is **not** a dilation eigenvector. Hence the eigenvector-based producer
of per-line orbit closure (which takes the eigenvector identity as its sufficient hypothesis) does
not apply to any genuine 2- or 3-term direction, which is exactly the worst-case sparse adversary
found by the probe (`s23max = 9 > s1max = 8`, uniform over `p ∈ {17,41,521}`). This does **not**
show that the bad set of such a direction fails to be orbit-closed: eigenvector failure is not
necessary-condition failure (PG-105; e.g. `f = X + X^2` on `mu_4 ⊆ F_5`, constant code, `delta = 0`,
has the orbit-invariant bad set `{0}`). So even if Conjecture 7.1 holds, the multi-term strata need
a different orbit-closure producer or a non-orbit incidence bound. -/
theorem multiterm_not_orbit_eligible (μ : F) (f : F[X])
    (hdistinct : ∀ a ∈ f.support, ∀ b ∈ f.support, μ ^ a = μ ^ b → a = b)
    (hcard : 2 ≤ f.support.card) :
    ¬ ∃ c : F, f.comp (C μ * X) = C c * f := by
  -- two distinct support exponents exist (card ≥ 2); they are dilation-distinct by `hdistinct`.
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard
  have hiM : f.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  have hjM : f.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hne : μ ^ i ≠ μ ^ j := fun h => hij (hdistinct i hi j hj h)
  exact not_eigen_of_two_distinct_support μ f hiM hjM hne

end ArkLib.ProximityGap.C71SparseOrbitGap

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.C71SparseOrbitGap.not_eigen_of_two_distinct_support
#print axioms ArkLib.ProximityGap.C71SparseOrbitGap.multiterm_not_orbit_eligible
