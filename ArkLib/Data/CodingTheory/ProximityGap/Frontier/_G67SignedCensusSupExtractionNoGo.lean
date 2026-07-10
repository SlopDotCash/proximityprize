/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G65WeightedCensusSubfloorNoGo

/-!
# LANE G67: signed depth-reweighting of the census yields no sup-norm lower bound

G65 closed the **nonnegative** census-side lever: no `w ≥ 0` depth reweighting drops the
`q·census` total strictly below the correspondingly-weighted DC floor `Σ w r · n^{2r}`.  The one
remaining census-side degree of freedom the adversarial critic flagged was *signed* depth
reweighting: could a weight family that is negative at some depths, forming the census functional

`P(t) := Σ_{r∈S} w r · t^r`   (a moment→sup transfer polynomial),

produce a genuine sup-norm bound where G65's nonneg pinning does not apply?  The critic's exact
signed-weight probe answered NO with a precise structural reason, verified numerically at the
adversarial thin primes: a signed weight family produces only **contentless inversions**.  A
moment→sup *lower* bound needs the transfer polynomial `P` to dominate the sup, i.e. the extracted
certificate is `P(M²)` where `M² = max_b |η_b|²`; but if a dominating depth carries a *negative*
weight the evaluation `P(M²)` is itself negative, so it can never certify a **nonnegative** sup
target `T ≥ 0` — the inference `P(M²) ≥ T` degenerates to `(negative) ≥ (nonneg)`, which is false.
The signed lever inverts the census pinning without ever bounding the sup norm.

This file formalizes that obstruction as small axiom-clean structural facts, uniform in the target
`T ≥ 0`, the (negative) dominating weight `w`, the strictly-positive evaluation point `M²`, and the
depth `r`.  SCOPE (matched exactly to the declarations): the no-go is proved for a transfer value
that IS negative — the pure dominating-depth negative-weight functional `w · t^r`, `w < 0` — which
is exactly the critic's `w(r₀) = -1` signed witness.  It does NOT by itself rule out a general
mixed-sign finite-window polynomial `P(t) = Σ_{r∈S} w_r t^r` that happens to evaluate nonnegative
at the sup despite having a negative coefficient (e.g. `-t + 2t²` at `t = 1` is positive); such a
mixed functional needs a separate dominance/negativity hypothesis before this obstruction applies.
This complements G65 on the signed side for the dominating-negative regime; the mixed-sign regime
with a nonnegative sup evaluation is not claimed closed here.

## What is proved (all axiom-clean)

Let `T ≥ 0` be any nonnegative sup-norm target and let `Pval` be the value `P(M²)` a census
transfer functional would have to reach to certify `M² ≥ (something producing T)`.

1. `neg_eval_cannot_certify_nonneg_target` : **the sup-extraction obstruction.** If `Pval < 0` and
   `0 ≤ T` then `¬ (T ≤ Pval)`: a negative transfer value certifies no nonnegative sup target.  The
   would-be signed lower bound is vacuous.
2. `single_neg_dominating_weight_eval_neg` : the concrete producer of a negative transfer value —
   the pure dominating-depth monomial `P(t) = w · t^r` with `w < 0` and `0 < t` evaluates to
   `w · t^r < 0`.  This is exactly the critic's `w(r₀) = -1` signed witness.
3. `signed_census_functional_no_sup_certificate` : the **combined no-go.**  A dominating-depth
   negative-weight census functional (value `w · M² ^ r`, `w < 0`, `M² > 0`) cannot certify any
   nonnegative sup target `T`: `¬ (T ≤ w · (M2) ^ r)`.  The signed depth lever is contentless.
4. `signedCensusYieldsSupBound` / `not_signedCensusYieldsSupBound` : an honest scope marker naming
   the refuted route — a dominating-depth negative signed reweighting does not yield a sup-norm
   lower bound.  No axioms, no goal weakening.

Together with G65 (nonneg side) this closes the two extremes of the census-functional lever: G65
pins every *nonnegative*-weighted census total at-or-above the weighted DC floor, and this file
shows a *negative* dominating-depth transfer value (the critic's `w(r₀) = -1` witness) certifies no
nonnegative sup norm.  It is a **precise route no-go**, not a closure: it does not bound
`wraparoundExcessR`, and CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) remains open / on-BGK.  Its content is
that the dominating-depth negative signed lever — the concrete surviving signed hope the critic
named — buys nothing toward the sup norm.  A general mixed-sign functional with a nonnegative sup
evaluation is out of scope and would need its own dominance hypothesis.

Issue #466.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.G67SignedCensusSupExtractionNoGo

/-- **The sup-extraction obstruction.**  A census transfer functional value `Pval := P(M²)` that a
signed reweighting would have to reach to certify a **nonnegative** sup-norm target `T` cannot do so
if `Pval` is negative: from `Pval < 0` and `0 ≤ T` we get `¬ (T ≤ Pval)`.

This is the load-bearing reason the signed census lever is contentless.  A moment→sup *lower* bound
needs `P(M²) ≥ T` for a nonnegative target `T`; when the transfer polynomial evaluates negative at
the sup, the required inequality `T ≤ P(M²)` is impossible.  The signed weights invert the census
pinning (G63/G65) without ever producing a sup bound. -/
theorem neg_eval_cannot_certify_nonneg_target {Pval T : ℝ} (hP : Pval < 0) (hT : 0 ≤ T) :
    ¬ (T ≤ Pval) := by
  intro hle
  exact absurd (le_trans hT hle) (not_le.mpr hP)

/-- The concrete producer of a negative transfer value: the pure dominating-depth monomial
`P(t) = w · t^r` with a negative weight `w < 0` at a strictly positive evaluation point `0 < t`
evaluates to `w · t^r < 0`.  This is exactly the critic's signed witness `w(r₀) = -1`: the highest
(dominating) depth carries a negative weight, so the transfer value at the sup `t = M²` is
negative. -/
theorem single_neg_dominating_weight_eval_neg {w t : ℝ} (hw : w < 0) (ht : 0 < t) (r : ℕ) :
    w * t ^ r < 0 :=
  mul_neg_of_neg_of_pos hw (pow_pos ht r)

/-- **The combined signed-census no-go.**  A dominating-depth negative-weight census transfer
functional — value `w · (M²)^r` with `w < 0` at the strictly positive sup evaluation `M² > 0` —
cannot certify any nonnegative sup-norm target `T`:

`¬ (T ≤ w · (M2) ^ r)`.

Composing the negative-value producer with the sup-extraction obstruction: the signed depth lever
inverts the census pinning without bounding the sup norm.  Uniform in the target `T ≥ 0`, the
negative weight `w`, the positive evaluation point `M2`, and the depth `r`. -/
theorem signed_census_functional_no_sup_certificate
    {w M2 T : ℝ} (hw : w < 0) (hM2 : 0 < M2) (hT : 0 ≤ T) (r : ℕ) :
    ¬ (T ≤ w * M2 ^ r) :=
  neg_eval_cannot_certify_nonneg_target (single_neg_dominating_weight_eval_neg hw hM2 r) hT

/-- The route the signed no-go refutes: "a dominating-depth negative signed reweighting yields a
sup-norm lower bound", i.e. the nonnegative sup target `T` is certified by the (negative) census
transfer value `w · (M2)^r`.  A scope marker for honesty — this proposition is a proven refutation
whenever the dominating weight is negative and the sup evaluation is positive. -/
def signedCensusYieldsSupBound (w M2 T : ℝ) (r : ℕ) : Prop :=
  T ≤ w * M2 ^ r

/-- The dominating-depth negative signed census reweighting provably does NOT yield a sup-norm
lower bound for any nonnegative target.  Honest scope marker, no axioms. -/
theorem not_signedCensusYieldsSupBound
    {w M2 T : ℝ} (hw : w < 0) (hM2 : 0 < M2) (hT : 0 ≤ T) (r : ℕ) :
    ¬ signedCensusYieldsSupBound w M2 T r :=
  signed_census_functional_no_sup_certificate hw hM2 hT r

#print axioms neg_eval_cannot_certify_nonneg_target
#print axioms single_neg_dominating_weight_eval_neg
#print axioms signed_census_functional_no_sup_certificate
#print axioms not_signedCensusYieldsSupBound

end ArkLib.ProximityGap.Frontier.G67SignedCensusSupExtractionNoGo
