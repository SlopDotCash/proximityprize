/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

set_option autoImplicit false

/-!
# D2 lower-tail concentration gate: the ∃-form gains nothing under a concentration floor

**Lane L3 (#466, dossier v3 §6 Tier-2): the D2 Rogers–Siegel DECISION — decided.**

The D2 sliver asked: *is a prize prime a rare large-deviation lower-tail anomaly?*  I.e. does the
∃-form of the core ("SOME prime `p ≡ 1 mod n` in the window has `M(n,p) ≤ C·√(n log(p/n))` with an
unusually small `C`") gain anything over the ∀-form?  The gate
`_D2RogersSiegelVarianceGate.lean` showed the Rogers/Siegel variance route needs a pointwise
prime-to-lattice coupling; the remaining DECIDABLE question was empirical: how does `M(n,p)`
DISTRIBUTE over the prime ensemble — heavy or thin lower tail?

**Empirical verdict (probe `scripts/probes/probe_466_rogers_siegel_tail.py`, output
`_out_466_rogers_siegel_tail.txt`, 2026-07-01): CONCENTRATION.**  Over ALL 2038 primes
`p ≡ 1 mod 16` in `(16⁴, 4·16⁴]` (full exact coset scan, Parseval-checked) and 2200+ sampled
primes `p ≡ 1 mod 32` in `(32⁴, 4·32⁴]`, the normalized statistic `x = M/√(n log(p/n))`:

* n = 16: `x ∈ [1.104, 1.218]`, std `0.019`; `P(x < 1.1) = 0` on the FULL ensemble;
* the Gumbel-standardized max sits ~1.9 scale units BELOW the iid benchmark with std `0.33`
  vs Gumbel `1.28` — the true max is *strictly more concentrated* than the iid model
  (consistent with the strict char-0 sub-Gaussianity,
  `D2LargeDeviationRateFunction.bessel_strictly_below_exp`);
* no anomaly class: the smallest-`x` primes show no `v₂`, generalized-Fermat, or
  smooth-cofactor signature; GF primes are NOT lower-tail outliers.

So the lower tail is doubly-exponentially THIN (thinner than Gumbel), and the best prime in the
whole window beats the median constant by < 4%.  This file records the resulting no-go
axiom-cleanly: the empirical concentration floor is carried as the named Prop
`LowerTailConcentrationFloor` (an EMPIRICAL hypothesis, per the honesty contract — measured, not
proven), and its consumers show the ∃-form collapses to the ∀-form up to the measured
band-width constant.  Complements (does not touch) the coupling gate in
`_D2RogersSiegelVarianceGate.lean`.
-/

namespace ArkLib.ProximityGap.Frontier.D2LowerTailConcentrationGate

/-- **The (empirical) lower-tail concentration floor.**  `stat p` (the prime statistic `M(n,p)`)
never falls below `c` times its natural scale (`√(n log(p/n))`).  Measured at `c = 1.10` for
`n = 16` (full ensemble) and at the corresponding band for `n = 32` (sampled + all structured
primes).  This is a NAMED EMPIRICAL HYPOTHESIS, not a theorem — the probe decides its truth over
the scanned windows only. -/
def LowerTailConcentrationFloor {P : Type*} (stat scale : P → ℝ) (c : ℝ) : Prop :=
  ∀ p, c * scale p ≤ stat p

/-- **The ∃-form lever is exactly a heavy lower tail.**  The negation of the concentration floor
is precisely the existence of an anomalous prime below the floor level.  The probe measured the
right-hand side FALSE at `c = 1.10`, `n ∈ {16, 32}` — so the lever is empirically dead. -/
theorem not_floor_iff_anomalous_witness {P : Type*} (stat scale : P → ℝ) (c : ℝ) :
    ¬ LowerTailConcentrationFloor stat scale c ↔ ∃ p, stat p < c * scale p := by
  unfold LowerTailConcentrationFloor
  push_neg
  rfl

/-- **No large-deviation anomaly below the floor.**  Under the concentration floor, no prime
achieves the statistic at any target `T` strictly below `c · scale p`: the ∃-form cannot certify
a constant below the measured floor `c`. -/
theorem no_anomalous_prime_of_floor {P : Type*} {stat scale : P → ℝ} {c : ℝ}
    (h : LowerTailConcentrationFloor stat scale c) (T : ℝ) :
    ¬ ∃ p, stat p ≤ T ∧ T < c * scale p := by
  rintro ⟨p, hle, hlt⟩
  exact absurd (lt_of_le_of_lt hle hlt) (not_lt_of_ge (h p))

/-- **The ∃-form collapses to the ∀-form up to the band ratio.**  If the ensemble sits in the
two-sided band `c · scale ≤ stat ≤ C · scale`, then the constant certified by the BEST prime
(any ∃-witness at level `c' · scale p`) is within the fixed factor `C/c` of the constant valid
for EVERY prime: choosing a rare good prime improves the core inequality by at most the measured
band width (probe: `C/c ≤ 1.218/1.104 < 1.11` at `n = 16`).  No order-of-magnitude gain is
available from the ∃-form. -/
theorem exists_form_within_band_of_forall {P : Type*} {stat scale : P → ℝ} {c C : ℝ}
    (hfloor : LowerTailConcentrationFloor stat scale c)
    (hceil : ∀ p, stat p ≤ C * scale p)
    {p₀ : P} {c' : ℝ} (hwitness : stat p₀ ≤ c' * scale p₀) (hscale : 0 < scale p₀) :
    c ≤ c' ∧ ∀ p, stat p ≤ C * scale p := by
  refine ⟨?_, hceil⟩
  have hfl := hfloor p₀
  have : c * scale p₀ ≤ c' * scale p₀ := le_trans hfl hwitness
  exact le_of_mul_le_mul_right (by linarith) hscale

/-! ## Axiom audit — must be ⊆ {propext, Classical.choice, Quot.sound}; no `sorryAx`. -/
#print axioms not_floor_iff_anomalous_witness
#print axioms no_anomalous_prime_of_floor
#print axioms exists_form_within_band_of_forall

end ArkLib.ProximityGap.Frontier.D2LowerTailConcentrationGate
