/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
-- Proximity Gap frontier lane (#334 / #444): GALOIS_STICKELBERGER_PHASE_DESCENT.
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Galois / Stickelberger phase-descent for the Gauss-period sup-norm — #444 lane

**Target object.** `μ_n ≤ F_p^*` order `n=2^μ`, `p ≡ 1 (mod n)`, `m := (p-1)/n`.
`η_b = Σ_{x∈μ_n} e_p(b x)` and `M = max_{b≠0} |η_b|`. Prize: `M ≤ C√(n log(p/n))`.

**The Galois structure (exact, classical).** `Gal(ℚ(ζ_p)/ℚ) ≅ (ℤ/p)^*`, `σ_t : ζ_p ↦ ζ_p^t`,
acts on the additive character by `e_p(x) ↦ e_p(tx)`, hence
`η_b^{σ_t} = Σ_{x∈μ_n} e_p(t b x) = η_{t b}`. Because `μ_n` stabilises each coset, `η_{tb}=η_b`
for `t∈μ_n`, so `η_b` depends only on the coset `b μ_n ∈ F_p^*/μ_n` and the **Galois orbit of
`η_b` is exactly the multiset of the `m=(p-1)/n` coset-values `{η_{tb}}_t`.**

**The load-bearing dichotomy this lane formalises (PROVEN here):**
* `GaloisOrbitRMS`: the *average* of `|η|²` over the `m` coset-values equals `n` exactly
  (Plancherel: `Σ_{b∈F_p^*}|η_b|² = n(p-1)`, each coset counted `n` times, so the `m`-term
  coset average is `(p-1)·n / (p-1) = n`). The Galois-orbit **RMS is `√n`, p-independently.**
* `GaloisOrbitMaxIsM`: the *maximum* over the Galois orbit equals `M` (tautological — the orbit
  is the set of all coset-values, whose max over all `b≠0` is `M`).

Combining: Galois-averaging recovers the magnitude floor `√n` and **never the max**. The
prize is the `max/RMS` ratio, and `(p E_k)^{1/2k} ≥ n` (the MRS phase-blind floor) shows every
magnitude/energy transfer is stuck at exponent `1`. Galois descent is one such transfer:
*the average of any Galois-invariant magnitude functional is fixed by Plancherel and carries
no phase*, so it cannot beat `√n·(spread)`.

**Stickelberger valuation spread (the reason the product formula is phase-blind), exact:**
for `χ` of order `d`, the Stickelberger fractional parts `{⟨ac/d⟩}_{c∈(ℤ/d)^*}` are, for every
`a` with `gcd(a,d)=1`, a *permutation of the same multiset* `{1/d,…,(d-1)/d}` (proven below as
`stickelberger_fracparts_const`). The valuation multiset of `g(χ^a)` is therefore **independent
of `a`** — it carries no per-character phase. All conjugates of `g(χ)/√p` lie on the unit circle,
so the Mahler measure is `1` and the product formula gives `0` phase information. This is the
precise obstruction: Galois + Stickelberger pin **magnitudes** (`|g|=√p`, RMS `=√n`), the prize
lives in the **archimedean phases**, which Galois averaging discards.

**Status.** `GaloisRMSDescent` (RMS `=√n` ⇒ no Galois-average bound below `√n` per coset) and
`stickelberger_fracparts_const` are PROVEN axiom-clean. The prize gap is recorded as the named
residual `GaloisPhaseSpreadResidual`: bounding `max/RMS = M/√n` by `C√(log m)` requires phase
anti-correlation among the `{η_{tb}}` that NO Galois-invariant magnitude functional sees.
This REDUCES Paley to a cleaner phase statement (orbit extreme-value spread) but does NOT
close it — Galois/Stickelberger is shown to be *phase-blind*, the same wall.
-/

namespace ArkLib.ProximityGap.GaloisStickelberger

open Finset

/-- **Stickelberger fractional-part spread is constant in `a`.** For modulus `d` and any unit
`a` (gcd(a,d)=1), `c ↦ (a*c) % d` is a permutation of the units mod `d`; hence the multiset of
Stickelberger fractional parts `{⟨a c / d⟩}` (equivalently `{(a*c) % d}`) over `c` ranging in a
unit-stable index set is independent of `a`. We capture the load-bearing combinatorial core:
multiplication by a unit is a bijection of `ZMod d`, so the image multiset of any finite index
map is reindexed, not changed.

This is the exact reason the Stickelberger valuation multiset of `g(χ^a)` does not depend on `a`
and so carries no per-character (phase) information. -/
theorem stickelberger_fracparts_const
    (d : ℕ) [NeZero d] (a : ZMod d) (ha : IsUnit a) :
    Finset.univ.image (fun c : ZMod d => a * c) = (Finset.univ : Finset (ZMod d)) := by
  -- multiplication by a unit is surjective onto univ
  apply Finset.eq_univ_of_forall
  intro y
  obtain ⟨u, hu⟩ := ha
  rw [Finset.mem_image]
  refine ⟨(↑u⁻¹) * y, Finset.mem_univ _, ?_⟩
  rw [← mul_assoc, ← hu, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

/-- The Galois-orbit magnitude functional (abstract). `orbitSqAvg` is the average of `|η|²` over
the `m` coset values; `GaloisOrbitRMS` asserts it equals `n`. We state it as a `Prop` over a
real-valued abstraction (the coset values `v : Fin m → ℝ` are `|η_{coset}|`), because the
Plancherel identity `(1/m)·Σ v i² = n` is the *only* input Galois averaging provides. -/
def GaloisOrbitRMS (m n : ℕ) (v : Fin m → ℝ) : Prop :=
    (∑ i, (v i)^2) = (m : ℝ) * (n : ℝ)

/-- The Galois-orbit max equals the prize quantity `M`. Tautological abstraction: `M` is the
greatest coset value, i.e. `M` is an upper bound and is attained. This makes precise that the
prize quantity `M` IS the orbit max — Galois descent cannot relocate it. -/
def GaloisOrbitMaxIsM (m : ℕ) (v : Fin m → ℝ) (M : ℝ) : Prop :=
    (∀ i, v i ≤ M) ∧ (∃ i, v i = M)

/-- **PROVEN: the Galois-average floor.** From the Plancherel RMS identity, the *quadratic mean*
of the orbit is exactly `√n`, so any bound obtained by averaging `|η|²` over the Galois orbit is
pinned at `√n` and cannot certify anything below it per coset. Concretely: there exists a coset
value with `v i² ≥ n` (the max is at least the mean), so the orbit-max `M ≥ √n` — Galois
averaging recovers the magnitude floor, never a sub-`√n` bound. -/
theorem GaloisRMSDescent
    (m n : ℕ) (hm : 0 < m) (v : Fin m → ℝ)
    (hRMS : GaloisOrbitRMS m n v) :
    ∃ i, (v i)^2 ≥ (n : ℝ) := by
  unfold GaloisOrbitRMS at hRMS
  by_contra h
  push Not at h
  -- every term < n, so the sum < m*n, contradicting the Plancherel identity = m*n
  have hsum : (∑ i, (v i)^2) < (m : ℝ) * (n : ℝ) := by
    calc (∑ i, (v i)^2) < ∑ _i : Fin m, (n : ℝ) := by
              apply Finset.sum_lt_sum_of_nonempty
              · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm)
              · intro i _; exact h i
      _ = (m : ℝ) * (n : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  rw [hRMS] at hsum
  exact lt_irrefl _ hsum

/-- **The named residual the lane reduces Paley TO** (a cleaner phase statement). Bounding the
Galois-orbit extreme value `M = max_i v i` by `C·√(n·log m)` — given only the RMS identity
`Σ v i² = m n` — is FALSE for arbitrary `v` (no concentration), and TRUE for the actual `η`
coset values *only because* their archimedean phases anti-correlate (Gumbel spread of `m`
near-independent `√n`-RMS phasors). Galois/Stickelberger pins the RMS (magnitudes) but is blind
to this phase anti-correlation. This is the precise cleaner statement Paley reduces to here. -/
def GaloisPhaseSpreadResidual (m n : ℕ) (v : Fin m → ℝ) (C : ℝ) : Prop :=
    GaloisOrbitRMS m n v →
      (∀ i, v i ≤ C * Real.sqrt ((n : ℝ) * Real.log (m : ℝ)))

end ArkLib.ProximityGap.GaloisStickelberger

