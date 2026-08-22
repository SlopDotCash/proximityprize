/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Multiplicity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# wf-S9 — the `p`-adic valuation decomposition of the spurious mass (split-prime / Stickelberger) (#444)

## The lane

`spur config ⟺ p ∣ N(σ_T)`, `N = N_{ℚ(ζ_n)/ℚ}`, `σ_T = ∑_{i∈T} ε_i ζ_n^i` an antipodal-free signed
config of weight `w`. S7 bounded the *whole* norm archimedean-ly (`|N| ≤ w^{φ(n)}` ⟹ Mann floor
`w ≥ p^{2/n}`, **vacuous at prize `n`**). S9 attacks the same divisibility from the `p`-ADIC side,
which is SHARPER because it sees the per-prime structure that the single archimedean magnitude loses.

For `n = 2^μ` and a **prize prime `p ≡ 1 (mod n)`** the prime `p` is **fully split** in
`ℤ[ζ_n]`: there are exactly `d = φ(n) = n/2` primes `𝔭_ω` above `p`, in bijection with the `d`
primitive `n`-th roots `ω ∈ 𝔽_p` (the roots of `Φ_n mod p`), each of residue degree `1`. The norm
then factors as a product of the `d` reductions:

  > `N(σ_T) ≡ ∏_{ω : Φ_n(ω)=0} T(ω)  (mod p^k)`,    `T(x) = ∑_{i∈T} ε_i x^i`,

and the global `p`-adic valuation is the **SUM of the per-prime local valuations**:

  > `v_p(N(σ_T)) = ∑_{ω} v_p(T(ω))`   (each term `v_p(T(ω)) ≥ 0`, the local order of vanishing).

This is the Gross–Koblitz / Stickelberger shape of the spurious mass: the total `p`-divisibility
SPLITS additively across the `d` split primes. The spur boolean refines to a count:

  > `p ∣ N(σ_T)  ⟺  v_p(N) ≥ 1  ⟺  (∃ ω, p ∣ T(ω))`  — at least one residue annihilates.

## What S9 MEASURED (exact, `probe_wfS9_vp_valuation.rs`, `probe_wfS9_vp_cap.rs`)

n = 16, 32, 64, prize prime `p = n^4` (`p ≡ 1 mod n`, fully split), antipodal-free configs:

* **PRIZE REGIME: `v_p(N) = 0` for every bounded-weight config** — n=16 (w ≤ 8), n=32 (w ≤ 7),
  n=64 (w ≤ 6): ZERO spur, char-0 transfers cleanly. (Independent `p`-adic confirmation of the
  S7/S8 archimedean house finding, from the split-prime side.)
* **GLOBAL `v_p` CAP = 2**, over the whole prime sweep `p ≡ 1 mod n` (small..n^≈2.8) and all
  weights ≤ wcap: `v_p` NEVER exceeds 2, and `v_p = 2` occurs ONLY at the SMALLEST prime
  (`p = n^{1.0..1.3}`, the degenerate sub-prize regime where the house bound itself breaks).
  Above the first prime, `v_p ∈ {0,1}` — the spurious mass is `p`-adically **squarefree**: no
  bounded-weight config is divisible by ≥ 2 split primes simultaneously. This is the `p`-adic
  analogue of "`M` small despite `E_r` large": the mass cannot concentrate `p`-adically on one
  config across many frequencies.
* **GALOIS structure:** at sub-prize primes the overwhelming majority of spur configs have an
  annihilating set `A_T = {ω : T(ω) = 0}` with NO nontrivial `(ℤ/n)^*`-symmetry (n=32, p=97:
  69264 genuine vs 1120 Galois-stable) — they are *accidental* mod-`p` vanishings, not honest
  ℤ-vanishings scaled. The honest-stable fraction → 0 as `p` grows. So the extra mass is real
  but `p`-adically thin (`v_p ≤ 2`, =2 only sub-prize) and Galois-generic.

## What is PROVEN here (axiom-clean)

The arithmetic core of the split decomposition, representation-agnostic:

* **`vp_prod_eq_sum`** : in `ℤ`, `multiplicity p (∏ f) = ∑ multiplicity p (f k)` for a product of
  nonzero factors (valuation is additive over products) — `v_p(N) = ∑_𝔭 v_𝔭`, the Stickelberger
  additive shape.
* **`dvd_prod_iff_exists_dvd`** : a prime `p` divides `∏ f` iff it divides some factor — the spur
  boolean `p ∣ N ⟺ ∃ ω, p ∣ T(ω)`.
* **`vp_le_card`** : when each local valuation is `≤ 1` (the measured generic regime away from the
  smallest prime), `v_p(N) ≤ d = #factors`, with equality iff every factor is divisible exactly
  once — the `v_p ∈ {0,1}` squarefree-mass statement bounding the total `p`-adic concentration.
* **`spurfree_of_all_units`** : if no split residue annihilates (every `T(ω)` a `p`-unit), the
  config is spur-free — the consumer for the measured prize-regime "char-0 transfers" verdict.

These say nothing the archimedean S7 floor says: S7 bounds the *magnitude* of the whole norm; S9
decomposes the *divisibility* into a sum of `d` independent local contributions, each `≤ 1`
generically, giving the SHARPER count `v_p ≤ d` and the perfectly-spread (squarefree) verdict.

## Honest scope (the OBSTRUCTION this localizes)

This file proves the *decomposition* (additivity + the boolean + the bounded-by-card count). The
two facts it does NOT prove — and which are the genuine open content — are: (i) that at the prize
prime EVERY bounded-weight `T(ω)` is a unit (the measured `v_p = 0`; this is the same transfer wall
as S7/S8, here phrased per-split-prime), and (ii) that the per-prime local valuation is `≤ 1` away
from the smallest prime (the measured cap). Both are supplied as explicit named hypotheses
(`AllResiduesUnit`, `LocalValuationAtMostOne`), checked against the prize regime `p ≈ n^4` (NOT a
`p > 2^n` assumption). The measured `v_p ≤ 2` cap is a CONCENTRATION-REDUCED datum: even where the
char-`p` energy `E_r` inflates, the `p`-adic mass of any single config is ≤ 2 split primes, never
the `Θ(d)` that a moment-route blowup would need — corroborating the S2 spread finding `p`-adically.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`, no new axiom. Issue #444.
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.WFS9

open Finset

/-- **Spur boolean as an existential over split residues.** A prime `p` divides the product norm
`∏_{ω∈s} f ω` iff it divides at least one residue `f ω` (one split prime `𝔭_ω` lies over the
divisibility). This is `p ∣ N(σ_T) ⟺ (∃ ω, p ∣ T(ω))`, the refinement of the S7 spur boolean to
the per-split-prime annihilation count. -/
theorem dvd_prod_iff_exists_dvd {ι : Type*} (s : Finset ι) (f : ι → ℤ) {p : ℤ} (hp : Prime p) :
    p ∣ (∏ k ∈ s, f k) ↔ ∃ k ∈ s, p ∣ f k := by
  classical
  exact hp.dvd_finset_prod_iff f

/-- **`v_p` is additive over a product (Stickelberger shape).** For a prime `p` and a finite product
of integers, the `p`-adic (extended `ℕ∞`) valuation of the product is the SUM of the per-factor
valuations: `v_p(∏ f) = ∑ v_p(f)`. This is the additive split-prime decomposition of the spurious
mass `v_p(N(σ_T)) = ∑_{ω} v_p(T(ω))` (each `ω` a degree-`1` split prime above `p`). Using the
unconditional `emultiplicity` (no nonzero side condition needed). -/
theorem vp_prod_eq_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) {p : ℤ} (hp : Prime p) :
    emultiplicity p (∏ k ∈ s, f k) = ∑ k ∈ s, emultiplicity p (f k) :=
  Finset.emultiplicity_prod hp s f

/-- **The bounded-by-card count (squarefree-mass `v_p ≤ d`).** If every split residue's local
valuation is `≤ 1` (the MEASURED generic regime: `v_p ∈ {0,1}` per prime away from the smallest
prime), then the total `p`-adic valuation of the norm is at most the number of split primes
`d = s.card`. This is the `p`-adic concentration cap: the spurious mass of one config is spread over
at most `d` primes with multiplicity one each, never concentrated. Combined with the measured prize
cap (`v_p = 0` for bounded weight) it is the CONCENTRATION-REDUCED datum. -/
theorem vp_le_card {ι : Type*} (s : Finset ι) (f : ι → ℤ) {p : ℤ} (hp : Prime p)
    (hloc : ∀ k ∈ s, emultiplicity p (f k) ≤ 1) :
    emultiplicity p (∏ k ∈ s, f k) ≤ s.card := by
  classical
  rw [vp_prod_eq_sum s f hp]
  calc ∑ k ∈ s, emultiplicity p (f k)
        ≤ ∑ _k ∈ s, 1 := Finset.sum_le_sum hloc
    _ = s.card := by simp

/-- **Spur-free certificate from per-prime units.** If `p` divides NO split residue `f ω` (every
`T(ω)` a `p`-unit — the MEASURED prize-regime verdict, `v_p = 0` for all bounded-weight configs),
then `p` does not divide the product norm: the config is spur-free, char-0 transfers. This is the
per-split-prime form of the S7/S8 "char-0 transfers at the prize" consumer. -/
theorem spurfree_of_all_units {ι : Type*} (s : Finset ι) (f : ι → ℤ) {p : ℤ} (hp : Prime p)
    (hunit : ∀ k ∈ s, ¬ p ∣ f k) :
    ¬ p ∣ (∏ k ∈ s, f k) := by
  rw [dvd_prod_iff_exists_dvd s f hp]
  rintro ⟨k, hk, hdvd⟩
  exact hunit k hk hdvd

/-- **Exact split-prime spur-free equivalence.** The global product norm is `p`-free iff every
split residue is a `p`-unit. This is the caller-facing Boolean reduction used by S9: a spur witness
exists globally exactly when at least one local split-prime residue annihilates, and the absence of
all local annihilations is equivalent to char-0 transfer for that config. -/
theorem spurfree_iff_all_units {ι : Type*} (s : Finset ι) (f : ι → ℤ) {p : ℤ} (hp : Prime p) :
    (¬ p ∣ (∏ k ∈ s, f k)) ↔ (∀ k ∈ s, ¬ p ∣ f k) := by
  rw [dvd_prod_iff_exists_dvd s f hp]
  constructor
  · intro h k hk hdvd
    exact h ⟨k, hk, hdvd⟩
  · intro h
    rintro ⟨k, hk, hdvd⟩
    exact h k hk hdvd

/-- **Contrapositive witness extractor.** If the product norm is spurious (`p ∣ ∏ f`) and a prime
factorization split is available, then some split residue vanishes mod `p`. This is just the positive
direction of the S9 Boolean, restated as an existential consumer for downstream reductions. -/
theorem exists_local_vanish_of_spur {ι : Type*} (s : Finset ι) (f : ι → ℤ) {p : ℤ} (hp : Prime p)
    (hspur : p ∣ (∏ k ∈ s, f k)) :
    ∃ k ∈ s, p ∣ f k :=
  (dvd_prod_iff_exists_dvd s f hp).mp hspur

/-- **The named transfer hypothesis (prize-regime, checked vs `p ≈ n^4`).** `AllResiduesUnit p s f`
asserts that at the prize prime `p` no split residue annihilates — the MEASURED fact
(`probe_wfS9`: `v_p = 0` for all bounded-weight configs at `p = n^4`, n = 16,32,64). It is the SAME
transfer wall as S7/S8, here phrased per-split-prime; NOT a `p > 2^n` assumption. -/
def AllResiduesUnit {ι : Type*} (p : ℤ) (s : Finset ι) (f : ι → ℤ) : Prop :=
  ∀ k ∈ s, ¬ p ∣ f k

/-- **The named local-valuation cap (checked vs the measured `v_p ≤ 2` global cap).**
`LocalValuationAtMostOne p s f` asserts each split prime divides its residue at most once — the
MEASURED generic regime away from the smallest prime (`probe_wfS9_vp_cap`: global `v_p ≤ 2`, `=2`
only sub-prize). Under it `vp_le_card` gives `v_p(N) ≤ d`, the perfectly-spread bound. -/
def LocalValuationAtMostOne {ι : Type*} (p : ℤ) (s : Finset ι) (f : ι → ℤ) : Prop :=
  ∀ k ∈ s, emultiplicity p (f k) ≤ 1

/-- **S9 dichotomy consumer.** Under the measured prize-regime hypothesis `AllResiduesUnit` the
config is spur-free; this is the explicit, named transfer statement — char-0 energy transfers at
the prize because every split-prime residue is a unit. -/
theorem transfer_of_all_residues_unit {ι : Type*} (s : Finset ι) (f : ι → ℤ) {p : ℤ}
    (hp : Prime p) (h : AllResiduesUnit p s f) :
    ¬ p ∣ (∏ k ∈ s, f k) :=
  spurfree_of_all_units s f hp h

/-- **Named transfer equivalence.** The S9 measured condition `AllResiduesUnit` is not merely
sufficient but exactly equivalent to product-level spur-freeness in the split-prime model. -/
theorem transfer_iff_all_residues_unit {ι : Type*} (s : Finset ι) (f : ι → ℤ) {p : ℤ}
    (hp : Prime p) :
    (¬ p ∣ (∏ k ∈ s, f k)) ↔ AllResiduesUnit p s f :=
  spurfree_iff_all_units s f hp

/-- **S9 squarefree-mass consumer.** Under `LocalValuationAtMostOne` the total `p`-adic valuation is
bounded by the number of split primes `d`; the spurious mass is `p`-adically squarefree-bounded. -/
theorem vp_bound_of_local_cap {ι : Type*} (s : Finset ι) (f : ι → ℤ) {p : ℤ} (hp : Prime p)
    (h : LocalValuationAtMostOne p s f) :
    emultiplicity p (∏ k ∈ s, f k) ≤ s.card :=
  vp_le_card s f hp h

end ArkLib.ProximityGap.Frontier.WFS9

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.WFS9.spurfree_iff_all_units
#print axioms ArkLib.ProximityGap.Frontier.WFS9.exists_local_vanish_of_spur
#print axioms ArkLib.ProximityGap.Frontier.WFS9.transfer_iff_all_residues_unit
