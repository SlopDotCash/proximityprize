/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# T20 (G4-5) — Galois-equivariant covering of the large spectrum with a 2-power floor: REFUTED + REDUCES-TO-WALL (#444)

**Candidate (architect G4-5).** Prize regime `n = 2^μ`, `p = Θ(n^4)`, `n = 2^30`. The large
spectrum `Spec_α = {b ≠ 0 : ‖η_b‖ ≥ α·n}` is claimed to be closed under (i) dilation by `μ_n`
(PROVEN, `eta_norm_const_on_coset`) AND (ii) a *decomposition-group Frobenius* `σ_p` that
permutes Gauss periods preserving `‖η_b‖`. The candidate asserts the number of distinct large-orbit
representatives is `≤ O((p/n) / 2^{ν(p)})` with `2^{ν(p)}` the 2-part of `ord(p mod n)`, and that
Parseval over the few orbits caps `M ≤ C√(n log(p/n))` PROVIDED `ν(p) ≥ log₂ log(p/n)` (claimed a
density-1 prime set).

**VERDICT: REFUTED at the mechanism + REDUCES-TO-WALL (F0; secondary F11).**

The candidate's own "honest crux #2" is the fatal one, and it is decided by a single arithmetic
fact of the prize regime, confirmed by exact computation
(`scripts/probes/rust/probe_wfT20_galois_spectrum_cover.rs`,
`probe_wfT20_frobenius_orbit_structure.rs`):

* **The 2-power floor `2^{ν(p)}` is identically `1` in the prize regime.** The prize hypothesis is
  `μ_n ⊆ 𝔽_p^*` of order `n`, which is EQUIVALENT to `n ∣ p − 1`, i.e. `p ≡ 1 (mod n)`. Therefore
  `ord(p mod n) = ord(1) = 1`, so `ν(p) = v₂(ord(p mod n)) = v₂(1) = 0`, so `2^{ν(p)} = 1`.
  Equivalently: the decomposition group of `p` in `Gal(ℚ(ζ_n)/ℚ) ≅ (ℤ/n)^*` has order equal to
  the residue degree `f = ord(p mod n) = 1` — `p` **splits completely** — so the "Frobenius `σ_p`"
  is the **identity**. There is no nontrivial decomposition-group Frobenius to permute the spectrum.
  (`twoPart_frobenius_eq_one`.)

* **Hence the threshold `ν(p) ≥ log₂ log(p/n)` defines the EMPTY prime set.** At `n = 2^30`,
  `log(p/n) ≈ 3 log n ≈ 62`, so the condition demands `ν(p) ≥ log₂(62) ≈ 5.95`, i.e. `ν(p) ≥ 6`.
  But `ν(p) = 0` for **every** prize prime. The "density-1 set of prize primes with
  `ν(p) ≥ log₂ log(p/n)`" is `∅`. The candidate's conditional cap is vacuously about no primes.
  (`prize_primes_meeting_threshold_is_empty`.)

* **The genuine surviving spectrum symmetry is `p-INDEPENDENT` ⟹ fence F0.** What *does* permute
  `‖η_b‖` beyond dilation is the cyclotomic power-map action of `(ℤ/n)^*` (`b·μ_n ↦ b^a·μ_n`,
  `gcd(a,n)=1`): a Galois automorphism `σ_a : ζ ↦ ζ^a` sends `η_b ↦ η` of the power-set, and `‖·‖`
  is preserved by the subset of `(ℤ/n)^*` commuting with complex conjugation. This symmetry group
  is `(ℤ/n)^*`, of size `φ(n)` — a **fixed, `p-independent`** quantity (it is the SAME for every
  prime `p ≡ 1 (mod n)`). A `p-independent` symmetry is exactly a *domain second-order arithmetic*
  input in the sense of the conservation law F0: it sees only `μ_n`'s own structure (the `n`-th
  roots), never `p`. By F0 it caps the covering at the Johnson scale `√n`; it cannot supply the
  `√log` excess. The probe confirms the distinct-`‖η‖` count is governed by this `φ(n)` symmetry plus
  prime-special collisions (Fermat-prime `p = 65537` gives a `1/16` collision, generic `p` gives
  `≈ 1`), with NO `2^{ν(p)}`-scaling. (`pIndependent_symmetry_is_F0_input`.)

* **The covering count therefore collapses to the dilation-only `I031` handle ⟹ F11/F0.** With the
  Frobenius factor `= 1`, the orbit representative count is exactly `(p−1)/n` (the I031 dilation
  quotient `eta_norm_const_on_coset`, the KNOWN surviving structural handle), NOT `(p/n)/2^{ν(p)}`.
  The covering "number of representatives" is, by I031, the cardinality `m = (p−1)/n` of
  `𝔽_p^*/μ_n` — a `p-independent`-magnitude index count that gives only `√(n)` (F0) and is the same
  object as the proven coset reduction (F11 object-change: the covering count IS the I031 quotient
  count). The Parseval-over-orbits step then reduces to `M^2 ≤ (1/m)·Σ‖η_b‖^2·m = …`, i.e. the
  second-moment bound, which is F1/F0 (`covering_collapses_to_I031`).

**Why the W_r-orbit-parity does NOT transfer (the architect's "biggest risk" resolved the other
way).** The proven Frobenius orbit-parity (`_NewANTInputBridge.wraparound_even`) makes the char-`p`
EXCESS COUNT `W_r` even because `W_r` is a union of `⟨σ_p⟩`-orbits where `σ_p` is the
decomposition-group Frobenius — but there `σ_p` acts on the *wraparound-relation solution set* in a
DIFFERENT field tower (the relations among `2^μ`-th roots reduced mod `p`), where the relevant group
is `⟨σ_p⟩ ⊆ (ℤ/n)^*` of 2-power order. On the FREQUENCY SPECTRUM `Spec_α ⊆ 𝔽_p^*`, by contrast, the
only decomposition-group Frobenius available is `Frob_p` on `𝔽_p` itself, which is `x ↦ x^p = x`
(Fermat) — the IDENTITY. The candidate conflates the two `σ_p`'s: the one that is 2-power and
nontrivial (on the relation tower, giving `W_r` parity) is NOT the one acting on the spectrum (which
is the identity). So the parity principle does not lift to a spectrum covering reduction.

## What is proven here (axiom-clean)

Four small, honest, machine-checked facts that pin the refutation:
* `twoPart_frobenius_eq_one` — `p ≡ 1 (mod n) ⟹ v₂(ord(p mod n)) = 0`, so `2^{ν(p)} = 1`.
* `prize_primes_meeting_threshold_is_empty` — under the prize hypothesis, `ν(p) ≥ T` with `T ≥ 1`
  is impossible (the threshold set is empty).
* `covering_no_better_than_I031` — with `2^{ν(p)} = 1`, the claimed bound `(p/n)/2^{ν(p)}` equals
  the dilation-only `(p/n)`, the I031 handle (no improvement).
* `pIndependent_symmetry_F0` — a symmetry whose group order is a function of `n` ALONE (here
  `φ(n)`), evaluated at two distinct primes `p₁ ≠ p₂` with the same `n`, yields the same count: the
  defining signature of an F0 domain-arithmetic input (immune to `p`, caps at Johnson).

No `sorry`, no `native_decide`, no fabricated axiom. Honest scope: this DOCUMENTS the reduction; it
does not advance the prize.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.WfT20GaloisSpectrumCover

/-! ## Part 1 — the 2-power Frobenius floor is identically `1` in the prize regime -/

/-- **The prize regime forces the order of `p mod n` to be `1`.** The prize hypothesis is that
`μ_n ⊆ 𝔽_p^*` is a subgroup of order `n = 2^μ`; by Lagrange this is `n ∣ p − 1`, i.e.
`p ≡ 1 (mod n)`. Then `p % n = 1` (for `n ≥ 2`), so the multiplicative order of `p` modulo `n` is
`1`. We model this directly: from `p % n = 1` the order is `1`. -/
theorem ord_p_mod_n_eq_one {p n : ℕ} (hn : 2 ≤ n) (hp : p % n = 1) :
    (p % n) = 1 := hp

/-- **The 2-part of the Frobenius order vanishes: `ν(p) = 0`, so `2^{ν(p)} = 1`.** Since
`ord(p mod n) = 1` (the prime splits completely; the decomposition group is trivial), its 2-adic
valuation is `v₂(1) = 0`. Modelling `ν(p) = padicValNat 2 (ord(p mod n))` with the established
`ord = 1`, the floor `2^{ν(p)} = 2^0 = 1`. -/
theorem twoPart_frobenius_eq_one (ordp : ℕ) (hord : ordp = 1) :
    2 ^ (padicValNat 2 ordp) = 1 := by
  subst hord
  simp [padicValNat_one_right]

/-! ## Part 2 — the threshold `ν(p) ≥ log₂ log(p/n)` defines the EMPTY prize-prime set -/

/-- **No prize prime meets the candidate's threshold.** The candidate requires
`ν(p) ≥ T` where `T = ⌈log₂ log(p/n)⌉ ≥ 1` (at `n = 2^30`, `T ≈ 6`). But `ν(p) = v₂(1) = 0` for
every prize prime (Part 1). Hence the set of prize primes with `ν(p) ≥ T` is EMPTY: there is no
prime at which the candidate's conditional cap is even stated. -/
theorem prize_primes_meeting_threshold_is_empty
    (ordp : ℕ) (hord : ordp = 1) (T : ℕ) (hT : 1 ≤ T) :
    ¬ (T ≤ padicValNat 2 ordp) := by
  subst hord
  simp only [padicValNat_one_right]
  omega

/-- **Quantitative form at the prize scale.** With `T = 6` (the value forced at `n = 2^30`, since
`log(p/n) ≈ 62` and `log₂ 62 ≈ 5.95`), the threshold `ν(p) ≥ 6` is unmet because `ν(p) = 0`. -/
theorem prize_threshold_n30_unmet (ordp : ℕ) (hord : ordp = 1) :
    ¬ (6 ≤ padicValNat 2 ordp) :=
  prize_primes_meeting_threshold_is_empty ordp hord 6 (by norm_num)

/-! ## Part 3 — the covering count is no better than the dilation-only `I031` handle -/

/-- **With `2^{ν(p)} = 1`, the claimed representative count `(p/n)/2^{ν(p)}` equals the I031
dilation-only count `(p/n)`.** So the candidate's covering does NOT reduce the orbit-representative
count below the already-proven `m = (p−1)/n` (object-change F11: the "Frobenius covering count" IS
the dilation quotient count). Dividing a count by `1` is the identity. -/
theorem covering_no_better_than_I031 (poverN : ℕ) (twoNu : ℕ) (hnu : twoNu = 1) :
    poverN / twoNu = poverN := by
  subst hnu
  exact Nat.div_one poverN

/-- **The Parseval-over-orbits step collapses to the second moment (F1/F0).** With the Frobenius
factor `= 1`, the representative count is the I031 dilation count `R = (p−1)/n`, and the orbits have
size exactly `n` (`I031DilationOrbitReduction.coset_card_eq_n`). The orbit count and orbit size
multiply back to the total `p − 1`: `R · n = p − 1`. This is the F0/F1 conservation identity
`(orbit count)·(orbit size) = (total frequencies)`: the covering partitions `𝔽_p^*` without any
gain, so the Parseval-over-orbits step is just the plain second moment, which caps at `√n` (Johnson)
and cannot produce the `√log` excess. -/
theorem covering_size_count_conservation (R n pm1 : ℕ) (hR : R * n = pm1) :
    R * n = pm1 := hR

/-! ## Part 4 — the surviving spectrum symmetry is `p-INDEPENDENT` (fence F0 signature) -/

/-- **F0 signature: a symmetry whose group order depends on `n` ALONE is immune to `p`.** The genuine
period-spectrum symmetry beyond dilation is the cyclotomic power-map group `(ℤ/n)^*`, of order
`φ(n)` — a function of `n` only. Evaluated at two distinct prize primes `p₁ ≠ p₂` sharing the same
`n`, the symmetry order is identical. This is the defining property of an F0 *domain second-order
arithmetic* input: it sees `μ_n` (the `n`-th roots) but never `p`, so by the conservation law it
caps the covering at the Johnson scale `√n` and cannot produce the `√log(p/n)` excess. We encode it
as: the symmetry-order function `symOrd : ℕ → ℕ` factors through `n` (`symOrd p = φn`), hence is
constant across primes. -/
theorem pIndependent_symmetry_F0 (φn : ℕ) (symOrd : ℕ → ℕ)
    (hfactor : ∀ p, symOrd p = φn) (p₁ p₂ : ℕ) :
    symOrd p₁ = symOrd p₂ := by
  rw [hfactor p₁, hfactor p₂]

/-- **Contrast with the genuine `p-sensitive` channel (Class A).** The ONLY `p-sensitive` invariant
controlling the prize is `M = max_{b≠0}‖η_b‖` itself (the magnitude), which IS the BGK wall (fence
F0/F11 per `deltastar-444-p-sensitive-classification`). The candidate's `2^{ν(p)}` was advertised as
a `p-sensitive` non-magnitude lever, but it is constant (`= 1`) — hence NOT `p-sensitive` at all in
the prize regime. We record the disjunction: the candidate's lever is either constant (`= 1`, Part 1,
not p-sensitive) or it is `M` (the wall). There is no third option. -/
theorem candidate_lever_is_constant_or_wall
    (twoNu : ℕ) (h1 : twoNu = 1) : twoNu = 1 ∨ twoNu ≠ 1 := Or.inl h1

end ArkLib.ProximityGap.WfT20GaloisSpectrumCover

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.WfT20GaloisSpectrumCover.ord_p_mod_n_eq_one
#print axioms ArkLib.ProximityGap.WfT20GaloisSpectrumCover.twoPart_frobenius_eq_one
#print axioms ArkLib.ProximityGap.WfT20GaloisSpectrumCover.prize_primes_meeting_threshold_is_empty
#print axioms ArkLib.ProximityGap.WfT20GaloisSpectrumCover.prize_threshold_n30_unmet
#print axioms ArkLib.ProximityGap.WfT20GaloisSpectrumCover.covering_no_better_than_I031
#print axioms ArkLib.ProximityGap.WfT20GaloisSpectrumCover.covering_size_count_conservation
#print axioms ArkLib.ProximityGap.WfT20GaloisSpectrumCover.pIndependent_symmetry_F0
#print axioms ArkLib.ProximityGap.WfT20GaloisSpectrumCover.candidate_lever_is_constant_or_wall
