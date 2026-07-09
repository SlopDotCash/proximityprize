/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CyclotomicNormDefectThreshold

/-!
# The sparse-support ideal-SVP HOUSE lower bound (Proximity Prize #407)

This file proves, **axiom-clean**, the *house* (sup-conjugate) lower bound for a spurious sparse
cyclotomic defect — the geometry-of-numbers companion to the norm-defect *upper* threshold in
`CyclotomicNormDefectThreshold.lean`. It is the rigorous core of the **ideal-SVP-split** analysis
(angle: the fully-split prime `𝔭 | p`, residue degree `1`, `N(𝔭) = p`).

## The mathematical content

Let `α = g(ζ_n)` be a nonzero cyclotomic integer (no primitive `n`-th root of unity is a root of
`g` over `ℂ`) that reduces to `0` modulo `𝔭` (a primitive root `ζ ∈ ZMod p` has `g(ζ) = 0`). The
**house** of `α` is `house(α) = max_t |σ_t(α)| = max_{Φ_n(ω)=0} |g(ω)|`, the largest absolute value
of an archimedean conjugate. Then:

> **`house(α)^{φ(n)} ≥ |Norm(α)| = |Res(Φ_n, g)| ≥ p`,  hence  `house(α) ≥ p^{1/φ(n)}`.**

The two inequalities:

* **AM-GM / sup ≥ geometric mean.** `|Res| = ∏_{Φ_n(ω)=0} |g(ω)| ≤ (max_ω |g(ω)|)^{φ(n)} =
  house(α)^{φ(n)}` (`natAbs_resultant_le_house_pow`, a direct instance of the existing
  `nnnorm_prod_eval_cyclotomic_roots_le_bound` with `M = house(α)`).
* **`p`-divisibility + nonvanishing.** `p ∣ |Res|` and `|Res| ≠ 0` give `p ≤ |Res|`
  (reusing `dvd_resultant_of_isPrimitiveRoot_isRoot_bound` and
  `resultant_ne_zero_of_forall_root_ne`).

Chaining: `p ≤ |Res| ≤ house(α)^{φ(n)}` (`prime_le_house_pow_of_cyclotomic_defect`).

### Why this is the right (and new) object

The norm threshold proves the *upper* bound `|N(α)| ≤ (2r)^{φ(n)}` for a `≤ 2r`-term sparse defect.
This file proves the matching *house lower* bound `house(α) ≥ p^{1/φ(n)}` — i.e. **the shortest
sparse defect of `𝔭` in the `ℓ^∞`-Minkowski (house) norm is bounded below by `p^{1/φ(n)} = p^{2/n}`**
(for `n = 2^μ`, `φ(n) = n/2`). It is the *ideal-SVP* statement: every nonzero element of `𝔭`,
sparse or not, has house `≥ p^{1/φ(n)}` (the Minkowski/Hermite floor for an index-`p` ideal).

Combined with the upper threshold, a sparse defect exists only in the window
`p^{1/φ(n)} ≤ house ≤ 2r`, i.e. requires `2r ≥ p^{1/φ(n)}` — **the same onset** `(2r)^{φ(n)} ≥ p`
as the box/norm threshold. **Verified numerically** (`scripts/probes/probe_407_house_min_law.py`,
`probe_407_sparse_vs_lattice_svp.py`): the lattice SVP-min of `𝔭` in house IS sparse-realizable
(its power-basis `ℓ^1` is `≈ 8–13`, well within a signed sum of `2r` roots), so the *sparse-support
sub-count coincides with the full ideal-SVP/box count* — **support sparsity does not lengthen the
shortest vector**, hence offers no lever beyond well-roundedness.

### Honesty contract (does NOT prove the prize)

This is the *easy, true* lower half. In the prize regime `n = p^{1/β}`, `β ∈ [4,5]`, `φ(n) = n/2`,
the bound `house ≥ p^{1/φ(n)} = p^{2/n} → 1` is **VACUOUS** (every sparse defect trivially has house
`≥ 1`; the bound certifies nothing past `house ≥ √2`, the dyadic floor). The genuinely **open** wall
— the *representation mass* of the bounded-house SVP-min orbit and the resulting `max_b |η_b|` — is
NOT addressed here and is not claimed. The sparse-support angle is **settled as `reconfirms_wall`**:
the SVP-min is sparse, the ideal is (approximately) well-rounded (`λ_n/λ_1 → ` bounded), and the
dual transference is tight, so the two-sided pin of the box count transfers verbatim to the sparse
sub-count. See `docs/kb/deltastar-407-sparse-support-ideal-svp-verdict-2026-06-13.md`.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Complex
open scoped NNReal

namespace ArkLib.ProximityGap.CyclotomicNormDefectThreshold

/-! ## §1  The house ≥ geometric-mean bound on the resultant -/

/-- **AM-GM for the cyclotomic resultant.** If the largest archimedean conjugate of `α = g(ζ_n)`
has absolute value `≤ H` (the *house* upper bound: `‖g(ω)‖ ≤ H` for every `n`-th root of unity `ω`),
then `|Res(Φ_n, g)| = ∏_ω |g(ω)| ≤ H^{φ(n)}`. This is the existing magnitude bound applied with
`M = H = house(α)` — the product of `φ(n)` factors each `≤ H` is `≤ H^{φ(n)}`. -/
theorem natAbs_resultant_le_house_pow (n H : ℕ) (g : ℤ[X])
    (hH : ∀ ω : ℂ, ω ^ n = 1 → ‖(g.map (Int.castRingHom ℂ)).eval ω‖₊ ≤ (H : ℝ≥0)) :
    (resultant (cyclotomic n ℤ) g (cyclotomic n ℤ).natDegree g.natDegree).natAbs
      ≤ H ^ n.totient :=
  natAbs_resultant_cyclotomic_le_bound n H g hH

/-! ## §2  The assembled house lower bound `p ≤ house(α)^{φ(n)}` -/

/-- **THE SPARSE-SUPPORT IDEAL-SVP HOUSE LOWER BOUND (assembled, axiom-clean).** Let `g : ℤ[X]`
represent `α = g(ζ_n)`, with:

* `hH`: every archimedean conjugate of `α` has absolute value `≤ H` — i.e. `house(α) ≤ H`
  (the *house bound*; for a `≤ 2r`-term sparse defect, `H = 2r` via `signedSum_eval_nnnorm_le`);
* `hSidon`: `α ≠ 0` in characteristic `0`; and
* `hgζ`: `α ≡ 0 (mod 𝔭)`, via a primitive `n`-th root `ζ ∈ ZMod p` with `g(ζ) = 0`.

Then `p ≤ H^{φ(n)}`. Equivalently, **every nonzero element of `𝔭` (whose house is realized by some
such `g`) has house `≥ p^{1/φ(n)}`** — the Minkowski floor for the index-`p` prime ideal `𝔭`.

This is the **lower** companion to `prime_le_of_cyclotomic_signed_sum`: there `H = 2r` is the
sparse-term *upper* house bound giving `p ≤ (2r)^{φ(n)}`; here `H = house(α)` is the *actual* house,
giving `p ≤ house(α)^{φ(n)}`, i.e. a lower bound on the shortest sparse defect. -/
theorem prime_le_house_pow_of_cyclotomic_defect {n : ℕ} (hn : 0 < n) {p H : ℕ} [Fact p.Prime]
    (g : ℤ[X])
    (hH : ∀ ω : ℂ, ω ^ n = 1 → ‖(g.map (Int.castRingHom ℂ)).eval ω‖₊ ≤ (H : ℝ≥0))
    (hgdeg : (g.map (Int.castRingHom (ZMod p))).natDegree = g.natDegree)
    (hSidon : ∀ ω : ℂ, ω ∈ (cyclotomic n ℂ).roots → (g.map (Int.castRingHom ℂ)).eval ω ≠ 0)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n)
    (hgζ : (g.map (Int.castRingHom (ZMod p))).eval ζ = 0) :
    p ≤ H ^ n.totient := by
  have hdvd := dvd_resultant_of_isPrimitiveRoot_isRoot_bound hn g hgdeg hζ hgζ
  have hbound := natAbs_resultant_le_house_pow n H g hH
  have hResne := resultant_ne_zero_of_forall_root_ne n g hSidon
  set R : ℤ := resultant (cyclotomic n ℤ) g (cyclotomic n ℤ).natDegree g.natDegree with hRdef
  have hpd : p ∣ R.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hpos : 0 < R.natAbs := Int.natAbs_pos.mpr hResne
  exact le_trans (Nat.le_of_dvd hpos hpd) hbound

/-- **House floor, contrapositive (sparse-support ideal-SVP minimum).** If `H^{φ(n)} < p` then no
nonzero cyclotomic integer of `house ≤ H` lies in `𝔭`: any `g` with all conjugates `≤ H`,
char-0-nonvanishing on primitive roots, has **no** primitive `n`-th root `ζ ∈ ZMod p` as a root.
I.e. `house(α) ≥ p^{1/φ(n)}` for every `0 ≠ α ∈ 𝔭`. (VACUOUS in the prize regime where
`p^{1/φ(n)} = p^{2/n} → 1`.) -/
theorem house_ge_of_cyclotomic_defect {n : ℕ} (hn : 0 < n) {p H : ℕ} [Fact p.Prime] (g : ℤ[X])
    (hH : ∀ ω : ℂ, ω ^ n = 1 → ‖(g.map (Int.castRingHom ℂ)).eval ω‖₊ ≤ (H : ℝ≥0))
    (hgdeg : (g.map (Int.castRingHom (ZMod p))).natDegree = g.natDegree)
    (hSidon : ∀ ω : ℂ, ω ∈ (cyclotomic n ℂ).roots → (g.map (Int.castRingHom ℂ)).eval ω ≠ 0)
    (hlt : H ^ n.totient < p)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n) :
    (g.map (Int.castRingHom (ZMod p))).eval ζ ≠ 0 := by
  intro hgζ
  exact absurd (prime_le_house_pow_of_cyclotomic_defect hn g hH hgdeg hSidon hζ hgζ)
    (Nat.not_le.mpr hlt)

/-- **Sparse defect window (assembled).** A spurious `≤ 2r`-term sparse defect `α` of `μ_n` mod `p`
satisfies the two-sided house pin `p^{1/φ(n)} ≤ house(α) ≤ 2r`, equivalently the existence window
`p ≤ (2r)^{φ(n)}` (the onset). Stated as the necessary onset: a `2r`-term defect forces
`p ≤ (2 * r) ^ φ(n)`. This re-derives the box onset from the house bounds — **the sparse-support
onset is the box onset** (no separation), the formal statement of the angle's `reconfirms_wall`
verdict. -/
theorem sparse_defect_onset {n : ℕ} (hn : 0 < n) {p r : ℕ} [Fact p.Prime] (g : ℤ[X])
    (hH : ∀ ω : ℂ, ω ^ n = 1 → ‖(g.map (Int.castRingHom ℂ)).eval ω‖₊ ≤ ((2 * r : ℕ) : ℝ≥0))
    (hgdeg : (g.map (Int.castRingHom (ZMod p))).natDegree = g.natDegree)
    (hSidon : ∀ ω : ℂ, ω ∈ (cyclotomic n ℂ).roots → (g.map (Int.castRingHom ℂ)).eval ω ≠ 0)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n)
    (hgζ : (g.map (Int.castRingHom (ZMod p))).eval ζ = 0) :
    p ≤ (2 * r) ^ n.totient :=
  prime_le_house_pow_of_cyclotomic_defect hn g hH hgdeg hSidon hζ hgζ

end ArkLib.ProximityGap.CyclotomicNormDefectThreshold

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.CyclotomicNormDefectThreshold
#print axioms natAbs_resultant_le_house_pow
#print axioms prime_le_house_pow_of_cyclotomic_defect
#print axioms house_ge_of_cyclotomic_defect
#print axioms sparse_defect_onset
end AxiomAudit
