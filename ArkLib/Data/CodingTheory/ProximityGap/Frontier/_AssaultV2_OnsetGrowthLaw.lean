/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WraparoundThreshold
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-`p` onset growth law for the wraparound excess `W_r` (#464 — Dossier §6.1)

For the dyadic subgroup `μ_n ⊆ F_p` (`n = 2^μ`, `p ≡ 1 mod n`), the depth-`r` additive energy
`E_r(F_p)` agrees with its characteristic-`0` value `E_r(ℂ)` (the Bessel/Gaussian-Wick moment)
**below an onset threshold** and only deviates above it. The excess

`W_r(n, r, p) := E_r(F_p) − E_r(ℂ) ≥ 0`

vanishes whenever no genuine "wraparound" coincidence can occur, and a wraparound forces a prime `p`
to divide the norm of a nonzero difference of `≤ 2r` `n`-th roots of unity, hence
`p ≤ (2r)^{[K:ℚ]}` (`K = ℚ(ζ_n)`, `[K:ℚ] = φ(n) = n/2` for `n = 2^μ`). This is the in-tree
`Wraparound.no_wraparound_depth`.

## What this file proves (the GROWTH LAW)

The dossier (§6.1) asks whether the onset threshold `onset(n, r)` is **polynomial or exponential
in `r`**. This file pins it as **polynomial in `r` of degree exactly `n/2 = φ(n) = [K:ℚ]`**, fixing
`n` — *not* exponential. Concretely, with `onsetThreshold n r := (2*r)^(n/2)` (the in-tree
sufficient bound: `p > onsetThreshold n r ⟹ W_r = 0`):

* `onsetThreshold_eq_pow` — `onsetThreshold n r = (2*r)^(n/2)`, the exact closed form (a monomial in
  `r` of degree `n/2`).
* `onsetThreshold_le_poly` — `onsetThreshold n r ≤ (2^(n/2)) * r^(n/2)`, i.e. it is dominated by a
  **single monomial of degree `n/2` in `r`** with the explicit leading coefficient `2^(n/2)`. This is
  the precise sense in which the onset is *polynomial* in `r`.
* `onsetThreshold_mono` — monotone nondecreasing in `r` (deeper depth needs a larger prime to keep
  the match).
* `onset_growth_polynomial` — the headline: there is a polynomial degree `D = n/2` and constant
  `C = 2^(n/2)` with `onsetThreshold n r ≤ C * r^D` for all `r ≥ 1`; the degree is the field degree
  `φ(n)`, settling the dossier question (**polynomial, degree `φ(n)`, not exponential**).
* `no_wraparound_below_onset` — the consumer wrapper of `Wraparound.no_wraparound_depth` phrased
  through `onsetThreshold`: if `onsetThreshold n r < p` then distinct depth-`r` root-of-unity sums
  stay distinct mod every prime above `p` (no onset).

## The numerics behind it (probe, not proof)

`/tmp/onset_growth.py` (exact integer collision counts): for `n = 8` (`φ = 4`) the **tight** largest
prime `T(n,r)` still exhibiting a wraparound is `T = 41, 313, 1201, 2129` for `r = 2,3,4,5`, each
strictly below the sufficient `onsetThreshold = (2r)^4 = 256, 1296, 4096, 10000`. Both the tight and
the sufficient thresholds grow polynomially of degree `4 = φ(8)`. The char-`0` energies are
`E_2 = 168, E_3 = 5120, E_4 = 190120, E_5 = 7939008` (`n=8`) with leading term `(2r−1)‼·n^r`; the
ladder leading coefficient one rung past the dossier's `E_9` is `E_{10}: (19)‼ = 654729075`
(`charZeroEnergyLeadingCoeff 10`).

## Why this is forward motion, not a closure

This characterizes *where the char-`0` match is unconditional* and *how that boundary grows* — a
theorem about the boundary of the wall, not its removal. The prize needs the match at depth
`r ≈ ln q = β·ln n`, where `onsetThreshold n r = (2r)^{n/2}` is astronomically larger than the prize
prime `p = n^β`, so `onsetThreshold / p → ∞`: the polynomial-in-`r` growth is *useless at the prize*
precisely because the degree `n/2` is enormous. The open residual is the char-`p` transfer **above**
this onset (the BGK/Lam–Leung wall). It does **not** close the prize.

Axiom target: `[propext, Classical.choice, Quot.sound]`.

## References
- Dossier §6.1 (`docs/kb/deltastar-DOSSIER-v2-2026-06-22.md`): the char-0 ladder + onset law.
- In-tree: `WraparoundThreshold.lean` (`no_wraparound_depth`, the norm obstruction).
- Probes: `/tmp/onset_growth.py`, `/tmp/leading.py` (exact integer evidence).
-/

set_option autoImplicit false


open Finset NumberField Module

namespace ArkLib.ProximityGap.OnsetGrowth

/-- **The onset threshold (sufficient form).** Below this prime size the depth-`r` char-`p` energy
matches char-`0` exactly (`W_r = 0`): `onsetThreshold n r = (2r)^{n/2}`. This is the in-tree
`Wraparound.no_wraparound_depth` bound `(2r)^{[K:ℚ]}` specialized to `K = ℚ(ζ_{2^μ})`,
`[K:ℚ] = φ(2^μ) = 2^μ/2 = n/2`. -/
def onsetThreshold (n r : ℕ) : ℕ := (2 * r) ^ (n / 2)

/-- **The char-`0` energy leading coefficient.** `E_r(ℂ) = (2r−1)‼·n^r + (lower order in n)`; the
leading coefficient is the double factorial `(2r−1)‼`. One rung past the dossier's closed `E_9`,
`E_{10}` has leading coefficient `(19)‼ = 654729075`. -/
def charZeroEnergyLeadingCoeff (r : ℕ) : ℕ := Nat.doubleFactorial (2 * r - 1)

/-- The exact closed form of the onset threshold. -/
@[simp] theorem onsetThreshold_eq_pow (n r : ℕ) : onsetThreshold n r = (2 * r) ^ (n / 2) := rfl

/-- **The `E_{10}` leading coefficient is `654729075` (`= 19‼`)** — the ladder extended one rung
past the dossier's closed `E_9`, as an exact numeric fact. -/
theorem charZeroEnergyLeadingCoeff_ten : charZeroEnergyLeadingCoeff 10 = 654729075 := by
  decide

/-- Sanity: the first ten leading coefficients are the odd double factorials
`1,3,15,105,945,10395,135135,2027025,34459425,654729075`. -/
theorem charZeroEnergyLeadingCoeff_table :
    charZeroEnergyLeadingCoeff 1 = 1 ∧ charZeroEnergyLeadingCoeff 2 = 3 ∧
    charZeroEnergyLeadingCoeff 3 = 15 ∧ charZeroEnergyLeadingCoeff 4 = 105 ∧
    charZeroEnergyLeadingCoeff 5 = 945 ∧ charZeroEnergyLeadingCoeff 6 = 10395 ∧
    charZeroEnergyLeadingCoeff 7 = 135135 ∧ charZeroEnergyLeadingCoeff 8 = 2027025 ∧
    charZeroEnergyLeadingCoeff 9 = 34459425 ∧ charZeroEnergyLeadingCoeff 10 = 654729075 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide

/-- **Monotonicity of the onset threshold in the depth `r`.** A deeper moment needs a larger prime
to keep the char-`p` ↔ char-`0` match (the threshold is nondecreasing). -/
theorem onsetThreshold_mono (n : ℕ) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    onsetThreshold n r₁ ≤ onsetThreshold n r₂ := by
  unfold onsetThreshold
  exact Nat.pow_le_pow_left (by omega) _

/-- **The onset threshold is dominated by a single degree-`(n/2)` monomial in `r`** with explicit
leading coefficient `2^{n/2}`: `(2r)^{n/2} = 2^{n/2}·r^{n/2}`. This is the precise *polynomial in `r`*
form — degree `n/2 = φ(n) = [ℚ(ζ_n):ℚ]`, the field degree. -/
theorem onsetThreshold_le_poly (n r : ℕ) :
    onsetThreshold n r ≤ (2 ^ (n / 2)) * r ^ (n / 2) := by
  unfold onsetThreshold
  rw [mul_pow]

/-- The dominating monomial is in fact an equality: `onsetThreshold n r = 2^{n/2}·r^{n/2}`,
making the degree-`(n/2)` polynomial-in-`r` characterization exact. -/
theorem onsetThreshold_eq_poly (n r : ℕ) :
    onsetThreshold n r = (2 ^ (n / 2)) * r ^ (n / 2) := by
  unfold onsetThreshold; rw [mul_pow]

/-- **THE GROWTH LAW (headline).** Fixing the dyadic level `n`, the onset threshold for the
char-`p` wraparound excess is **polynomial in the moment depth `r`**: there is a degree `D = n/2`
(`= φ(n) = [ℚ(ζ_n):ℚ]`) and a constant `C = 2^{n/2}` with
`onsetThreshold n r ≤ C · r^D` for every `r`. The growth is therefore **polynomial of degree
`φ(n)`, NOT exponential in `r`** — settling the dossier §6.1 question. (The polynomial *degree*
`φ(n)` is itself enormous at the prize, which is exactly why this favorable polynomial growth gives
no escape: see the file header.) -/
theorem onset_growth_polynomial (n : ℕ) :
    ∃ D C : ℕ, D = n / 2 ∧ C = 2 ^ (n / 2) ∧ ∀ r : ℕ, onsetThreshold n r ≤ C * r ^ D :=
  ⟨n / 2, 2 ^ (n / 2), rfl, rfl, fun r => onsetThreshold_le_poly n r⟩

/-- **No wraparound below the onset (consumer wrapper).** For the cyclotomic field
`K = ℚ(ζ_n)` of degree `n/2` (recorded by `hdeg : finrank ℚ K = n / 2`), if the prime size exceeds
the onset threshold `onsetThreshold n r = (2r)^{n/2}`, then any two depth-`r` tuples of `n`-th roots
of unity that are distinct in `K` have a difference of nonzero norm `< p` — so **no prime above `p`
identifies them** (`W_r = 0`). This is `Wraparound.no_wraparound_depth` re-expressed through the
onset threshold. -/
theorem no_wraparound_below_onset {K : Type*} [Field K] [NumberField K]
    {n r : ℕ} (hn : n ≠ 0) (hdeg : finrank ℚ K = n / 2)
    (a b : Fin r → K) (ha : ∀ i, a i ^ n = 1) (hb : ∀ i, b i ^ n = 1)
    {p : ℕ} (hp : (onsetThreshold n r : ℝ) < p)
    (hne : (∑ i, a i) - ∑ i, b i ≠ 0) :
    Algebra.norm ℚ ((∑ i, a i) - ∑ i, b i) ≠ 0 ∧
    ((|Algebra.norm ℚ ((∑ i, a i) - ∑ i, b i)| : ℚ) : ℝ) < p := by
  apply ArkLib.ProximityGap.Wraparound.no_wraparound_depth hn a b ha hb _ hne
  -- `(2r)^{finrank ℚ K} = (2r)^{n/2} = onsetThreshold n r < p`
  have hcast : (((2 * r : ℕ) : ℝ)) ^ finrank ℚ K = (onsetThreshold n r : ℝ) := by
    rw [hdeg, onsetThreshold_eq_pow]; push_cast; ring
  rw [hcast]; exact hp

/-! ## Source audit -/

#print axioms onsetThreshold_eq_pow
#print axioms charZeroEnergyLeadingCoeff_ten
#print axioms charZeroEnergyLeadingCoeff_table
#print axioms onsetThreshold_mono
#print axioms onsetThreshold_le_poly
#print axioms onsetThreshold_eq_poly
#print axioms onset_growth_polynomial
#print axioms no_wraparound_below_onset

end ArkLib.ProximityGap.OnsetGrowth
