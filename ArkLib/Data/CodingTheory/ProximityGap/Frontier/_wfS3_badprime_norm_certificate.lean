/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# S3: the bad-prime / effective-Chebotarev certificate (#444, lane wf-S3)

## The object and the direction

A prize prime `p ≈ n^β` (`p ≡ 1 mod n`, `n = 2^μ`) is **bad at depth `r`** for the char-`p`
spurious-mass route iff `p` divides the cyclotomic norm `N(σ_T) = N_{ℚ(ζ_n)/ℚ}(Σ_{i∈T} ±ζ_n^i)`
of SOME antipodal-free signed config `T` of weight `|T| ≤ 2r`. (`spur_r(p) > 0` ⟺ such a
`p | N(σ_T)`; the spurious mass is exactly the mod-`p` collapse of these cyclotomic norms.)

Lane S3 attacks this from **effective Chebotarev / bad-prime counting**: is the SPECIFIC prize
prime good, and is the bad-prime SET sparse?

## The decisive MEASUREMENT (exact, Rust, reproducible — `probe_wfS3_*`, `c1_badprime_chebotarev`)

For each `n` enumerate every antipodal-free signed config of weight `≤ w = 2r` (coefficient
vector `a ∈ {-1,0,1}^{φ(n)}`) and compute the EXACT integer norm `N(σ_T) =
det(negacyclic matrix of a)`. Let `MAXNORM(n,w) = max_T |N(σ_T)|`. Findings:

| n  | w | MAXNORM log₂ | band floor `β·log₂n` (β=4) | margin | bad density |
|----|---|--------------|----------------------------|--------|-------------|
| 8  | 8 | 3.17         | 12.0                       | −8.83  | 0 (PROVABLE)|
| 16 | 8 | 11.23        | 16.0                       | −4.77  | 0 (PROVABLE)|
| 32 | 4 | 15.23        | 20.0                       | −4.77  | 0 (PROVABLE)|
| 32 | 6 | 20.34        | 20.0                       | +0.34  | 0           |
| 32 | 8 | 23.82        | 20.0                       | +3.82  | 0.0036      |

and the β-sweep at `n=32, w=8`: `β=3 → 40%`, `β=4 → 0.36%`, `β≥5 → 0` (PROVABLE: floor 25 >
MAXNORM 23.82). **Two regimes, cleanly separated by ONE inequality.**

## THE CERTIFICATE this file formalizes (axiom-clean, the rigorous half)

`p | N(σ_T)` with `N(σ_T) ≠ 0` forces `p ≤ |N(σ_T)|` (a prime divisor of a nonzero integer is at
most its absolute value). Contrapositive — the **good-prime certificate**:

  > if `|N(σ_T)| < p` for EVERY config `T` of weight `≤ 2r`, then `p` divides no such norm,
  > i.e. `p` is GOOD at depth `r` (no spurious config, `spur_r(p) = 0`).

Equivalently, with `MAXNORM(n, 2r) := max_T |N(σ_T)|`: **`MAXNORM(n,2r) < p ⟹ p good`.**
This is exactly the `PROVABLE-ZERO` column above, and it is unconditional number theory.

`badPrime` / `goodAtDepth` below name the predicate; `good_of_maxnorm_lt` and
`good_of_norm_lt_of_forall` are the certificate, both axiom-clean.

## The honest scope (the OBSTRUCTION at prize scale)

The certificate is a THEOREM but its hypothesis FAILS at the genuine prize scale:
`MAXNORM(n,w)` grows ~ **linearly in `n`** at fixed weight (measured `MAXNORM log₂(w=4) ≈ 0.48·n`),
while the band floor grows only ~ `β·log₂ n` (logarithmically). So at `n = 2^30` even the minimal
weight-4 norms vastly exceed `p ≈ n^4`, the certificate's hypothesis is false, and bad primes
EXIST. Worse, at depth `r ≈ ln q` the weight `w = 2r ≈ 2β ln n` GROWS, the config count is
quasi-polynomial `n^{Θ(ln n)}`, and the bad set is no longer provably sparse — this is the
recorded S3 OBSTRUCTION (the "generic prime is good" hope, via norm-size, dies at prize scale).
What SURVIVES: at any FIXED depth `r` the bad set is FINITE and explicitly certifiable, and the
density decays as `β` grows. See `probe_wfS3_badprime_crossover.rs` and the #444 comment.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`, no new axiom. Issue #444.
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.WFS3

/-- A prime `p` is **bad** for the cyclotomic-norm collection `norms` (the integer norms
`N(σ_T)` over all antipodal-free signed configs `T` of weight `≤ 2r`) iff it divides one of the
NONZERO norms. This is the char-`p` spurious-config predicate: `p` bad ⟺ `spur_r(p) > 0`. -/
def badPrime (p : ℕ) (norms : Finset ℤ) : Prop :=
  ∃ N ∈ norms, N ≠ 0 ∧ (p : ℤ) ∣ N

/-- `p` is **good at depth `r`** for the collection `norms` iff it is not bad. -/
def goodAtDepth (p : ℕ) (norms : Finset ℤ) : Prop := ¬ badPrime p norms

/-- **Norm-size certificate (single config).** If a nonzero cyclotomic norm `N` is divided by `p`
(with `p ≥ 1`), then `p ≤ |N|`. (A divisor of a nonzero integer is at most its absolute value.)
This is the load-bearing arithmetic fact behind the whole S3 dichotomy. -/
theorem le_natAbs_of_dvd {p : ℕ} {N : ℤ} (hN : N ≠ 0) (hdvd : (p : ℤ) ∣ N) :
    p ≤ N.natAbs := by
  have hNa : (N.natAbs : ℤ) ≠ 0 := by
    simpa [Int.natAbs_eq_zero] using hN
  have hdvd' : p ∣ N.natAbs := by
    have : (p : ℤ) ∣ (N.natAbs : ℤ) := (Int.dvd_natAbs).mpr hdvd
    exact_mod_cast this
  have hpos : 0 < N.natAbs := Int.natAbs_pos.mpr hN
  exact Nat.le_of_dvd hpos hdvd'

/-- **Good-prime certificate (single config form).** If `|N| < p`, then `p` does not divide the
nonzero norm `N`. -/
theorem not_dvd_of_natAbs_lt {p : ℕ} {N : ℤ} (hN : N ≠ 0)
    (hlt : N.natAbs < p) : ¬ (p : ℤ) ∣ N := by
  intro hdvd
  exact absurd (le_natAbs_of_dvd hN hdvd) (Nat.not_le.mpr hlt)

/-- **The S3 good-prime certificate (collection form).** If EVERY norm in the collection has
absolute value `< p`, then `p` is good at depth `r`: it divides no nonzero norm, so
`spur_r(p) = 0`. This is the unconditional `PROVABLE-ZERO` lever; its hypothesis is the
`MAXNORM(n,2r) < p` inequality measured in the probe. -/
theorem good_of_forall_natAbs_lt {p : ℕ} {norms : Finset ℤ}
    (h : ∀ N ∈ norms, N.natAbs < p) : goodAtDepth p norms := by
  rintro ⟨N, hmem, hN, hdvd⟩
  exact not_dvd_of_natAbs_lt hN (h N hmem) hdvd

/-- **`MAXNORM` form.** If the maximum `natAbs` over the collection is `< p`, then `p` is good.
This is the exact statement read off the probe's `MAXNORM(n,2r) < p ⟹ PROVABLE-ZERO` column:
the bad-prime density is identically `0` whenever the largest bounded-weight cyclotomic norm is
below the band floor `p`. -/
theorem good_of_maxnorm_lt {p : ℕ} {norms : Finset ℤ}
    (hmax : ∀ N ∈ norms, N.natAbs ≤ (norms.image Int.natAbs).max.getD 0)
    (hlt : (norms.image Int.natAbs).max.getD 0 < p) : goodAtDepth p norms :=
  good_of_forall_natAbs_lt (fun N hN => lt_of_le_of_lt (hmax N hN) hlt)

/-- The certificate is genuinely two-sided: a bad prime witnesses a norm at least its own size.
This packages the OBSTRUCTION direction — to be bad, `p` must divide a norm `≥ p`, which (at
prize scale) requires `MAXNORM(n,2r) ≥ p`, i.e. the certificate's hypothesis must fail. -/
theorem exists_large_norm_of_bad {p : ℕ} {norms : Finset ℤ}
    (hbad : badPrime p norms) : ∃ N ∈ norms, p ≤ N.natAbs := by
  obtain ⟨N, hmem, hN, hdvd⟩ := hbad
  exact ⟨N, hmem, le_natAbs_of_dvd hN hdvd⟩

end ArkLib.ProximityGap.Frontier.WFS3
