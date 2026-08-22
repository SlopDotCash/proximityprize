/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26SumsOfRootsOfUnity

/-!
# The effective bad-prime ceiling for the char-`p` spurious-collision count (Issue #444)

The latest open-core characterization (commit `40df3426d`, KB `direct-supnorm-data-beta4-2026-06-15.md`)
pins the prize obstruction to the **arithmetic** (p-divisibility) count

    `Spur_r(p) = #{ antipodal-free T, |T| ≤ 2r : p ∣ N(σ_T) }`,   `N(σ_T) = Res_ℤ(R_T, Φ_{2^m})`,

the number of short antipodal-free relations whose cyclotomic norm is divisible by the prize prime `p`.
The wf-C1 lane studies the **effective-Chebotarev count** of the "bad" primes (those for which any
genuine short relation can be `p`-divisible). This file lands the foundational **finiteness / ceiling**
input for that count, building directly on the in-tree archimedean resultant bound.

## The ceiling

`KKH26.natAbs_resultant_cyclotomic_le` gives the archimedean size bound `|Res_ℤ(R, Φ_{2^m})| ≤
‖R‖₁^{2^{m−1}}` for a relation `R` with `deg R < 2^{m−1}`, and `ResultantLiftLoop52`/`KKH26` give that
this resultant is **nonzero** for a coprime nonzero `R`. A prime dividing a nonzero integer is at most
its absolute value. Combining:

> **`bad_prime_le_l1On_pow`** — if a prime `p` divides `Res_ℤ(R, Φ_{2^m})` for a genuine short relation
> `R` (`R ≠ 0`, `deg R < 2^{m−1}`), then `p ≤ ‖R‖₁^{2^{m−1}}`.

So **every bad prime for a fixed short relation lies below an explicit, `p`-independent ceiling**
`‖R‖₁^{2^{m−1}}`. For an antipodal-free relation of weight `w` (`‖R‖₁ ≤ w`), this specialises to

> **`bad_prime_weight_le`** — `p ≤ w^{2^{m−1}}`.

This is the wf-C1 effective-Chebotarev *finiteness* substrate: the bad-prime set for weight-`w` relations
is contained in `[2, w^{2^{m−1}}]`, hence finite, and is **disjoint from the prize regime** for any prime
`p > w^{2^{m−1}}` — in particular the per-relation bad set never reaches a prize prime `p ≈ n^β` once
`w^{2^{m−1}} < p`, i.e. whenever the relation weight stays below `p^{1/2^{m−1}} = p^{2/n}`. The genuine
open content (the BCHKS-1.12 wall) is the regime where the depth `r ≈ log q` forces weights `w ≈ 2 log q`
with `w^{2^{m−1}} ≫ p`, so the ceiling no longer excludes the prize prime and the count `Spur_r(p)` is
genuinely live.

## Probe corroboration

`probe_pdiv_resbound_count.py` / `probe_pdiv_generator_norms.py` (exact sympy, proper `μ_n`, `n = 2^m`,
`m = 4,5`, never `n = q−1`):
- **The size bound holds:** max weight-4 norm `196 ≤ 8^4` (`n=16`), `38416 ≤ 8^8` (`n=32`), i.e.
  `|N| ≤ (4r)^{φ(n)/2} = 8^{n/4}` for `2r = 4`.
- **The weight-4 bad-prize set is FINITE** (subset of the prime divisors of the `9`/`53` distinct
  weight-4 norm values), with the effective-Chebotarev count bounded by `Σ log₂|N| / log₂(n+1)`
  (`12.1`/`115.1`, actual `2`/`24` — the divisor bound is loose as expected).

## Honest scope (rules 1, 3, 6)

NOT a CORE closure and NOT a new analytic input — it is the contrapositive packaging of the in-tree
size⟹not-dvd bridge (`not_dvd_resultant_of_l1On_pow_lt`) as a positive `p`-independent ceiling on the
per-relation bad-prime set, the finiteness substrate the wf-C1 effective-Chebotarev count rests on. It
does NOT bound `Spur_r(p)` at the prize depth `r ≈ log q` (where `w^{2^{m−1}} ≫ p` and the ceiling is
vacuous) — that is exactly the open BCHKS-1.12 wall. CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays **OPEN**.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
- KB `direct-supnorm-data-beta4-2026-06-15.md`; `SpurBadPrimeChebotarev.lean` (the `p ≡ 3 mod 4`
  exclusion); `ShortRelationNormBase.lean` (weight-2 base).
- `KKH26SumsOfRootsOfUnity.lean` (`natAbs_resultant_cyclotomic_le`, `l1On`,
  `not_dvd_resultant_of_l1On_pow_lt`); `ResultantLiftLoop52.lean` (resultant nonvanishing).
-/

set_option linter.style.longLine false
set_option autoImplicit false

namespace ArkLib.ProximityGap.SpurBadPrimeCeiling

open Polynomial Finset
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.ResultantLiftLoop52

/-- **THE EFFECTIVE BAD-PRIME CEILING.** If a prime `p` divides the cyclotomic resultant
`Res_ℤ(R, Φ_{2^m})` of a genuine short relation `R` (`R ≠ 0`, `deg R < 2^{m−1}`, `m ≥ 1`), then
`p ≤ ‖R‖₁^{2^{m−1}}`. The resultant is nonzero (coprimality over `ℚ`) and of absolute value
`≤ ‖R‖₁^{2^{m−1}}` (archimedean bound `natAbs_resultant_cyclotomic_le`); a prime dividing a nonzero
integer is at most its absolute value. So the per-relation bad-prime set lies below an explicit,
`p`-independent ceiling — the wf-C1 effective-Chebotarev finiteness substrate. -/
theorem bad_prime_le_l1On_pow {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : 1 ≤ m)
    {R : Polynomial ℤ} (hR0 : R ≠ 0) (hdeg : R.natDegree < 2 ^ (m - 1))
    (hdvd : (p : ℤ) ∣ Polynomial.resultant R (cyclotomic (2 ^ m) ℤ)) :
    p ≤ l1On (2 ^ (m - 1)) R ^ 2 ^ (m - 1) := by
  -- the resultant is nonzero
  have hne : Polynomial.resultant R (cyclotomic (2 ^ m) ℤ) ≠ 0 :=
    resultant_int_ne_zero_of_isCoprime_rat _ _ (diff_coprime_cyclotomic_rat hm R hdeg hR0)
  -- p divides it ⟹ p ≤ |Res|
  have hle : p ≤ (Polynomial.resultant R (cyclotomic (2 ^ m) ℤ)).natAbs := by
    have h2 := Int.natAbs_dvd_natAbs.mpr hdvd
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (by simpa using h2)
  -- |Res| ≤ ‖R‖₁^{2^{m-1}}
  have hub := natAbs_resultant_cyclotomic_le hm R hdeg
  exact le_trans hle hub

/-- **Weight-specialised ceiling.** If additionally the relation has `ℓ¹`-mass at most `w`
(`l1On (2^{m−1}) R ≤ w` — automatic for a weight-`w` relation, `‖R‖₁ ≤ w`), a bad prime satisfies
`p ≤ w^{2^{m−1}}`. So the bad-prime set for weight-`w` short relations is contained in `[2, w^{2^{m−1}}]`,
disjoint from any prize prime `p > w^{2^{m−1}}`. -/
theorem bad_prime_weight_le {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : 1 ≤ m)
    {R : Polynomial ℤ} (hR0 : R ≠ 0) (hdeg : R.natDegree < 2 ^ (m - 1))
    {w : ℕ} (hw : l1On (2 ^ (m - 1)) R ≤ w)
    (hdvd : (p : ℤ) ∣ Polynomial.resultant R (cyclotomic (2 ^ m) ℤ)) :
    p ≤ w ^ 2 ^ (m - 1) := by
  refine le_trans (bad_prime_le_l1On_pow hp hm hR0 hdeg hdvd) ?_
  exact Nat.pow_le_pow_left hw _

/-- **Prize-prime exclusion (the per-relation form).** A prime `p` strictly above the ceiling
`‖R‖₁^{2^{m−1}}` is NOT bad for `R`: it divides no cyclotomic resultant of the short relation. This is
the positive content of the ceiling — for relations light enough that the ceiling sits below the prize
regime, the prize prime is automatically good. (Contrapositive of `bad_prime_le_l1On_pow`; also a direct
restatement of the in-tree `not_dvd_resultant_of_l1On_pow_lt` size⟹not-dvd bridge.) -/
theorem prize_prime_good_of_gt_ceiling {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : 1 ≤ m)
    {R : Polynomial ℤ} (hR0 : R ≠ 0) (hdeg : R.natDegree < 2 ^ (m - 1))
    (hgt : l1On (2 ^ (m - 1)) R ^ 2 ^ (m - 1) < p) :
    ¬ (p : ℤ) ∣ Polynomial.resultant R (cyclotomic (2 ^ m) ℤ) := by
  intro hdvd
  have hle := bad_prime_le_l1On_pow hp hm hR0 hdeg hdvd
  omega

end ArkLib.ProximityGap.SpurBadPrimeCeiling

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SpurBadPrimeCeiling.bad_prime_le_l1On_pow
#print axioms ArkLib.ProximityGap.SpurBadPrimeCeiling.bad_prime_weight_le
#print axioms ArkLib.ProximityGap.SpurBadPrimeCeiling.prize_prime_good_of_gt_ceiling
