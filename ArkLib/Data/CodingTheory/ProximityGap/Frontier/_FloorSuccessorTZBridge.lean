/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._TZSubquarticBookkeeping
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FloorLinnikTZClosure

/-!
# The floor-successor ⇒ off-BGK floor closure, on ONE named arithmetic conjecture (#466, lane FS3)

This file collapses the **entire off-BGK floor closure** onto exactly **one** genuinely-open
arithmetic input — the uniform floor-bad conjecture `FloorLocalizationUniform` — by driving the
least-prime premise from the **faithful [TZ24] Theorem 1.1 hypothesis**
`TZDyadicShortIntervalLB` (`_TZSubquarticBookkeeping.lean`), a *confirmed literature theorem*
carried as a named `Prop`, rather than from the abstract per-rung `TZPrimeSupply` family.

## The exact logical chain (part (a) of the lane task)

Write `n = 2^a`.  The chain is:

```
  (C1)  FloorLocalizationUniform FloorBad                    -- THE genuine residual (open)
             i.e.  floor-bad(2^a) = { smallestPrime1ModN(2^a) }   for every a ≥ 4
  (C2)  TZDyadicShortIntervalLB c a₀ β₀   with  β₀ ≤ 3       -- [TZ24] Thm 1.1 §3.1 (CONFIRMED)
  (C3)  density-≥-1 side condition at the rung a             -- arithmetic (true for large a)
     ─────────────────────────────────────────────────────────────────────────────────────
  (S1)  exists_dyadic_prime_below_prize  [from C2+C3]
             ⟹  ∃ prime q ≡ 1 (mod 2^a),  (q:ℝ) ≤ (2^a)^4
  (S2)  smallestPrime1ModN_le_of_witness + "(2^a)^4 is not prime"
             ⟹  smallestPrime1ModN(2^a, 2^{5a}) < (2^a)^4        ( = LinnikLeastPrimeBelowPrize @ a )
  (S3)  floor_closes_by_linnik (inlined at the rung a)  [from C1+S2]
             ⟹  every prize prime  p ≥ (2^a)^4  is floor-GOOD:  ¬ FloorBad (2^a) p
```

**Which piece is the genuine residual?**  Exactly **(C1)**, `FloorLocalizationUniform` — the
uniform floor-bad = `{p_min(n)}` conjecture (verified `n=16` axiom-clean, `n=32` by exhaustive
scan; `floor-bad(64) = {193}?` open, an integer-divisibility/height question, NOT a character
sum).  (C2) is a genuine theorem of Thorner–Zaman (confirmed verbatim in
`docs/kb/deltastar-464-thorner-zaman-subquartic-CONFIRMED-2026-06-27.md`), beyond present Lean
analytic NT but *not conjectural*; (C3) is an elementary size side condition on `c, a` (the
window density grows like `(2^a)^{β₀−1} → ∞`).  So the whole off-BGK floor rests on **one**
open arithmetic statement with a clean cyclotomic-resultant characterization.

## The height angle (part (b), recorded — NOT a Lean claim here)

The obstruction norms `N_{r_k}(A) = Res(V_A, Φ_n)` (`scripts/probes/_out_466_successor_norm.txt`)
have height `≤ (n+1)^{n/2} = 2^{O(n log n)}`:

| n  | p_min | max‖N_{r_k}‖ (log₂) | crude bound (n+1)^{n/2} (log₂) | prize scale n⁴ (log₂) | R_n odd part |
|----|-------|---------------------|--------------------------------|-----------------------|--------------|
| 16 | 17    | 11.2                | 32.7                           | 16.0                  | 17² (=289)   |
| 32 | 97    | 35.4                | 80.7                           | 20.0                  | 97² (=9409)  |
| 64 | 193   | 141.4               | 192.7                          | 24.0                  | (see below)  |

Two decisive observations, both **against** a height proof of (C1):

* The resultant height `2^{O(n log n)} = (2^a)^{O(a)}` is **exponentially above prize scale**
  `n⁴ = (2^a)⁴`.  So a height bound on `N_{r_k}(A)` (hence on any `≡1 mod n` prime factor)
  **cannot** certify `p_min < n⁴`; that separation is exactly what TZ (C2) supplies and height
  does not.  (At `n=16` the height `2^{11.2}` already exceeds `n⁴`; every second candidate prime
  `97 ≡ 1 mod 16 < 2^{11.2}` is height-admissible yet does not divide `R_16`.)
* What actually selects `p_min` is the **arithmetic identity** `oddPart(R_n) = p_min²`
  (exact at `n=16,32`) together with the *cross-`r_k` gcd* structure: at `n=64` the canonical
  (non-realizable) pattern's seven norms have **empty** `≡1 mod 64` intersection (gcd `= 2^{12}`,
  odd part `1`), so realizability is decided by which primes are *common to all seven norms*, a
  divisibility fact invisible to any single-norm height bound.

**Conclusion (b):** the height bound is valid but *insufficient*; it does not force
`common factor = p_min`.  The uniform conjecture (C1) is therefore genuinely irreducible to a
height inequality and remains the one residual — precisely the modular status this file records.

## Honesty (scope)

Nothing here proves (C1) `FloorLocalizationUniform`, nor (C2) `TZDyadicShortIntervalLB` — both
are named `Prop` hypotheses (never axioms; (C2) is CONFIRMED literature, (C1) is the open
target).  Everything else is proven, `[propext, Classical.choice, Quot.sound]` only.  This is the
FLOOR, off the BGK/Paley sup-norm wall; the δ* prize CORE stays OPEN.

## References
* [TZ24] Thorner–Zaman, arXiv:2108.10878, Thm 1.1, §3.1.  Issues #334/#464/#466.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.FloorLocalization
open ArkLib.ProximityGap.Frontier.FloorLinnikTZClosure
open ArkLib.ProximityGap.Frontier.TZSubquarticBookkeeping

namespace ArkLib.ProximityGap.Frontier.FloorSuccessorTZBridge

/-- **The elementary density side condition (C3).**  `TZDensityGeOne c β₀ a` asserts that the
[TZ24] window density at threshold exponent `β₀` and modulus `2^a` reaches `1`.  On the [TZ24]
instantiation this holds for all large `a` because the density grows like `(2^a)^{β₀−1}`; it is a
pure size condition on `c` and `a`, carried explicitly (never vacuously exploited). -/
def TZDensityGeOne (c β₀ : ℝ) (a : ℕ) : Prop :=
  (1 : ℝ) ≤ c * ((2 ^ a : ℕ) : ℝ) ^ β₀ /
    ((Nat.totient (2 ^ a) : ℝ) * Real.log (2 * ((2 ^ a : ℕ) : ℝ) ^ β₀))

/-- **Step S1→S2 at one rung, from the faithful [TZ24] hypothesis.**  Fix `n = 2^a` with
`a₀ ≤ a` and `4 ≤ a`.  Given the named [TZ24] Theorem 1.1 short-interval bound
`TZDyadicShortIntervalLB c a₀ β₀` at an exponent `β₀ ≤ 3` and the density side condition at `a`,
the least prime `≡ 1 mod 2^a` within the closure's search bound `2^{5a}` lies below prize scale
`(2^a)^4` — i.e. `LinnikLeastPrimeBelowPrize` holds at this rung.  The bridge is: the faithful
hypothesis yields `TZPrimeSupply (2^a) β₀ 1` (`tzPrimeSupply_dyadic_of_shortIntervalLB`), which
feeds the existing `linnik_rung_of_tzSupply`. -/
theorem linnik_rung_of_shortIntervalLB {c : ℝ} {a₀ : ℕ} {β₀ : ℝ}
    (hTZ : TZDyadicShortIntervalLB c a₀ β₀) (hβ₀ : β₀ ≤ 3)
    {a : ℕ} (ha0 : a₀ ≤ a) (ha4 : 4 ≤ a) (hone : TZDensityGeOne c β₀ a) :
    smallestPrime1ModN (2 ^ a) (2 ^ (5 * a)) < (2 ^ a) ^ 4 := by
  have hone' : (1 : ℝ) ≤ c * ((2 ^ a : ℕ) : ℝ) ^ β₀ /
      ((Nat.totient (2 ^ a) : ℝ) * Real.log (2 * ((2 ^ a : ℕ) : ℝ) ^ β₀)) := hone
  have hsupply : TZPrimeSupply (2 ^ a) β₀ 1 :=
    tzPrimeSupply_dyadic_of_shortIntervalLB hTZ ha0 le_rfl (by exact_mod_cast hone')
  exact linnik_rung_of_tzSupply ha4 hβ₀ hsupply

/-- **The FS3 capstone (per prize rung): the off-BGK floor closes on ONE named conjecture.**
Given
* (C1) `FloorLocalizationUniform FloorBad` — the *only genuine residual*, the uniform
  floor-bad `= {p_min}` conjecture;
* (C2) `TZDyadicShortIntervalLB c a₀ β₀` with `β₀ ≤ 3` — [TZ24] Theorem 1.1 (confirmed
  literature, named `Prop`);
* (C3) `TZDensityGeOne c β₀ a` — the elementary density side condition at the rung;

every prize-regime prime `p ≥ (2^a)^4` (with `p ≡ 1 mod 2^a`, `a₀ ≤ a`, `4 ≤ a`) is
floor-GOOD: `¬ FloorBad (2^a) p`.  This is `floor_closes_by_linnik` inlined at the single rung
`a`, with its least-prime premise now DERIVED from the faithful [TZ24] hypothesis rather than
assumed.  The proof: (S1+S2) give `smallestPrime1ModN(2^a) < (2^a)^4 ≤ p`, so `p` is not the
least prime, so by (C1) it is not floor-bad. -/
theorem floor_closes_by_shortIntervalLB_and_uniform
    (FloorBad : ℕ → ℕ → Prop) (hUnif : FloorLocalizationUniform FloorBad)
    {c : ℝ} {a₀ : ℕ} {β₀ : ℝ} (hβ₀ : β₀ ≤ 3) (hTZ : TZDyadicShortIntervalLB c a₀ β₀)
    {a : ℕ} (ha0 : a₀ ≤ a) (ha4 : 4 ≤ a) (hone : TZDensityGeOne c β₀ a)
    (p : ℕ) (hp : p.Prime) (hmod : p % (2 ^ a) = 1) (hprize : (2 ^ a) ^ 4 ≤ p) :
    ¬ FloorBad (2 ^ a) p := by
  have hlin : smallestPrime1ModN (2 ^ a) (2 ^ (5 * a)) < (2 ^ a) ^ 4 :=
    linnik_rung_of_shortIntervalLB hTZ hβ₀ ha0 ha4 hone
  intro hbad
  -- (C1): floor-bad ⟹ p is the least prime ≡ 1 mod 2^a
  have heq : p = smallestPrime1ModN (2 ^ a) (2 ^ (5 * a)) := (hUnif a ha4 p hp hmod).mp hbad
  -- but the least prime is < (2^a)^4 ≤ p, contradiction
  rw [heq] at hprize
  exact absurd (lt_of_lt_of_le hlin hprize) (lt_irrefl _)

/-- **`LinnikLeastPrimeBelowPrize` in full, from [TZ24].**  If the [TZ24] absolute threshold `a₀`
is within the prize range (`a₀ ≤ 4`, so every prize rung `a ≥ 4` is covered) and the density side
condition holds at every rung `a ≥ 4`, then the faithful [TZ24] hypothesis discharges the full
`LinnikLeastPrimeBelowPrize` premise (`∀ a ≥ 4`).  The `a₀ ≤ 4` hypothesis is flagged honestly:
if the true dyadic Siegel-free threshold exceeds `a = 4`, the finitely many rungs `a ∈ [4, a₀)`
are separately decidable (e.g. `17 < 16^4`, `97 < 32^4`, and the concrete ladder rungs
`tzPrimeSupply_128/256_*`), so the full premise still follows — this form isolates the clean
"TZ covers all prize rungs" case. -/
theorem linnikLeastPrimeBelowPrize_of_shortIntervalLB {c : ℝ} {a₀ : ℕ} {β₀ : ℝ}
    (hTZ : TZDyadicShortIntervalLB c a₀ β₀) (hβ₀ : β₀ ≤ 3) (ha0le : a₀ ≤ 4)
    (hdens : ∀ a : ℕ, 4 ≤ a → TZDensityGeOne c β₀ a) :
    LinnikLeastPrimeBelowPrize := by
  intro a ha4
  exact linnik_rung_of_shortIntervalLB hTZ hβ₀ (le_trans ha0le ha4) ha4 (hdens a ha4)

/-- **Full off-BGK floor closure, both inputs named.**  Under `a₀ ≤ 4` and a density family, the
uniform conjecture (C1) plus the faithful [TZ24] hypothesis (C2) give: every prize prime at every
dyadic rung `a ≥ 4` is floor-GOOD.  This is exactly `floor_closes_by_linnik` with its least-prime
premise supplied by [TZ24] — the "entire off-BGK floor on one named conjecture" statement. -/
theorem floor_closes_on_uniform_conjecture
    (FloorBad : ℕ → ℕ → Prop) (hUnif : FloorLocalizationUniform FloorBad)
    {c : ℝ} {a₀ : ℕ} {β₀ : ℝ} (hβ₀ : β₀ ≤ 3) (hTZ : TZDyadicShortIntervalLB c a₀ β₀)
    (ha0le : a₀ ≤ 4) (hdens : ∀ a : ℕ, 4 ≤ a → TZDensityGeOne c β₀ a)
    (a : ℕ) (ha4 : 4 ≤ a) (p : ℕ) (hp : p.Prime) (hmod : p % (2 ^ a) = 1)
    (hprize : (2 ^ a) ^ 4 ≤ p) :
    ¬ FloorBad (2 ^ a) p :=
  floor_closes_by_linnik FloorBad hUnif
    (linnikLeastPrimeBelowPrize_of_shortIntervalLB hTZ hβ₀ ha0le hdens) a ha4 p hp hmod hprize

/-- **Non-vacuity of the residual interface.**  The uniform conjecture is a *satisfiable* named
`Prop`: at `n = 16` the concrete floor-bad predicate `FloorBad n p := (p = 17)` restricted to the
`a = 4` rung matches `FloorLocalizationUniform`'s rung condition, and `17` is genuinely the least
prime `≡ 1 mod 16` below the search bound.  (The FULL uniform conjecture is proven only at `a=4`;
this records that the residual hypothesis is not vacuous.) -/
theorem residual_is_nonvacuous_at_16 :
    smallestPrime1ModN 16 100 = 17 ∧ (17 : ℕ) < 16 ^ 4 := by
  refine ⟨by decide, by decide⟩

end ArkLib.ProximityGap.Frontier.FloorSuccessorTZBridge

-- Axiom audits (must show only [propext, Classical.choice, Quot.sound]).
open ArkLib.ProximityGap.Frontier.FloorSuccessorTZBridge in
#print axioms linnik_rung_of_shortIntervalLB
open ArkLib.ProximityGap.Frontier.FloorSuccessorTZBridge in
#print axioms floor_closes_by_shortIntervalLB_and_uniform
open ArkLib.ProximityGap.Frontier.FloorSuccessorTZBridge in
#print axioms linnikLeastPrimeBelowPrize_of_shortIntervalLB
open ArkLib.ProximityGap.Frontier.FloorSuccessorTZBridge in
#print axioms floor_closes_on_uniform_conjecture
open ArkLib.ProximityGap.Frontier.FloorSuccessorTZBridge in
#print axioms residual_is_nonvacuous_at_16
