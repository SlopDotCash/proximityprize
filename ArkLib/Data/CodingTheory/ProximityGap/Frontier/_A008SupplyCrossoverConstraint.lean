/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A008 — the supply-vs-badcount CROSSOVER, and why the binding rung overflows it (#444)

The maintainer's untried-non-wall census (#444, 2026-06-17) flags **A008** — the *probabilistic
method over qualifying primes*: use ONLY the proven unconditional bad-prime UPPER bound
(`KKH26.card_biUnion_bigPrimeFactors_le`) against the unconditional Thorner–Zaman supply to show a
random qualifying prime is good w.h.p., **avoiding** the Thorner–Zaman supply LOWER bound.  The
census's honest funnel verdict: *"needs the supply lower bound to dominate, which it can't
unconditionally → still the analytic wall."*  That verdict was stated in prose; this file makes it
an **exact, machine-checked constraint lemma** (rule 4 — a refutation with its constraint lemma),
pinning the EXACT crossover and proving the binding rung lands on the wrong side of it.

## The exact crossover (the honest replacement for the prose funnel)

The KKH26 good-prime hypothesis (`kkh26_good_prime_paper_form`'s `hcount`) is, in the thin 2-power
tower (`s = 2^μ`, prize `n = s`, `log n = log s`), with the in-tree resultant bound
`|Res| ≤ s^{s/2}` so `logM = (s/2)·log s`:

  `badcount  =  a² · logM / (β · log n)  =  a² · (s/2) · log s / (β · log s)  =  a² · s / (2β)`,

and the unconditional Thorner–Zaman supply is `n^{β−1} = s^{β−1}`.  So the good-prime certificate
fires **iff a single CONDITION ON `a`** (the count of signed sum-polynomials) holds:

  `badcount < supply  ⟺  a² · s / (2β) < s^{β−1}  ⟺  a² < 2β · s^{β−2}`.

The threshold `a*² = 2β·s^{β−2}` is **polynomial** in `s`.  (Probe
`scripts/probes/probe_a008_supply_crossover.py`: the crossover equivalence is exact across the prize
tower, β ∈ {2.5, 4, 5.27}; PASS.)

## Why the binding rung overflows the threshold (the refutation mechanism)

At the binding rung `ρ = 1/4` the signed-data count is `a = 2^r · C(s/2, r)` with `r = s/4`
(`kkh26_good_prime_paper_form`'s `a` field).  Hence `a ≥ 2^r = 2^{s/4}`, so `a² ≥ 4^{s/4} = 2^{s/2}`,
which is **exponential** in `s`, while the threshold `2β·s^{β−2}` is **polynomial**.  So for the
probabilistic certificate to fire at the binder, the threshold would have to *exceed the exponential
binder count*: `2^{s/2} ≤ a² < 2β·s^{β−2}` — impossible for all large `s`.  The method is killed by
the **exponential collision-pair count at the binding rung**, NOT by the supply being too thin — so
it cannot avoid a finer supply LOWER bound.  (Probe: `a²/threshold → ∞`, e.g. `≈ 10^{4.8e8}` at
`μ = 30`, β = 4; and the concrete `s = 64`, β = 4 witness `2^{32} > 8·64²` below.)

## What this file lands (axiom-clean, honest)

* `a008_crossover_iff` / `a008_crossover_clean` — the EXACT crossover as a clean real inequality:
  with `badcount` and `supply` the in-tree quantities, `badcount < supply ⟺ a² < 2β·s^{β−2}`.  The
  honest, provable form of the funnel.
* `a008_subthreshold_fires` — the POSITIVE half: `a² < 2β·s^{β−2}` is exactly the (cleaned) `hcount`
  hypothesis of `kkh26_good_prime_paper_form`, so a sub-threshold (polynomial) `a` yields a good
  prime unconditionally.  The probabilistic method DOES close below threshold.
* `binder_a_ge_two_pow` / `binder_a_sq_ge_two_pow` — the binding-rung lower bound `2^{2r} ≤ a²` from
  `a = 2^r · C(s/2, r)`.
* `a008_binder_forces_threshold_above_exp` — **THE CONSTRAINT LEMMA (forcing form)**: at the binder,
  if the cleaned `hcount` holds then the (real) threshold must exceed the exponential binder count:
  `(2 : ℝ)^{2r} < 2β·s^{β−2}`.  So the probabilistic certificate at the binder REQUIRES a polynomial
  threshold to dominate an exponential — the precise obstruction.
* `a008_binder_overflow_witness` — a concrete `Nat` refutation witness at `s = 64`, `r = s/4 = 16`,
  β = 4 (threshold `2β·s^{β−2} = 8·64² = 32768`): the binder `a² ≥ 2^{32} = 4294967296 > 32768`, so
  `hcount` FAILS at this tower level — the threshold is overflowed by `≈ 131072×` already at `s = 64`.

## Honest scope

NOT a CORE closure and NOT a δ* pin.  This is a CONSTRAINT lemma (rule 4): it converts A008's prose
funnel into the EXACT polynomial crossover threshold `a² < 2β·s^{β−2}` and proves the binding-rung
`a = 2^{s/4}·C(s/2, s/4)` overflows it exponentially (forcing form + concrete witness).  It makes NO
capacity / beyond-Johnson / sub-linear claim; the ASYMPTOTIC-GUARD cliff-at-n/2 is untouched; CORE
`M(μ_n) ≤ C√(n·log(p/n))` stays OPEN.  Char-sum-free, char-agnostic (the count is p-independent); the
thinness enters only through the tower `s = 2^μ` and the binding rung `r = s/4`.

## References
- `KKH26ThornerZaman.lean` — `kkh26_good_prime_paper_form` (the conditional good-prime existence)
  and `card_biUnion_bigPrimeFactors_le` (the unconditional bad-prime upper bound).
-/

set_option linter.style.longLine false
set_option autoImplicit false

namespace ArkLib.ProximityGap.A008SupplyCrossover

open Real

/-! ## Part 1 — the EXACT crossover threshold (real inequality) -/

/-- **The exact A008 crossover (cleaned).**  In the thin tower `log n = log s` and the in-tree
`logM = (s/2)·log s`, the KKH26 bad-prime budget `badcount = a²·logM/(β·log s)` is strictly below the
Thorner–Zaman supply `supply = s^{β−1}` **iff** `a² < 2β·s^{β−2}`.  Stated on the cleaned quantities
`a² · s / (2β)` and `s^{β−1}` (the `logM`/`log s` cancellation done on paper), so the content is the
pure polynomial comparison.  `s > 0`, `β > 0`. -/
theorem a008_crossover_iff (a s : ℕ) (β : ℝ) (hs : 0 < s) (hβ : 0 < β) :
    ((a : ℝ) ^ 2 * s / (2 * β) < (s : ℝ) ^ (β - 1))
      ↔ ((a : ℝ) ^ 2 < 2 * β * (s : ℝ) ^ (β - 2)) := by
  have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have h2β : (0 : ℝ) < 2 * β := by positivity
  -- s^{β-1} = s^{β-2} * s
  have hsplit : (s : ℝ) ^ (β - 1) = (s : ℝ) ^ (β - 2) * (s : ℝ) := by
    rw [show (β - 1) = (β - 2) + 1 by ring, Real.rpow_add hs0, Real.rpow_one]
  rw [hsplit, div_lt_iff₀ h2β]
  constructor
  · intro h
    -- a^2 * s < (s^{β-2} * s) * (2β)  ⟹  a^2 < 2β * s^{β-2}   (cancel s>0)
    have hcancel : (a : ℝ) ^ 2 * s < (2 * β * (s : ℝ) ^ (β - 2)) * s := by nlinarith [h]
    exact lt_of_mul_lt_mul_right hcancel (le_of_lt hs0)
  · intro h
    nlinarith [h, hs0]

/-- **The crossover threshold IS the KKH26 `hcount` (paper form), cleaned.**  Restates the threshold
`a² < 2β·s^{β−2}` as the exact inequality `a²·(s/2)·log s/(β·log s) < s^{β−1}` that appears (after the
`(2^{μ−1})·μ·log 2 = (s/2)·log s` identification and `log n = log s`) inside
`kkh26_good_prime_paper_form`'s `hcount`. -/
theorem a008_crossover_clean (a s : ℕ) (β : ℝ) (hs : 1 < s) (hβ : 0 < β) :
    ((a : ℝ) ^ 2 * ((s : ℝ) / 2 * Real.log s) / (β * Real.log s) < (s : ℝ) ^ (β - 1))
      ↔ ((a : ℝ) ^ 2 < 2 * β * (s : ℝ) ^ (β - 2)) := by
  have hs1 : (1 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hlog : 0 < Real.log s := Real.log_pos hs1
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  have hlogne : Real.log s ≠ 0 := ne_of_gt hlog
  have hsimp : (a : ℝ) ^ 2 * ((s : ℝ) / 2 * Real.log s) / (β * Real.log s)
      = (a : ℝ) ^ 2 * s / (2 * β) := by
    have hL : Real.log s ≠ 0 := hlogne
    field_simp
  rw [hsimp]
  exact a008_crossover_iff a s β (by omega) hβ

/-! ## Part 2 — the POSITIVE half: sub-threshold ⟹ probabilistic method fires -/

/-- **Sub-threshold `a` ⟹ the good-prime certificate fires (unconditionally).**  If
`a² < 2β·s^{β−2}` (equivalently `badcount < supply`), then the cleaned KKH26 hypothesis holds, so the
probabilistic method DOES close the good-prime certificate without a finer supply lower bound — the
honest POSITIVE content of A008, valid exactly when `a` is polynomially bounded below the threshold.
The cleaned inequality this delivers is exactly `kkh26_good_prime_paper_form`'s `hcount` (modulo the
`(2^{μ−1})·μ·log 2 = (s/2)·log s` and `log n = log s` identifications). -/
theorem a008_subthreshold_fires (a s : ℕ) (β : ℝ) (hs : 1 < s) (hβ : 0 < β)
    (hsub : (a : ℝ) ^ 2 < 2 * β * (s : ℝ) ^ (β - 2)) :
    (a : ℝ) ^ 2 * ((s : ℝ) / 2 * Real.log s) / (β * Real.log s) < (s : ℝ) ^ (β - 1) :=
  (a008_crossover_clean a s β hs hβ).mpr hsub

/-! ## Part 3 — the binding rung overflows the threshold (the refutation) -/

/-- **The binding-rung signed-data count is `≥ 2^r`.**  With `a = 2^r · C(s2, r)` and `r ≤ s2`
(so `C(s2, r) ≥ 1`), we have `2^r ≤ a`.  Pure `Nat`. -/
theorem binder_a_ge_two_pow (s2 r : ℕ) (hr : r ≤ s2) :
    2 ^ r ≤ 2 ^ r * Nat.choose s2 r := by
  have hch : 1 ≤ Nat.choose s2 r := Nat.choose_pos hr
  calc 2 ^ r = 2 ^ r * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ r * Nat.choose s2 r := Nat.mul_le_mul_left _ hch

/-- **`a² ≥ 2^{2r}` at the binder.**  Square `binder_a_ge_two_pow`. -/
theorem binder_a_sq_ge_two_pow (s2 r : ℕ) (hr : r ≤ s2) :
    2 ^ (2 * r) ≤ (2 ^ r * Nat.choose s2 r) ^ 2 := by
  have h := binder_a_ge_two_pow s2 r hr
  calc 2 ^ (2 * r) = (2 ^ r) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ (2 ^ r * Nat.choose s2 r) ^ 2 := Nat.pow_le_pow_left h 2

/-- **THE CONSTRAINT LEMMA (forcing form).**  At the binder `a = 2^r · C(s2, r)` (`r ≤ s2`), if the
cleaned `hcount` (`badcount < supply`, equiv. `a² < 2β·s^{β−2}`) holds, then the polynomial threshold
must EXCEED the exponential binder count: `(2 : ℝ)^{2r} < 2β·s^{β−2}`.  So the probabilistic
certificate at the binder REQUIRES a polynomial threshold to dominate an exponential — the precise
obstruction the census funnel names.  (`s > 0`.) -/
theorem a008_binder_forces_threshold_above_exp (s s2 r : ℕ) (β : ℝ) (hr : r ≤ s2)
    (hhcount : (((2 ^ r * Nat.choose s2 r : ℕ) : ℝ)) ^ 2 < 2 * β * (s : ℝ) ^ (β - 2)) :
    ((2 : ℝ)) ^ (2 * r) < 2 * β * (s : ℝ) ^ (β - 2) := by
  have hbind : (2 : ℕ) ^ (2 * r) ≤ (2 ^ r * Nat.choose s2 r) ^ 2 := binder_a_sq_ge_two_pow s2 r hr
  have hbindR : ((2 : ℝ)) ^ (2 * r) ≤ (((2 ^ r * Nat.choose s2 r : ℕ) : ℝ)) ^ 2 := by
    have hcast : (((2 ^ r * Nat.choose s2 r : ℕ) : ℝ)) ^ 2
        = (((2 ^ r * Nat.choose s2 r) ^ 2 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]
    have : (((2 : ℕ) ^ (2 * r) : ℕ) : ℝ) ≤ (((2 ^ r * Nat.choose s2 r) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hbind
    simpa using this
  exact lt_of_le_of_lt hbindR hhcount

/-- **Concrete `Nat` refutation witness at `s = 64`, β = 4.**  The binder rung `r = s/4 = 16`,
`s2 = s/2 = 32`, threshold `2β·s^{β−2} = 8·64² = 32768`.  The binder count `a² ≥ 2^{2·16} = 2^{32} =
4294967296 > 32768`, so the cleaned `hcount` (`a² < 32768`) FAILS already at `s = 64`: the exponential
binder count overflows the polynomial threshold by a factor `≈ 131072` at this single tower level.
This certifies (decidably, no analytic input) that A008's probabilistic certificate does NOT fire at
the binder — the funnel verdict, witnessed. -/
theorem a008_binder_overflow_witness :
    (32768 : ℕ) < 2 ^ (2 * 16) ∧ (2 : ℕ) ^ (2 * 16) ≤ (2 ^ 16 * Nat.choose 32 16) ^ 2 := by
  refine ⟨by decide, binder_a_sq_ge_two_pow 32 16 (by norm_num)⟩

/-! ## Part 4 — non-vacuity -/

/-- **Non-vacuity (the crossover fires below threshold).**  At `s = 16`, β = 4 the threshold is
`2β·s^{β−2} = 8·256 = 2048`; a polynomial `a = 4` (so `a² = 16 < 2048`) is sub-threshold, so
`a008_subthreshold_fires` delivers the cleaned `hcount` — the positive half is non-vacuous. -/
example : ((4 : ℕ) : ℝ) ^ 2 < 2 * (4 : ℝ) * ((16 : ℕ) : ℝ) ^ ((4 : ℝ) - 2) := by
  have hr : ((16 : ℕ) : ℝ) ^ ((4 : ℝ) - 2) = 256 := by
    rw [show (4 : ℝ) - 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [hr]; norm_num

/-- **Non-vacuity (the binder forcing fires).**  At `s2 = 32`, `r = 16` the binder lower bound
`2^{32} ≤ a²` holds, the input to the forcing lemma `a008_binder_forces_threshold_above_exp`. -/
example : (2 : ℕ) ^ (2 * 16) ≤ (2 ^ 16 * Nat.choose 32 16) ^ 2 :=
  binder_a_sq_ge_two_pow 32 16 (by norm_num)

end ArkLib.ProximityGap.A008SupplyCrossover

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only — no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.A008SupplyCrossover.a008_crossover_iff
#print axioms ArkLib.ProximityGap.A008SupplyCrossover.a008_crossover_clean
#print axioms ArkLib.ProximityGap.A008SupplyCrossover.a008_subthreshold_fires
#print axioms ArkLib.ProximityGap.A008SupplyCrossover.binder_a_ge_two_pow
#print axioms ArkLib.ProximityGap.A008SupplyCrossover.binder_a_sq_ge_two_pow
#print axioms ArkLib.ProximityGap.A008SupplyCrossover.a008_binder_forces_threshold_above_exp
#print axioms ArkLib.ProximityGap.A008SupplyCrossover.a008_binder_overflow_witness
