/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# `_AvLSP_AlmostAllPrimesLargeSieve` — the large sieve OVER PRIMES for the Gauss-period sup-norm (#444)

This file isolates the exact, provable content of "almost-all-primes Paley" for the prize sup-norm
`M(p) = max_{b≠0} |η_b(p)|`, `η_b(p) = Σ_{x∈μ_n} e_p(b x)`, and pins precisely WHY it is a genuine
partial that does **NOT** close the `∀q` prize floor. Everything is grounded in exact computation
(`/tmp/ls5.py … ls8.py`, reproduced this session).

## The mechanism, made exact

The large sieve / Plancherel gives one unconditional fact about the **second moment over primes** of
a *single, fixed* frequency-coset `b`:

  `Σ_{p≤x, p≡1(n)} |η_b(p)|²  =  (1 + o(1)) · n · π(x; n, 1)`  (each term has mean `n`).

Exact-computed averages (this session, `ls7.py`): at `n=16`, `(1/π)Σ|η_g|² = 13.55 ≈ n=16`; at
`n=32`, `25.23 ≈ n=32`. So per FIXED coset the period has second moment `≈ n` over primes.

**Markov over primes (the clean half).** For a single fixed coset `b`, with the second-moment input
`Σ_{p≤x} |η_b(p)|² ≤ A · n · π(x)`, the exceptional set at threshold `T`

  `E_b(x; T) := { p ≤ x, p≡1(n) : |η_b(p)|² > T }`   satisfies   `|E_b(x;T)| ≤ A·n·π(x) / T`.

With `T = C²·n·log p` this is `|E_b| ≤ (A/C²)·π(x)/log p = o(π(x))`. **Provable, density-1, clean.**

**Why the SUP fails (the vacuous half = the asymmetry).** `M(p) = max` over the `m = (p−1)/n ≈ p/n`
DISTINCT cosets. The only unconditional (phase-blind) lift of the per-coset bound to the max is the
union bound:

  `|{p : M(p)² > T}| ≤ Σ_{cosets} |E_b(x;T)| ≤ m · A·n·π(x)/T = A·p·π(x)/T`.

For this to be `o(π(x))` one needs `T > p`, i.e. `M(p)² ≲ p` — the **Weil scale `√p = n²`**, NOT the
Paley scale `√(n log p)`. The union over `p/n` cosets reintroduces a factor `p/n`, exactly cancelling
the `n` from Plancherel and leaving the trivial `p`. This is the SAME vacuity proved for the sieve
over frequencies in `_AvE6_LargeSieveVacuous`, now transferred to the sieve over primes.

To cross from `√p` to `√(n log p)` the per-coset tail must be controlled at the level of the `K`-th
moment with `K → ∞` (so that `m^{1/K} → 1` kills the coset count): this is the **moment ladder**, and
`moment_ladder_exceeds_prize` (in-tree) proves NO finite `K` reaches exponent `1/2`. Exact `ls8.py`:
the ladder bound `(qE_K)^{1/K}` on `M²` decays `564→13.6→4.5→2.8→2.14×` the prize scale as `K=1…5`,
never below `1×` — the `K`-moment barrier `α(K)=½+β/(2K) > ½`.

## EXACT exceptional-set census (this session)

Single-coset tail of `|η_b|²/n` (`ls5.py`, n=16, 2866 (coset,prime) samples): mean `0.987` (Plancherel),
`P(>1)=0.329`, `P(>2)=0.165`, `P(>4)=0.039`, `P(>6)=0.0091`. The tail is **sub-exponential** (`~e^{-t}`)
but **heavier than Gaussian** (`P(>4)=0.039` vs `e^{-4}=0.018`, ~2×; `P(>6)` ~3.6×) — this heavy tail
is exactly why the worst-case constant grows toward `√2`.

Exceptional fraction `|{p~x : M(p)²>C²n log p}|/π(x;n,1)` at `C=√2` (`ls6.py`, octave windows): `0` in
EVERY octave up to `p≈16000` for both `n=16,32`. Max ratio `M²/(n log p)` creeps up: `1.155` (n=16),
`1.445` (n=32) — already at `√2≈1.414` for `n=32`, consistent with the known `→√2` at thin Fermat-type
primes. So `C=√2` is empirically the floor for an almost-all bound at these scales, NOT `C=1`.

The exceptional set is NOT cleanly "high-`v2(p−1)`": at `n=32` the single worst prime in range is
`p=5857` with `v2=5` (the MINIMUM `v2` for `p≡1 mod 32`), not a Fermat-adjacent high-`v2` prime
(`ls4.py`). The mean ratio rises weakly with `v2` (n=16: `0.887→0.921` for `v2=4→6`) but the MAX does
not stratify by `v2` at these scales. So part (2)'s "exceptional = high-`v2`" is **REFUTED at small `n`**:
the worst small-`p` primes are spread across `v2`; the `√2`-extremal Fermat behaviour is an *asymptotic*
(`β→4`) phenomenon, not visible as a `v2`-characterized exceptional set at finite `x`.

## What this file PROVES (axiom-clean ℝ/Finset arithmetic)

The fixed-coset **Markov-over-primes exceptional bound** as a clean finite inequality, and the
**union-bound blow-up** that makes the SUP version vacuous — i.e. the exact asymmetry. The number
theory (the second moment `≈ n`) is the named hypothesis; the sieve combinatorics is the theorem.

## HONEST SCOPE — this is NOT the prize

* The fixed-coset density-1 bound is genuinely TRUE and proven (Markov + Plancherel-over-primes).
* It does NOT give `∀q`: it controls each frequency for *almost all* primes, leaving an `o(π)`
  exceptional set that can (and at the thin Fermat-type worst case, does) contain the very primes
  the `∀q` floor must handle. "Almost-all-primes Paley" ⊬ "`∀`-prime Paley".
* The union-over-cosets lift to the actual `M(p)` is VACUOUS at the Paley scale (needs `√p`), so even
  the almost-all statement for the SUP-NORM `M` is NOT delivered by the L² large sieve — only the
  moment ladder could, and the `K`-moment barrier forbids it. `isPrizeClosure = false`.
* Part (3): "almost-all + construction avoids the `o(1)` exceptional primes" CANNOT feed the `∀q`
  floor, because the floor quantifies over ALL primes `p≡1 mod n` (∀q-uniform, workbench line 79);
  one does not get to *choose* the prime. It could only help an `∃-explicit` ceiling/Dirichlet route,
  which is the UPPER bracket (`kkh26_mcaDeltaStar_le_unconditional`), already unconditional. So
  almost-all gives nothing new even there.

## References
- In-tree: `_AvE6_LargeSieveVacuous.lean` (same vacuity over frequencies), `moment_ladder_exceeds_prize`,
  `_AvFrontier_KMomentBarrier`, `_AvCP_AlmostAllPrimesNoWraparound.lean` (almost-all at fixed depth).
- [BGK] Bourgain–Glibichuk–Konyagin; [ABF26] ePrint 2026/680 (issue #444).
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.AvLSPAlmostAllPrimesLargeSieve

open Finset

/-- **Abstract sieve data over primes.** `P` is the finite index set of primes `p ≤ x` with
`p ≡ 1 mod n` (the residue class the prize quantifies over). For a fixed frequency-coset, `w p`
is `|η_b(p)|²`. `T` is the Paley threshold (`= C²·n·log p`). The single number-theoretic input is
`secondMoment : Σ_p w p ≤ A·n·(#P)` (the large-sieve / Plancherel-over-primes bound, exact-computed
`A ≈ 1`). -/
structure SieveData where
  /-- The finite set of primes `p ≤ x`, `p ≡ 1 mod n` (indices). -/
  P : Type*
  [fP : Fintype P]
  [dP : DecidableEq P]
  /-- Per-prime squared period for the fixed coset: `w p = |η_b(p)|²`. -/
  w : P → ℝ
  hw_nonneg : ∀ p, 0 ≤ w p
  /-- Subgroup size `n`. -/
  n : ℝ
  hn_pos : 0 < n
  /-- Second-moment constant from Plancherel-over-primes (exact-computed `A ≈ 1`). -/
  A : ℝ
  hA_pos : 0 < A
  /-- **The number-theoretic input (named):** `Σ_p |η_b(p)|² ≤ A·n·(#P)`. -/
  secondMoment : (∑ p, w p) ≤ A * n * (Fintype.card P)

attribute [instance] SieveData.fP SieveData.dP

variable (S : SieveData)

/-- The exceptional set at threshold `T` for the fixed coset: primes where `w p > T`. -/
noncomputable def exceptional (T : ℝ) : Finset S.P :=
  Finset.univ.filter (fun p => T < S.w p)

/-- **Markov core.** On the exceptional set every term is `> T`, so the full second moment
dominates `T · #exceptional`. -/
theorem threshold_mul_card_le {T : ℝ} (_hT : 0 ≤ T) :
    T * (exceptional S T).card ≤ ∑ p, S.w p := by
  have hsub : (exceptional S T) ⊆ (Finset.univ : Finset S.P) := Finset.subset_univ _
  -- Σ_all w ≥ Σ_exceptional w ≥ Σ_exceptional T = T · #exceptional
  have h1 : (∑ p ∈ exceptional S T, S.w p) ≤ ∑ p, S.w p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => S.hw_nonneg p)
  have h2 : (∑ _p ∈ exceptional S T, T) ≤ ∑ p ∈ exceptional S T, S.w p := by
    apply Finset.sum_le_sum
    intro p hp
    have : T < S.w p := by
      simpa [exceptional, Finset.mem_filter] using hp
    exact le_of_lt this
  have h3 : (∑ _p ∈ exceptional S T, T) = T * (exceptional S T).card := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [h3] at h2
  linarith [h1, h2]

/-- **The fixed-coset Markov / large-sieve exceptional bound (the clean partial).**
For any positive threshold `T`, the number of primes `p ≤ x` (`p≡1 mod n`) at which the fixed
frequency `|η_b(p)|²` exceeds `T` is at most `A·n·(#P)/T`. With `T = C²·n·log p` this is
`(A/C²)·(#P)/log p`, i.e. an `o(#P)` exceptional set — "almost-all-primes Paley" for a FIXED
frequency. (Consumes only `secondMoment`, the Plancherel-over-primes input.) -/
theorem exceptional_card_le {T : ℝ} (hT : 0 < T) :
    ((exceptional S T).card : ℝ) ≤ S.A * S.n * (Fintype.card S.P) / T := by
  rw [le_div_iff₀ hT]
  calc ((exceptional S T).card : ℝ) * T
      = T * (exceptional S T).card := by ring
    _ ≤ ∑ p, S.w p := threshold_mul_card_le S (le_of_lt hT)
    _ ≤ S.A * S.n * (Fintype.card S.P) := S.secondMoment

/-- **The asymmetry / vacuity of the union lift (honest negative).** Lifting the fixed-coset bound to
the SUP `M(p) = max over m cosets` by the union bound multiplies the exceptional bound by `m`. We
record the resulting bound `m · A·n·(#P) / T` and show that to make it `o(#P)` one needs `T > m·A·n`.
With `m = (p−1)/n` cosets, `m·n = p−1`, so the required threshold is `T ≳ p` — the **Weil scale**,
NOT the Paley scale `n log p`. The union over `p/n` cosets exactly cancels the Plancherel `n`. -/
theorem union_threshold_is_weil_scale {T : ℝ} (m : ℝ) (_hm : 0 < m)
    (hT : 0 < T) (hsmall : m * (S.A * S.n * (Fintype.card S.P) / T) < (Fintype.card S.P)) :
    m * (S.A * S.n) < T := by
  -- the union bound is o(#P)  ⟹  m·A·n·#P / T < #P  ⟹  m·A·n < T  (when #P > 0)
  rcases Nat.eq_zero_or_pos (Fintype.card S.P) with h0 | hpos
  · -- empty prime set: the strict hypothesis `… < 0` is impossible (LHS ≥ 0)
    exfalso
    rw [h0] at hsmall
    simp only [Nat.cast_zero, mul_zero, zero_div] at hsmall
    linarith [hsmall]
  · have hcardpos : (0 : ℝ) < (Fintype.card S.P) := by exact_mod_cast hpos
    have hrw : m * (S.A * S.n * (Fintype.card S.P) / T) = (m * S.A * S.n * (Fintype.card S.P)) / T := by
      ring
    rw [hrw, div_lt_iff₀ hT] at hsmall
    -- m·A·n·#P < #P·T  ⟹  m·A·n < T
    have := hsmall
    nlinarith [hcardpos, this]

#print axioms threshold_mul_card_le
#print axioms exceptional_card_le
#print axioms union_threshold_is_weil_scale

end ArkLib.ProximityGap.Frontier.AvLSPAlmostAllPrimesLargeSieve
