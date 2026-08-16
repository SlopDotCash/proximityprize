/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (target F7 — the combinatorial half of the good-prime Linnik residual,
  framed on the complete-homogeneous forced-bad-scalar values `γ_R = −h_{a−k}(R)/h_{b−k}(R)`)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SpecS3_GaloisReduction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors

/-!
# Spec F7 — the COMBINATORIAL half of the good-prime collision count (#444)

⚠️ **STATUS — SUBSTRATE / frontier-isolation, NOT a δ\* pin.** This file lands the **combinatorial
half** of the good-prime Linnik residual (the `F4` companion), framed directly on the
complete-homogeneous *forced bad-scalar* values rather than on the KKH26 collision resultant
(`_BchksF4_GoodPrimeLinnik` covers the resultant route). The two faces of the **forced bad scalar**
of a node set `R ⊆ μ_s` are

  `γ_R = − h_{a−k}(R) / h_{b−k}(R)`,   where `h_r(R) = schurH …` is the complete-homogeneous value

(`SchurLagrangeBridge.schurH`, the `dividedDifferencePow` surrogate). The δ\* floor needs a prime
`p` at which the char-`0`-**distinct** `h_r(R)` values stay distinct mod `p` — only then does the
char-`0` count of distinct bad scalars survive the reduction `ℤ[ζ_s] → 𝔽_p`. This brick isolates
exactly that combinatorial content; it is **NOT** a δ\* pin (the complete-homogeneous *spectrum*
route is REFUTED as a δ\* pin — `#distinct h_r` is exponential while the actual bad count at δ\* is
`~n`; see `docs/kb/deltastar-444-BCHKS-correct-object-and-attack-2026-06-16.md` §D4 and
`_SpecS3_GaloisReduction`). The content here is *finiteness of the bad-prime obstruction* — landable
— while *quantitative existence at the prize field scale* `p = Θ(n^β)` is the named analytic
residual (the BGK / good–bad-prime crossover boundary).

## What is LANDED (axiom-clean)

* **(A) reduction-compatibility of the complete-homogeneous value.** `schurH_reduce` (and
  `dividedDifferencePow_reduce`): for any ring/field hom `σ : F →+* K` (e.g. the reduction `mod p`),
  `σ (h_r(R)) = h_r(σ(R))`. Derived as a **clean corollary of the committed S3 crown jewel**
  `SpecS3.dividedDifferencePow_map` (hypothesis-free) and `SpecS3.schurH_map`. This is the precise
  statement that the char-`0` `h_r` values **reduce compatibly mod `p`**.

* **(B) collision ⟹ divisibility, finite bad set.** Working in the abstract `ℕ` norm model — a
  char-`0`-distinct value pair is represented by a *nonzero* norm `N : ℕ` of the algebraic-integer
  difference `Δ` — the bad primes (those at which the pair collides) are exactly `N.primeFactors`,
  with the `p`-independent ceilings `p ∣ N ∧ N ≠ 0 → p ≤ N` (`badPrimeOfPair` finiteness) and the
  divisor count `(N.primeFactors).card ≤ Nat.log 2 N`. The union over the finitely many pairs of a
  finite family stays finite via `Finset.biUnion` (`pairBadPrimes`, `pairBadPrimes_card_le`).

* **(C) the named analytic residual.** `EffectiveGoodPrimeExists badset lo hi : Prop` — the
  existence of a prime of size `Θ(n^β)` (range `[lo,hi]`) avoiding the finite bad set. It is left
  **genuinely open** (it reduces to effective Linnik / Lagarias–Odlyzko PNT-in-AP — see the
  docstring; NOT proven). The honest reduction `goodPrime_preserves_distinct_of_effective` states:
  GIVEN `EffectiveGoodPrimeExists`, a good prime exists past the bad set. The Prop has **real
  content** (not vacuously true): `effectiveGoodPrimeExists_nonvacuous` is a concrete badset where a
  good prime exists, and `effectiveGoodPrimeExists_can_fail` is a too-small range where it FAILS.

## Honest scope

SUBSTRATE for the good-prime Linnik residual, schurH-framed. The combinatorial finiteness is
LANDED; the quantitative existence at polynomial field size is the named analytic residual =
the BGK / good–bad-prime boundary. This is **NOT** a δ\* pin and does **NOT** close the prize.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
- [Kambiré] arXiv 2604.09724 (the sumset ceiling; bad primes divide the collision resultant /
  norm of the difference of char-`0`-distinct complete-homogeneous values).
- Lagarias, Odlyzko. *Effective versions of the Chebotarev density theorem*. 1977.
- Thorner, Zaman, *A unified and improved Chebotarev density theorem* (effective PNT-in-AP).
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset

namespace ArkLib.ProximityGap.Frontier.SpecF7GoodPrimeCollisionCount

open ProximityGap.SchurLagrange
open ArkLib.ProximityGap.SpecS3

/-! ## Part A — reduction-compatibility of the complete-homogeneous value `h_r`

The forced bad scalar of a node set `R` is `γ_R = − h_{a−k}(R)/h_{b−k}(R)`; its numerator and
denominator are complete-homogeneous values `h_r(R) = schurH …`. To pull a char-`0`
distinctness statement of these values down to char-`p`, we need that the value map commutes with
the reduction hom `σ : ℤ[ζ_s] → 𝔽_p` (equivalently any field hom). This is a direct corollary of
the committed S3 crown jewel `SpecS3.dividedDifferencePow_map` (and `SpecS3.schurH_map`). -/

section Reduction

variable {F K : Type*} [Field F] [Field K] {ι : Type*} [DecidableEq ι]

/-- **(A.0) reduction-compatibility of the divided-difference value (hypothesis-free).**
For ANY field hom `σ : F →+* K` — the reduction `mod p` is one — the divided-difference value
`dividedDifferencePow s v b` reduces compatibly:

  `σ (dividedDifferencePow s v b) = dividedDifferencePow s (σ ∘ v) b`.

This is *verbatim* the committed S3 crown jewel `SpecS3.dividedDifferencePow_map`, re-exported here
under the reduction-mod-`p` reading. It is char-agnostic and total (no hypotheses on `s`, `v`, `b`),
so it is exactly the tool that pulls a char-`0` value statement down to char-`p`. -/
theorem dividedDifferencePow_reduce (σ : F →+* K) (s : Finset ι) (v : ι → F) (b : ℕ) :
    σ (dividedDifferencePow s v b) = dividedDifferencePow s (fun i => σ (v i)) b :=
  SpecS3.dividedDifferencePow_map σ s v b

/-- **(A) reduction-compatibility of the complete-homogeneous value `h_r` — `schurH_reduce`.**
For an INJECTIVE field hom `σ : F →+* K` (the reduction `ℤ[ζ_s] → 𝔽_p` is injective on the relevant
node set when `p` carries `μ_s`, keeping the node set genuine on both sides), a nonempty node set
`s` with values injective on `s`,

  `σ (h_r(R)) = h_r(σ(R))`   — explicitly `σ (schurH s v b) = schurH s (σ ∘ v) b`.

Since `γ_R = − h_{a−k}(R)/h_{b−k}(R)`, this is the statement that **the numerator and denominator of
the forced bad scalar reduce compatibly mod `p`**: a char-`0`-distinct pair of `h_r` values reduces
to the corresponding pair over `𝔽_p`, so it collides mod `p` iff `σ` identifies them. Derived as a
clean corollary of the committed `SpecS3.schurH_map`. -/
theorem schurH_reduce (σ : F →+* K) (hσ : Function.Injective σ)
    {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s) (hs : s.Nonempty) (b : ℕ) :
    σ (schurH s v b) = schurH s (fun i => σ (v i)) b :=
  SpecS3.schurH_map σ hσ hvs hs b

/-- **(A′) the forced-bad-scalar `γ_R` itself reduces compatibly.** With `γ_R = − h_{a}(R)/h_{b}(R)`
(here `a = numerator degree`, `b = denominator degree`), the reduction hom `σ` carries `γ_R` to the
`γ` of the reduced node set `σ(R)`, PROVIDED the denominator does not vanish under `σ` (else both
sides collapse to the junk value `0⁻¹ = 0`, which `σ` still preserves by `map_inv₀`). We state the
clean non-degenerate form: if `σ (h_b(R)) ≠ 0`, then

  `σ (− h_a(R) / h_b(R)) = − h_a(σ R) / h_b(σ R)`.

This is the full reduction-compatibility of the forced bad scalar, assembled from `schurH_reduce`
on numerator and denominator. -/
theorem gamma_reduce (σ : F →+* K) (hσ : Function.Injective σ)
    {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s) (hs : s.Nonempty) (a b : ℕ) :
    σ (- schurH s v a / schurH s v b)
      = - schurH s (fun i => σ (v i)) a / schurH s (fun i => σ (v i)) b := by
  rw [map_div₀, map_neg, schurH_reduce σ hσ hvs hs a, schurH_reduce σ hσ hvs hs b]

end Reduction

/-! ## Part B — collision ⟹ divisibility; the finite bad-prime set (abstract `ℕ` norm model)

A pair of char-`0`-**distinct** complete-homogeneous values `(h_r(R₁), h_r(R₂))` has a nonzero
algebraic-integer difference `Δ = h_r(R₁) − h_r(R₂) ∈ ℤ[ζ_s]`; the primes at which the pair
*collides* mod `p` are exactly the primes `p` with `p ∣ N`, `N = |Norm(Δ)| ≠ 0` the absolute field
norm. We model this abstractly: a distinct pair is carried by a *nonzero* norm `N : ℕ`, its bad
primes are `N.primeFactors`, and the union over the finite family of pairs is finite. The landable
content is exactly this **finiteness** (plus a `p`-independent ceiling); nothing here is char-`p`. -/

section NormModel

/-- **(B.0) a positive integer has at most `log₂ N` distinct prime factors.** Each distinct prime
factor is `≥ 2`, so `2 ^ (#primeFactors) ≤ ∏ primeFactors ≤ N`; take `log₂`. This is the
per-pair exclusion: a fixed nonzero norm `N` rules out at most `Nat.log 2 N` primes. -/
theorem card_primeFactors_le_natLog {N : ℕ} (hN : 1 ≤ N) :
    N.primeFactors.card ≤ Nat.log 2 N := by
  classical
  have hpow : 2 ^ N.primeFactors.card ≤ N := by
    calc 2 ^ N.primeFactors.card
        = ∏ _p ∈ N.primeFactors, 2 := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ N.primeFactors, p :=
          Finset.prod_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ N := Nat.le_of_dvd hN (Nat.prod_primeFactors_dvd N)
  exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr hpow

/-- **(B.1) the bad-prime set of a single distinct pair, abstract norm model.** A pair of
char-`0`-distinct complete-homogeneous values is carried by a nonzero norm `N`; the primes at which
the pair collides are exactly the prime factors of `N`. -/
def badPrimeOfPair (N : ℕ) : Finset ℕ := N.primeFactors

/-- **collision ⟹ divisibility.** `p` is a bad prime of the pair carried by `N` iff `p` is a prime
and `p ∣ N` (and `N ≠ 0`); i.e. the *only* way two char-`0`-distinct values fuse mod `p` is
`p ∣ Norm(Δ)`. -/
theorem mem_badPrimeOfPair {N p : ℕ} :
    p ∈ badPrimeOfPair N ↔ p.Prime ∧ p ∣ N ∧ N ≠ 0 := by
  unfold badPrimeOfPair
  rw [Nat.mem_primeFactors]

/-- **the bad-prime set of a distinct pair is FINITE with a `p ≤ N` size cap.** Every bad prime of
a pair carried by a nonzero `N` divides `N`, hence is `≤ N`. This is the elementary finiteness
witness: the obstruction primes of one pair live in `[2, N]`. -/
theorem badPrimeOfPair_le {N p : ℕ} (hN : N ≠ 0) (hp : p ∈ badPrimeOfPair N) : p ≤ N := by
  rw [mem_badPrimeOfPair] at hp
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hp.2.1

/-- **per-pair divisor-count ceiling (`p`-independent).** A distinct pair carried by `N ≥ 1` has at
most `Nat.log 2 N` bad primes. -/
theorem badPrimeOfPair_card_le {N : ℕ} (hN : 1 ≤ N) :
    (badPrimeOfPair N).card ≤ Nat.log 2 N :=
  card_primeFactors_le_natLog hN

variable {ι : Type*}

/-- **(B.2) the aggregate bad-prime set** over a finite family of distinct pairs. `pairs : Finset ι`
indexes the char-`0`-distinct pairs of `h_r` values; `Nrel i` is the nonzero norm of the `i`-th
pair's difference. The aggregate obstruction is the union of the per-pair bad-prime sets — still a
**finite** `Finset ℕ` by `Finset.biUnion`. -/
noncomputable def pairBadPrimes (pairs : Finset ι) (Nrel : ι → ℕ) : Finset ℕ :=
  pairs.biUnion (fun i => badPrimeOfPair (Nrel i))

/-- `p` is in the aggregate bad set iff it is a prime factor of some pair's norm. -/
theorem mem_pairBadPrimes {pairs : Finset ι} {Nrel : ι → ℕ} {p : ℕ} :
    p ∈ pairBadPrimes pairs Nrel ↔ ∃ i ∈ pairs, p.Prime ∧ p ∣ Nrel i ∧ Nrel i ≠ 0 := by
  classical
  unfold pairBadPrimes
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨i, hi, hp⟩; exact ⟨i, hi, (mem_badPrimeOfPair).mp hp⟩
  · rintro ⟨i, hi, hp⟩; exact ⟨i, hi, (mem_badPrimeOfPair).mpr hp⟩

/-- **(B.3) the aggregate count ceiling.** If every pair's norm satisfies `1 ≤ Nrel i ≤ B`, the
aggregate obstruction set has size at most `(#pairs) · log₂ B` — a finite, `p`-independent bound.
This is the count of primes the good-prime existence statement must dodge. -/
theorem pairBadPrimes_card_le {pairs : Finset ι} {Nrel : ι → ℕ} {B : ℕ}
    (h1 : ∀ i ∈ pairs, 1 ≤ Nrel i) (hB : ∀ i ∈ pairs, Nrel i ≤ B) :
    (pairBadPrimes pairs Nrel).card ≤ pairs.card * Nat.log 2 B := by
  classical
  unfold pairBadPrimes
  calc (pairs.biUnion (fun i => badPrimeOfPair (Nrel i))).card
      ≤ ∑ i ∈ pairs, (badPrimeOfPair (Nrel i)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ pairs, Nat.log 2 B := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        calc (badPrimeOfPair (Nrel i)).card
            ≤ Nat.log 2 (Nrel i) := badPrimeOfPair_card_le (h1 i hi)
          _ ≤ Nat.log 2 B := Nat.log_mono_right (hB i hi)
    _ = pairs.card * Nat.log 2 B := by rw [Finset.sum_const, smul_eq_mul]

/-- **a prime outside the aggregate bad set divides NO pair's norm** — hence collides no
char-`0`-distinct pair, so the char-`0` distinctness is preserved mod `p`. -/
theorem not_dvd_of_not_mem_pairBadPrimes {pairs : Finset ι} {Nrel : ι → ℕ} {p : ℕ}
    (hp : p.Prime) (hgood : p ∉ pairBadPrimes pairs Nrel)
    (hne : ∀ i ∈ pairs, Nrel i ≠ 0) :
    ∀ i ∈ pairs, ¬ (p ∣ Nrel i) := by
  intro i hi hdvd
  exact hgood (mem_pairBadPrimes.mpr ⟨i, hi, hp, hdvd, hne i hi⟩)

end NormModel

/-! ## Part C — the named analytic residual (effective Linnik / Lagarias–Odlyzko)

The combinatorial half (Part B) delivers a *finite, `p`-independent* obstruction set
`pairBadPrimes pairs Nrel`. What remains is purely the **existence** of a prime in the prize range
`[lo, hi]` (with `lo, hi = Θ(n^β)`) **outside** that finite set. We name this as a `Prop` and keep
it **genuinely open** — it reduces to effective Linnik / Lagarias–Odlyzko / Thorner–Zaman
PNT-in-AP, the same analytic input as `_BchksF4` and B3 / `_AvW2`. It is NOT proven here; only the
*reduction to it* is landed. -/

section Residual

/-- **(C) the named analytic input — `EffectiveGoodPrimeExists`.** A prime in the window `[lo, hi]`
that avoids the finite bad set `badset`. Quantitatively, `lo, hi = Θ(n^β)` is the prize field scale
and `badset = pairBadPrimes …` is the `O((#pairs)·log B)`-size obstruction. Whether such a prime
exists is precisely an **effective Linnik / Lagarias–Odlyzko PNT-in-AP** statement (the least prime
in an arithmetic progression avoiding `O(…)` excluded primes, in a polynomial-size window). It is
**OPEN** — NOT proven in this file (and is the BGK / good–bad-prime crossover boundary). -/
def EffectiveGoodPrimeExists (badset : Finset ℕ) (lo hi : ℕ) : Prop :=
  ∃ p, lo ≤ p ∧ p ≤ hi ∧ p.Prime ∧ p ∉ badset

/-- **THE F7 REDUCTION (honest delivery).** GIVEN the named effective-Linnik input
`EffectiveGoodPrimeExists badset lo hi`, a good prime `p ∈ [lo,hi]` exists that lies outside the
finite obstruction `badset`. When `badset = pairBadPrimes pairs Nrel`, such a `p` divides no pair's
norm (`not_dvd_of_not_mem_pairBadPrimes`), so the char-`0`-distinct count of `h_r` values is
**preserved mod `p`**. This is the whole content: the combinatorial obstruction (finite bad set +
divisor-count ceiling) is proven axiom-clean; only the *existence* of a prime past it in the prize
window remains, named `EffectiveGoodPrimeExists`, reducing to effective PNT-in-AP. -/
theorem goodPrime_preserves_distinct_of_effective
    {ι : Type*} (pairs : Finset ι) (Nrel : ι → ℕ) (lo hi : ℕ)
    (hne : ∀ i ∈ pairs, Nrel i ≠ 0)
    (hE : EffectiveGoodPrimeExists (pairBadPrimes pairs Nrel) lo hi) :
    ∃ p, lo ≤ p ∧ p ≤ hi ∧ p.Prime ∧ (∀ i ∈ pairs, ¬ (p ∣ Nrel i)) := by
  obtain ⟨p, hlo, hhi, hp, hgood⟩ := hE
  exact ⟨p, hlo, hhi, hp, not_dvd_of_not_mem_pairBadPrimes hp hgood hne⟩

/-! ### Non-vacuity / falsifiability of `EffectiveGoodPrimeExists` (machine-checked)

`EffectiveGoodPrimeExists` is NOT vacuously true: it has real content. We exhibit (1) a concrete
badset and window where a good prime DOES exist, and (2) a window so small that — for the same
badset — NO good prime exists, so the Prop FAILS. Together these certify the Prop discriminates. -/

/-- **(C.1) non-vacuity witness: the Prop CAN hold.** Take `badset = {3, 5}` (two "bad" primes) and
the window `[7, 11]`. The prime `7 ∈ [7,11]` is prime and avoids `{3,5}`, so
`EffectiveGoodPrimeExists {3,5} 7 11` HOLDS. -/
theorem effectiveGoodPrimeExists_nonvacuous :
    EffectiveGoodPrimeExists {3, 5} 7 11 := by
  refine ⟨7, le_refl 7, by norm_num, by decide, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- **(C.2) falsifiability witness: the Prop CAN FAIL.** With the same intent but a window too small
to contain any prime avoiding the bad set — `badset = {2, 3}` and the window `[4, 4]` — there is no
prime in `[4,4]` at all, so `EffectiveGoodPrimeExists {2,3} 4 4` is FALSE. This proves the Prop is
not vacuously true: existence genuinely depends on the window reaching past the obstruction. -/
theorem effectiveGoodPrimeExists_can_fail :
    ¬ EffectiveGoodPrimeExists {2, 3} 4 4 := by
  rintro ⟨p, hlo, hhi, hp, _⟩
  -- `p ∈ [4,4]` forces `p = 4`, which is not prime.
  have hp4 : p = 4 := le_antisymm hhi hlo
  rw [hp4] at hp
  exact (by decide : ¬ Nat.Prime 4) hp

/-- **(C.3) a sharper falsifiability witness: even when the window contains a prime, if EVERY prime
in the window is bad the Prop fails.** `badset = {5, 7}` with window `[5, 7]`: the only primes in
`[5,7]` are `5` and `7`, both bad, so `EffectiveGoodPrimeExists {5,7} 5 7` is FALSE — the window
must reach a prime *outside* the obstruction, which is exactly the analytic content. -/
theorem effectiveGoodPrimeExists_all_bad_fails :
    ¬ EffectiveGoodPrimeExists {5, 7} 5 7 := by
  rintro ⟨p, hlo, hhi, hp, hgood⟩
  -- the only primes in `[5,7]` are `5` and `7`; both are in the bad set, contradicting `hgood`.
  apply hgood
  -- `p ∈ {5,7}` reduces to `p = 5 ∨ p = 7`; bounds give `p ∈ {5,6,7}`, primality kills `6`.
  have hp6 : p ≠ 6 := by rintro rfl; exact (by decide : ¬ Nat.Prime 6) hp
  have : p = 5 ∨ p = 7 := by omega
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact this

end Residual

end ArkLib.ProximityGap.Frontier.SpecF7GoodPrimeCollisionCount

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.Frontier.SpecF7GoodPrimeCollisionCount
-- Part A — reduction-compatibility (from the S3 crown jewel)
#print axioms dividedDifferencePow_reduce
#print axioms schurH_reduce
#print axioms gamma_reduce
-- Part B — collision ⟹ divisibility, finite bad set
#print axioms card_primeFactors_le_natLog
#print axioms mem_badPrimeOfPair
#print axioms badPrimeOfPair_le
#print axioms badPrimeOfPair_card_le
#print axioms mem_pairBadPrimes
#print axioms pairBadPrimes_card_le
#print axioms not_dvd_of_not_mem_pairBadPrimes
-- Part C — the named analytic residual + non-vacuity / falsifiability
#print axioms goodPrime_preserves_distinct_of_effective
#print axioms effectiveGoodPrimeExists_nonvacuous
#print axioms effectiveGoodPrimeExists_can_fail
#print axioms effectiveGoodPrimeExists_all_bad_fails
end AxiomAudit
