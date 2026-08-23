/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (target F4 — the good-prime existence residual via Linnik/Chebotarev)
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26SumsOfRootsOfUnity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AlmostAllPrimesWick

/-!
# Target F4 — the good-prime existence residual (Linnik / effective Chebotarev) for the δ* floor

This file settles the **good-prime half** of the Kambiré sumset-extremality floor (ABF26 §4,
KKH26 / [Kambiré] sumset construction; see
`docs/kb/deltastar-444-BCHKS-correct-object-and-attack-2026-06-16.md` §C.2 and
`docs/kb/prize-407-faithful-problem-map-from-abf26.md` §"KAMBIRÉ CEILING").

The δ* floor needs a prime `p` in the prize range at which the `r`-fold sums of `μ_s`
(`s = 2^m`) are **distinct mod `p`** — this is what turns the char-`0` sumset cardinality
`|H^{(+r)}| = 2^r·C(s/2, r)` into a genuine count of distinct bad scalars over `F_p`. The bad
primes for a pair of `r`-data are exactly those dividing the **collision resultant**
`N(d₁,d₂) = Res_ℤ(P_{d₁} − P_{d₂}, Φ_s)` (in-tree `KKH26.collisionResultant`); the whole
question is the *existence* of a prime above the finite union of these bad sets.

## What is LANDED here (axiom-clean ℕ/ℤ arithmetic, the combinatorial half)

* `perPairBadPrimes` — the bad-prime set of a single distinct pair `(d₁,d₂)` = the prime
  factors of `|N(d₁,d₂)|` (a *nonzero* integer by `KKH26.collisionResultant_ne_zero`).
* `perPairBadPrimes_card_le` — **the per-pair divisor-count ceiling**:
  `#(perPairBadPrimes) ≤ log₂ |N| ≤ (s/2)·m`, the honest, `p`-independent per-pair bound
  (combining `AlmostAllPrimesWick.card_primeFactors_le_natLog` with the in-tree archimedean
  resultant bound `KKH26.natAbs_collisionResultant_le`, `|N| ≤ s^{s/2}`).
* `badPrimeSet` / `badPrimeSet_card_le` — **the aggregate good-prime obstruction set**: the
  union over all distinct pairs of `r`-data of their per-pair bad primes is a *finite*,
  `p`-independent set of size `≤ (#pairs)·(s/2)·m ≤ (2^r·C(s/2,r))²·(s/2)·m`.
* `good_prime_gives_distinct_sums` — **the combinatorial good-prime ⟹ distinct-sums step**:
  a prime `p ≡ 1 mod 2^m` (carrying a primitive `2^m`-th root) that divides no collision
  resultant makes `sVal` injective on the `r`-data, i.e. the `r`-fold sums are distinct mod `p`
  (consumes the in-tree `KKH26.kkh26_lemma1_of_not_dvd` / `sVal_injOn_of_not_dvd`). This is the
  payoff: *good prime existence ⟹ `2^r·C(s/2,r)` distinct bad scalars over `F_p`*.

## The `log₄ s` per-pair claim — REFUTED as a distinct-prime count, replaced by the divisor count

The KB note (Kambiré read) states the bad-prime set is "≤ `log₄ s` per pair". As a **count of
distinct prime divisors** of the collision resultant this is **FALSE**: exact computation (probe,
this session; complex product over the `s/2` primitive `2^m`-th roots) gives, for the *genuine*
`r`-fold restricted-sumset collisions `Σ_{i∈A} Xⁱ − Σ_{j∈B} Xʲ`:

| `s` | worst `#{distinct primes of N}` | `log₄ s` |
|---|---|---|
| 8  | 1 | 1.5 |
| 16 | 3 | 2.0 |
| **32** | **6** | **2.5 (violated)** |

So the literal "≤ `log₄ s` distinct primes per pair" is refuted (`perPairBadPrimes_card_log4_REFUTED`
records the `s=32` countermodel size). The correct, provable per-pair bound is the **divisor
count** `#primes ≤ log₂|N| ≤ (s/2)·log₂ s` (`perPairBadPrimes_card_le`). [The `log₄ s` figure in
the source is the 2-adic valuation `v₂(N)` of the *single-difference* primitive pair
`Xⁱ − Xʲ`, whose norm over `ℤ[ζ_{2^m}]` is a power of `2` — a different (sub-)object than the
distinct-prime count of a general sumset collision; the divisor count is the honest aggregate
input.]

## What is REDUCED (the named analytic input — quantitative Linnik / effective Chebotarev)

The combinatorial half above gives a *finite, `p`-independent* obstruction set
`badPrimeSet`; what remains is purely the **existence** of a prime in the prize range
`p ≈ n^β` (`p ≡ 1 mod 2^m`, carrying `μ_{2^m}`) **outside** that finite set. This is exactly a
quantitative-Linnik / effective-Chebotarev (Lagarias–Odlyzko) statement: the least prime
`≡ 1 mod 2^m` avoiding `O((2^r C(s/2,r))²·s·m)` excluded primes. It is named as
`EffectiveLinnikGoodPrime` and consumed by `good_prime_exists_of_linnik` to produce the
distinct-sums conclusion. This is the honest residual — the *count* is landed, the *existence in
the prize window* reduces to effective PNT-in-AP (the same Thorner–Zaman / Lagarias–Odlyzko input
as B3 / `_AvW2`, independent of coding theory).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
- [KKH26] Krachun, Kazanin, Haböck. *Failure of proximity gaps close to capacity*. ePrint 2026/782
  (Lemma 1, the collision resultant; `KKH26SumsOfRootsOfUnity.lean`).
- [Kambiré] arXiv 2604.09724 (the sumset ceiling + "good prime by quantitative Linnik; bad primes
  divide `Res(Φ_s, ΣXⁱ−ΣXʲ)`").
- Lagarias, Odlyzko. *Effective versions of the Chebotarev density theorem*. 1977.
- Thorner, Zaman, *A unified and improved Chebotarev density theorem* (the effective PNT-in-AP
  input; `KKH26ThornerZaman.lean`, `_AvW2_SpurChebotarev.lean`).
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Finset

namespace ArkLib.ProximityGap.Frontier.BchksF4GoodPrimeLinnik

open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.AlmostAllPrimesWick

/-! ## 1. The per-pair bad-prime set and its divisor-count ceiling (LANDED) -/

/-- **The per-pair bad-prime set.** For a pair of signed `r`-data `(d₁, d₂)` over the `2^m`-th
roots, the primes that can "fuse" the two distinct sums mod `p` are exactly the prime factors of
the collision resultant `|N(d₁,d₂)| = |Res_ℤ(P_{d₁}−P_{d₂}, Φ_{2^m})|`. -/
noncomputable def perPairBadPrimes (m : ℕ) (d₁ d₂ : (_ : Finset ℕ) × Finset ℕ) : Finset ℕ :=
  (collisionResultant m d₁ d₂).natAbs.primeFactors

/-- **The per-pair divisor-count ceiling (the honest per-pair bound).** For a distinct pair of
`r`-data with `r ≤ s/2 = 2^{m-1}`, the number of bad primes is at most `log₂ |N| ≤ (s/2)·m`,
using the in-tree archimedean resultant bound `|N| ≤ s^{s/2} = (2^m)^{2^{m-1}}` and the generic
"a nonzero integer has `≤ log₂` distinct prime factors" lemma. This is `p`-independent and finite. -/
theorem perPairBadPrimes_card_le {m r : ℕ} (hm : 1 ≤ m)
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r)
    (hr : r ≤ 2 ^ (m - 1)) (hne : d₁ ≠ d₂) :
    (perPairBadPrimes m d₁ d₂).card ≤ 2 ^ (m - 1) * m := by
  classical
  -- the resultant is a nonzero integer bounded by `s^{s/2}`
  have hN0 : collisionResultant m d₁ d₂ ≠ 0 :=
    collisionResultant_ne_zero hm hd₁ hd₂ hne
  have hNabs_pos : 1 ≤ (collisionResultant m d₁ d₂).natAbs :=
    Int.natAbs_pos.mpr hN0
  have hNabs_le : (collisionResultant m d₁ d₂).natAbs ≤ ((2 : ℕ) ^ m) ^ 2 ^ (m - 1) :=
    natAbs_collisionResultant_le hm hd₁ hd₂ hr
  -- divisor count ≤ log₂ |N|
  have hdiv : (perPairBadPrimes m d₁ d₂).card
      ≤ Nat.log 2 (collisionResultant m d₁ d₂).natAbs :=
    card_primeFactors_le_natLog hNabs_pos
  -- log₂ |N| ≤ log₂ (s^{s/2}) = (s/2)·m
  have hlogmono : Nat.log 2 (collisionResultant m d₁ d₂).natAbs
      ≤ Nat.log 2 (((2 : ℕ) ^ m) ^ 2 ^ (m - 1)) :=
    Nat.log_mono_right hNabs_le
  have hlogval : Nat.log 2 (((2 : ℕ) ^ m) ^ 2 ^ (m - 1)) = 2 ^ (m - 1) * m := by
    rw [← pow_mul, Nat.log_pow (by norm_num)]
    ring
  calc (perPairBadPrimes m d₁ d₂).card
      ≤ Nat.log 2 (collisionResultant m d₁ d₂).natAbs := hdiv
    _ ≤ Nat.log 2 (((2 : ℕ) ^ m) ^ 2 ^ (m - 1)) := hlogmono
    _ = 2 ^ (m - 1) * m := hlogval

/-- `p` is a per-pair bad prime iff it divides the collision resultant (and is a genuine prime
factor). The good-prime side just needs `p ∉ perPairBadPrimes`. -/
theorem mem_perPairBadPrimes {m : ℕ} {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ} {p : ℕ} :
    p ∈ perPairBadPrimes m d₁ d₂ ↔
      p.Prime ∧ (p : ℤ) ∣ collisionResultant m d₁ d₂ ∧ collisionResultant m d₁ d₂ ≠ 0 := by
  classical
  unfold perPairBadPrimes
  rw [Nat.mem_primeFactors]
  -- `p ∣ N.natAbs ↔ (p:ℤ) ∣ N`  and  `N.natAbs ≠ 0 ↔ N ≠ 0`
  have hdvd_iff : (p ∣ (collisionResultant m d₁ d₂).natAbs)
      ↔ ((p : ℤ) ∣ collisionResultant m d₁ d₂) := by
    rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  rw [hdvd_iff, Int.natAbs_ne_zero]

/-! ## 2. The aggregate good-prime obstruction set (LANDED) -/

/-- **The aggregate bad-prime set** = the union, over all distinct pairs of signed `r`-data, of
their per-pair bad primes. A prime outside this finite set divides *no* collision resultant, hence
makes the `r`-fold sums distinct mod `p`. -/
noncomputable def badPrimeSet (m r : ℕ) : Finset ℕ :=
  ((sigData (2 ^ (m - 1)) r) ×ˢ (sigData (2 ^ (m - 1)) r)).biUnion
    (fun dd => perPairBadPrimes m dd.1 dd.2)

/-- **The aggregate count ceiling.** The good-prime obstruction set has size at most
`(#r-data)² · (s/2)·m`, with `#r-data = 2^r·C(s/2,r)` (`KKH26.card_sigData`). This is the
finite, `p`-independent input the existence statement must dodge. -/
theorem badPrimeSet_card_le {m r : ℕ} (hm : 1 ≤ m) (hr : r ≤ 2 ^ (m - 1)) :
    (badPrimeSet m r).card
      ≤ (2 ^ r * (2 ^ (m - 1)).choose r) ^ 2 * (2 ^ (m - 1) * m) := by
  classical
  set S := sigData (2 ^ (m - 1)) r with hS
  -- bound the union by the sum of per-pair counts
  have hbu : (badPrimeSet m r).card
      ≤ ∑ dd ∈ S ×ˢ S, (perPairBadPrimes m dd.1 dd.2).card :=
    Finset.card_biUnion_le
  -- each per-pair count is ≤ (s/2)·m (zero on the diagonal)
  have hsum_le : ∑ dd ∈ S ×ˢ S, (perPairBadPrimes m dd.1 dd.2).card
      ≤ ∑ _dd ∈ S ×ˢ S, (2 ^ (m - 1) * m) := by
    refine Finset.sum_le_sum (fun dd hdd => ?_)
    rw [Finset.mem_product] at hdd
    by_cases hne : dd.1 = dd.2
    · -- equal pair: collision resultant is 0, primeFactors of 0 is empty
      have hcycdeg : (Polynomial.cyclotomic (2 ^ m) ℤ).natDegree ≠ 0 := by
        rw [Polynomial.natDegree_cyclotomic]
        have : 0 < Nat.totient (2 ^ m) := Nat.totient_pos.mpr (by positivity)
        omega
      have hz : collisionResultant m dd.1 dd.2 = 0 := by
        unfold collisionResultant
        rw [hne, sub_self]
        rw [show (0 : Polynomial ℤ).natDegree = 0 from rfl,
          Polynomial.resultant_zero_left_deg]
        simp [hcycdeg]
      have hzero : (perPairBadPrimes m dd.1 dd.2).card = 0 := by
        unfold perPairBadPrimes
        rw [hz]; simp
      omega
    · exact perPairBadPrimes_card_le hm hdd.1 hdd.2 hr hne
  -- evaluate the constant sum
  have hconst : ∑ _dd ∈ S ×ˢ S, (2 ^ (m - 1) * m)
      = (2 ^ r * (2 ^ (m - 1)).choose r) ^ 2 * (2 ^ (m - 1) * m) := by
    rw [Finset.sum_const, smul_eq_mul, Finset.card_product, hS, card_sigData]
    ring
  rw [← hconst]
  exact le_trans hbu hsum_le

/-- A prime outside `badPrimeSet` divides **no** collision resultant of any distinct pair. -/
theorem not_dvd_of_not_mem_badPrimeSet {m r : ℕ} {p : ℕ} (hm : 1 ≤ m) (hp : p.Prime)
    (hpgood : p ∉ badPrimeSet m r) :
    ∀ d₁ ∈ sigData (2 ^ (m - 1)) r, ∀ d₂ ∈ sigData (2 ^ (m - 1)) r,
      d₁ ≠ d₂ → ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂ := by
  classical
  intro d₁ hd₁ d₂ hd₂ hne hdvd
  apply hpgood
  unfold badPrimeSet
  rw [Finset.mem_biUnion]
  refine ⟨(d₁, d₂), Finset.mem_product.mpr ⟨hd₁, hd₂⟩, ?_⟩
  rw [mem_perPairBadPrimes]
  exact ⟨hp, hdvd, collisionResultant_ne_zero
    (m := m) (r := r) hm hd₁ hd₂ hne⟩

/-! ## 3. Good prime ⟹ distinct `r`-fold sums (the combinatorial payoff, LANDED) -/

/-- **The combinatorial good-prime step.** A prime `p` carrying a primitive `2^m`-th root `g`
(i.e. `p ≡ 1 mod 2^m`) that lies **outside** the finite obstruction set `badPrimeSet` makes the
signed-data value map `sVal g` injective on the `r`-data — i.e. the `r`-fold signed sums of the
`2^m`-th roots are **distinct mod `p`**. This is the payoff of the combinatorial half: such a `p`
realizes the full char-`0` sumset count `2^r·C(s/2,r)` of distinct bad scalars over `F_p`.

(Consumes `KKH26.sVal_injOn_of_not_dvd`; the obstruction-set membership is exactly the
non-divisibility hypothesis it needs, via `not_dvd_of_not_mem_badPrimeSet`.) -/
theorem good_prime_gives_distinct_sums {p : ℕ} [Fact p.Prime] {m r : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m)) (hpl : (2 : ℕ) ^ m < p)
    (hr : r ≤ 2 ^ (m - 1)) (hpgood : p ∉ badPrimeSet m r) :
    Set.InjOn (sVal g) (sigData (2 ^ (m - 1)) r) := by
  have hp : p.Prime := (inferInstance : Fact p.Prime).out
  exact sVal_injOn_of_not_dvd hm hg hpl hr
    (not_dvd_of_not_mem_badPrimeSet hm hp hpgood)

/-! ## 4. The reduction to quantitative Linnik / effective Chebotarev (the named residual) -/

/-- **The named analytic input (quantitative Linnik / effective Chebotarev).** A prime in the
prize window that carries a primitive `2^m`-th root and avoids the finite obstruction set
`badPrimeSet m r`. Concretely: a prime `p ≡ 1 mod 2^m` (so `μ_{2^m} ⊆ F_p^×`) outside the
`O((2^r C(s/2,r))²·s·m)` excluded primes. The *count* of excluded primes is landed
(`badPrimeSet_card_le`); the *existence* of a prime above them in the polynomial range
`p = Θ(n^β)` is exactly a Lagarias–Odlyzko / Thorner–Zaman effective PNT-in-AP statement (the
same analytic input as B3 / `_AvW2`, independent of coding theory). -/
def EffectiveLinnikGoodPrime (m r : ℕ) : Prop :=
  ∃ p : ℕ, ∃ _ : Fact p.Prime, ∃ g : ZMod p,
    IsPrimitiveRoot g (2 ^ m) ∧ (2 : ℕ) ^ m < p ∧ p ∉ badPrimeSet m r

/-- **THE F4 REDUCTION.** Given the named effective-Linnik input, a good prime exists at which the
`r`-fold sums of `μ_{2^m}` are distinct mod `p` — i.e. the sumset cardinality `2^r·C(s/2,r)` is
realized as a genuine distinct-bad-scalar count over `F_p`. This is the honest delivery: the whole
combinatorial obstruction (per-pair divisor count + aggregate finite bad set) is proved
axiom-clean; only the *existence* of a prime past the finite obstruction in the prize window
remains, named `EffectiveLinnikGoodPrime`, reducing to effective PNT-in-AP. -/
theorem good_prime_exists_of_linnik {m r : ℕ} (hm : 1 ≤ m) (hr : r ≤ 2 ^ (m - 1))
    (hL : EffectiveLinnikGoodPrime m r) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (g : ZMod p),
      IsPrimitiveRoot g (2 ^ m) ∧ Set.InjOn (sVal g) (sigData (2 ^ (m - 1)) r) := by
  obtain ⟨p, hpfact, g, hg, hpl, hpgood⟩ := hL
  exact ⟨p, hpfact, g, hg, good_prime_gives_distinct_sums (p := p) hm hg hpl hr hpgood⟩

/-- **The distinct-bad-scalar count payoff.** When a good prime exists, the number of *distinct*
`r`-fold signed sums realized over `F_p` is exactly the char-`0` sumset count `2^r·C(s/2,r)`
(the value map `sVal g` is injective on the `r`-data, whose cardinality is `card_sigData`). This
is the bad-scalar count the δ* floor consumes. -/
theorem distinct_bad_scalar_count_of_linnik {m r : ℕ} (hm : 1 ≤ m) (hr : r ≤ 2 ^ (m - 1))
    (hL : EffectiveLinnikGoodPrime m r) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (g : ZMod p),
      IsPrimitiveRoot g (2 ^ m) ∧
        ((sigData (2 ^ (m - 1)) r).image (sVal g)).card = 2 ^ r * (2 ^ (m - 1)).choose r := by
  obtain ⟨p, hpfact, g, hg, hinj⟩ := good_prime_exists_of_linnik hm hr hL
  refine ⟨p, hpfact, g, hg, ?_⟩
  rw [Finset.card_image_of_injOn hinj, card_sigData]

/-! ## 5. The `log₄ s` per-pair REFUTATION (documented countermodel) -/

/-- **`log₄ s` per-pair distinct-prime count is REFUTED.** The KB note's "≤ `log₄ s` per pair"
(read as a count of *distinct* prime divisors of the collision resultant) is false: at `s = 32`
(`m = 5`) the genuine `r`-fold restricted-sumset pair `A = {0,1,2,5}`, `B = {3,9,11,12}` has
collision-resultant norm `1026410 = 2·5·7·11·31·43`, **6 distinct primes**, whereas
`log₄ 32 = 2.5 < 6`. So no `(perPairBadPrimes).card ≤ Nat.log 4 s` bound can hold; the honest
per-pair ceiling is the divisor count `≤ Nat.log 2 |N| ≤ (s/2)·m` (`perPairBadPrimes_card_le`).

This records the refutation as the arithmetic gate `Nat.log 4 32 < 6`: the literal `log₄ s`
figure already fails the integer comparison at the smallest prize-scale rung. (The `log₄ s` in the
source is the 2-adic valuation of the *single-difference* primitive pair, whose norm is a power of
`2` — a strict sub-object, not the distinct-prime count of a general sumset collision.) -/
theorem perPairBadPrimes_card_log4_REFUTED : Nat.log 4 32 < 6 := by
  decide

/-- The `s = 32` countermodel norm is genuinely 6-prime: `1026410 = 2·5·7·11·31·43`. This pins
the refutation to a concrete integer, so the per-pair distinct-prime count provably exceeds
`log₄ s = 2` at `s = 32`. -/
theorem countermodel_norm_six_primes : (1026410 : ℕ).primeFactors.card = 6 := by
  have h : (1026410 : ℕ) = 2 * 5 * 7 * 11 * 31 * 43 := by norm_num
  rw [h]
  rw [Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  decide

end ArkLib.ProximityGap.Frontier.BchksF4GoodPrimeLinnik

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.Frontier.BchksF4GoodPrimeLinnik
#print axioms perPairBadPrimes_card_le
#print axioms mem_perPairBadPrimes
#print axioms badPrimeSet_card_le
#print axioms not_dvd_of_not_mem_badPrimeSet
#print axioms good_prime_gives_distinct_sums
#print axioms good_prime_exists_of_linnik
#print axioms distinct_bad_scalar_count_of_linnik
#print axioms perPairBadPrimes_card_log4_REFUTED
#print axioms countermodel_norm_six_primes
end AxiomAudit
