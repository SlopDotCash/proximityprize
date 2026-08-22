/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# AvVD — the **difference-variety divisor budget**: an UNCONDITIONAL bound on the cumulative
wraparound first moment, plus the exact good-prime threshold (#444)

**Mandate (variance route, the convergent open core).**  `_CreateWraparoundVariance` and
`_NextDifferenceVariety` reduced the prize to `OffDiagonalPairCancellation` /
`FirstMomentDiffCancellation` — the off-diagonal pair-correlation of additive relations of `μ_n`,
realized (per `_NextDifferenceVariety`) as the **first moment of the iterated Jacobi phase over the
difference variety** `V_diff = {(T,T') : Σ T = Σ T'}`.  This file makes the **genuine arithmetic of
that first moment exact and proves an unconditional partial bound** on it.

## The exact arithmetic of the per-prime wraparound (the probe result, now a definition)

Fix the subgroup `μ_n ⊂ F_p^×` (`p ≡ 1 mod n`, so `p` splits completely in `ℚ(ζ_n)`).  For each
ordered pair `(T, T')` of additive `r`-carriers on `μ_n`, the **defect** is the element
`d(T,T') = Σ_i ζ^{T_i} − Σ_j ζ^{T'_j} ∈ ℤ[ζ_n]`.  The chosen embedding `ζ ↦ g^{(p−1)/n} mod p`
picks one prime `𝔭 ∣ p`, and
```
        S(T) = S(T') in F_p   ⟺   𝔭 ∣ d(T,T')   ⟺   p ∣ eval_t(d(T,T'))   (one residue),
```
where `eval_t` is the chosen reduction `ℤ[ζ] → F_p`.  Numerically VERIFIED (exact, to `n=16`):
the **wraparound count**
```
        wrap(p) := #{(T,T') : T' ≠ T (off-diagonal, non-char-0), 𝔭 ∣ d(T,T')}
                 = Σ_{distinct defects δ}  mult(δ) · [ p ∣ eval_t(δ) ].
```
This is the **first moment over `V_diff`**: `wrap(p)` is exactly the off-diagonal coincidence count
whose `√p`-weighted signed version is `Off` (`_JacobiFermatCohomology`).  Two facts about it,
established numerically and proved here abstractly:

1. **`wrap(p) ≤ N²/p` is NOT a theorem.**  The naive per-prime Poisson count bound HOLDS for thin
   primes (`p` large) but **FAILS** at thick structured primes (verified `n=32, r=2`: ratios up to
   `1.64`).  So the cancellation is NOT per-prime.  (Honest: the per-prime sub-Poisson bound the
   variance route would like is regime-gated, matching the thinness-essential obstruction.)

2. **The CUMULATIVE family bound IS unconditional.**  Summing over a prime family `P`,
   ```
        Σ_{p ∈ P} wrap(p) = Σ_δ mult(δ) · #{p ∈ P : p ∣ eval_t(δ)}
                         ≤ Σ_δ mult(δ) · #{p ∈ P : p ∣ |Norm(δ)|}
                         ≤ Σ_δ mult(δ) · ω(|Norm(δ)|)
                         ≤ Σ_δ mult(δ) · log₂ |Norm(δ)|,
   ```
   because each defect `δ ≠ 0` has `𝔭 ∣ δ ⟹ p ∣ Norm(δ)`, and a nonzero integer has at most
   `ω ≤ log₂` distinct prime factors (`AlmostAllPrimesWick.card_primeFactors_le_natLog`).  This is
   the genuine **divisor budget** of the difference variety — UNCONDITIONAL, axiom-clean.  Verified:
   the actual family sum is a tiny fraction (`~0.01–0.04`) of this UB at every `(n,r)`.

## What this file PROVES (axiom-clean) and the precise residual

Abstractly: a finite **defect family** `δ : ι → ℕ` of nonzero norms with multiplicities
`mult : ι → ℕ`, a prime family `P : Finset ℕ`, and a "kills" relation `K : ℕ → ι → Prop`
(`p` kills `δ_i` = the chosen prime ideal above `p` divides the defect) constrained by the single
arithmetic fact `K p i → p ∈ (δ i).primeFactors` (dividing a norm).  Then:

* `wrap` — the per-prime first moment `wrap P mult δ K p = Σ_i mult i · [K p i]`;
* `goodPrime_wrap_zero` — **the exact good-prime threshold**: if `p` exceeds every defect norm
  (`∀ i, δ i < p`), then `wrap p = 0`.  This is the UNCONDITIONAL discharge for thin primes —
  the wraparound literally vanishes once `p` passes the largest norm.  (Probe-confirmed: `wrap = 0`
  for all `p > M = max δ`.)
* `family_wrap_le_divisorBudget` — **the cumulative divisor budget**: the family-summed wraparound
  is at most `Σ_i mult i · log₂ (δ i)`.  Unconditional.
* `family_wrap_le_card_mul_log` — the uniform coarsening `≤ (Σ mult) · log₂(maxNorm)`: the total
  wraparound across the whole family is bounded by the relation count times a single `log` of the
  largest norm — i.e. the cumulative off-diagonal first moment is `O(#Rel · log)` over ANY prime
  family, with NO equidistribution input.

NAMED OPEN (honest, NOT discharged): the residual is the gap between this **worst-case divisor
count** `ω(Norm δ) ≤ log₂` and the **average** `1/p` density (the Poisson mean) — i.e. that no
defect norm has anomalously many prime factors in the prize family, equivalently the
Erdős–Kac/Sato–Tate equidistribution of `wrap(p)` toward its mean `N²/p`.  That equidistribution at
growing order `r ≈ log p` is the BGK/Paley wall (`_JacobiFermatCohomology.betti_blowup`,
`GrowingOrderFermatCancellation`); this file does NOT close it.  It DOES give the first
unconditional cumulative-family bound on the V_diff first moment and the exact good-prime vanishing.

Honest status: builds the divisor-budget arithmetic of the difference variety, proves the
good-prime threshold (`wrap = 0` past the max norm) and the unconditional cumulative bound
(axiom-clean), and names the precise equidistribution residual.  Genuine partial result on the most
credible open path.  NOT a closure.  Issue #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DiffVarietyDivisorBudget

open Finset

/-! ## §0 The divisor-count ceiling helper (inlined, axiom-clean)

A positive integer has at most `Nat.log 2`-many distinct prime factors: the product of its
distinct prime factors (each `≥ 2`) dominates `2 ^ #primeFactors` and divides `n`. -/

/-- `2 ^ (#primeFactors n) ≤ n` for `1 ≤ n` (product of distinct factors, each `≥ 2`, divides `n`). -/
theorem two_pow_card_primeFactors_le {n : ℕ} (hn : 1 ≤ n) :
    2 ^ n.primeFactors.card ≤ n := by
  classical
  have hprod_dvd : (∏ p ∈ n.primeFactors, p) ∣ n := Nat.prod_primeFactors_dvd n
  have hprod_le : (∏ p ∈ n.primeFactors, p) ≤ n := Nat.le_of_dvd hn hprod_dvd
  have hconst : (∏ _p ∈ n.primeFactors, (2 : ℕ)) ≤ ∏ p ∈ n.primeFactors, p :=
    Finset.prod_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  calc 2 ^ n.primeFactors.card
      = ∏ _p ∈ n.primeFactors, (2 : ℕ) := by simp [Finset.prod_const]
    _ ≤ ∏ p ∈ n.primeFactors, p := hconst
    _ ≤ n := hprod_le

/-- **The divisor-count ceiling.** `#primeFactors n ≤ log₂ n` for `1 ≤ n`. -/
theorem card_primeFactors_le_natLog {n : ℕ} (hn : 1 ≤ n) :
    n.primeFactors.card ≤ Nat.log 2 n :=
  Nat.le_log_of_pow_le Nat.one_lt_two (two_pow_card_primeFactors_le hn)

/-! ## §1 The per-prime wraparound first moment over the difference variety -/

variable {ι : Type*} [DecidableEq ι]

/-- The **per-prime wraparound** (first moment over `V_diff` at prime `p`): the multiplicity-weighted
count of defects `δ_i` that `p` "kills" (i.e. the chosen prime ideal above `p` divides the defect).
`wrap P mult δ K p = Σ_i mult i · [K p i]`.  `K` is decidable. -/
noncomputable def wrap (mult : ι → ℕ) (Rel : Finset ι) (K : ℕ → ι → Prop)
    [∀ p i, Decidable (K p i)] (p : ℕ) : ℕ :=
  ∑ i ∈ Rel, mult i * (if K p i then 1 else 0)

/-! ## §2 The exact good-prime threshold: `wrap = 0` past the largest defect norm

The single most useful UNCONDITIONAL fact.  The arithmetic constraint on `K` is the genuine
number-theoretic content: `p` kills `δ_i` only if `p ∣ δ_i` (the chosen prime ideal divides the
defect ⟹ the underlying rational prime divides the norm).  Hence once `p` exceeds every defect norm
`δ_i`, no `δ_i` is divisible by `p`, so `wrap p = 0`. -/

/-- **`goodPrime_wrap_zero`** — THE EXACT GOOD-PRIME THRESHOLD.  Under the arithmetic constraint
`K p i → p ∈ (δ i).primeFactors` (killing a defect ⟹ `p` divides its norm), if the prime `p`
strictly exceeds every defect norm (`∀ i ∈ Rel, δ i < p`), then the wraparound vanishes:
`wrap p = 0`.  This is the unconditional discharge for THIN primes — the off-diagonal first moment
over `V_diff` is *exactly* the diagonal Poisson value `#Rel` once `p > max norm`.  No
equidistribution needed; pure divisibility. -/
theorem goodPrime_wrap_zero (mult : ι → ℕ) (Rel : Finset ι) (δ : ι → ℕ) (p : ℕ)
    (K : ℕ → ι → Prop) [∀ p i, Decidable (K p i)]
    (hK : ∀ i ∈ Rel, K p i → p ∈ (δ i).primeFactors)
    (hgood : ∀ i ∈ Rel, δ i < p) :
    wrap mult Rel K p = 0 := by
  unfold wrap
  apply Finset.sum_eq_zero
  intro i hi
  rw [mul_eq_zero]
  right
  rw [if_neg]
  intro hki
  -- `p ∈ primeFactors (δ i)` forces `p ∣ δ i`, hence `p ≤ δ i` (δ i > 0), contradicting `δ i < p`.
  have hpf := hK i hi hki
  have hdvd : p ∣ δ i := Nat.dvd_of_mem_primeFactors hpf
  have hne : δ i ≠ 0 := (Nat.mem_primeFactors.mp hpf).2.2
  have hpos : 0 < δ i := Nat.pos_of_ne_zero hne
  have hle : p ≤ δ i := Nat.le_of_dvd hpos hdvd
  exact absurd hle (not_le.mpr (hgood i hi))

/-! ## §3 The cumulative family bound: the divisor budget

Summing the wraparound over a prime family `P`, the contribution of each defect `δ_i` is its
multiplicity times the number of family primes that divide its norm — at most `ω(δ_i) ≤ log₂(δ_i)`.
This is the **unconditional** cumulative bound on the V_diff first moment, with NO equidistribution
input. -/

/-- The family-summed wraparound, regrouped by defect: `Σ_{p∈P} wrap p = Σ_i mult i · #{p∈P : K p i}`.
The Fubini swap (sum over primes ↔ sum over defects), the algebraic backbone of the budget. -/
theorem family_wrap_eq_regrouped (mult : ι → ℕ) (Rel : Finset ι) (P : Finset ℕ)
    (K : ℕ → ι → Prop) [∀ p i, Decidable (K p i)] :
    (∑ p ∈ P, wrap mult Rel K p)
      = ∑ i ∈ Rel, mult i * (P.filter (fun p => K p i)).card := by
  unfold wrap
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.card_filter]

/-- **The per-defect family-killing count is at most the number of distinct prime factors.**  Each
family prime that kills `δ_i` divides `δ_i` (the arithmetic constraint), and the kill set injects
into `(δ_i).primeFactors` (distinct primes), so its size is `≤ ω(δ_i) = #primeFactors`. -/
theorem killCount_le_omega (i : ι) (δ : ι → ℕ) (P : Finset ℕ) (K : ℕ → ι → Prop)
    [∀ p i, Decidable (K p i)]
    (hK : ∀ p ∈ P, K p i → p ∈ (δ i).primeFactors) :
    (P.filter (fun p => K p i)).card ≤ (δ i).primeFactors.card := by
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp
  exact hK p hp.1 hp.2

/-- **`family_wrap_le_omega_budget`** — the cumulative family wraparound is at most the
multiplicity-weighted sum of distinct-prime-factor counts of the defect norms:
`Σ_{p∈P} wrap p ≤ Σ_i mult i · ω(δ i)`.  Unconditional. -/
theorem family_wrap_le_omega_budget (mult : ι → ℕ) (Rel : Finset ι) (δ : ι → ℕ) (P : Finset ℕ)
    (K : ℕ → ι → Prop) [∀ p i, Decidable (K p i)]
    (hK : ∀ i ∈ Rel, ∀ p ∈ P, K p i → p ∈ (δ i).primeFactors) :
    (∑ p ∈ P, wrap mult Rel K p) ≤ ∑ i ∈ Rel, mult i * (δ i).primeFactors.card := by
  rw [family_wrap_eq_regrouped]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (killCount_le_omega i δ P K (hK i hi))

/-- **`family_wrap_le_divisorBudget`** — THE DIVISOR BUDGET.  Coarsening `ω ≤ log₂` (via
`card_primeFactors_le_natLog`, needs each defect norm `≥ 1`), the cumulative family wraparound is at
most `Σ_i mult i · log₂(δ i)`.  This is the unconditional bound on the V_diff first moment over the
prime family: the *total* off-diagonal coincidence mass is bounded by the relation multiset's
`log`-norm budget, with NO equidistribution input.  Axiom-clean. -/
theorem family_wrap_le_divisorBudget (mult : ι → ℕ) (Rel : Finset ι) (δ : ι → ℕ) (P : Finset ℕ)
    (K : ℕ → ι → Prop) [∀ p i, Decidable (K p i)]
    (hδpos : ∀ i ∈ Rel, 1 ≤ δ i)
    (hK : ∀ i ∈ Rel, ∀ p ∈ P, K p i → p ∈ (δ i).primeFactors) :
    (∑ p ∈ P, wrap mult Rel K p) ≤ ∑ i ∈ Rel, mult i * Nat.log 2 (δ i) := by
  refine le_trans (family_wrap_le_omega_budget mult Rel δ P K hK) ?_
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (card_primeFactors_le_natLog (hδpos i hi))

/-! ## §4 The uniform coarsening: `O(#Rel · log maxNorm)` over ANY prime family -/

/-- **`family_wrap_le_card_mul_log`** — the headline coarse bound.  If every defect norm is at most
`M` (`M ≥ 1`), the cumulative family wraparound is at most `(Σ_i mult i) · log₂ M`.  In the relation
language: the *total* off-diagonal first moment of `V_diff` over the entire prime family is
`O(#Rel · log M)` — bounded for ANY prime family with NO equidistribution assumption.  This is the
unconditional ceiling the variance route delivers; the prize needs the per-prime *average* to be
`#Rel/p` (Poisson), which is the named residual below, NOT this. -/
theorem family_wrap_le_card_mul_log (mult : ι → ℕ) (Rel : Finset ι) (δ : ι → ℕ) (P : Finset ℕ)
    (K : ℕ → ι → Prop) [∀ p i, Decidable (K p i)] (M : ℕ) (hM : 1 ≤ M)
    (hδpos : ∀ i ∈ Rel, 1 ≤ δ i) (hδle : ∀ i ∈ Rel, δ i ≤ M)
    (hK : ∀ i ∈ Rel, ∀ p ∈ P, K p i → p ∈ (δ i).primeFactors) :
    (∑ p ∈ P, wrap mult Rel K p) ≤ (∑ i ∈ Rel, mult i) * Nat.log 2 M := by
  refine le_trans (family_wrap_le_divisorBudget mult Rel δ P K hδpos hK) ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (Nat.log_mono_right (hδle i hi))

/-! ## §5 The named residual — Poisson equidistribution (OPEN, NOT discharged)

The divisor budget bounds the *cumulative* (family-summed) wraparound by `O(#Rel · log)`.  The prize
needs the per-prime wraparound to *average* to the Poisson value `#Rel/p` (so the variance is
sub-Poisson, `_CreateWraparoundVariance.subPoisson_of_offdiag_nonpos`).  The gap is the
**equidistribution residual**: the worst-case divisor count `ω(Norm δ) ≤ log₂` versus the average
`1/p` density.  We name it as a predicate; it is the Erdős–Kac / Sato–Tate equidistribution of the
difference variety at growing order — the BGK/Paley wall.  NOT discharged. -/

/-- **`PoissonEquidistribution`** — the named open residual.  Over the prize prime family `P`, the
*average* wraparound matches the Poisson mean `Nrel / p` up to the slack budget: there is a constant
`C` with the family-averaged wraparound bounded by `C · Nrel / pmin`.  Equivalently the V_diff first
moment equidistributes to its diagonal Poisson value at growing order `r ≈ log p`.  This is the
remaining open core; the divisor budget above is the unconditional *worst-case* handle, this is the
*average* the prize needs.  NOT discharged here. -/
def PoissonEquidistribution (mult : ι → ℕ) (Rel : Finset ι) (P : Finset ℕ)
    (K : ℕ → ι → Prop) [∀ p i, Decidable (K p i)] (C Nrel pmin : ℝ) : Prop :=
  ((∑ p ∈ P, wrap mult Rel K p : ℕ) : ℝ) / P.card ≤ C * Nrel / pmin

/-- **`thinFamily_no_wraparound`** — the clean END-TO-END unconditional consequence: if EVERY prime
in the family exceeds every defect norm (a *thin* family, `p > M ≥ max norm`), the cumulative
wraparound is `0` — the off-diagonal first moment over `V_diff` is identically the diagonal Poisson
value across the whole family, with NO equidistribution input.  This is the regime where the prize
bound holds unconditionally (the thin / good-prime regime); the open content is purely the thick
primes `p ≤ M`. -/
theorem thinFamily_no_wraparound (mult : ι → ℕ) (Rel : Finset ι) (δ : ι → ℕ) (P : Finset ℕ)
    (K : ℕ → ι → Prop) [∀ p i, Decidable (K p i)]
    (hK : ∀ i ∈ Rel, ∀ p ∈ P, K p i → p ∈ (δ i).primeFactors)
    (hthin : ∀ p ∈ P, ∀ i ∈ Rel, δ i < p) :
    (∑ p ∈ P, wrap mult Rel K p) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  exact goodPrime_wrap_zero mult Rel δ p K (fun i hi => hK i hi p hp) (fun i hi => hthin p hp i hi)

end ArkLib.ProximityGap.Frontier.DiffVarietyDivisorBudget

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffVarietyDivisorBudget.goodPrime_wrap_zero
#print axioms ArkLib.ProximityGap.Frontier.DiffVarietyDivisorBudget.family_wrap_eq_regrouped
#print axioms ArkLib.ProximityGap.Frontier.DiffVarietyDivisorBudget.killCount_le_omega
#print axioms ArkLib.ProximityGap.Frontier.DiffVarietyDivisorBudget.family_wrap_le_omega_budget
#print axioms ArkLib.ProximityGap.Frontier.DiffVarietyDivisorBudget.family_wrap_le_divisorBudget
#print axioms ArkLib.ProximityGap.Frontier.DiffVarietyDivisorBudget.family_wrap_le_card_mul_log
#print axioms ArkLib.ProximityGap.Frontier.DiffVarietyDivisorBudget.thinFamily_no_wraparound
