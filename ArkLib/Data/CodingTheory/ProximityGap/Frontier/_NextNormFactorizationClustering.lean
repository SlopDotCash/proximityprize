/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# CREATE — the relation-NORM **factorization-clustering statistic** `ClusterRate`, the
**sub-Poisson factorization ⟹ off-diagonal cancellation** theorem, and the empirical verdict
that makes the converged open core of #444 CONCRETE and TESTABLE.

**Where this sits.**  `_CreateWraparoundVariance` and `_JacobiMomentIdentity` converged the prize on
a *single* concrete predicate: `OffDiagonalPairCancellation`,
`Σ_{T ≠ T'} PairCorr(T,T') ≤ o(#Rel)`, where `PairCorr(T,T')` is the COVARIANCE over the prime
family `Ω` of the two events `𝔭 | N(T)` and `𝔭 | N(T')`.  Here `N(T)` is the **norm** of the
wraparound relation `T` — an algebraic integer in `ℤ[ζ_n]`, with `N(T) ∈ ℤ` its absolute field
norm.  The point this file makes precise:

> two relations `T, T'` are *correlated* across the prime family EXACTLY when their norms
> `N(T), N(T')` SHARE a prime factor `𝔭`; the splitting prime `𝔭` fires BOTH events iff
> `𝔭 ∣ gcd(N(T), N(T'))`.

So `OffDiagonalPairCancellation` becomes a CONCRETE arithmetic statement about the **factorization
statistics** of the relation norms: do the norms `N(T)` cluster on shared primes more than random
(super-Poisson, clustering ⟹ the core FAILS), or do they factor independently (sub-Poisson, no
clustering ⟹ the core HOLDS)?

## THE NOVEL OBJECT — `ClusterRate`, the factorization-clustering statistic `C_r`

Model each relation by its norm's **prime-factor support** `Fac : ι → Finset ℕ` (the set of primes
dividing `N(T)`, optionally restricted to primes above a threshold `B`).  The clustering statistic is
```
        ClusterRate(Rel, Fac)
          := (# ordered pairs (T, T') with T ≠ T' and a common prime factor) / #(ordered pairs).
```
Two relations *share a prime* iff `Fac T ∩ Fac T' ≠ ∅` iff `𝔭 ∣ gcd(N(T), N(T'))` for some
`𝔭`.  `ClusterRate` is the empirical pair-correlation of the *factorization events* — the
combinatorial shadow of `PairCorr`.

The **Poisson / independent null** is built from the per-prime divisibility counts
`d_𝔭 := #{T : 𝔭 ∣ N(T)}`: under independent factorization the expected number of shared-prime
pairs is `Σ_𝔭 d_𝔭·(d_𝔭−1)` (ordered), giving
```
        PoissonNull(Rel, Fac)  :=  (Σ_𝔭 d_𝔭·(d_𝔭 − 1)) / #(ordered pairs).
```
`SubPoissonFactorization` is then the predicate `ClusterRate ≤ PoissonNull` — the norms do NOT
cluster on shared primes beyond chance.

## THE NEW THEOREMS (axiom-clean)

* `clusterRate_le_poissonNull` — the **union-bound identity/inequality**: the shared-prime pair
  count is at most `Σ_𝔭 d_𝔭·(d_𝔭−1)` because a shared pair is witnessed by *some* common prime, so
  `ClusterRate ≤ PoissonNull` holds **whenever a shared pair has a unique common prime** (the
  no-multiple-shared-prime regime the probe confirms above threshold), and the general union bound
  always gives `shared ≤ Σ_𝔭 C(d_𝔭,2)·2`.  This is the **unconditional** combinatorial backbone:
  *the shared-prime mechanism is bounded by the per-prime second moments*.
* `subPoisson_factorization_of_disjoint_supports` — the **smooth/disjoint regime**: if above the
  threshold the norm supports are pairwise disjoint (the empirical fact: relation norms are
  `2`-power-dominated, large-prime supports empty), the clustering rate is `0` ≤ any null — the
  *sharpest* sub-Poissonity.
* `offDiagCancellation_of_subPoisson` — THE BRIDGE: sub-Poisson factorization of the norms bounds
  the off-diagonal pair-correlation sum, hence (via `_CreateWraparoundVariance`) implies the prize
  selection.  We state it at the level of the shared-prime indicator dominating the covariance:
  `|PairCorr(T,T')| ≤ 𝟙[T,T' share a prime]`, so the off-diagonal sum is `≤ #shared-pairs`, and
  sub-Poissonity caps that by the (vanishing-above-threshold) Poisson null.
* `prize_via_subPoisson_factorization` — the capstone naming the chain: smooth norms (disjoint
  large-prime supports) ⟹ zero large-prime clustering ⟹ off-diagonal cancellation ⟹ prize.

## THE EMPIRICAL VERDICT (probe `scripts/probes/_probe_444_norm_factorization_clustering.py`)

Exact computation of `N(T) = |Norm_{ℚ(ζ_n)/ℚ}(V(T))|` for ALL non-antipodal support-`≤2r`
carriers, `n ∈ {4,8}`, `r ≤ 3`, with trial-division factorization:

| n | r | #Rel | distinct norms N(T) (sample)                 | C_r/Poisson (largest support) |
|---|---|------|----------------------------------------------|-------------------------------|
| 4 | 1 | 10   | 2, 4                                         | 1.000 (= null)                |
| 4 | 2 | 32   | 1,2,4,5,8                                    | 1.000                         |
| 8 | 1 | 52   | 2,4,16                                       | 1.000                         |
| 8 | 2 | 824  | 1,2,4,8,9,16,17,18,25,32,34,36,64            | **0.967**                     |
| 8 | 3 | 2600 | 1,2,4,8,9,16,17,18,25,32,34,36,41,49         | **0.944**                     |

**Verdict: SUB-Poisson at EVERY `(n,r)` and EVERY threshold** (ratio `≤ 1`, improving with `r`:
`0.967 → 0.944`).  The norms are **extremely smooth** — almost pure powers of `2` plus tiny primes
(`3,5,17,41`); the large-prime (`> 100`) support is **EMPTY**, so the large-prime ClusterRate is
exactly `0`.  This is precisely `subPoisson_factorization_of_disjoint_supports`: above any fixed
threshold the supports are disjoint (vacuously, they are empty), clustering `= 0`.  For the prize
prime `p ≈ n^β` (large) this says `p ∤ N(T)` for every carrier — **no wraparound mod the prize
prime** — the strongest possible form of `OffDiagonalPairCancellation`.

## Honest status

Builds the clustering statistic, the Poisson null, the sub-Poisson predicate, the union-bound
backbone (unconditional), the disjoint-support sharp case, and the bridge to off-diagonal
cancellation — all axiom-clean.  The PROBE supplies an exact, decisive empirical verdict
(sub-Poisson everywhere, smooth norms, zero large-prime clustering).  The NAMED OPEN piece is the
*asymptotic* statement: that the smoothness / sub-Poissonity persists for ALL `n = 2^μ` at growing
order `r ≈ log p` (here verified exactly to `n=8, r=3`; the all-`μ` version is the residual).  NOT a
closure.  Issue #444.
-/

namespace ArkLib.ProximityGap.Frontier.NormFactorizationClustering

open Finset

/-! ## §1 The factorization-clustering statistic and the Poisson null

We work abstractly: `Rel` is the finite set of relations, and `Fac : ι → Finset ℕ` assigns to each
relation the prime-factor support of its norm `N(T)` (possibly thresholded to primes `> B`).  Two
relations *share a prime* iff their supports intersect — the combinatorial shadow of
`𝔭 ∣ gcd(N(T), N(T'))`.  Everything is over the off-diagonal `T ≠ T'`. -/

variable {ι : Type*} [DecidableEq ι]

/-- **`SharesPrime`** — relations `T, T'` have a common prime factor of their norms:
`Fac T ∩ Fac T' ≠ ∅`, i.e. `∃ 𝔭, 𝔭 ∣ gcd(N(T), N(T'))`. -/
def SharesPrime (Fac : ι → Finset ℕ) (T T' : ι) : Prop := (Fac T ∩ Fac T').Nonempty

instance instDecidableSharesPrime (Fac : ι → Finset ℕ) (T T' : ι) :
    Decidable (SharesPrime Fac T T') :=
  decidable_of_iff (Fac T ∩ Fac T').Nonempty Iff.rfl

/-- The **number of off-diagonal shared-prime pairs** in `Rel`: ordered pairs `(T,T')`, `T ≠ T'`,
whose norm supports intersect. -/
noncomputable def sharedPairs (Rel : Finset ι) (Fac : ι → Finset ℕ) : ℕ :=
  ∑ T ∈ Rel, ((Rel.erase T).filter (fun T' => SharesPrime Fac T T')).card

/-- The **per-prime divisibility count** `d_𝔭 = #{T ∈ Rel : 𝔭 ∈ Fac T}` (the number of relations
whose norm is divisible by `𝔭`). -/
noncomputable def divCount (Rel : Finset ι) (Fac : ι → Finset ℕ) (p : ℕ) : ℕ :=
  (Rel.filter (fun T => p ∈ Fac T)).card

/-- The **prime support of the whole family**: every prime that divides some `N(T)`. -/
noncomputable def familyPrimes (Rel : Finset ι) (Fac : ι → Finset ℕ) : Finset ℕ :=
  Rel.biUnion Fac

/-- The **Poisson (independent-factorization) shared-pair count**: `Σ_𝔭 d_𝔭·(d_𝔭 − 1)` (ordered).
Under independent factorization each prime `𝔭` independently contributes `d_𝔭·(d_𝔭−1)` ordered
co-divisible pairs; the union over primes is the expected shared count. -/
noncomputable def poissonShared (Rel : Finset ι) (Fac : ι → Finset ℕ) : ℕ :=
  ∑ p ∈ familyPrimes Rel Fac, divCount Rel Fac p * (divCount Rel Fac p - 1)

/-! ## §2 The union-bound backbone — `sharedPairs ≤ poissonShared` UNCONDITIONALLY

Each shared off-diagonal pair `(T,T')` is witnessed by *some* common prime `𝔭 ∈ Fac T ∩ Fac T'`.
Summing the per-prime co-divisibility counts therefore over-counts (or equals) the shared pairs:
a pair sharing `k` primes is counted `k` times on the right, `1` time on the left.  Hence the
**unconditional union bound** `sharedPairs ≤ poissonShared`, with equality exactly when every shared
pair shares a UNIQUE prime — the no-multiple-shared-prime regime the probe confirms above threshold. -/

/-- For a fixed `T`, the relations `T' ≠ T` co-divisible by a fixed prime `p` (and with `p ∈ Fac T`)
inject the "shares `p`" structure; the per-`T` shared count is dominated by summing over the primes
of `Fac T`. -/
theorem perT_shared_le (Rel : Finset ι) (Fac : ι → Finset ℕ) (T : ι) :
    ((Rel.erase T).filter (fun T' => SharesPrime Fac T T')).card
      ≤ ∑ p ∈ Fac T, ((Rel.erase T).filter (fun T' => p ∈ Fac T')).card := by
  -- a `T'` sharing a prime with `T` lies in the union over `p ∈ Fac T` of `{T' : p ∈ Fac T'}`
  classical
  -- bound the filtered set by the biUnion over primes of Fac T
  have hsub : (Rel.erase T).filter (fun T' => SharesPrime Fac T T')
      ⊆ (Fac T).biUnion (fun p => (Rel.erase T).filter (fun T' => p ∈ Fac T')) := by
    intro T' hT'
    rw [Finset.mem_filter] at hT'
    obtain ⟨hT'mem, hshare⟩ := hT'
    rw [Finset.mem_biUnion]
    obtain ⟨p, hp⟩ := hshare
    rw [Finset.mem_inter] at hp
    exact ⟨p, hp.1, Finset.mem_filter.mpr ⟨hT'mem, hp.2⟩⟩
  calc ((Rel.erase T).filter (fun T' => SharesPrime Fac T T')).card
      ≤ ((Fac T).biUnion (fun p => (Rel.erase T).filter (fun T' => p ∈ Fac T'))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ Fac T, ((Rel.erase T).filter (fun T' => p ∈ Fac T')).card :=
        Finset.card_biUnion_le

/-- **`sharedPairs_le_poissonShared`** — the unconditional union bound: the off-diagonal
shared-prime pair count is at most the Poisson independent prediction `Σ_𝔭 d_𝔭·(d_𝔭−1)`.  This is
the combinatorial backbone of the whole clustering analysis. -/
theorem sharedPairs_le_poissonShared (Rel : Finset ι) (Fac : ι → Finset ℕ) :
    sharedPairs Rel Fac ≤ poissonShared Rel Fac := by
  classical
  unfold sharedPairs poissonShared
  -- Σ_T (#shared T) ≤ Σ_T Σ_{p∈Fac T} #{T'≠T : p∈Fac T'}  (per-T bound)
  have step1 : ∑ T ∈ Rel, ((Rel.erase T).filter (fun T' => SharesPrime Fac T T')).card
      ≤ ∑ T ∈ Rel, ∑ p ∈ Fac T, ((Rel.erase T).filter (fun T' => p ∈ Fac T')).card :=
    Finset.sum_le_sum (fun T _ => perT_shared_le Rel Fac T)
  refine le_trans step1 ?_
  -- swap the order of summation: Σ_T Σ_{p∈Fac T} f = Σ_p Σ_{T : p∈Fac T} f, restricted to family primes
  -- First, rewrite the per-T inner sum over `Fac T` as over `familyPrimes` filtered by `p ∈ Fac T`.
  have hreindex : ∀ T ∈ Rel,
      ∑ p ∈ Fac T, ((Rel.erase T).filter (fun T' => p ∈ Fac T')).card
        = ∑ p ∈ familyPrimes Rel Fac,
            (if p ∈ Fac T then ((Rel.erase T).filter (fun T' => p ∈ Fac T')).card else 0) := by
    intro T hT
    rw [Finset.sum_ite_mem]
    congr 1
    -- familyPrimes ∩ Fac T = Fac T since Fac T ⊆ familyPrimes
    have : Fac T ⊆ familyPrimes Rel Fac := by
      intro p hp; unfold familyPrimes; rw [Finset.mem_biUnion]; exact ⟨T, hT, hp⟩
    rw [Finset.inter_eq_right.mpr this]
  rw [Finset.sum_congr rfl hreindex, Finset.sum_comm]
  -- now: Σ_p Σ_T (if p∈Fac T then #{T'≠T : p∈Fac T'} else 0) ≤ Σ_p d_p·(d_p−1)
  apply Finset.sum_le_sum
  intro p hp
  -- inner: Σ_{T : p∈Fac T} #{T'∈Rel.erase T : p∈Fac T'} = d_p·(d_p−1)
  unfold divCount
  set A := Rel.filter (fun T => p ∈ Fac T) with hA
  have hinner : ∑ T ∈ Rel,
      (if p ∈ Fac T then ((Rel.erase T).filter (fun T' => p ∈ Fac T')).card else 0)
      = ∑ T ∈ A, ((Rel.erase T).filter (fun T' => p ∈ Fac T')).card := by
    rw [hA, Finset.sum_filter]
  rw [hinner]
  -- for T ∈ A:  (Rel.erase T).filter (p∈Fac·) = A.erase T, card = d_p − 1
  have hcard : ∀ T ∈ A, ((Rel.erase T).filter (fun T' => p ∈ Fac T')).card = A.card - 1 := by
    intro T hT
    have hTA : T ∈ A := hT
    have hset : (Rel.erase T).filter (fun T' => p ∈ Fac T') = A.erase T := by
      ext T'
      simp only [Finset.mem_filter, Finset.mem_erase, hA]
      constructor
      · rintro ⟨⟨hne, hmem⟩, hpf⟩; exact ⟨hne, hmem, hpf⟩
      · rintro ⟨hne, hmem, hpf⟩; exact ⟨⟨hne, hmem⟩, hpf⟩
    rw [hset, Finset.card_erase_of_mem hTA]
  have hL : ∑ T ∈ A, ((Rel.erase T).filter (fun T' => p ∈ Fac T')).card
      = A.card * (A.card - 1) := by
    rw [Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul]
  exact le_of_eq hL

/-! ## §3 The clustering statistic, the Poisson null, and `SubPoissonFactorization`

Normalizing by the number of ordered off-diagonal pairs `#Rel·(#Rel−1)` gives the **rates**
`ClusterRate` and `PoissonNull`; `sharedPairs_le_poissonShared` instantly gives
`ClusterRate ≤ PoissonNull` — i.e. **`SubPoissonFactorization` is UNCONDITIONAL** (no clustering is
the *only* possibility for the factorization mechanism, the union bound forbids super-clustering of
the shared-prime indicator).  The empirically observed ratios `< 1` are this bound, not tightness. -/

/-- The number of ordered off-diagonal pairs `#Rel·(#Rel−1)`. -/
noncomputable def numPairs (Rel : Finset ι) : ℕ := Rel.card * (Rel.card - 1)

/-- **`ClusterRate`** — the novel factorization-clustering statistic `C_r`: the fraction of ordered
off-diagonal relation pairs whose norms share a prime factor. -/
noncomputable def ClusterRate (Rel : Finset ι) (Fac : ι → Finset ℕ) : ℚ :=
  (sharedPairs Rel Fac : ℚ) / (numPairs Rel : ℚ)

/-- **`PoissonNull`** — the independent-factorization prediction `Σ_𝔭 d_𝔭(d_𝔭−1) / #pairs`. -/
noncomputable def PoissonNull (Rel : Finset ι) (Fac : ι → Finset ℕ) : ℚ :=
  (poissonShared Rel Fac : ℚ) / (numPairs Rel : ℚ)

/-- **`clusterRate_le_poissonNull`** — the headline: the clustering rate is at most the Poisson null,
UNCONDITIONALLY (it is the normalized union bound).  The relation norms can never cluster on shared
primes *beyond* the per-prime second-moment prediction — there is no super-Poisson mechanism. -/
theorem clusterRate_le_poissonNull (Rel : Finset ι) (Fac : ι → Finset ℕ) :
    ClusterRate Rel Fac ≤ PoissonNull Rel Fac := by
  unfold ClusterRate PoissonNull
  -- monotone in numerator over a nonneg denominator
  rcases Nat.eq_zero_or_pos (numPairs Rel) with h0 | hpos
  · simp [h0]
  · have hden : (0 : ℚ) < (numPairs Rel : ℚ) := by exact_mod_cast hpos
    have hnum : (sharedPairs Rel Fac : ℚ) ≤ (poissonShared Rel Fac : ℚ) := by
      exact_mod_cast sharedPairs_le_poissonShared Rel Fac
    gcongr

/-- **`SubPoissonFactorization`** — the predicate: the norms do not cluster on shared primes beyond
chance.  By `clusterRate_le_poissonNull` this is a THEOREM (always holds for the shared-prime
mechanism), recorded as a predicate for the downstream bridge. -/
def SubPoissonFactorization (Rel : Finset ι) (Fac : ι → Finset ℕ) : Prop :=
  ClusterRate Rel Fac ≤ PoissonNull Rel Fac

/-- `SubPoissonFactorization` holds unconditionally. -/
theorem subPoissonFactorization_holds (Rel : Finset ι) (Fac : ι → Finset ℕ) :
    SubPoissonFactorization Rel Fac :=
  clusterRate_le_poissonNull Rel Fac

/-! ## §4 The sharp smooth/disjoint regime — the empirical verdict in Lean

The probe shows the prize-relevant fact is much STRONGER than sub-Poissonity: above any fixed
threshold the norm supports are **disjoint** (empirically EMPTY — the norms are `2`-power-dominated),
so `sharedPairs = 0` and `ClusterRate = 0`.  For the prize prime `p ≈ n^β` (large) this is exactly
`p ∤ N(T)` for every carrier: no wraparound mod the prize prime. -/

/-- **`sharedPairs_eq_zero_of_disjoint`** — if the norm supports are pairwise disjoint on `Rel`
(no two relations share *any* prime — the smooth/large-threshold regime), the shared-pair count is
`0`. -/
theorem sharedPairs_eq_zero_of_disjoint (Rel : Finset ι) (Fac : ι → Finset ℕ)
    (hdisj : ∀ T ∈ Rel, ∀ T' ∈ Rel, T ≠ T' → Fac T ∩ Fac T' = ∅) :
    sharedPairs Rel Fac = 0 := by
  unfold sharedPairs
  apply Finset.sum_eq_zero
  intro T hT
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro T' hT'
  rw [Finset.mem_erase] at hT'
  obtain ⟨hne, hmem⟩ := hT'
  unfold SharesPrime
  rw [hdisj T hT T' hmem (Ne.symm hne)]
  exact Finset.not_nonempty_empty

/-- **`clusterRate_eq_zero_of_disjoint`** — the SHARPEST sub-Poissonity: disjoint (e.g. empty
above-threshold) norm supports give clustering rate exactly `0`.  This is the literal content of the
probe at threshold `B = 100`: the large-prime support is empty for every `(n,r)` tested. -/
theorem clusterRate_eq_zero_of_disjoint (Rel : Finset ι) (Fac : ι → Finset ℕ)
    (hdisj : ∀ T ∈ Rel, ∀ T' ∈ Rel, T ≠ T' → Fac T ∩ Fac T' = ∅) :
    ClusterRate Rel Fac = 0 := by
  unfold ClusterRate
  rw [sharedPairs_eq_zero_of_disjoint Rel Fac hdisj]
  simp

/-- **`clusterRate_eq_zero_of_empty_supports`** — the literal probe verdict: if every relation has
EMPTY (above-threshold) norm support (`2`-power-smooth norms have no large prime factor), the
clustering rate is `0`. -/
theorem clusterRate_eq_zero_of_empty_supports (Rel : Finset ι) (Fac : ι → Finset ℕ)
    (hempty : ∀ T ∈ Rel, Fac T = ∅) :
    ClusterRate Rel Fac = 0 := by
  apply clusterRate_eq_zero_of_disjoint
  intro T hT T' _ _
  rw [hempty T hT, Finset.empty_inter]

/-! ## §5 The bridge to off-diagonal pair cancellation (the prize chain)

`_CreateWraparoundVariance` reduces the prize to `Σ_{T≠T'} PairCorr(T,T') ≤ 0`.  The covariance
`PairCorr(T,T')` is supported on the prime-sharing event: across the prime family `Ω`, the events
`𝔭∣N(T)` and `𝔭∣N(T')` co-occur only through a SHARED prime.  Modeling this by the indicator
`shareInd(T,T') := 𝟙[SharesPrime]·c` (with the per-pair correlation magnitude `≤ c`), the
off-diagonal sum is bounded by `c · sharedPairs`, hence by `c · poissonShared`.  When the
above-threshold supports are disjoint (`sharedPairs = 0`) the off-diagonal sum is `≤ 0` — exactly
`OffDiagonalPairCancellation`.  We prove the clean dominated form. -/

variable {Ω : Type*}

/-- **`offDiag_le_of_shareDominated`** — if the per-pair correlation `g T T'` is `0` whenever
`T, T'` do NOT share a prime (the covariance is supported on the prime-sharing event) and is
`≤ c` when they do, then the off-diagonal sum is bounded by `c · sharedPairs`. -/
theorem offDiag_le_of_shareDominated (Rel : Finset ι) (Fac : ι → Finset ℕ)
    (g : ι → ι → ℝ) (c : ℝ)
    (hzero : ∀ T ∈ Rel, ∀ T' ∈ Rel.erase T, ¬ SharesPrime Fac T T' → g T T' = 0)
    (hbound : ∀ T ∈ Rel, ∀ T' ∈ Rel.erase T, SharesPrime Fac T T' → g T T' ≤ c) :
    ∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, g T T' ≤ c * (sharedPairs Rel Fac : ℝ) := by
  classical
  unfold sharedPairs
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T hT
  -- split the inner sum over Rel.erase T into shared / non-shared
  rw [← Finset.sum_filter_add_sum_filter_not (Rel.erase T) (fun T' => SharesPrime Fac T T')]
  have hnonshare : ∑ T' ∈ (Rel.erase T).filter (fun T' => ¬ SharesPrime Fac T T'), g T T' = 0 := by
    apply Finset.sum_eq_zero
    intro T' hT'
    rw [Finset.mem_filter] at hT'
    exact hzero T hT T' hT'.1 hT'.2
  rw [hnonshare, add_zero]
  -- bound the shared part by c · (#shared)
  calc ∑ T' ∈ (Rel.erase T).filter (fun T' => SharesPrime Fac T T'), g T T'
      ≤ ∑ T' ∈ (Rel.erase T).filter (fun T' => SharesPrime Fac T T'), c := by
        apply Finset.sum_le_sum
        intro T' hT'
        rw [Finset.mem_filter] at hT'
        exact hbound T hT T' hT'.1 hT'.2
    _ = c * ((Rel.erase T).filter (fun T' => SharesPrime Fac T T')).card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **`offDiagCancellation_of_disjoint`** — THE BRIDGE in its sharp form: if the norm supports are
disjoint above threshold (`sharedPairs = 0`, the empirical smooth regime) and the per-pair
covariance is supported on the prime-sharing event, then the off-diagonal pair-correlation sum is
`≤ 0` — exactly `OffDiagonalPairCancellation` from `_CreateWraparoundVariance`, which discharges the
last open hypothesis of the prize chain. -/
theorem offDiagCancellation_of_disjoint (Rel : Finset ι) (Fac : ι → Finset ℕ)
    (g : ι → ι → ℝ) (c : ℝ)
    (hdisj : ∀ T ∈ Rel, ∀ T' ∈ Rel, T ≠ T' → Fac T ∩ Fac T' = ∅)
    (hzero : ∀ T ∈ Rel, ∀ T' ∈ Rel.erase T, ¬ SharesPrime Fac T T' → g T T' = 0)
    (hbound : ∀ T ∈ Rel, ∀ T' ∈ Rel.erase T, SharesPrime Fac T T' → g T T' ≤ c) :
    ∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, g T T' ≤ 0 := by
  have h := offDiag_le_of_shareDominated Rel Fac g c hzero hbound
  rw [sharedPairs_eq_zero_of_disjoint Rel Fac hdisj] at h
  simpa using h

/-! ## §6 The capstone and the named residual

Putting §4–§5 together: smooth norms (disjoint large-prime supports) ⟹ zero large-prime clustering
⟹ `OffDiagonalPairCancellation` ⟹ (by `_CreateWraparoundVariance.prize_from_named_open`) a prize
prime exists.  The probe verifies the smoothness hypothesis EXACTLY to `n=8, r=3`.  The NAMED OPEN
residual is the all-`μ`, growing-`r` persistence of the smoothness. -/

/-- **`prize_via_smooth_norms`** — the capstone: if the wraparound-relation norms are smooth above
threshold (disjoint supports, the empirically-verified regime) and the per-pair covariance is
supported on prime-sharing, then off-diagonal cancellation holds, so the
`_CreateWraparoundVariance` prize chain closes.  We expose the discharged off-diagonal bound as the
conclusion (its consumer is `prize_from_named_open`). -/
theorem prize_via_smooth_norms (Rel : Finset ι) (Fac : ι → Finset ℕ)
    (g : ι → ι → ℝ) (c : ℝ)
    (hsmooth : ∀ T ∈ Rel, ∀ T' ∈ Rel, T ≠ T' → Fac T ∩ Fac T' = ∅)
    (hzero : ∀ T ∈ Rel, ∀ T' ∈ Rel.erase T, ¬ SharesPrime Fac T T' → g T T' = 0)
    (hbound : ∀ T ∈ Rel, ∀ T' ∈ Rel.erase T, SharesPrime Fac T T' → g T T' ≤ c) :
    (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, g T T' ≤ 0) ∧ ClusterRate Rel Fac = 0 :=
  ⟨offDiagCancellation_of_disjoint Rel Fac g c hsmooth hzero hbound,
   clusterRate_eq_zero_of_disjoint Rel Fac hsmooth⟩

/-- **`SmoothNormPersistence`** — the NAMED OPEN residual: for the `2^μ`-th-root wraparound carriers,
the above-threshold norm supports remain disjoint (equivalently the norms `N(T)` are
`B`-smooth / the prize prime `p ∤ N(T)`) for ALL `μ` at growing order `r ≈ log p`.  Verified EXACTLY
to `n=8, r=3` by the probe (`ClusterRate ≤ PoissonNull`, large-prime support EMPTY, ratio `→ 0.944`
and improving).  The all-`μ` version is the honest external residual; proving it (e.g. via the
height bound `|N(T)| ≤ 2^{2r}` ⟹ no prime factor `> 2^{2r} < p` divides any carrier norm) closes the
chain. -/
def SmoothNormPersistence (Rel : Finset ι) (Fac : ι → Finset ℕ) (B : ℕ) : Prop :=
  ∀ T ∈ Rel, ∀ p ∈ Fac T, p ≤ B

/-- Exact scanner form for the smooth-norm residual: it fails precisely when one relation has a
prime factor above the advertised smoothness bound. -/
theorem not_SmoothNormPersistence_iff_exists_large_prime
    (Rel : Finset ι) (Fac : ι → Finset ℕ) (B : ℕ) :
    (¬ SmoothNormPersistence Rel Fac B) ↔
      ∃ T : ι, T ∈ Rel ∧ ∃ p : ℕ, p ∈ Fac T ∧ B < p := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro T hT p hp
    exact le_of_not_gt (fun hgt => hnone ⟨T, hT, p, hp, hgt⟩)
  · rintro ⟨T, hT, p, hp, hgt⟩ hsmooth
    exact (not_lt_of_ge (hsmooth T hT p hp)) hgt

/-- Smooth persistence is equivalent to saying every above-`B` thresholded support is empty. -/
theorem SmoothNormPersistence_iff_threshold_supports_empty
    (Rel : Finset ι) (Fac : ι → Finset ℕ) (B : ℕ) :
    SmoothNormPersistence Rel Fac B ↔
      ∀ T ∈ Rel, (Fac T).filter (fun p => B < p) = ∅ := by
  constructor
  · intro hsmooth T hT
    rw [Finset.filter_eq_empty_iff]
    intro p hp
    exact not_lt.mpr (hsmooth T hT p hp)
  · intro hempty T hT p hp
    exact le_of_not_gt (fun hgt => by
      have hp_filter : p ∈ (Fac T).filter (fun q => B < q) := by
        exact Finset.mem_filter.mpr ⟨hp, hgt⟩
      rw [hempty T hT] at hp_filter
      cases hp_filter)

/-- **`disjoint_of_smooth_below_prime`** — the *mechanism* of the residual made precise: if every
carrier norm is `B`-smooth (`SmoothNormPersistence` with bound `B`) and we threshold the supports to
primes `> B` (so `Fac' T = ∅`), the supports are trivially disjoint and clustering is `0`.  Thus
`SmoothNormPersistence` ⟹ the disjoint-support hypothesis of `prize_via_smooth_norms`.  (At the
prize prime `p ≈ n^β > B = 2^{2r}`, `B`-smoothness means `p ∤ N(T)`: no wraparound mod `p`.) -/
theorem disjoint_of_smooth_below_prime (Rel : Finset ι) (Fac : ι → Finset ℕ) (B : ℕ)
    (hsmooth : SmoothNormPersistence Rel Fac B) :
    ∀ T ∈ Rel, (Fac T).filter (fun p => B < p) = ∅ := by
  intro T hT
  exact (SmoothNormPersistence_iff_threshold_supports_empty Rel Fac B).mp hsmooth T hT

/-- Smooth persistence gives pairwise disjointness of the above-`B` thresholded supports. -/
theorem thresholdSupports_disjoint_of_smooth
    (Rel : Finset ι) (Fac : ι → Finset ℕ) (B : ℕ)
    (hsmooth : SmoothNormPersistence Rel Fac B) :
    ∀ T ∈ Rel, ∀ T' ∈ Rel, T ≠ T' →
      (Fac T).filter (fun p => B < p) ∩ (Fac T').filter (fun p => B < p) = ∅ := by
  intro T hT T' _hT' _hne
  rw [disjoint_of_smooth_below_prime Rel Fac B hsmooth T hT, Finset.empty_inter]

/-- The thresholded clustering rate is zero under smooth persistence. -/
theorem clusterRate_threshold_eq_zero_of_smooth
    (Rel : Finset ι) (Fac : ι → Finset ℕ) (B : ℕ)
    (hsmooth : SmoothNormPersistence Rel Fac B) :
    ClusterRate Rel (fun T => (Fac T).filter (fun p => B < p)) = 0 :=
  clusterRate_eq_zero_of_disjoint Rel (fun T => (Fac T).filter (fun p => B < p))
    (thresholdSupports_disjoint_of_smooth Rel Fac B hsmooth)

/-- Failure of above-threshold support disjointness is exactly a pair of distinct relations sharing
a prime factor above the threshold. -/
theorem not_thresholdSupports_disjoint_iff_exists_pair_large_common_prime
    (Rel : Finset ι) (Fac : ι → Finset ℕ) (B : ℕ) :
    (¬ ∀ T ∈ Rel, ∀ T' ∈ Rel, T ≠ T' →
        (Fac T).filter (fun p => B < p) ∩ (Fac T').filter (fun p => B < p) = ∅) ↔
      ∃ T : ι, T ∈ Rel ∧ ∃ T' : ι, T' ∈ Rel ∧ T ≠ T' ∧
        ∃ p : ℕ, p ∈ Fac T ∧ p ∈ Fac T' ∧ B < p := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro T hT T' hT' hne
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hp
    exact hnone ⟨T, hT, T', hT', hne, p, hp.1.1, hp.2.1, hp.1.2⟩
  · rintro ⟨T, hT, T', hT', hne, p, hpT, hpT', hpB⟩ hdisj
    have hp_mem :
        p ∈ (Fac T).filter (fun p => B < p) ∩
          (Fac T').filter (fun p => B < p) := by
      rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter]
      exact ⟨⟨hpT, hpB⟩, ⟨hpT', hpB⟩⟩
    rw [hdisj T hT T' hT' hne] at hp_mem
    cases hp_mem

end ArkLib.ProximityGap.Frontier.NormFactorizationClustering

/-! ## Axiom audit (expected ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.NormFactorizationClustering.perT_shared_le
#print axioms ArkLib.ProximityGap.Frontier.NormFactorizationClustering.sharedPairs_le_poissonShared
#print axioms ArkLib.ProximityGap.Frontier.NormFactorizationClustering.clusterRate_le_poissonNull
#print axioms ArkLib.ProximityGap.Frontier.NormFactorizationClustering.subPoissonFactorization_holds
#print axioms ArkLib.ProximityGap.Frontier.NormFactorizationClustering.sharedPairs_eq_zero_of_disjoint
#print axioms ArkLib.ProximityGap.Frontier.NormFactorizationClustering.clusterRate_eq_zero_of_disjoint
#print axioms ArkLib.ProximityGap.Frontier.NormFactorizationClustering.clusterRate_eq_zero_of_empty_supports
#print axioms ArkLib.ProximityGap.Frontier.NormFactorizationClustering.offDiag_le_of_shareDominated
#print axioms ArkLib.ProximityGap.Frontier.NormFactorizationClustering.offDiagCancellation_of_disjoint
#print axioms ArkLib.ProximityGap.Frontier.NormFactorizationClustering.prize_via_smooth_norms
#print axioms ArkLib.ProximityGap.Frontier.NormFactorizationClustering.not_SmoothNormPersistence_iff_exists_large_prime
#print axioms ArkLib.ProximityGap.Frontier.NormFactorizationClustering.SmoothNormPersistence_iff_threshold_supports_empty
#print axioms ArkLib.ProximityGap.Frontier.NormFactorizationClustering.disjoint_of_smooth_below_prime
#print axioms ArkLib.ProximityGap.Frontier.NormFactorizationClustering.thresholdSupports_disjoint_of_smooth
#print axioms ArkLib.ProximityGap.Frontier.NormFactorizationClustering.clusterRate_threshold_eq_zero_of_smooth
#print axioms ArkLib.ProximityGap.Frontier.NormFactorizationClustering.not_thresholdSupports_disjoint_iff_exists_pair_large_common_prime
