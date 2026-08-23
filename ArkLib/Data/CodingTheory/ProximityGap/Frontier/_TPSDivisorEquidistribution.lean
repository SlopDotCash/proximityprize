/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# TPS divisor-equidistribution (#466 lane L8): budget gates + the named conjecture

The typical-prime sieve (essay §2.5, dossier v3 §15/F) closes moment depth `r ≤ β`
unconditionally; BEYOND that it needs **Conjecture TPS**: the divisor mass of the
cyclotomic relation norms `{N_a : ‖a‖₁ ≤ 2r}` equidistributes over primes `p ≡ 1 (mod n)`
in `[X, 2X]` up to `K^r` for `r ≤ c·log X`.  This lane produced the FIRST measurement of
that mass (`scripts/probes/probe_466_tps_equidist.py`, output
`scripts/probes/_out_466_tps_equidist.txt`).

## What is PROVEN here (axiom-clean)

For an abstract norm family `N : α → ℕ` on a finite relation set `A` with height cap
`cap` (`∀ a ∈ A, N a ≤ cap`):

* `divisorMass_eq_zero_of_cap_lt` — **the onset gate**: a prime above the cap receives
  ZERO divisor mass.  With the sharp height law `N_a ≤ (4r)^{φ(n)/2}` (measured ATTAINED
  at n=8,16 r=2,3 and n=32 r=2; provable by Parseval-on-the-fold + AM–GM, carried below as
  the named `SharpHeightLaw`) this makes the β-window onset depth
  `r*(n,β) = n^{2β/φ(n)}/4` EXACT: at n=8 the β=3 AND β=4 windows are empty at every
  realizable depth; at n=16 the β=4 window is empty for r ≤ 4.
* `sum_divisorMass_le` — **the global divisor budget** (double counting +
  `card_primeFactors_le_natLog`): the total mass over any prime set is
  `≤ #A · log₂ cap`.
* `card_overserved_mul_le` — **the anti-clustering census**: at most
  `#A · log₂ cap / T` primes can be `T`-over-served.  This is the UNCONDITIONAL half of
  equidistribution: clustering is budget-limited; what the conjecture adds is that no
  single prime exceeds `K^r` times the fair share.
* `tps_window_empty_of_heightLaw` — the conditional window-emptiness consumer of
  `SharpHeightLaw`.
* `tpsDivisorEquidistribution_mono` — monotone glue in `K`.

## What is MEASURED (probe, 2026-07-01/02 — the first data ever on this object)

Units: symmetry ORBITS of folded relations under `X ↦ ζᵗX^k` (order `n·φ(n)`) — raw
vector counts are degenerate (unfold × orbit ≈ 2^{2r}·n·φ(n) design effect).

* n=16, β=3 window `[4096,16384]`, orbit-unit Poisson index var/mean by depth:
  r=4 **0.806** (40/169 served, top share 0.049) · r=5 **0.858** (96/169, 0.032) ·
  r=6 **0.848** (113/169, 0.030 — richest cell, orbit mean 0.98) · r=7 **1.011**
  (69/169, 0.033).  n=32, β=3, r=2: 1.273 on tiny mass (7 orbits).
  **Poisson-consistent everywhere; no generic clustering.**
* **The β=4 window `[65536, 262144]` at n=16 is served for the FIRST TIME at r=6**
  (7 primes, orbit index **0.997**) and r=7 (12 primes, **0.994**) — every served prime
  generic (`v₂(p−1) ∈ {4,5,6}`, no GF, all single-orbit); r ≤ 5 has ZERO mass even where
  the cap permits (r=5 cap 160000 > 65536), and r=8 is the `{0,±1}` model boundary
  (`2r = n` forces full support; window mass returns to 0).
* Exceptions are exactly the KNOWN structured ones: the below-`√cap` small-prime regime
  (17 at n=16 — the canonical width-4 anchor factor, reproduced), and NOTHING else:
  generalized-Fermat primes are NOT over-served in the `{0,±1}` stack (their resonance is
  multiplicity-carried: the D4 anchor `W₄(65537, n=16) = +4480` is reproduced here and
  shown 100% carried by folded coefficients `|c_j| ≥ 3` — the `{0,±1}` stack has
  `W(65537) = 0` PROVABLY at r ≤ 4 by the onset gate, cap `16⁴ = 65536 < 65537`, and
  MEASURED 0 at r = 5,6,7 where the cap permits).
* Fair-share ratios (max orbit count / orbit mean, n=16 β=3): ≈ 8.2 at r=4, ≈ 5.4 at
  r=5, ≈ 5.1 at r=6, ≈ 5.6 at r=7 — consistent with `K^r` at `K ≤ 2`, if anything
  FLAT-to-decreasing in `r` (K^r slack unused).

## The DECISION (lane L8 verdict)

Fixed-depth divisor mass **equidistributes** in orbit units with only the known
structured exceptions.  The TPS-beyond-β residue is therefore **NOT refuted — it stays
live**, now as a quantitative named conjecture with measured constants
(`TPSDivisorEquidistribution K c`, measured-consistent at `K = 2` on every cell reached;
`c` unconstrained by data below `r = 8`).  Depth `r ≈ log p` remains numerically out of
reach (`#relations ≈ n^{2r}`); this Prop is the honest carrier.  ⚠️ NOT proven; NOT
claimed; refutable by any future cell with orbit-unit index ≫ 1 or a single unstructured
prime absorbing ≫ K^r fair shares.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open Finset

namespace ArkLib.ProximityGap.Frontier.TPSDivisorEquidistribution

/-! ## The per-integer divisor-count ceiling (inlined from `_AlmostAllPrimesWick`, whose
olean is not warm on this box — same statement, same proof; lane precedent
`_AvVD_DiffVarietyDivisorBudget.lean`) -/

/-- `2 ^ (#primeFactors n) ≤ n` for `n ≥ 1`. -/
theorem two_pow_card_primeFactors_le {n : ℕ} (hn : 1 ≤ n) :
    2 ^ n.primeFactors.card ≤ n := by
  classical
  have hprod_dvd : (∏ p ∈ n.primeFactors, p) ∣ n := Nat.prod_primeFactors_dvd n
  have hprod_le : (∏ p ∈ n.primeFactors, p) ≤ n := Nat.le_of_dvd hn hprod_dvd
  have hconst : (∏ _p ∈ n.primeFactors, (2 : ℕ)) ≤ ∏ p ∈ n.primeFactors, p :=
    Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  calc 2 ^ n.primeFactors.card
      = ∏ _p ∈ n.primeFactors, (2 : ℕ) := by simp [Finset.prod_const]
    _ ≤ ∏ p ∈ n.primeFactors, p := hconst
    _ ≤ n := hprod_le

/-- A positive integer has at most `log₂`-many distinct prime factors. -/
theorem card_primeFactors_le_natLog {n : ℕ} (hn : 1 ≤ n) :
    n.primeFactors.card ≤ Nat.log 2 n :=
  Nat.le_log_of_pow_le Nat.one_lt_two (two_pow_card_primeFactors_le hn)

/-! ## The abstract divisor-mass object -/

variable {α : Type}

open Classical in
/-- The divisor mass `W(p)` of the norm family `N` on the relation set `A` at the prime
`p`: the number of relations whose nonzero norm `p` divides (char-p wraparound relations
are exactly `p ∣ N_a ≠ 0`). -/
noncomputable def divisorMass (A : Finset α) (N : α → ℕ) (p : ℕ) : ℕ :=
  (A.filter fun a => N a ≠ 0 ∧ p ∣ N a).card

open Classical in
/-- **The onset gate.** A prime strictly above the family's height cap receives zero
divisor mass.  Instantiated at the sharp height law this pins the window onset depth
`r*(n,β) = n^{2β/φ(n)}/4` and proves the n=8 window emptiness and the n=16 r≤4 β=4
emptiness the probe reports. -/
theorem divisorMass_eq_zero_of_cap_lt {A : Finset α} {N : α → ℕ} {cap p : ℕ}
    (hcap : ∀ a ∈ A, N a ≤ cap) (hp : cap < p) :
    divisorMass A N p = 0 := by
  classical
  unfold divisorMass
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro a ha ⟨hne, hdvd⟩
  have hple : p ≤ N a := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  exact absurd (le_trans hple (hcap a ha)) (not_le.mpr hp)

open Classical in
/-- Per-relation prime-divisor count within any prime set is at most `log₂ cap`. -/
theorem card_filter_dvd_le_natLog {A : Finset α} {N : α → ℕ} {cap : ℕ}
    (hcap : ∀ a ∈ A, N a ≤ cap) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {a : α} (ha : a ∈ A) :
    (P.filter fun p => N a ≠ 0 ∧ p ∣ N a).card ≤ Nat.log 2 cap := by
  classical
  by_cases hz : N a = 0
  · have : (P.filter fun p => N a ≠ 0 ∧ p ∣ N a) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro p _ ⟨hne, _⟩
      exact hne hz
    simp [this]
  · have hsub : (P.filter fun p => N a ≠ 0 ∧ p ∣ N a) ⊆ (N a).primeFactors := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact Nat.mem_primeFactors.mpr ⟨hP p hp.1, hp.2.2, hp.2.1⟩
    calc (P.filter fun p => N a ≠ 0 ∧ p ∣ N a).card
        ≤ (N a).primeFactors.card := Finset.card_le_card hsub
      _ ≤ Nat.log 2 (N a) := card_primeFactors_le_natLog (Nat.one_le_iff_ne_zero.mpr hz)
      _ ≤ Nat.log 2 cap := Nat.log_mono_right (hcap a ha)

open Classical in
/-- **The global divisor budget** (the sieve's bookkeeping bound, now formal): the total
divisor mass of the family over ANY set of primes is at most `#A · log₂ cap`. -/
theorem sum_divisorMass_le {A : Finset α} {N : α → ℕ} {cap : ℕ}
    (hcap : ∀ a ∈ A, N a ≤ cap) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P, divisorMass A N p ≤ A.card * Nat.log 2 cap := by
  classical
  have hswap : ∑ p ∈ P, divisorMass A N p
      = ∑ a ∈ A, (P.filter fun p => N a ≠ 0 ∧ p ∣ N a).card := by
    simp only [divisorMass, Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  calc ∑ a ∈ A, (P.filter fun p => N a ≠ 0 ∧ p ∣ N a).card
      ≤ ∑ _a ∈ A, Nat.log 2 cap :=
        Finset.sum_le_sum fun a ha => card_filter_dvd_le_natLog hcap P hP ha
    _ = A.card * Nat.log 2 cap := by rw [Finset.sum_const, smul_eq_mul]

open Classical in
/-- **The anti-clustering census** (the unconditional half of equidistribution): the
number of `T`-over-served primes times `T` is bounded by the global budget — clustering
is budget-limited.  The conjecture below strengthens this from "few over-served primes"
to "NO prime exceeds `K^r` fair shares". -/
theorem card_overserved_mul_le {A : Finset α} {N : α → ℕ} {cap : ℕ}
    (hcap : ∀ a ∈ A, N a ≤ cap) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (T : ℕ) :
    (P.filter fun p => T ≤ divisorMass A N p).card * T ≤ A.card * Nat.log 2 cap := by
  classical
  have hsum : (P.filter fun p => T ≤ divisorMass A N p).card * T
      ≤ ∑ p ∈ P.filter (fun p => T ≤ divisorMass A N p), divisorMass A N p := by
    have h := Finset.card_nsmul_le_sum (P.filter fun p => T ≤ divisorMass A N p)
      (divisorMass A N) T fun p hp => (Finset.mem_filter.mp hp).2
    simpa [nsmul_eq_mul] using h
  have hmono : ∑ p ∈ P.filter (fun p => T ≤ divisorMass A N p), divisorMass A N p
      ≤ ∑ p ∈ P, divisorMass A N p :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  exact le_trans hsum (le_trans hmono (sum_divisorMass_le hcap P hP))

/-! ## The concrete relation-norm family -/

/-- The relation polynomial `A(X) = Σ_j a_j X^j` of an integer relation vector. -/
noncomputable def relationPoly (n : ℕ) (a : Fin n → ℤ) : Polynomial ℤ :=
  ∑ j : Fin n, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)

/-- The relation norm `N_a = |Res(Φ_n, A)|`: the integer invariant whose prime divisors
`p` are exactly the primes at which `a` is a wraparound relation on `μ_n` (`A` vanishes
at a primitive `n`-th root of unity mod `p`), for `N_a ≠ 0`. -/
noncomputable def relationNorm (n : ℕ) (a : Fin n → ℤ) : ℕ :=
  (Polynomial.resultant (Polynomial.cyclotomic n ℤ) (relationPoly n a)).natAbs

open Classical in
/-- The depth-`r` relation ball: `a ∈ ℤ^n` with `‖a‖₁ ≤ 2r` (the full L1 ball — the
`{0,±1}` stack is its multiplicity-free part; the D4 anchor shows the multiplicity
carriers `|a_j| ≥ 2` matter exactly at the resonant GF primes). -/
noncomputable def relationBall (n r : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.Icc (-(2 * r : ℤ)) (2 * r)).filter
    (fun a => ∑ j : Fin n, (a j).natAbs ≤ 2 * r)

/-- **The sharp height law** (named hypothesis — measured ATTAINED at n=8,16 with
r=2,3 and n=32 with r=2; provable by Parseval on the antipodal fold + AM–GM over the
`φ(n)` primitive embeddings; NOT formalized).  Quadratically stronger than the crude
conjugate bound `(2r)^{φ(n)}` used by all prior bookkeeping. -/
def SharpHeightLaw (n r : ℕ) : Prop :=
  ∀ a ∈ relationBall n r, relationNorm n a ≤ (4 * r) ^ (n / 4)

open Classical in
/-- Window emptiness below onset, conditional on the height law: any prime above
`(4r)^{n/4}` receives zero mass from the depth-`r` ball.  (At `n = 8`: `(4r)^2 ≤ 256`
for all realizable `r ≤ 4`, so both prize windows are empty at EVERY depth; at `n = 16`,
`r = 4`: cap `65536 < 65537` kills the GF prime exactly.) -/
theorem tps_window_empty_of_heightLaw {n r p : ℕ} (h : SharpHeightLaw n r)
    (hp : (4 * r) ^ (n / 4) < p) :
    divisorMass (relationBall n r) (relationNorm n) p = 0 :=
  divisorMass_eq_zero_of_cap_lt (fun a ha => h a ha) hp

/-! ## The conjecture (HONEST LABEL: open, not proven; supported by first data) -/

open Classical in
/-- The class primes `p ≡ 1 (mod n)` in the dyadic window `[X, 2X]`. -/
noncomputable def classPrimes (n X : ℕ) : Finset ℕ :=
  (Finset.Icc X (2 * X)).filter fun p => p.Prime ∧ p % n = 1

open Classical in
/-- Total divisor mass of the depth-`r` ball over the class window. -/
noncomputable def windowMass (n r X : ℕ) : ℕ :=
  ∑ p ∈ classPrimes n X, divisorMass (relationBall n r) (relationNorm n) p

/-- **CONJECTURE (TPS divisor-equidistribution) — OPEN, NOT PROVEN.**
No class prime in `[X, 2X]` receives more than `K^r` times the fair share (+1 for
integrality) of the depth-`r` relation-norm divisor mass, for depths up to `c·log₂ X`.
This is the exact named input that pushes the typical-prime sieve past `r ≈ β`
(essay §2.5); its only previously-proposed prize consumer (CMK ∘ TPS) is DEAD
(DISPROOF `466-r2-cmk-lonespike-refuted`), so this Prop is currently a sieve-side
carrier, not a prize closure.

Measured support (first data, probe_466_tps_equidist): orbit-unit Poisson indexes
0.806/0.858/0.848/1.011 (n=16 β=3, r=4..7), 0.997/0.994 (n=16 β=4, r=6/7 — the first
in-window mass ever measured), 1.273 (n=32 β=3, r=2, tiny mass); max fair-share ratio
≈ 5–8 flat in r — consistent with `K = 2` with the `K^r` slack unused; the only
over-served primes are below `√cap` (the small-prime regime the conjecture's
`[X, 2X]`-window form excludes by design once `X > √cap`).  ⚠️ Raw VECTOR counts are the
wrong unit (design effect ≈ 2^{2r}·n·φ(n)); any refutation must be stated in orbit
units. -/
def TPSDivisorEquidistribution (K c : ℕ) : Prop :=
  ∀ μ r X : ℕ, 4 ≤ μ → 1 ≤ r → r ≤ c * Nat.log 2 X →
    ∀ p ∈ classPrimes (2 ^ μ) X,
      divisorMass (relationBall (2 ^ μ) r) (relationNorm (2 ^ μ)) p
        ≤ K ^ r * (windowMass (2 ^ μ) r X / (classPrimes (2 ^ μ) X).card + 1)

/-- Monotone glue: the law at `K` gives the law at any `K' ≥ K`. -/
theorem tpsDivisorEquidistribution_mono {K K' c : ℕ} (hK : K ≤ K')
    (h : TPSDivisorEquidistribution K c) : TPSDivisorEquidistribution K' c := by
  intro μ r X hμ hr hrc p hp
  exact le_trans (h μ r X hμ hr hrc p hp)
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hK r))

/-! ## Source audit -/

#print axioms divisorMass_eq_zero_of_cap_lt
#print axioms card_filter_dvd_le_natLog
#print axioms sum_divisorMass_le
#print axioms card_overserved_mul_le
#print axioms tps_window_empty_of_heightLaw
#print axioms tpsDivisorEquidistribution_mono

end ArkLib.ProximityGap.Frontier.TPSDivisorEquidistribution
