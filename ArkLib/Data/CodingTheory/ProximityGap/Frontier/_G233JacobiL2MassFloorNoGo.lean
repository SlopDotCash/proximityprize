/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# G233: basis-independent coefficient-L2 mass floor for the quotient-Jacobi fanout (#466)

G228 rewrote the shared Mellin factor `S_χ = ∑_{u ∈ G} conj(χ)(2 - u)`, `What(χ) = n·S_χ`, as the
quotient-Jacobi column decomposition `S = V · 1`, with

```text
V_λ(χ) = (1/m) ∑_{u ∈ F_p^*} λ(u) conj(χ)(2 - u)      (an m × m matrix over nontrivial χ).
```

G228/G229 gave a fixed few-term / triangle floor `K = Ω(√m)`.  G231 upgraded it to the exact
large-sieve operator bound `λ_max(Vᴴ V) ≤ n²`, so any *fixed unit-weight coordinate* subfamily of
size `K` recovering a constant fraction of `‖S‖` needs `K ≥ ⌈(m − n)/(4n)⌉ ≈ 2⁹⁶ / 2⁹⁷`.  G232
checked empirically that no *coherent eigen-subfamily* helps either.

This file kernel-checks the single **basis-independent** inequality that subsumes all of the above.
The two exact analytic inputs, in the sponsor regime `2 ∉ G`, are

* `(A)` large-sieve operator bound:  `‖V a‖² ≤ n² · ‖a‖²` for every coefficient vector `a`;
* `(B)` sponsor Parseval lower bound:  `‖S‖² ≥ n · (m − n)`.

From these alone, any coefficient vector `a` (sparse or dense, coordinate subset or coherent
eigen-combination, adaptive or fixed) whose reconstruction `V a` captures at least a fraction `f` of
`‖S‖` (`‖V a‖² ≥ f² · ‖S‖²`) satisfies

```text
‖a‖² ≥ f² · ‖S‖² / n² ≥ f² · (m − n) / n.
```

For half capture `f = 1/2` this is `‖a‖² ≥ (m − n)/(4n)`, equivalently the division-free
`4 · n · ‖a‖² ≥ m − n`.  The pure `K`-dimensional subspace question is vacuous (any line through `S`
captures all of `S`), so the coefficient-L2 mass is the correct non-vacuous invariant: it bounds
unit-weight sparse families (recovering G231's `K ≥ (m − n)/(4n)` as the special case
`‖a‖² = K`) and unbounded-weight coherent / eigen combinations by the *same closed floor*,
independent of any basis.

The abstract lemma `l2_mass_floor_of_largesieve_parseval` is the real content.  We then pin the
exact sponsor constants for the two certified #466 primes:

```text
P1 = 2³⁰ · (2¹²⁸ + 192) + 1,   m1 = 2¹²⁸ + 192,
P2 = 2³⁰ · (2¹²⁹ + 13)  + 1,   m2 = 2¹²⁹ + 13,   n = 2³⁰,
```

so a unit-weight sparse family (`‖a‖² = K`) needs `K ≥ 2⁹⁶` at `P1` and `K ≥ 2⁹⁷` at `P2` to reach
half recovery.  This is a calibrated no-go, not a new character-sum estimate and not prize closure.
-/
set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G233JacobiL2MassFloorNoGo

/-! ## Abstract basis-independent mass floor

We work with nonnegative reals standing for the squared quantities `‖V a‖²`, `‖a‖²`, `‖S‖²`.
The two analytic inputs are recorded as hypotheses; the conclusion is the division-free mass
floor. -/

/-- **Basis-independent coefficient-L2 mass floor.**

Given the large-sieve operator bound `vNorm2 ≤ n² · aNorm2` (input `A`), the sponsor Parseval lower
bound `sNorm2 ≥ n · (m - n)` (input `B`), and a half-capture reconstruction `vNorm2 ≥ sNorm2 / 4`,
the squared coefficient mass obeys the division-free floor `4 · n · aNorm2 ≥ m - n`.

No basis, sparsity, coherence, or adaptivity assumption is used: the conclusion holds for every
coefficient vector, so it simultaneously governs fixed coordinate subfamilies (G228/G229/G231) and
coherent eigen-combinations (G232). -/
theorem l2_mass_floor_of_largesieve_parseval
    (n m : ℕ) (hn : 0 < n)
    (aNorm2 vNorm2 sNorm2 : ℝ)
    (hLargeSieve : vNorm2 ≤ (n : ℝ) ^ 2 * aNorm2)
    (hParseval : (n : ℝ) * ((m : ℝ) - n) ≤ sNorm2)
    (hHalf : sNorm2 / 4 ≤ vNorm2) :
    (m : ℝ) - n ≤ 4 * n * aNorm2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- Chain the three inputs:  n(m-n) ≤ sNorm2 ≤ 4 vNorm2 ≤ 4 n² aNorm2.
  have h1 : (n : ℝ) * ((m : ℝ) - n) ≤ 4 * vNorm2 := by
    have : sNorm2 ≤ 4 * vNorm2 := by linarith [hHalf]
    linarith [hParseval, this]
  have h2 : (n : ℝ) * ((m : ℝ) - n) ≤ 4 * ((n : ℝ) ^ 2 * aNorm2) := by
    have : (4 : ℝ) * vNorm2 ≤ 4 * ((n : ℝ) ^ 2 * aNorm2) := by linarith [hLargeSieve]
    linarith [h1, this]
  -- Divide by n > 0:  (m - n) ≤ 4 n aNorm2.
  have hkey : (n : ℝ) * ((m : ℝ) - n) ≤ (n : ℝ) * (4 * n * aNorm2) := by
    have : (4 : ℝ) * ((n : ℝ) ^ 2 * aNorm2) = (n : ℝ) * (4 * n * aNorm2) := by ring
    linarith [h2, this.ge, this.le]
  exact le_of_mul_le_mul_left hkey hn0

/-- **Unit-weight sparse specialization.**  For a unit-weight `K`-sparse coefficient vector,
`aNorm2 = K`, so the mass floor becomes the coordinate-count floor `4 n K ≥ m - n`, i.e.
`K ≥ (m - n)/(4n)`.  This recovers the G231 fixed-subfamily statement as a special case. -/
theorem sparse_count_floor_of_mass_floor
    (n m K : ℕ) (hn : 0 < n)
    (vNorm2 sNorm2 : ℝ)
    (hLargeSieve : vNorm2 ≤ (n : ℝ) ^ 2 * (K : ℝ))
    (hParseval : (n : ℝ) * ((m : ℝ) - n) ≤ sNorm2)
    (hHalf : sNorm2 / 4 ≤ vNorm2) :
    (m : ℝ) - n ≤ 4 * n * K :=
  l2_mass_floor_of_largesieve_parseval n m hn (K : ℝ) vNorm2 sNorm2
    hLargeSieve hParseval hHalf

/-! ## Sponsor primes

The production subgroup order and the two certified quotient sizes.  We prove the exact `2⁹⁶`/`2⁹⁷`
unit-weight-sparse half-recovery floors by closed `ℕ` arithmetic. -/

/-- The production subgroup order used by the sponsor primes. -/
def sponsorN : ℕ := 2 ^ 30

/-- Quotient size `(P1 - 1)/sponsorN`. -/
def sponsorM1 : ℕ := 2 ^ 128 + 192

/-- Quotient size `(P2 - 1)/sponsorN`. -/
def sponsorM2 : ℕ := 2 ^ 129 + 13

/-- The first certified sponsor prime. -/
def sponsorP1 : ℕ := sponsorN * sponsorM1 + 1

/-- The second certified sponsor prime. -/
def sponsorP2 : ℕ := sponsorN * sponsorM2 + 1

/-- `n ≤ m1` (needed for the mass-floor hypothesis). -/
theorem sponsorN_le_M1 : sponsorN ≤ sponsorM1 := by
  unfold sponsorN sponsorM1; norm_num

/-- `n ≤ m2`. -/
theorem sponsorN_le_M2 : sponsorN ≤ sponsorM2 := by
  unfold sponsorN sponsorM2; norm_num

/-- **P1 exact unit-weight half-recovery floor.**  Any `K`-sparse unit-weight Jacobi family with
`4 · sponsorN · K < sponsorM1 - sponsorN` fails the mass floor; the threshold `⌈(m1-n)/(4n)⌉` is
exactly `2⁹⁶`.  Equivalently, strict half recovery needs `K ≥ 2⁹⁶`. -/
theorem p1_half_recovery_needs_two_pow_96 :
    ∀ K : ℕ, 4 * sponsorN * K ≥ sponsorM1 - sponsorN → K ≥ 2 ^ 96 := by
  intro K hK
  -- sponsorM1 - sponsorN = 2^128 + 192 - 2^30;  4 * 2^30 = 2^32;  threshold = 2^96 (exact).
  -- 4 * sponsorN * (2^96 - 1) < sponsorM1 - sponsorN ≤ 4 * sponsorN * K  ⇒  K ≥ 2^96.
  by_contra h
  simp only [not_le] at h
  have hle : K ≤ 2 ^ 96 - 1 := by omega
  have hmul : 4 * sponsorN * K ≤ 4 * sponsorN * (2 ^ 96 - 1) :=
    Nat.mul_le_mul_left (4 * sponsorN) hle
  have hcontra : 4 * sponsorN * (2 ^ 96 - 1) < sponsorM1 - sponsorN := by
    unfold sponsorN sponsorM1; norm_num
  omega

/-- **P2 exact unit-weight half-recovery floor.**  The threshold `⌈(m2-n)/(4n)⌉` is exactly `2⁹⁷`,
so strict half recovery needs `K ≥ 2⁹⁷`. -/
theorem p2_half_recovery_needs_two_pow_97 :
    ∀ K : ℕ, 4 * sponsorN * K ≥ sponsorM2 - sponsorN → K ≥ 2 ^ 97 := by
  intro K hK
  by_contra h
  simp only [not_le] at h
  have hle : K ≤ 2 ^ 97 - 1 := by omega
  have hmul : 4 * sponsorN * K ≤ 4 * sponsorN * (2 ^ 97 - 1) :=
    Nat.mul_le_mul_left (4 * sponsorN) hle
  have hcontra : 4 * sponsorN * (2 ^ 97 - 1) < sponsorM2 - sponsorN := by
    unfold sponsorN sponsorM2; norm_num
  omega

end ArkLib.ProximityGap.Frontier.G233JacobiL2MassFloorNoGo
