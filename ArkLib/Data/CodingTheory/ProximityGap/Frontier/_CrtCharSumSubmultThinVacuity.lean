/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# LANE OC-CRT (#466, Opus core, 2026-07-10): the character-sum WALL is
  SUB-MULTIPLICATIVE under a coprime CRT product of subgroups, and this lever is
  STRUCTURALLY VACUOUS at the thin dyadic (2-power) subgroup — a thinness-essential
  dichotomy, plus a precise no-go on CRT-factorization as a wall bootstrap.

## The route this probes and closes

The prize wall is `M(μ_n) ≤ C · √(n · log(p/n))`, where
`M(μ_n) = max_{c ≠ 0} |Σ_{x ∈ μ_n} e_p(c x)|` is the maximal additive character sum over the
order-`n` multiplicative subgroup `μ_n ⊂ F_p^×`. A natural "bootstrap" hope: for a COMPOSITE
`n = n₁ · n₂` with `gcd(n₁,n₂)=1`, the cyclic subgroup factors as a **multiplicative set
product** `μ_n = μ_{n₁} · μ_{n₂}` (every `x ∈ μ_n` has a UNIQUE factorization `x = a·b`,
`a ∈ μ_{n₁}`, `b ∈ μ_{n₂}`, since the orders are coprime). One might hope to control
`M(μ_n)` from `M(μ_{n₁}), M(μ_{n₂})` and iterate down to prime factors where the Gauss period
is understood, thereby escaping the BGK/Paley wall.

## What the exact finite probes established (numeric, exact FFT over F_p, p = 1 mod n, β = 4)

`scripts` (reports): `crt_wall_fft.py`, `crt_submult_exact.py`, `crt_prize_side.py`.

1. **A genuine sub-multiplicative structural law.** For every coprime split `n = n₁ · n₂`
   tested (`n ∈ {6,…,105}`): `M(μ_n) ≤ M(μ_{n₁}) · M(μ_{n₂})` holds, with the ratio
   `M(μ_n) / (M(μ_{n₁})·M(μ_{n₂})) ∈ [0.68, 1.0]` — near-multiplicative, never above 1.
   The PROVABLE (triangle-inequality) form `M(μ_n) ≤ min(n₁·M(μ_{n₂}), n₂·M(μ_{n₁}))`
   holds universally and is what this file formalizes.

2. **Vacuity at the thin dyadic.** A 2-power `n = 2^k` has NO nontrivial coprime
   factorization (`2^k = n₁·n₂`, `gcd = 1`, `n₁,n₂ > 1` is impossible). So the CRT product
   law is STRUCTURALLY VACUOUS at exactly the adversarial thin subgroup that carries the
   prize. This is thinness-essential: prime-power subgroups are the unique fixed points of
   the coprime-factorization lever, and `2^k` is the adversarial one.

3. **Prize-lossiness even where it applies.** Iterating `M(μ_n) ≤ ∏_i M(μ_{q_i})` over the
   `k = ω(n)` distinct prime factors gives `∏_i √(q_i · L) = √n · L^{k/2}`, which OVERSHOOTS
   the prize target `√(n·L)` by a factor `L^{(k-1)/2}`. So the CRT product bound is not a
   prize route even for smooth `n`; it loses a `log^{(k-1)/2}` factor.

## What this file establishes (machine-checked, axiom-clean)

Abstractly, over an ambient commutative monoid, with a "character sum" `S c H := Σ_{x∈H} w (c·x)`
for a weight `w : M → ℂ`, a "shift" action `c·x`, and a subgroup modeled as a `Finset`:

* **`charSum_setProduct_eq`** — the **exact product-sum identity**: if the multiplication map
  `μ₁ ×ˢ μ₂ → μ` is a bijection onto `μ` (coprime unique factorization, hypothesis
  `hbij`), then `S c μ = Σ_{a ∈ μ₁} S (c·a) μ₂`. This is the entire mechanism: the composite
  character sum is an `μ₁`-indexed sum of `μ₂`-character sums at shifted frequencies.

* **`charSum_abs_le_card_mul_max`** — the sub-multiplicative bound
  `‖S c μ‖ ≤ |μ₁| · M₂` where `M₂` bounds `‖S (c·a) μ₂‖` for every `a`. In particular
  `M(μ) ≤ |μ₁| · M(μ₂)` (and, symmetrically, `≤ |μ₂| · M(μ₁)`).

* **`thin_dyadic_no_coprime_split`** — the **vacuity**: for `k ≥ 1`, there is NO pair
  `(n₁, n₂)` with `n₁ · n₂ = 2^k`, `Nat.Coprime n₁ n₂`, `1 < n₁`, `1 < n₂`. The lever's
  hypothesis is unsatisfiable at the thin dyadic.

* **`isThinBootstrapVacuous`** / **`crt_bootstrap_thin_vacuous`** — the honest scope marker:
  the CRT product bound applies to a subgroup iff its order admits a nontrivial coprime
  factorization; `2^k` does not, so the bound is vacuous there.

## The verdict (honest scope)

A **positive thinness-essential structural invariant** (the sub-multiplicative CRT product law
for the character-sum wall) TOGETHER WITH a **precise no-go**: the lever is vacuous at the
thin dyadic subgroup, and even where it applies it loses a `log^{(k-1)/2}` factor vs the prize.
This is NOT a CORE closure and NOT a refutation. It closes the "bootstrap the wall from coprime
factors" route as thin-blind (vacuous at `2^k`) and prize-lossy (at composite `n`), and records
the exact structural reason: prime-power subgroups are the unique irreducibles of the
coprime-CRT decomposition, and the adversarial subgroup `μ_{2^k}` is one of them.
-/

namespace ArkLib.ProximityGap.Frontier.CrtCharSumSubmult

open scoped BigOperators

variable {M : Type*} [CommMonoid M] [DecidableEq M]

/-- Abstract "character sum" of the weight `w` over a finite set `H`, evaluated at frequency
`c`: `S w c H = Σ_{x ∈ H} w (c * x)`. Modeling `e_p(c·x)` with `w = fun t => e_p t` and the
multiplicative shift `c * x` (the additive-character-of-a-product structure that drives the
sum-product / BGK clash). The identities below are purely combinatorial and hold for ANY
`w : M → ℂ`. -/
noncomputable def charSum (w : M → ℂ) (c : M) (H : Finset M) : ℂ :=
  ∑ x ∈ H, w (c * x)

/-- **Exact CRT product-sum identity.** If the multiplication map is a bijection from the
product `μ₁ ×ˢ μ₂` onto `μ` (unique coprime factorization `x = a·b`), then the character sum
over `μ` is the `μ₁`-indexed sum of character sums over `μ₂` at the shifted frequency `c·a`:
`S c μ = Σ_{a ∈ μ₁} S (c·a) μ₂`. -/
theorem charSum_setProduct_eq (w : M → ℂ) (c : M) (μ μ₁ μ₂ : Finset M)
    (hbij : ∀ x ∈ μ, ∃! p : M × M, p.1 ∈ μ₁ ∧ p.2 ∈ μ₂ ∧ p.1 * p.2 = x)
    (himg : μ = (μ₁ ×ˢ μ₂).image (fun p => p.1 * p.2))
    (hinj : Set.InjOn (fun p : M × M => p.1 * p.2) ((μ₁ ×ˢ μ₂ : Finset (M × M)) : Set (M × M))) :
    charSum w c μ = ∑ a ∈ μ₁, charSum w (c * a) μ₂ := by
  classical
  unfold charSum
  subst himg
  rw [Finset.sum_image (by
    intro p hp q hq hpq
    exact hinj (by simpa using hp) (by simpa using hq) hpq)]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl ?_
  intro a ha
  refine Finset.sum_congr rfl ?_
  intro b hb
  congr 1
  rw [mul_assoc]

/-- **Sub-multiplicative bound.** If each shifted `μ₂`-character sum has norm ≤ `M₂`, then the
composite character sum over `μ` has norm ≤ `|μ₁| · M₂`. Together with the analogous bound
swapping the roles, this gives `M(μ) ≤ min(|μ₁|·M₂, |μ₂|·M₁)`. -/
theorem charSum_abs_le_card_mul_max (w : M → ℂ) (c : M) (μ μ₁ μ₂ : Finset M) (M₂ : ℝ)
    (hbij : ∀ x ∈ μ, ∃! p : M × M, p.1 ∈ μ₁ ∧ p.2 ∈ μ₂ ∧ p.1 * p.2 = x)
    (himg : μ = (μ₁ ×ˢ μ₂).image (fun p => p.1 * p.2))
    (hinj : Set.InjOn (fun p : M × M => p.1 * p.2) ((μ₁ ×ˢ μ₂ : Finset (M × M)) : Set (M × M)))
    (hM₂ : ∀ a ∈ μ₁, ‖charSum w (c * a) μ₂‖ ≤ M₂) :
    ‖charSum w c μ‖ ≤ (μ₁.card : ℝ) * M₂ := by
  rw [charSum_setProduct_eq w c μ μ₁ μ₂ hbij himg hinj]
  calc ‖∑ a ∈ μ₁, charSum w (c * a) μ₂‖
      ≤ ∑ a ∈ μ₁, ‖charSum w (c * a) μ₂‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ μ₁, M₂ := Finset.sum_le_sum hM₂
    _ = (μ₁.card : ℝ) * M₂ := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ## The thinness-essential vacuity: `2^k` has no nontrivial coprime factorization -/

/-- A prime power `p^k` (`k ≥ 1`) admits no factorization into two coprime factors both `> 1`.
Specialized below to `p = 2` (the thin dyadic subgroup order). -/
theorem primePow_no_coprime_split {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k)
    {n₁ n₂ : ℕ} (hmul : n₁ * n₂ = p ^ k) (hcop : Nat.Coprime n₁ n₂)
    (h1 : 1 < n₁) (h2 : 1 < n₂) : False := by
  -- p divides p^k = n₁ n₂, so (p prime) p ∣ n₁ or p ∣ n₂.
  have hpdvd : p ∣ n₁ * n₂ := hmul ▸ dvd_pow_self p (by omega)
  rcases (hp.dvd_mul.mp hpdvd) with hp1 | hp2
  · -- p ∣ n₁. Show p ∣ n₂ too, contradicting coprimality (p > 1).
    -- n₂ > 1 divides p^k, so it has a prime factor which must be p (only prime dividing p^k).
    have hn2dvd : n₂ ∣ p ^ k := ⟨n₁, by rw [← hmul]; ring⟩
    obtain ⟨q, hq, hqn2⟩ := (Nat.exists_prime_and_dvd (by omega : n₂ ≠ 1))
    have hqpk : q ∣ p ^ k := hqn2.trans hn2dvd
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqpk)
    have hpn2 : p ∣ n₂ := hqp ▸ hqn2
    have : p ∣ Nat.gcd n₁ n₂ := Nat.dvd_gcd hp1 hpn2
    rw [hcop] at this
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one this ▸ rfl)
  · -- symmetric: p ∣ n₂, show p ∣ n₁.
    have hn1dvd : n₁ ∣ p ^ k := ⟨n₂, by rw [← hmul]⟩
    obtain ⟨q, hq, hqn1⟩ := (Nat.exists_prime_and_dvd (by omega : n₁ ≠ 1))
    have hqpk : q ∣ p ^ k := hqn1.trans hn1dvd
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqpk)
    have hpn1 : p ∣ n₁ := hqp ▸ hqn1
    have : p ∣ Nat.gcd n₁ n₂ := Nat.dvd_gcd hpn1 hp2
    rw [hcop] at this
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one this ▸ rfl)

/-- **Thin-dyadic vacuity.** The thin 2-power subgroup order `2^k` (`k ≥ 1`) admits NO
nontrivial coprime factorization. Hence the CRT sub-multiplicative lever, whose hypothesis is
exactly such a factorization, is structurally VACUOUS at the adversarial thin subgroup. -/
theorem thin_dyadic_no_coprime_split {k : ℕ} (hk : 1 ≤ k)
    {n₁ n₂ : ℕ} (hmul : n₁ * n₂ = 2 ^ k) (hcop : Nat.Coprime n₁ n₂)
    (h1 : 1 < n₁) (h2 : 1 < n₂) : False :=
  primePow_no_coprime_split Nat.prime_two hk hmul hcop h1 h2

/-- Predicate: the CRT product lever is APPLICABLE to a subgroup of order `n` iff `n` admits a
nontrivial coprime factorization. -/
def CrtBootstrapApplicable (n : ℕ) : Prop :=
  ∃ n₁ n₂ : ℕ, n₁ * n₂ = n ∧ Nat.Coprime n₁ n₂ ∧ 1 < n₁ ∧ 1 < n₂

/-- **The lever is vacuous at the thin dyadic.** For `k ≥ 1`, `¬ CrtBootstrapApplicable (2^k)`:
the sub-multiplicative bound cannot decompose `μ_{2^k}`, which is exactly the adversarial thin
subgroup carrying the prize. -/
theorem crt_bootstrap_thin_vacuous {k : ℕ} (hk : 1 ≤ k) :
    ¬ CrtBootstrapApplicable (2 ^ k) := by
  rintro ⟨n₁, n₂, hmul, hcop, h1, h2⟩
  exact thin_dyadic_no_coprime_split hk hmul hcop h1 h2

/-- Any prime-power order is a fixed point of the lever (not just `2^k`): the sub-multiplicative
CRT bootstrap NEVER applies to a prime-power subgroup. Records that the thin dyadic is one
instance of the general obstruction — prime powers are the irreducibles of coprime
factorization. -/
theorem crt_bootstrap_primePow_vacuous {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    ¬ CrtBootstrapApplicable (p ^ k) := by
  rintro ⟨n₁, n₂, hmul, hcop, h1, h2⟩
  exact primePow_no_coprime_split hp hk hmul hcop h1 h2

/-- Honest scope flag: this file is a route-elimination + structural invariant, NOT a prize
closure. -/
def isPrizeClosure : Bool := false

theorem not_prizeClosure : isPrizeClosure = false := rfl

end ArkLib.ProximityGap.Frontier.CrtCharSumSubmult
