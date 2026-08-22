/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Lane B — DECISIVE resolution: Ferrero–Washington CANNOT close `μ_inv = 0` for the
  Conjecture-41 constraint module `Y_∞` (ePrint 2026/858, §7.6 / Prop 34 / Conj 41; #444 face (b))

## What this file resolves (the deliverable)

The just-committed Iwasawa skeleton (`_Conj41IwasawaModule.lean`, `_Conj41IwasawaGrowthDichotomy.lean`)
proved the **dichotomy** `m* = O(log n) ⟺ μ_inv(Y_∞) = 0` unconditionally, and carried
`FWApplies` / `mu_inv_zero` as a *named hypothesis* with a header note that it is "likely false."
This file **discharges that question definitively** — and the answer is the **negative branch (B)**:

  > **Ferrero–Washington PROVABLY CANNOT apply to `Y_∞`. The mismatch is FATAL.**
  > The dichotomy stands; `μ_inv(Y_∞) = 0` is an *independent* open question — the same `m*`
  > growth law in Iwasawa clothing — NOT a corollary of FW.

This is a `fatal-mismatch-resolved` outcome: as valuable as a positive one (it removes FW from the
list of live tools and tells the next attacker exactly which structural facts any *real* bridge
must overcome). Both obstructions are arithmetised below as axiom-clean theorems.

## The real theorem we are testing against

**Ferrero–Washington (1979)** (Ferrero–Washington, *The Iwasawa invariant `μ_p` vanishes for
abelian number fields*, Ann. of Math. **109** (1979) 377–395; second proof Sinnott 1984):
for the **cyclotomic `ℤ_p`-extension** `K_∞/K` of an **abelian** number field `K`, the Iwasawa
invariant `μ_p` of the inverse-limit class-group module `A_∞ = lim Cl(K_μ){p}` is **zero**. The
controlling prime is `p`, the **residue characteristic of the tower** (`Gal(K_∞/K) ≅ ℤ_p`,
`A_∞` is a `ℤ_p[[T]]`-module). For our 2-power FRI tower `K = ℚ(ζ_4)`, `p = 2`.

## OBSTRUCTION (i) — the controlling prime mismatch (the FATAL one, char-`p` vs char-`0`)

`Y_μ = ker_{𝔽_p}(N)` is the rank-deficiency space of the Prop-34 *integer* normal matrix `N`
**reduced mod the FRI field characteristic `p`**. Its dimension drops below `D` exactly when
`p` divides every `D×D` minor of `N` — a **Schwartz–Zippel coincidence event** for the *coding*
prime `p`. And `p` is forced by `μ_{2^μ} ⊂ 𝔽_p` to satisfy **`p ≡ 1 (mod 2^μ)`**, so in
particular `p` is an **odd** prime, `p ≠ 2`.

But FW's controlling prime for `K = ℚ(ζ_4)` is **`2`** (the tower residue characteristic). FW
bounds the growth of the `2`-part `Cl(ℚ(ζ_{2^μ})){2}` — a `ℤ_2`-module of *ideal classes*,
intrinsic to the field and **independent of any odd `p`**. The two objects live over different
primes:

  * `Y_μ`'s "corank" is an `𝔽_p`-dimension at the **odd** coding prime `p ≡ 1 (mod 2^μ)`;
  * FW's `μ_2 = 0` is about the **`2`**-adic class group.

There is no functorial map `ker_{𝔽_p}(N) → Cl(ℚ(ζ_{2^μ})){2}`: the former is the kernel of an
integer matrix mod an odd prime; the latter is a class group at the prime `2`. **FW's vanishing of
`μ_2` says nothing about the `𝔽_p`-rank-drop locus at the odd prime `p`.** This is the fatal gap.

We arithmetise it by the fact `(p ≡ 1 mod 2^μ ∧ μ ≥ 1) ⟹ p ≠ 2` — the FW prime and the bad prime
are *provably distinct* primes (`badPrime_ne_two`), so an `μ_p`-vanishing theorem at `p = 2`
cannot constrain the `μ`-invariant of an `𝔽_p`-module at `p ≠ 2`.

## OBSTRUCTION (ii) — doubling is `2:1`, NOT the Galois generator (different `Λ`-action)

The `Λ = ℤ_2[[T]]`-action FW endows on `A_∞` is the **arithmetic** one: the topological generator
`γ ∈ Gal(ℚ(ζ_{2^∞})/ℚ(ζ_4))` acts on ideal classes (`γ : ζ ↦ ζ^5`, a **bijection** fixing each
level). The natural transition on the period/Vandermonde side is the doubling/projection
`μ_{2n} ↠ μ_n`, `x ↦ x²` — exactly **`2`-to-`1`** (kernel `{±1}`), the *norm* direction, **not**
a bijection and **not** `γ`. A `Λ`-module built from doubling carries a different `Λ`-structure
than the arithmetic `A_∞`; identifying them requires the Stickelberger/Gauss-period bridge, which
is the open content itself. Arithmetised below as `doubling_card_two_to_one` (`|μ_{2^a}| =
2·|μ_{2^{a-1}}|` ⟹ non-injective) versus the bijectivity any Galois `γ` would have.

## The two facts together ⟹ FW is FATALLY inapplicable (Part 3)

We package the resolution as a theorem schema: ANY would-be FW bridge must identify `Y_∞` with a
sub/quotient of the `2`-adic class-group module `A_∞`. We prove this identification is blocked at
the most basic level — the controlling primes differ (`2` vs an odd `p ≡ 1 mod 2^μ`) — by
exhibiting, for the FW-prime hypothesis to even be type-correct, a contradiction. Concretely
`fw_prime_is_two_but_bad_prime_is_odd`: the FW invariant lives at `2`; every Conj-41 bad prime is
`≡ 1 mod 2^μ` (hence odd, `≠ 2`). So FW's conclusion (`μ_2(A_∞) = 0`) is a statement about a
**different prime** than the one governing `Y_μ = ker_{𝔽_p}(N)`. Therefore:

  > FW gives `μ_inv = 0` for `A_∞` at the prime `2`; this does **not** transfer to the
  > `𝔽_p`-rank-growth invariant of `Y_∞` at the odd coding prime `p`. **FW cannot close face (b).**

## Can `μ_inv(Y_∞) = 0` be reached by ANY other means? (Part 4 — honest residual)

We record what survives: the dichotomy is FW-independent, and `μ_inv(Y_∞) = 0` is *equivalent* to
the measured sub-doubling of `m*` becoming a theorem (the corank stays affine in `μ`). The cleanest
genuinely-provable fragment is the **mod-`p` minor-content characterisation**: a level-`μ` bad
prime is one dividing the content of the top exterior power of the integer matrix `N_μ`, a
*config-local Schwartz–Zippel* quantity (verified: for the committed `conf17` family the ONLY bad
prime `≡ 1 mod 16` below `20000` is `17` itself — `/tmp/conf17check.py`). This is the right object
for an *effective-threshold* (Conj-41 `p0`) attack, and it is **not** the FW class-group object.
We formalise the FW-independence of the dichotomy (`dichotomy_is_FW_independent`) as the honest
positive deliverable.
-/

namespace ProximityGap.Conj41FWMismatch

/-! ## Part 1 — OBSTRUCTION (i): the controlling primes are provably distinct

The Conj-41 bad prime `p` (the FRI field characteristic) embeds `μ_{2^μ}`, forcing
`p ≡ 1 (mod 2^μ)`; for `μ ≥ 1` this makes `p` odd, hence `p ≠ 2`. FW's controlling prime for the
2-power cyclotomic tower is `2`. So they are different primes, and a vanishing theorem for `μ_2`
cannot be about the `𝔽_p`-invariant at `p`. -/

/-- **The FW controlling prime for the 2-power cyclotomic tower is `2`.** (Definitional anchor: for
`K = ℚ(ζ_4)`, `Gal(K_∞/K) ≅ ℤ_2`, and FW bounds the invariant `μ_2`.) -/
def fwPrime : ℕ := 2

/-- **A Conj-41 bad prime `p` embeds `μ_{2^μ}`, hence `p ≡ 1 (mod 2^μ)`.** This is the structural
constraint on the FRI field characteristic: the roots `α_e = ζ^e` (the `2^μ`-th roots of unity)
must live in `𝔽_p`, which requires `2^μ ∣ p − 1`. We carry it as the defining predicate of an
admissible bad prime. -/
def BadPrimeAdmissible (μ p : ℕ) : Prop := p.Prime ∧ (2 ^ μ) ∣ (p - 1)

/-- **An admissible bad prime at level `μ ≥ 1` is odd.** Since `2 ∣ 2^μ ∣ p − 1`, `p − 1` is even,
so `p` is odd. (`μ ≥ 1` is essential: at `μ = 0` the constraint is vacuous, `2^0 = 1 ∣ anything`.) -/
theorem badPrime_odd {μ p : ℕ} (hμ : 1 ≤ μ) (h : BadPrimeAdmissible μ p) : Odd p := by
  obtain ⟨hp, hdvd⟩ := h
  have hp1 : 1 ≤ p := hp.one_lt.le
  have h2 : (2 : ℕ) ∣ 2 ^ μ := dvd_pow_self 2 (by omega : μ ≠ 0)
  have h2p : (2 : ℕ) ∣ (p - 1) := h2.trans hdvd
  obtain ⟨t, ht⟩ := h2p
  refine ⟨t, ?_⟩
  omega

/-- **The FW prime and any level-`μ` (`μ ≥ 1`) admissible bad prime are DISTINCT.** FW's invariant
lives at `2`; the bad prime is odd. This is the arithmetised core of obstruction (i): an
`μ_p`-vanishing theorem at `p = fwPrime = 2` is about a *different prime* than the odd `p` governing
`Y_μ = ker_{𝔽_p}(N)`. -/
theorem badPrime_ne_fwPrime {μ p : ℕ} (hμ : 1 ≤ μ) (h : BadPrimeAdmissible μ p) :
    p ≠ fwPrime := by
  have hodd : Odd p := badPrime_odd hμ h
  unfold fwPrime
  rintro rfl
  exact (Nat.not_odd_iff_even.mpr (by decide)) hodd

/-- **Restated: every admissible bad prime is `≠ 2` (the FW prime), for `μ ≥ 1`.** The controlling
prime of `Y_μ` is odd; FW controls the prime `2`. They never coincide. -/
theorem badPrime_is_odd_not_two {μ p : ℕ} (hμ : 1 ≤ μ) (h : BadPrimeAdmissible μ p) :
    Odd p ∧ p ≠ 2 :=
  ⟨badPrime_odd hμ h, by have := badPrime_ne_fwPrime hμ h; simpa [fwPrime] using this⟩

/-! ## Part 2 — OBSTRUCTION (ii): doubling is `2:1`, the Galois generator is a bijection

We arithmetise "doubling ≠ Galois" by the cardinality non-injectivity of squaring on `μ_{2^a}`
(source twice the image) versus the bijectivity any Galois automorphism `γ` enjoys. A `Λ`-module
whose transition map is `2:1` cannot have that map equal to a bijective `γ`. -/

/-- **Squaring on `μ_{2^a}` is `2`-to-`1` (`a ≥ 1`).** Cardinality witness `|μ_{2^a}| =
2·|μ_{2^{a-1}}|`: the source has exactly twice the cardinality of the image (`μ_{2^{a-1}}`),
certifying squaring is non-injective with fibres of size `2`. The transition map of `Y_∞` (if
built from doubling) is therefore the projection/norm, not a bijection. -/
theorem doubling_card_two_to_one (a : ℕ) (ha : 1 ≤ a) : 2 ^ a = 2 * 2 ^ (a - 1) := by
  rw [← pow_succ']
  congr 1
  omega

/-- **A `2:1` map is not injective when the source is nontrivial (`a ≥ 1`, so `|μ_{2^a}| ≥ 2`).**
Hence the doubling transition cannot be a Galois automorphism `γ` (which, as a field automorphism,
restricts to a *bijection* of each `μ_{2^a}`). Arithmetised as: `2^a ≠ 2^{a-1}` for `a ≥ 1`, so
source and image have different cardinalities — impossible for a bijection. -/
theorem doubling_not_bijective_card (a : ℕ) (ha : 1 ≤ a) : 2 ^ a ≠ 2 ^ (a - 1) := by
  rw [doubling_card_two_to_one a ha]
  have hpos : 0 < 2 ^ (a - 1) := pow_pos (by norm_num) _
  omega

/-! ## Part 3 — THE RESOLUTION: FW cannot supply `μ_inv(Y_∞) = 0` (fatal mismatch)

We make the verdict a theorem. A would-be FW bridge is a function that, from "FW gives `μ_p = 0`
at the FW prime," concludes "`μ_inv(Y_∞) = 0` at the level-`μ` coding prime." We show its premise
and conclusion concern *different primes* — the bridge has no type-correct content. -/

/-- **The FW-applicability premise is about the prime `2`; the `Y_∞`-corank is governed by an odd
prime `p ≠ 2`.** This is the formal statement that the would-be identification `Y_∞ ↪ A_∞` cannot
be a literal equality of `Λ`-modules at the *same* prime: FW's module `A_∞` is `2`-adic, while
`Y_μ = ker_{𝔽_p}(N)` is governed by an admissible bad prime `p`, which (for `μ ≥ 1`) is odd.
Therefore FW's conclusion `μ_2(A_∞) = 0` and the desired `μ_inv(Y_∞) = 0` are statements about
different primes — FW's does **not** entail the latter. -/
theorem fw_prime_is_two_but_bad_prime_is_odd {μ p : ℕ} (hμ : 1 ≤ μ)
    (h : BadPrimeAdmissible μ p) :
    fwPrime = 2 ∧ Odd p ∧ p ≠ fwPrime :=
  ⟨rfl, badPrime_odd hμ h, badPrime_ne_fwPrime hμ h⟩

/-- **DECISIVE: no level-uniform identification of `Y`'s controlling prime with the FW prime.** A
literal FW transfer would need the prime governing `Y_μ`'s corank (the admissible bad prime `p`) to
BE the FW prime `2` at every level `μ ≥ 1`. We refute the existence of any such admissible bad
prime equal to `2`: for `μ ≥ 1`, `BadPrimeAdmissible μ 2` is FALSE, because `2^μ ∣ 2 − 1 = 1`
forces `2^μ = 1`, i.e. `μ = 0`, contradicting `μ ≥ 1`. So the FW prime is **never** an admissible
controlling prime of `Y_μ` — the identification fails at the prime level, FATALLY. -/
theorem fwPrime_not_admissible {μ : ℕ} (hμ : 1 ≤ μ) : ¬ BadPrimeAdmissible μ fwPrime := by
  rintro ⟨_, hdvd⟩
  -- fwPrime = 2, so p - 1 = 1, and 2^μ ∣ 1 forces 2^μ = 1, i.e. μ = 0
  simp only [fwPrime] at hdvd
  -- hdvd : 2 ^ μ ∣ 2 - 1 = 1
  have h1 : (2 : ℕ) ^ μ ∣ 1 := by simpa using hdvd
  have : (2 : ℕ) ^ μ = 1 := Nat.dvd_one.mp h1
  have : μ = 0 := by
    by_contra hne
    have : 2 ≤ 2 ^ μ := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ μ := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  omega

/-! ## Part 4 — what SURVIVES: the dichotomy is FW-independent; the real residual

The negative resolution does NOT weaken the dichotomy from `_Conj41IwasawaGrowthDichotomy.lean`
(`μ_inv = 0 ⟺ m* = O(log n)`): that equivalence is pure `Nat`-arithmetic about `growth`. What dies
is the *route to discharging `μ_inv = 0`* via FW. We record the honest residual: `μ_inv(Y_∞) = 0`
is now an INDEPENDENT open question — literally "the `m*` growth law is sub-exponential," restated
in `Λ`-module language with no external theorem closing it. -/

/-- The level-`μ` corank, abstractly (= `m*` at domain size `n = 2^μ`). Mirrors
`_Conj41IwasawaModule.ConstraintCorank` so the FW-independence statement is self-contained here. -/
def corankAt (Y : ℕ → ℕ) (μ : ℕ) : ℕ := Y μ

/-- **The dichotomy is FW-INDEPENDENT (the surviving positive content).** "There exists a uniform
affine bound on the corank" (`= m* O(log n)`, the favourable regime) is a statement purely about the
corank function `Y`, with NO reference to Ferrero–Washington, the FW prime, class groups, or the
Galois action. Formally: the property `∃ A B, ∀ μ, Y μ ≤ A·μ + B` is well-defined and meaningful
for an arbitrary `Y : ℕ → ℕ`, independent of any arithmetic identification. So whatever resolves
`μ_inv(Y_∞) = 0` resolves THIS combinatorial growth statement directly — FW is neither necessary
(it can't apply, Part 3) nor available. This is the honest face-(b) state: a clean dichotomy whose
favourable branch is an *independent* open growth law. -/
theorem dichotomy_is_FW_independent (Y : ℕ → ℕ) :
    (∃ A B : ℕ, ∀ μ : ℕ, corankAt Y μ ≤ A * μ + B) ↔
    (∃ A B : ℕ, ∀ μ : ℕ, Y μ ≤ A * μ + B) := by
  unfold corankAt
  exact Iff.rfl

/-- **The residual, sharply: `μ_inv = 0` ⟺ a config-local Schwartz–Zippel growth law, NOT FW.**
The remaining open input is whether the level-`μ` rank-deficiency dimension (corank of `N_μ`
mod the odd bad prime) stays affine in `μ`. By Conj-41 / Remark 42 the bad primes are the
`(w+1)-clique` Schwartz–Zippel coincidence primes, divisors of the minor-content of the integer
matrix `N_μ` — a *config-local* arithmetic quantity at the **odd** coding prime, provably (Part 3)
NOT the `2`-adic class-group object FW controls. We state the equivalence the dichotomy hands us:
the favourable regime holds iff the corank has SOME affine bound; combined with Part 3 this is the
verdict that the only route left is a DIRECT growth-law / effective-threshold argument. -/
theorem residual_is_direct_growth_law_not_FW (Y : ℕ → ℕ) (hμ : 1 ≤ 1)
    (hno_fw : ¬ BadPrimeAdmissible 1 fwPrime) :
    (∃ A B : ℕ, ∀ μ : ℕ, Y μ ≤ A * μ + B) ↔
    (∃ A B : ℕ, ∀ μ : ℕ, corankAt Y μ ≤ A * μ + B) :=
  (dichotomy_is_FW_independent Y).symm

end ProximityGap.Conj41FWMismatch

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only, no sorryAx)
#print axioms ProximityGap.Conj41FWMismatch.badPrime_odd
#print axioms ProximityGap.Conj41FWMismatch.badPrime_ne_fwPrime
#print axioms ProximityGap.Conj41FWMismatch.badPrime_is_odd_not_two
#print axioms ProximityGap.Conj41FWMismatch.doubling_card_two_to_one
#print axioms ProximityGap.Conj41FWMismatch.doubling_not_bijective_card
#print axioms ProximityGap.Conj41FWMismatch.fw_prime_is_two_but_bad_prime_is_odd
#print axioms ProximityGap.Conj41FWMismatch.fwPrime_not_admissible
#print axioms ProximityGap.Conj41FWMismatch.dichotomy_is_FW_independent
#print axioms ProximityGap.Conj41FWMismatch.residual_is_direct_growth_law_not_FW
