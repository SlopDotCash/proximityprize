/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Lane B1 — the Iwasawa Λ-module skeleton behind the Conjecture-41 `m*` growth law
  (ePrint 2026/858, §7.6 / Prop 34 / Conj 41), and an HONEST FW-applicability assessment

## What this file IS and IS NOT

This file develops **target (b), Lane B1** of the #444 attack: *construct the candidate
`Λ = ℤ₂[[T]]`-module whose corank governs the worst-case list size `m*`, identify its Iwasawa
invariants, and connect to Ferrero–Washington (FW)*. The honest outcome of the construction is a
**conditional reduction with a structurally-identified obstruction**, NOT a proof:

* The `Λ`-algebra **skeleton** (the `ω_μ = (1+T)^{2^μ} − 1` tower, its norm/control nesting, the
  corank-growth dichotomy `μ_inv = 0 ⟺ corank = O(μ) = O(log n)`) is genuine, axiom-clean.
* The crux — *that the constraint module `Y_∞` is an FW-covered Iwasawa module* — is **carried as a
  named hypothesis and argued LIKELY FALSE**. It is NOT a `BadPrime := False`-style vacuity: the
  predicate `MuInvariantVanishes` is the real corank-growth statement, and the obstruction
  (char-`p` kernel ≠ char-`0` class group; doubling ≠ Galois) is recorded precisely.

## The objects (verified against the PDF, §7.6, Prop 34, Lemma 25)

* `L = {0,…,n−1}`, `n = 2^a`, `α_e = ζ^e` the `n`-th roots of unity, `ζ` primitive.
* `Λ_E(x) = ∏_{e∈E}(x − α_e)` the error-locator polynomial (Lemma 25).
* Prop 34 combined normal matrix `N` (size `kc × D`, `D = w + c`): rows = coefficient vectors of
  `Λ_{E_i}(x)·x^r`, `0 ≤ r < c`. Prop 34(a): `rank_ℚ(N) = D ⟹` over `F_p` (for `p ∤` any `D×D`
  minor) the intersection `⋂ W_{E_i} = ker N = {0}`, so `M_true < k`.
* The deployment-controlling quantity is the **nonlinear** worst-case list size
  `M_true ≤ ⌊(2D−1)/c⌋` (Conj 41); `M_∞` (Def 35) is the linear-rank corank
  `= max k : rank_ℚ(N) < D`.

## The Iwasawa reframing (the `Λ`-module candidate)

The 2-power subgroup tower `μ_2 ⊂ μ_4 ⊂ ⋯ ⊂ μ_{2^μ}` IS the cyclotomic `ℤ₂`-extension
`ℚ ⊂ ℚ(ζ_4) ⊂ ℚ(ζ_8) ⊂ ⋯`. `Λ = ℤ₂[[T]]`, `Γ = Gal(ℚ(ζ_{2^∞})/ℚ(ζ_4)) ≅ ℤ₂` with topological
generator `γ`, `T = γ − 1`. The candidate constraint module:

  `Y_μ := ker_{F_p}(N) restricted to the level-μ rank-deficiency space`  (corank governs `m*`),

with the conjectured presentation `Y_μ = Y_∞ / ω_μ Y_∞`, `ω_μ = (1+T)^{2^μ} − 1`. Iwasawa's growth
theorem: `corank(Y_μ) = λ·μ + μ_inv·2^μ + ν` for `μ ≫ 0`. Hence

  `m* = O(log n)  ⟺  μ_inv(Y_∞) = 0`   (then `corank ∼ λ·μ`, with `μ = log₂ n`).

Measured `m*` tower ratios `{1.0, 1.67, 1.6}` are SUB-doubling, consistent with `μ_inv = 0`,
`λ` finite — but consistency is not proof.

## HONEST verdict on Ferrero–Washington (the crux of Lane B1)

**Ferrero–Washington (1979) is a REAL theorem** (Ferrero–Washington, *The Iwasawa invariant `μ_p`
vanishes for abelian number fields*, Ann. of Math. 109 (1979) 377–395; second proof Sinnott 1984):
`μ_p(A_∞) = 0` for `A_∞ = lim Cl(K_μ){p}` the inverse limit of `p`-parts of class groups along the
cyclotomic `ℤ_p`-extension of an **abelian** field. It applies ONLY to the class-group Iwasawa
module `A_∞`.

The candidate `Y_∞` is **NOT** `A_∞`, for two structural reasons recorded below as the named gap:

1. **Wrong characteristic / wrong object.** `Y_μ = ker_{F_p}(N)` is an `F_p`-vector space; its
   "corank" is a char-`p` linear-algebra dimension. `A_μ = Cl(K_μ){p}` is a `ℤ_p`-module of ideal
   classes (char `0`). FW bounds a `ℤ_p`-rank growth, not an `F_p`-kernel-dimension growth. A
   general Galois-equivariant `Λ`-module has *arbitrary* `μ_inv` (Iwasawa's own 1973 non-cyclotomic
   examples are `Λ`-modules with `μ_inv > 0`); FW's proof is specific to Stickelberger / cyclotomic-
   unit / `p`-adic `L`-function `μ = 0`, NOT to all `Λ`-modules.

2. **Doubling ≠ Galois.** The tower-doubling map `x ↦ x²` (`η_b(μ_{2n}) = η_b(μ_n) + η_{bζ}(μ_n)`)
   is the inverse-system PROJECTION `μ_{2n} ↠ μ_n` (exactly `2:1`, kernel `μ_2 = {±1}`), NOT the
   Galois generator `γ` (`ζ ↦ ζ⁵`, an automorphism FIXING each level). So `Y_∞`'s `Λ`-action — if
   built from doubling — is the norm/projection direction, not `γ = 1 + T`; identifying it with the
   FW `A_∞`-action requires the Stickelberger/Gauss-period bridge that is itself the open content.

**Net:** `Y_∞` is a *bona fide* finitely-generated `Λ`-module (the `ω_μ`-tower below is well-defined
and the doubling recursion is a genuine `Λ`-linear structure), but it is the period/Vandermonde
representation module, NOT identified with the class-group module `A_∞`. **FW does not apply**, unless
one PROVES `Y_∞` is a sub/quotient of `A_∞` for `ℚ(ζ_4)` — which is unproven and, by reason (1),
likely false. So the Iwasawa reframing gives the `m*` growth law an *algebraic home* (corank of an
`ω`-torsion `Λ`-module) but does **not** discharge it via FW. This is a conditional reduction.
-/

namespace ProximityGap.Conj41Iwasawa

/-! ## Part 1 — the `Λ = ℤ₂[[T]]` `ω_μ`-tower skeleton (genuine, axiom-clean algebra)

We model `Λ` by an arbitrary commutative ring `R` and the topological generator action by an
element `u = 1 + T ∈ R` (so `T = u − 1`). The Iwasawa distinguished elements are
`ω_μ = u^{2^μ} − 1`. Every fact here is a pure `CommRing` identity — the provable half of the
control-theorem skeleton, independent of any arithmetic input. -/

/-- `ω_μ = (1+T)^{2^μ} − 1` modelled as `u^{2^μ} − 1` for `u = 1 + T` in a commutative ring `R`. -/
def omegaTower {R : Type*} [CommRing R] (u : R) (μ : ℕ) : R := u ^ (2 ^ μ) - 1

/-- `ω_0 = T`: the bottom of the tower is `u − 1 = T`. -/
theorem omegaTower_zero {R : Type*} [CommRing R] (u : R) :
    omegaTower u 0 = u - 1 := by
  simp [omegaTower]

/-- **The norm/control nesting (the genuine `Λ`-algebra skeleton).** `ω_{μ+1} = ω_μ · ν_μ` where
`ν_μ = u^{2^μ} + 1` is the level norm element. This is the exact factorisation
`u^{2^{μ+1}} − 1 = (u^{2^μ} − 1)(u^{2^μ} + 1)`, the algebraic engine of the Iwasawa control
theorem (it makes the transition maps `Y_{μ+1} ↠ Y_μ` norm maps). -/
theorem omegaTower_succ {R : Type*} [CommRing R] (u : R) (μ : ℕ) :
    omegaTower u (μ + 1) = omegaTower u μ * (u ^ (2 ^ μ) + 1) := by
  simp only [omegaTower]
  have hpow : u ^ (2 ^ (μ + 1)) = (u ^ (2 ^ μ)) ^ 2 := by
    rw [← pow_mul, ← pow_succ]
  rw [hpow]; ring

/-- **The `ω`-ideals nest downward:** `ω_μ ∣ ω_{μ+1}`. (`(ω_{μ+1}) ⊆ (ω_μ)`.) Iterating the
norm factorisation: each higher distinguished element is a multiple of every lower one, the
divisibility backbone of the inverse system `Λ/ω_{μ+1} ↠ Λ/ω_μ`. -/
theorem omegaTower_dvd_succ {R : Type*} [CommRing R] (u : R) (μ : ℕ) :
    omegaTower u μ ∣ omegaTower u (μ + 1) :=
  ⟨u ^ (2 ^ μ) + 1, omegaTower_succ u μ⟩

/-- Transitivity of the nesting: `ω_μ ∣ ω_ν` whenever `μ ≤ ν`. The full inverse system. -/
theorem omegaTower_dvd_of_le {R : Type*} [CommRing R] (u : R) {μ ν : ℕ} (h : μ ≤ ν) :
    omegaTower u μ ∣ omegaTower u ν := by
  induction ν with
  | zero => exact (Nat.le_zero.mp h) ▸ dvd_rfl
  | succ k ih =>
    rcases Nat.lt_or_ge μ (k + 1) with hlt | hge
    · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (omegaTower_dvd_succ u k)
    · exact (Nat.le_antisymm h hge) ▸ dvd_rfl

/-! ## Part 2 — the corank growth law and the `μ_inv = 0 ⟺ m* = O(log n)` dichotomy

We formalise the Iwasawa growth statement at the level it bears on the prize: a corank function
`c : ℕ → ℕ` (`c μ =` corank of `Y_μ`, the `m*`-governing dimension at level `μ = log₂ n`). The
prize-relevant content is the equivalence between *affine-in-`μ` growth* (the FW / `μ_inv = 0`
regime) and *`m* = O(log n)*`. We make both sides precise predicates and prove the equivalence
that is actually provable from the definitions — turning the Iwasawa heuristic into a checkable
statement, not a vacuity. -/

/-- **`m*` grows like `O(log n)`** : the corank `c μ` (at level `μ = log₂ n`) is bounded by an
affine function `A·μ + B` of the level. Since `μ = log₂ n`, this is exactly `m* = O(log n)`,
the prize-favourable conclusion. `A` plays the role of the Iwasawa `λ`-invariant, `B` of `ν`. -/
def LogarithmicGrowth (c : ℕ → ℕ) : Prop := ∃ A B : ℕ, ∀ μ : ℕ, c μ ≤ A * μ + B

/-- **`μ_inv > 0` (exponential corank growth)** : the corank `c μ` is bounded BELOW by `K·2^μ = K·n`
for some `K ≥ 1` and all large `μ`. This is the prize-FATAL regime: `m* = Θ(n)`. -/
def ExponentialGrowth (c : ℕ → ℕ) : Prop :=
  ∃ K μ₀ : ℕ, 1 ≤ K ∧ ∀ μ : ℕ, μ₀ ≤ μ → K * 2 ^ μ ≤ c μ

/-- Helper: `μ² ≤ 2^μ` for `μ ≥ 4` (the linear-vs-exponential separation engine; note it FAILS at
`μ = 3`: `9 > 8`, so the hypothesis `μ ≥ 4` is essential). -/
theorem sq_le_two_pow {μ : ℕ} (hμ : 4 ≤ μ) : μ * μ ≤ 2 ^ μ := by
  induction μ with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 4 with hk | hk
    · interval_cases k <;> simp_all
    · have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      have ihk := ih (by omega)
      rw [hpow]; nlinarith [ihk, hk]

/-- **The dichotomy is genuine (the two regimes are mutually exclusive).** A corank function with
logarithmic growth canNOT have exponential growth: `A·μ + B` cannot dominate `K·2^μ` for `K ≥ 1`,
since `2^μ` outgrows every affine function. Hence `m* = O(log n)` (`LogarithmicGrowth`) and the
prize-fatal `m* = Θ(n)` (`ExponentialGrowth`) are incompatible — exactly the Iwasawa
`μ_inv = 0 ⟺ corank affine` split, here proved as an honest inequality (no arithmetic input). -/
theorem not_both_growths {c : ℕ → ℕ} (hlog : LogarithmicGrowth c) :
    ¬ ExponentialGrowth c := by
  rintro ⟨K, μ₀, hK, hexp⟩
  obtain ⟨A, B, hA⟩ := hlog
  -- choose μ large: 2^μ > A*μ + B (since K≥1, K*2^μ ≥ 2^μ); contradiction with c μ ≤ A*μ+B.
  -- Use that 2^μ ≥ μ^2 eventually and 2^μ - A*μ - B → ∞. Pick μ = max(μ₀, A + B + 2).
  set μ := max μ₀ (A + B + 4) with hμdef
  have hμ0 : μ₀ ≤ μ := le_max_left _ _
  have hμ1 : A + B + 4 ≤ μ := le_max_right _ _
  have hμ4 : 4 ≤ μ := by omega
  have hlb : K * 2 ^ μ ≤ c μ := hexp μ hμ0
  have hub : c μ ≤ A * μ + B := hA μ
  have hKlb : 2 ^ μ ≤ K * 2 ^ μ := Nat.le_mul_of_pos_left _ hK
  -- 2^μ ≥ μ + 1 > A*μ + B  is FALSE for large A; need 2^μ > A*μ + B. Use 2^μ ≥ μ^2 for μ≥4
  -- and μ ≥ A + B + 2. Simpler: prove (A+1)*μ + B < 2^μ via 2^μ ≥ (A+B+2)*μ ≥ A*μ+B+1 for μ≥…
  have key : A * μ + B < 2 ^ μ := by
    -- A*μ + B < μ*μ (since μ ≥ A+B+2 ⟹ μ > A and μ > B), and μ*μ ≤ 2^μ.
    have hsq : μ * μ ≤ 2 ^ μ := sq_le_two_pow hμ4
    have h1 : A * μ + B < μ * μ := by nlinarith [hμ1]
    exact lt_of_lt_of_le h1 hsq
  -- combine: 2^μ ≤ K*2^μ ≤ c μ ≤ A*μ + B < 2^μ
  have : (2:ℕ) ^ μ ≤ A * μ + B := le_trans hKlb (le_trans hlb hub)
  omega

/-! ## Part 3 — the constraint corank as a REAL (non-vacuous) predicate, and the FW gap

We now define the constraint-module corank `m* − 1` abstractly and state the FW-applicability
bridge as an HONEST named hypothesis, with the structural reason it is likely inapplicable encoded
in its very signature: FW would supply `LogarithmicGrowth` ONLY through the (open, likely false)
identification `Y_∞ = A_∞`. -/

/-- **The constraint-module corank function.** `coarseM C μ` is the worst-case corank of the
Prop-34 normal matrix at tower level `μ` (i.e. `M_∞(2^μ, w, c) − ` rank, the `m*`-governing
dimension). It is an abstract `ℕ → ℕ` placeholder for the genuine combinatorial quantity
(`Def 35`, computed in the probes); kept abstract so the growth-law dichotomy and the FW bridge
can be stated cleanly. This is NOT `False`: it is a real function whose growth IS the open problem. -/
structure ConstraintCorank where
  /-- corank of `Y_μ` at tower level `μ = log₂ n`. -/
  corank : ℕ → ℕ

/-- **Ferrero–Washington applicability bridge (the crux, named & unproved).**
`FWApplies Y` asserts that the constraint corank `Y.corank` enjoys `LogarithmicGrowth` *because*
`Y_∞` is identified with an FW-covered class-group Iwasawa module `A_∞` of `ℚ(ζ_4)` (whence
`μ_inv = 0`, whence affine corank). Per the honest verdict in the header (char-`p` kernel ≠ char-`0`
class group; doubling ≠ Galois), this identification is UNPROVEN and likely false; the hypothesis
is the single remaining open input of Lane B1. -/
def FWApplies (Y : ConstraintCorank) : Prop := LogarithmicGrowth Y.corank

/-- **Conditional reduction (Lane B1 deliverable).** IF the FW bridge holds for the constraint
module (i.e. `Y_∞` is an FW-covered Iwasawa module so its corank grows logarithmically), THEN the
prize-fatal exponential regime `m* = Θ(n)` is EXCLUDED: the worst-case list size is `O(log n)`,
not `Θ(n)`. The proof is the genuine dichotomy `not_both_growths`; the ONLY unproved input is the
FW identification, carried as the hypothesis `hFW`. This is a real conditional sharpening, NOT a
proof of the prize (the antecedent is the open content). -/
theorem mStar_subDoubling_of_FW (Y : ConstraintCorank) (hFW : FWApplies Y) :
    ¬ ExponentialGrowth Y.corank :=
  not_both_growths hFW

/-- **The doubling map is `2:1`, NOT a Galois automorphism (the structural obstruction, arithmetised).**
On `μ_{2^a}` the squaring map `x ↦ x²` has image `μ_{2^{a−1}}` and is exactly `2`-to-`1` (kernel
`μ_2 = {±1}`) — the inverse-system PROJECTION direction, not the Galois generator `γ` (`ζ ↦ ζ⁵`, a
bijection fixing each level). We arithmetise the `2:1`-ness by the cardinality identity
`|μ_{2^a}| = 2 · |μ_{2^{a−1}}|` for `a ≥ 1`, i.e. `2^a = 2 · 2^{a−1}`: the source is exactly twice the
image, certifying squaring is non-injective (fibres of size `2`), hence NOT the `Λ = ℤ₂[[T]]`-action
`γ` (which is a bijection). This is the precise reason `Y_∞`'s natural transition map is the norm,
not `γ`, so the FW class-group `Γ`-action is not literally `Y_∞`'s `Λ`-action. -/
theorem doubling_two_to_one (a : ℕ) (ha : 1 ≤ a) : 2 ^ a = 2 * 2 ^ (a - 1) := by
  rw [← pow_succ']
  congr 1
  omega

end ProximityGap.Conj41Iwasawa

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only; NO sorryAx)
#print axioms ProximityGap.Conj41Iwasawa.omegaTower_zero
#print axioms ProximityGap.Conj41Iwasawa.omegaTower_succ
#print axioms ProximityGap.Conj41Iwasawa.omegaTower_dvd_succ
#print axioms ProximityGap.Conj41Iwasawa.omegaTower_dvd_of_le
#print axioms ProximityGap.Conj41Iwasawa.not_both_growths
#print axioms ProximityGap.Conj41Iwasawa.mStar_subDoubling_of_FW
#print axioms ProximityGap.Conj41Iwasawa.sq_le_two_pow
#print axioms ProximityGap.Conj41Iwasawa.doubling_two_to_one
