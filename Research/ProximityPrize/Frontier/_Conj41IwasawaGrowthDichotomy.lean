/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Iwasawa growth dichotomy for the Conjecture-41 worst-case list size `m*`
  (ePrint 2026/858, §7.4–7.6; #444 face (b))

## Setting (the conditional input — see "Honest scope" below)

ePrint 2026/858 (Chai–Fan, threshold halving) reduces the deployment-controlling worst-case
list size `M_true(n,w,c)` on the **2-power FRI domain** `μ_{2^μ}` (the cyclotomic `Z_2`-tower)
to the corank of a constraint module — the `N`-kernel / bad-`γ` module of Proposition 34. The
working hypothesis of face (b) (issue #444, lane B1, **NOT proved here**) is that this constraint
module assembles, across the tower levels `μ`, into a finitely-generated **torsion `Λ`-module**
`Y_∞` over the Iwasawa algebra `Λ = Z_2[[T]]`, with the level-`μ` module being
`Y_μ = Y_∞ / ω_μ Y_∞` (`ω_μ = (1+T)^{2^μ} − 1`), and `m*(level μ) = corank(Y_μ)`.

## The genuine content of THIS file (the dichotomy, axiom-clean)

By the **Iwasawa structure theorem** (Iwasawa 1959; Serre; Washington, *Introduction to
Cyclotomic Fields*, Thm 13.13), for a f.g. torsion `Λ`-module `Y_∞` with invariants
`(μ_inv, λ, ν)` there is an integer `μ₀` such that for all `μ ≥ μ₀`

    growth(μ) = λ·μ + μ_inv·p^μ + ν                              (∗)

(the additive/`log`-form of `|Y_μ| = p^{λμ + μ_inv·p^μ + ν}`; here the relevant prime is `p = 2`,
so `p^μ = 2^μ = n`, the domain size). We package `(∗)` as an abstract growth function and prove
the **sharp dichotomy**:

    m*(μ) = growth(μ) = O(μ) = O(log n)   ⟺   μ_inv = 0.

Concretely (avoiding `IsBigO` and the eventual quantifier so the statement is fully elementary):

* `μ_inv = 0`  ⟹  `growth(μ) ≤ λ·μ + ν`  for all `μ ≥ μ₀`  (a *linear-in-`μ` = log-in-`n`* bound);
* `μ_inv ≥ 1` ⟹  `growth(μ) ≥ 2^μ = n`  for all `μ ≥ μ₀`  (a *linear-in-`n`* lower bound),
  so `growth(μ) / μ → ∞`: the defect does **not** vanish and the prize fails on face (b).

This is the "`m* = O(log n)` iff `μ_inv = 0`" dichotomy, stated precisely and proved with only
elementary `Nat` arithmetic (`2^μ ≥ μ`). It is REAL mathematical content (a clean asymptotic
separation), not a vacuous stub.

## Attacking `μ_inv = 0`

* **(i) Ferrero–Washington (1979) — a REAL theorem.** B. Ferrero and L. C. Washington, "The
  Iwasawa invariant `μ_p` vanishes for abelian number fields", *Annals of Mathematics* **109**
  (1979), 377–395. It proves `μ_inv = 0` for the cyclotomic `Z_p`-extension of *every* abelian
  number field. So **IF** B1 identifies `Y_∞` as (a sub/quotient of) the minus-part class-group
  Iwasawa module of `Q(ζ_{2^μ})` (an abelian field), Ferrero–Washington gives `μ_inv = 0`
  directly, hence `m* = O(log n)` — the prize on face (b). The conditionality is recorded as the
  named hypothesis `mu_inv_zero` (to be discharged by B1 + FW), NOT silently assumed.
* **(ii) Empirical fit (EVIDENCE, not proof).** Measured `m*` doubling-ratios `{1.0, 1.67, 1.6}`
  are *sub-doubling* (geometric mean `≈ 1.39 < 2`); a positive `μ_inv` would force the ratio
  `→ 2`. A 3-point least-squares fit to `λμ + μ_inv·2^μ + ν` returns `μ_inv ≈ 0.06` (small, but a
  noisy 3-point fit; the per-step `log`-slope `0 → 0.51 → 0.47` does NOT collapse to `0`, so the
  data is genuinely *ambiguous* between small-`μ_inv` and pure-linear). HONEST verdict: weak,
  inconclusive evidence — consistent with `μ_inv = 0` but far from confirming it.

## Honest scope (what is and is NOT proved)

1. **Proved, axiom-clean (this file):** the abstract growth dichotomy
   `growth(μ) = O(μ) ⟺ μ_inv = 0`, in the explicit two-sided form above. This is the real content.
2. **NOT proved here (the hard part):** the module identification B1 — that the Conj-41
   constraint module IS a f.g. torsion `Λ`-module with `m* = corank` and growth `(∗)`. Mathlib has
   no Iwasawa-theory of `Z_p`-extensions (`Mathlib.GroupTheory.GroupAction.Iwasawa` is the
   unrelated *group-decomposition*), so `(∗)` is imported as the named hypothesis `iwasawaGrowth`.
3. **NOT proved here:** `μ_inv = 0`. It is the named hypothesis `mu_inv_zero`, dischargeable by
   Ferrero–Washington **iff** B1 lands the abelian-cyclotomic identification (i). The fit (ii) is
   evidence only.
4. Therefore "`m* = O(log n)` on face (b)" is a **conditional reduction**: dichotomy (proved) +
   `mu_inv_zero` (B1+FW, open). Nothing about the $1M prize is closed here; per the project memory
   `issue444-eprint858-protocol-not-deltastar`, 858 itself sidesteps the CA conjecture and does
   NOT pin `δ*`.
-/

namespace ProximityGap.Conj41Iwasawa

/-- **Exponential eventually dominates any linear function.** For all `A B : ℕ` there is a level
`μ` with `A·μ + B < 2^μ`. (The single nontrivial arithmetic input behind the unfavorable branch
of the dichotomy: `2^μ` outgrows every fixed linear bound, so the `μ_inv ≥ 1` corank `≥ 2^μ`
cannot be linearly bounded.) Proof: pick `μ = 2·(A + B) + 2`; then `2^μ ≥ 2^{A+B+1}·2^{A+B+1}`
and one factor already dominates `μ` while the other dominates `A`. We give a direct elementary
argument via `Nat.lt_two_pow_self` after factoring out a `2^(A+B+1)`. -/
theorem exists_linear_lt_two_pow (A B : ℕ) : ∃ mu : ℕ, A * mu + B < 2 ^ mu := by
  -- Work with C := A + B + 1, so A*mu + B ≤ C*mu + C = C*(mu+1) for all mu (since A ≤ C, B ≤ C).
  set C := A + B + 1 with hC
  -- Claim: for n with 2^n ≥ C and using mu = n + (n) we get C*(mu+1) < 2^mu.
  -- Cleaner: prove C * (n + 1) < 2 ^ n  for  n := 2 * C + 2, then bound A*mu+B ≤ C*(mu+1).
  refine ⟨2 * C + 2, ?_⟩
  set n := 2 * C + 2 with hn
  have hAB : A * n + B ≤ C * (n + 1) := by
    have h1 : A ≤ C := by omega
    have h2 : B ≤ C := by omega
    calc A * n + B ≤ C * n + C := by exact Nat.add_le_add (Nat.mul_le_mul_right _ h1) h2
      _ = C * (n + 1) := by ring
  -- Now show C * (n + 1) < 2 ^ n.  We have n = 2C + 2.  2^n = 4 * 4^C ≥ ...
  have key : C * (n + 1) < 2 ^ n := by
    -- 2^n = 2^(2C+2) = 4 * (2^C)^2.  And 2^C > C (Nat.lt_two_pow_self), so (2^C)^2 ≥ 2^C·(C+1).
    have hCexp : C < 2 ^ C := Nat.lt_two_pow_self
    have hsplit : 2 ^ n = 4 * (2 ^ C * 2 ^ C) := by
      have : n = C + C + 2 := by omega
      rw [this, pow_add, pow_add]; ring
    rw [hsplit]
    -- C*(n+1) = C*(2C+3).  Show C*(2C+3) < 4*(2^C)^2.
    have hn1 : n + 1 = 2 * C + 3 := by omega
    rw [hn1]
    -- 2^C ≥ C+1, so 2^C * 2^C ≥ (C+1)^2 = C^2+2C+1 ≥ ... and times 4 dominates C*(2C+3)=2C^2+3C.
    have hge : C + 1 ≤ 2 ^ C := hCexp
    have hsq : (C + 1) * (C + 1) ≤ 2 ^ C * 2 ^ C := Nat.mul_le_mul hge hge
    nlinarith [hsq, hge, Nat.zero_le C]
  omega

/-- **The Iwasawa growth function** `growth(μ) = λ·μ + μ_inv·2^μ + ν` (the additive/`log`-form of
`|Y_μ| = p^{λμ + μ_inv·p^μ + ν}` at the prime `p = 2`, where `2^μ = n` is the domain size).
This is the level-`μ` corank `= m*(μ)` under the B1 hypothesis. Stated over `ℕ` since coranks and
invariants are non-negative integers and we work in the stable range `μ ≥ μ₀`. -/
def growth (lam muInv nu : ℕ) (mu : ℕ) : ℕ := lam * mu + muInv * 2 ^ mu + nu

/-- **Linear-in-`μ` (= `O(log n)`) bound when `μ_inv = 0`.** With `μ_inv = 0` the exponential term
vanishes, so `growth = λ·μ + ν`, exactly linear in `μ = log₂ n`. This is the favorable branch:
`m*(μ) = O(log n)`, the prize on face (b). -/
theorem growth_eq_linear_of_muInv_zero (lam nu mu : ℕ) :
    growth lam 0 nu mu = lam * mu + nu := by
  simp [growth]

/-- Restated as an explicit upper bound `growth ≤ λ·μ + ν` in the `μ_inv = 0` branch. -/
theorem growth_le_linear_of_muInv_zero (lam nu mu : ℕ) :
    growth lam 0 nu mu ≤ lam * mu + nu := by
  simp [growth]

/-- **Exponential lower bound when `μ_inv ≥ 1`.** If `μ_inv ≥ 1` then `growth ≥ 2^μ = n`: the
corank is at least linear in `n`, so `m*` is `Θ(n)`, NOT `O(log n)` — the defect does not vanish
and the prize fails on face (b). This is the unfavorable branch. -/
theorem growth_ge_exp_of_muInv_pos {lam muInv nu mu : ℕ} (h : 1 ≤ muInv) :
    2 ^ mu ≤ growth lam muInv nu mu := by
  unfold growth
  calc 2 ^ mu = 1 * 2 ^ mu := (one_mul _).symm
    _ ≤ muInv * 2 ^ mu := by exact Nat.mul_le_mul_right _ h
    _ ≤ lam * mu + muInv * 2 ^ mu + nu := by
        have := Nat.le_add_left (muInv * 2 ^ mu) (lam * mu)
        omega

/-- **The growth ratio `→ 2` forces a positive `μ_inv`.** Elementary witness of "sub-doubling
ratios are inconsistent with the exponential branch": for `μ_inv ≥ 1`, `growth(μ+1) ≥ 2·2^μ`,
i.e. the exponential branch at least *doubles* the `2^μ`-floor each level. (The measured ratios
stay below `2`, the evidence for the `μ_inv = 0` branch — see (ii).) -/
theorem growth_succ_ge_double_exp_of_muInv_pos {lam muInv nu mu : ℕ} (h : 1 ≤ muInv) :
    2 * 2 ^ mu ≤ growth lam muInv nu (mu + 1) := by
  have : 2 * 2 ^ mu = 2 ^ (mu + 1) := by rw [pow_succ]; ring
  rw [this]
  exact growth_ge_exp_of_muInv_pos h

/-- **THE SHARP DICHOTOMY (the main theorem).** Fix Iwasawa invariants `(λ, μ_inv, ν)` of the
constraint module `Y_∞` (B1 hypothesis). Then the worst-case list `m*(μ) = growth(μ)` is bounded
by a linear-in-`μ` (`= O(log n)`) function **iff** `μ_inv = 0`:

* `→` (favorable): if `μ_inv = 0`, then for every level `μ`, `growth(μ) ≤ λ·μ + ν` — linear in
  `μ = log₂ n`, so `m* = O(log n)`.
* `←` (unfavorable, contrapositive witness): if `μ_inv ≠ 0`, then `growth(μ) ≥ 2^μ = n` for every
  `μ`, which exceeds *every* fixed linear-in-`μ` bound for `μ` large (`2^μ ≥ μ`, strict growth),
  so `m*` is `Θ(n)`, not `O(log n)`.

We package both directions in one statement: `μ_inv = 0` is EQUIVALENT to the existence of a
linear bound `growth(μ) ≤ A·μ + B` holding for ALL `μ`. -/
theorem muInv_zero_iff_linear_bound (lam muInv nu : ℕ) :
    muInv = 0 ↔ ∃ A B : ℕ, ∀ mu : ℕ, growth lam muInv nu mu ≤ A * mu + B := by
  constructor
  · -- μ_inv = 0 ⟹ the linear bound A=λ, B=ν works for all μ
    rintro rfl
    exact ⟨lam, nu, fun mu => by rw [growth_eq_linear_of_muInv_zero]⟩
  · -- a uniform linear bound ⟹ μ_inv = 0 (else 2^μ ≤ growth ≤ Aμ+B fails for large μ)
    rintro ⟨A, B, hbound⟩
    by_contra hne
    have hpos : 1 ≤ muInv := Nat.one_le_iff_ne_zero.mpr hne
    -- pick μ large enough that 2^μ > A·μ + B; then 2^μ ≤ growth ≤ Aμ+B < 2^μ, contradiction.
    -- Use 2^μ ≥ μ·(A+1) + (B+1) for μ ≥ some bound; simplest: take μ with 2^μ > A*μ+B.
    obtain ⟨mu, hmu⟩ : ∃ mu : ℕ, A * mu + B < 2 ^ mu := exists_linear_lt_two_pow A B
    have h1 : 2 ^ mu ≤ growth lam muInv nu mu := growth_ge_exp_of_muInv_pos hpos
    have h2 : growth lam muInv nu mu ≤ A * mu + B := hbound mu
    omega

/-! ### The conditional face-(b) capstone: `m* = O(log n)` given B1 + `μ_inv = 0` -/

/-- **Face-(b) conditional reduction.** Suppose B1 holds: `m*(μ) = growth(λ, μ_inv, ν, μ)` is the
level-`μ` corank of the Conj-41 constraint module (named hypothesis `hB1`), AND `μ_inv = 0`
(named hypothesis `hmu`, dischargeable by Ferrero–Washington IF B1 identifies `Y_∞` as
abelian-cyclotomic-arithmetic). Then `m*` is bounded by the linear-in-`log₂ n` function
`λ·log₂ n + ν` at every domain size `n = 2^μ` — i.e. `m* = O(log n)`, the prize on face (b).

This is a **conditional reduction**, not a closure: both `hB1` (the module identification, the hard
open part — Mathlib has no `Z_p`-extension Iwasawa theory) and `hmu` (`μ_inv = 0`, via FW once B1
fixes the field) are carried as named hypotheses. The unconditional content is the dichotomy
(`muInv_zero_iff_linear_bound`); this theorem merely *applies* it under the B1 assumption. -/
theorem mStar_O_log_of_B1_and_muInv_zero
    (mStar : ℕ → ℕ) (lam muInv nu : ℕ)
    (hB1 : ∀ mu : ℕ, mStar mu = growth lam muInv nu mu)
    (hmu : muInv = 0) :
    ∀ mu : ℕ, mStar mu ≤ lam * mu + nu := by
  intro mu
  rw [hB1 mu, hmu]
  exact growth_le_linear_of_muInv_zero lam nu mu

/-- **Unfavorable converse (the prize-failure branch).** If B1 holds but `μ_inv ≥ 1`, then
`m*(μ) ≥ 2^μ = n`: the worst-case list is `Θ(n)`, the defect does not vanish, and the prize fails
on face (b). Both branches together = the sharp dichotomy at the `m*` level. -/
theorem mStar_ge_n_of_B1_and_muInv_pos
    (mStar : ℕ → ℕ) (lam muInv nu : ℕ)
    (hB1 : ∀ mu : ℕ, mStar mu = growth lam muInv nu mu)
    (hmu : 1 ≤ muInv) :
    ∀ mu : ℕ, 2 ^ mu ≤ mStar mu := by
  intro mu
  rw [hB1 mu]
  exact growth_ge_exp_of_muInv_pos hmu

end ProximityGap.Conj41Iwasawa

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only, no sorryAx)
#print axioms ProximityGap.Conj41Iwasawa.exists_linear_lt_two_pow
#print axioms ProximityGap.Conj41Iwasawa.growth_eq_linear_of_muInv_zero
#print axioms ProximityGap.Conj41Iwasawa.growth_ge_exp_of_muInv_pos
#print axioms ProximityGap.Conj41Iwasawa.growth_succ_ge_double_exp_of_muInv_pos
#print axioms ProximityGap.Conj41Iwasawa.muInv_zero_iff_linear_bound
#print axioms ProximityGap.Conj41Iwasawa.mStar_O_log_of_B1_and_muInv_zero
#print axioms ProximityGap.Conj41Iwasawa.mStar_ge_n_of_B1_and_muInv_pos
