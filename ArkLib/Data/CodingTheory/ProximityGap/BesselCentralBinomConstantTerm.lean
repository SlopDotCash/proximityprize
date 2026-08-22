/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungBesselEnergy
import Mathlib.Data.Nat.Choose.Central

/-!
# The central-binomial constant-term core of the Bessel even-moment law (#407)

This file formalizes the **combinatorial core (Step 3)** of the Bessel even-moment law

  `E_r^{char0}(μ_n) = (2r)!·[x^r] I₀(2√x)^{n/2}`,

namely the constant-term-to-central-binomials identity that turns the analytic Bessel
coefficient into a pure central-binomial sum.

## The setup (from the #407 Bessel-law proof)

With `n = 2^μ`, `ζ = ζ_n`, the power basis `{1, ζ, …, ζ^{n/2-1}}` is a `ℚ`-basis of
`ℚ(ζ_n)` (degree `φ(2^μ) = n/2`), and `ζ^{n/2} = -1`.  So each `ζ^a` is a *signed unit
vector* `±e_j`, and the char-0 additive energy of the *multiplicative* group `μ_n` equals
the *additive* energy of the signed-unit-vector set `{±e_j : j < n/2}`:

  `E_r^{char0}(μ_n) = [z^0]( Σ_{j<n/2} (z_j + z_j^{-1}) )^{2r}`.

Setting `d = n/2`, the multinomial expansion of this constant term requires each
coordinate exponent even (`α_j = 2β_j`, `Σβ_j = r`), with per-coordinate constant term
`[z_j^0](z_j + z_j^{-1})^{2β_j} = C(2β_j, β_j) = centralBinom β_j`, weighted by the
level-`2r` multinomial `(2r)!/∏_j (2β_j)!`:

  `[z^0](…)^{2r} = Σ_{|β|=r} ((2r)!/∏_j (2β_j)!)·∏_j centralBinom β_j`.

The Bessel coefficient `besselCoeff d r` (defined in `RungBesselEnergy.lean`) is the
factorial-square form `Σ_{|β|=r} ∏_j 1/(β_j!)²`.

## What this file proves

The **load-bearing identity** of Step 3, per coordinate, is

  `centralBinom β · (β!)² = (2β)!`               (`centralBinom_mul_sq_factorial`)

(a specialization of `Nat.choose_mul_factorial_mul_factorial`), equivalently over `ℚ`

  `(1 : ℚ)/(β!)² = centralBinom β / (2β)!`        (`one_div_sq_factorial_eq`),

which converts each factorial-square Bessel term into central-binomial constant-term
form.  Summed and multiplied through by `(2r)!`, this is the Step-3 identity

  `(2r)!·besselCoeff d r
      = Σ_{|β|=r} ((2r)!/∏_j (2β_j)!)·∏_j centralBinom β_j`
                                          (`besselCoeff_eq_centralBinom_sum`),

the central-binomial constant-term form with the Laurent-polynomial bookkeeping replaced
by exact `ℚ`-arithmetic.  No characters, no characteristic-`p` content: this is the char-0
additive-energy combinatorial core of the Bessel reduction.

## Verification

Probe-verified exact against direct collision enumeration of `E_r^{char0}(μ_n)`
(`d∈{2,4,8}`, `r∈{2,3,4}`): e.g. `(2r)!·besselCoeff 4 2 = 168`,
`(2r)!·besselCoeff 8 3 = 50560`, `(2r)!·besselCoeff 2 4 = 4900`.

All theorems depend only on `[propext, Classical.choice, Quot.sound]`.
-/

open Finset BigOperators

namespace ProximityGap.PrizeWorkbench

/-- **The load-bearing per-coordinate identity (`ℕ`):**
`centralBinom β · (β!)² = (2β)!`.  This is `Nat.choose_mul_factorial_mul_factorial`
specialized to the central case `n = 2β, k = β`.  It is the exact statement
`[z^0](z + z^{-1})^{2β}·(β!)² = (2β)!` that powers Step 3 of the Bessel even-moment law. -/
theorem centralBinom_mul_sq_factorial (β : ℕ) :
    Nat.centralBinom β * (Nat.factorial β) ^ 2 = Nat.factorial (2 * β) := by
  have h := Nat.choose_mul_factorial_mul_factorial
    (Nat.le_mul_of_pos_left β (by norm_num : 0 < 2))
  -- h : (2*β).choose β * β! * (2*β - β)! = (2*β)!
  rw [Nat.centralBinom_eq_two_mul_choose]
  have hsub : 2 * β - β = β := by omega
  rw [hsub] at h
  rw [pow_two, ← Nat.mul_assoc]
  exact h

/-- **The load-bearing per-coordinate identity (`ℚ`):**
`(1 : ℚ)/(β!)² = centralBinom β / (2β)!`.  Converts the factorial-square Bessel term
into central-binomial constant-term form, one coordinate at a time. -/
theorem one_div_sq_factorial_eq (β : ℕ) :
    (1 : ℚ) / (Nat.factorial β) ^ 2
      = (Nat.centralBinom β : ℚ) / (Nat.factorial (2 * β)) := by
  have hfac2_pos : (0 : ℚ) < (Nat.factorial (2 * β) : ℚ) := by
    exact_mod_cast Nat.factorial_pos (2 * β)
  have hsq_pos : (0 : ℚ) < (Nat.factorial β : ℚ) ^ 2 := by positivity
  rw [div_eq_div_iff (ne_of_gt hsq_pos) (ne_of_gt hfac2_pos), one_mul]
  -- goal: (2β)! = centralBinom β * (β!)²
  have key : (Nat.factorial (2 * β) : ℚ)
      = (Nat.centralBinom β : ℚ) * (Nat.factorial β : ℚ) ^ 2 := by
    have h0 := centralBinom_mul_sq_factorial β
    have h1 : ((Nat.centralBinom β * (Nat.factorial β) ^ 2 : ℕ) : ℚ)
        = (Nat.factorial (2 * β) : ℚ) := by exact_mod_cast h0
    push_cast at h1
    linarith [h1]
  rw [key]

/-- **Step 3 (central-binomial constant-term form), per multi-index `β`:**
`(2r)! · ∏_j 1/(β_j!)² = ((2r)!/∏_j (2β_j)!) · ∏_j centralBinom β_j`.
The factorial-square Bessel weight of `β` equals its central-binomial constant-term
weight. -/
theorem besselTerm_mul_eq_centralBinomTerm {d r : ℕ} (β : Fin d → ℕ) :
    (Nat.factorial (2 * r) : ℚ) * ∏ j, (1 : ℚ) / (Nat.factorial (β j)) ^ 2
      = ((Nat.factorial (2 * r) : ℚ) / ∏ j, (Nat.factorial (2 * β j) : ℚ))
          * ∏ j, (Nat.centralBinom (β j) : ℚ) := by
  have hprod : ∏ j, (1 : ℚ) / (Nat.factorial (β j)) ^ 2
      = ∏ j, (Nat.centralBinom (β j) : ℚ) / (Nat.factorial (2 * β j)) := by
    apply Finset.prod_congr rfl
    intro j _
    exact one_div_sq_factorial_eq (β j)
  rw [hprod, Finset.prod_div_distrib]
  ring

/-- **The Bessel coefficient in central-binomial constant-term form (Step 3 summed):**
`(2r)! · besselCoeff d r = Σ_{|β|=r} ((2r)!/∏_j (2β_j)!) · ∏_j centralBinom β_j`.

The RHS is the level-`2r` constant term `[z^0](Σ_j (z_j + z_j^{-1}))^{2r}` written via
central binomials — the pure-combinatorial Step 3 of the Bessel even-moment law, with the
Laurent-polynomial bookkeeping replaced by exact `ℚ`-arithmetic.  No characters, no
characteristic-`p` content; this is the char-0 additive-energy combinatorial core. -/
theorem besselCoeff_eq_centralBinom_sum (d r : ℕ) :
    (Nat.factorial (2 * r) : ℚ) * besselCoeff d r
      = ∑ β ∈ Finset.Nat.antidiagonalTuple d r,
          ((Nat.factorial (2 * r) : ℚ) / ∏ j, (Nat.factorial (2 * β j) : ℚ))
            * ∏ j, (Nat.centralBinom (β j) : ℚ) := by
  unfold besselCoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  exact besselTerm_mul_eq_centralBinomTerm β

/-- **The `r = 0` normalization anchor of the Bessel even-moment ladder.**
At rung `r = 0`, `antidiagonalTuple d 0 = {0}` (the single zero tuple), so each
per-coordinate factor is `1/(0!)² = 1` (Bessel) resp. `1/0! = 1` (Gaussian), and the
product over the `d` coordinates is `1`.  Hence both the Bessel coefficient
`besselCoeff d 0 = [x⁰] I₀(2√x)^d` and the Gaussian coefficient
`gaussianCoeff d 0 = [x⁰] e^{d x²}` normalize to `1`.  This pins the base case of the
even-moment recursion `E_r^{char0}(μ_n) = (2r)!·[x^r] I₀(2√x)^{n/2}`. -/
theorem besselCoeff_zero_and_gaussianCoeff_zero (d : ℕ) :
    besselCoeff d 0 = 1 ∧ gaussianCoeff d 0 = 1 := by
  constructor
  · unfold besselCoeff
    rw [Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton]
    simp [Nat.factorial_zero, Finset.prod_const_one]
  · unfold gaussianCoeff
    rw [Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton]
    simp [Nat.factorial_zero, Finset.prod_const_one]


/-- **Sign anchor for the Bessel coefficient**: `0 ≤ besselCoeff d r`.
`besselCoeff d r = Σ_{|m|=r} ∏_i 1/(mᵢ!)²` is a sum over the antidiagonal tuple of
products of factors `1/(mᵢ!)² ≥ 0`, hence nonnegative.  This pins the sign of the exact
char-0 additive-energy coefficient `[x^{2r}]I₀(2x)^d` (so `(2r)!·besselCoeff d r =
E_r^{char0}(μ_n) ≥ 0`), the trivial-but-load-bearing positivity baseline of the Bessel
even-moment law (#407). -/
theorem besselCoeff_nonneg (d r : ℕ) : 0 ≤ besselCoeff d r := by
  unfold besselCoeff
  apply Finset.sum_nonneg
  intro x _
  apply Finset.prod_nonneg
  intro i _
  positivity


/-- **Strict positivity of the Bessel coefficient (energy non-degeneracy baseline):**
`0 < besselCoeff d r` for `d ≥ 1`.  Since `(2r)!·besselCoeff d r = E_r^{char0}(μ_n)`
(the exact char-0 additive-energy coefficient of the multiplicative group `μ_n`, with
`d = n/2`), this is the strict non-degeneracy statement `E_r^{char0}(μ_n) > 0`: the
energy of any nonempty signed-unit-vector set is strictly positive.

`besselCoeff d r = Σ_{m ∈ antidiagonalTuple d r} ∏_i 1/(mᵢ!)²` is a sum of nonnegative
terms (`besselCoeff_nonneg`); the witness tuple putting all mass on coordinate `0`,
`m = (fun i => if i = ⟨0,hd⟩ then r else 0)`, lies in `antidiagonalTuple d r` (its
coordinate-sum is `r`) and contributes a product of strictly positive factors `1/(mᵢ!)² > 0`.
`Finset.sum_pos'` (nonnegativity + one strictly-positive member) upgrades the trivial
`besselCoeff_nonneg` baseline to strict positivity whenever `d ≥ 1`. -/
theorem besselCoeff_pos_of_pos {d : ℕ} (hd : 0 < d) (r : ℕ) : 0 < besselCoeff d r := by
  unfold besselCoeff
  -- The witness tuple: all mass on coordinate ⟨0, hd⟩.
  set m₀ : Fin d → ℕ := fun i => if i = (⟨0, hd⟩ : Fin d) then r else 0 with hm₀
  -- Membership: its coordinate-sum is r.
  have hmem : m₀ ∈ Finset.Nat.antidiagonalTuple d r := by
    rw [Finset.Nat.mem_antidiagonalTuple]
    rw [hm₀]
    rw [Finset.sum_ite_eq' Finset.univ (⟨0, hd⟩ : Fin d) (fun _ => r)]
    simp
  -- The witness term is a strictly positive product of strictly positive factors.
  have hpos : (0 : ℚ) < ∏ i, (1 : ℚ) / (Nat.factorial (m₀ i)) ^ 2 := by
    apply Finset.prod_pos
    intro i _
    positivity
  -- Sum is strictly positive: all terms nonnegative + one strictly positive member.
  apply Finset.sum_pos'
  · intro x _
    apply Finset.prod_nonneg
    intro i _
    positivity
  · exact ⟨m₀, hmem, hpos⟩


end ProximityGap.PrizeWorkbench

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PrizeWorkbench.centralBinom_mul_sq_factorial
#print axioms ProximityGap.PrizeWorkbench.one_div_sq_factorial_eq
#print axioms ProximityGap.PrizeWorkbench.besselTerm_mul_eq_centralBinomTerm
#print axioms ProximityGap.PrizeWorkbench.besselCoeff_eq_centralBinom_sum
#print axioms ProximityGap.PrizeWorkbench.besselCoeff_zero_and_gaussianCoeff_zero
#print axioms ProximityGap.PrizeWorkbench.besselCoeff_nonneg
#print axioms ProximityGap.PrizeWorkbench.besselCoeff_pos_of_pos
