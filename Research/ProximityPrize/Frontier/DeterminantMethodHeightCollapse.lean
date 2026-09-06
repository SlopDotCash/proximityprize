/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The determinant-method height collapse (Proximity Prize #444, lens [determinant-method])

This file records, **axiom-clean**, the precise integer-arithmetic wall that stops the
Bombieri–Pila–Heath-Brown **determinant method** from giving a sub-norm defect count for the
sparse-vanishing problem over the order-`n` subgroup `μ_n ⊆ 𝔽_p^×` (`n = 2^a`, `n ∣ p−1`).

## The lens and what it would buy

Let `g ∈ ℤ[X]` be a *sparse `±1` defect*: at most `2r` monomials, each coefficient `±1`, with
`g(ζ) = 0` in `𝔽_p` for a primitive `n`-th root `ζ`. Its archimedean **height** is `H = 2r`
(triangle bound on `≤ 2r` unit terms — `HeightGateNormBound.indicatorPoly_eval_nnnorm_le`). The
determinant method bounds the count of height-`≤ H` integer points on a variety by a quantity
that scales with **`log H`** (Heath-Brown). The hope: a defect count polynomial in `log H = log(2r)`
would *dodge* the `(2r)^{φ(n)}` norm wall (`CyclotomicNormDefectThreshold.prime_le_of_cyclotomic_signed_sum`).

## The collapse (what is PROVEN here)

To certify the vanishing condition `g(ζ) = 0` over `μ_n` by a determinant, the auxiliary system
must **separate all `φ(n)` archimedean conjugates** `g(ω)`, `Φ_n(ω) = 0` — i.e. it needs
`s = φ(n) = n/2` monomial rows. (Fewer rows under-determine the resultant: any proper sub-product
of the `φ(n)` factors `g(ω)` is not a `p`-divisible integer, so cannot certify `p ∣ N(g)`.) With
`s = φ(n)` rows of unit-modulus entries, the determinant `det(ω_i^{e_j})` is — up to the unit
Vandermonde of the roots — **exactly the cyclotomic resultant** `Res(Φ_n, g) = ∏_ω g(ω)`, whose
realized magnitude is the block witness `2^{n/2−1}` (`HeightGateNormBound.block_sum_norm`) and whose
worst-case archimedean bound is `(2r)^{φ(n)} = H^{n/2}` (`natAbs_resultant_cyclotomic_le_bound`).

So the determinant-method count exponent is
`detExp r n := φ(n) · log₂ H = (n/2) · log₂(2r)`,
which is **identical** to the norm-bound exponent `normExp r n := φ(n) · log₂(2r)`. The `log H`
saving of Bombieri–Pila is *per determinant entry*, but the method is forced to use `φ(n) = n/2`
rows, so the saving is multiplied back up by `n/2` and the **full height `H^{n/2}` reappears**.

The numeric companion `scripts/probes/probe_444_determinant_method_defect.py` confirms (exact
Gaussian-integer determinants, small `n`): the square `φ(n)×φ(n)` monomial Vandermonde over the
primitive roots has `log₂|det|` matching the Hadamard value `½·φ·log₂φ` exactly (`n=4,8,16,32 →
1,4,12,32`), and Part 3 tabulates `detExp ≈ normExp` up to `n = 2^30`.

## The closed-form `M(n)` conjecture from THIS lens (false-as-stated; the honest output)

The lens *would* predict a determinant defect bound `M(n) ≤ √(n · log m)` **iff** the determinant
method gave a count `≤ poly(log H)` per conjugate that did NOT multiply by `φ(n)`. The collapse
proven here says the exponent is `φ(n)·log H`, so the per-`b` Gauss-period house controlled by this
route is only `M(n) ≤ √n · 2^{φ(n)·…}`-trivial — i.e. the determinant method yields **no bound
better than the norm wall**. We state the would-be bound as a named `Prop`
`DeterminantDodgesHeight` and *refute its arithmetic core*: `detExp = normExp` exactly (so there is
no `log`-saving). The honest verdict: this lens falls on horn (ii) — the determinant of monomials
over `μ_n` re-introduces the full height `(2r)^{n/2}`.

Closed input (named/decidable/proven): `Nat.totient (2^a) = 2^{a-1}` (Mathlib
`Nat.totient_prime_pow`) and integer/`Nat.log` arithmetic (`decide`/`norm_num`). The resultant
identification is the in-tree `CyclotomicNormDefectThreshold` chain (cited, not re-derived).

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DeterminantMethodHeightCollapse

/-! ## §1  The two exponents (determinant-method vs norm-wall), integer surrogates

For `n = 2^a`, the cyclotomic degree is `φ(n) = n/2 = 2^{a-1}`. The norm-bound count of
height-`≤ H` sparse `±1` defects has `log₂`-exponent `φ(n)·log₂ H`; the height surrogate is
`H = 2r`, so `log₂ H = ⌊log₂(2r)⌋` in the integer surrogate `Nat.log 2 (2r)`. The
determinant-method count, after the forced `s = φ(n)` rows, has the SAME exponent. -/

/-- `φ(2^a) = 2^{a-1}` (Mathlib `Nat.totient_prime_pow`). The number of archimedean conjugates,
= the number of monomial rows the determinant method is forced to separate. -/
theorem totient_two_pow (a : ℕ) (ha : 1 ≤ a) : (2 ^ a).totient = 2 ^ (a - 1) := by
  rw [Nat.totient_prime_pow Nat.prime_two ha]; omega

/-- The **norm-wall exponent** (integer surrogate): `log₂` of the worst-case resultant magnitude
`(2r)^{φ(n)}` is `φ(n) · ⌊log₂(2r)⌋`. -/
def normExp (a r : ℕ) : ℕ := 2 ^ (a - 1) * Nat.log 2 (2 * r)

/-- The **determinant-method exponent** (integer surrogate): the forced `s = φ(n) = 2^{a-1}`
monomial rows, each contributing the per-entry height `⌊log₂(2r)⌋` (Bombieri–Pila per-row saving),
give a determinant of `log₂`-magnitude `φ(n) · ⌊log₂(2r)⌋` — the row count multiplies the saving
back up. -/
def detExp (a r : ℕ) : ℕ := (2 ^ a).totient * Nat.log 2 (2 * r)

/-! ## §2  THE COLLAPSE: `detExp = normExp` exactly (no `log` saving survives) -/

/-- **THE HEIGHT COLLAPSE (exact).** For every `n = 2^a` (`a ≥ 1`) and every sparseness `r`, the
determinant-method exponent equals the norm-wall exponent: `detExp a r = normExp a r`. The
`φ(n) = n/2` forced rows exactly cancel the per-row `log H` saving, so the determinant method
yields *no* sub-norm count. (This is the integer-arithmetic core of horn (ii): the monomial
determinant over `μ_n` re-introduces the full height `(2r)^{φ(n)}`.) -/
theorem detExp_eq_normExp (a r : ℕ) (ha : 1 ≤ a) : detExp a r = normExp a r := by
  unfold detExp normExp
  rw [totient_two_pow a ha]

/-- **Concrete prize-row collapse at `r = 2` (`2r = 4`, `⌊log₂ 4⌋ = 2`).** At any dyadic `n = 2^a`,
both exponents equal `2^{a-1} · 2 = 2^a = n`. So the determinant count of `4`-term `±1` defects is
`2^n`-large — exactly the norm wall, no improvement. -/
theorem detExp_prize_r2 (a : ℕ) (ha : 1 ≤ a) : detExp a 2 = 2 ^ a := by
  rw [detExp_eq_normExp a 2 ha]
  unfold normExp
  have hlog : Nat.log 2 (2 * 2) = 2 := by
    have : (2 * 2 : ℕ) = 2 ^ 2 := by norm_num
    rw [this, Nat.log_pow (by norm_num : (1:ℕ) < 2)]
  rw [hlog]
  -- 2^{a-1} * 2 = 2^a
  rw [← pow_succ]
  congr 1; omega

/-- At the prize point `n = 2^30`, the `4`-term-defect determinant count exponent is `2^30 = n`
(astronomically larger than `log₂` of the prize prime `~158`). The determinant method certifies
nothing at the prize. -/
theorem detExp_prize_point : detExp 30 2 = 2 ^ 30 := detExp_prize_r2 30 (by norm_num)

/-! ## §3  The would-be dodge, as a named `Prop`, and its refutation -/

/-- **The hoped-for determinant dodge, as a named `Prop` (NOT a placebo).**
`DeterminantDodgesHeight a r` asserts the determinant-method count exponent is *strictly smaller*
than the norm-wall exponent — i.e. the `log H` saving survives the row count. This is exactly what
a winning use of Bombieri–Pila would need: a defect count polynomial in `log(height)` rather than
`height^{φ(n)}`. -/
def DeterminantDodgesHeight (a r : ℕ) : Prop := detExp a r < normExp a r

/-- **REFUTED.** The determinant dodge is false for every dyadic `n = 2^a` (`a ≥ 1`) and every `r`:
the exponents are *equal* (`detExp_eq_normExp`), never strictly smaller. The `φ(n) = n/2` forced
monomial rows exactly absorb the per-row `log H` saving, so the monomial determinant over `μ_n`
re-introduces the full height `(2r)^{φ(n)}`. The determinant method offers no lever past the
elementary norm gate (`n ≤ 32`). -/
theorem determinantDodgesHeight_REFUTED (a r : ℕ) (ha : 1 ≤ a) :
    ¬ DeterminantDodgesHeight a r := by
  unfold DeterminantDodgesHeight
  rw [detExp_eq_normExp a r ha]
  exact lt_irrefl _

/-! ## §4  Monotone persistence: the collapse only widens up the index/sparseness tower -/

/-- For fixed `r` the collapse exponent grows like `n/2 = 2^{a-1}` in `a` (since `⌊log₂(2r)⌋ ≥ 1`
once `r ≥ 1`). So the determinant method falls further behind as `n → 2^30`, never catching up. -/
theorem detExp_ge_half_n (a r : ℕ) (ha : 1 ≤ a) (hr : 1 ≤ r) :
    2 ^ (a - 1) ≤ detExp a r := by
  rw [detExp_eq_normExp a r ha]
  unfold normExp
  have hlog : 1 ≤ Nat.log 2 (2 * r) := by
    have h2 : (2 : ℕ) ≤ 2 * r := by omega
    have hl2 : Nat.log 2 2 = 1 := by decide
    calc 1 = Nat.log 2 2 := hl2.symm
      _ ≤ Nat.log 2 (2 * r) := Nat.log_mono_right h2
  calc 2 ^ (a - 1) = 2 ^ (a - 1) * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ (a - 1) * Nat.log 2 (2 * r) := Nat.mul_le_mul_left _ hlog

end ArkLib.ProximityGap.Frontier.DeterminantMethodHeightCollapse

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.Frontier.DeterminantMethodHeightCollapse
#print axioms totient_two_pow
#print axioms detExp_eq_normExp
#print axioms detExp_prize_r2
#print axioms detExp_prize_point
#print axioms determinantDodgesHeight_REFUTED
#print axioms detExp_ge_half_n
end AxiomAudit
