/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Nat.Choose.Central

/-!
# The rep-theoretic (zero-weight multiplicity) view of `E_r^{char0}(μ_n)` (#444, avenue Rep)

This brick records the **representation-theoretic identification** of the char-0 additive energy
`E_r^{char0}(μ_n)` as a **zero-weight-space multiplicity**, and proves axiom-clean the single new
atom that the rep route contributes: the **per-direction central-binomial sub-Gaussian
domination**. It then states the exact gap (why the rep route does NOT reach the char-`p` prize).

## The rep-theoretic dictionary (paper, verified exactly n=4,8,16 in `scripts`)

`μ_n = {n-th roots of unity}`, `n = 2^μ`, `m = n/2`. By the Lam–Leung 2-power theorem
(`_AvX_LamLeungTwoPowerAntipodalBalan`, in-tree), a vanishing `ℚ`-sum of `2^μ`-th roots is a
union of antipodal pairs `{ζ^j, −ζ^j}`. Hence a "collision" `∑ xᵢ = ∑ yⱼ` (`x, y ∈ μ_n^r`)
decouples across the `m` antipodal **directions** `j = 0,…,m−1`: for each `j`, the combined
`2r`-multiset must place EQUAL counts `c_j` on `ζ^j` and `−ζ^j`, with `∑_j c_j = r`.

This is exactly the structure of a **zero-weight space**: write `V = ℂ[μ_n]`; the additive
collision condition is "weight `0`" for the weight given by the embedding `μ_n ↪ ℂ` modulo the
antipodal relation lattice `L = ⟨e_j + e_{j+m}⟩` (rank `m = n/2 = rank` of the relation lattice,
since the `n` roots span `ℚ(ζ)` of degree `φ(n) = n/2`). Concretely, with reduced coordinates
`d_j = (#{=ζ^j}) − (#{=ζ^{j+m}}) ∈ ℤ^m`, the energy is

  `E_r^{char0}(μ_n) = Σ_{d ∈ ℤ^m} N_r(d)²`,  `N_r(d) = #{r-tuples of ±e_j ∈ ℤ^m summing to d}`,

i.e. `E_r^{char0}` is the **number of closed `2r`-walks on `ℤ^m` with step set `{±e_j}`** =
`m_{2r}(S_m)`, the `2r`-th moment of `S_m = X_1+…+X_m`, `X_j = 2cos(U_j)` iid (`E[X^{2k}] =
C(2k,k)`, `Var(X) = 2`, `Var(S_m) = 2m = n`). Because the directions are **independent**, this is
the **tensor/branching (Schur–Weyl) decomposition**, giving the EXACT composition sum

  `E_r^{char0}(μ_n) = Σ_{c_0+…+c_{m-1}=r} (2r)! / ∏ⱼ (2c_j)! · ∏ⱼ C(2c_j, c_j)`   (★)

(`= (2r)!·[x^{2r}] I₀(2x)^m`; verified exactly vs brute-force, n=4,8,16, r≤4 in the probe).

## What this brick proves (axiom-clean `{propext, Classical.choice, Quot.sound}`)

The per-direction factor `C(2c, c)` is the dimension of the degree-`2c` balanced (zero-weight)
invariant space in ONE antipodal direction. The Wick target is the Gaussian `2r`-th moment with
`Var = n`, which by the SAME tensor structure factors as `∏ⱼ (2c_j−1)‼·2^{c_j}` per composition.
The bound `E_r^{char0} ≤ Wick_r` therefore follows **per direction** from the single atom proved
here:

- `centralBinom_le_doubleFactorialPow` :  `C(2c, c) ≤ 2^c · (2c−1)‼`   for all `c`,

with EQUALITY iff `c ≤ 1`. This is the **zero-weight per-direction sub-Gaussian domination**: the
balanced-multiset count in one direction is bounded by the Gaussian moment of one `2cos(U)` factor.
It is the rep-theoretic re-derivation of `_AvW0.besselCoeff_le_expCoeff` (`1/(c!)² ≤ 1/c!`): indeed
`C(2c,c)/(2c)! = 1/(c!)²` and `(2^c (2c−1)‼)/(2c)! = 1/c!`, so the two domination atoms are the
SAME inequality `c! ≥ 1` viewed in the multiplicity (this file) vs. coefficient (`_AvW0`) gauge.

## Honest scope (`closesPrize = false`) — the EXACT gap

The tensor/branching factorization (★) — the whole reason the bound is clean per-direction — holds
**ONLY in characteristic 0** (or any prime not dividing the relevant resultants). Over `𝔽_p` the
`2^μ`-th roots satisfy ADDITIONAL relations (wraparound: a short `±1`-sum of roots `≡ 0 (mod p)`
without being antipodally balanced). These extra relations ENLARGE the zero-weight space:

  `E_r^{𝔽_p}(μ_n) = E_r^{char0}(μ_n) + W_r`,   `W_r ≥ 0`,  `W_r > 0` for `r ≥ r₀(n) ≈ 5`.

Crucially, the wraparound relations **COUPLE the directions** (a single mod-`p` relation involves
roots from several antipodal directions at once), so the zero-weight space over `𝔽_p` is **NOT a
tensor product over directions** — the Schur–Weyl branching that yields (★) and the clean
per-direction bound FAILS. Bounding the surviving coupled multiplicity `W_r` at the moment saddle
`r ≈ ln p` for the worst prime IS the BGK / Paley wall, untouched here.

**Exact gap, one line:** the rep multiplicity factors over the `m = n/2` antipodal directions iff
`char = 0`; over `𝔽_p` the wraparound generators raise the relation-lattice rank above `m` and
couple directions, so the branching rule no longer applies. The proved atom bounds the **char-0**
multiplicity exactly (reproducing `_AvW0`), and reaches no further.

Issue #444.
-/

namespace ArkLib.ProximityGap.Frontier.AvRep

open Nat

/-! ## The per-direction zero-weight atom: `C(2c,c) ≤ 2^c · (2c−1)‼`. -/

/-- `(2c)! = 2^c · c! · (2c−1)‼`. From `factorial_eq_mul_doubleFactorial` (`(n+1)! = (n+1)‼·n‼`)
and `doubleFactorial_two_mul` (`(2c)‼ = 2^c·c!`). -/
lemma factorial_two_mul_split (c : ℕ) :
    (2 * c)! = 2 ^ c * c ! * (2 * c - 1)‼ := by
  cases c with
  | zero => decide
  | succ k =>
    have h2 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    rw [h2, Nat.factorial_eq_mul_doubleFactorial]
    -- ((2k+1)+1)! = ((2k+1)+1)‼ * (2k+1)‼; ((2k+1)+1)‼ = (2(k+1))‼ = 2^{k+1}(k+1)!
    have e1 : (2 * k + 1 + 1)‼ = (2 * (k + 1))‼ := by congr 1
    have e2 : (2 * k + 1)‼ = (2 * (k + 1) - 1)‼ := by congr 1
    rw [e1, Nat.doubleFactorial_two_mul, e2]
    ring

/-- The Gaussian `2c`-th moment of a single `Var = 2` factor, in the integer form
`2^c · (2c−1)‼ = (2c)! / c!`. This is the per-direction Wick target. -/
lemma doubleFactorialPow_eq (c : ℕ) :
    2 ^ c * (2 * c - 1)‼ = (2 * c)! / c ! := by
  rw [factorial_two_mul_split]
  -- goal: 2^c * (2c-1)‼ = (2^c * c! * (2c-1)‼) / c!
  set D := (2 * c - 1)‼ with hD
  have hrw : 2 ^ c * c ! * D = (2 ^ c * D) * c ! := by ring
  rw [hrw, Nat.mul_div_cancel _ (Nat.factorial_pos c)]

/-- **The rep-theoretic per-direction sub-Gaussian atom.**
The central binomial coefficient `C(2c, c)` (= dimension of the degree-`2c` balanced /
zero-weight invariant space in one antipodal direction) is dominated by the Gaussian `2c`-th
moment `2^c · (2c−1)‼` of a single `2cos(U)` factor. Equality iff `c ≤ 1`. -/
theorem centralBinom_le_doubleFactorialPow (c : ℕ) :
    Nat.centralBinom c ≤ 2 ^ c * (2 * c - 1)‼ := by
  rw [doubleFactorialPow_eq]
  -- `C(2c,c) = (2c)!/(c! · c!)` and target `= (2c)!/c!`; since `c! ≥ 1`, `/(c!·c!) ≤ /c!`.
  unfold Nat.centralBinom
  rw [Nat.choose_eq_factorial_div_factorial (by omega)]
  -- `(2c)! / (c! * (2c - c)!) = (2c)! / (c! * c!)`
  have hcc : 2 * c - c = c := by omega
  rw [hcc]
  -- want: (2c)! / (c! * c!) ≤ (2c)! / c!
  apply Nat.div_le_div_left
  · -- c! ≤ c! * c!
    calc c ! = c ! * 1 := (Nat.mul_one _).symm
      _ ≤ c ! * c ! := Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero c))
  · exact Nat.factorial_pos c

/-- Equality holds at `c = 0, 1` (the `Var`-matching base cases that make the bound tight at
small depth, hence at the energy onset `r₀`). -/
example : Nat.centralBinom 0 = 2 ^ 0 * (2 * 0 - 1)‼ := by decide
example : Nat.centralBinom 1 = 2 ^ 1 * (2 * 1 - 1)‼ := by decide

/-- Strict for `c ≥ 2` (the per-direction slack that, summed over directions, is the falling
`E_r/Wick` ratio in char 0). -/
example : Nat.centralBinom 2 < 2 ^ 2 * (2 * 2 - 1)‼ := by decide
example : Nat.centralBinom 3 < 2 ^ 3 * (2 * 3 - 1)‼ := by decide

/-! ## The exact gap, as named Props (no proof — these ARE the open core / its char-0 shadow). -/

/-- **(★) The zero-weight multiplicity composition-sum identity** (char-0), as a named carrier.
`E m r` is the char-0 energy `E_r^{char0}(μ_{2m})`; the RHS is the Schur–Weyl branching
decomposition over the `m` antipodal directions, weighted by the multinomial `(2r)!/∏(2c_j)!` and
the per-direction central-binomial dimensions `∏ C(2c_j, c_j)`. The compositions of `r` into `m`
parts are indexed by `Finset.Nat.antidiagonalTuple m r` (tuples `c : Fin m → ℕ` with `∑ c = r`).
(The full Lean proof of (★) is the `_AvW0` Bessel identity in coefficient gauge; this names the
multiplicity gauge. Verified exactly vs brute force n=4,8,16, r≤4 in the probe.) -/
def ZeroWeightCompositionSum (E : ℕ → ℕ → ℕ) : Prop :=
  ∀ m r, E m r =
    ∑ c ∈ Finset.Nat.antidiagonalTuple m r,
      ((2 * r)! / (∏ j, (2 * c j)!)) * (∏ j, Nat.centralBinom (c j))

/-- **The exact gap, named.** The branching factorization (★) — hence the clean per-direction
bound `centralBinom_le_doubleFactorialPow` summed over directions — holds ONLY when the relation
lattice has rank exactly `m = n/2` (char 0). Over `𝔽_p` the wraparound generators raise the rank
and COUPLE directions, so the char-`p` zero-weight multiplicity exceeds the char-0 one by
`W_r ≥ 0` (`> 0` for `r ≥ r₀ ≈ 5`). `EFp m r = E^{char0} m r + W m r` with `W m r ≥ 0`. Proving
`W m r = 0` at `r ≈ ln p` for the worst prime is the prize; it is FALSE for `r ≥ r₀` (onset), so the
rep route bounds only the char-0 layer. This Prop records the decomposition; the open core is the
size of `W` at the saddle. -/
def WraparoundExcessDecomposition (EFp E W : ℕ → ℕ → ℕ) : Prop :=
  ∀ m r, EFp m r = E m r + W m r

/-- This brick does NOT close the prize: it proves the char-0 per-direction atom only. -/
theorem closesPrize : False ∨ True := Or.inr trivial

end ArkLib.ProximityGap.Frontier.AvRep

-- Axiom audit (run via pg-iterate; must show only propext, Classical.choice, Quot.sound)
#print axioms ArkLib.ProximityGap.Frontier.AvRep.centralBinom_le_doubleFactorialPow
#print axioms ArkLib.ProximityGap.Frontier.AvRep.factorial_two_mul_split
#print axioms ArkLib.ProximityGap.Frontier.AvRep.doubleFactorialPow_eq
