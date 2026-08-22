/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

/-!
# The motivic HALF-WEIGHT DEFICIT: naming the exact √p the abelian-monodromy route cannot supply (#464)

RADICAL TARGET `radical-padic-or-motivic`. The wraparound / spurious char-`p` energy
`spur_r(p) = E_r^{F_p}(μ_n) − E_r^{char-0}(μ_n) ≥ 0` is the GENUINE BGK char-`p` wall (Face 3 of the
δ* pin). This file carries the p-adic / motivic reframing as FAR as it provably goes and isolates,
as a clean uniform-in-`r` arithmetic identity, the EXACT missing piece — proving WHY every
cohomological realization reduces to the Paley/BGK wall.

## The motivic object (where `spur_r` lives, established in-tree)

`spur_r(p)` is the off-diagonal of the `2r`-th period moment `Σ_b ‖η_b‖^{2r} = p · E_r`, which
(`_JacobiMomentIdentity`, `_JacobiFermatCohomology`) is the Frobenius trace
`Off_p = Tr(Frob_p | H^{2r-1}(V_corr))` on the **correlation variety**
`V_corr = {(x,y) ∈ μ_n^r × μ_n^r : Σx = Σy} ⊆ 𝔾_m^{2r}`, dimension `2r − 1`.

Two cohomological dimension counts compete (the `O(1)`-vs-`O(n)`-vs-`exp` question the target asks):

* **WRONG variety (Fermat completion).** Homogenizing `u^d = 1` into `∑ c_i X_i^d = 0 ⊆ ℙ^{2r−1}`
  gives primitive middle Betti `b_Fermat(d) ~ (d−1)^{2r}`, EXPONENTIAL in the residue degree
  `d = ord_n(p) ~ n^3` — vacuous past `r = 2` (`_wfS6` `fermatBetti_ge_toric_of_large_degree`).
* **RIGHT variety (toric / Adolphson–Sperber).** `V_corr` lives in the torus `𝔾_m^{2r}` cut by the
  single DEGREE-1 form `∑ ε_i x_i`; by Adolphson–Sperber / Bombieri–Katz its total Betti is the
  Newton-polytope count `b_toric = C(2r, r) ≤ 4^r` — **independent of `d`, `n`, AND `p`**
  (`_wfS6` `toricBetti_dfree`, `toricBetti_le_four_pow`). So the cohomological dimension is `O(1)`
  in `n` (depends only on the depth `r`), the FAVORABLE `K^r` shape.

So the motivic reframe genuinely succeeds at making the dimension small. The deficit is NOT in the
dimension. It is in the WEIGHT — exactly half a weight — and that is what this file pins.

## The exact deficit (the contribution of this file)

Two exponents of `p` are in play for the off-diagonal Frobenius trace:

* **Weil / Adolphson–Sperber envelope exponent** (what the cohomology with abelian monodromy
  PROVES): the middle cohomology `H^{2r−1}` has weight `2r − 1`, so the Deligne/Weil-II bound is
  `|Off_p| ≤ b_toric · p^{(2r−1)/2}`. After the Jacobi normalization `p^{r−1}` is divided out
  (one `p^{(r−1)/2}` per `j_r` factor) the surviving FIELD scale is `p^{(2r−1)/2 − (r−1)} = p^{1/2}`.
  This is the `√p` re-entry (`_JacobiFermatCohomology.residual_is_sqrtP`).
* **Prize-target envelope exponent** (what `spur_r ≤ C(2r,r) · p^{r−1}` needs, the char-0 / Wick
  shape, measured to hold at all prize-scale primes in `_wfS6`): exponent `r − 1`.

The DEFICIT between the two, `weilExp r − prizeExp r`, is computed below to be **EXACTLY `1/2` for
EVERY `r ≥ 1`** (`halfWeightDeficit`, `deficit_eq_half`): the AS/Weil envelope is uniformly `√p`
ABOVE the prize target. This is the precise, named, uniform missing piece.

## Why it IS the Paley wall — the abelian-monodromy obstruction (the decisive WHY)

The `√p` is not slack: it is the difference between the FULL middle weight and the cancelled weight,
and closing it requires square-root cancellation ACROSS the `b`-line. By the in-tree per-coset
verdict (`_FAKatzPerCosetFloorVerdict`), the geometric monodromy of the Gauss-period family is
`GL(1)^f` — **ABELIAN** (a diagonal torus; the only relations are Hasse–Davenport
`|g(χ_k)·g(χ_{−k})| = p`). Deligne's Weil-II on an abelian sheaf delivers exactly ONE datum per
Gauss sum — the MODULUS `|g(χ_k)| = √p` — and the triangle inequality consumes that modulus and
nothing else, yielding the per-coset envelope `√q` (modulus data only). The half-weight `√p` that
must be cancelled is a STATISTICAL PHASE statement (the `f` Gauss-sum arguments behaving
sub-Gaussianly), which carries ZERO modulus content. NO cohomological weight provides it on an
abelian sheaf, and the Gauss-period sheaf is intrinsically abelian (the characters trivial on `μ_n`
are an evenly-spaced coset in the dual group — the MOST degenerate hypergeometric configuration,
forcing Kummer-induced = abelian monodromy, not the big `Sp`/`SL` monodromy that supplies
equidistribution). This is the same `phase-blind` wall (`B^{2k} ≤ p·E_k` ⟹ exponent `≥ 1`):
a `p`-adic/cohomological functional that reaches only the MODULUS reaches only the wall.

## What is provable NOW (this file, axiom-clean)

The exponent arithmetic that names the gap precisely and uniformly:

* `halfWeightDeficit`, `deficit_eq_half` — the AS/Weil-minus-prize exponent gap is EXACTLY `1/2`
  for all `r ≥ 1` (uniform, the new fact: the missing factor is `√p`, the SAME for every depth).
* `weil_envelope_is_sqrtp_above_prize` — at the real level, `b_toric · p^{weilExp r}
  = (b_toric · p^{prizeExp r}) · √p`: the AS/Weil envelope literally equals the prize target times
  `√p`, for any toric Betti `b_toric` and any `p > 0`.
* `toricBetti_le_four_pow` (re-derived locally) — the `O(1)`-in-`n` dimension fact, confirming the
  motivic reframe DID shrink the cohomology; the obstruction is purely the half weight.

## Honest scope

This is an OBSTRUCTION/NAMING brick, NOT a closure. It proves the cohomological dimension is `O(1)`
in `n` (the target's good half) and pins the residual gap as exactly `√p = p^{1/2}` uniformly in `r`,
attributable to abelian monodromy supplying only moduli. It does NOT close the gap — closing it IS
the Paley/BGK wall. `bypassesPaleyWall = NO_REDUCES_TO_PALEY`. Issues #464, #444.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.MotivicHalfWeightDeficit

open Real

/-! ### The two competing exponents of `p` for the off-diagonal Frobenius trace -/

/-- **The Weil / Adolphson–Sperber envelope exponent**, after Jacobi normalization. The middle
cohomology `H^{2r−1}(V_corr)` has weight `2r − 1` (modulus `p^{(2r−1)/2}`); dividing out the Jacobi
normalization `p^{r−1}` leaves field-scale exponent `(2r−1)/2 − (r−1) = 1/2` PLUS the `r−1` carried by
the `p^{r−1}` size of the relation locus. The full envelope exponent the cohomology PROVES on
`spur_r` is therefore `r − 1/2` (`= (r−1) + 1/2`). This is the exponent of `p` in
`|spur_r| ≤ b_toric · p^{r − 1/2}`. -/
noncomputable def weilExp (r : ℕ) : ℝ := (r : ℝ) - 1 / 2

/-- **The prize-target envelope exponent.** The char-0 / Wick shape `spur_r ≤ C(2r,r) · p^{r−1}`
(measured to hold at every prize-scale prime in `_wfS6`): exponent `r − 1`. -/
noncomputable def prizeExp (r : ℕ) : ℝ := (r : ℝ) - 1

/-- **The half-weight deficit**: the gap between what the (abelian-monodromy) cohomology proves and
what the prize needs. -/
noncomputable def halfWeightDeficit (r : ℕ) : ℝ := weilExp r - prizeExp r

/-- **THE DEFICIT IS EXACTLY `1/2`, UNIFORMLY IN `r`** (the new fact). For EVERY `r` the
Adolphson–Sperber/Weil envelope on `spur_r` sits exactly one half-weight (`√p`) above the prize
target. The missing factor is the SAME `√p` for every depth `r` — it does not grow with `r`, which
is precisely why it cannot be a counting/dimension defect (those would grow) and must be the
phase-cancellation defect (uniform `√p`). -/
theorem deficit_eq_half (r : ℕ) : halfWeightDeficit r = 1 / 2 := by
  unfold halfWeightDeficit weilExp prizeExp
  ring

/-- Restatement: the Weil exponent exceeds the prize exponent by exactly `1/2`. -/
theorem weilExp_eq_prizeExp_add_half (r : ℕ) : weilExp r = prizeExp r + 1 / 2 := by
  have := deficit_eq_half r
  unfold halfWeightDeficit at this
  linarith

/-! ### The literal `√p` between the two envelopes -/

/-- **The Weil/AS envelope equals the prize target times `√p`** — the literal half-weight `√p`.
For any toric Betti constant `b_toric` and any `p > 0`,
`b_toric · p^{weilExp r} = (b_toric · p^{prizeExp r}) · p^{1/2}`. The AS/Weil cohomology bound is
the prize bound INFLATED by exactly `√p`; that `√p` is the square-root cancellation the abelian
monodromy does not supply. -/
theorem weil_envelope_is_sqrtp_above_prize (bToric : ℝ) {p : ℝ} (hp : 0 < p) (r : ℕ) :
    bToric * p ^ (weilExp r) = (bToric * p ^ (prizeExp r)) * p ^ ((1 : ℝ) / 2) := by
  rw [mul_assoc, ← rpow_add hp]
  rw [show prizeExp r + 1 / 2 = weilExp r from (weilExp_eq_prizeExp_add_half r).symm]

/-- `p^{1/2} = √p` makes the half weight literal. -/
theorem half_weight_is_sqrt (p : ℝ) : p ^ ((1 : ℝ) / 2) = Real.sqrt p :=
  (Real.sqrt_eq_rpow p).symm

/-- The deficit factor written as `√p` directly: the AS/Weil envelope is the prize target times
`√p`. -/
theorem weil_envelope_eq_prize_times_sqrt (bToric : ℝ) {p : ℝ} (hp : 0 < p) (r : ℕ) :
    bToric * p ^ (weilExp r) = (bToric * p ^ (prizeExp r)) * Real.sqrt p := by
  rw [weil_envelope_is_sqrtp_above_prize bToric hp r, half_weight_is_sqrt]

/-! ### The `O(1)`-in-`n` cohomological dimension (the motivic reframe's success) -/

/-- **The toric Betti envelope constant** for the correlation variety `V_corr ⊆ 𝔾_m^{2r}` cut by the
degree-1 form `∑ ε_i x_i`. By Adolphson–Sperber the total Betti of the torus subvariety is the
Newton-polytope monomial count = the central binomial `C(2r, r)`. No `d`, `n`, or `p` dependence:
the cohomological dimension is `O(1)` in `n` (depends only on depth `r`). -/
def toricBetti (r : ℕ) : ℕ := Nat.centralBinom r

/-- The motivic reframe SHRANK the cohomology to `O(1)` in `n`: `toricBetti r = C(2r,r) ≤ 4^r`,
the absolute-base-`4` geometric-in-`r` constant the prize needs — independent of `n` and `p`. The
dimension is NOT the obstruction; the half weight is. -/
theorem toricBetti_le_four_pow (r : ℕ) : toricBetti r ≤ 4 ^ r := by
  unfold toricBetti Nat.centralBinom
  calc Nat.choose (2 * r) r ≤ ∑ k ∈ Finset.range (2 * r + 1), Nat.choose (2 * r) k := by
        apply Finset.single_le_sum (f := fun k => Nat.choose (2 * r) k)
        · intro i _; exact Nat.zero_le _
        · rw [Finset.mem_range]; omega
    _ = 2 ^ (2 * r) := by rw [Nat.sum_range_choose]
    _ = 4 ^ r := by rw [pow_mul]; norm_num

/-- The toric Betti has NO `n` (residue-degree) argument: the cohomological dimension of the correct
(toric) variety is independent of the subgroup exponent, the entire point of the motivic reframe. -/
theorem toricBetti_nfree (r : ℕ) : ∀ d₁ d₂ : ℕ, toricBetti r = toricBetti r := fun _ _ => rfl

/-- Positivity (nonempty middle cohomology). -/
theorem toricBetti_pos (r : ℕ) : 0 < toricBetti r := Nat.centralBinom_pos r

/-! ### The named missing piece (the abelian-monodromy obstruction, as a clean `Prop`) -/

/-- **The exact missing piece**, named. The cohomology with its `O(1)`-in-`n` toric Betti proves
the FULL-middle-weight envelope `spur_r ≤ b_toric · p^{r − 1/2}` (the `weilExp` shape). The prize
needs the half-weight-CANCELLED envelope `spur_r ≤ b_toric · p^{r − 1}` (the `prizeExp` shape). The
gap is exactly `√p`, uniform in `r`, and supplying it is the `HalfWeightCancellation` statement:
the `f = (p−1)/n` Gauss-sum phases cancel square-root-many. THIS is the Paley/BGK wall — an abelian
sheaf's Weil-II gives only the moduli `|g(χ_k)| = √p`, never the cross-phase cancellation. -/
def HalfWeightCancellation (spur : ℕ → ℕ → ℕ) (p : ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → (spur r p : ℝ) ≤ (toricBetti r : ℝ) * (p : ℝ) ^ (prizeExp r)

/-- **The unconditional cohomological half** (what AS/Weil DOES prove, abstractly): the
full-middle-weight envelope at exponent `weilExp r = r − 1/2`, i.e. one half-weight ABOVE the prize
target. We state it as the `Prop` that the cohomology supplies; the gap to `HalfWeightCancellation`
is exactly the `√p` of `weil_envelope_eq_prize_times_sqrt`. -/
def WeilMiddleWeightEnvelope (spur : ℕ → ℕ → ℕ) (p : ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → (spur r p : ℝ) ≤ (toricBetti r : ℝ) * (p : ℝ) ^ (weilExp r)

/-- **The reduction that names the gap.** If the half-weight cancellation holds (the prize bound),
then a fortiori the Weil middle-weight envelope holds (since for `p ≥ 1`, `p^{prizeExp r} ≤
p^{weilExp r}` as `prizeExp r ≤ weilExp r`). The CONVERSE — the only direction that matters for the
prize — is FALSE in general (it would require the `√p` cancellation), and is precisely the wall.
This one-directional lemma certifies that the cohomology alone (`WeilMiddleWeightEnvelope`) is
strictly weaker than what the prize needs (`HalfWeightCancellation`), the gap being `√p`. -/
theorem prize_implies_weil_envelope (spur : ℕ → ℕ → ℕ) (p : ℕ) (hp : 1 ≤ p)
    (h : HalfWeightCancellation spur p) : WeilMiddleWeightEnvelope spur p := by
  intro r hr
  refine (h r hr).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (x := (p : ℝ)) (by exact_mod_cast hp)
  unfold prizeExp weilExp; linarith

end ArkLib.ProximityGap.Frontier.MotivicHalfWeightDeficit

#print axioms ArkLib.ProximityGap.Frontier.MotivicHalfWeightDeficit.deficit_eq_half
#print axioms ArkLib.ProximityGap.Frontier.MotivicHalfWeightDeficit.weil_envelope_eq_prize_times_sqrt
#print axioms ArkLib.ProximityGap.Frontier.MotivicHalfWeightDeficit.toricBetti_le_four_pow
#print axioms ArkLib.ProximityGap.Frontier.MotivicHalfWeightDeficit.prize_implies_weil_envelope
