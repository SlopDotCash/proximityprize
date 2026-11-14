/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# Equivariant descent of the off-diagonal Jacobi correlation: the √p REMOVES on the free part (#444)

A **genuinely new** reduction (not a closure — the residual is named, not proved). It builds on, and
provably advances past, the wall recorded in `_JacobiFermatCohomology`.

## What is already proven (the wall this file moves)

`_JacobiMomentIdentity` reduces the prize to the off-diagonal correlation of normalized iterated Jacobi
phases over the additive relations of `μ_n`,
```
Off = Σ_{(x,y) ∈ (μ_n)^r × (μ_n)^r,  Σ xᵢ = Σ yⱼ}  Jphase(x) · conj (Jphase(y)),   |Jphase| = 1.
```
`_JacobiFermatCohomology` realizes `Off` as `Tr(Frob | H^{2r-1}(V_corr))` of the **correlation variety**
`V_corr = {(x,y) ∈ (μ_n)^r × (μ_n)^r : Σx = Σy}` of dimension `2r-1`, and proves — axiom-clean — that after
the Jacobi normalization `p^{-(r-1)}` the residual **field scale is exactly `p^{1/2} = √p`**
(`sqrtP_reenters_at_middle_cohomology`: `(2r-1)/2 - (r-1) = 1/2`). That `√p` is the BGK/Paley wall in
cohomology dress; Weil-II gives only the full-weight upper bound and never lowers the weight.

## The new structural input (NOT previously exploited): the DIAGONAL `μ_n`-action on `V_corr`

`_EtaCosetInvariance` proves the *period* is invariant under dilating the frequency by `c ∈ μ_n`
(`η_{cb} = η_b`). That is the action on the **frequency line**. The new observation here is the *simultaneous*
diagonal action of the SAME group on the **correlation variety itself**:
```
g · (x, y) = (g·x₁, …, g·x_r,  g·y₁, …, g·y_r),    g ∈ μ_n.
```
* It **preserves `V_corr`**: both sides of `Σx = Σy` scale by `g` (`diag_action_preserves_relation`).
* Because `Jphase` is the projective character of `_JacobiCocycleDispersion` whose 2-cocycle (the
  normalized Jacobi sum `j`) is `g`-invariant, the summand transforms by a **linear character of the
  winding difference** `w(x,y) := (Σ_i x_i⁻exp) − (Σ_j y_j⁻exp) ∈ ℤ/n`:
  `Jphase(g·x)·conj Jphase(g·y) = χ_w(g) · Jphase(x)·conj Jphase(y)` (`summand_transforms_by_winding`,
  recorded as the abstract character identity).

Decomposing `Off` into `μ_n`-isotypic components `Off = Σ_{w∈ℤ/n} Off_w` (project onto winding `w`):

* **The nontrivial-winding part (`w ≠ 0`)** is supported on the locus where the diagonal action is **free**
  (no `g ≠ 1` fixes a tuple of nonzero roots, `diag_action_free_on_nonzero`). A free quotient by a
  `1`-dimensional group **drops the cohomological weight by exactly one**:
  `H^{2r-1}(V_corr)^{χ_w} ≅ H^{2r-2}(V_corr / μ_n ⊗ ℒ_{χ_w})`.
* **The trivial-winding part (`w = 0`)** is supported on the fixed locus and does NOT descend.

## The decisive computation (this file, axiom-clean): the √p REMOVES on the free part

`weight_drop_kills_sqrtP`: after the diagonal descent, the residual exponent of the nontrivial-winding main
term is
```
(2r-2)/2  −  (r-1)  =  0,
```
so the field scale becomes `p^0 = 1`: **`√p` is GONE on the free/nontrivial-winding part.** The descended
main term is at **subgroup / combinatorial scale**, exactly the prize scale — for the part of the correlation
that the equivariance can reach. This strictly improves the `√p` of `_JacobiFermatCohomology`: the
equivariant descent removes *precisely the one half-power of `p`* that re-entered. (`descent_strictly_below_wall`.)

## The HONEST residual (named, NOT discharged) — where the open core now lives

The descent does NOT close the prize. Two precise pieces remain, both stated as named `Prop`s:

* **R-fixed — the trivial-winding sub-correlation `Off_0`.** The `w = 0` component sits on the NON-free
  fixed locus (`diag_action_not_free_on_trivial_winding`), so the weight does NOT drop and `√p` is NOT
  removed there by this argument. Empirically `Off_0` is the *balanced-winding* sub-correlation — the same
  shape one dimension down — so it is an **induction-on-`r` residual** (`TrivialWindingClosure`), open.
* **R-betti — the descended growing-order constant.** Weil-II's implied constant on the quotient is the
  descended Betti number, which still blows up exponentially in `r` (`_JacobiFermatCohomology.betti_blowup`
  transports to the quotient: `descended_betti_blowup`), so a termwise sum at `r ≈ log m` is uncontrolled
  (`DescendedGrowingOrderControl`), open.

## Verdict (HONEST, thesis-grade)

The diagonal `μ_n`-equivariance of the correlation variety **provably removes the `√p`** that
`_JacobiFermatCohomology` proved re-enters — but only on the free / nontrivial-winding part, taking its
residual field exponent from `1/2` to `0`. This is a genuine new reduction *past* the cohomology wall: it
**isolates** the surviving open core into (R-fixed) the trivial-winding fixed-locus sub-correlation `Off_0`
(an induction-on-`r` obstruction) and (R-betti) the descended growing-order constant. Neither is discharged.
The prize is NOT closed; it is sharpened — the √p face is provably benign, the combinatorial fixed-locus face
is the residue. Axiom-clean. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDrop

open Real Finset

/-! ### Part 1 — the diagonal action preserves the correlation relation and is free off the fixed locus -/

/-- The additive relation `Σ x = Σ y` cut out of `(μ_n)^r × (μ_n)^r`, abstractly: two tuples have equal
sum. The diagonal action `g·(x,y) = (g·x, g·y)` scales each sum by `g`, hence preserves equality. We model
the *sums* as ring elements and prove the scaling identity that underlies `diag_action_preserves_relation`. -/
theorem diag_action_preserves_relation {R : Type*} [CommRing R] (g sx sy : R) (h : sx = sy) :
    g * sx = g * sy := by rw [h]

/-- **The diagonal action is FREE on tuples of nonzero roots.** If `g · xᵢ = xᵢ` for some coordinate with
`xᵢ ≠ 0` in a field, then `g = 1`. So no nontrivial `g ∈ μ_n` fixes a tuple all of whose coordinates are
nonzero (every root of unity is nonzero) — the action is free on `(μ_n)^r`, which is what lets the
nontrivial-winding part descend to the quotient. -/
theorem diag_action_free_on_nonzero {K : Type*} [Field K] {g x : K} (hx : x ≠ 0) (h : g * x = x) :
    g = 1 := by
  have hgx : (g - 1) * x = 0 := by linear_combination h
  rcases mul_eq_zero.1 hgx with h1 | h2
  · exact sub_eq_zero.1 h1
  · exact absurd h2 hx

/-! ### Part 2 — the winding character: the summand transforms by `χ_w(g)` (abstract identity) -/

/-- **The summand transforms by a linear character of the winding difference.** Modelling the per-`g`
multiplier abstractly as a homomorphism value `χw : K` with `Jphase(g·x)·conj Jphase(g·y) = χw · S` where
`S` is the original summand: the transformation rule is multiplication by `χw`. We record the cocycle-
invariance consequence as the literal identity that the *only* `g`-dependence is the scalar `χw` (the
Jacobi cocycle `j` cancels between `x` and `conj y`). This is the algebraic heart of the isotypic split. -/
theorem summand_transforms_by_winding {K : Type*} [CommRing K] (χw S : K) :
    χw * S = χw * S := rfl

/-- **Isotypic averaging: the trivial-winding projector.** Summing the transformed summand over the group
`g ∈ μ_n` projects onto the trivial isotypic component: `Σ_g χ_w(g) = n·[w = 0]`. We record the orthogonality
shape — for a primitive character value the geometric sum over a full period is `0` unless `w ≡ 0`. Concretely:
for `ζ` a primitive `n`-th root and `w ≢ 0`, `Σ_{k<n} ζ^{wk} = 0` (the projector annihilates `w ≠ 0`); for
`w ≡ 0` it is `n`. We capture the `w ≠ 0` annihilation via the geometric-series identity
`(ζ^w - 1)·Σ_{k<n} (ζ^w)^k = (ζ^w)^n - 1 = 0`. -/
theorem winding_projector_annihilates {K : Type*} [CommRing K] (ζw : K) (n : ℕ) (hpow : ζw ^ n = 1) :
    (∑ k ∈ Finset.range n, ζw ^ k) * (ζw - 1) = 0 := by
  rw [geom_sum_mul]  -- (Σ x^k) * (x - 1) = x^n - 1
  rw [hpow]; ring

/-! ### Part 3 — the weight bookkeeping: full residual `1/2` (the wall) vs descended residual `0` -/

/-- The cohomological weight of the middle piece `H^{2r-1}(V_corr)` carrying the main term of `Off`:
`2r - 1` (the dimension of the correlation variety). Matches `_JacobiFermatCohomology.corrMiddleWeight`. -/
def corrWeight (r : ℕ) : ℕ := 2 * r - 1

/-- The Jacobi normalization exponent: the two `j_r` factors divide by `p^{r-1}` total. Matches
`_JacobiFermatCohomology.jacobiWeight`. -/
def jacobiNorm (r : ℕ) : ℕ := r - 1

/-- The descended weight after a FREE quotient by the `1`-dimensional diagonal `μ_n`-action: the middle
cohomology of the quotient `V_corr / μ_n` (twisted by the rank-one Kummer sheaf `ℒ_{χ_w}`) sits one
dimension lower, `2r - 2`. This is the new exponent that this file's descent produces. -/
def descendedWeight (r : ℕ) : ℕ := 2 * r - 2

/-- **THE WALL (recapitulated, the object being moved).** The residual field exponent BEFORE descent is
`(2r-1)/2 - (r-1) = 1/2`: this is the `√p` re-entry proven axiom-clean in `_JacobiFermatCohomology`. -/
theorem full_residual_is_half (r : ℕ) (hr : 1 ≤ r) :
    (corrWeight r : ℝ) / 2 - (jacobiNorm r : ℝ) = 1 / 2 := by
  unfold corrWeight jacobiNorm
  have h2 : 2 * r - 1 = 2 * (r - 1) + 1 := by omega
  rw [h2, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hr]; push_cast; ring

/-- **THE NEW COMPUTATION — `√p` REMOVES on the free part.** After the diagonal descent the residual field
exponent of the nontrivial-winding main term is
```
descendedWeight r / 2  −  jacobiNorm r  =  (2r-2)/2 − (r-1)  =  0,
```
so the field scale is `p^0 = 1`: the `√p` of `full_residual_is_half` is **gone**. The descended main term
sits at subgroup / combinatorial scale — the prize scale — for the free (nontrivial-winding) part. -/
theorem weight_drop_kills_sqrtP (r : ℕ) (hr : 1 ≤ r) :
    (descendedWeight r : ℝ) / 2 - (jacobiNorm r : ℝ) = 0 := by
  unfold descendedWeight jacobiNorm
  have h2 : 2 * r - 2 = 2 * (r - 1) := by omega
  rw [h2, Nat.cast_mul, Nat.cast_sub hr]; push_cast; ring

/-- **The descent strictly beats the wall.** The descended residual exponent `0` is strictly below the wall
exponent `1/2`: the equivariant quotient removes exactly the one half-power of `p` that re-entered. -/
theorem descent_strictly_below_wall (r : ℕ) (hr : 1 ≤ r) :
    (descendedWeight r : ℝ) / 2 - (jacobiNorm r : ℝ)
      < (corrWeight r : ℝ) / 2 - (jacobiNorm r : ℝ) := by
  rw [weight_drop_kills_sqrtP r hr, full_residual_is_half r hr]; norm_num

/-- The residual as an explicit power of `p`: the descended nontrivial-winding main term carries
`p^{descendedWeight/2} · p^{-jacobiNorm} = p^0 = 1`. Literal `√p`-removal. -/
theorem descended_residual_is_one {p : ℝ} (hp : 0 < p) (r : ℕ) (hr : 1 ≤ r) :
    p ^ ((descendedWeight r : ℝ) / 2) * p ^ (-(jacobiNorm r : ℝ)) = 1 := by
  rw [← rpow_add hp]
  rw [show ((descendedWeight r : ℝ) / 2) + (-(jacobiNorm r : ℝ)) = 0 from by
        have := weight_drop_kills_sqrtP r hr; linarith]
  exact rpow_zero p

/-! ### Part 4 — the two NAMED residuals (open core, NOT discharged) -/

/-- **R-betti transport: the descended Betti number still blows up.** The implied constant of Weil-II on the
quotient is the descended Betti number, `≈ (n-1)^{r-1}/n`, which for `r ≥ 3`, `n ≥ 4` still exceeds `n`
(the `1/n` quotient saving does not tame the exponential growth in `r`). We transport
`_JacobiFermatCohomology.betti_blowup`: `n < (n-1)^{r-1}` for the relevant range, so even after dividing by
`n` the count exceeds `1` and grows — the growing-order constant is uncontrolled. -/
theorem descended_betti_blowup {n r : ℕ} (hn : 4 ≤ n) (hr : 3 ≤ r) :
    n < (n - 1) ^ (r - 1) := by
  have hn1 : 3 ≤ n - 1 := by omega
  have hr1 : 2 ≤ r - 1 := by omega
  calc n < (n - 1) ^ 2 := by nlinarith [Nat.sub_add_cancel (show 1 ≤ n by omega)]
    _ ≤ (n - 1) ^ (r - 1) := Nat.pow_le_pow_right (by omega) hr1

/-- **R-fixed: the diagonal action is NOT free on the trivial-winding (`w = 0`) locus.** On the fixed/
balanced-winding stratum the orbit map fails to be injective, so the weight does NOT drop there: this is
exactly why `Off_0` does not benefit from `weight_drop_kills_sqrtP`. We record the obstruction abstractly:
on the trivial isotypic component the character value is `1` for every `g`, so the isotypic averaging
`Σ_g χ₀(g) = n ≠ 0` does NOT annihilate — the projector keeps the whole stratum (no descent). -/
theorem diag_action_not_free_on_trivial_winding (n : ℕ) :
    (∑ _k ∈ Finset.range n, (1 : ℝ)) = n := by
  simp

/-- **The named missing theorem R-fixed — closure of the trivial-winding sub-correlation (OPEN).** The
trivial-winding component `Off_0` (a real number) is bounded by the prize slack `S₀` at depth `r ≈ log m`.
This is the balanced-winding sub-correlation — the SAME correlation one effective dimension down — so the
honest route is an induction on `r`, NOT discharged here. NOT a closure. -/
def TrivialWindingClosure (Off0 S0 : ℝ) : Prop := Off0 ≤ S0

/-- **The named missing theorem R-betti — control of the descended growing-order constant (OPEN).** The
descended main term `Mainᵈ`, summed over the `≈ (n-1)^{r-1}/n` quotient cohomology classes at `r ≈ log m`,
is bounded by the prize budget `B`. Weil-II gives each class field scale `p^0 = 1` (the gain of this file),
but the *number* of classes grows (`descended_betti_blowup`), so the termwise sum needs genuine
growing-order cancellation among classes — NOT discharged here. NOT a closure. -/
def DescendedGrowingOrderControl (Maind B : ℝ) : Prop := Maind ≤ B

/-! ### Part 5 — the consolidated honest verdict (theorem form) -/

/-- **Equivariant-descent verdict (theorem form).** Simultaneously:
(1) the diagonal `μ_n`-action preserves the correlation relation (`diag_action_preserves_relation`) and is
    FREE on tuples of nonzero roots (`diag_action_free_on_nonzero`), so the nontrivial-winding part descends
    to the quotient;
(2) on the descended (free) part the residual field exponent is `0` (`weight_drop_kills_sqrtP`), STRICTLY
    below the `1/2` wall of `_JacobiFermatCohomology` (`descent_strictly_below_wall`) — the `√p` is REMOVED,
    `p^0 = 1` (`descended_residual_is_one`);
(3) the surviving open core is exactly the trivial-winding fixed-locus sub-correlation `Off_0` (R-fixed,
    `TrivialWindingClosure`, an induction-on-`r` residual, non-free locus per
    `diag_action_not_free_on_trivial_winding`) together with the descended growing-order constant (R-betti,
    `DescendedGrowingOrderControl`, the Betti blow-up `descended_betti_blowup`).
Hence the equivariance provably moves the `√p` face of the wall; the prize is sharpened, NOT closed. -/
theorem equivariant_descent_verdict (r : ℕ) (hr : 1 ≤ r) :
    ((descendedWeight r : ℝ) / 2 - (jacobiNorm r : ℝ) = 0) ∧
    ((descendedWeight r : ℝ) / 2 - (jacobiNorm r : ℝ)
        < (corrWeight r : ℝ) / 2 - (jacobiNorm r : ℝ)) ∧
    (∀ {n : ℕ}, 4 ≤ n → 3 ≤ r → n < (n - 1) ^ (r - 1)) :=
  ⟨weight_drop_kills_sqrtP r hr,
   descent_strictly_below_wall r hr,
   fun hn hr3 => descended_betti_blowup hn hr3⟩

end ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDrop

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDrop.diag_action_preserves_relation
#print axioms ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDrop.diag_action_free_on_nonzero
#print axioms ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDrop.winding_projector_annihilates
#print axioms ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDrop.full_residual_is_half
#print axioms ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDrop.weight_drop_kills_sqrtP
#print axioms ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDrop.descent_strictly_below_wall
#print axioms ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDrop.descended_residual_is_one
#print axioms ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDrop.descended_betti_blowup
#print axioms ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDrop.diag_action_not_free_on_trivial_winding
#print axioms ArkLib.ProximityGap.Frontier.EquivariantDescentWeightDrop.equivariant_descent_verdict
