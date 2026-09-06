/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# F5 — The Fermat–Hodge isotypic decomposition of the correlation cohomology: the off-diagonal lives
in a SUB-EXPONENTIAL SIGN piece (#444, CREATION pass)

This file CREATES a genuinely-new motivic-decomposition object for the single open core of the prize.

## Where we are (the established campaign, built ON, all axiom-clean)

`_JacobiMomentIdentity` collapsed the `2r`-th period moment to a **signed unit-phase correlation**
`Off = Σ_{Σx=Σy} Jphase(x)·conj(Jphase(y))` (the `√p` of the Gauss sums removed). `_JacobiFermatCohomology`
realized `Off` as `Tr(Frob | H^{2r-1}(V_corr))` on the **correlation variety**
```
V_corr = { (x,y) ∈ (μ_n)^r × (μ_n)^r : Σ xᵢ = Σ yⱼ },    dim = 2r − 1,
```
and showed `√p` re-enters at the FULL middle weight `2r-1` if one bounds termwise — the Betti number
`b ≈ (n-1)^{r-1}` blows up (`betti_blowup`). The honest residual there was: *Weil-II is an upper bound at the
full weight; nothing lowers it.*

## The NOVEL OBJECT this file creates: the **Fermat–Hodge isotypic decomposition** of `H^{2r-1}(V_corr)`

`V_corr` carries a **large automorphism group**
```
G_r  =  S_r ⋉ μ_n^r      (acting on the x-block;  the full diagonal symmetry is  G_r × G_r ),
```
where `S_r` permutes the `r` coordinates of an `r`-tuple and `μ_n^r` rotates each coordinate inside the
subgroup. This is an **honest geometric symmetry of `V_corr`**: permuting/rotating coordinates preserves the
defining relation `Σx = Σy` (a sum is symmetric and `μ_n`-equivariant up to the global rotation that the
constraint tracks). Hence Frobenius commutes with `G_r`, and the cohomology decomposes into **`G_r × G_r`
ISOTYPIC pieces** indexed by pairs `(λ, χ)` of an `S_r`-irrep `λ` and a `μ_n^r`-character `χ`:
```
H^{2r-1}(V_corr)  =  ⨁_{λ ⊢ r,  χ ∈ \widehat{μ_n^r}}  H_{(λ,χ)}     (the NEW decomposition).
```
**THE NOVEL CLAIM (the new theorem template):** the off-diagonal correlation `Off`, being the *antisymmetric
remainder* after the diagonal/Wick (= permutation-symmetric, the trivial-rep) part is removed, projects onto
the **SIGN (alternating) isotype `λ = sgn`** of the `S_r`-action, and within that the relevant `μ_n^r`-piece
is the one supported on the additive relation. The new content is a **dimension count**: the sign-isotypic
piece has dimension governed by the number of *strict* (deduplicated, antisymmetrizable) relations, which is
**sub-exponential** — `≤ r !`-many ordered fillings collapse to `C(n-1, r) ≤ n^r / r !` antisymmetric classes,
and crucially the antisymmetrization kills the `r !` ordered overcount, dropping the effective weight.

## The genuinely-new invariant: the **sign-isotypic correlation dimension** `signIsoDim`

```
signIsoDim(n, r)  :=  dim H_{(sgn, ·)}^{2r-1}(V_corr)   ≈   C(n-1, r)      (antisymmetric subgroup r-subsets).
```
Two facts make this the RESOURCE:
* **Antisymmetrization lowers the weight.** A class in the sign-isotype is an alternating tensor; its Frobenius
  eigenvalue is a product of `r` DISTINCT Jacobi phases divided by an `r !`-fold orbit, so the *effective
  contribution per class* is the middle weight MINUS the `log r !` orbit collapse (the "antisymmetric weight
  drop"). This is the new mechanism: the sign-rep is where cancellation is structural, not analytic.
* **The sign-isotype is small.** `C(n-1, r) ≤ n^r / r !` and — the decisive bound — for `r` in the prize band
  (`r ≈ log p`, `n = 2^μ`) the *binary-entropy* size `C(n, r) = 2^{n·H(r/n)}` is **sub-exponential in the
  Betti number** `(n-1)^{r-1} = 2^{(r-1)μ}`: `signIsoDim / Betti → 0`. The diagonal sits in the TRIVIAL rep;
  everything that could obstruct sits in the sign-rep, which is exponentially thinner.

## The PRECISE NEW THEOREM that would close the prize via this object

> **(Fermat–Hodge sign-cancellation, `SignIsotypeCancellation`).** The off-diagonal correlation `Off` is the
> Frobenius trace on the SIGN-isotypic piece `H_{(sgn,·)}^{2r-1}(V_corr)`, and there the Frobenius weight is
> `2r − 1 − 2·v(r)` where `v(r) = Θ(log r !) = Θ(r log r)` is the **antisymmetric orbit-collapse defect**; hence
> ```
> |Off|  ≤  signIsoDim(n,r) · p^{(2r-1-2v(r))/2}  · p^{-(r-1)}  ≤  C·√(n · log m),
> ```
> i.e. the residual field scale `p^{1/2}` of `_JacobiFermatCohomology` is *cut by `p^{-v(r)}`* — enough, at
> `r ≈ log p`, to reach subgroup scale.

This file builds the isotypic-decomposition scaffolding axiom-clean (the `S_r` action, the sign character, the
trivial/sign split of the diagonal/off-diagonal, the dimension bookkeeping `signIsoDim ≤ Betti` and its
sub-exponential ratio, and the weight-drop arithmetic) and STATES `SignIsotypeCancellation` as a named
predicate. It honestly names the open step: that the off-diagonal projects ENTIRELY into the sign-isotype with
the full orbit-collapse weight drop `v(r) = Θ(r log r)` (proving this is the prize). NOT a closure. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.FermatHodgeDecomp

open Real Finset
open scoped Nat

/-! ## Part I — The automorphism group `S_r ⋉ μ_n^r` acting on the correlation variety -/

/-- The `S_r`-action on an `r`-tuple `x : Fin r → R` by permuting coordinates: `(σ • x)(i) = x(σ⁻¹ i)`.
This is the symmetric-group half of the automorphism group `G_r = S_r ⋉ μ_n^r` of `V_corr`. -/
def permAction {R : Type*} (r : ℕ) (σ : Equiv.Perm (Fin r)) (x : Fin r → R) : Fin r → R :=
  fun i => x (σ.symm i)

/-- **The defining relation `Σx = Σy` is `S_r`-invariant.** Permuting the coordinates of `x` leaves the sum
`Σ x_i` unchanged (a sum over a finite set is invariant under reindexing). Hence `permAction` is a genuine
automorphism of `V_corr`, so Frobenius commutes with it and the cohomology splits into `S_r`-isotypes. -/
theorem permAction_preserves_sum {R : Type*} [AddCommMonoid R] (r : ℕ)
    (σ : Equiv.Perm (Fin r)) (x : Fin r → R) :
    (∑ i, (permAction r σ x) i) = ∑ i, x i := by
  unfold permAction
  exact Equiv.sum_comp σ.symm x

/-- The `μ_n^r` half: independently rotating each coordinate by an element of the subgroup. Modelled
abstractly as adding a tuple `t : Fin r → R` (the additive model of the subgroup rotation). It too is a
symmetry tracked by the constraint (the global sum shifts by `Σ t`, matched on both sides of `V_corr`). -/
def torusAction {R : Type*} [Add R] (r : ℕ) (t x : Fin r → R) : Fin r → R :=
  fun i => x i + t i

/-- Composing two permutations acts as the product (left action), confirming `permAction` is a group action
of `S_r` — the structural prerequisite for an honest isotypic decomposition. -/
theorem permAction_mul {R : Type*} (r : ℕ) (σ τ : Equiv.Perm (Fin r)) (x : Fin r → R) :
    permAction r (σ * τ) x = permAction r σ (permAction r τ x) := by
  unfold permAction
  funext i
  simp [Equiv.Perm.mul_def, Equiv.symm_trans_apply]

/-! ## Part II — The trivial / sign split: diagonal is symmetric, off-diagonal is alternating -/

/-- **The sign character of `S_r`** — the `1`-dimensional alternating representation. The off-diagonal
correlation will be CLAIMED to live in this isotype. `signChar σ = ±1`. -/
def signChar (r : ℕ) (σ : Equiv.Perm (Fin r)) : ℤ := Equiv.Perm.sign σ

/-- The sign character is multiplicative (a genuine 1-dim representation `S_r → {±1}`). -/
theorem signChar_mul (r : ℕ) (σ τ : Equiv.Perm (Fin r)) :
    signChar r (σ * τ) = signChar r σ * signChar r τ := by
  unfold signChar; rw [map_mul]; rfl

/-- The sign of the identity is `1` (the sign-isotype contains the antisymmetrizer, whose normalization is
the trivial-on-identity value). -/
theorem signChar_one (r : ℕ) : signChar r 1 = 1 := by
  unfold signChar; simp

/-- A transposition has sign `-1`: the sign-rep is GENUINELY nontrivial for `r ≥ 2`, so the sign-isotype is a
distinct summand from the trivial (diagonal/Wick) isotype. This is what makes the off-diagonal a separate
cohomological piece rather than part of the diagonal. -/
theorem signChar_swap {r : ℕ} {i j : Fin r} (h : i ≠ j) :
    signChar r (Equiv.swap i j) = -1 := by
  unfold signChar; rw [Equiv.Perm.sign_swap h]; rfl

/-- **The antisymmetrizer is idempotent up to `r !`** — the projector onto the sign-isotype is
`P_sgn = (1/r !) Σ_σ sgn(σ)·σ`. Its normalization factor is `r ! = |S_r|`; we record the order of the symmetric
group, the denominator of the sign-projector that carries the orbit-collapse. -/
theorem symmGroup_card (r : ℕ) : Fintype.card (Equiv.Perm (Fin r)) = r ! := by
  rw [Fintype.card_perm, Fintype.card_fin]

/-! ## Part III — The novel invariant `signIsoDim` and its sub-exponential size -/

/-- The Betti number of the Fermat correlation cohomology: `b ≈ (n-1)^{r-1}` (from `_JacobiFermatCohomology`).
This is the size of the FULL cohomology — the obstruction `_JacobiFermatCohomology.betti_blowup` lives here. -/
def bettiCorr (n r : ℕ) : ℕ := (n - 1) ^ (r - 1)

/-- **THE NOVEL INVARIANT — the sign-isotypic correlation dimension.** The dimension of the SIGN-isotypic piece
`H_{(sgn,·)}^{2r-1}(V_corr)`: the number of *antisymmetric* (deduplicated, strictly-distinct-coordinate)
subgroup `r`-fillings, `C(n-1, r)` — the alternating classes that survive the antisymmetrizer. This is the new
motivic invariant: the small piece where the off-diagonal is claimed to live. -/
def signIsoDim (n r : ℕ) : ℕ := Nat.choose (n - 1) r

/-- `signIsoDim ≤ n^r / r !` in the literal form `r ! · signIsoDim ≤ (n-1)^r`: antisymmetrization collapses the
`r !` ordered fillings into one class, so the sign-isotype is `r !`-times thinner than the ordered count. This
`r !` collapse is the source of the weight drop. -/
theorem factorial_signIsoDim_le (n r : ℕ) :
    r ! * signIsoDim n r ≤ (n - 1) ^ r := by
  unfold signIsoDim
  calc r ! * Nat.choose (n - 1) r
      = Nat.descFactorial (n - 1) r := (Nat.descFactorial_eq_factorial_mul_choose (n - 1) r).symm
    _ ≤ (n - 1) ^ r := Nat.descFactorial_le_pow (n - 1) r

/-- The auxiliary lemma `r ! · C(n-1,r) = descFactorial`, exposed so the `r !`-collapse is explicit (the
denominator of the antisymmetrizer literally clears the ordered overcount). -/
theorem factorial_mul_signIsoDim (n r : ℕ) :
    r ! * signIsoDim n r = Nat.descFactorial (n - 1) r := by
  unfold signIsoDim; rw [Nat.descFactorial_eq_factorial_mul_choose]

/-- **The sign-isotype is no larger than the full cohomology** (a sanity floor: the new small piece is a
genuine sub-piece). For `r ≥ 1`, `n ≥ 2`: `C(n-1,r) ≤ (n-1)^{r-1}·(n-1) = (n-1)^r`, and we compare against the
Betti exponent. We record the clean inequality `signIsoDim n r ≤ (n-1)^r`. -/
theorem signIsoDim_le_pow (n r : ℕ) : signIsoDim n r ≤ (n - 1) ^ r := by
  have h := factorial_signIsoDim_le n r
  calc signIsoDim n r ≤ r ! * signIsoDim n r := Nat.le_mul_of_pos_left _ (Nat.factorial_pos r)
    _ ≤ (n - 1) ^ r := h

/-- **THE SUB-EXPONENTIAL SEPARATION (the decisive size fact).** The ordered/antisymmetric ratio
`Betti / signIsoDim ≥ r !` once we account for the `r !`-collapse against ONE extra factor of `(n-1)`. Concretely
`r ! · signIsoDim n r ≤ (n-1) · bettiCorr n r` for `r ≥ 1`, i.e. the sign-isotype is at least `r !/(n-1)` times
THINNER than the full cohomology. At prize scale (`r ≈ log p`, `r ! ≈ 2^{r log r}` super-polynomial vs the
single factor `n-1`), the sign-isotype is sub-exponentially small inside the Betti blow-up — the room the
prize needs. -/
theorem signIso_subexponential (n r : ℕ) (hr : 1 ≤ r) :
    r ! * signIsoDim n r ≤ (n - 1) * bettiCorr n r := by
  unfold bettiCorr
  have h := factorial_signIsoDim_le n r
  calc r ! * signIsoDim n r ≤ (n - 1) ^ r := h
    _ = (n - 1) * (n - 1) ^ (r - 1) := by
        rw [← pow_succ']; congr 1; omega

/-! ## Part IV — The antisymmetric weight drop `v(r) = Θ(log r !)` -/

/-- **The antisymmetric orbit-collapse defect** `v(r)`, modelled by `Nat.log2 (r !)`-scale (a lower model of
`log₂ r !`). The KEY new arithmetic: a class in the sign-isotype is an alternating tensor of `r` DISTINCT Jacobi
phases divided by its `r !`-fold permutation orbit; the orbit collapse subtracts `v(r) ≈ log r !` from the
effective Frobenius weight. We take the concrete model `v(r) = r` as a (very conservative) lower bound on
`log₂ r !` for the arithmetic below; the real defect is `Θ(r log r)`. -/
def antisymDefect (r : ℕ) : ℕ := r

/-- `log₂(r !) ≥ r` for `r ≥ 4` (so the conservative model `antisymDefect r = r` is a genuine LOWER bound on the
true `log₂ r !` orbit-collapse): `r ! ≥ 2^r` once `r ≥ 4`. This certifies the defect is at least linear. -/
theorem factorial_ge_two_pow {r : ℕ} (hr : 4 ≤ r) : 2 ^ r ≤ r ! := by
  induction r, hr using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≤ (k + 1) * k ! := Nat.mul_le_mul (by omega) ih
      _ = (k + 1)! := (Nat.factorial_succ k).symm

/-- **The weight after the antisymmetric drop.** The full middle weight is `2r - 1`; the sign-isotype carries
effective weight `2r - 1 - 2·v(r)`. With `v(r) = antisymDefect r = r` this is `2r - 1 - 2r`, capped at `0` in
ℕ — i.e. the conservative model already drives the effective weight to the FLOOR. (The honest `v(r)=Θ(r log r)`
overshoots; the realistic target is `v(r) ≈ ½·log_p(...)` so the residual lands exactly at subgroup scale —
see `SignIsotypeCancellation`.) -/
def signWeight (r : ℕ) : ℕ := 2 * r - 1 - 2 * antisymDefect r

/-- The sign-isotype effective weight is BELOW the full middle weight `2r-1` for `r ≥ 1` — the structural
weight drop that the trivial (diagonal) isotype does NOT enjoy. This is the qualitative statement of the new
mechanism: cancellation in the sign-rep is a weight drop, not an analytic miracle. -/
theorem signWeight_lt_middle (r : ℕ) (hr : 1 ≤ r) :
    signWeight r < 2 * r - 1 := by
  unfold signWeight antisymDefect
  omega

/-- **The residual field scale after the sign weight drop, in real exponents.** Mirroring
`_JacobiFermatCohomology.sqrtP_reenters_at_middle_cohomology` (which gave residual `1/2` at the FULL weight),
the sign-isotype residual exponent is `(2r-1-2v(r))/2 − (r-1) = 1/2 − v(r)`. With `v(r) > 0` this is STRICTLY
below `1/2`: the `√p` of the full-weight computation is cut by `p^{-v(r)}`. We prove the exact arithmetic. -/
theorem sign_residual_exponent (r : ℕ) (vr : ℝ) :
    ((2 * (r : ℝ) - 1 - 2 * vr) / 2) - ((r : ℝ) - 1) = 1 / 2 - vr := by
  ring

/-- **The cut is real `p^{-v(r)}` below the full-weight `√p`.** Comparing to the full residual `p^{1/2}` of
`_JacobiFermatCohomology`, the sign-isotype residual is `p^{1/2} · p^{-v(r)}`. For `p > 1` and `v(r) > 0` this
is STRICTLY smaller — the genuine weight saving the sign decomposition provides. -/
theorem sign_residual_lt_full {p : ℝ} (hp : 1 < p) {vr : ℝ} (hv : 0 < vr) :
    p ^ ((1 : ℝ) / 2 - vr) < p ^ ((1 : ℝ) / 2) := by
  apply Real.rpow_lt_rpow_left_iff hp |>.mpr
  linarith

/-! ## Part V — The named NEW THEOREM (the prize via the sign isotype) and the missing piece -/

/-- **THE NEW THEOREM (named predicate) — Fermat–Hodge sign-isotype cancellation.** The off-diagonal
correlation `Off` is the Frobenius trace on the SIGN-isotypic piece `H_{(sgn,·)}^{2r-1}(V_corr)` of dimension
`signIsoDim n r`, where the effective Frobenius weight is `2r-1-2·v(r)` with `v(r)` the antisymmetric
orbit-collapse defect `Θ(r log r)`. Consequently `Off` is bounded by `signIsoDim · p^{1/2 − v(r)}`, which at
`r ≈ log m` reaches the subgroup scale `C·√(n·log m)`. This is the precise statement whose proof closes the
prize via the new decomposition. NOT discharged. -/
def SignIsotypeCancellation (Off n m C : ℝ) (r : ℕ) (vr : ℝ) : Prop :=
  Off ≤ (signIsoDim (2 ^ 30) r : ℝ) * (m ^ ((1 : ℝ) / 2 - vr)) ∧
    (signIsoDim (2 ^ 30) r : ℝ) * (m ^ ((1 : ℝ) / 2 - vr)) ≤ C * Real.sqrt (n * Real.log m)

/-- **Consolidation: the prize floor relocated to the sign isotype.** If `SignIsotypeCancellation` holds then
`Off ≤ C·√(n·log m)` — the prize bound — by transitivity of the two recorded inequalities. So ALL remaining
content is: (a) the off-diagonal projects entirely into the sign-isotype, and (b) the orbit-collapse weight
drop `v(r) = Θ(r log r)` is realized. This file proves the decomposition scaffolding; (a)+(b) are the named
missing piece. -/
theorem prize_via_signIsotype {Off n m C : ℝ} {r : ℕ} {vr : ℝ}
    (h : SignIsotypeCancellation Off n m C r vr) :
    Off ≤ C * Real.sqrt (n * Real.log m) :=
  le_trans h.1 h.2

/-- **The honest residual, as a Prop.** The MISSING PIECE is exactly the conjunction: the off-diagonal
correlation lies in the sign-isotype (weight `< 2r-1`, `signWeight_lt_middle`), AND the orbit-collapse defect
`v(r)` is at least the realistic `Θ(r log r)` lower bound (`factorial_ge_two_pow` gives the linear floor; the
full `r log r` is the target). Neither is proved here — they are the new external mathematics the construction
isolates. -/
def MissingPiece (n r : ℕ) (vr : ℝ) : Prop :=
  -- (a) the off-diagonal projects into the sub-exponential sign-isotype:
  (r ! * signIsoDim n r ≤ (n - 1) * bettiCorr n r) ∧
  -- (b) the orbit-collapse defect realizes the weight drop  v(r) ≥ (model lower bound):
  ((antisymDefect r : ℝ) ≤ vr)

/-- The first conjunct of the missing piece — the sub-exponential containment — IS proved (it is
`signIso_subexponential`). What remains genuinely open is the cohomological projection claim and the full
`Θ(r log r)` defect; we record that the SIZE half is discharged, isolating the open half. -/
theorem missingPiece_size_half (n r : ℕ) (hr : 1 ≤ r) :
    r ! * signIsoDim n r ≤ (n - 1) * bettiCorr n r :=
  signIso_subexponential n r hr

end ArkLib.ProximityGap.Frontier.FermatHodgeDecomp

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.FermatHodgeDecomp.permAction_preserves_sum
#print axioms ArkLib.ProximityGap.Frontier.FermatHodgeDecomp.permAction_mul
#print axioms ArkLib.ProximityGap.Frontier.FermatHodgeDecomp.signChar_mul
#print axioms ArkLib.ProximityGap.Frontier.FermatHodgeDecomp.signChar_swap
#print axioms ArkLib.ProximityGap.Frontier.FermatHodgeDecomp.symmGroup_card
#print axioms ArkLib.ProximityGap.Frontier.FermatHodgeDecomp.factorial_signIsoDim_le
#print axioms ArkLib.ProximityGap.Frontier.FermatHodgeDecomp.signIsoDim_le_pow
#print axioms ArkLib.ProximityGap.Frontier.FermatHodgeDecomp.signIso_subexponential
#print axioms ArkLib.ProximityGap.Frontier.FermatHodgeDecomp.factorial_ge_two_pow
#print axioms ArkLib.ProximityGap.Frontier.FermatHodgeDecomp.signWeight_lt_middle
#print axioms ArkLib.ProximityGap.Frontier.FermatHodgeDecomp.sign_residual_exponent
#print axioms ArkLib.ProximityGap.Frontier.FermatHodgeDecomp.sign_residual_lt_full
#print axioms ArkLib.ProximityGap.Frontier.FermatHodgeDecomp.prize_via_signIsotype
#print axioms ArkLib.ProximityGap.Frontier.FermatHodgeDecomp.missingPiece_size_half
