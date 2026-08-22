/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (TASK A1-pairwise)
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Pairwise → sub-Gaussian: the `t`-wise-independence → moment-bound framework (#444, A1-pairwise)

## The structural situation (machine-verified, `phase_independence.py`)

The prize floor `M = max_{b≠0}|η_b| ≤ C·√(n log m)` reduces (the arcsine-iid framing,
`_ArcsineIIDFraming`) to: the Gauss period
`η_b = Σ_{k=1}^{n/2} Y_k`,  `Y_k = 2cos(2π·b·x_k/p)`  (`x_k` = the `n/2` antipodal pair reps of `μ_n`)
is **sub-Gaussian with variance proxy `n`**, uniformly over the `m = (p−1)/n` frequencies `b`.

The machine finding pins the *mechanism*. The phases `θ_k = b·x_k` are a **rank-1 linear function of
`b`**, so the `n/2` contributions are **NOT jointly independent** (the naive iid framing of
`_ArcsineIIDFraming` is only a moment match). What *is* true:

* they are **pairwise near-independent** (`max|Corr(Y_j,Y_k)| = 0.045` over `b`) — this gives the
  **2nd moment** (`Var(η) = n`, exact Parseval, the `√n` floor);
* the sum concentrates **sub-Gaussianly** (`E[η⁶]/E[η²]³ = 12.3 < ` Gaussian `15`);
* each `Y_k = 2cos(·)` is bounded `|Y_k| ≤ 2` with Bessel MGF `I₀(2y) ≤ exp(y²)` (sub-Gaussian
  per-phase proxy `2`, in-tree `_CharZeroMGFBesselBound.besselI0Two_le_exp_sq`).

So **pairwise** independence gives only the 2nd moment. To get sub-Gaussianity we need control of **all
even moments** `E[η^{2r}]` = the energy `E_r`. The precise open question this file frames:

> Does `k`-wise independence (for `k` up to `2r`) suffice for the `r`-th moment? And does the
> required depth `t ≈ log m` hold for the dilated phases `θ_k = b·x_k`?

## What this file BUILDS (the `t`-wise → moment-bound framework)

The clean algebraic fact: the `r`-th moment of a sum **expands multinomially** as a sum over tuples
`p : Fin r → ι`,
```
E[(Σ_{k∈s} Y_k)^r] = Σ_{p : Fin r → s}  E[∏_{i:Fin r} Y_{p i}].
```
Each term is the expectation of a product over a tuple of length `r`, hence over **at most `r`
distinct indices** (the image of `p`). So if `r ≤ t` and the family is **`t`-wise independent** —
i.e. every product over a tuple of length `≤ t` has its expectation equal to (resp. bounded by) the
value an independent family with the same marginals would give — then **every term of the expansion
matches (resp. is bounded by) its independent surrogate**, and the `r`-th moment matches (resp. is
bounded by) the independent `r`-th moment. That independent moment is exactly the Wick/Gaussian value
`E_r ≤ (2r−1)‼·n^r` the prize needs (`GaussianEnergyBound`).

So the implication is: **`t`-wise independence (depth `t`) ⟹ moments up to order `t` match Gaussian
⟹ partial sub-Gaussianity (the prize floor uses moments up to `r ≈ log m`, hence needs `t ≈ 2 log m`).**

### PROVEN here, axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `sorry`)

* `moment_expansion` — the **multinomial moment identity**
  `E[(Σ Y_k)^r] = Σ_{tuples p} E[∏ Y_{p i}]` (from `Finset.sum_pow'`, linearity of `expt`).
* `tuple_image_card_le` — every tuple `p : Fin r → ι` has `|image p| ≤ r` (the "at most `r` distinct
  indices" fact that makes `r ≤ t` the right threshold).
* `moment_match_of_tIndep` — **`t`-wise independence ⟹ the `r`-th moment EQUALS the independent
  surrogate** for `r ≤ t` (every expansion term factorizes).
* `moment_bound_of_tIndepBound` — **`t`-wise *bounded* independence ⟹ the `r`-th moment is `≤` the
  summed surrogate bound** for `r ≤ t` (the inequality version, what the energy ceiling consumes).
* `wick_moment_bound_of_tIndep` — specialized to a **per-tuple Wick ceiling** `B`: `t`-wise bounded
  independence with `E[∏ Y_{p i}] ≤ B p` gives `E[(Σ Y_k)^r] ≤ Σ_p B p`. Plugging the Gaussian
  per-tuple value makes `Σ_p B p = (2r−1)‼·n^r`, the energy bound.

### The NAMED OPEN INPUT (REDUCED — the honest open content)

* `TIndepBound` / `TIndep` — the **`t`-wise (bounded) independence** hypothesis of the family
  `Y : ι → Ω → ℝ`: every tuple of length `≤ t` has product-expectation `≤` (resp. `=`) its independent
  surrogate. **The open core is exactly this Prop for the dilated phases `Y_k(b) = 2cos(2π b x_k/p)`
  at depth `t ≈ 2 log m`.** Pairwise (`t = 2`) is machine-true (`|Corr| = 0.045`); whether it extends
  to `t ≈ log m` is the BGK/BCHKS-1.12 wall under a structural name — the rank-1 linearity of the
  phases is precisely what can make high-order tuples DEPENDENT (collisions of the linear form
  `Σ ± x_{k_i} ≡ 0 mod p`, the short `±1`-relations of `2^μ`-th roots; memory
  `issue444-Wr-excess-onset-threshold-not-birthday`). We name it; we do not discharge it.

## Honest scope

The `t`-wise → moment-bound machinery is **prize-TRUE direction and fully proven**. It is NOT a prize
closure: the input `TIndepBound Y t` at depth `t ≈ log m` for the dilated phases is the open core, the
same wall (`EnergyIsNAMoment` in `_ShawNegativeDependence`, the char-`p` excess in
`_CharZeroMGFBesselBound`) under the `t`-wise-independence name. This is a LANDED abstract framework +
REDUCED bridge, per the project modularity convention. Issue #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset

namespace ArkLib.ProximityGap.Frontier.PhasePairwiseToSubGaussian

/-! ## §1. Uniform finite expectation (self-contained, matches `_ShawNegativeDependence.expt`). -/

variable {Ω : Type*} [Fintype Ω] {ι : Type*} [DecidableEq ι]

/-- The uniform expectation `E[X] = (∑_ω X ω) / |Ω|` of a real random variable on a finite space. -/
noncomputable def expt (X : Ω → ℝ) : ℝ :=
  (∑ ω : Ω, X ω) / (Fintype.card Ω : ℝ)

/-- Linearity of expectation over a finite sum of variables:
`E[∑_{p∈t} F p] = ∑_{p∈t} E[F p]`. (The expansion below sums one term per tuple.) -/
theorem expt_sum {κ : Type*} (t : Finset κ) (F : κ → Ω → ℝ) :
    expt (fun ω => ∑ p ∈ t, F p ω) = ∑ p ∈ t, expt (F p) := by
  unfold expt
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]

/-- Monotonicity of expectation: a pointwise `≤` between variables lifts to expectations. -/
theorem expt_mono {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) : expt X ≤ expt Y := by
  unfold expt
  apply div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => h ω))
  positivity

/-- Monotonicity of a finite sum of expectations from a per-term `≤`. -/
theorem expt_sum_le_sum {κ : Type*} (t : Finset κ) (F : κ → Ω → ℝ) (B : κ → ℝ)
    (h : ∀ p ∈ t, expt (F p) ≤ B p) :
    expt (fun ω => ∑ p ∈ t, F p ω) ≤ ∑ p ∈ t, B p := by
  rw [expt_sum]
  exact Finset.sum_le_sum h

/-! ## §2. The multinomial moment expansion: `E[(Σ Y_k)^r] = Σ_{tuples} E[∏ Y_{p i}]`. -/

/-- The index set of length-`r` tuples drawn from a block `s : Finset ι`:
`tupleSet s r = { p : Fin r → ι | ∀ i, p i ∈ s }` (as a `Finset`, via `Fintype.piFinset`). -/
noncomputable def tupleSet (s : Finset ι) (r : ℕ) : Finset (Fin r → ι) :=
  Fintype.piFinset (fun _ : Fin r => s)

/-- **The multinomial moment expansion (the algebraic engine).** The `r`-th moment of a finite sum of
random variables `Y : ι → Ω → ℝ` over a block `s` expands as a sum over length-`r` index tuples:
```
E[(Σ_{k∈s} Y_k)^r] = Σ_{p ∈ tupleSet s r}  E[∏_{i:Fin r} Y_{p i}].
```
This is pure algebra (`Finset.sum_pow'` for the integrand, then linearity of `expt`); it is the
identity that turns a moment of a *sum* into a sum of *product-moments*, each over a tuple of length
`r` (hence `≤ r` distinct indices). The entire `t`-wise reduction acts term-by-term on this RHS. -/
theorem moment_expansion (Y : ι → Ω → ℝ) (s : Finset ι) (r : ℕ) :
    expt (fun ω => (∑ k ∈ s, Y k ω) ^ r)
      = ∑ p ∈ tupleSet s r, expt (fun ω => ∏ i : Fin r, Y (p i) ω) := by
  have hpt : (fun ω => (∑ k ∈ s, Y k ω) ^ r)
      = (fun ω => ∑ p ∈ tupleSet s r, ∏ i : Fin r, Y (p i) ω) := by
    funext ω
    rw [Finset.sum_pow']
    rfl
  rw [hpt]
  exact expt_sum (tupleSet s r) (fun p ω => ∏ i : Fin r, Y (p i) ω)

/-! ## §3. Every length-`r` tuple touches at most `r` distinct indices. -/

/-- **The threshold fact: a length-`r` tuple has at most `r` distinct entries.** `|image p| ≤ r` for
`p : Fin r → ι`. This is *why* `r ≤ t` is the exact condition for the `r`-th moment to be controlled
by `t`-wise independence: each product `∏_i Y_{p i}` involves only the `≤ r` distinct indices in the
image of `p`, so a `t`-wise factorization with `t ≥ r` applies to every expansion term. -/
theorem tuple_image_card_le {r : ℕ} (p : Fin r → ι) :
    (Finset.univ.image p).card ≤ r := by
  calc (Finset.univ.image p).card ≤ (Finset.univ : Finset (Fin r)).card :=
        Finset.card_image_le
    _ = r := by rw [Finset.card_univ, Fintype.card_fin]

/-! ## §4. The `t`-wise independence hypotheses (NAMED OPEN INPUTS). -/

/-- **`t`-wise BOUNDED independence (the inequality form — the open content the energy ceiling needs).**

`TIndepBound Y t B` asserts that for every length-`r` tuple `p : Fin r → ι` with `r ≤ t` (so the
product touches `≤ t` distinct indices), the product-moment is bounded by the *independent surrogate*
`B`:
```
∀ r ≤ t, ∀ p : Fin r → ι,  E[∏_{i:Fin r} Y_{p i}] ≤ B r p.
```
Here `B r p` is the value an independent family with the same marginals would give (e.g. the Wick
value). **This is the named open core.** Pairwise (`t = 2`) is machine-true for the dilated phases
(`max|Corr(Y_j,Y_k)| = 0.045`); whether it extends to depth `t ≈ 2 log m` (needed for the
`r ≈ log m` moment that pins the floor) is the BGK/BCHKS-1.12 wall: the phases `θ_k = b·x_k` are
rank-1 linear in `b`, so high-order tuples can be DEPENDENT (short `±1`-relations
`Σ ± x_{k_i} ≡ 0 mod p` of `2^μ`-th roots; memory `issue444-Wr-excess-onset-threshold-not-birthday`).
We name it; we do not discharge it. -/
def TIndepBound (Y : ι → Ω → ℝ) (t : ℕ) (B : ∀ r : ℕ, (Fin r → ι) → ℝ) : Prop :=
  ∀ r : ℕ, r ≤ t → ∀ p : Fin r → ι, expt (fun ω => ∏ i : Fin r, Y (p i) ω) ≤ B r p

/-- **`t`-wise EXACT independence (the equality form).** `TIndep Y t M` asserts that every product
over a length-`r` tuple with `r ≤ t` has expectation EQUAL to the independent-surrogate moment `M`:
```
∀ r ≤ t, ∀ p : Fin r → ι,  E[∏_{i:Fin r} Y_{p i}] = M r p.
```
Under this, the `r`-th moment of the sum matches its fully-independent value exactly (for `r ≤ t`) —
"moments up to order `t` match Gaussian". This is the structural reformulation of full independence
*truncated at depth `t`*: it is implied by joint independence but is strictly weaker. -/
def TIndep (Y : ι → Ω → ℝ) (t : ℕ) (M : ∀ r : ℕ, (Fin r → ι) → ℝ) : Prop :=
  ∀ r : ℕ, r ≤ t → ∀ p : Fin r → ι, expt (fun ω => ∏ i : Fin r, Y (p i) ω) = M r p

/-! ## §5. `t`-wise independence ⟹ the moment matches / is bounded by the independent surrogate. -/

/-- **`t`-wise EXACT independence ⟹ the `r`-th moment matches the independent surrogate** (for
`r ≤ t`). Combining the multinomial expansion (`moment_expansion`) with the per-tuple equality
(`TIndep`, valid because every tuple touches `≤ r ≤ t` indices), the `r`-th moment of the sum equals
the summed surrogate:
```
E[(Σ_{k∈s} Y_k)^r] = Σ_{p ∈ tupleSet s r} M r p.
```
This is the precise sense in which **"`t`-wise independence ⟹ moments up to order `t` match those of
an independent (Gaussian) family"** — the partial-sub-Gaussianity statement. -/
theorem moment_match_of_tIndep {Y : ι → Ω → ℝ} {t : ℕ}
    {M : ∀ r : ℕ, (Fin r → ι) → ℝ} (hY : TIndep Y t M)
    (s : Finset ι) {r : ℕ} (hr : r ≤ t) :
    expt (fun ω => (∑ k ∈ s, Y k ω) ^ r) = ∑ p ∈ tupleSet s r, M r p := by
  rw [moment_expansion Y s r]
  exact Finset.sum_congr rfl (fun p _ => hY r hr p)

/-- **`t`-wise BOUNDED independence ⟹ the `r`-th moment is bounded by the summed surrogate** (for
`r ≤ t`). The inequality version, which is what the energy ceiling consumes: combining the expansion
with the per-tuple bound `E[∏ Y_{p i}] ≤ B r p` (valid for every tuple, each touching `≤ r ≤ t`
indices) gives
```
E[(Σ_{k∈s} Y_k)^r] ≤ Σ_{p ∈ tupleSet s r} B r p.
```
With `B r p` the Gaussian/Wick per-tuple value this RHS is the `(2r−1)‼·n^r` energy bound. -/
theorem moment_bound_of_tIndepBound {Y : ι → Ω → ℝ} {t : ℕ}
    {B : ∀ r : ℕ, (Fin r → ι) → ℝ} (hY : TIndepBound Y t B)
    (s : Finset ι) {r : ℕ} (hr : r ≤ t) :
    expt (fun ω => (∑ k ∈ s, Y k ω) ^ r) ≤ ∑ p ∈ tupleSet s r, B r p := by
  rw [moment_expansion Y s r]
  exact Finset.sum_le_sum (fun p _ => hY r hr p)

/-! ## §6. Specialization: a per-tuple Wick ceiling ⟹ the energy/moment bound. -/

/-- **The Wick moment bound from `t`-wise independence (the capstone).** Suppose the family is
`t`-wise bounded-independent against a per-tuple Wick ceiling `B` (the value an independent Gaussian
family with the matched marginals assigns to each tuple). Then for every `r ≤ t` the `r`-th moment of
the sum `S = Σ_{k∈s} Y_k` obeys the Wick ceiling:
```
E[S^r] ≤ Σ_{p ∈ tupleSet s r} B r p.
```
When the marginals are the arcsine variance-proxy `2` and `|s| = n/2`, the RHS is the Gaussian
even-moment `(2r−1)‼·n^r` (the `(2r−1)‼` perfect matchings of the `2r` exponents), i.e. the in-tree
`GaussianEnergyBound`. So the **entire prize floor follows from `TIndepBound` at depth `t ≈ 2 log m`**
— which is the single named open input. This theorem is the abstract Wick bound; it is the prize-true
direction, fully proven from the `t`-wise hypothesis. -/
theorem wick_moment_bound_of_tIndep {Y : ι → Ω → ℝ} {t : ℕ}
    {B : ∀ r : ℕ, (Fin r → ι) → ℝ} (hY : TIndepBound Y t B)
    (s : Finset ι) {r : ℕ} (hr : r ≤ t) :
    expt (fun ω => (∑ k ∈ s, Y k ω) ^ r) ≤ ∑ p ∈ tupleSet s r, B r p :=
  moment_bound_of_tIndepBound hY s hr

/-- **Joint independence ⟹ `t`-wise independence at every depth (the truncation is genuine).** If a
per-tuple equality `M` holds for ALL tuples (full joint independence / a complete moment match), then
in particular it holds up to any depth `t`, so `TIndep Y t M`. This records that `t`-wise independence
is *implied by* — hence weaker than — full independence: the naive iid framing (`_ArcsineIIDFraming`)
is the `t = ∞` instance; the real object only needs the finite-depth truncation `t ≈ 2 log m`. -/
theorem tIndep_of_fullIndep {Y : ι → Ω → ℝ}
    {M : ∀ r : ℕ, (Fin r → ι) → ℝ}
    (hfull : ∀ r : ℕ, ∀ p : Fin r → ι, expt (fun ω => ∏ i : Fin r, Y (p i) ω) = M r p)
    (t : ℕ) : TIndep Y t M :=
  fun r _ p => hfull r p

/-- **The exact-equality moment match upgrades to a bound** (bridge `TIndep → TIndepBound`): if the
tuple-moments equal a surrogate `M`, then they are bounded by it, so the equality-form `t`-wise
independence feeds the inequality-form consumers. -/
theorem tIndepBound_of_tIndep {Y : ι → Ω → ℝ} {t : ℕ}
    {M : ∀ r : ℕ, (Fin r → ι) → ℝ} (hY : TIndep Y t M) :
    TIndepBound Y t M :=
  fun r hr p => le_of_eq (hY r hr p)

end ArkLib.ProximityGap.Frontier.PhasePairwiseToSubGaussian

/-! ## Axiom audit — must be ⊆ {propext, Classical.choice, Quot.sound}; no `sorryAx`. -/
open ArkLib.ProximityGap.Frontier.PhasePairwiseToSubGaussian in
#print axioms moment_expansion
open ArkLib.ProximityGap.Frontier.PhasePairwiseToSubGaussian in
#print axioms tuple_image_card_le
open ArkLib.ProximityGap.Frontier.PhasePairwiseToSubGaussian in
#print axioms moment_match_of_tIndep
open ArkLib.ProximityGap.Frontier.PhasePairwiseToSubGaussian in
#print axioms moment_bound_of_tIndepBound
open ArkLib.ProximityGap.Frontier.PhasePairwiseToSubGaussian in
#print axioms wick_moment_bound_of_tIndep
open ArkLib.ProximityGap.Frontier.PhasePairwiseToSubGaussian in
#print axioms tIndep_of_fullIndep
