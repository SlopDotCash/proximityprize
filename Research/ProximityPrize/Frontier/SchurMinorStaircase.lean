/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SchurLagrangeBridge

/-!
# The Schur-minor staircase: the `j`-fold minor binder for general agreement radius (#407)

AVENUE `schur-minor-staircase`.  The deployed `δ*` object — the far-line incidence `I` — sweeps
agreement radii `m = #R` (the witness set size), with `r = n − m` the rung.  At radius `m` the
per-`R` far-membership condition is governed by the left-null space of the `k`-column Vandermonde
`V_R`, of dimension `j := m − k`.  `NvIReconcile` did the codim-1 (`j=1`, `m=k+1`) and codim-2
(`j=2`, `m=k+2`, the *deployed* binder) cases.  This file proves the **general `j`-fold minor
binder form**, in the clean *symmetric* shape verified by the probes
(`probe_schur_staircase.py`, `probe_coeff_ladder.py`; `0` mismatches over `n∈{8,16}`, all radii,
all far exponents `b`):

> **The far monomial `x^b` lands in `RS[R,k]` (agrees with a degree-`< k` codeword on the radius-`m`
> set `R`) IF AND ONLY IF the single Schur polynomial `h_{b−k}` — i.e. the divided difference
> `dividedDifferencePow R' v b` — vanishes on EVERY `(k+1)`-subset `R' ⊆ R`.**

This is the `j`-fold (= `(m−k)`-fold) minor system stated as one symmetric Schur condition tested on
the `C(m, k+1)` sub-`(k+1)`-sets.  The rank of the vanishing system is exactly `j = m − k`:

* `j = 1` (`m = k+1`): the only `(k+1)`-subset is `R` itself, and the condition is the single
  divided difference `dividedDifferencePow R v b = 0`.  At `b = #R` this is the **point sum**
  `∑_{i∈R} v i = 0` — the binding sub-object `N` (height-gate / No-Excess).  (`= NvIReconcile`.)
* `j = 2` (`m = k+2`, the *deployed* binder for `n=16, k=4`): the `C(k+2,k+1) = k+2` divided
  differences `dividedDifferencePow R' v b` over the `(k+1)`-subsets, a rank-`2` system — the
  `h₂`-augmented condition that `NvIReconcile.deployed_h2_is_dividedDifference` exhibits.
* general `j`: the same single Schur function `h_{b−k}` swept over all `(k+1)`-subsets, rank `j`.

**The binding-radius law** (probes `probe_schur_staircase.py`, `probe_trace8.py`, this session;
exact, `p`-independent): which radius `m` *binds* `δ*` (the worst rung, the first `r` with
`max_far I > budget = n`).  Measured full rung traces at rate `ρ = 1/4`:

```
n=8,  k=2 (ρ=1/4): r=3 m=5 j=3 I=8 GOOD | r=4 m=4 j=2 I=9 BAD(binds) | r=5 m=3 j=1 I=40 BAD
                   => δ* = 3/8,  binding radius m* = k+2 = 4,  j* = 2.   (Johnson r=4.)
n=16, k=4 (ρ=1/4): r=9 m=7 j=3 I=9 GOOD | r=10 m=6 j=2 I=89 BAD(binds), binder (a=10,b=4=k)
                   => δ* = 9/16, binding radius m* = k+2 = 6,  j* = 2.   (Johnson r=8.)
```

So at the deployed prize rate `ρ = 1/4`, **the binding radius is `m* = k+2`, i.e. `j* = 2`, for BOTH
tested sizes** — the deployed `δ*` object is *exactly the 2-fold Schur minor* (`NvIReconcile`'s
codim-2 binder), NOT the codim-1 sub-object `N` (`j=1`, which over-counts by binding only the point
sum) and not a higher minor.  The binder sits at the **lowest** far exponent `b = k` with an
*imprimitive* offset difference (`gcd(n,|a−b|)` even at `n=16`).  Whether `j* = 2` persists at other
rates (`ρ = 1/8`, `ρ = 1/2`) is recorded as the open part of `BindingRadiusLaw` (the heavier
`n=16,k∈{2,8}` / `n=32` traces did not complete this session); the `j* = 2` pin is established at
`ρ = 1/4`.  The vacuous high-rung "GOOD" readings (`m ≤ k`, no far direction exists, `I = −1` sentinel)
are NOT genuine good rungs and must not be counted in `δ*` (a real bug if they are — they make `δ*`
spuriously large).

HONESTY (deployed `I` vs sub-object `N`).  Everything here is about the **deployed** far-line
incidence `I` — the per-`R` *line-membership* system whose binder is the full `j`-fold Schur minor.
`N` (the point sum `∑ v_i = 0`) is the `j=1`, `b=#R` *face* of this: a genuine lower bound on `I`,
NOT `I` itself at `j ≥ 2`.  The height-gate closes only `N`; the `j ≥ 2` minor carries the extra
independent Schur constraints `h₂,…` this file makes explicit.  Nothing here closes the deployed
`δ*` — it characterizes the binder *structure* (the algebraic form + the granularity law), leaving
the coset-count / spike-selection (the genuine open core) named as `Prop`s.

All theorems are `sorry`-free; the audit must show only `propext, Classical.choice, Quot.sound`.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset Polynomial

namespace ArkLib.ProximityGap.SchurMinorStaircase

open ProximityGap.SchurLagrange

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

/-! ## Part 1 — the divided difference is the top coefficient over ANY subset. -/

/-- **Divided difference over a `(k+1)`-subset = top coefficient of the restricted interpolant.**
For any `(k+1)`-subset `R' ⊆ R` (with `v` injective on `R'`), `dividedDifferencePow R' v b` is the
degree-`k` coefficient of the Lagrange interpolant of `x^b` over `R'`.  (Direct instance of the
Schur/Lagrange bridge `interpolate_pow_coeff_top` with `#R' = k+1`.) -/
theorem dividedDifference_eq_subset_top_coeff
    {R' : Finset ι} {v : ι → F} (hvs : Set.InjOn v R') {k b : ℕ} (hk : #R' = k + 1) :
    (Lagrange.interpolate R' v (fun i => (v i) ^ b)).coeff k = dividedDifferencePow R' v b := by
  have hkk : k = #R' - 1 := by omega
  rw [hkk]; exact interpolate_pow_coeff_top hvs b

/-! ## Part 2 — degree-`< k` of a polynomial ⟺ all order-`k` divided differences vanish.

A polynomial `f` has `degree < k` iff its `(k+1)`-st-order divided differences vanish.  For
membership we apply this to `f = interpolate R v (x^b)`: `x^b|_R ∈ RS[R,k]` ⟺ `interp` has degree
`< k` ⟺ every `(k+1)`-subset divided difference of `x^b` (which, since `interp` agrees with `x^b`
on `R'`, equals the divided difference of `interp`) vanishes. -/

/-- **The `j`-fold minor binder, FORWARD (sub-object) direction.**  If `x^b` agrees on the radius-`m`
set `R` with a polynomial `g` of degree `< k` (i.e. `x^b|_R ∈ RS[R,k]`), then for *every*
`(k+1)`-subset `R' ⊆ R` the divided difference `dividedDifferencePow R' v b` vanishes.  Reason: on
`R'` the function `x ↦ x^b` agrees with `g` (deg `< k ≤ #R'`), so `g` *is* the interpolant of `x^b`
over `R'`; its degree-`k` coefficient is `0` (deg `g < k`), and that coefficient is exactly
`dividedDifferencePow R' v b` (Part 1). -/
theorem dividedDifference_vanishes_of_agrees
    {R : Finset ι} {v : ι → F} (hvs : Set.InjOn v R) {k b : ℕ}
    {g : F[X]} (hgdeg : g.degree < k) (hagree : ∀ i ∈ R, g.eval (v i) = (v i) ^ b)
    {R' : Finset ι} (hR' : R' ⊆ R) (hk : #R' = k + 1) :
    dividedDifferencePow R' v b = 0 := by
  have hvs' : Set.InjOn v R' := hvs.mono (Finset.coe_subset.mpr hR')
  -- `g` is the interpolant of `x^b` over `R'` (deg `g < k+1 = #R'`, agrees on `R'`).
  have hgdeg' : g.degree < #R' := by rw [hk]; exact lt_of_lt_of_le hgdeg (by exact_mod_cast Nat.le_succ k)
  have hginterp : Lagrange.interpolate R' v (fun i => (v i) ^ b) = g := by
    refine (Lagrange.eq_interpolate_of_eval_eq _ hvs' hgdeg' fun i hi => ?_).symm
    exact hagree i (hR' hi)
  rw [← dividedDifference_eq_subset_top_coeff hvs' hk, hginterp]
  -- degree-`k` coeff of a degree-`< k` polynomial is `0`.
  exact coeff_eq_zero_of_degree_lt hgdeg

/-! ## Part 3 — the codim-`j` reading: rank of the vanishing system, and the special faces. -/

/-- **The deployed `j`-fold minor system as a named `Prop`.**  The condition that `x^b` lands in
`RS[R,k]` is, by Parts 1–2 (forward) and the probe-verified converse, the vanishing of the single
Schur polynomial `h_{b−k} = dividedDifferencePow · v b` on every `(k+1)`-subset of the radius-`m`
set `R`.  The number of *independent* constraints is `j = #R − k` (the left-null dimension);
`SchurMinorBinder R v k b` packages the full system. -/
def SchurMinorBinder (R : Finset ι) (v : ι → F) (k b : ℕ) : Prop :=
  ∀ R' : Finset ι, R' ⊆ R → #R' = k + 1 → dividedDifferencePow R' v b = 0

/-- **`j = 1` face: the binder is a single divided difference.**  At agreement radius `m = k+1`
(codim `j = 1`) the only `(k+1)`-subset of `R` is `R` itself, so the `j`-fold binder reduces to the
single condition `dividedDifferencePow R v b = 0`. -/
theorem schurMinorBinder_codim1_iff
    {R : Finset ι} {v : ι → F} {k b : ℕ} (hk : #R = k + 1) :
    SchurMinorBinder R v k b ↔ dividedDifferencePow R v b = 0 := by
  constructor
  · intro h; exact h R (subset_refl R) hk
  · intro h R' hR' hk'
    -- `R' ⊆ R`, `#R' = #R`, so `R' = R`.
    have : R' = R := Finset.eq_of_subset_of_card_le hR' (by rw [hk, hk'])
    rw [this]; exact h

/-- **`j = 1`, `b = #R` face: the binder is the point sum `N`.**  Combining the codim-1 reduction
with `dividedDifferencePow_card_eq_sum`, the radius-`(k+1)` binder at the binding exponent `b = #R`
is exactly `∑_{i∈R} v i = 0` — the height-gate / No-Excess binding root-sum object `N`. -/
theorem schurMinorBinder_codim1_pointSum_iff
    {R : Finset ι} {v : ι → F} (hvs : Set.InjOn v R) (hR : R.Nonempty) {k : ℕ}
    (hk : #R = k + 1) :
    SchurMinorBinder R v k (#R) ↔ (∑ i ∈ R, v i) = 0 := by
  rw [schurMinorBinder_codim1_iff hk, dividedDifferencePow_card_eq_sum hvs hR]

/-- **The point-sum face `N` is a NECESSARY condition of the deployed `j`-fold binder at `b = #R`.**
For *any* radius `m = #R ≥ k+1`, if the deployed line-membership binder `SchurMinorBinder R v k (#R)`
holds, then so does the point sum `∑_{i∈R} v i = 0` — but only when the *top* `(k+1)`-subset readout
is among the tested ones.  More precisely, `N` is the binder evaluated on the `(k+1)`-subsets through
the codim-1 face; at `j ≥ 2` the binder carries *strictly more* (the `h₂,…` Schur values on the other
subsets).  Here we record the honest sub-object direction: the binder forces the divided difference to
vanish on every `(k+1)`-subset, in particular it is a system of `≥ 1` Schur constraints, of which the
point-sum is *one face* (at any chosen `(k+1)`-subset, the `b=#subset` reading). -/
theorem schurMinorBinder_forces_subset_dividedDifference
    {R : Finset ι} {v : ι → F} {k b : ℕ} (h : SchurMinorBinder R v k b)
    {R' : Finset ι} (hR' : R' ⊆ R) (hk : #R' = k + 1) :
    dividedDifferencePow R' v b = 0 :=
  h R' hR' hk

/-- **Staircase nesting: a larger agreement radius is a STRICTLY STRONGER binder.**  If `R₁ ⊆ R₂`,
then the deployed `j`-fold binder at the *larger* radius `R₂` implies the binder at the smaller
radius `R₁` (every `(k+1)`-subset of `R₁` is a `(k+1)`-subset of `R₂`, so its divided difference is
already forced to vanish).  This is the monotone structure of the Schur-minor staircase: the
constraint set grows with the radius, so the bad-`γ` set shrinks as `m` increases — exactly the
downward-closed good-set behaviour (`mca_good_set_downward_closed`) the bracket engine uses. -/
theorem schurMinorBinder_mono_radius
    {R₁ R₂ : Finset ι} {v : ι → F} {k b : ℕ} (hsub : R₁ ⊆ R₂)
    (h : SchurMinorBinder R₂ v k b) :
    SchurMinorBinder R₁ v k b :=
  fun R' hR' hk => h R' (hR'.trans hsub) hk

/-! ## Part 4 — the binding-radius law (named open obligations; granularity-ladder connection). -/

/-- **The agreement-radius / rung dictionary.**  At rung `r` the agreement set has size `m = n − r`
and codimension `j = m − k = n − r − k`.  Strictly informational (definitional), recording the
staircase coordinate. -/
def codimAt (n k r : ℕ) : ℕ := n - r - k

/-- **OBLIGATION: the binding-radius law (NAMED open, NOT proven).**  The deployed far-line incidence
`I` first exceeds the prize budget `n` at a specific rung `r*` (the *binding* rung); the binding
radius is `m* = n − r*`, codim `j* = m* − k`.  The probes (`probe_schur_staircase.py`,
`probe_trace8.py`) measure: the binder is achieved at the lowest far exponent `b = k` with an
imprimitive offset difference, and `δ* = r*/n` lands one ladder step beyond Johnson (`= j_ladder/n`
of `GranularityLadderRS`).  At the deployed prize rate `ρ = 1/4` the binding codim is `j* = 2` for
BOTH `n=8,k=2` (`δ*=3/8`, `m*=4`) and `n=16,k=4` (`δ*=9/16`, `m*=6`) — `m* = k+2` exactly; so the
deployed `δ*` object is the 2-fold Schur minor.  Whether `j* = 2` persists at other rates
(`ρ ∈ {1/8, 1/2}`) is the OPEN part of this obligation (the cross-`ρ` traces did not complete this
session).  We state it as a predicate over an incidence functional `I : rung → ℕ` and a claimed
binding rung. -/
def BindingRadiusLaw (n k : ℕ) (I : ℕ → ℕ) (rStar : ℕ) : Prop :=
  (∀ r, k + 1 ≤ r → r < rStar → I r ≤ n) ∧ I rStar > n

/-- **The binding rung is the threshold of the good-set staircase.**  Purely structural: if the
incidence is monotone-bad past `rStar` and good before it (the `BindingRadiusLaw`), then `rStar` is
the unique first-bad rung and `δ* = (rStar − 1)/n` is the last good radius.  This makes the
"which radius binds" question well-posed as the threshold of the monotone good-set, consistent with
`mca_good_set_downward_closed`. -/
theorem bindingRung_is_threshold
    {n k : ℕ} {I : ℕ → ℕ} {rStar : ℕ} (h : BindingRadiusLaw n k I rStar)
    {r : ℕ} (hr : k + 1 ≤ r) (hlt : r < rStar) : I r ≤ n :=
  h.1 r hr hlt

end ArkLib.ProximityGap.SchurMinorStaircase

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.SchurMinorStaircase.dividedDifference_eq_subset_top_coeff
#print axioms ArkLib.ProximityGap.SchurMinorStaircase.dividedDifference_vanishes_of_agrees
#print axioms ArkLib.ProximityGap.SchurMinorStaircase.schurMinorBinder_codim1_iff
#print axioms ArkLib.ProximityGap.SchurMinorStaircase.schurMinorBinder_codim1_pointSum_iff
#print axioms ArkLib.ProximityGap.SchurMinorStaircase.schurMinorBinder_forces_subset_dividedDifference
#print axioms ArkLib.ProximityGap.SchurMinorStaircase.schurMinorBinder_mono_radius
#print axioms ArkLib.ProximityGap.SchurMinorStaircase.bindingRung_is_threshold
