/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-!
# CREATE — the **difference variety** `V_diff` and the SECOND→FIRST moment reduction (#444)

**Mandate (CREATION pass).**  The variance campaign (`_CreateWraparoundVariance`,
`_JacobiMomentIdentity`) reduced the prize to the single open core
**`OffDiagonalPairCancellation`**: the off-diagonal pair-correlation sum
`Σ_{T ≠ T'} PairCorr(T, T') ≤ o(#Rel)`, where each `PairCorr(T,T')` is the family covariance of
the two phases `Jphase(T)·conj Jphase(T')`.  That is a *second-moment* object (a sum over PAIRS
of relations).  This file does the structural move the second-moment machinery has been pointing
at: it **collapses the pair into a single tuple**, turning the second moment into a *first* moment
over a new variety.

## THE NOVEL OBJECT — `diffTuple` and the difference variety `V_diff`

Given two `r`-tuples `T, T' : Fin r → R` (additive carriers on `μ_n`), define the **difference
tuple**
```
        diffTuple T T'  :=  Fin.append T (-T')  :  Fin (r + r) → R,
```
the `2r`-tuple obtained by concatenating `T` with the *negated* tuple `-T'`.  Its additive defect
is exactly the difference of defects:
```
        Σ (diffTuple T T')  =  Σ T  −  Σ T'.
```
So the **difference variety**
```
        V_diff  :=  { (T, T') ∈ Rel × Rel , T' ≠ T :  Σ T = Σ T' }
                 =  { (T, T') :  diffTuple T T'  lies on the trivial additive relation }
```
is the dimension-`(2r − 1)` correlation variety — the locus where the *concatenated* `2r`-tuple
is itself a (wraparound) additive relation.  This is the object whose first moment governs the
pair correlation.

## THE NEW THEOREM — `secondMoment_eq_firstMoment_diff` (2nd → 1st moment reduction)

For a **unit additive character** `θ` (`θ(a+b)=θ(a)·θ(b)`, `θ 0 = 1`, `|θ s| = 1`; the Gauss
phase is exactly such a `θ`), the per-pair second-moment summand collapses to a single first-moment
summand on the difference tuple:
```
        Jphase θ T · conj (Jphase θ T')  =  Jphase θ (diffTuple T T').      (pairCorr_eq_diff)
```
Summing the off-diagonal `T ≠ T'` gives the headline identity
```
   Σ_T Σ_{T' ≠ T} Jphase θ T · conj (Jphase θ T')
        =  Σ_T Σ_{T' ≠ T} Jphase θ (diffTuple T T').          (secondMoment_eq_firstMoment_diff)
```
The LEFT side is the off-diagonal of the *second moment* (pairs of relations); the RIGHT side is a
*first moment* of `Jphase` over the difference variety (a single sum of `2r`-tuple phases).  The √p
is already gone (each `Jphase` is a unit, `_JacobiMomentIdentity`), and now the *combinatorial*
dimension is back to a single tuple sum — the shape a Deligne/Katz first-moment (Lang–Weil point
count, one `Tr Frob`) bound attacks.

## Why this is the right move

The pair correlation `PairCorr(T,T')` is, per the converged map, the covariance of the events
`𝔭 | N(T)` and `𝔭 | N(T')`.  `diffTuple` realizes that covariance as the divisibility of a SINGLE
norm `N(diffTuple T T')`: the concatenated relation's norm is `N(T)·N̄(T')`, and the shared-prime
clustering of the *pair* becomes the *first-moment* arithmetic of the difference tuple's norm.  So
`OffDiagonalPairCancellation` ⟺ the first moment `Σ Jphase(diffTuple)` over `V_diff` is `≤ o(#Rel)`
— a single equidistribution-of-a-character-sum statement, one rung simpler than a pair statement.

## What this file PROVES (axiom-clean) vs the named open core

PROVED here, axiom-clean, fully general (no `sorry`):
* `diffTuple_sum` — `Σ (diffTuple T T') = Σ T − Σ T'`;
* `onDiff_iff_sum_eq` — `Σ (diffTuple T T') = 0` ⟺ `Σ T = Σ T'` (the `V_diff` membership predicate);
* `char_neg` — a unit additive character sends negation to conjugation (`θ(−s)=conj θ s`);
* `Jphase_prod_append` — the phase product over a concatenation factors;
* `pairCorr_eq_diff` — THE summand reduction: `Jphase T · conj(Jphase T') = Jphase(diffTuple T T')`;
* `secondMoment_eq_firstMoment_diff` — the off-diagonal double sum (second moment) equals the
  off-diagonal first moment of `Jphase` on difference tuples;
* `DiffTrace` / `diffTrace_eq_secondMoment` — the per-prime first moment named as a first-class
  trace, equal to the off-diagonal second moment.

NAMED OPEN (the honest external mathematics, NOT discharged):
* `FirstMomentDiffCancellation` — the first moment of `Jphase` over the difference variety
  `Σ_{T ≠ T'} Jphase(diffTuple T T')` is `≤ o(#Rel)` at `r ≈ log p`.  This is EQUAL (by
  `secondMoment_eq_firstMoment_diff`) to the off-diagonal second moment, hence — once averaged over
  the prime family — to `OffDiagonalPairCancellation`, hence to the prize.  It does NOT close
  anything new: the reduction is an exact equality, so this is the SAME open core re-expressed as a
  single-tuple first moment (a Lang–Weil / Katz character-sum equidistribution on `V_diff`, OPEN at
  growing order).

Honest status: builds the difference variety, proves the second-→first-moment reduction
axiom-clean, and re-expresses the open core as a first moment — genuinely-new *structure* (a cleaner
attack surface), NOT new *closure*.  Issue #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.NextDifferenceVariety

open Finset ComplexConjugate

/-! ## §1 The difference tuple and its additive defect -/

variable {R : Type*} [AddCommGroup R] {r : ℕ}

/-- The **difference tuple** `diffTuple T T' = append T (−T')` — the concatenation of the `r`-tuple
`T` with the negated `r`-tuple `−T'`, a single `2r`-tuple (`Fin (r + r) → R`).  Its support is the
union of the supports of `T` and `T'`; its additive defect is `Σ T − Σ T'`. -/
def diffTuple (T T' : Fin r → R) : Fin (r + r) → R :=
  Fin.append T (-T')

/-- **`diffTuple_sum`** — the additive defect of the difference tuple is the difference of the
two defects: `Σ (diffTuple T T') = Σ T − Σ T'`.  Hence `diffTuple T T'` lies on the trivial
additive relation (`Σ = 0`) ⟺ `Σ T = Σ T'` (the difference-variety membership). -/
theorem diffTuple_sum (T T' : Fin r → R) :
    (∑ i, diffTuple T T' i) = (∑ i, T i) - ∑ j, T' j := by
  unfold diffTuple
  rw [Fin.sum_univ_add]
  have hL : (∑ i : Fin r, Fin.append T (-T') (Fin.castAdd r i)) = ∑ i, T i :=
    Finset.sum_congr rfl (fun i _ => by rw [Fin.append_left])
  have hR : (∑ j : Fin r, Fin.append T (-T') (Fin.natAdd r j)) = ∑ j, (-(T' j)) :=
    Finset.sum_congr rfl (fun j _ => by rw [Fin.append_right]; rfl)
  rw [hL, hR, Finset.sum_neg_distrib]
  abel

/-- **`onDiff_iff_sum_eq`** — the difference tuple lies on the *trivial* additive relation
(`Σ (diffTuple T T') = 0`) exactly on the difference variety `{Σ T = Σ T'}`.  This is the
membership predicate of `V_diff`. -/
theorem onDiff_iff_sum_eq (T T' : Fin r → R) :
    (∑ i, diffTuple T T' i) = 0 ↔ (∑ i, T i) = ∑ j, T' j := by
  rw [diffTuple_sum, sub_eq_zero]

/-! ## §2 The normalized iterated Jacobi phase and the product split

We re-use the `Jphase` of `_JacobiMomentIdentity`: `Jphase θ x = (∏ θ(x_i))·conj(θ(Σ x_i))`,
a UNIT for a unit phase `θ`.  Here `θ` is moreover a unit *additive character*
(`θ(a+b)=θ(a)·θ(b)`, `θ 0 = 1`) — the Gauss phase. -/

/-- The normalized iterated Jacobi phase (matches `_JacobiMomentIdentity.Jphase`). -/
noncomputable def Jphase (θ : R → ℂ) (x : Fin r → R) : ℂ :=
  (∏ i, θ (x i)) * conj (θ (∑ i, x i))

/-- **`Jphase_prod_append`** — the phase *product* over a concatenation factors:
`∏ θ((append T S) i) = (∏ θ(T i))·(∏ θ(S j))`. -/
theorem Jphase_prod_append (θ : R → ℂ) (T S : Fin r → R) :
    (∏ i, θ (Fin.append T S i)) = (∏ i, θ (T i)) * ∏ j, θ (S j) := by
  rw [Fin.prod_univ_add]
  congr 1
  · exact Finset.prod_congr rfl (fun i _ => by rw [Fin.append_left])
  · exact Finset.prod_congr rfl (fun j _ => by rw [Fin.append_right])

/-! ## §3 A unit additive character sends negation to conjugation -/

variable {θ : R → ℂ}

/-- **`char_neg`** — for a unit additive character (`θ(a+b)=θ a·θ b`, `θ 0 = 1`, `|θ s|=1`),
`θ(−s) = conj(θ s)`.  This is the bridge that lets the `conj` in the second-moment summand be
absorbed as the *negated* coordinates of the difference tuple. -/
theorem char_neg (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (s : R) :
    θ (-s) = conj (θ s) := by
  have hne : θ s ≠ 0 := by
    intro h
    have := hunit s
    rw [h] at this
    simp at this
  have hinv : θ (-s) * θ s = 1 := by rw [← hmul, neg_add_cancel, hone]
  have hcc : conj (θ s) * θ s = 1 := by
    have h2 : (Complex.normSq (θ s) : ℂ) = θ s * conj (θ s) := (Complex.mul_conj (θ s)).symm
    rw [hunit] at h2
    rw [mul_comm]; exact h2.symm
  have heq := hinv.trans hcc.symm
  exact mul_right_cancel₀ hne heq

/-! ## §4 The summand reduction: pair correlation = first moment on the difference tuple -/

/-- **`pairCorr_eq_diff`** — THE summand reduction.  For a unit additive character `θ`, the
second-moment pair summand `Jphase θ T · conj (Jphase θ T')` equals the *first*-moment summand
`Jphase θ (diffTuple T T')` on the difference tuple.  The conjugate of the second relation's phase
is absorbed by NEGATING its coordinates (the `−T'` half of `diffTuple`), and the two defect phases
combine into the single difference-defect phase `conj(θ(ΣT − ΣT'))`. -/
theorem pairCorr_eq_diff (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (T T' : Fin r → R) :
    Jphase θ T * conj (Jphase θ T') = Jphase θ (diffTuple T T') := by
  -- RHS: expand Jphase of the difference tuple
  unfold Jphase diffTuple
  rw [Jphase_prod_append θ T (-T')]
  -- the product over the negated tuple = conj of the product over T'
  have hneg : (∏ j, θ ((-T') j)) = conj (∏ j, θ (T' j)) := by
    rw [map_prod]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [Pi.neg_apply, char_neg hmul hone hunit]
  -- the defect of the difference tuple
  have hsum : (∑ i, Fin.append T (-T') i) = (∑ i, T i) - ∑ j, T' j := by
    have h := diffTuple_sum T T'; unfold diffTuple at h; exact h
  rw [hneg, hsum]
  -- conj(θ(ΣT − ΣT')) = conj(θ(ΣT))·θ(ΣT')   [character + conjugation]
  have hdef : conj (θ ((∑ i, T i) - ∑ j, T' j)) = conj (θ (∑ i, T i)) * θ (∑ j, T' j) := by
    rw [sub_eq_add_neg, hmul, map_mul, char_neg hmul hone hunit, Complex.conj_conj]
  rw [hdef]
  simp only [map_mul, Complex.conj_conj]
  ring

/-! ## §5 The off-diagonal second moment = first moment over the difference variety -/

variable [DecidableEq (Fin r → R)]

/-- **`secondMoment_eq_firstMoment_diff`** — THE headline identity.  Summing `pairCorr_eq_diff`
over the off-diagonal `T ≠ T'` (`Rel.erase T`), the off-diagonal of the *second moment* (the pairs
sum `Σ_T Σ_{T'≠T} Jphase T · conj Jphase T'`) equals the *first* moment of `Jphase` over the
difference tuples (`Σ_T Σ_{T'≠T} Jphase (diffTuple T T')`). -/
theorem secondMoment_eq_firstMoment_diff (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T'))
      = ∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ (diffTuple T T') := by
  refine Finset.sum_congr rfl (fun T _ => Finset.sum_congr rfl (fun T' _ => ?_))
  exact pairCorr_eq_diff hmul hone hunit T T'

/-- **`DiffTrace`** — the per-prime **first moment** of the iterated Jacobi phase over the
off-diagonal of the difference variety: `Σ_T Σ_{T'≠T} Jphase θ (diffTuple T T')`.  This single sum
of `2r`-tuple phases is the object a Lang–Weil / Katz character-sum estimate attacks. -/
noncomputable def DiffTrace (θ : R → ℂ) (Rel : Finset (Fin r → R)) : ℂ :=
  ∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ (diffTuple T T')

/-- **`diffTrace_eq_secondMoment`** — the named trace IS the off-diagonal second moment (the same
content, re-expressed as a first moment).  This is the bridge to `_CreateWraparoundVariance`'s
`OffDiagonalPairCancellation`: bounding `DiffTrace` (per prime, then averaged) bounds the pair
correlation sum. -/
theorem diffTrace_eq_secondMoment (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    DiffTrace θ Rel = ∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T') := by
  unfold DiffTrace
  rw [secondMoment_eq_firstMoment_diff hmul hone hunit Rel]

/-! ## §6 The named open core — `FirstMomentDiffCancellation`

The only remaining open content is a bound on the real part of `DiffTrace` (the first moment over
`V_diff`).  Because `diffTrace_eq_secondMoment` is an EXACT equality, this is logically the same
statement as `OffDiagonalPairCancellation` — re-expressed as a single-tuple first moment.  Naming
it separately advertises the cleaner attack surface; it does NOT discharge the open core. -/

/-- **`FirstMomentDiffCancellation`** — the named open core, re-expressed.  The real part of the
first moment of `Jphase` over the difference variety is bounded by a slack `S` (the deviation below
the diagonal Poisson value) at `r ≈ log p`.  This is the Lang–Weil / Katz equidistribution of the
single `2r`-tuple character sum on `V_diff`; by `diffTrace_eq_secondMoment` it equals the
off-diagonal second moment, hence proving it (per prime, averaged over the family) discharges
`OffDiagonalPairCancellation` and closes the prize.  NOT discharged here. -/
def FirstMomentDiffCancellation (θ : R → ℂ) (Rel : Finset (Fin r → R)) (S : ℝ) : Prop :=
  (DiffTrace θ Rel).re ≤ S

/-- **`firstMoment_to_secondMoment_bound`** — the *consumer* direction made explicit: a bound on the
first-moment trace `DiffTrace` is, verbatim, a bound on the off-diagonal second-moment real part.
This is the one-line bridge that lets a future Lang–Weil estimate on `V_diff` feed
`_CreateWraparoundVariance.subPoisson_of_offdiag_nonpos`. -/
theorem firstMoment_to_secondMoment_bound (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (h : FirstMomentDiffCancellation θ Rel S) :
    (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re ≤ S := by
  unfold FirstMomentDiffCancellation at h
  rwa [diffTrace_eq_secondMoment hmul hone hunit Rel] at h

end ArkLib.ProximityGap.Frontier.NextDifferenceVariety

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.NextDifferenceVariety.diffTuple_sum
#print axioms ArkLib.ProximityGap.Frontier.NextDifferenceVariety.onDiff_iff_sum_eq
#print axioms ArkLib.ProximityGap.Frontier.NextDifferenceVariety.char_neg
#print axioms ArkLib.ProximityGap.Frontier.NextDifferenceVariety.Jphase_prod_append
#print axioms ArkLib.ProximityGap.Frontier.NextDifferenceVariety.pairCorr_eq_diff
#print axioms ArkLib.ProximityGap.Frontier.NextDifferenceVariety.secondMoment_eq_firstMoment_diff
#print axioms ArkLib.ProximityGap.Frontier.NextDifferenceVariety.diffTrace_eq_secondMoment
#print axioms ArkLib.ProximityGap.Frontier.NextDifferenceVariety.firstMoment_to_secondMoment_bound
