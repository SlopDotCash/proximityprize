/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.FactorAssignmentPigeonhole
import ArkLib.ToMathlib.CentreVanishingSupply

/-!
# Issue #304 — the double assignment: both pigeonholes composed, one numeric input

The truncation capstone's per-place inputs arrive through **two stacked pigeonholes**:

1. **Claim 5.7** (factor assignment): each good place's decoded divisibility at the full
   integer interpolant `Q₀` routes to *some* irreducible-factor representative `rep R'`;
   pigeonholing over the `m₁` factors of `Q` hands one representative `≥ |goodSet|/m₁`
   places.
2. **The branch assignment**: at the chosen representative, the centre specialization
   factors as `∏ Hᵢ`; the decoded centre values land on *some* branch `Hᵢ`; pigeonholing
   over the `m₂` centre factors hands one branch `≥ |goodSet|/(m₁·m₂)` places.

This file composes them (`double_assignment`) with the arithmetic glue
(`exists_n_of_mul_le`): **one numeric inequality** `m₁ · (m₂ · (n + 1)) ≤ |goodSet|` delivers
a factor representative `R'`, a branch `H`, and a matching set of `> n` places carrying BOTH
per-place facts the capstone consumes —

* `(Y′ − C (Pz z)) ∣ (rep R')|_{Z:=z}` (the `hdvd` field), and
* `H(z, (Pz z).eval x₀) = 0` (the `hinc` field)

— with the branch `H` drawn from any chosen factorization of the centre specialization of
`rep R'` (the `PigeonholeFactorSupply.exists_factorization_with_hypotheses` output, which
also carries `Hypotheses`/monic/irreducible/positive-degree for the chosen `H`).

## References
* [BCIKS20] Claim 5.7, §5.2.6, §6; issue #304.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate

namespace ArkLib

namespace DoubleAssignmentChain

variable {F : Type} [Field F]

/-! ## Arithmetic glue -/

/-- The trivial witness: `m·(n+1) ≤ N` produces a count `n' > n` with `m·n' ≤ N`. -/
theorem exists_n_of_mul_le {m n N : ℕ} (h : m * (n + 1) ≤ N) :
    ∃ n', n < n' ∧ m * n' ≤ N :=
  ⟨n + 1, Nat.lt_succ_self n, h⟩

/-! ## The double assignment -/

/-- **The double assignment (both pigeonholes composed).**  From the Claim-5.7 assignment
data, per-good-place decoded divisibilities at `Q₀`, a centre-specialization factorization of
each representative, and the single count `m₁ · (m₂ · n) ≤ |goodSet|` — a factor
representative `R'`, a branch index `i`, and a matching set of `≥ n` places carrying BOTH
per-place capstone inputs. -/
theorem double_assignment [DecidableEq F] [DecidableEq ((RatFunc F)[X][Y])]
    {Q : (RatFunc F)[X][Y]} {Q₀ : (F[X])[X][Y]} {x₀ : F}
    (rep : (RatFunc F)[X][Y] → (F[X])[X][Y]) (bad : F[X])
    (hassign : ∀ z : F, bad.eval z ≠ 0 → ∀ q : F[X],
      (Polynomial.X - Polynomial.C q) ∣
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) →
        ∃ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
          (Polynomial.X - Polynomial.C q) ∣
            (rep R).map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hfne : (UniqueFactorizationMonoid.factors Q).toFinset.Nonempty)
    -- the per-representative centre-specialization factorizations:
    (nF : (RatFunc F)[X][Y] → ℕ)
    (HfF : (R' : (RatFunc F)[X][Y]) → Fin (nF R') → F[X][Y])
    (hfacF : ∀ R' ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
      Bivariate.evalX (Polynomial.C x₀) (rep R') = ∏ i, HfF R' i)
    (hnF : ∀ R' ∈ (UniqueFactorizationMonoid.factors Q).toFinset, 0 < nF R')
    {Pz : F → F[X]} {goodSet : Finset F}
    (hgood_bad : ∀ z ∈ goodSet, bad.eval z ≠ 0)
    (hdvd : ∀ z ∈ goodSet, (Polynomial.X - Polynomial.C (Pz z)) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    {n : ℕ}
    (hcount : (UniqueFactorizationMonoid.factors Q).toFinset.card
        * ((Finset.univ.sup (fun R' : {R // R ∈ (UniqueFactorizationMonoid.factors Q).toFinset}
            => nF R'.1)) * n) ≤ goodSet.card) :
    ∃ R' ∈ (UniqueFactorizationMonoid.factors Q).toFinset, ∃ i : Fin (nF R'),
      ∃ matchingSet : Finset F,
        matchingSet ⊆ goodSet ∧ n ≤ matchingSet.card ∧
        (∀ z ∈ matchingSet, (Polynomial.X - Polynomial.C (Pz z)) ∣
          (rep R').map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) ∧
        (∀ z ∈ matchingSet,
          Polynomial.evalEval z ((Pz z).eval x₀) (HfF R' i) = 0) := by
  classical
  -- first pigeonhole: the factor representative
  obtain ⟨R', hR', ms₁, hms₁_sub, hms₁_card, hms₁_dvd⟩ :=
    FactorAssignmentPigeonhole.exists_rep_incidence_large rep bad hassign hfne
      hgood_bad hdvd
      (n := (Finset.univ.sup (fun R'' : {R // R ∈ (UniqueFactorizationMonoid.factors Q).toFinset}
        => nF R''.1)) * n) hcount
  -- the centre vanishing on ms₁, via the evaluation-order swap
  have hvan : ∀ z ∈ ms₁,
      Polynomial.evalEval z ((Pz z).eval x₀)
        (Bivariate.evalX (Polynomial.C x₀) (rep R')) = 0 :=
    fun z hz => CentreVanishingSupply.centre_vanishing_of_specialized_dvd
      (hms₁_dvd z hz) x₀
  -- second pigeonhole: the branch, over the chosen representative's centre factors
  have hfac' : Bivariate.evalX (Polynomial.C x₀) (rep R') = ∏ i, HfF R' i := hfacF R' hR'
  have hsne : (Finset.univ : Finset (Fin (nF R'))).Nonempty := by
    have h0 := hnF R' hR'
    exact ⟨⟨0, h0⟩, Finset.mem_univ _⟩
  have hcount₂ : (Finset.univ : Finset (Fin (nF R'))).card * n ≤ ms₁.card := by
    have hle : nF R' ≤ Finset.univ.sup
        (fun R'' : {R // R ∈ (UniqueFactorizationMonoid.factors Q).toFinset} => nF R''.1) :=
      Finset.le_sup (f := fun R'' : {R // R ∈ (UniqueFactorizationMonoid.factors Q).toFinset}
        => nF R''.1) (Finset.mem_univ ⟨R', hR'⟩)
    have : (Finset.univ : Finset (Fin (nF R'))).card = nF R' := Finset.card_fin _
    rw [this]
    calc nF R' * n
        ≤ (Finset.univ.sup (fun R'' : {R // R ∈ (UniqueFactorizationMonoid.factors Q).toFinset}
            => nF R''.1)) * n := Nat.mul_le_mul_right _ hle
      _ ≤ ms₁.card := hms₁_card
  obtain ⟨i, _, ms₂, hms₂_sub, hms₂_card, hms₂_inc⟩ :=
    BranchValuePigeonhole.matching_supply_of_centre_vanishing
      (R := rep R') (Hf := HfF R') hfac' hsne
      (y := fun z => (Pz z).eval x₀)
      (fun z hz => hvan z hz) hcount₂
  exact ⟨R', hR', i, ms₂, hms₂_sub.trans hms₁_sub, hms₂_card,
    fun z hz => hms₁_dvd z (hms₂_sub hz), hms₂_inc⟩

end DoubleAssignmentChain

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.DoubleAssignmentChain.exists_n_of_mul_le
#print axioms ArkLib.DoubleAssignmentChain.double_assignment
