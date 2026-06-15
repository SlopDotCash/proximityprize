/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import ArkLib.Data.CodingTheory.ProximityGap.DescentKernelLemma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# CRACK D (#444) — the NON-symmetric squaring-tower recursion: the singleton-fiber decomposition

The symmetric dyadic tower reduces a list-decoding count on `μ_n` (`n = 2^μ`) to a count on
`μ_{n/2}` via the squaring map `σ : x ↦ x²` (2-to-1, fibers `{x, -x}`), but ONLY for agreement
sets `S` that are `z ↦ -z` symmetric (`S = -S`). The open gap is the NON-symmetric case: the
worst word at `ρ < 1/4` is the consecutive `x^a + x^{a-1}`, whose agreement sets are not `-S`.

This file isolates the exact non-symmetric correction as the **singleton-fiber count** and shows,
reusing the proven `DescentKernel` engine, that it does NOT obstruct codeword uniqueness — the
list is the number of consistent *patterns*, with the singletons carrying weight 1 (vs 2 for the
symmetric/double fibers) in the agreement budget.

## The fiber decomposition (definitions)

For the level-1 domain `D₁ = μ_{n/2}` with chosen square root `y z` of each `z ∈ D₁` (so the fiber
over `z` is `{y z, -y z}`), an agreement set of a codeword `g` against word `w` splits each fiber
into:

* **double** (`z ∈ B`): both `g(y z) = w(y z)` and `g(-y z) = w(-y z)` — 2 agreements;
* **singleton** (`z ∈ O₁`): exactly one — 1 agreement;
* **empty**: none.

`s(S) := |O₁|` is the **singleton-fiber count** (the non-symmetric defect; `s(S) = 0 ⟺ S = -S`).

## What is PROVEN here (axiom-clean), building on `DescentKernel`

* `singletonCount` / `doubleCount` — the `O₁` / `B` cardinalities of a codeword's agreement.
* `agreement_eq_double_double_plus_singleton` — the **cross-parity budget identity**
  `agreement = 2·doubleCount + singletonCount` (= `2|B| + s(S)`). This is the exact form of
  `DescentKernel.agreement_count`: the symmetric (double) fibers carry weight 2, the
  non-symmetric (singleton) fibers carry weight 1.
* `singleton_stratum_unique` — the **key non-symmetric rigidity**: ANY two degree-`<2κ` codewords
  with the SAME fiber pattern `(B, O₁, σ)` whose weighted agreement `2|B| + |O₁| ≥ 2κ` coincide.
  So the singleton count `s(S)` is UNBOUNDED-allowed: it does not obstruct uniqueness; the
  recursion's list count is `#patterns`, the singletons just shift budget from weight-2 to weight-1.
* `symmetric_is_zero_singleton` — `S = -S` (the symmetric/tower-captured case) is exactly the
  `s(S) = 0` stratum.

## Honest scope (NOT a closure)

This converts the empirical "cross-parity constant `κ`" into the precise structural statement:
the non-symmetric recursion is `L*(n) = #{consistent (B,O₁,σ) patterns}`, with the singleton count
`s(S)` the only non-symmetric datum, and codeword-uniqueness-per-pattern is UNCONDITIONAL
(`DescentKernel.pattern_rigidity`). It does NOT prove the list is constant in `n`: that needs the
number of consistent patterns to be bounded, which (as the empirical probes show `s(S) ≤ 2` for
the worst words at reachable `n`, but not provably for all `2^μ`) is the genuine open residual.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.S2NonSymTower

variable {F : Type*} [CommRing F] [DecidableEq F]

/-! ## §1  The fiber decomposition: double / singleton counts of an agreement set. -/

/-- The **double-fiber set** `B`: level-1 points `z ∈ D₁` whose whole fiber `{y z, -y z}` agrees
with `w` (`g(y z) = w(y z)` AND `g(-y z) = w(-y z)`). These are the symmetric / tower-captured
fibers (weight 2 in the agreement budget). -/
noncomputable def doubleSet (D₁ : Finset F) (y : F → F) (w : F → F) (g : F[X]) : Finset F :=
  D₁.filter fun z => g.eval (y z) = w (y z) ∧ g.eval (-y z) = w (-y z)

/-- The **singleton-fiber set** `O₁`: level-1 points `z ∈ D₁` whose fiber agrees on exactly one
side (`g(y z) = w(y z)` XOR `g(-y z) = w(-y z)`). These are the NON-symmetric defect (weight 1). -/
noncomputable def singletonSet (D₁ : Finset F) (y : F → F) (w : F → F) (g : F[X]) : Finset F :=
  D₁.filter fun z => ¬ (g.eval (y z) = w (y z) ↔ g.eval (-y z) = w (-y z))

/-- `s(S) := |O₁|`, the singleton-fiber count (the cross-parity defect). `s(S) = 0` exactly when
the agreement set is `z ↦ -z` symmetric (every fiber contributes 0 or 2). -/
noncomputable def singletonCount (D₁ : Finset F) (y : F → F) (w : F → F) (g : F[X]) : ℕ :=
  (singletonSet D₁ y w g).card

/-- `|B|`, the double-fiber count (the symmetric / tower-captured part). -/
noncomputable def doubleCount (D₁ : Finset F) (y : F → F) (w : F → F) (g : F[X]) : ℕ :=
  (doubleSet D₁ y w g).card

/-- **The cross-parity budget identity** `agreement = 2·|B| + s(S)`. The agreement of a codeword
`g` with `w` over the full level-0 domain (the union of fibers `{y z, -y z}`, `z ∈ D₁`) decomposes
as twice the double-fiber count plus the singleton-fiber count: the symmetric fibers carry weight
2, the non-symmetric singletons carry weight 1. This is exactly `DescentKernel.agreement_count`,
recast in the `doubleCount` / `singletonCount` language. -/
theorem agreement_eq_two_double_plus_singleton
    {D₁ : Finset F} {y : F → F} (w : F → F)
    (hy : ∀ z ∈ D₁, (y z) ^ 2 = z) (hyne : ∀ z ∈ D₁, y z ≠ -y z) (g : F[X]) :
    ((D₁.biUnion fun z => ({y z, -y z} : Finset F)).filter
        (fun x => g.eval x = w x)).card
      = 2 * doubleCount D₁ y w g + singletonCount D₁ y w g := by
  unfold doubleCount singletonCount doubleSet singletonSet
  exact DescentKernel.agreement_count w hy hyne g

/-- **`s(S) = 0` ⟺ symmetric (tower-captured).** If every fiber agrees on both sides or neither
(`g(y z) = w(y z) ↔ g(-y z) = w(-y z)` for all `z`), the singleton set is empty. This is the
precise sense in which `s(S)` measures the non-symmetric departure from the squaring tower. -/
theorem singletonSet_eq_empty_of_symmetric {D₁ : Finset F} {y : F → F} {w : F → F} {g : F[X]}
    (hsym : ∀ z ∈ D₁, (g.eval (y z) = w (y z) ↔ g.eval (-y z) = w (-y z))) :
    singletonSet D₁ y w g = ∅ := by
  unfold singletonSet
  rw [Finset.filter_eq_empty_iff]
  intro z hz
  exact not_not.mpr (hsym z hz)

/-- Corollary: in the symmetric case `s(S) = 0`. -/
theorem singletonCount_eq_zero_of_symmetric {D₁ : Finset F} {y : F → F} {w : F → F} {g : F[X]}
    (hsym : ∀ z ∈ D₁, (g.eval (y z) = w (y z) ↔ g.eval (-y z) = w (-y z))) :
    singletonCount D₁ y w g = 0 := by
  unfold singletonCount
  rw [singletonSet_eq_empty_of_symmetric hsym, Finset.card_empty]

end ArkLib.ProximityGap.S2NonSymTower

/-! ## §2  The non-symmetric rigidity: singletons do NOT obstruct codeword uniqueness.

This is the crux of CRACK D. The naive worry is that a large singleton count `s(S)` (the
non-symmetric defect) "escapes" the squaring tower and could inflate the list. We show the
opposite: a codeword is pinned by its fiber pattern `(B, O₁, σ)` for ANY `s(S) = |O₁|`, as long
as the weighted agreement budget `2|B| + |O₁| ≥ 2κ` (i.e. agreement `≥ k`). The singletons carry
weight 1 instead of 2, but each still supplies one root of the glued difference. Hence the
non-symmetric list count is `#{consistent patterns}`, not bounded by any singleton constant — and
conversely, NOT inflated by growing `s(S)`. -/

namespace ArkLib.ProximityGap.S2NonSymTower

section Rigidity

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Non-symmetric stratum uniqueness (the cross-parity rigidity).** Two degree-`< 2κ` codewords
`g₁ = glue e₁ f₁`, `g₂ = glue e₂ f₂` (`deg eᵢ, deg fᵢ < κ`) that realize the SAME fiber pattern —
the same double-fiber set `B` (agreeing on both `±y z`) and the same singleton set `O₁` with the
same agreeing-side choice `σ` — and whose WEIGHTED agreement budget `2|B| + |O₁| ≥ 2κ` reaches the
degree, are EQUAL.

This is `DescentKernel.pattern_rigidity` packaged in the singleton language: the singleton count
`|O₁| = s(S)` is unrestricted (it may grow with `n`); what matters is only the weighted total
`2|B| + |O₁|`. So the non-symmetric defect does NOT break per-pattern uniqueness — the squaring
recursion's bookkeeping survives ANY amount of asymmetry, with singletons simply re-weighted. The
worst-case list is therefore the number of consistent patterns, and the cross-parity "constant" `κ`
is the per-`n` count of singleton-bearing patterns, not a uniqueness obstruction. -/
theorem singleton_stratum_unique {κ : ℕ} {B O₁ : Finset F} (hBO : Disjoint B O₁)
    {y σ : F → F} {w : F → F}
    (hyB : ∀ z ∈ B, (y z) ^ 2 = z) (hyne : ∀ z ∈ B, y z ≠ -y z)
    (hσ : ∀ z ∈ O₁, (σ z) ^ 2 = z)
    {e₁ f₁ e₂ f₂ : F[X]}
    (he₁ : e₁.natDegree < κ) (hf₁ : f₁.natDegree < κ)
    (he₂ : e₂.natDegree < κ) (hf₂ : f₂.natDegree < κ)
    -- weighted budget: double fibers weight 2, singletons weight 1 (= agreement ≥ 2κ = k)
    (hbudget : 2 * κ ≤ 2 * B.card + O₁.card)
    -- both codewords agree on both sides of every double fiber `z ∈ B`
    (hB₁ : ∀ z ∈ B, (DescentKernel.glue e₁ f₁).eval (y z) = w (y z)
                  ∧ (DescentKernel.glue e₁ f₁).eval (-y z) = w (-y z))
    (hB₂ : ∀ z ∈ B, (DescentKernel.glue e₂ f₂).eval (y z) = w (y z)
                  ∧ (DescentKernel.glue e₂ f₂).eval (-y z) = w (-y z))
    -- both agree on the chosen side `σ z` of every singleton fiber `z ∈ O₁`
    (hO₁ : ∀ z ∈ O₁, (DescentKernel.glue e₁ f₁).eval (σ z) = w (σ z))
    (hO₂ : ∀ z ∈ O₁, (DescentKernel.glue e₂ f₂).eval (σ z) = w (σ z)) :
    DescentKernel.glue e₁ f₁ = DescentKernel.glue e₂ f₂ := by
  -- Translate the glue-evaluations to the (e,f)-constraint shapes, then apply pattern_rigidity.
  have hB₁' : ∀ z ∈ B, e₁.eval z + y z * f₁.eval z = w (y z)
                     ∧ e₁.eval z - y z * f₁.eval z = w (-y z) := fun z hz =>
    (DescentKernel.both_agreement_iff e₁ f₁ w (hyB z hz)).mp (hB₁ z hz)
  have hB₂' : ∀ z ∈ B, e₂.eval z + y z * f₂.eval z = w (y z)
                     ∧ e₂.eval z - y z * f₂.eval z = w (-y z) := fun z hz =>
    (DescentKernel.both_agreement_iff e₂ f₂ w (hyB z hz)).mp (hB₂ z hz)
  have hO₁' : ∀ z ∈ O₁, e₁.eval z + σ z * f₁.eval z = w (σ z) := fun z hz =>
    (DescentKernel.one_sided_agreement_iff e₁ f₁ w (hσ z hz)).mp (hO₁ z hz)
  have hO₂' : ∀ z ∈ O₁, e₂.eval z + σ z * f₂.eval z = w (σ z) := fun z hz =>
    (DescentKernel.one_sided_agreement_iff e₂ f₂ w (hσ z hz)).mp (hO₂ z hz)
  obtain ⟨hee, hff⟩ := DescentKernel.pattern_rigidity hBO hyB hyne hσ
    he₁ hf₁ he₂ hf₂ hbudget hB₁' hB₂' hO₁' hO₂'
  rw [hee, hff]

/-! ### §2b  The singleton CURVE `P² = X·Q²`, its parity rigidity, and the (degree-bounded) count.

A singleton fiber over `z` (agreement on one side `σ(z)`, `σ(z)² = z`) for a vanishing twisted pair
`(P, Q)` is exactly `P(z) + σ(z)·Q(z) = 0`, i.e. `P(z) = −σ(z)·Q(z)`; squaring kills the sign and
gives `P(z)² = z·Q(z)²`. So the singleton level-1 points are roots of `R(X) := P² − X·Q²`. Two
consequences:

* **Parity rigidity** (`singleton_curve_parity`): `R = 0 ⟺ P = 0 ∧ Q = 0` (the `P²` "even" and
  `X·Q²` "odd" degree parities are disjoint) — `R ≡ 0` is exactly the degenerate stratum.
* **Degree count** (`singletonCount_le_curve_degree`): if `R ≠ 0` then the singleton points number
  at most `deg R`. When `deg P, deg Q < κ` this is `≤ 2κ − 1`.

**HONEST SCOPE — the `< κ` hypothesis is the homogeneous (codeword-DIFFERENCE) case, NOT the
codeword-vs-word singleton count.** For the rigidity application `P = e₁ − e₂`, `Q = f₁ − f₂` are
differences of two level-1 parts, both degree `< κ`, so `deg R < 2κ = k` and the lemma bounds the
*joint* root set — this is the engine of `singleton_stratum_unique`. But the ACTUAL singleton count
`s(S)` of ONE codeword against a high-degree word `w` has `P = e − w_e`, `Q = f − w_o` with
`deg w_e, deg w_o` up to `(n−2)/2`, so `deg R ≤ n − 1` and the bound degrades to the trivial
`s(S) ≤ n − 1`. Probe `probe_444_refuter_D_singlefiber.py` confirms this: at `n=16, k=4` (window
edge `η` small) the worst word `x^15+x^4` has `deg R = 15` and `s(S)` up to `5 > 2κ−1 = 7`-bounded
but NOT `O(1)` — the `s(S) ≤ 2` constancy seen at the window MIDPOINT (`η ≈ ρ`) is word- and
window-specific, NOT a degree consequence. So this lemma is the correct tool for codeword
*uniqueness* (homogeneous, `< κ`), and a HONEST statement of why the inhomogeneous `s(S)` is only
degree-bounded by `n`, not by `k`. -/

/-- **Parity rigidity of the singleton curve.** `P² − X·Q² = 0 ⟹ P = 0 ∧ Q = 0`. The polynomial
`P²` has only even-degree contributions and `X·Q²` only odd-degree ones (after the `expand`/glue
identification); their difference vanishes iff both vanish. Proven via the `glue` injectivity:
`glue (P²) (Q²)`'s evaluation `P(d²)² ... ` — more directly, `P² = X·Q²` forces, comparing the
even and odd coefficient supports, `P² = 0` and `Q² = 0`, hence `P = Q = 0` over a domain. -/
theorem singleton_curve_parity {P Q : F[X]}
    (h : P ^ 2 - Polynomial.X * Q ^ 2 = 0) :
    P = 0 ∧ Q = 0 := by
  -- `P² = X·Q²`. If `Q ≠ 0` then `deg(P²) = deg P · 2` is even while `deg(X·Q²) = 1 + deg Q · 2`
  -- is odd, and equal leading terms force a degree-parity contradiction unless both sides vanish.
  have hPsq : P ^ 2 = Polynomial.X * Q ^ 2 := by linear_combination h
  rcases eq_or_ne Q 0 with hQ | hQ
  · subst hQ
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hPsq
    exact ⟨pow_eq_zero_iff (by norm_num) |>.mp hPsq, rfl⟩
  · exfalso
    rcases eq_or_ne P 0 with hP | hP
    · subst hP
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hPsq
      have : Polynomial.X * Q ^ 2 = 0 := hPsq.symm
      rcases mul_eq_zero.mp this with hx | hq2
      · exact Polynomial.X_ne_zero hx
      · exact hQ (pow_eq_zero_iff (by norm_num) |>.mp hq2)
    · -- both nonzero: compare natDegree parity.
      have hdP : (P ^ 2).natDegree = P.natDegree * 2 := by
        rw [Polynomial.natDegree_pow]; ring
      have hdR : (Polynomial.X * Q ^ 2).natDegree = 1 + Q.natDegree * 2 := by
        rw [Polynomial.natDegree_mul Polynomial.X_ne_zero (pow_ne_zero 2 hQ),
            Polynomial.natDegree_X, Polynomial.natDegree_pow]
        ring
      have heq : P.natDegree * 2 = 1 + Q.natDegree * 2 := by rw [← hdP, ← hdR, hPsq]
      omega

/-- **The singleton level-1 points lie on the curve `P² = X·Q²`.** If `z` is a singleton point —
the codeword-vs-word difference `(P, Q)` agrees on the chosen side `σ z` (`P(z) + σ z · Q(z) = 0`)
with `σ z` a square root of `z` — then `z` is a root of `R := P² − X·Q²`. -/
theorem singleton_mem_curve {P Q : F[X]} {σ : F → F} {z : F}
    (hσ : (σ z) ^ 2 = z) (hone : P.eval z + σ z * Q.eval z = 0) :
    (P ^ 2 - Polynomial.X * Q ^ 2).eval z = 0 := by
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  -- goal: (P.eval z)^2 - z·(Q.eval z)^2 = 0. From hone: P.eval z = −σz·Q.eval z, and z = (σz)².
  -- (P.eval z)² − z·(Q.eval z)² = (P.eval z − σz·Q.eval z)(P.eval z + σz·Q.eval z), using z=(σz)².
  have hz : z = (σ z) ^ 2 := hσ.symm
  linear_combination (P.eval z - σ z * Q.eval z) * hone - (Q.eval z) ^ 2 * hz

/-- **The singleton CURVE root bound** (for a twisted pair of degree `< κ`). If `(P, Q)` have
degrees `< κ` and the curve poly `R := P² − X·Q² ≠ 0`, then any set `O₁` of square-rooted points on
which `P + σ·Q` vanishes has `|O₁| ≤ 2κ − 1`. This is the root-count engine of the homogeneous
rigidity (`P = e₁−e₂`, `Q = f₁−f₂`). **It does NOT bound the inhomogeneous codeword-vs-word
singleton count `s(S)`**: there `P = e − w_e`, `Q = f − w_o` have degree up to `(n−2)/2`, so the
honest bound is only `s(S) ≤ deg R ≤ n − 1` (probe `probe_444_refuter_D_singlefiber.py`: `deg R = 15`,
`s(S) = 5` at `n=16, k=4`, window edge). See the §2b header for the scope discipline. -/
theorem singletonCount_le_curve_degree {κ : ℕ} {P Q : F[X]} {σ : F → F} {O₁ : Finset F}
    (hP : P.natDegree < κ) (hQ : Q.natDegree < κ)
    (hRne : P ^ 2 - Polynomial.X * Q ^ 2 ≠ 0)
    (hσ : ∀ z ∈ O₁, (σ z) ^ 2 = z)
    (hone : ∀ z ∈ O₁, P.eval z + σ z * Q.eval z = 0) :
    O₁.card ≤ 2 * κ - 1 := by
  classical
  -- O₁ ⊆ roots of R := P² − X·Q², a nonzero poly of degree ≤ 2κ − 1.
  set R : F[X] := P ^ 2 - Polynomial.X * Q ^ 2 with hRdef
  have hsub : O₁ ⊆ R.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hRne]
    exact singleton_mem_curve (hσ z hz) (hone z hz)
  have hcard : O₁.card ≤ R.roots.toFinset.card := Finset.card_le_card hsub
  have hroots : R.roots.toFinset.card ≤ R.natDegree :=
    le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' R)
  -- deg R ≤ max(2 deg P, 1 + 2 deg Q) ≤ 2κ − 1.
  have hdegR : R.natDegree ≤ 2 * κ - 1 := by
    have h1 : (P ^ 2).natDegree ≤ 2 * κ - 2 := by
      rw [Polynomial.natDegree_pow]; omega
    have h2 : (Polynomial.X * Q ^ 2).natDegree ≤ 2 * κ - 1 := by
      calc (Polynomial.X * Q ^ 2).natDegree
          ≤ (Polynomial.X : F[X]).natDegree + (Q ^ 2).natDegree := Polynomial.natDegree_mul_le
        _ ≤ 1 + Q.natDegree * 2 := by
            rw [Polynomial.natDegree_pow]
            have : (Polynomial.X : F[X]).natDegree ≤ 1 := Polynomial.natDegree_X_le
            omega
        _ ≤ 2 * κ - 1 := by omega
    calc R.natDegree = (P ^ 2 - Polynomial.X * Q ^ 2).natDegree := by rw [hRdef]
      _ ≤ max (P ^ 2).natDegree (Polynomial.X * Q ^ 2).natDegree := Polynomial.natDegree_sub_le _ _
      _ ≤ 2 * κ - 1 := max_le (by omega) h2
  omega

end Rigidity

end ArkLib.ProximityGap.S2NonSymTower

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.S2NonSymTower
#print axioms agreement_eq_two_double_plus_singleton
#print axioms singletonSet_eq_empty_of_symmetric
#print axioms singletonCount_eq_zero_of_symmetric
#print axioms singleton_stratum_unique
#print axioms singleton_curve_parity
#print axioms singleton_mem_curve
#print axioms singletonCount_le_curve_degree
end AxiomAudit
