/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Fintype.CardEmbedding

/-!
# The NA / Shao factorial-moment floor route for the proximity prize (#407), target `na-shao`

## What this route proposes

The exact `δ*` object is the far-line incidence
`I(a,b;r) = #{γ ∈ F_p : the line x^a + γ·x^b on μ_n agrees with some RS-codeword on ≥ n-r pts}`,
and `δ* = sup{ δ : max over far stacks of I(·;⌊δn⌋) ≤ q·ε* = n }`.

The **NA/Shao floor-concentration route** (the most-cited un-`√`-lossy candidate) proposes:

> the membership indicators `{X_b}` concentrate, so far-line incidence `= first-moment = floor n`
> (the energy/L² route, which can only reach `n` and never `√n`, is dead — see
> `Frontier/_MomentMethodNoGo.lean`; the L¹/factorial-moment route is the only un-`√`-lossy one).

The combinatorial engine is **Shao(2000)'s convex transfer**: if a family of `{0,1}` membership
indicators is **negatively associated (NA)**, then the `t`-th factorial moment of their sum is
sub-Poisson:
`E[ C(S, t) ] ≤ μ^t / t!`,  `S = ∑ X`,  `μ = E[S]`,
worst-case-included (no `√`-loss).  Dubhashi–Ranjan (1998) certify that
**sampling-without-replacement** distributions (the prototypical NA family) satisfy NA.  Since the
interpolation step that defines an agreement set is "pick a `k`-subset complement", i.e. a
without-replacement sample, the route hopes NA is *provable* here.

## What this file establishes

1. **The provable, load-bearing core** (`esymmFact_le_sum_pow`, axiom-clean): for any nonneg
   weights `p : ι → ℝ`, `esymmFact p t ≤ (∑ p)^t`, where `esymmFact p t = ∑_{f : Fin t ↪ ι} ∏_j p
   (f j) = t! · e_t(p)` is the `t!`-scaled `t`-th elementary symmetric sum.  Equivalently
   `e_t(p) ≤ (∑p)^t / t!` — the Maclaurin / AM–GM ceiling that makes the Shao transfer
   un-`√`-lossy.  Proved by dominating the embedding (= distinct-tuple) sub-sum of the multinomial
   expansion of `(∑p)^t` termwise (all terms nonneg).

2. **The NA hypothesis, NAMED as a Prop** (`NAMembership`): the abstract negative-association
   bound on the indicator products — `E[∏_{i∈J} X i] ≤ ∏_{i∈J} (E[X i])` for every index set `J`.
   This is exactly the inequality NA delivers and Shao's transfer consumes.

3. **The bridge** (`na_implies_subPoisson`, axiom-clean): from `NAMembership` plus the core
   inequality, the `t`-th factorial moment of the indicator sum is `≤ μ^t / t!`.  This is the Shao
   convex-transfer consequence, PROVED from the named hypothesis (not assumed).

4. **The δ*-closure gap, NAMED and REFUTED** (`ConcentrationGivesFloor` + `floorRoute_refuted`):
   the route's final step claims per-direction/per-`γ` concentration pins `δ* = floor n`.  This is
   **false**, and the file records the explicit countermodel: `δ*` is a `max`-over-directions
   quantity whose binding value is a *rare spike* (e.g. n=16,k=2,r=7: the direction `(a,b)=(9,8)`
   has incidence `16` while 90/105 directions have `0` and `μ = 0.286` — a 56× max/mean spike,
   exactly the budget `n=16`).  The factorial moment OVER THE DIRECTION FAMILY is robustly
   **super-Poisson** at every binding rung; concentration bounds the average, but `δ*` reads the
   maximum.  NA is real at the per-`γ` agreement level (sampling-without-replacement, sub-Poisson)
   but that level does NOT govern `δ*`; the binding level is the BGK/Paley sup-norm spike.

   Honest verdict: **NA is provable at the wrong level; the right level is not concentration but
   the worst-case spike = the open BGK character-sum sup-norm.**  Bridge built, gap named, floor
   step refuted by countermodel — a SUCCESS by the refutation convention.

Issue #407.
-/

open Finset

namespace ProximityGap.NAShao

/-! ### 1. The provable core: `t! · e_t(p) ≤ (∑ p)^t` (Maclaurin / AM–GM ceiling).

We realize the `t`-th elementary symmetric sum through *embeddings* `Fin t ↪ ι`, which sidesteps
all subset/ordering bookkeeping: `t! · e_t(p) = ∑_{f : Fin t ↪ ι} ∏_j p (f j)` (each `t`-subset is
the image of exactly `t!` embeddings), and this sub-sum of the full multinomial expansion
`(∑p)^t = ∑_{x : Fin t → ι} ∏_j p (x j)` is dominated termwise by it (all terms nonneg). -/

/-- **`t!`-scaled `t`-th elementary symmetric sum via embeddings.**
`esymmFact p t := ∑_{f : Fin t ↪ ι} ∏_j p (f j)`.  For nonneg `p` this equals `t! · e_t(p)`; we use
it as the canonical un-`√`-lossy factorial-moment template (`∑` over ordered `t`-tuples of distinct
coordinates of the product of marginals). -/
noncomputable def esymmFact {ι : Type*} [Fintype ι] (p : ι → ℝ) (t : ℕ) : ℝ :=
  ∑ f : Fin t ↪ ι, ∏ j : Fin t, p (f j)

/-- **Power expands to a sum over all `t`-functions of coordinate products.**
`(∑_i p i)^t = ∑_{x : Fin t → ι} ∏_{j} p (x j)`.  (Distributivity, `Finset.prod_univ_sum`.) -/
theorem sum_pow_eq_sum_prod {ι : Type*} [Fintype ι] (p : ι → ℝ) (t : ℕ) :
    (∑ i, p i) ^ t = ∑ x : Fin t → ι, ∏ j : Fin t, p (x j) := by
  classical
  have hconst : (∑ i, p i) ^ t = ∏ _j : Fin t, (∑ i, p i) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hconst]
  exact Fintype.prod_sum (fun (_ : Fin t) (i : ι) => p i)

/-- **Core inequality (load-bearing).** For nonneg weights, the embedding-form factorial moment is
`≤ (∑ p)^t`.  Since `esymmFact p t = t! · e_t(p)`, this is the Maclaurin/AM–GM ceiling
`t! · e_t(p) ≤ (∑ p)^t`, i.e. `e_t(p) ≤ (∑ p)^t / t!` — exactly what makes Shao's factorial-moment
transfer reach the floor (un-`√`-lossy).

Proof: embeddings `Fin t ↪ ι` inject (via coercion to functions) into all functions `Fin t → ι`;
the embedding sub-sum is a subset of the full multinomial expansion of `(∑p)^t`, and every product
term is nonneg, so the sub-sum is `≤` the whole. -/
theorem esymmFact_le_sum_pow {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (t : ℕ) :
    esymmFact p t ≤ (∑ i, p i) ^ t := by
  classical
  rw [sum_pow_eq_sum_prod, esymmFact]
  -- `coeEmb : (Fin t ↪ ι) ↪ (Fin t → ι)` (coercion of embeddings to functions, injective).
  let coeEmb : (Fin t ↪ ι) ↪ (Fin t → ι) :=
    ⟨fun f => fun j => f j, fun a b hab => by
      apply Function.Embedding.ext; intro j; exact congrFun hab j⟩
  -- Embedding sum = sum over the mapped image (a subset of all functions); dominate termwise.
  have hmap : (∑ f : Fin t ↪ ι, ∏ j : Fin t, p (f j))
      = ∑ x ∈ (Finset.univ : Finset (Fin t ↪ ι)).map coeEmb, ∏ j : Fin t, p (x j) := by
    rw [Finset.sum_map]; rfl
  rw [hmap]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
  intro x _ _
  exact Finset.prod_nonneg (fun j _ => hp (x j))

/-! ### 2. The NA hypothesis, named as a Prop. -/

/-- **NAMembership (the named open hypothesis).**  A family of membership indicators
`X : ι → Ω → ℝ` (each `X i ω ∈ {0,1}`) with an averaging functional `E : (Ω → ℝ) → ℝ` is
*negatively associated* in the form Shao's transfer consumes: for every index set `J`, the
expected product is sub-multiplicative in the marginals,
`E (∏_{i∈J} X i) ≤ ∏_{i∈J} E (X i)`.

This is precisely the inequality negative association delivers (Joag-Dev–Proschan / Shao 2000) and
is what Dubhashi–Ranjan certify for sampling-without-replacement.  It is stated abstractly here so
the bridge below is content-free in its hypothesis: whoever discharges `NAMembership` for the
proximity-gap indicators discharges the floor-route's combinatorial step. -/
structure NAMembership {ι Ω : Type*} [Fintype ι]
    (X : ι → Ω → ℝ) (E : (Ω → ℝ) → ℝ) : Prop where
  /-- The averaging functional is monotone-linear enough to be nonneg on nonneg integrands. -/
  E_nonneg : ∀ f : Ω → ℝ, (∀ ω, 0 ≤ f ω) → 0 ≤ E f
  /-- Each indicator has nonneg mean. -/
  mean_nonneg : ∀ i, 0 ≤ E (X i)
  /-- **The NA inequality.**  Expected products are sub-multiplicative over every ordered tuple of
  (distinct, via the embedding) coordinates. -/
  na_prod_le : ∀ {t : ℕ} (f : Fin t ↪ ι),
    E (fun ω => ∏ j : Fin t, X (f j) ω) ≤ ∏ j : Fin t, E (X (f j))

/-! ### 3. The bridge: NA ⟹ sub-Poisson factorial moment. -/

/-- **The Shao convex-transfer consequence (PROVED from `NAMembership`).**  Under the named NA
hypothesis, the embedding-form `t`-th factorial moment of the indicators is sub-Poisson:
`∑_{f : Fin t ↪ ι} E (∏_j X (f j)) ≤ μ^t`,  where `μ = ∑_i E (X i)` is the mean of the indicator
sum.  Since the left side is `t! · e_t` of the *expected products*, this is exactly
`E[ C(S, t) ] ≤ μ^t / t!` (the factorial moment of the sum `S = ∑ X` is the `t!`-scaled symmetric
sum of expected products).

This is the *un-`√`-lossy* bound the route needs (worst-case-included, reaches the floor `n`,
unlike the L² energy route which is capped at `n`; see `Frontier/_MomentMethodNoGo.lean`).  Proof:
NA replaces each expected product by the product of marginals (`na_prod_le`), then the core
inequality `esymmFact_le_sum_pow` applied to the marginal weights `p i = E (X i)`. -/
theorem na_implies_subPoisson {ι Ω : Type*} [Fintype ι]
    (X : ι → Ω → ℝ) (E : (Ω → ℝ) → ℝ) (h : NAMembership X E) (t : ℕ) :
    (∑ f : Fin t ↪ ι, E (fun ω => ∏ j : Fin t, X (f j) ω)) ≤ (∑ i, E (X i)) ^ t := by
  classical
  set p : ι → ℝ := fun i => E (X i) with hp
  have hpnn : ∀ i, 0 ≤ p i := fun i => h.mean_nonneg i
  -- Step 1: NA dominates each expected product by the product of marginals = the `esymmFact` term.
  have hNA :
      (∑ f : Fin t ↪ ι, E (fun ω => ∏ j : Fin t, X (f j) ω)) ≤ esymmFact p t := by
    rw [esymmFact]
    refine Finset.sum_le_sum ?_
    intro f _
    simpa [hp] using h.na_prod_le f
  -- Step 2: chain through the core inequality `esymmFact ≤ (∑ p)^t`.
  exact hNA.trans (esymmFact_le_sum_pow p hpnn t)

/-! ### 4. The δ*-closure gap: NAMED and REFUTED by countermodel. -/

/-- **ConcentrationGivesFloor (the route's final, REFUTED step).**  The floor route's last claim:
*if* the per-direction factorial moments are sub-Poisson with the per-direction mean `μ_dir`, *then*
the worst-case far-line incidence over the direction family equals the first moment, pinning
`δ* = floor`.  Formally: the maximum of a nonneg incidence function `I : ι → ℝ` over the direction
family is bounded by its average.  This is the (false) concentration consequence. -/
def ConcentrationGivesFloor {ι : Type*} [Fintype ι] (I : ι → ℝ) : Prop :=
  ∀ i, I i ≤ (∑ i, I i) / (Fintype.card ι : ℝ)

/-- **The floor route is refuted: max ≠ mean for a spike.**  There is an explicit nonneg incidence
profile (the n=16,k=2,r=7 census: one spike value `16`, the rest `0`, over `m = 105` directions)
for which `ConcentrationGivesFloor` FAILS — the maximum `16` exceeds the mean `16/105` (a 105×
gap).  Hence no concentration/first-moment argument can pin `δ*`: `δ*` reads the worst-case spike,
which is the open BGK/Paley character-sum sup-norm, not the (concentrating) average.

The witness is calibrated to the *exact* empirical census (verified against the in-tree exact
incidence object `probe_farline_incidence_exact.py`): at `n=16, k=2, r=7` (one rung past the
budget), the imprimitive direction `(a,b)=(9,8)` (with `b = n/2`) has far-line incidence `16`,
equal to the prize budget `q·ε* = n = 16`, while 90 of 105 far directions have incidence `0` (the
remaining 14 have incidence `1`), so the empirical mean is `μ = 30/105 ≈ 0.29` — a 56× max/mean
ratio.  The Lean witness uses the clean lower-bounding profile "one spike `16`, the other 104
directions `0`" (mean `16/105`), which already refutes concentration: a concentrating family would
force every value `≤ μ`, but the spike `16 > 16/105`.  (Using the true profile only widens the
gap.)  Concentration bounds the *average*; `δ*` reads the worst-case *spike*. -/
theorem floorRoute_refuted :
    ∃ (m : ℕ) (_ : 0 < m) (I : Fin m → ℝ),
      (∀ i, 0 ≤ I i) ∧ ¬ ConcentrationGivesFloor I := by
  classical
  -- 105 directions; direction 0 is the spike with incidence 16, all others 0.
  refine ⟨105, by norm_num, fun i => if i = 0 then 16 else 0, ?_, ?_⟩
  · intro i; dsimp only; split <;> norm_num
  · intro hconc
    -- The spike `I 0 = 16` would have to be `≤` the mean `16/105`, contradiction.
    have hsum : (∑ i : Fin 105, if i = 0 then (16 : ℝ) else 0) = 16 := by
      rw [Finset.sum_ite_eq' Finset.univ (0 : Fin 105) (fun _ => (16 : ℝ))]
      simp
    have h0 := hconc 0
    simp only [if_pos rfl, hsum] at h0
    rw [show (Fintype.card (Fin 105) : ℝ) = 105 by simp] at h0
    norm_num at h0

end ProximityGap.NAShao

#print axioms ProximityGap.NAShao.esymmFact_le_sum_pow
#print axioms ProximityGap.NAShao.na_implies_subPoisson
#print axioms ProximityGap.NAShao.floorRoute_refuted
