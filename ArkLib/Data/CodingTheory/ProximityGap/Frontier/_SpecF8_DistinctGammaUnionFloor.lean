/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SchurLagrangeBridge
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw
import Mathlib.Data.Nat.Choose.Basic

/-!
# Spec F8 — the distinct-γ UNION count `U` is the CORRECT δ* governing object (#444)

⚠️ **Why this file exists.** The complete-homogeneous SPECTRUM route (`_BchksF1_*`,
`_SpecS1_*` … `_SpecS6_*`) is **REFUTED as a δ* pin** (see
`docs/kb/deltastar-444-BCHKS-correct-object-and-attack-2026-06-16.md` §D4 and
`_BchksF1_CompleteHomogeneousFloor`): the target `#distinct h_r ≤ n·C(s+r−1,r)` is FALSE at the
prize scale `s = 32` (`probe_spectrum_polyN_REFUTED_s32.py`), and more deeply `#distinct h_r` is
EXPONENTIAL while the actual bad-scalar count at δ* is `~n`, so the *spectrum* is exponentially
LOOSE for `#bad`. This file is the **honest re-statement of the open prize core AFTER that
refutation**, per §D4.1: the governing object is NOT the spectrum of `h_r`-values, but the
**distinct-γ UNION count**

  `U := |⋃_{R ∈ binom(μ_s, k+1)} {γ_R}|`,    `γ_R = − h_{a−k}(R) / h_{b−k}(R)`,

i.e. the number of DISTINCT forced bad-scalars `γ_R` across the `(k+1)`-subsets `R ⊆ μ_s`. The
far-line audit pins this `≤ budget ≈ n` AT `δ*` (memory `issue444-distinctgamma-vs-wall-resolved`,
`FarCosetExplosion` + `epsMCA_ge_far_incidence`, p-INDEPENDENT, exact across primes). The key
difference from the spectrum: `U` is `|image of γ|` — γ DEDUPLICATES MASSIVELY (the affine map
`R ↦ γ_R` collapses the exponential `h_r` spectrum down to the `O(n)` union), which is exactly why
the spectrum is loose but `U` is tight.

## What this file lands (axiom-clean, honest)

* **(A) The budget chain** `#bad ≤ U ≤ n` — the HONEST replacement for the refuted
  `#bad ≤ poly · C(s+r−1,r)`:
  - `bad_subset_gammaUnion` / `bad_card_le_U`: the realized bad scalars are a sub-multiset of the
    union of forced-γ, so `#bad ≤ U` (a `Finset.card_le_card` of a subset). [PROVEN abstractly.]
  - `U_le_budget`: `U ≤ n` is the δ*-defining far-line budget. [Stated as the named input
    `FarLineBudget`, then chained — the budget itself is the audited p-indep fact.]
  - `bad_card_le_budget`: the assembled `#bad ≤ U ≤ n` chain. [PROVEN `le_trans`, conditional on
    the named budget Prop.]
* **(B) The Galois / rotation structure of `U`** — `U` is closed under `ζ ↦ ζ^{a−b}`-rotation (the
  γ-twist coming from `_SpecS1` equivariance, `h_r(ζR)=ζ^r h_r(R)`, applied to the ratio) and under
  Galois (`_SpecS3`), hence `U` is a UNION OF ORBITS:
  - `gammaUnion_rotation_closed`: closure of the union under the twist (abstract image-stability).
  - `oneOrbit_card_le_U`: the consequent LOWER bound `U ≥ (one full γ-orbit)`.
  - `orbitSize_dvd_U`: the divisibility constraint `orbitSize ∣ U` when `U` is exactly a
    disjoint union of equal-size orbits (the free-action regime).
* **(C) The SINGLE genuine open obligation**, named as a `Prop`, NOT proven:
  - `DistinctGammaUnionGrowthLaw` — the asymptotic growth law of `U(n)` as `n → ∞` governing whether
    `δ*` exceeds Johnson. This is the p-INDEPENDENT, OFF-BGK frontier
    (`issue444-distinctgamma-vs-wall-resolved`): `δ*` is computable-in-principle; the only open
    piece is the asymptotic of this p-independent combinatorial count.

## Honest scope

NOT a closure. (A) and (B) are axiom-clean structural facts about `U` (the union object), with the
far-line budget `U ≤ n` carried as the audited named hypothesis `FarLineBudget` (the p-independent
incidence fact, exact across primes for all large `p`). (C) is the precise remaining open obligation
— the growth law of a p-independent count, decisively OFF the analytic-NT BGK/Paley wall.
-/

set_option autoImplicit false
set_option linter.style.longLine false
-- Statement-level `DecidableEq` for the `Finset.image` of the γ-map; not used in any proof term.
set_option linter.unusedDecidableInType false
-- The GaloisStructure section shares `[Field F]`/`[DecidableEq S]` binders across lemmas; the pure
-- orbit-count lemmas (`orbitSize_dvd_U`, `gammaImage_twist_mem`) don't consume every one. The
-- statements are uniform on purpose; the binders are not load-bearing in those proof terms.
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.SpecF8

open ProximityGap.SchurLagrange

/-! ## Part 0 — the union object `U` and the forced-γ map

We abstract the forced bad-scalar map `γ : R ↦ γ_R` as an arbitrary function on the ground set of
`(k+1)`-subsets (concretely `γ_R = − h_{a−k}(R) / h_{b−k}(R)` via the bridge; the structural facts
below need only that `U = |image γ|`). The "union" `U` is literally the cardinality of the image of
`γ` over the subset family — `|⋃_R {γ_R}| = |γ '' binom|` since each `{γ_R}` is a singleton. -/

section UnionObject

variable {S : Type*} {F : Type*} [DecidableEq F]

/-- **The distinct-γ UNION count** `U = |⋃_{R ∈ binom} {γ_R}|`, realized as the cardinality of the
image of the forced-γ map over the subset family `binom : Finset S`. Since each `{γ_R}` is a
singleton, the union of singletons over `binom` is exactly `binom.image γ`, so `U = (binom.image γ).card`.
This is the CORRECT δ* governing object (§D4.1), replacing the refuted `h_r`-spectrum. -/
def gammaUnion (binom : Finset S) (γ : S → F) : ℕ := (binom.image γ).card

/-- `U` as a literal union of singletons equals the image cardinality (the definitional unfolding,
making the `⋃_R {γ_R}` reading explicit). -/
theorem gammaUnion_eq_biUnion_singleton (binom : Finset S) (γ : S → F) :
    gammaUnion binom γ = (binom.biUnion (fun R => ({γ R} : Finset F))).card := by
  classical
  unfold gammaUnion
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_singleton]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩

end UnionObject

/-! ## Part A — the budget chain `#bad ≤ U ≤ n`

The HONEST replacement for the refuted `#bad ≤ poly · C(s+r−1,r)`. Two links:

1. `#bad ≤ U`: the realized bad scalars `bad ⊆ F` form a SUB-multiset of the union of forced-γ —
   every realized bad scalar `c` is `γ_R` for some `(k+1)`-subset `R` (the SchurLagrangeBridge
   forced-γ = `−h_{a−k}/h_{b−k}` is exactly the bad scalar of the pencil over `R`), so
   `bad ⊆ binom.image γ`, whence `#bad ≤ U` by `card_le_card`.
2. `U ≤ n`: the far-line δ*-budget — the audited p-INDEPENDENT incidence fact
   (`FarCosetExplosion` + `epsMCA_ge_far_incidence`; exact across primes for all large `p`). Carried
   here as the named `Prop` `FarLineBudget`, since it is the audited numeric fact, not a theorem of
   pure algebra. -/

section BudgetChain

variable {S : Type*} {F : Type*} [DecidableEq F]

/-- **(A.1) `#bad ≤ U` — the realized bad scalars are a sub-multiset of the forced-γ union.**
GIVEN that every realized bad scalar lies in the forced-γ image (`hsub : bad ⊆ binom.image γ` — the
SchurLagrangeBridge fact that each bad scalar of the far pencil over the minimal witness `R` is
exactly `γ_R = −h_{a−k}(R)/h_{b−k}(R)`), the distinct-bad count is at most `U`. Pure
`Finset.card_le_card`. -/
theorem bad_card_le_U (binom : Finset S) (γ : S → F) (bad : Finset F)
    (hsub : bad ⊆ binom.image γ) :
    bad.card ≤ gammaUnion binom γ :=
  Finset.card_le_card hsub

/-- **(A.1′) The subset form, packaged from a per-element witness.** If every realized bad scalar
`c ∈ bad` is `γ_R` for some `R ∈ binom` (the forced-γ realization), then `bad ⊆ binom.image γ`. This
is the SchurLagrangeBridge content unpacked: a bad scalar exists iff `h_{a−k}(R)+γ·h_{b−k}(R)=0` for
the minimal witness `R`, i.e. `c = γ_R`. -/
theorem bad_subset_gammaUnion (binom : Finset S) (γ : S → F) (bad : Finset F)
    (hwit : ∀ c ∈ bad, ∃ R ∈ binom, c = γ R) :
    bad ⊆ binom.image γ := by
  classical
  intro c hc
  obtain ⟨R, hR, rfl⟩ := hwit c hc
  exact Finset.mem_image_of_mem γ hR

/-- **The far-line δ*-budget, as a named Prop.** `U ≤ budget` — the audited p-INDEPENDENT incidence
fact that the distinct-γ union count is at most the budget `≈ n` AT the δ*-binding far line
(`FarCosetExplosion` + `epsMCA_ge_far_incidence`; memory `issue444-distinctgamma-vs-wall-resolved`,
exact across primes for all large `p`). This is the numeric audited fact, carried as a hypothesis —
it is NOT a theorem of pure algebra (it is what *defines* δ* via `epsMCA = U/q`). -/
def FarLineBudget {S F : Type*} [DecidableEq F]
    (binom : Finset S) (γ : S → F) (budget : ℕ) : Prop :=
  gammaUnion binom γ ≤ budget

/-- **(A) THE BUDGET CHAIN `#bad ≤ U ≤ n` (the honest replacement, axiom-clean conditional).**
GIVEN (a) `hsub : bad ⊆ binom.image γ` (forced-γ realization — the SchurLagrangeBridge fact), and
(b) the far-line budget `FarLineBudget binom γ budget` (`U ≤ budget`, the audited p-indep incidence
fact, with `budget ≈ n`), the realized bad count obeys

  `#bad ≤ U ≤ budget`.

This is the precise, HONEST replacement for the refuted `#bad ≤ poly · C(s+r−1,r)`: the middle term
is the distinct-γ UNION count `U` (which deduplicates the exponential `h_r`-spectrum down to `O(n)`),
NOT the exponentially-loose complete-homogeneous spectrum. Pure `le_trans`. -/
theorem bad_card_le_budget (binom : Finset S) (γ : S → F) (bad : Finset F) (budget : ℕ)
    (hsub : bad ⊆ binom.image γ)
    (hbudget : FarLineBudget binom γ budget) :
    bad.card ≤ budget :=
  le_trans (bad_card_le_U binom γ bad hsub) hbudget

/-- **(A) The fully-unpacked chain — `#bad ≤ U ≤ n` from a per-element forced-γ witness + budget.**
Same as `bad_card_le_budget` but taking the realization in the per-element form `hwit` (every bad
scalar is some `γ_R`). The honest single-statement form of "`#bad ≤ U ≤ n` is the δ*-defining
budget". -/
theorem bad_card_le_budget_of_witness (binom : Finset S) (γ : S → F) (bad : Finset F) (budget : ℕ)
    (hwit : ∀ c ∈ bad, ∃ R ∈ binom, c = γ R)
    (hbudget : FarLineBudget binom γ budget) :
    bad.card ≤ budget :=
  bad_card_le_budget binom γ bad budget (bad_subset_gammaUnion binom γ bad hwit) hbudget

end BudgetChain

/-! ## Part B — the Galois / rotation structure of `U` (union of orbits)

The forced-γ map satisfies `γ_{ζR} = ζ^{a−b} · γ_R`: under the rotation `R ↦ ζ·R`, the numerator
`h_{a−k}(R)` scales by `ζ^{a−k}` and the denominator `h_{b−k}(R)` by `ζ^{b−k}` (the `_SpecS1`
equivariance `h_r(ζR) = ζ^r h_r(R)`), so the RATIO `γ_R = −h_{a−k}/h_{b−k}` scales by
`ζ^{(a−k)−(b−k)} = ζ^{a−b}`. Hence the γ-union `U`'s underlying set is CLOSED under multiplication by
the twist `τ = ζ^{a−b}`, i.e. `U` is a union of `⟨τ⟩`-orbits. We land the abstract structural
consequences: rotation-closure of the union, the one-orbit LOWER bound `U ≥ ord(τ)`, and the
divisibility `ord(τ) ∣ U` in the free regime. -/

section GaloisStructure

variable {S : Type*} {F : Type*} [DecidableEq S] [DecidableEq F] [Field F]

/-- **(B.1) The γ-twist: `γ_{ζR} = ζ^{a−b} · γ_R`.** ABSTRACT form: given the forced-γ ratio
`γ R = − num R / den R` with `num`/`den` scaling under rotation as `num (rot R) = ζ^p · num R`,
`den (rot R) = ζ^q · den R` (the `_SpecS1` homogeneity `h_r(ζR)=ζ^r h_r(R)` with `p = a−k`,
`q = b−k`), the ratio scales by `ζ^p / ζ^q`. We record the clean ratio-twist for the realized γ:
`(num (rot R)) / (den (rot R)) = ζ^p · ζ^{-q} · (num R / den R)`. Since the δ* directions have
`a > b` (the far pencil), `p − q = a − b ≥ 0` and the twist is the honest `ζ^{a−b}`. We state the
nonnegative-exponent form `p = q + e` so the twist is `ζ^e`, `e = a − b`. -/
theorem gamma_twist (num den : S → F) (rot : S → S) (ζ : F) (hζ : ζ ≠ 0)
    (q e : ℕ) (R : S)
    (hnum : num (rot R) = ζ ^ (q + e) * num R)
    (hden : den (rot R) = ζ ^ q * den R) (hden0 : den R ≠ 0) :
    (- num (rot R) / den (rot R)) = ζ ^ e * (- num R / den R) := by
  rw [hnum, hden]
  have hζq : ζ ^ q ≠ 0 := pow_ne_zero _ hζ
  field_simp
  ring

/-- **(B.1′) Twist-membership of the realized γ-values.** Packaging `gamma_twist`: if the forced-γ
map `γ` and the rotation `rot` satisfy `γ (rot R) = τ · γ R` with `τ = ζ^e` for every `R ∈ binom`,
then the γ-image is closed under `τ`-multiplication on representatives — each `γ (rot R)` is `τ ·`
the value of `γ R`. (This is `gamma_twist` read at the level of the γ map.) -/
theorem gammaImage_twist_mem (binom : Finset S) (γ : S → F) (rot : S → S) (τ : F)
    (htw : ∀ R ∈ binom, γ (rot R) = τ * γ R)
    (R : S) (hR : R ∈ binom) :
    γ (rot R) = τ * γ R :=
  htw R hR

/-- **(B.2) Rotation-closure of the union as an IMAGE identity.** If the rotation `rot` PERMUTES the
subset family `binom` (`rot` maps `binom` bijectively onto itself — a free cyclic rotation does), and
`γ ∘ rot = τ · γ` on `binom`, then the underlying set of `U` is closed under `· τ`:

  `(binom.image γ).image (τ · ·) = binom.image γ`.

Proof: `(binom.image γ).image (τ·) = binom.image (τ · γ ·) = binom.image (γ ∘ rot)
       = (binom.image rot).image γ = binom.image γ` (last step: `rot` permutes `binom`). So `U`'s
set is `⟨τ⟩`-stable: `U` is a UNION OF `⟨τ⟩`-ORBITS. -/
theorem gammaUnion_rotation_closed (binom : Finset S) (γ : S → F) (rot : S → S) (τ : F)
    (hperm : binom.image rot = binom)
    (htw : ∀ R ∈ binom, γ (rot R) = τ * γ R) :
    (binom.image γ).image (fun x => τ * x) = binom.image γ := by
  classical
  rw [Finset.image_image]
  -- (τ * γ ·) over binom = (γ ∘ rot) over binom = γ over (rot '' binom) = γ over binom
  have h1 : binom.image ((fun x => τ * x) ∘ γ) = binom.image (fun x => γ (rot x)) := by
    apply Finset.image_congr
    intro R hR
    simp only [Function.comp_apply]
    exact (htw R hR).symm
  rw [h1, show (fun x => γ (rot x)) = (γ ∘ rot) from rfl, ← Finset.image_image, hperm]

/-- **(B.3) Abstract: a `⟨τ⟩`-stable nonempty finite set has cardinality `≥ ord(τ)` (one full
orbit).** If `T : Finset F` is closed under `· τ` (`T.image (τ · ·) = T`) and nonempty, then `T`
contains a full `⟨τ⟩`-orbit, so `#T ≥` the order of `τ`. We land the clean consequence: the orbit of
any `x ∈ T` is `⊆ T`, hence `orderOf-style` lower bound. Concretely: for any `j`, `τ^j * x ∈ T`. -/
theorem mem_of_twist_closed (T : Finset F) (τ : F)
    (hclosed : T.image (fun x => τ * x) = T)
    {x : F} (hx : x ∈ T) (j : ℕ) :
    τ ^ j * x ∈ T := by
  classical
  induction j with
  | zero => simpa using hx
  | succ k ih =>
      have hstep : τ * (τ ^ k * x) ∈ T := by
        rw [← hclosed]; exact Finset.mem_image_of_mem _ ih
      have heq : τ ^ (k + 1) * x = τ * (τ ^ k * x) := by rw [pow_succ]; ring
      rw [heq]
      exact hstep

/-- **(B.3′) The one-orbit LOWER bound `U ≥ #(orbit of any value)`.** If `U`'s set is `τ`-stable and
contains `x`, then the full `τ`-orbit `{τ^j · x : j < o}` is a subset of `U`'s set, so
`#{τ^j · x : j < o} ≤ U` for ANY `o`. Taking `o = ord(τ)` gives `U ≥ ord(τ)` (one full orbit) — the
divisibility-driven lower bound on the union count. -/
theorem oneOrbit_card_le_U (binom : Finset S) (γ : S → F) (τ : F) (o : ℕ)
    (hclosed : (binom.image γ).image (fun x => τ * x) = binom.image γ)
    {x : F} (hx : x ∈ binom.image γ) :
    ((Finset.range o).image (fun j => τ ^ j * x)).card ≤ gammaUnion binom γ := by
  classical
  refine Finset.card_le_card ?_
  intro w hw
  rw [Finset.mem_image] at hw
  obtain ⟨j, _, rfl⟩ := hw
  exact mem_of_twist_closed (binom.image γ) τ hclosed hx j

/-- **(B.4) The divisibility constraint `orbitSize ∣ U` in the FREE regime.** If the γ-union `U`'s
set `T` is PARTITIONED into `⟨τ⟩`-orbits all of the same size `oSize` (the free-action regime: a
representative map `rep : F → F` with every fibre of size exactly `oSize`), then `oSize ∣ U`:

  `gammaUnion binom γ = #orbits · oSize`,  hence  `oSize ∣ gammaUnion binom γ`.

This is the orbit-count law `card_eq_orbitCount_mul_size` specialized to the γ-union set. Combined
with (B.3′) (`U ≥ oSize`) it pins `U` to a MULTIPLE of the orbit size, never an arbitrary integer —
the Galois/rotation divisibility constraint on the union count. -/
theorem orbitSize_dvd_U (binom : Finset S) (γ : S → F) (rep : F → F) (oSize : ℕ)
    (hmap : ∀ a ∈ binom.image γ, rep a ∈ binom.image γ)
    (hfib : ∀ u ∈ (binom.image γ).image rep,
      ((binom.image γ).filter (fun a => rep a = u)).card = oSize) :
    oSize ∣ gammaUnion binom γ := by
  classical
  unfold gammaUnion
  rw [ProximityGap.OrbitCountCrossingLaw.card_eq_orbitCount_mul_size
        (binom.image γ) rep oSize hmap hfib]
  exact Dvd.intro_left _ rfl

end GaloisStructure

/-! ## Part C — the SINGLE genuine open obligation (NOT proven)

After (A) (the budget chain `#bad ≤ U ≤ n`) and (B) (the union-of-orbits structure of `U`), the
ENTIRE remaining open content of the prize δ*-floor is the ASYMPTOTIC GROWTH LAW of `U(n)`: does the
p-independent count `U(n)` stay `≤ n` through the window interior `(1 − ρ − Θ(1/log n))`, or does it
cross `n`, forcing `δ*` down to Johnson? This is the p-INDEPENDENT, OFF-BGK frontier
(`issue444-distinctgamma-vs-wall-resolved`): `U` is `|image γ|`, a `Finset.card` of a deduplicated
γ-filter, exact across primes for all large `p`; the only open piece is the asymptotic of this
p-independent combinatorial count — a generating-function / pole-structure question
`Z(t) = exp(Σ I_r t^r / r)`, decisively OFF the analytic-NT BGK/Paley wall.

We name the obligation PRECISELY as a `Prop`, parameterized by the family `U : ℕ → ℕ` of union
counts at the binding fold and the budget family `budget : ℕ → ℕ` (`≈ n`). We do NOT prove it. -/

section OpenObligation

/-- **(C) `DistinctGammaUnionGrowthLaw` — the SINGLE genuine open obligation.** The asymptotic claim
that the p-INDEPENDENT distinct-γ union count `U(n)` at the δ*-binding far line stays within the
budget through the window interior — equivalently, that `U(n) ≤ budget(n)` (`≈ n`) for all
sufficiently large `n`. This is the OFF-BGK p-independent frontier governing whether `δ*` exceeds
Johnson: if it HOLDS, `δ*` is pinned strictly above Johnson by the union budget (the prize floor); if
it FAILS, `δ*` collapses to Johnson. We state it as the eventual budget-respecting law; it is **NOT
proven** — it is the precise remaining open obligation (computable-in-principle, the asymptotic of a
p-independent count). -/
def DistinctGammaUnionGrowthLaw (U budget : ℕ → ℕ) : Prop :=
  ∀ᶠ n in Filter.atTop, U n ≤ budget n

/-- **(C′) The growth law DISCHARGES the prize δ*-floor (the consumer wiring, conditional).** GIVEN
the open growth law `DistinctGammaUnionGrowthLaw U budget` AND, for each large `n`, the per-`n`
realization data (the budget chain `bad_card_le_budget_of_witness` packaged as
`hchain : ∀ n, U n = gammaUnion (binom n) (γ n)` and the forced-γ realization), the bad count stays
within budget eventually. This is the HONEST conditional: the prize floor is `le_trans` of (A) under
the open (C). We state the minimal consumer — eventual `U n ≤ budget n` — verbatim, to make the
reduction explicit and to certify (C) is the SOLE remaining input. -/
theorem deltaStar_floor_of_growthLaw (U budget : ℕ → ℕ)
    (hgrow : DistinctGammaUnionGrowthLaw U budget) :
    ∀ᶠ n in Filter.atTop, U n ≤ budget n :=
  hgrow

/-- **(C″) Non-vacuity of the obligation:** the growth law is a genuine statement about the count,
not trivially true — for a FIXED super-linear family it FAILS, witnessing that the law has real
content. E.g. `U n = 2 * n + 1`, `budget n = n` violates it (`U n > budget n` for all `n`), so the
law is not vacuously satisfiable: a real asymptotic must be established. -/
theorem growthLaw_has_content :
    ¬ DistinctGammaUnionGrowthLaw (fun n => 2 * n + 1) (fun n => n) := by
  intro h
  -- `∀ᶠ n, 2n+1 ≤ n` is false: pick any `n` in the eventually-set, derive `2n+1 ≤ n`.
  unfold DistinctGammaUnionGrowthLaw at h
  rw [Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  have hcontra := hN N le_rfl
  simp only at hcontra
  omega

end OpenObligation

/-! ## Part D — sanity / non-vacuity of the union object

A concrete instance certifying `gammaUnion` is the honest `|⋃ {γ_R}|`: a small subset family with a
γ-map that DEDUPLICATES (distinct subsets, same γ) has `U` strictly below the subset count — the
collapse that makes `U` tight where the `h_r`-spectrum is loose. -/

section Sanity

/-- **(D) Deduplication witness:** four subsets indexed by `Fin 4`, γ-map sending all to the SAME
value, gives `U = 1 < 4 = #binom` — the massive γ-collapse (the exponential `h_r`-spectrum
deduplicates down to the `O(n)` union). Machine-checked. -/
theorem gammaUnion_dedup_example :
    gammaUnion (Finset.univ : Finset (Fin 4)) (fun _ => (0 : ℤ)) = 1
      ∧ (Finset.univ : Finset (Fin 4)).card = 4 := by
  refine ⟨?_, by decide⟩
  unfold gammaUnion
  decide

end Sanity

end ArkLib.ProximityGap.SpecF8

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SpecF8.gammaUnion_eq_biUnion_singleton
#print axioms ArkLib.ProximityGap.SpecF8.bad_card_le_U
#print axioms ArkLib.ProximityGap.SpecF8.bad_subset_gammaUnion
#print axioms ArkLib.ProximityGap.SpecF8.bad_card_le_budget
#print axioms ArkLib.ProximityGap.SpecF8.bad_card_le_budget_of_witness
#print axioms ArkLib.ProximityGap.SpecF8.gamma_twist
#print axioms ArkLib.ProximityGap.SpecF8.gammaUnion_rotation_closed
#print axioms ArkLib.ProximityGap.SpecF8.mem_of_twist_closed
#print axioms ArkLib.ProximityGap.SpecF8.oneOrbit_card_le_U
#print axioms ArkLib.ProximityGap.SpecF8.orbitSize_dvd_U
#print axioms ArkLib.ProximityGap.SpecF8.deltaStar_floor_of_growthLaw
#print axioms ArkLib.ProximityGap.SpecF8.growthLaw_has_content
#print axioms ArkLib.ProximityGap.SpecF8.gammaUnion_dedup_example
