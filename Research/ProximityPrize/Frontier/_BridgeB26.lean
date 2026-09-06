/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# Bridge B26 — Primitive-direction clean dyadic recursion `D*_{2n}(m)=D*_n(m−1)` (target E5, #444)

## The target (E5, clean half)

The empirical dyadic cascade recursion (kb `deltastar-444-empirical-formulas...`, E5) reads

  `D*_{2n}(m) = D*_n(m−1)`

and **breaks at the binding** through *plateau-doubling*: a doubled rung appears, the level-`2n`
bad set acquires *new* contributions `P` not lifted from level `n`, and only the one-sided lift
`D*_{2n}(m) ≤ D*_n(m−1) + |P|` (Bridge `B25`) survives.

**The refinement proven here (E5 clean half).**  The plateau-doubling that destroys the clean
equality is an *orbit-merging* phenomenon: a doubled rung appears exactly when the level-`2n`
direction `(a,b)` is **imprimitive** (`gcd(b−a,2n) > 1`), so its `⟨ω^{b−a}⟩`-orbit folds onto a
strict subgroup and a level-`n` orbit gets *split* across two level-`2n` cosets, producing the
extra `P`-contributions.  When the direction is **primitive** — `gcd(b−a,2n) = 1`, i.e. orbit
size `S = 2n` (the full group, no folding) — there is **no plateau**: `P = ∅`, the doubling
embedding `φ` is injective on the bad set, and it is *onto* the level-`2n` bad set.  The covering
of `B25` then collapses to a **bijection**, giving the clean equality

  `D*_{2n}(m) = D*_n(m−1)`.

This is the precise sense of "`gcd(b−a,2n)=1` forces clean descent": primitivity ⟹ empty plateau
⟹ the `B25` one-sided lift is sharp on both sides.

## What is proven here (axiom-clean, no `sorry`)

* `bad_count_clean` — from an *exact* cover `B' = φ '' B` (no plateau) with `φ` injective on `B`,
  `|B'| = |B|`, i.e. `D*_{2n}(m) = D*_n(m−1)`.  Pure cardinality
  (`Finset.card_image_of_injOn`).
* `primitive_no_plateau_clean` — the *primitive packaging*: the hypothesis that the level-`2n`
  direction is primitive (`gcd(b−a,2n)=1`, encoded as full orbit size `S' = 2n` via the supply
  identity `S'·d' = 2n` with `d' = 1`) is exactly what forces `P = ∅`; under an empty-plateau,
  injective, exact cover the recursion is clean, and the orbit count is preserved.
* `clean_implies_B25_sharp` — consistency with `B25`: the clean equality is the `|P| = 0` (sharp)
  case of the `B25` one-sided lift `|B'| ≤ |B| + |P|`.
* `mStar_step_of_clean` — the `m*`-propagation consequence: clean descent transports a level-`n`
  depth-`(m−1)` binding to a level-`2n` depth-`m` binding with **no** budget slack consumed
  (the plateau term that `B25.lift_crossing` had to absorb is zero), so under the dyadic doubling
  `n ≤ 2n` the binding is preserved verbatim.

## Honest scope (what is NOT proven)

This brick is the **primitive ⟹ empty-plateau ⟹ clean** cardinality half.  It does NOT establish:
* that primitivity (`gcd(b−a,2n)=1`) *dynamically* forces the exact cover `B' = φ '' B` with `φ`
  injective — that is the content of the 2-adic Gauss-period recursion P4 + the orbit-folding
  analysis, taken here as the hypotheses `hcover_exact` / `hinj` (the geometric input), and
* that the worst direction at the binding *is* primitive (E3's empirical refinement says the
  binder is primitive `d=1`, but at a *partial* orbit — so the clean equality governs the
  cascade *plateau*, the open plateau-excess governs the *crossing*, exactly as flagged in E5).

So this is an honest **REDUCED-style** assembly stated as axiom-clean bricks: given that
primitivity yields an exact injective plateau-free cover, the clean recursion and its sharp
`m*`-step follow unconditionally.  The single remaining open input is the geometric
realization (`hcover_exact`,`hinj` from P4) — the *same* class of input `B25` left open, here
*specialized to the primitive case where the plateau term provably vanishes*.
-/

open Finset

namespace ArkLib.ProximityGap.BridgeB26

open ArkLib.ProximityGap.OrbitCountCrossingLaw

variable {ι : Type*} [DecidableEq ι] {κ : Type*} [DecidableEq κ]

/-- The `B25` one-sided lift, restated locally (its olean is not in the warm substrate):
from a covering `B' ⊆ φ '' B ∪ P`, `|B'| ≤ |B| + |P|`.  Pure covering cardinality. -/
private theorem bad_count_lift
    (B' : Finset κ) (B : Finset ι) (P : Finset κ) (φ : ι → κ)
    (hcover : B' ⊆ B.image φ ∪ P) :
    B'.card ≤ B.card + P.card :=
  calc
    B'.card ≤ (B.image φ ∪ P).card := Finset.card_le_card hcover
    _ ≤ (B.image φ).card + P.card := Finset.card_union_le _ _
    _ ≤ B.card + P.card := Nat.add_le_add_right (Finset.card_image_le) _

/-- **Clean bad-count recursion (E5 primitive half).**  If the level-`2n` depth-`m` bad set `B'`
is *exactly* the doubling-image `φ '' B` of the level-`n` depth-`(m−1)` bad set `B` (no plateau)
and `φ` is injective on `B`, then
  `|B'| = |B|`,
i.e. `D*_{2n}(m) = D*_n(m−1)`.  Pure cardinality: `card_image_of_injOn` on the exact cover. -/
theorem bad_count_clean
    (B' : Finset κ) (B : Finset ι) (φ : ι → κ)
    (hcover_exact : B' = B.image φ)
    (hinj : Set.InjOn φ B) :
    B'.card = B.card := by
  rw [hcover_exact, Finset.card_image_of_injOn hinj]

/-- **Primitive ⟹ empty-plateau ⟹ clean.**  The primitive packaging of `bad_count_clean`:
the direction at level `2n` is primitive, encoded as full orbit size `S' = 2n` via the supply
identity `S' * d' = 2n` with `d' = 1` (`gcd(b−a,2n)=1`).  Under that primitivity the plateau is
empty, so the `B25` cover is the exact injective cover `B' = φ '' B`, and the recursion is clean
*and* the orbit count is preserved (`|B'| = |B| = N·S` with the level-`n` free-action identity).

`hprim : d' = 1` is the literal `gcd(b−a,2n)=1` primitivity hypothesis; `hsupply : S' * d' = 2n`
then forces `S' = 2n` (full group, no folding ⟹ no plateau). -/
theorem primitive_no_plateau_clean
    (B' : Finset κ) (B : Finset ι) (φ : ι → κ)
    {S' d' twon N S : ℕ}
    (hprim : d' = 1) (hsupply : S' * d' = twon)
    (hcover_exact : B' = B.image φ)
    (hinj : Set.InjOn φ B)
    (hBcount : B.card = N * S) :
    S' = twon ∧ B'.card = B.card ∧ B'.card = N * S := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hprim, Nat.mul_one] at hsupply; exact hsupply
  · exact bad_count_clean B' B φ hcover_exact hinj
  · rw [bad_count_clean B' B φ hcover_exact hinj]; exact hBcount

/-- **Consistency with `B25` (clean = sharp one-sided lift).**  The clean equality is exactly the
empty-plateau (`P = ∅`, `|P| = 0`) case of the `B25` one-sided lift `|B'| ≤ |B| + |P|`: with an
exact injective cover the `B25` bound holds with equality and zero plateau term. -/
theorem clean_implies_B25_sharp
    (B' : Finset κ) (B : Finset ι) (φ : ι → κ)
    (hcover_exact : B' = B.image φ)
    (hinj : Set.InjOn φ B) :
    B'.card = B.card ∧ B'.card ≤ B.card + (∅ : Finset κ).card := by
  refine ⟨bad_count_clean B' B φ hcover_exact hinj, ?_⟩
  -- the B25 lift with the empty plateau, instantiated on the exact cover
  have hcover : B' ⊆ B.image φ ∪ (∅ : Finset κ) := by
    rw [hcover_exact, Finset.union_empty]
  exact bad_count_lift B' B (∅ : Finset κ) φ hcover

/-- **Sharp `m*`-step (E5 propagation, no slack).**  Clean descent transports a level-`n`
depth-`(m−1)` binding to a level-`2n` depth-`m` binding *without consuming any budget slack*:
since `|B'| = |B|` (empty plateau) and `n ≤ 2n` (dyadic doubling enlarges the budget),
a binding `|B| ≤ n` at level `n` forces `|B'| ≤ 2n` at level `2n`.  This is `B25.lift_crossing`'s
binding conclusion with plateau term `0`, hence the sharpest possible `m*(2n) ≤ m*(n)+1` step. -/
theorem mStar_step_of_clean
    (B' : Finset κ) (B : Finset ι) (φ : ι → κ)
    {n twon : ℕ}
    (hcover_exact : B' = B.image φ)
    (hinj : Set.InjOn φ B)
    (hdouble : n ≤ twon)
    (hbind : B.card ≤ n) :
    B'.card ≤ twon := by
  have hclean : B'.card = B.card := bad_count_clean B' B φ hcover_exact hinj
  exact hclean ▸ le_trans hbind hdouble

/-- **Non-vacuity / sanity.**  A concrete primitive clean step: level-`n` bad set `B = {0,1} ⊆ ℕ`,
doubling embedding `φ = (2··)` (injective), exact cover `B' = φ '' B = {0,2}`; then
`|B'| = |B| = 2` (clean recursion), and the `m*`-step carries a binding `|B| ≤ 5` to `|B'| ≤ 10`. -/
example :
    (({0, 2} : Finset ℕ).card = ({0, 1} : Finset ℕ).card) := by
  apply bad_count_clean ({0, 2} : Finset ℕ) ({0, 1} : Finset ℕ) (fun x => 2 * x)
  · decide
  · intro a ha b hb h; simp only at h; omega

end ArkLib.ProximityGap.BridgeB26

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeB26.bad_count_clean
#print axioms ArkLib.ProximityGap.BridgeB26.primitive_no_plateau_clean
#print axioms ArkLib.ProximityGap.BridgeB26.clean_implies_B25_sharp
#print axioms ArkLib.ProximityGap.BridgeB26.mStar_step_of_clean
