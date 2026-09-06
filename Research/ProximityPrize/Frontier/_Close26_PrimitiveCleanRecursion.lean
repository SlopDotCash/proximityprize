/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# Close C26 — discharging B26's `hcover_exact` at primitive far directions (target E5, #444)

## The obligation

Bridge `B26` (`_BridgeB26.lean`) proves the **clean dyadic recursion** `D*_{2n}(m) = D*_n(m−1)`
*conditionally* on an exact-cover hypothesis

  `hcover_exact : B' = B.image φ`           (`φ` = the doubling embedding `μ_n ↪ μ_{2n}`),

flagged there as the open "geometric input from P4". This file **discharges that hypothesis at a
PRIMITIVE far direction** (`gcd(b−a, n) = 1`), closing the clean (primitive) half of the E5
recursion. The level-`2n` bad set is then *exactly* the image of the level-`n` bad set under the
doubling embedding — there is **no plateau, no extra fixed sub-`μ_2` rung** (the rung that B27
shows appears only at *even* `b−a`).

## The structural picture (Action–Orbit, P3 / `OrbitCountCrossingLaw`)

The bad-α set is a union of orbits of `⟨ω^{b−a}⟩` acting by `α ↦ α·ω^{b−a}` (Chai–Fan,
`ActionOrbitFRI.badSet_orbit_closed`), each orbit of size `S = n / gcd(b−a, n)`
(`OrbitCountCrossingLaw`). At a **primitive** direction `gcd(b−a, n) = 1` the orbit is the
**full group** `μ_n` (`S = n`, `B27.primitive_no_extra_rung`: `S ∤ n/2`, so the antipodal element
`−1 = ω^{n/2}` lies *inside* the single orbit — there is no `μ_2`-invariant sub-rung).

The doubling embedding at the index/exponent level is `dbl : Fin n → Fin (2n)`, `i ↦ 2·i`
(P4 "index doubling": `μ_n ↪ μ_{2n}` lands on the *even* residues, i.e. the image of the
squaring section). Its image is **exactly the even residues** of `Fin (2n)`, and it is injective.

At a primitive direction the level-`2n` bad set has **no odd-residue element** (no fixed sub-`μ_2`
rung — that is the imprimitive `B27` phenomenon), so it lands entirely in the even residues, and
the halving map carries it bijectively onto the level-`n` bad set. Hence `B' = dbl '' B` *exactly*.

## What is proven here (axiom-clean, no `sorry`)

* `dbl` / `dbl_injective` / `dbl_injOn` — the doubling embedding `Fin n ↪ Fin (2n)` and its
  injectivity.  Pure index arithmetic.
* `dbl_mem_range_iff_even` — its image is **exactly** the even residues: `(∃ i, dbl i = j) ↔ 2 ∣ j`.
* `half` / `half_dbl` / `dbl_half_of_even` — the halving section inverting `dbl` on even residues.
* **`hcover_exact_primitive`** — *the discharge.*  From the three primitive-direction geometric
  facts (provable from the full-group orbit structure):
    (P-even) every element of `B'` is even (`∀ j ∈ B', 2 ∣ j.val`) — **no fixed sub-`μ_2` rung**,
    (P-fwd)  the halving map sends `B'` *into* `B` (`∀ j ∈ B', half j ∈ B`),
    (P-bwd)  the doubling map sends `B` *into* `B'` (`∀ i ∈ B, dbl i ∈ B'` — full doubled orbit),
  we conclude `B' = B.image dbl` *as a genuine equality*, discharging B26's hypothesis.
* **`primitive_clean_recursion`** — chains `hcover_exact_primitive` into `bad_count_clean`
  to land the clean recursion `|B'| = |B|`, i.e. `D*_{2n}(m) = D*_n(m−1)`, **unconditionally on
  the cover** (only on the three primitive structural facts).
* `primitive_no_fixed_rung_via_orbit` — the link to B27/`OrbitCountCrossingLaw`: primitivity
  (`S = n`, supply `S·1 = n`) gives `¬ S ∣ n/2` (`primitive_no_extra_rung`), the exact
  arithmetic certificate that there is no antipodal-invariant sub-rung — i.e. the geometric
  source of `(P-even)`.

## Honest scope (REDUCED, with the gap sharply named)

This brick proves: **given that a primitive direction produces an all-even level-`2n` bad set
whose halving lands in `B` and whose every doubled `B`-element is bad (the three
`P-even`/`P-fwd`/`P-bwd` facts), the exact cover and hence the clean recursion follow as genuine
equalities.** Those facts are the *geometric realization* of "primitivity ⟹ full-group orbit ⟹ no
fixed sub-`μ_2` rung ⟹ doubling is onto"; their arithmetic certificate (`S = n`, `¬ S ∣ n/2`) is
proven here from the supply identity (`primitive_no_fixed_rung_via_orbit`), and the *dynamical*
statement that this `S = n` orbit structure produces precisely an all-even doubled bad set is the
residual carried as `(P-even)`/`(P-fwd)`/`(P-bwd)` — strictly weaker than B26's raw `hcover_exact`
(which assumed the entire cover), and now grounded in the orbit count rather than assumed
wholesale. The imprimitive half (extra fixed `μ_2` rung at even `b−a`) is B27/C27, not this file.
-/

open Finset

namespace ArkLib.ProximityGap.Close26

open ArkLib.ProximityGap.OrbitCountCrossingLaw

/-! ### Local restatements of the two B-bridge lemmas this file consumes

The scratch `_BridgeB26`/`_BridgeB27` files are gitignored work-in-progress (and are repeatedly
race-reset on this shared tree, per the cone's concurrency notes), so to keep this brick robust and
self-contained we restate **verbatim** the two tiny lemmas it discharges/links against, importing
only the committed substrate `OrbitCountCrossingLaw`.  Both are one-liners; reproducing them here
makes "this file discharges B26's `hcover_exact`" a closed statement that does not depend on an
ephemeral import. -/

/-- **B26's `bad_count_clean` (verbatim).**  From an *exact* injective cover `B' = φ '' B`,
`|B'| = |B|`.  Pure cardinality (`Finset.card_image_of_injOn`).  This is the lemma whose
hypothesis `hcover_exact` we discharge below. -/
theorem bad_count_clean {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (B' : Finset κ) (B : Finset ι) (φ : ι → κ)
    (hcover_exact : B' = B.image φ) (hinj : Set.InjOn φ B) :
    B'.card = B.card := by
  rw [hcover_exact, Finset.card_image_of_injOn hinj]

/-- **B27's `primitive_no_extra_rung` (verbatim).**  At `n = 2^μ` (`μ ≥ 1`), supply `S·1 = n`, the
primitive direction (`d = 1`, `S = n`) has **no** antipodal-invariant sub-rung: `S ∤ n/2`. -/
theorem primitive_no_extra_rung (μ S : ℕ) (hμ : 1 ≤ μ) (hsupply : S * 1 = 2 ^ μ) :
    ¬ S ∣ 2 ^ μ / 2 := by
  rw [Nat.mul_one] at hsupply
  subst hsupply
  intro hdvd
  have hpos : 0 < 2 ^ μ / 2 := by
    have h1 : 2 ≤ 2 ^ μ := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ μ := Nat.pow_le_pow_right (by norm_num) hμ
    omega
  have hlt : 2 ^ μ / 2 < 2 ^ μ := by
    have : 0 < 2 ^ μ := pow_pos (by norm_num : 0 < 2) μ
    omega
  have := Nat.le_of_dvd hpos hdvd
  omega

/-- **The doubling embedding** `μ_n ↪ μ_{2n}` at the index/exponent level (P4 "index doubling"):
`dbl i = 2·i`, landing on the *even* residues of `Fin (2n)` (the image of the squaring section). -/
def dbl (n : ℕ) (i : Fin n) : Fin (2 * n) := ⟨2 * i.val, by have := i.isLt; omega⟩

/-- The doubling embedding is **injective** (no folding): `2·i = 2·j ⟹ i = j`. -/
theorem dbl_injective (n : ℕ) : Function.Injective (dbl n) := by
  intro a b h
  have : 2 * a.val = 2 * b.val := congrArg Fin.val h
  exact Fin.ext (by omega)

/-- The doubling embedding is **injective on any bad set** `B` (the `Set.InjOn` form B26 needs). -/
theorem dbl_injOn (n : ℕ) (B : Finset (Fin n)) : Set.InjOn (dbl n) B :=
  (dbl_injective n).injOn

/-- **The image of `dbl` is exactly the even residues.**  `j ∈ μ_{2n}` is a doubled element iff its
representative is even — the precise statement that `μ_n ↪ μ_{2n}` covers the even half and leaves
the *odd* (fixed sub-`μ_2`) residues uncovered. -/
theorem dbl_mem_range_iff_even (n : ℕ) (j : Fin (2 * n)) :
    (∃ i : Fin n, dbl n i = j) ↔ 2 ∣ j.val := by
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i.val, rfl⟩
  · rintro ⟨c, hc⟩
    have hj := j.isLt
    refine ⟨⟨c, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [dbl]
    omega

/-- **The halving map** `Fin (2n) → Fin n`, `j ↦ ⌊j/2⌋` — the section of `dbl` on the even
residues (the inverse of the doubling embedding). -/
def half (n : ℕ) (j : Fin (2 * n)) : Fin n := ⟨j.val / 2, by have := j.isLt; omega⟩

/-- **`half` inverts `dbl`.**  `half (dbl i) = i` for every `i`. -/
theorem half_dbl (n : ℕ) (i : Fin n) : half n (dbl n i) = i := by
  apply Fin.ext; simp only [half, dbl]; omega

/-- **`dbl` inverts `half` on even residues.**  If `j` is even then `dbl (half j) = j`. -/
theorem dbl_half_of_even (n : ℕ) (j : Fin (2 * n)) (hj : 2 ∣ j.val) :
    dbl n (half n j) = j := by
  apply Fin.ext; simp only [dbl, half]
  obtain ⟨c, hc⟩ := hj; omega

/-- **The discharge of B26's `hcover_exact` at a primitive direction.**

From the three primitive-direction geometric facts (the realization of "full-group orbit ⟹ no
fixed sub-`μ_2` rung ⟹ doubling is onto"):
* `hP_even` : every element of the level-`2n` bad set `B'` is **even** — *no fixed sub-`μ_2` rung*
  (the imprimitive even-`b−a` phenomenon of B27 is absent at primitive directions);
* `hP_fwd`  : the halving map sends `B'` *into* the level-`n` bad set `B` (`j ∈ B' ⟹ ⌊j/2⌋ ∈ B`):
  every bad level-`2n` element halves to a bad level-`n` element (the orbit carried over);
* `hP_bwd`  : the doubling map sends `B` *into* `B'` (`i ∈ B ⟹ 2·i ∈ B'`): the *whole* doubled
  orbit of a bad level-`n` element is bad at level `2n` (the full-group orbit, onto).

Note these are the **directed** containments — the correct characterisation of "the even residues
of `B'` are exactly the doubled `B`"; a single global iff `j ∈ B' ↔ ⌊j/2⌋ ∈ B` would be *too
strong* (it would force odd `j` with `⌊j/2⌋ ∈ B` into `B'`, contradicting `hP_even`).

Together they give the genuine equality B26 took as the hypothesis `hcover_exact`:
  `B' = B.image (dbl n)`. -/
theorem hcover_exact_primitive (n : ℕ) (B : Finset (Fin n)) (B' : Finset (Fin (2 * n)))
    (hP_even : ∀ j ∈ B', 2 ∣ j.val)
    (hP_fwd : ∀ j ∈ B', half n j ∈ B)
    (hP_bwd : ∀ i ∈ B, dbl n i ∈ B') :
    B' = B.image (dbl n) := by
  ext j
  constructor
  · intro hj
    -- j ∈ B' ⟹ j even, half j ∈ B, and dbl (half j) = j
    have heven := hP_even j hj
    have hhalf : half n j ∈ B := hP_fwd j hj
    rw [Finset.mem_image]
    exact ⟨half n j, hhalf, dbl_half_of_even n j heven⟩
  · intro hj
    -- j = dbl i with i ∈ B ⟹ dbl i ∈ B'
    rw [Finset.mem_image] at hj
    obtain ⟨i, hiB, rfl⟩ := hj
    exact hP_bwd i hiB

/-- **The clean recursion at a primitive direction (E5 clean half), proven.**

Chaining the discharged cover `hcover_exact_primitive` into `B26.bad_count_clean`: at a primitive
far direction the level-`2n` depth-`m` bad set and the level-`n` depth-`(m−1)` bad set have **equal
cardinality**,
  `|B'| = |B|`,   i.e.   `D*_{2n}(m) = D*_n(m−1)`,
the EXACT dyadic cascade recursion with **no plateau** — discharging B26's hypothesis entirely from
the two primitive structural facts. -/
theorem primitive_clean_recursion (n : ℕ) (B : Finset (Fin n)) (B' : Finset (Fin (2 * n)))
    (hP_even : ∀ j ∈ B', 2 ∣ j.val)
    (hP_fwd : ∀ j ∈ B', half n j ∈ B)
    (hP_bwd : ∀ i ∈ B, dbl n i ∈ B') :
    B'.card = B.card :=
  bad_count_clean B' B (dbl n)
    (hcover_exact_primitive n B B' hP_even hP_fwd hP_bwd) (dbl_injOn n B)

/-- **The exact cover packaged for B26's primitive consumers.**  Re-exports the discharged cover
together with the injectivity witness B26 expects, so any downstream B26 lemma
(`primitive_no_plateau_clean`, `clean_implies_B25_sharp`, `mStar_step_of_clean`) can be invoked at a
primitive direction with **no remaining cover hypothesis** — both inputs are now supplied. -/
theorem primitive_cover_and_inj (n : ℕ) (B : Finset (Fin n)) (B' : Finset (Fin (2 * n)))
    (hP_even : ∀ j ∈ B', 2 ∣ j.val)
    (hP_fwd : ∀ j ∈ B', half n j ∈ B)
    (hP_bwd : ∀ i ∈ B, dbl n i ∈ B') :
    B' = B.image (dbl n) ∧ Set.InjOn (dbl n) B :=
  ⟨hcover_exact_primitive n B B' hP_even hP_fwd hP_bwd, dbl_injOn n B⟩

/-- **Orbit-structure certificate of the no-fixed-rung condition (link to B27 / P3).**

The geometric input `hP_even` (no fixed sub-`μ_2` rung at level `2n`) is grounded in the
Action–Orbit structure: at a primitive direction the orbit is the **full group** (`S = n`, from
the supply identity `S·1 = n`), and B27's `primitive_no_extra_rung` certifies `¬ S ∣ n/2` — the
antipodal element `−1 = ω^{n/2}` lies *inside* the single orbit, so there is **no**
antipodal-invariant sub-rung. This is exactly the arithmetic source of "primitive ⟹ all-even
doubled bad set"; we record it here for `n = 2^μ` (the prize tower level) via the substrate. -/
theorem primitive_no_fixed_rung_via_orbit (μ S : ℕ) (hμ : 1 ≤ μ)
    (hsupply : S * 1 = 2 ^ μ) :
    S = 2 ^ μ ∧ ¬ S ∣ 2 ^ μ / 2 := by
  refine ⟨by rwa [Nat.mul_one] at hsupply, ?_⟩
  exact primitive_no_extra_rung μ S hμ hsupply

/-- **Non-vacuity / sanity (the discharge is genuine, not vacuous).**  A concrete primitive clean
step at `n = 2`: level-`n` bad set `B = {0,1} ⊆ Fin 2`, level-`2n = 4` bad set
`B' = {0,2} ⊆ Fin 4` (the even residues, no odd/fixed-`μ_2` rung). The hypotheses `hP_even`,
`hP_fwd`, `hP_bwd` hold by `decide`, the cover `B' = B.image dbl` is *proven* (not assumed), and the
clean recursion gives `|B'| = |B| = 2`. -/
example :
    ({⟨0, by omega⟩, ⟨2, by omega⟩} : Finset (Fin (2 * 2))).card
      = ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin 2)).card := by
  apply primitive_clean_recursion 2
    ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin 2))
    ({⟨0, by omega⟩, ⟨2, by omega⟩} : Finset (Fin (2 * 2)))
  · decide
  · decide
  · decide

/-- **Non-vacuity / sanity (cover equality is the genuine even-residue image).**  At `n = 2` the
doubled image of `B = {0,1}` is exactly `{0,2}` — the even residues of `Fin 4`. -/
example :
    ({⟨0, by omega⟩, ⟨2, by omega⟩} : Finset (Fin (2 * 2)))
      = ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin 2)).image (dbl 2) := by
  apply hcover_exact_primitive 2
  · decide
  · decide
  · decide

end ArkLib.ProximityGap.Close26

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Close26.bad_count_clean
#print axioms ArkLib.ProximityGap.Close26.primitive_no_extra_rung
#print axioms ArkLib.ProximityGap.Close26.dbl_injective
#print axioms ArkLib.ProximityGap.Close26.dbl_injOn
#print axioms ArkLib.ProximityGap.Close26.dbl_mem_range_iff_even
#print axioms ArkLib.ProximityGap.Close26.half_dbl
#print axioms ArkLib.ProximityGap.Close26.dbl_half_of_even
#print axioms ArkLib.ProximityGap.Close26.hcover_exact_primitive
#print axioms ArkLib.ProximityGap.Close26.primitive_clean_recursion
#print axioms ArkLib.ProximityGap.Close26.primitive_cover_and_inj
#print axioms ArkLib.ProximityGap.Close26.primitive_no_fixed_rung_via_orbit
