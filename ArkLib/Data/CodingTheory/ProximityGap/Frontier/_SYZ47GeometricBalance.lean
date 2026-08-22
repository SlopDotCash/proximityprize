/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ45ImbalanceBound

/-!
# SYZ47 — the geometric-balance imbalance floor `δ₁ ≥ max(a,b,c)`

## Where this sits

SYZ44 collapsed the rate-`1/2` `SylvesterInjective` residual to a single open geometric input, the
μ-basis **imbalance bound** `ι = ⌊(a+b+c)/2⌋ − δ₁ ≤ 1` for the reduced pairwise-coprime band triple
`(W_AB, W_AC, W_BC)` of reduced degrees `(a,b,c)`, with `δ₁ ≤ δ₂` the two minimal syzygy
*product-degrees* (`δ₁ + δ₂ = a + b + c`).  SYZ45 **refuted** the pure-algebra hope: balanced
degrees `(4,4,4)` admit `ι = 2` via a constant syzygy — but *only* for triples that are **not
band-realizable**.  So `ι ≤ 1` is geometric, and the question is which band structure forces it.

This file extracts the sharpest **unconditional** partial provable from the band's *triangle*
structure, and pins exactly which band sub-region it covers.

## The band triangle inequalities

In the band each reduced degree is capped, `a, b, c ≤ budget = k − 1 − t` (SYZ37 uniform window),
while the interior slack forces `a + b + c ≥ 2·budget + 3` (G172).  Hence the two smallest reduced
degrees sum to `≥ (2·budget + 3) − budget > budget ≥` the largest: **each reduced degree is at most
the sum of the other two**,
`a ≤ b + c`,  `b ≤ a + c`,  `c ≤ a + b`.
(The refuting `(1,1,6)` profile of SYZ45 *violates* this — `6 > 1 + 1` — which is exactly why it is
not band-realizable.)

## The theorem (axiom-clean)

**`δ₁ ≥ max(a,b,c)`** for every band-triangle triple.  Mechanism — the *two-term collapse*:

* **Two-term lower bound** (`two_term_product_degree_ge`, real polynomial theorem).  A nonzero
  syzygy of a coprime *pair* `(W_AC, W_BC)`, `W_AC s_AC + W_BC s_BC = 0`, forces `W_AC ∣ s_BC`
  (coprimality), so `deg s_BC ≥ b` and the carrying slot has product-degree
  `deg(W_BC s_BC) = c + deg s_BC ≥ b + c`.  A two-term syzygy is never cheaper than the sum of the
  two involved degrees.

* **Coordinate floor** (`coord_natDegree_le_product_degree`).  If a whole three-term syzygy has all
  slot product-degrees `≤ δ` and `δ < a := deg W_AB`, then the `AB` slot is degree-forced to vanish
  (`s_AB = 0`); the residual `W_AC s_AC + W_BC s_BC = 0` is a nonzero *two-term* syzygy, so by the
  bound its product-degree is `≥ b + c ≥ a` (triangle) `> δ` — contradiction.  Hence `a ≤ δ`, and
  symmetrically `max(a,b,c) ≤ δ` (`syzygy_product_degree_ge_max`).

Specialised to the minimal syzygy: `δ₁ ≥ max(a,b,c)`, so `ι = ⌊(a+b+c)/2⌋ − δ₁ ≤ ⌊(a+b+c)/2⌋ −
max(a,b,c)`.  In particular **`ι ≤ 1` whenever `max(a,b,c) ≥ ⌊(a+b+c)/2⌋ − 1`**
(`imbalance_le_one_of_max_near_edge`).

## What it covers, and what stays open (honest)

Probe `probe_syz47_geometric_balance.py` (70 397 band-realizable triples over four roots-of-unity
domains + two random domains):

* `δ₁ ≥ max(a,b,c)`: **0 violations** — the floor is unconditional on the band triangle.
* The partial `ι ≤ 1` (region `max(a,b,c) ≥ ⌊(a+b+c)/2⌋ − 1`) covers **37.7 %** of band triples —
  the *moderately unbalanced* strip.  The remaining **62.3 %** balanced interior (`max < ⌊S/2⌋−1`)
  is **not** discharged here (empirically `ι ≤ 1`, `max ι = 1` observed, but the floor only gives
  `ι ≤ ⌊d/2⌋` there — matching the `(4,4,4)⇒ι≤2` tightness).
* **Structured vs random** (matched band sizes, `𝔽₆₁` on `μ₆₀`): contiguous/coset index windows
  (the SYZ6 block-design pattern) sit at `ι = 0` *uniformly* (`4000/4000`), while random disjoint
  windows reach `ι = 1` (`18/4000`).  Structured overlap windows carry a strictly larger margin —
  the production instantiation is deeper inside `ι ≤ 1` than the worst case.

So SYZ47 turns the SYZ45 refutation into a *positive* partial: the imbalance floor `δ₁ ≥ max` is a
genuine theorem, it proves `ι ≤ 1` on the unbalanced band strip, and it exactly localises the open
kernel to the balanced interior. CORE remains OPEN / ON-BGK.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ47

open Polynomial

/-! ## 1. Two-term syzygy lower bound (real polynomial theorem, axiom-clean)

A nonzero syzygy of a coprime *pair* costs at least the sum of the two degrees. -/

/-- **Two-term product-degree bound.**  For a coprime pair `(W_AC, W_BC)` with a nonzero two-term
syzygy `W_AC s_AC + W_BC s_BC = 0` (`W_BC, s_BC ≠ 0`), coprimality gives `W_AC ∣ s_BC`, so the
carrying slot has product-degree `deg(W_BC s_BC) ≥ deg W_AC + deg W_BC`.  This is the exact reason a
two-term dependence is never cheaper than the sum of the two involved reduced degrees. -/
theorem two_term_product_degree_ge
    {K : Type*} [Field K] (WAC WBC sAC sBC : K[X])
    (hcop : IsCoprime WAC WBC)
    (hsyz : WAC * sAC + WBC * sBC = 0)
    (hWBC : WBC ≠ 0) (hsBC : sBC ≠ 0) :
    WAC.natDegree + WBC.natDegree ≤ (WBC * sBC).natDegree := by
  have heq : WBC * sBC = WAC * (-sAC) := by linear_combination hsyz
  have hdvd : WAC ∣ WBC * sBC := ⟨-sAC, heq⟩
  have hdvd' : WAC ∣ sBC := hcop.dvd_of_dvd_mul_left hdvd
  have hle : WAC.natDegree ≤ sBC.natDegree := natDegree_le_of_dvd hdvd' hsBC
  have hmul : (WBC * sBC).natDegree = WBC.natDegree + sBC.natDegree := natDegree_mul hWBC hsBC
  omega

/-! ## 2. The coordinate floor: no coordinate exceeds the syzygy product-degree -/

/-- **Coordinate floor.**  Let a nonzero three-term syzygy `W_AB s_AB + W_AC s_AC + W_BC s_BC = 0`
of a pairwise-coprime triple have every slot product-degree `≤ δ`.  If the reduced degree of a
coordinate is at most the sum of the other two (the band triangle inequality) then that coordinate
is at most `δ`: `deg W_AB ≤ δ`.

Proof (two-term collapse): if `δ < deg W_AB` the `AB` slot cannot carry `s_AB ≠ 0` (its degree would
be `≥ deg W_AB > δ`), so `s_AB = 0`; the residual `W_AC s_AC + W_BC s_BC = 0` is a nonzero two-term
syzygy of the coprime pair `(W_AC, W_BC)`, hence by `two_term_product_degree_ge` its product-degree
is `≥ deg W_AC + deg W_BC ≥ deg W_AB > δ`, contradicting the slot bound. -/
theorem coord_natDegree_le_product_degree
    {K : Type*} [Field K] (WAB WAC WBC sAB sAC sBC : K[X]) (δ : ℕ)
    (hcopACBC : IsCoprime WAC WBC)
    (hWAB : WAB ≠ 0) (hWAC : WAC ≠ 0) (hWBC : WBC ≠ 0)
    (htri : WAB.natDegree ≤ WAC.natDegree + WBC.natDegree)
    (hsyz : WAB * sAB + WAC * sAC + WBC * sBC = 0)
    (hnz : ¬ (sAB = 0 ∧ sAC = 0 ∧ sBC = 0))
    (hAB : (WAB * sAB).natDegree ≤ δ)
    (hAC : (WAC * sAC).natDegree ≤ δ)
    (hBC : (WBC * sBC).natDegree ≤ δ) :
    WAB.natDegree ≤ δ := by
  by_contra hlt
  push_neg at hlt   -- `δ < WAB.natDegree`
  -- The `AB` slot must vanish: else its product-degree would be `≥ deg W_AB > δ`.
  have hsAB : sAB = 0 := by
    by_contra hs
    have hmul : (WAB * sAB).natDegree = WAB.natDegree + sAB.natDegree := natDegree_mul hWAB hs
    omega
  subst hsAB
  -- Residual two-term syzygy.
  have hsyz' : WAC * sAC + WBC * sBC = 0 := by
    have := hsyz; simp only [mul_zero, zero_add] at this; exact this
  -- The carrying cofactor `s_BC` is nonzero.
  have hsBC : sBC ≠ 0 := by
    rintro rfl
    have h0 : WAC * sAC = 0 := by simpa using hsyz'
    rcases mul_eq_zero.mp h0 with hh | hh
    · exact hWAC hh
    · exact hnz ⟨rfl, hh, rfl⟩
  have hge := two_term_product_degree_ge WAC WBC sAC sBC hcopACBC hsyz' hWBC hsBC
  -- `b + c ≥ a > δ`, but the `BC` slot is `≤ δ`.
  omega

/-! ## 3. The imbalance floor `δ₁ ≥ max(a,b,c)` and its `ι ≤ 1` corollary -/

/-- **Syzygy product-degree floor.**  Under all three band triangle inequalities and pairwise
coprimality, any nonzero syzygy with slot product-degrees `≤ δ` has `max(a,b,c) ≤ δ`: no reduced
degree is cheaper than the syzygy itself.  Applied to the minimal syzygy this reads `δ₁ ≥ max(a,b,c)`
— the imbalance floor. -/
theorem syzygy_product_degree_ge_max
    {K : Type*} [Field K] (WAB WAC WBC sAB sAC sBC : K[X]) (δ : ℕ)
    (hcopABAC : IsCoprime WAB WAC) (hcopABBC : IsCoprime WAB WBC)
    (hcopACBC : IsCoprime WAC WBC)
    (hWAB : WAB ≠ 0) (hWAC : WAC ≠ 0) (hWBC : WBC ≠ 0)
    (htriAB : WAB.natDegree ≤ WAC.natDegree + WBC.natDegree)
    (htriAC : WAC.natDegree ≤ WAB.natDegree + WBC.natDegree)
    (htriBC : WBC.natDegree ≤ WAB.natDegree + WAC.natDegree)
    (hsyz : WAB * sAB + WAC * sAC + WBC * sBC = 0)
    (hnz : ¬ (sAB = 0 ∧ sAC = 0 ∧ sBC = 0))
    (hAB : (WAB * sAB).natDegree ≤ δ)
    (hAC : (WAC * sAC).natDegree ≤ δ)
    (hBC : (WBC * sBC).natDegree ≤ δ) :
    max WAB.natDegree (max WAC.natDegree WBC.natDegree) ≤ δ := by
  have hA : WAB.natDegree ≤ δ :=
    coord_natDegree_le_product_degree WAB WAC WBC sAB sAC sBC δ
      hcopACBC hWAB hWAC hWBC htriAB hsyz hnz hAB hAC hBC
  -- `B`-coordinate: rotate the syzygy to put `W_AC` in the leading slot.
  have hB : WAC.natDegree ≤ δ := by
    refine coord_natDegree_le_product_degree WAC WAB WBC sAC sAB sBC δ
      hcopABBC hWAC hWAB hWBC htriAC ?_ ?_ hAC hAB hBC
    · linear_combination hsyz
    · rintro ⟨h1, h2, h3⟩; exact hnz ⟨h2, h1, h3⟩
  -- `C`-coordinate.
  have hC : WBC.natDegree ≤ δ := by
    refine coord_natDegree_le_product_degree WBC WAB WAC sBC sAB sAC δ
      hcopABAC hWBC hWAB hWAC htriBC ?_ ?_ hBC hAB hAC
    · linear_combination hsyz
    · rintro ⟨h1, h2, h3⟩; exact hnz ⟨h2, h3, h1⟩
  omega

/-- **Imbalance floor (pure `ℕ`).**  Given the polynomial floor `δ₁ ≥ max(a,b,c)`
(`syzygy_product_degree_ge_max` at the minimal syzygy), the μ-basis imbalance is bounded by the
*balance defect* `⌊(a+b+c)/2⌋ − max(a,b,c)`. -/
theorem imbalance_le_balance_defect
    (a b c δ₁ : ℕ) (hfloor : max a (max b c) ≤ δ₁) :
    SYZ45.imbalance a b c δ₁ ≤ (a + b + c) / 2 - max a (max b c) := by
  unfold SYZ45.imbalance; omega

/-- **Partial `ι ≤ 1` on the unbalanced band strip.**  If the imbalance floor holds
(`max(a,b,c) ≤ δ₁`) and the largest reduced degree sits within `1` of the balanced edge
(`⌊(a+b+c)/2⌋ ≤ max(a,b,c) + 1`, i.e. `max(a,b,c) ≥ ⌊(a+b+c)/2⌋ − 1`), then `ι ≤ 1`.  This is the
band sub-region (empirically `37.7 %` of band triples) discharged unconditionally by the geometric
floor. -/
theorem imbalance_le_one_of_max_near_edge
    (a b c δ₁ : ℕ) (hfloor : max a (max b c) ≤ δ₁)
    (hedge : (a + b + c) / 2 ≤ max a (max b c) + 1) :
    SYZ45.imbalance a b c δ₁ ≤ 1 := by
  unfold SYZ45.imbalance; omega

/-! ## 4. Band triangle inequalities are forced (pure `ℕ`, axiom-clean)

The hypotheses `htriAB/htriAC/htriBC` of §3 are *not* extra assumptions on the syzygy — they are
implied by the band degree cap together with the interior slack.  This records the derivation. -/

/-- **Band ⟹ triangle.**  With each reduced degree capped by `budget` (`a, b, c ≤ budget`) and the
interior slack `2·budget + 3 ≤ a + b + c` (G172), every reduced degree is at most the sum of the
other two.  Stated for the `a`-coordinate; the others are symmetric. -/
theorem band_forces_triangle
    (a b c budget : ℕ)
    (ha : a ≤ budget) (hb : b ≤ budget) (hc : c ≤ budget)
    (hslack : 2 * budget + 3 ≤ a + b + c) :
    a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b := by
  refine ⟨?_, ?_, ?_⟩ <;> omega

end ArkLib.ProximityGap.SYZ47

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ47.two_term_product_degree_ge
#print axioms ArkLib.ProximityGap.SYZ47.coord_natDegree_le_product_degree
#print axioms ArkLib.ProximityGap.SYZ47.syzygy_product_degree_ge_max
#print axioms ArkLib.ProximityGap.SYZ47.imbalance_le_balance_defect
#print axioms ArkLib.ProximityGap.SYZ47.imbalance_le_one_of_max_near_edge
#print axioms ArkLib.ProximityGap.SYZ47.band_forces_triangle
