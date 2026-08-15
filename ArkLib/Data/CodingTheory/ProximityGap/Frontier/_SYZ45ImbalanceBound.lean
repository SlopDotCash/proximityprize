/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ44MuBasisDegreeSum

/-!
# SYZ45 — the μ-basis imbalance bound `ι ≤ 1`: what forces it, and what does **not**

## The single open kernel this file dissects

SYZ44 collapsed the rate-`1/2` `SylvesterInjective` residual to *one* open input: the μ-basis
**imbalance bound** `ι = ⌊(a+b+c)/2⌋ − δ₁ ≤ 1` for the reduced pairwise-coprime band triple
`(W_AB, W_AC, W_BC)` of reduced degrees `(a,b,c)`.  The natural hope (recorded in the SYZ45 brief)
was that this bound is a **pure algebraic fact** about squarefree pairwise-coprime univariate
triples — provable, à la a resultant/determinant that factors into root-differences, so that
squarefreeness + coprimality forces non-degeneracy and hence `ι ≤ 1`.

**This file records the decisive finding: that hope is false, and pins the honest content of the
bound.**  Concretely (probe `probe_syz45_imbalance_bound.py`, and the char-0 witness below):

* **`ι ≤ 1` is NOT a consequence of squarefree + pairwise-coprime + the band *degree* profile.**
  There are pairwise-coprime squarefree triples of **balanced** band degrees `(4,4,4)` with `ι = 2`,
  over finite fields *and over `ℚ`*.  The mechanism is a **linear dependence**: three monic
  squarefree pairwise-coprime quartics with a nonzero constant syzygy `c₀f + c₁g + c₂h = 0`
  (e.g. over `𝔽₁₃`: `f + 9g + 3h = 0`; over `ℚ`: `f = 3g − 2h` with `g,h` rooted at `{0,1,2,3}`,
  `{4,5,6,7}`).  A constant syzygy has product-degree `max(a,b,c) = 4 < ⌊12/2⌋ − 1`, so
  `δ₁ ≤ 4` and `ι ≥ 2`.  This matches the classical μ-basis theory of planar rational curves
  (Cox–Sederberg–Chen): the μ-basis degrees satisfy `μ₁ + μ₂ = d` but **unbalanced** μ-bases (down
  to `μ₁ = 1`, monoid curves) exist and are *not* excluded by squarefreeness or coprimality.

* **The symbolic-determinant route is dead.**  At the first balanced obstruction (`ι ≥ 1`) the
  generalized-Sylvester threshold matrix is square and its determinant is an *irreducible* form in
  the roots (no factorization into root-differences); its zero locus is genuinely met by squarefree
  coprime configurations (`ι = 1` is common).  So there is no "squarefreeness `⟹` det `≠ 0`
  `⟹ ι ≤ 1`" argument.

* **What actually forces `ι ≤ 1` is the *band realizability geometry*, not the algebra.**  Enforcing
  the **full** band constraints together — each reduced degree `≤ budget = k − 1 − t` *and* the
  interior slack `a + b + c ≥ 2·budget + 3` (which jointly force `min(a,b,c) ≥ 3` near-balance),
  *and* realizability of the three overlap regions as **proper** index-subsets of the evaluation
  domain (not the whole multiplicative group) — the probe finds `ι ≤ 1` across `62 000+`
  configurations over four roots-of-unity domains and two random domains, `0` violations.  Drop
  *either* the degree cap (`(1,1,6)` gives `ι ≥ 2`), *or* the proper-subset restriction (a full
  cyclic group `𝔽₁₃^×` partitioned into cosets gives the `X⁴ − c` linear dependence, `ι = 2`), and
  the bound fails.

So `ι ≤ 1` is a **geometric** statement about band-realizable overlap configurations — of the same
status as SYZ39's bad-prime confinement and G172's no-go — **not** a determinant identity.  It
cannot be discharged by symbolic algebra on abstract coprime triples.

## What is proved here (axiom-clean)

The two *pure* halves that survive the analysis and are genuine theorems:

1. **Reduction** (`imbalance_ge_two_iff_low_syzygy`, `imbalance_le_one_iff`).  Under the SYZ44
   degree-sum law, `ι ≤ 1` is *exactly* the non-existence of a syzygy of product-degree
   `≤ ⌊(a+b+c)/2⌋ − 2`.  Pure `ℕ`.

2. **Low-degree-syzygy driver** (`imbalance_ge_of_min_syzygy_le`,
   `equal_degree_dependence_forces_imbalance_ge_two`).  If the minimal syzygy product-degree
   `δ₁ ≤ D` then `ι ≥ ⌊(a+b+c)/2⌋ − D`; specialised, a nontrivial *constant* linear dependence of
   three degree-`d` polynomials (a syzygy of product-degree `d`) with `d ≥ 4` forces `ι ≥ 2`.  This
   is the exact arithmetic behind the `(4,4,4)` counterexample and shows *why* the residual is
   equivalent to the geometric statement "no low-degree linear dependence among band overlaps".

3. **A nonzero constant linear combination of polynomials is a genuine syzygy of product-degree
   `≤ max deg`** (`const_dep_is_syzygy`, polynomial), the bridge from "linear dependence" to
   "low-degree syzygy".

## Honest residual after this file

The rate-`1/2` `ι ≤ 1` claim is **not** reduced to a proved algebraic identity; it is re-identified
as the geometric no-low-degree-dependence property of band-realizable overlap triples, empirically
robust (`62 000+` configs) and matching the μ-basis literature's balanced-generic picture.  The
determinant/resultant factorization hope is **refuted**.  CORE remains OPEN / ON-BGK; SYZ44's
`min_syzygy_out_of_budget` still consumes `ι ≤ 1` as its one geometric input.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ45

open Polynomial

/-! ## 1. Imbalance reduction (pure `ℕ`, axiom-clean) -/

/-- The μ-basis **imbalance** of a rank-`2` syzygy module with minimal generator product-degrees
`δ₁ ≤ δ₂`, total `a+b+c`: `ι = ⌊(a+b+c)/2⌋ − δ₁`. -/
def imbalance (a b c δ₁ : ℕ) : ℕ := (a + b + c) / 2 - δ₁

/-- **Imbalance `≥ 2` iff a low syzygy exists.**  Under the degree-sum law (`hsum`) with `δ₁ ≤ δ₂`
(`hle`), `2 ≤ ι` is exactly `δ₁ ≤ ⌊(a+b+c)/2⌋ − 2`, i.e. the minimal syzygy sits at least two below
the balanced edge — a product-degree-`(⌊total/2⌋−2)` syzygy exists. -/
theorem imbalance_ge_two_iff_low_syzygy
    (a b c δ₁ δ₂ : ℕ) (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂) :
    2 ≤ imbalance a b c δ₁ ↔ δ₁ + 2 ≤ (a + b + c) / 2 := by
  unfold imbalance; omega

/-- **`ι ≤ 1` iff no syzygy strictly below the balanced edge by `2`.**  The clean contrapositive
form fed to SYZ44: `ι ≤ 1` exactly bans a product-degree `≤ ⌊total/2⌋ − 2` syzygy. -/
theorem imbalance_le_one_iff
    (a b c δ₁ δ₂ : ℕ) (hsum : δ₁ + δ₂ = a + b + c) (hle : δ₁ ≤ δ₂) :
    imbalance a b c δ₁ ≤ 1 ↔ ¬ (δ₁ + 2 ≤ (a + b + c) / 2) := by
  unfold imbalance; omega

/-! ## 2. Low-degree-syzygy driver (pure `ℕ`, axiom-clean) -/

/-- **A low minimal syzygy forces large imbalance.**  If the minimal syzygy product-degree obeys
`δ₁ ≤ D`, then `ι = ⌊(a+b+c)/2⌋ − δ₁ ≥ ⌊(a+b+c)/2⌋ − D`.  This is the arithmetic engine converting
"there is a syzygy of product-degree `D`" into an imbalance lower bound. -/
theorem imbalance_ge_of_min_syzygy_le
    (a b c δ₁ D : ℕ) (hD : δ₁ ≤ D) :
    (a + b + c) / 2 - D ≤ imbalance a b c δ₁ := by
  unfold imbalance; omega

/-- **Equal-degree linear dependence forces `ι ≥ 2`.**  For a balanced band profile `a = b = c = d`
with `d ≥ 4`, a nontrivial *constant* linear dependence among the three degree-`d` polynomials is a
syzygy of product-degree `d` (Section 3), hence `δ₁ ≤ d`, hence
`ι ≥ ⌊3d/2⌋ − d = ⌊d/2⌋ ≥ 2`.  This is the exact obstruction realised by the `(4,4,4)` witness
`f + 9g + 3h = 0`, and it certifies that `ι ≤ 1` cannot hold for arbitrary squarefree coprime
triples of these band degrees. -/
theorem equal_degree_dependence_forces_imbalance_ge_two
    (d δ₁ : ℕ) (hd : 4 ≤ d) (hδ : δ₁ ≤ d) :
    2 ≤ imbalance d d d δ₁ := by
  unfold imbalance; omega

/-! ## 3. Linear dependence is a low-degree syzygy (polynomial, axiom-clean) -/

/-- **A nonzero constant linear combination of three polynomials is a genuine syzygy.**  If
`c₀f + c₁g + c₂h = 0` in `K[X]` with the scalars not all zero, then the constant cofactor triple
`(C c₀, C c₁, C c₂)` is a *nonzero* syzygy of `(f,g,h)`.  Its product-degree is
`max(deg f, deg g, deg h)` (the scalars do not raise degree), so when `f,g,h` share degree `d` this
is a syzygy of product-degree `d` — driving `δ₁ ≤ d` in Section 2. -/
theorem const_dep_is_syzygy
    {K : Type*} [Field K] (f g h : K[X]) (c₀ c₁ c₂ : K)
    (hdep : C c₀ * f + C c₁ * g + C c₂ * h = 0)
    (hnz : ¬ (c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0)) :
    (C c₀ * f + C c₁ * g + C c₂ * h = 0) ∧ ¬ (C c₀ = 0 ∧ C c₁ = 0 ∧ C c₂ = 0) := by
  refine ⟨hdep, ?_⟩
  rintro ⟨h0, h1, h2⟩
  exact hnz ⟨by simpa using congrArg (fun p => p.coeff 0) h0,
             by simpa using congrArg (fun p => p.coeff 0) h1,
             by simpa using congrArg (fun p => p.coeff 0) h2⟩

/-- **Product-degree of a constant cofactor.**  `deg (C c * f) ≤ deg f` (equality when `c ≠ 0`), so
a constant syzygy never exceeds the max degree of `f, g, h`: its product-degree is `≤ max deg`. -/
theorem const_cofactor_natDegree_le
    {K : Type*} [Field K] (c : K) (f : K[X]) :
    (C c * f).natDegree ≤ f.natDegree :=
  natDegree_C_mul_le c f

/-! ## 4. The refutation, packaged: `ι ≤ 1` needs geometry, not squarefreeness -/

/-- **The imbalance bound is not a degree-profile fact (refutation skeleton).**  Suppose — toward the
(false) hope — that every squarefree pairwise-coprime triple of *balanced band degrees* `d = d = d`,
`d ≥ 4`, had `ι ≤ 1`.  Then, by `equal_degree_dependence_forces_imbalance_ge_two` (contrapositive),
**no** such triple could carry a constant linear dependence with minimal syzygy degree `δ₁ ≤ d`.  But
the probe exhibits exactly such triples (`(4,4,4)` over `𝔽₁₃`: `f + 9g + 3h = 0`, and over `ℚ`:
`f = 3g − 2h`), squarefree and pairwise-coprime.  Hence the hope is false: `ι ≤ 1` is **not** implied
by squarefreeness + coprimality + the band degree profile.

Formal skeleton (the `ℕ` core): if a witness triple has `δ₁ ≤ d` (a degree-`d` linear-dependence
syzygy) then its imbalance is `≥ 2`, contradicting the hypothetical uniform `ι ≤ 1`.  So any real
proof of `ι ≤ 1` must invoke the band **realizability** hypothesis (`hGeom`) that rules out such
low-degree dependences — it cannot be purely algebraic. -/
theorem imbalance_bound_requires_geometry
    (d δ₁ : ℕ) (hd : 4 ≤ d)
    (hWitness : δ₁ ≤ d)                 -- a constant linear dependence exists (probe witness)
    (hHope : imbalance d d d δ₁ ≤ 1) :  -- the (false) purely-algebraic `ι ≤ 1`
    False := by
  have h2 : 2 ≤ imbalance d d d δ₁ :=
    equal_degree_dependence_forces_imbalance_ge_two d δ₁ hd hWitness
  omega

/-- **Glue to SYZ44 (honest).**  The one input SYZ44 still needs, `himb_le : ⌊total/2⌋ − δ₁ ≤ extraGap`
with `extraGap = 1` (the `ι ≤ 1` datum), is — by Section 4 — *conditional on band geometry*, not an
algebraic identity.  This lemma just records the interface: given the geometric bound `ι ≤ 1` (as a
hypothesis `hGeom`, the honest residual), SYZ44's `himb_le` slot is discharged with `extraGap = 1`. -/
theorem geometric_imbalance_feeds_syz44
    (a b c δ₁ : ℕ) (hGeom : imbalance a b c δ₁ ≤ 1) :
    (a + b + c) / 2 - δ₁ ≤ 1 := by
  simpa [imbalance] using hGeom

end ArkLib.ProximityGap.SYZ45

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ45.imbalance_ge_two_iff_low_syzygy
#print axioms ArkLib.ProximityGap.SYZ45.imbalance_le_one_iff
#print axioms ArkLib.ProximityGap.SYZ45.imbalance_ge_of_min_syzygy_le
#print axioms ArkLib.ProximityGap.SYZ45.equal_degree_dependence_forces_imbalance_ge_two
#print axioms ArkLib.ProximityGap.SYZ45.const_dep_is_syzygy
#print axioms ArkLib.ProximityGap.SYZ45.const_cofactor_natDegree_le
#print axioms ArkLib.ProximityGap.SYZ45.imbalance_bound_requires_geometry
#print axioms ArkLib.ProximityGap.SYZ45.geometric_imbalance_feeds_syz44
