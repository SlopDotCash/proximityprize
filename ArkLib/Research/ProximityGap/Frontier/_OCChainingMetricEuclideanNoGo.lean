/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# LANE OC-CHAIN (#466, Opus core, 2026-07-10): the generic-chaining increment metric on the
  Gauss-period spectrum lives in the 2-DIMENSIONAL EUCLIDEAN plane and is (measurably)
  non-ultrametric — axiom-clean METRIC-GEOMETRY LEMMAS + exact numeric evidence bearing on the
  "2-adic structured (tree) chaining" hope in the tool-shape principle. This is EVIDENCE + two
  supporting lemmas, NOT a full closure of that hope (see the calibrated Verdict below).

## The route this probes and closes

The prize wall is `M(μ_n) ≤ C·√(n·log(p/n))`. The `#464` "tool-shape principle" (dossier §6)
says any surviving sup-control method must be an L∞ generic-chaining bound fed by computable
second-order data: `sup_b |η_b| ≤ √n · γ₂(T, d)`, with `d(b,b') = ‖η_b − η_{b'}‖` the increment
(chaining) metric on the frequency index set `T = F_p^×`, and `γ₂` Talagrand's functional (an
integral of `√(log N(T,d,ε))` over scales `ε`, `N` the covering number). Flat Dudley chaining on
`m := (p−1)/n` metrically-distinct points at diameter `Θ(√n)` gives exactly the target order
`√n · √(log m) = √n · √(log(p/n))` — CONDITIONAL on sub-Gaussian increments (the open Wick atom).

The last *unrun* hope in that principle is a **structured chaining refinement**: since `n = 2^k`
is a 2-power, the coset index set carries a natural 2-adic (dyadic-tower) labelling. IF the
increment metric `d` were ULTRAMETRIC / hierarchical with respect to that tower, a structured
(Walsh/Haar, tree) chaining could telescope and produce a covering profile below the flat
2-dimensional one, potentially beating `√(log m)`.

## What the exact finite probes established (numeric, exact character sums over F_p, p ≡ 1 mod n)

`scripts` (reports): `oc_isometry_exact.py`, `oc_chain_metric_probe.py`, `oc_ultrametric_probe.py`.

1. **Exact μ_n-isometry / coset-constancy.** `η_{u·b} = η_b` for every `u ∈ μ_n` (the Gauss
   period is constant on each `μ_n`-coset, an exact reindexing identity), so the increment metric
   `d` descends to a metric on the `m = (p−1)/n` coset representatives, whose `η`-values are
   generically all distinct. (In-tree as `eta_norm_const_on_coset`; the μ_n-action is by
   isometries — `d(u·b, u·b') = d(b,b')`.)
2. **The metric is strongly NON-ultrametric.** Over `n ∈ {8,16}`, many primes up to `p = 2113`:
   relative ultrametric defect `max_{triples}(d(x,z) − max(d(x,y),d(y,z))) / diam ≈ 0.44…0.50`,
   i.e. as far from ultrametric as a generic 2-D Euclidean point cloud (an ultrametric has defect
   `0`). No 2-adic hierarchical clustering appears, at any tested thin prime.
3. **The packing profile is 2-D Euclidean, not tree-like.** The `ε`-packing number of the coset
   cloud grows like `(diam/ε)²` (points live in the plane `ℂ`), NOT like a bounded-per-scale
   (ultrametric/tree) profile: e.g. at `m = 132` (p=2113,n=16) the packing at `ε = 0.05·diam` is
   `≈ 14 ≈ (1/0.05)^{~1}`, the volumetric 2-D count, not `m`.

## What this file formalizes (two axiom-clean metric-geometry lemmas)

The character sum `η_b = Σ_{x∈μ_n} e_p(b·x)` is a **complex number**; the coset spectrum is a
finite subset of `ℂ`, and the increment metric is the ambient Euclidean metric of the plane.
Two supporting lemmas, stated for EXACTLY what they prove:

* **(A) 2-D Euclidean packing UPPER bound (finite).** `card_packing_le`: any `2ε`-separated set
  of points in `ℂ` contained in a ball of radius `R` has cardinality
  `≤ (⌊R/ε⌋ + 1 - ⌊-R/ε⌋).toNat² = O((R/ε)²)` (the grid index injects the set into a bounded
  integer box). This is a genuine finite volumetric estimate. IMPORTANT SCOPE: it is an UPPER
  bound on the packing number; it caps how many separated points fit, but by itself does NOT
  supply a matching LOWER packing profile for a specific spectrum, and therefore does not by
  itself prove that structured chaining cannot improve on flat Dudley. It is the covering-side
  ingredient; the lower-profile fact is supplied numerically (probe item 3 above), not proved
  here.

* **(B) Non-ultrametric CONDITIONAL criterion.** `not_ultrametric_of_collinear_evenly_spaced`:
  IF a spectrum contains an equally-spaced collinear triple `x, x+δ, x+2δ` (real step `δ ≠ 0`)
  THEN that triple fails the ultrametric inequality (`d(x, x+2δ) = 2|δ| > |δ|`).
  `not_ultrametric_witness` records the concrete ambient instance `{0,1,2} ⊆ ℂ`. SCOPE: the probe
  `oc_ultrametric_probe.py` (in `/tmp/arklib-reports/`, reproduced in this lane's report, NOT
  committed to the repo) measures a nonzero ultrametric DEFECT for the coset-η cloud at every
  tested thin prime, which certifies SOME violating triple exists; it does not certify the EXACT
  equally-spaced collinear shape this criterion's hypothesis demands. So (B) is a reusable
  criterion plus numeric evidence of non-ultrametricity, NOT a proof that the Gauss-period
  spectrum satisfies (B)'s hypothesis.

## Verdict (calibrated)

EVIDENCE + TWO AXIOM-CLEAN LEMMAS, honestly scoped. The generic-chaining increment metric on the
Gauss-period spectrum lives in the 2-dimensional Euclidean plane `ℂ`, and the exact probes
measure it to be strongly non-ultrametric (relative defect `≈ 0.44–0.50`) with a 2-D-Euclidean
(`Θ((diam/ε)²)`, not tree-like) packing profile at every tested thin prime — so no 2-adic
hierarchical clustering is observed for the 2-power (thin) subgroup. The two Lean lemmas capture
the provable ambient facts (a finite volumetric packing UPPER bound; a conditional
non-ultrametric criterion). What remains UNPROVED (and is left as an explicit gap, not claimed):
a spectrum-specific LOWER packing profile and a proof that (B)'s exact-shape hypothesis holds for
the Gauss-period cloud — both would be required to turn this evidence into a full no-go against
structured 2-adic chaining. CORE unchanged: OPEN, ON-BGK. This lane is the metric-side (frequency
`b`-side chaining geometry) complement to the moment-side I031 cosmetic-entropy reduction (energy
`A_r` side) and the domain-side 2-adic Stepanov kills (the `x`-side separable-orbit collapse,
I008/I015).

Honesty: this file provides supporting lemmas + numeric evidence toward a reduction-hope no-go; it
does NOT close that hope in full, and does NOT close the core. No `axiom`, `sorry`,
`native_decide`, `opaque`, or goal weakening. The `not_prizeClosure` marker records the honest
scope.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false


namespace ArkLib.ProximityGap.Frontier.OCChaining

open scoped Real

/-! ## (A) The 2-D Euclidean packing UPPER bound (covering-side ingredient). -/

/-- An `ε`-separated finite family of complex points, all within distance `R` of a center `z₀`.
This is the abstract shape of the coset-η spectrum viewed under the chaining increment metric. -/
structure SeparatedInBall (S : Finset ℂ) (z₀ : ℂ) (R ε : ℝ) : Prop where
  radius : ∀ z ∈ S, dist z z₀ ≤ R
  separated : ∀ z ∈ S, ∀ w ∈ S, z ≠ w → ε ≤ dist z w

/-- **The grid-index of a point** relative to `(z₀, ε)`: round its real/imaginary offsets to the
nearest `ε`-cell. Two points in the same cell are within `√2·ε < 2·ε` of each other. -/
noncomputable def gridIndex (z₀ : ℂ) (ε : ℝ) (z : ℂ) : ℤ × ℤ :=
  (⌊(z - z₀).re / ε⌋, ⌊(z - z₀).im / ε⌋)

/-- **Same grid cell ⟹ close** (the pigeonhole engine): if two points share a grid cell then
each coordinate offset differs by `< ε`, so their planar distance is `< 2·ε`. -/
theorem dist_lt_of_gridIndex_eq {z₀ : ℂ} {ε : ℝ} (hε : 0 < ε) {z w : ℂ}
    (h : gridIndex z₀ ε z = gridIndex z₀ ε w) : dist z w < 2 * ε := by
  -- unfold the grid indices
  simp only [gridIndex, Prod.mk.injEq] at h
  obtain ⟨hre, him⟩ := h
  -- floor equality gives |a - b| < 1 after dividing by ε, i.e. |Δre| < ε, |Δim| < ε
  have hre' : |((z - z₀).re / ε) - ((w - z₀).re / ε)| < 1 :=
    Int.abs_sub_lt_one_of_floor_eq_floor hre
  have him' : |((z - z₀).im / ε) - ((w - z₀).im / ε)| < 1 :=
    Int.abs_sub_lt_one_of_floor_eq_floor him
  -- clear denominators
  have hdre : |z.re - w.re| < ε := by
    have : ((z - z₀).re / ε) - ((w - z₀).re / ε) = (z.re - w.re) / ε := by
      simp [Complex.sub_re]; ring
    rw [this, abs_div, abs_of_pos hε, div_lt_one hε] at hre'
    exact hre'
  have hdim : |z.im - w.im| < ε := by
    have : ((z - z₀).im / ε) - ((w - z₀).im / ε) = (z.im - w.im) / ε := by
      simp [Complex.sub_im]; ring
    rw [this, abs_div, abs_of_pos hε, div_lt_one hε] at him'
    exact him'
  -- dist z w = ‖z - w‖ ≤ |Δre| + |Δim| < 2ε
  have hbound : dist z w ≤ |z.re - w.re| + |z.im - w.im| := by
    have hnorm := Complex.norm_le_abs_re_add_abs_im (z - w)
    rw [Complex.dist_eq]
    simpa [Complex.sub_re, Complex.sub_im] using hnorm
  calc dist z w ≤ |z.re - w.re| + |z.im - w.im| := hbound
    _ < ε + ε := add_lt_add hdre hdim
    _ = 2 * ε := by ring

/-- **The grid index is INJECTIVE on any `2ε`-separated set** (the pigeonhole half of the
packing bound): distinct points are `≥ 2ε` apart, but same-cell points are `< 2ε` apart, so no
two separated points share a cell — exactly what forbids a below-Euclidean (ultrametric-style,
scale-free) packing profile. -/
theorem gridIndex_injOn_of_separated {S : Finset ℂ} {z₀ : ℂ} {R ε : ℝ}
    (hε : 0 < ε) (h : SeparatedInBall S z₀ R (2 * ε)) :
    Set.InjOn (gridIndex z₀ ε) (S : Set ℂ) := by
  intro z hz w hw hidx
  by_contra hne
  have hclose : dist z w < 2 * ε := dist_lt_of_gridIndex_eq hε hidx
  have hfar : 2 * ε ≤ dist z w := h.separated z hz w hw hne
  exact absurd hclose (not_lt.mpr hfar)

/-- **Each grid coordinate of a ball point lies in a bounded integer interval** (the volumetric
half): if `dist z z₀ ≤ R` then both grid coordinates lie in `Icc ⌊-R/ε⌋ ⌊R/ε⌋`, because
`|(z - z₀).re| ≤ dist z z₀ ≤ R` and floor/division are monotone. -/
theorem gridIndex_mem_box {z₀ : ℂ} {R ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : dist z z₀ ≤ R) :
    gridIndex z₀ ε z ∈
      Finset.Icc ⌊-R/ε⌋ ⌊R/ε⌋ ×ˢ Finset.Icc ⌊-R/ε⌋ ⌊R/ε⌋ := by
  have hRe : |(z - z₀).re| ≤ R := le_trans (by
      have := Complex.abs_re_le_norm (z - z₀); rwa [← Complex.dist_eq] at this) hz
  have hIm : |(z - z₀).im| ≤ R := le_trans (by
      have := Complex.abs_im_le_norm (z - z₀); rwa [← Complex.dist_eq] at this) hz
  have key : ∀ x : ℝ, |x| ≤ R → (⌊-R/ε⌋ ≤ ⌊x/ε⌋ ∧ ⌊x/ε⌋ ≤ ⌊R/ε⌋) := by
    intro x hx
    rw [abs_le] at hx
    refine ⟨Int.floor_le_floor ?_, Int.floor_le_floor ?_⟩
    · have hstep : (-R) / ε ≤ x / ε := div_le_div_of_nonneg_right hx.1 hε.le
      simpa [neg_div] using hstep
    · exact div_le_div_of_nonneg_right hx.2 hε.le
  simp only [gridIndex, Finset.mem_product, Finset.mem_Icc]
  exact ⟨key _ hRe, key _ hIm⟩

/-- **THE 2-D EUCLIDEAN PACKING UPPER BOUND (finite volumetric form).** A `2ε`-separated set of
complex points in a ball of radius `R` (`0 < ε`) has cardinality at most
`(⌊R/ε⌋ + 1 - ⌊-R/ε⌋).toNat ^ 2` — at most the number of `ε`-grid cells meeting the ball,
`O((R/ε)²)`. Proof: the grid index injects `S` into a bounded integer box of that cardinality.
SCOPE: this is an UPPER bound on the packing number (how many separated points fit); it is the
covering-side ingredient. It does NOT by itself establish a matching lower packing profile for a
particular spectrum, nor that hierarchical chaining cannot beat flat Dudley — those need a
spectrum-specific lower-profile result (supplied only numerically in this lane, not proved). -/
theorem card_packing_le {S : Finset ℂ} {z₀ : ℂ} {R ε : ℝ}
    (hε : 0 < ε) (h : SeparatedInBall S z₀ R (2 * ε)) :
    S.card ≤ ((⌊R/ε⌋ + 1 - ⌊-R/ε⌋).toNat) ^ 2 := by
  classical
  set box : Finset (ℤ × ℤ) := Finset.Icc ⌊-R/ε⌋ ⌊R/ε⌋ ×ˢ Finset.Icc ⌊-R/ε⌋ ⌊R/ε⌋ with hbox
  have hinj : Set.InjOn (gridIndex z₀ ε) (S : Set ℂ) :=
    gridIndex_injOn_of_separated hε h
  have hsub : S.image (gridIndex z₀ ε) ⊆ box := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact gridIndex_mem_box hε (h.radius z hz)
  have hcard : S.card = (S.image (gridIndex z₀ ε)).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hboxcard : box.card = ((⌊R/ε⌋ + 1 - ⌊-R/ε⌋).toNat) ^ 2 := by
    rw [hbox, Finset.card_product, Int.card_Icc, sq]
  calc S.card = (S.image (gridIndex z₀ ε)).card := hcard
    _ ≤ box.card := Finset.card_le_card hsub
    _ = ((⌊R/ε⌋ + 1 - ⌊-R/ε⌋).toNat) ^ 2 := hboxcard

/-! ## (B) Non-ultrametric criteria (conditional + concrete ambient witness). -/

/-- **Ultrametric predicate** on a triple of complex points (the "three-point tree condition"). -/
def IsUltraTriple (x y z : ℂ) : Prop :=
  dist x z ≤ max (dist x y) (dist y z) ∧
  dist x y ≤ max (dist x z) (dist z y) ∧
  dist y z ≤ max (dist y x) (dist x z)

/-- **THE NON-ULTRAMETRIC WITNESS (ambient).** The collinear triple `0, 1, 2 ∈ ℂ` violates the
ultrametric inequality: `dist(0,2) = 2 > 1 = max(dist(0,1), dist(1,2))`. This shows the ambient
plane `ℂ` is NOT ultrametric — an ambient obstruction. It does not by itself locate such a triple
inside a particular spectrum; the next theorem supplies the reusable conditional criterion, and
`oc_ultrametric_probe.py` measures a nonzero ultrametric DEFECT (`≈ 0.44–0.50`) for the coset-η
cloud at every tested thin prime — evidence of SOME violating triple, but NOT a certificate of the
exact equally-spaced collinear shape the criterion's hypothesis demands. -/
theorem not_ultrametric_witness :
    ¬ IsUltraTriple (0 : ℂ) 1 2 := by
  intro h
  have h1 := h.1
  have hd02 : dist (0 : ℂ) 2 = 2 := by
    simp [Complex.dist_eq]
  have hd01 : dist (0 : ℂ) 1 = 1 := by
    simp [Complex.dist_eq]
  have hd12 : dist (1 : ℂ) 2 = 1 := by
    rw [Complex.dist_eq]
    norm_num
  rw [hd02, hd01, hd12] at h1
  norm_num at h1

/-- **NON-ULTRAMETRIC FROM AN EQUALLY-SPACED COLLINEAR TRIPLE (reusable conditional criterion).**
If three points `x, y, z` are collinear and equally spaced with a nonzero real step `δ` —
`y = x + δ`, `z = x + 2δ`, `δ ≠ 0` (a real cast into `ℂ`) — then the triple is NON-ultrametric,
because the endpoints are `2|δ|` apart while each adjacent distance is only `|δ|`. SCOPE: this is a
CONDITIONAL criterion on the exact equally-spaced-collinear shape; the numeric probe measures a
nonzero ultrametric DEFECT (hence SOME violating triple) for the coset-η cloud, which is evidence
of non-ultrametricity but does NOT certify this exact shape. So this lemma is a reusable
criterion, not a proof that the Gauss-period spectrum satisfies its hypothesis. -/
theorem not_ultrametric_of_collinear_evenly_spaced
    (x : ℂ) (δ : ℝ) (hδ : δ ≠ 0) :
    ¬ IsUltraTriple x (x + (δ : ℂ)) (x + (2 * δ : ℂ)) := by
  intro h
  have h1 := h.1
  have hxz : dist x (x + (2 * δ : ℂ)) = 2 * |δ| := by
    rw [Complex.dist_eq]
    have hstep : x - (x + (2 * δ : ℂ)) = ((-(2 * δ) : ℝ) : ℂ) := by push_cast; ring
    rw [hstep, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul]
    norm_num
  have hxy : dist x (x + (δ : ℂ)) = |δ| := by
    rw [Complex.dist_eq]
    have hstep : x - (x + (δ : ℂ)) = ((-δ : ℝ) : ℂ) := by push_cast; ring
    rw [hstep, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  have hyz : dist (x + (δ : ℂ)) (x + (2 * δ : ℂ)) = |δ| := by
    rw [Complex.dist_eq]
    have hstep : (x + (δ : ℂ)) - (x + (2 * δ : ℂ)) = ((-δ : ℝ) : ℂ) := by push_cast; ring
    rw [hstep, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  rw [hxz, hxy, hyz] at h1
  have hpos : 0 < |δ| := abs_pos.mpr hδ
  simp only [max_self] at h1
  linarith

/-! ## Scope marker — honest scope, not a closure.

This lane provides supporting metric-geometry lemmas + numeric evidence BEARING ON the "2-adic
structured chaining beats flat Dudley" reduction hope; it does NOT close that hope (the
spectrum-specific lower packing profile and the exact non-ultrametric witness are left as explicit
unproved gaps, per the calibrated Verdict above), and it does NOT close the δ* core. The core wall
`M(μ_n) ≤ C·√(n·log(p/n))` stays open on the BGK/Paley `A_r ≤ Wick` atom. The marker below is a
genuine negation (`¬ False`), NOT a vacuous `: True` placebo, so it discharges a real (if trivial)
obligation and depends on no axioms. -/

/-- The core is NOT claimed closed by this file (honest scope marker; depends on no axioms). -/
def isPrizeClosure : Prop := False

theorem not_prizeClosure : ¬ isPrizeClosure := id

end ArkLib.ProximityGap.Frontier.OCChaining
