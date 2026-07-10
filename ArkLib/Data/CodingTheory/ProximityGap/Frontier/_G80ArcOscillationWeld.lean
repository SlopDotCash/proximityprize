/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G78KMSpreadCircularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# LANE G80 (#466, 2026-07-10): the ARC MODEL for G78 — chord-arc oscillation estimate +
  exact equally-spaced center cancellation, welded into the rank-one arc-increment
  extraction (axiom-clean; pays G78's explicitly owed formalization debt).

## The debt this pays

G78 (`_G78KMSpreadCircularity.lean`) proved the abstract Kelley–Meka increment-extraction
chain up to `exists_cell_deviation_of_approximated_phase_bias`, whose scope note records:
*"the rank-one arc application and its oscillation estimate remain to be formalized"* — the
two concrete inputs `happrox` (how well the K-arc cell model approximates the genuine phase
sum) and `hcancel` (the representative-phase cancellation bound `B`). This lane supplies both:

* **Chord-arc bound** (`norm_expI_sub_expI_le`): `‖e^{ia} − e^{ib}‖ ≤ |a − b|` — the chord is
  at most the arc (via `2|sin(x/2)| ≤ |x|`, packaged in Mathlib's
  `Real.norm_exp_I_mul_ofReal_sub_one_le`).
* **Single-arc oscillation estimate** (`phase_sum_arc_approx`): points whose phases lie
  within `wid` of an arc center `γ` satisfy
  `‖∑ e^{iθ(x)} − #T·e^{iγ}‖ ≤ #T · wid`.
* **Grouped approximation** (`grouped_phase_sum_approx`): for any assignment of the point set
  into cells with per-cell centers, the total model error is `≤ #pts · wid` — this is
  EXACTLY G78's `happrox` with `D = #pts · wid`.
* **Exact center cancellation** (`sum_equally_spaced_centers_eq_zero`): the `K ≥ 2` equally
  spaced arc centers `γ_j = 2πj/K` sum to ZERO (they are the K-th roots of unity), so G78's
  `hcancel` holds with `B = 0` — the reference-mass term drops out entirely.
* **Capstone weld** (`exists_arc_deviation_equally_spaced`): if the genuine phase sum has
  norm `≥ A` and every point's phase is within `wid` of its arc's center, then some arc's
  point count deviates from ANY reference mass `m` by at least `(A − #pts·wid)/K`.

With the equally-spaced-arc instantiation `wid = 2π/K` this is the rank-one arc-density
increment: `‖η‖ ≥ A` forces an arc whose occupancy deviates from uniform by
`≥ (A − 2π·#pts/K)/K` — the quantitative statement G78's probe measured two-sidedly
(dev/(M/n) ∈ [3.1, 6.9]).

## Honest scope

Completes the arc MODEL abstractly (arbitrary phase functions θ and arc assignments κ). The
remaining gap to the arithmetic cell is pure plumbing: instantiating `θ x = 2π·val(bx)/p` on
`x ∈ μ_n`, `κ = arc index ⌊K·val(bx)/p⌋`, for which the width hypothesis holds with
`wid = 2π/K` by construction. No claim that this closes the KM spreadness circularity (G78's
verdict stands: the loop has no contraction; the non-circular input remains the
BGK/Cilleruelo–Garaev anti-concentration frontier). CORE remains OPEN / ON-BGK.

Issue #466. Axiom-clean.
-/

open Finset Complex

namespace ArkLib.ProximityGap.Frontier.G80ArcOscillationWeld

open ArkLib.ProximityGap.Frontier.G78KMSpreadCircularity

/-- **Chord-arc bound**: the chord between two points of the unit circle is at most the
arc length, `‖e^{ia} − e^{ib}‖ ≤ |a − b|`. -/
theorem norm_expI_sub_expI_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  have hfact : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)
      = Complex.exp ((b : ℂ) * Complex.I) *
          (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfact, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  calc ‖Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1‖ ≤ ‖a - b‖ :=
        Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |a - b| := Real.norm_eq_abs _

/-- **Single-arc oscillation estimate**: if every point's phase lies within `wid` of the arc
center `γ`, the arc's phase sum is within `#T · wid` of the centered model `#T · e^{iγ}`. -/
theorem phase_sum_arc_approx {α : Type*} (T : Finset α) (θ : α → ℝ) (γ wid : ℝ)
    (hosc : ∀ x ∈ T, |θ x - γ| ≤ wid) :
    ‖(∑ x ∈ T, Complex.exp ((θ x : ℂ) * Complex.I)) -
        (T.card : ℂ) * Complex.exp ((γ : ℂ) * Complex.I)‖ ≤ (T.card : ℝ) * wid := by
  have hconst : (T.card : ℂ) * Complex.exp ((γ : ℂ) * Complex.I)
      = ∑ _x ∈ T, Complex.exp ((γ : ℂ) * Complex.I) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hconst, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x ∈ T, ‖Complex.exp ((θ x : ℂ) * Complex.I) -
          Complex.exp ((γ : ℂ) * Complex.I)‖
      ≤ ∑ x ∈ T, wid := by
        refine Finset.sum_le_sum fun x hx => ?_
        exact (norm_expI_sub_expI_le (θ x) γ).trans (hosc x hx)
    _ = (T.card : ℝ) * wid := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Grouped (fiberwise) approximation** — G78's `happrox` input: assigning the point set to
cells with per-cell centers, the K-cell model `∑_j n_j e^{iγ_j}` approximates the genuine
phase sum within `#pts · wid`. -/
theorem grouped_phase_sum_approx {α S : Type*} [DecidableEq S]
    (pts : Finset α) (cells : Finset S) (κ : α → S) (hκ : ∀ x ∈ pts, κ x ∈ cells)
    (θ : α → ℝ) (γ : S → ℝ) (wid : ℝ)
    (hosc : ∀ x ∈ pts, |θ x - γ (κ x)| ≤ wid) :
    ‖(∑ x ∈ pts, Complex.exp ((θ x : ℂ) * Complex.I)) -
        ∑ j ∈ cells, ((pts.filter (fun x => κ x = j)).card : ℂ) *
          Complex.exp ((γ j : ℂ) * Complex.I)‖ ≤ (pts.card : ℝ) * wid := by
  rw [← Finset.sum_fiberwise_of_maps_to hκ (fun x => Complex.exp ((θ x : ℂ) * Complex.I)),
    ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hcell : ∀ j ∈ cells,
      ‖(∑ x ∈ pts.filter (fun x => κ x = j), Complex.exp ((θ x : ℂ) * Complex.I)) -
          ((pts.filter (fun x => κ x = j)).card : ℂ) *
            Complex.exp ((γ j : ℂ) * Complex.I)‖
        ≤ ((pts.filter (fun x => κ x = j)).card : ℝ) * wid := by
    intro j _
    refine phase_sum_arc_approx _ θ (γ j) wid ?_
    intro x hx
    obtain ⟨hxp, hxj⟩ := Finset.mem_filter.mp hx
    have := hosc x hxp
    rwa [hxj] at this
  calc ∑ j ∈ cells, ‖(∑ x ∈ pts.filter (fun x => κ x = j),
          Complex.exp ((θ x : ℂ) * Complex.I)) -
          ((pts.filter (fun x => κ x = j)).card : ℂ) *
            Complex.exp ((γ j : ℂ) * Complex.I)‖
      ≤ ∑ j ∈ cells, ((pts.filter (fun x => κ x = j)).card : ℝ) * wid :=
        Finset.sum_le_sum hcell
    _ = (∑ j ∈ cells, ((pts.filter (fun x => κ x = j)).card : ℝ)) * wid := by
        rw [Finset.sum_mul]
    _ = (pts.card : ℝ) * wid := by
        rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise hκ]

/-- **Exact cancellation of equally spaced centers**: for `K ≥ 2` the arc centers
`γ_j = 2πj/K` are the K-th roots of unity and sum to ZERO — G78's `hcancel` holds with
`B = 0`. -/
theorem sum_equally_spaced_centers_eq_zero {K : ℕ} (hK : 2 ≤ K) :
    ∑ j ∈ Finset.range K,
      Complex.exp (((2 * Real.pi * j / K : ℝ) : ℂ) * Complex.I) = 0 := by
  have hK0 : K ≠ 0 := by omega
  have hprim := Complex.isPrimitiveRoot_exp K hK0
  have hterm : ∀ j ∈ Finset.range K,
      Complex.exp (((2 * Real.pi * j / K : ℝ) : ℂ) * Complex.I)
        = Complex.exp (2 * Real.pi * Complex.I / K) ^ j := by
    intro j _
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm]
  exact hprim.geom_sum_eq_zero (by omega)

/-- **Capstone weld — the rank-one arc-increment extraction.** If the genuine phase sum has
norm `≥ A`, points are assigned to `K ≥ 2` equally spaced arcs with each phase within `wid`
of its arc center, then some arc's occupancy deviates from ANY reference mass `m` by at least
`(A − #pts·wid)/K`. G78's `exists_cell_deviation_of_approximated_phase_bias` fires with
`D = #pts·wid` (grouped oscillation estimate) and `B = 0` (exact center cancellation). -/
theorem exists_arc_deviation_equally_spaced {α : Type*}
    (pts : Finset α) {K : ℕ} (hK : 2 ≤ K) (κ : α → ℕ)
    (hκ : ∀ x ∈ pts, κ x ∈ Finset.range K)
    (θ : α → ℝ) (wid A m : ℝ) (hm : 0 ≤ m)
    (hosc : ∀ x ∈ pts, |θ x - 2 * Real.pi * (κ x) / K| ≤ wid)
    (hbias : A ≤ ‖∑ x ∈ pts, Complex.exp ((θ x : ℂ) * Complex.I)‖) :
    ∃ j ∈ Finset.range K,
      (A - (pts.card : ℝ) * wid) / (K : ℝ) ≤
        |((pts.filter (fun x => κ x = j)).card : ℝ) - m| := by
  have hs : (Finset.range K).Nonempty := by
    rw [Finset.nonempty_range_iff]
    omega
  have happrox := grouped_phase_sum_approx pts (Finset.range K) κ hκ θ
    (fun j => 2 * Real.pi * j / K) wid hosc
  have hcancel : ‖∑ j ∈ Finset.range K,
      Complex.exp (((2 * Real.pi * j / K : ℝ) : ℂ) * Complex.I)‖ ≤ (0 : ℝ) := by
    rw [sum_equally_spaced_centers_eq_zero hK, norm_zero]
  have hc : ∀ j ∈ Finset.range K,
      ‖Complex.exp (((2 * Real.pi * j / K : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
    intro j _
    rw [Complex.norm_exp_ofReal_mul_I]
  obtain ⟨j, hj, hdev⟩ := exists_cell_deviation_of_approximated_phase_bias
    (Finset.range K) hs
    (fun j => ((pts.filter (fun x => κ x = j)).card : ℝ))
    (fun j => Complex.exp (((2 * Real.pi * j / K : ℝ) : ℂ) * Complex.I))
    (∑ x ∈ pts, Complex.exp ((θ x : ℂ) * Complex.I))
    m A (0 : ℝ) ((pts.card : ℝ) * wid) hm hc hbias happrox hcancel
  refine ⟨j, hj, ?_⟩
  simpa [Finset.card_range, mul_zero, sub_zero] using hdev

end ArkLib.ProximityGap.Frontier.G80ArcOscillationWeld

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80ArcOscillationWeld.norm_expI_sub_expI_le
#print axioms
  ArkLib.ProximityGap.Frontier.G80ArcOscillationWeld.phase_sum_arc_approx
#print axioms
  ArkLib.ProximityGap.Frontier.G80ArcOscillationWeld.grouped_phase_sum_approx
#print axioms
  ArkLib.ProximityGap.Frontier.G80ArcOscillationWeld.sum_equally_spaced_centers_eq_zero
#print axioms
  ArkLib.ProximityGap.Frontier.G80ArcOscillationWeld.exists_arc_deviation_equally_spaced
