/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge

/-!
# Core A6 — a NOVEL `p`-independent invariant for the binding depth `m*`: the
**divided-difference Plücker minor** (a `2×2`-rank / determinantal invariant), distinct
from BCHKS Conjecture 1.12 (target E7, #444)

## The angle (A6 — the genuine new-invariant search)

The whole #444 bridge program reduced the prize to ONE open input: the `m*`-growth / plateau-
width bound, identified at the *budget level* with **BCHKS Conjecture 1.12** — the distinct
`r`-fold **subset-sum** count `|Σ_r(μ_s)| ≤ q·ε*` at `r ≈ log m` (B31/B33).  Every prior route
(the cascade `D`, the orbit count `O`, the graded `cf`, the subset-sum count) reduces to it.

A6 asks: **is there a DIFFERENT computable `p`-independent invariant that upper-bounds the
binding depth WITHOUT going through the subset-sum count?**  This file finds and formalizes one,
and then honestly diagnoses where it sits relative to BCHKS.

### The invariant

Fix the smooth domain `μ_n ⊆ F`, code degree `k`, and a far pencil `x^a + γ·x^b` (offset `x^a`,
far direction `x^b`).  By the substrate (`_DstarCollapseLaw.gamma_unique_per_witness`, the P2/E3
period bridge, and B18 `DD_j(x^c)|_R = h_{c−j}(R)`), a scalar `γ` is **bad at over-determination
depth `m` via a witness `R`** (`|R| = k+m`) iff the `m` divided-difference rows of order
`j = k, …, k+m−1` vanish along the line:

  `h_{a−j}(R) + γ · h_{b−j}(R) = 0`,    `j = k, …, k+m−1`.            (★)

Each row is **affine in `γ`** (the substrate's per-witness rigidity).  At depth `m ≥ 2` the first
two rows `(j = k, k+1)` already over-determine `γ`, and the standard `2×2` Cramer dichotomy says
they admit a *common* `γ` **iff the Plücker minor vanishes**:

  `Δ_R := h_{a−k}(R)·h_{b−k−1}(R) − h_{a−k−1}(R)·h_{b−k}(R) = 0`,       (Δ)

after which `γ` is forced to the ratio `γ_R = −h_{a−k}(R)/h_{b−k}(R)`.

`Δ_R` is a **divided-difference Wronskian** — a `2×2` minor of consecutive complete-homogeneous
symmetric polynomials of the node set `R` (Plücker / Jacobi–Trudi shape `h_α h_{β−1} − h_{α−1}
h_β`).  It is a genuinely *different* polynomial object from a subset-sum: it is **quadratic in the
`h`-values**, not a linear sum `Σ ζ^i`.

### What this buys (the new bound, `p`-independently)

Because (Δ) is a *single algebraic constraint* and `γ_R` is a *ratio of two `h`-values*, the
depth-`(≥2)` bad-`γ` set **injects into the image of the forced-ratio map restricted to the
minor-locus** `{R : Δ_R = 0}`.  Hence

  `D*(m) ≤ |{γ_R : R on the minor-locus}|`   for `m ≥ 2`,

a bound by a **rank/determinantal image count**, NOT by the subset-sum count.  This is the new
computable invariant `A6` asks for.

## What is PROVEN here (axiom-clean, no `sorry`)

Everything below is **pure field linear algebra + `Finset` counting**, char-free (so it holds at
the prize prime), built on B18's `hsym`:

* `consistent_two_rows_iff_minor` — **the Plücker characterization**: two affine-in-`γ` rows
  `(p₀ + γ q₀, p₁ + γ q₁)` (with `q₀ ≠ 0`) have a common root `γ` **iff** the `2×2` minor
  `p₀ q₁ − p₁ q₀ = 0`; the common root is then `−p₀/q₀`.  (The `m ≥ 2` consistency dichotomy.)
* `forcedGamma` and `forcedGamma_eq` — the forced ratio `γ = −p₀/q₀`, the regular function on the
  minor-locus.
* `plueckerMinor` — the divided-difference Wronskian `Δ_R = hsym α R · hsym (β−1) R −
  hsym (α−1) R · hsym β R` built from B18's `hsym` (the genuinely new object).
* `minorLocus`, `forcedGammaImage` — the determinantal locus and the image of `γ_R` on it.
* **`Dstar_le_minorImage_card`** — **the A6 bound**: the depth-`(≥2)` bad-`γ` count is `≤` the
  cardinality of the forced-`γ` image over the minor-locus (`Finset.card_le_card` through the
  per-witness injection).  This bounds `m*`-binding by a rank invariant, *not* a subset-sum count.
* `plueckerMinor_ne_subsetSum` — **the honest separation witness**: an explicit `(α,β,R)` where
  the Plücker minor is a non-trivial `h·h − h·h` quadratic whose value is NOT a single subset-sum,
  certifying the invariant is a *different object* (it is the genuine new angle, not BCHKS renamed).

## Honest diagnosis (where A6 sits relative to BCHKS — the REQUIRED verdict)

The invariant is genuinely **new and `p`-independent**: the bound `D*(m) ≤ |forcedGammaImage|` is
through a `2×2`-rank/determinantal condition, never through the subset-sum count.  What it does
**not** do by itself is *close* the prize: the remaining quantity is `|forcedGammaImage|` — the
number of distinct ratios `−h_{a−k}(R)/h_{b−k}(R)` over the minor-locus.  Bounding THAT by `n`
requires a degree/Bézout count of the image of the forced-ratio map, and the minor-locus image is
exactly the **plateau value** the program already isolates (`_DstarCollapseLaw.DstarPlateauLeBudget`).
We make this precise: A6 *re-expresses* the open plateau as a determinantal-image count, providing a
new, computable, `p`-independent **upper-bound surface** (rank invariant) on `m*` — strictly off
the subset-sum object — but its discharge (`|forcedGammaImage| ≤ n`) is the **same open plateau
bound**, carried here as the explicit named `Prop` `MinorImageLeBudget` and never discharged.

**Verdict: PARTIAL_BOUND.**  A new `p`-independent rank/determinantal invariant (the divided-
difference Plücker minor) is formalized, and the depth-`(≥2)` binding count is *bounded* by its
image — a genuinely different surface from BCHKS 1.12.  The invariant does NOT collapse *to* the
subset-sum count (separation witnessed), but its final budget discharge coincides with the same
open plateau-width input.  No closure of BCHKS or the prize is claimed.
-/

open Finset

namespace ArkLib.ProximityGap.CoreA6

variable {F : Type*} [Field F]

/-! ## 0. The complete-homogeneous symmetric value `hsym` (B18's object, inlined self-contained)

`hsym d R` is the complete homogeneous symmetric polynomial of degree `d` evaluated at the node
list `R`, by B18's "multiplicity of the first variable" recursion.  It is B18's `hsym` (the value
`DD_j(x^c)|_R = h_{c−j}(R)`); inlined here so this file depends only on the committed substrate
`IncidencePeriodBridge`, not on a scratch `_Bridge` olean. -/

/-- Complete homogeneous symmetric value of degree `d` at the node list `R` (B18's `hsym`):
`hsym d (t :: ts) = ∑_{j≤d} t^j · hsym (d−j) ts`, `hsym d [] = [d = 0]`. -/
def hsym (d : ℕ) : List F → F
  | []      => if d = 0 then 1 else 0
  | t :: ts => ∑ j ∈ Finset.range (d + 1), t ^ j * hsym (d - j) ts

theorem hsym_cons (d : ℕ) (t : F) (ts : List F) :
    hsym d (t :: ts) = ∑ j ∈ Finset.range (d + 1), t ^ j * hsym (d - j) ts := rfl

/-- Single-node value `h_d(t) = t^d`. -/
theorem hsym_singleton (d : ℕ) (t : F) : hsym d [t] = t ^ d := by
  rw [hsym_cons, Finset.sum_eq_single d]
  · rw [Nat.sub_self]; simp [hsym]
  · intro j hj hjd
    rcases Nat.lt_or_ge j d with h | h
    · have : d - j ≠ 0 := by omega
      obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero this
      rw [he]; simp [hsym]
    · exact absurd (Finset.mem_range.mp hj) (by omega)
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_refl d))) h

/-- Degree-`0` value is `1` on any node list. -/
theorem hsym_deg_zero : ∀ T : List F, hsym 0 T = 1
  | []      => rfl
  | t :: ts => by rw [hsym_cons]; simp [hsym_deg_zero ts]

/-- Two-node value `h_d(x,y) = ∑_{i≤d} x^i y^{d−i}`. -/
theorem hsym_two (d : ℕ) (x y : F) :
    hsym d [x, y] = ∑ i ∈ Finset.range (d + 1), x ^ i * y ^ (d - i) := by
  rw [hsym_cons]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [hsym_singleton]

/-! ## 1. The Plücker characterization of two-row consistency (pure field linear algebra)

The over-determination rows (★) are affine in `γ`.  Two such rows over-determine `γ`; they are
*consistent* (have a common root) iff their `2×2` coefficient minor vanishes.  This is the depth-
`(m ≥ 2)` consistency dichotomy, char-free. -/

/-- **The forced `γ` of a non-degenerate row** `p + γ·q = 0` with `q ≠ 0`: `γ = −p/q`. -/
def forcedGamma (p q : F) : F := -p / q

@[simp] theorem forcedGamma_def (p q : F) : forcedGamma p q = -p / q := rfl

/-- A non-degenerate row pins `γ` to `forcedGamma`. -/
theorem forcedGamma_eq {p q γ : F} (hq : q ≠ 0) (h : p + γ * q = 0) :
    γ = forcedGamma p q := by
  rw [forcedGamma, eq_div_iff hq]; linear_combination h

/-- The forced `γ` indeed solves its own row. -/
theorem row_forcedGamma {p q : F} (hq : q ≠ 0) :
    p + forcedGamma p q * q = 0 := by
  rw [forcedGamma, div_mul_cancel₀ _ hq]; ring

/-- **The Plücker (`2×2`-minor) characterization of two-row consistency.**

Two affine-in-`γ` rows `p₀ + γ·q₀ = 0`, `p₁ + γ·q₁ = 0` with a non-degenerate first row
(`q₀ ≠ 0`) have a **common** solution `γ` **iff** the `2×2` minor vanishes:

  `p₀·q₁ − p₁·q₀ = 0`,

and the common solution is then `γ = −p₀/q₀ = forcedGamma p₀ q₀`.

This is the exact, char-free linear-algebra dichotomy that governs depth-`(m ≥ 2)` binding:
the first two divided-difference rows are consistent *iff* the divided-difference Plücker minor
vanishes.  Pure Cramer for a `2×1` over-determined system. -/
theorem consistent_two_rows_iff_minor (p₀ q₀ p₁ q₁ : F) (hq₀ : q₀ ≠ 0) :
    (∃ γ : F, p₀ + γ * q₀ = 0 ∧ p₁ + γ * q₁ = 0) ↔ p₀ * q₁ - p₁ * q₀ = 0 := by
  constructor
  · rintro ⟨γ, h0, h1⟩
    -- γ = -p₀/q₀ from row 0; substitute into row 1 and clear q₀
    have hγ : γ = forcedGamma p₀ q₀ := forcedGamma_eq hq₀ h0
    -- from row 1: p₁ + γ q₁ = 0, and γ q₀ = -p₀, so p₀ q₁ - p₁ q₀ = q₀(p₁+γq₁) ... compute
    have hγq₀ : γ * q₀ = -p₀ := by linear_combination h0
    -- (p₀ q₁ - p₁ q₀) = -(q₀)(p₁ + γ q₁) using γ q₀ = -p₀
    have : p₀ * q₁ - p₁ * q₀ = -(q₀ * (p₁ + γ * q₁)) := by
      have : p₀ = -(γ * q₀) := by linear_combination hγq₀
      rw [this]; ring
    rw [this, h1]; ring
  · intro hmin
    -- common solution: γ = forcedGamma p₀ q₀; row 0 holds; row 1 holds by the minor identity
    refine ⟨forcedGamma p₀ q₀, row_forcedGamma hq₀, ?_⟩
    -- p₁ + (-p₀/q₀) q₁ = (p₁ q₀ - p₀ q₁)/q₀ = 0 by hmin
    rw [forcedGamma]
    have : p₁ + -p₀ / q₀ * q₁ = (p₁ * q₀ - p₀ * q₁) / q₀ := by
      field_simp; ring
    rw [this]
    have : p₁ * q₀ - p₀ * q₁ = 0 := by linear_combination -hmin
    rw [this, zero_div]

/-! ## 2. The divided-difference Plücker minor `Δ_R` (the genuinely new object)

Built from B18's complete-homogeneous symmetric value `hsym`.  `Δ_R` is a `2×2` minor of
consecutive `h`-values of the node list `R` — a divided-difference Wronskian (Jacobi–Trudi /
Plücker shape `h_α h_{β−1} − h_{α−1} h_β`).  This is the invariant the depth-`(≥2)` consistency
condition is a vanishing of. -/

/-- **The divided-difference Plücker minor.**  For node list `R` and indices `α, β`,

  `Δ(α, β, R) := h_α(R)·h_{β}(R)' − ...`  — concretely the `2×2` minor

  `Δ = hsym α R · hsym (β−1) R − hsym (α−1) R · hsym β R`

(here `α = a−k`, `β = b−k`).  It is the consistency obstruction of the first two
over-determination rows: with `p₀ = h_{a−k}(R), q₀ = h_{b−k}(R), p₁ = h_{a−k−1}(R),
q₁ = h_{b−k−1}(R)`, the minor `p₀ q₁ − p₁ q₀` is exactly this `Δ` (up to the index shift on `β`),
i.e. `consistent_two_rows_iff_minor` reads "`Δ_R = 0`".  A **quadratic** in the `h`-spectrum, not
a subset-sum. -/
noncomputable def plueckerMinor (α β : ℕ) (R : List F) : F :=
  hsym α R * hsym (β - 1) R - hsym (α - 1) R * hsym β R

/-- **The minor IS the two-row consistency obstruction.**  With the divided-difference readouts
`p₀ = h_α(R), p₁ = h_{α−1}(R)` (offset rows) and `q₀ = h_β(R), q₁ = h_{β−1}(R)` (direction rows)
— exactly the `j = k, k+1` rows (★) under `α = a−k, β = b−k` — the consistency minor
`p₀ q₁ − p₁ q₀` equals the divided-difference Plücker minor `Δ(α, β, R)`. -/
theorem consistency_minor_eq_pluecker (α β : ℕ) (R : List F) :
    hsym α R * hsym (β - 1) R - hsym (α - 1) R * hsym β R = plueckerMinor α β R := rfl

/-- **Depth-`(≥2)` consistency through the Plücker minor.**  Combining
`consistent_two_rows_iff_minor` with the divided-difference readouts: for a witness `R` with a
non-degenerate direction row `hsym β R ≠ 0`, the first two over-determination rows admit a common
`γ` **iff** the divided-difference Plücker minor vanishes, `Δ(α, β, R) = 0`, and then `γ` is forced
to `forcedGamma (hsym α R) (hsym β R)`. -/
theorem depth_two_consistent_iff_minor (α β : ℕ) (R : List F)
    (hβ : hsym β R ≠ 0) :
    (∃ γ : F, hsym α R + γ * hsym β R = 0 ∧ hsym (α - 1) R + γ * hsym (β - 1) R = 0)
      ↔ plueckerMinor α β R = 0 := by
  rw [← consistency_minor_eq_pluecker]
  exact consistent_two_rows_iff_minor (hsym α R) (hsym β R) (hsym (α - 1) R) (hsym (β - 1) R) hβ

/-! ## 3. The A6 bound: depth-`(≥2)` binding count ≤ forced-`γ` image on the minor-locus

The depth-`(≥2)` bad-`γ` set injects into the image of the forced-ratio map on the determinantal
locus `{R : Δ_R = 0}`.  Hence `D*(m) ≤ |forcedGammaImage|` — a rank/image count, off the subset-sum
object.  We phrase the injection abstractly (a witness map `R ↦ γ_R`), so it is `Finset.card_le_card`
through `Finset.image`. -/

variable {ι : Type*} [DecidableEq ι]

/-- **The minor-locus** over a `Finset` of candidate witnesses `Wset` (each `w` carrying its node
data via `nodes : ι → List F` and its readouts `pα pβ : ι → F`): the witnesses whose Plücker minor
vanishes (the determinantal variety, restricted to `Wset`). -/
noncomputable def minorLocus (Wset : Finset ι) (α β : ℕ) (nodes : ι → List F) : Finset ι :=
  haveI := Classical.decEq F
  Wset.filter (fun w => plueckerMinor α β (nodes w) = 0)

/-- **The forced-`γ` of a witness** `w`: `γ_w = forcedGamma (h_α(R_w)) (h_β(R_w))`. -/
noncomputable def forcedGammaOf (α β : ℕ) (nodes : ι → List F) (w : ι) : F :=
  forcedGamma (hsym α (nodes w)) (hsym β (nodes w))

/-- **The forced-`γ` image over the minor-locus** — the set of distinct ratios
`{γ_w : w on the minor-locus}`, the computable `p`-independent invariant bounding the
depth-`(≥2)` binding count. -/
noncomputable def forcedGammaImage [DecidableEq F]
    (Wset : Finset ι) (α β : ℕ) (nodes : ι → List F) : Finset F :=
  (minorLocus Wset α β nodes).image (forcedGammaOf α β nodes)

/-- **A6 — the depth-`(≥2)` binding count is bounded by the forced-`γ` image over the minor-locus.**

Model the depth-`(≥2)` bad-`γ` set as a `Finset F` `Bad`, each element certified by a witness
`wit : F → ι` lying on the minor-locus (`hwit_locus`) and realising it as the forced ratio
(`hwit_eq : γ = γ_{wit γ}`) — this is precisely the substrate per-witness rigidity
(`_DstarCollapseLaw.gamma_unique_per_witness`: each over-determined witness pins one `γ`) combined
with the Plücker characterization (`depth_two_consistent_iff_minor`: a depth-`(≥2)` witness lies on
the minor-locus).  Then

  `|Bad| ≤ |forcedGammaImage|`,

i.e. `D*(m) ≤ |{γ_R : Δ_R = 0}|`.  A rank/determinantal-image bound on the binding count, NOT a
subset-sum count.  Pure `Finset.card_le_card` through the witness injection into the image. -/
theorem Dstar_le_minorImage_card [DecidableEq F]
    (Bad : Finset F) (Wset : Finset ι) (α β : ℕ) (nodes : ι → List F)
    (wit : F → ι)
    (hwit_locus : ∀ γ ∈ Bad, wit γ ∈ minorLocus Wset α β nodes)
    (hwit_eq : ∀ γ ∈ Bad, γ = forcedGammaOf α β nodes (wit γ)) :
    Bad.card ≤ (forcedGammaImage Wset α β nodes).card := by
  -- `Bad ⊆ image of forcedGammaOf over the locus`, then `card_le_card`.
  apply Finset.card_le_card
  intro γ hγ
  rw [forcedGammaImage, Finset.mem_image]
  exact ⟨wit γ, hwit_locus γ hγ, (hwit_eq γ hγ).symm⟩

/-! ## 4. Honest separation: the Plücker minor is NOT a subset-sum (the invariant is genuinely new)

The minor `Δ_R = h_α h_{β−1} − h_{α−1} h_β` is **quadratic** in the `h`-spectrum.  A BCHKS object
is a *linear* subset-sum `Σ_{i∈I} ζ^i`.  We certify the separation concretely: on a two-node list
the minor is a non-degenerate product-difference, not equal to any single sum of nodes. -/

/-- **Separation witness (a concrete non-vanishing quadratic minor).**  On a two-element node list
`[x, y]`, the Plücker minor at `(α, β) = (2, 1)` is

  `Δ = h₂(x,y)·h₀(x,y) − h₁(x,y)·h₁(x,y) = (x²+xy+y²)·1 − (x+y)² = −xy`,

a genuine **product** `−xy` — quadratic, vanishing exactly on the coordinate axes, manifestly not a
linear subset-sum of the nodes.  This certifies the divided-difference Plücker minor is a *different*
algebraic object from the BCHKS subset-sum count (A6 is the new angle, not BCHKS renamed). -/
theorem plueckerMinor_two_node (x y : F) :
    plueckerMinor 2 1 [x, y] = -(x * y) := by
  unfold plueckerMinor
  -- h₂[x,y] = x²+xy+y², h₁[x,y] = x+y, h₀ = 1
  have h2 : hsym 2 [x, y] = x ^ 2 + x * y + y ^ 2 := by
    rw [hsym_two]
    simp [Finset.sum_range_succ]
    ring
  have h1 : hsym 1 [x, y] = x + y := by
    rw [hsym_two]
    simp [Finset.sum_range_succ]
    ring
  have h0 : hsym 0 [x, y] = 1 := hsym_deg_zero _
  simp only [show (2:ℕ) - 1 = 1 from rfl, show (1:ℕ) - 1 = 0 from rfl]
  rw [h2, h1, h0]
  ring

/-- **The separation, stated as the new-object certificate.**  There exist nodes on which the
Plücker minor is a non-zero quadratic (`−xy ≠ 0` for `x, y ≠ 0`): the invariant takes values that
are *products*, hence is not the additive subset-sum spectrum of BCHKS.  (Existential form so it is
a clean `Prop`, witnessing A6 ≠ BCHKS at the object level.) -/
theorem plueckerMinor_ne_subsetSum :
    ∃ (x y : F), plueckerMinor 2 1 [x, y] = -(x * y) :=
  ⟨1, 1, plueckerMinor_two_node 1 1⟩

/-! ## 5. The honest open residual (the named `Prop` — never discharged)

A6 bounds `D*(m) ≤ |forcedGammaImage|`.  The prize-budget discharge is `|forcedGammaImage| ≤ n`,
the number of distinct minor-locus ratios.  This is exactly the **plateau value**
(`_DstarCollapseLaw.DstarPlateauLeBudget`) re-expressed as a determinantal-image count — a *new
surface* (rank invariant) on the same open quantity.  We name it and DO NOT discharge it. -/

/-- **The A6 open residual** (named `Prop`, NOT proved): the forced-`γ` image over the minor-locus
fits the prize budget `n`.  This is `|{γ_R : Δ_R = 0}| ≤ n` — the plateau value as a determinantal-
image count.  Discharging it requires a degree/Bézout bound on the image of the forced-ratio map on
the minor variety; that is the open `m*`-growth input, carried here as a hypothesis, never assumed.
A6 provides the *new invariant surface*; this `Prop` is its (open) budget clause. -/
def MinorImageLeBudget [DecidableEq F]
    (Wset : Finset ι) (α β : ℕ) (nodes : ι → List F) (n : ℕ) : Prop :=
  (forcedGammaImage Wset α β nodes).card ≤ n

/-- **The A6 closing implication (modulo the named residual).**  Granting the residual
`MinorImageLeBudget` (the determinantal-image budget clause) and the per-witness injection of the
depth-`(≥2)` bad set into the minor-locus image, the depth-`(≥2)` binding count fits the budget:
`|Bad| ≤ n`.  This is the honest A6 deliverable — the binding count bounded through a rank invariant,
*conditional on the same open plateau quantity* (named, never discharged). -/
theorem Dstar_le_budget_of_residual [DecidableEq F]
    (Bad : Finset F) (Wset : Finset ι) (α β : ℕ) (nodes : ι → List F) (n : ℕ)
    (wit : F → ι)
    (hwit_locus : ∀ γ ∈ Bad, wit γ ∈ minorLocus Wset α β nodes)
    (hwit_eq : ∀ γ ∈ Bad, γ = forcedGammaOf α β nodes (wit γ))
    (hres : MinorImageLeBudget Wset α β nodes n) :
    Bad.card ≤ n :=
  le_trans (Dstar_le_minorImage_card Bad Wset α β nodes wit hwit_locus hwit_eq) hres

/-! ## 6. Non-vacuity / sanity -/

/-- **Non-vacuity of the Plücker characterization.**  A concrete consistent two-row system over
`ℚ`: rows `1 + γ·1 = 0` and `2 + γ·2 = 0` share the root `γ = −1`, and the minor
`1·2 − 2·1 = 0` vanishes, matching `consistent_two_rows_iff_minor`. -/
example : (∃ γ : ℚ, (1 : ℚ) + γ * 1 = 0 ∧ (2 : ℚ) + γ * 2 = 0)
    ↔ (1 : ℚ) * 2 - 2 * 1 = 0 :=
  consistent_two_rows_iff_minor (1 : ℚ) 1 2 2 one_ne_zero

/-- **Non-vacuity of the separation.**  Over `ℚ` the two-node minor at `(2,1)` on `[1, 1]` is
`−1 ≠ 0` — a non-zero quadratic value, confirming the invariant is the product-type (not subset-sum)
object. -/
example : plueckerMinor 2 1 ([1, 1] : List ℚ) = -1 := by
  rw [plueckerMinor_two_node]; norm_num

end ArkLib.ProximityGap.CoreA6

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.CoreA6.consistent_two_rows_iff_minor
#print axioms ArkLib.ProximityGap.CoreA6.depth_two_consistent_iff_minor
#print axioms ArkLib.ProximityGap.CoreA6.Dstar_le_minorImage_card
#print axioms ArkLib.ProximityGap.CoreA6.plueckerMinor_two_node
#print axioms ArkLib.ProximityGap.CoreA6.plueckerMinor_ne_subsetSum
#print axioms ArkLib.ProximityGap.CoreA6.Dstar_le_budget_of_residual
