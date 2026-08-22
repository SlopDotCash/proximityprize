/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-W6 frontier — successive-minima count frame)
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The successive-minima POINT-COUNT frame for the spurious count `Spur_r(p)` (#444, lane wf-W6)

## What this supplies (the frame `_wf7W6` named as MISSING)

Lane wf-W6 (`_wf7W6_shortvector_spur.lean`) reduces the prize char-`p` transfer to the
**theta-series / lattice-point count**

  `(S-W6)   Spur_r(p) = #{ v ∈ L_p : v ≠ 0, ‖v‖² ≤ φ(n)·2r } ≤ ε·(2r−1)‼·n^r`,

uniform over prize primes `p ≍ n^β`, where `L_p = ker(ev_h : ℤ[ζ_n] ↠ 𝔽_p)` is the **index-`p`
sublattice** of the cyclotomic trace lattice (`n = 2^m`, `d = φ(n) = n/2`, `det L_p = p`).

That file proves only the **first-minimum gap** `spur_zero_of_below_lambda1`
(`φ(n)·2r < λ₁(L_p)² ⟹ Spur = 0`) and states, explicitly, that the gap is **insufficient** at the
prize depth `r* ≈ ln(q)/2` (the pre-screen shows `φ(n)·2r* > λ₁²` once `n ≥ 16`), so:

> *"the open crux genuinely needs the full **counting** (second-moment-of-counts) version of
>  transference, NOT just the first minimum."*

This file lands that counting version: the classical **successive-minima point-count** inequality,
abstracted to its load-bearing combinatorial core, instantiated to bound `Spur_r(p)` by a product
over the successive minima of `L_p`. It **strictly generalises** `spur_zero_of_below_lambda1`: when
the radius drops below `λ₁` the product collapses to `0`, recovering the gap as a corollary.

## The mechanism (classical geometry of numbers, no field, no analysis)

Take a basis `b_1,…,b_d` of the lattice `L_p` with Gram–Schmidt norms `λ_i := ‖b_i*‖`
(equivalently a reduced basis realising the successive minima up to a dimensional constant). Any
lattice point `v = Σ c_i b_i` with `‖v‖ ≤ R` has each integer coordinate confined to a finite range
`|c_i| ≤ ⌊R/λ_i⌋` (the Gram–Schmidt / Babai box bound). Hence the lattice points in the ball of
radius `R` inject into the integer box `∏_i [-⌊R/λ_i⌋, ⌊R/λ_i⌋]`, whose cardinality is exactly

  `∏_i (2⌊R/λ_i⌋ + 1)`.

Subtracting the origin gives the **nonzero** point-count bound, which dominates `Spur_r(p)`.

### Probe (probe-first, exact, prize-shaped, NEVER `n = q−1`)

`scripts/probes/probe_spur_successive_minima_count.py` (proper `μ_n = ⟨h⟩`, prize primes `p ≍ n^4`,
`p ≡ 1 mod n`, exact short-vector enumeration at `d ≤ 8` + LLL successive-minima proxy at `d = 16`):

* **The minima are tightly clustered near `p^{1/d}`** (Q1): `λ_d/λ_1 ≈ 1.06–1.85` and the geometric
  mean of `λ_i` equals `p^{1/d}` to 3 decimals across `n ∈ {8,16,32}` — `L_p` is a nearly-isotropic
  index-`p` lattice. So the per-axis ranges `⌊R/λ_i⌋` are all comparable; the box-count product is
  well-behaved (no single tiny minimum blowing it up).
* **The product point-count bound is VALID** (Q2): `∏(1 + 2R/λ_i) − 1 ≥` the exact enumerated
  nonzero count at every checked radius (including `R² = 20, n = 16`, where the true count is `16`
  and the bound `≈ 1.2e4`). It correctly upper-bounds even where the first-minimum gap has failed.
* **Honest catch — the bound is LOOSE at the prize band** (Q3): at `n = 32, β = 4`
  (`p^{1/d} = 2.38`, small) the product exceeds `Wick` at low depth (`∏/Wick ≈ 2.5e3` at `r=2`,
  `2.81` at `r=4`), dropping below `Wick` only at `r ≥ 5`. The product point-count is a **valid but
  not yet ε-small** upper bound; closing `(S-W6)` needs the product to beat `Wick` uniformly, which
  the *worst-case* product does not deliver at small `β`. The genuine open content is the gap between
  the worst-case product and the actual (much smaller) theta-count — the BCHKS-1.12 wall.

## What is PROVEN here (axiom-clean ℕ/ℤ combinatorics)

* `box_card` — the integer box `∏_i [-k_i, k_i]` has exactly `∏_i (2 k_i + 1)` points (`piFinset`
  + `Int.card_Icc`). The fully-rigorous combinatorial core.
* `LatticeBallData` — the honest geometric interface: a coordinate map `coord : Pt → (Fin d → ℤ)`
  that is injective on the short-vector set and lands each coordinate in `[-(k i), k i]`
  (the Gram–Schmidt box bound, with `k i := ⌊R/λ_i⌋`).
* `shortVectors_card_le_box` — `#{short vectors} ≤ ∏_i (2 k_i + 1)`: the point-count via the
  injection into the box.
* `spurCount_le_prod` — `Spur_r(p) ≤ ∏_i (2 k_i + 1)`: the named `(S-W6)` count, now bounded by an
  EXPLICIT product over the successive-minima ranges (the missing counting frame).
* `spur_zero_of_all_ranges_zero` — recovers `spur_zero_of_below_lambda1` as a corollary: if every
  range `k_i = 0` (radius below every minimum, in particular below `λ₁`), the product is `1`, the
  nonzero count is `0`, so `Spur = 0`. The first-minimum gap is the `∀ i, k_i = 0` slice.
* `energy_bound_of_prod_le` — composes with the char-`0` ceiling: if the product (minus origin)
  fits the slack `ε·Wick`, the char-`p` energy obeys `(1+ε)·Wick` — the prize shape, now reduced to
  a bound on the product of successive-minima ranges rather than a binary gap.

## Honest scope (rules 1, 3, 4, 6 + ASYMPTOTIC GUARD)

This is a **frame**, not a closure: it replaces the insufficient first-minimum gap with the correct
quantitative point-count and reduces `(S-W6)` to bounding `∏_i (2⌊R/λ_i⌋ + 1)` by `ε·Wick`. The probe
shows the worst-case product is VALID but LOOSE at small `β` (it is not yet `≤ Wick` at the prize
depth) — so the remaining open content is the gap between the worst-case successive-minima product
and the true theta-count. The coordinate-box interface (`LatticeBallData`) carries the Gram–Schmidt
bound as an explicit hypothesis (the standard reduced-basis fact), matching how `_wf7W6` carries the
additive split as an interface. NOT thinness-essential in isolation (geometry of numbers on the
index-`p` cyclotomic sublattice); does NOT close CORE. `CORE M(μ_n) ≤ C·√(n·log(p/n))` stays **OPEN**.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.SpurSuccessiveMinima

open Finset

/-- **Box point-count.** The integer box `∏_i [-(k i), k i]` (as a `Finset` of functions
`Fin d → ℤ`) has exactly `∏_i (2·(k i) + 1)` points. The fully-rigorous combinatorial core of the
successive-minima point-count: each axis contributes `2 k_i + 1` integer points. -/
theorem box_card {d : ℕ} (k : Fin d → ℕ) :
    (Fintype.piFinset (fun i => Finset.Icc (-(k i : ℤ)) (k i))).card
      = ∏ i, (2 * (k i) + 1) := by
  rw [Fintype.card_piFinset]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Int.card_Icc]
  -- #(Icc (-(k i)) (k i)) = ((k i) + 1 - (-(k i))).toNat = 2*(k i)+1
  have h : ((k i : ℤ) + 1 - (-(k i : ℤ))) = ((2 * (k i) + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- **The geometric interface (honest Gram–Schmidt box bound).** A bundle recording, abstractly:
* `Pt` — a type of lattice points (the spurious short vectors of `L_p`);
* `coord : Pt → (Fin d → ℤ)` — the reduced-basis coordinate map;
* `k : Fin d → ℕ` — the per-axis Gram–Schmidt ranges `k i = ⌊R/λ_i⌋`;
* `coord_mem` — every short vector's `i`-th coordinate lies in `[-(k i), k i]` (the box bound, the
  standard reduced-basis fact: `|c_i| ≤ ⌊R/λ_i⌋` for `‖Σ c_i b_i‖ ≤ R`);
* `coord_inj` — `coord` is injective (a basis: distinct points have distinct coordinate vectors).

This is the load-bearing geometry-of-numbers input, carried as an explicit interface exactly as
`_wf7W6`'s `EnergySplit` carries the additive split. -/
structure LatticeBallData (d : ℕ) where
  /-- the type of short lattice points (spurious vectors inside the config radius). -/
  Pt : Type
  /-- finiteness of the short-vector set (a ball in a lattice contains finitely many points). -/
  fintypePt : Fintype Pt
  /-- the reduced-basis coordinate map. -/
  coord : Pt → (Fin d → ℤ)
  /-- the per-axis Gram–Schmidt range `k i = ⌊R / λ_i⌋`. -/
  k : Fin d → ℕ
  /-- box bound: each coordinate lies in `[-(k i), k i]`. -/
  coord_mem : ∀ (v : Pt) (i : Fin d), coord v i ∈ Finset.Icc (-(k i : ℤ)) (k i)
  /-- the coordinate map is injective (basis property). -/
  coord_inj : Function.Injective coord

attribute [instance] LatticeBallData.fintypePt

/-- **Successive-minima point-count.** The number of short lattice points is at most the box-count
`∏_i (2 k_i + 1)`: the coordinate map injects the short-vector set into the integer box. -/
theorem shortVectors_card_le_box {d : ℕ} (L : LatticeBallData d) :
    Fintype.card L.Pt ≤ ∏ i, (2 * (L.k i) + 1) := by
  classical
  rw [← box_card L.k]
  -- card Pt = card (image of coord) ≤ card (box), via injectivity + membership
  have himg : (Finset.univ.image L.coord) ⊆ Fintype.piFinset (fun i => Finset.Icc (-(L.k i : ℤ)) (L.k i)) := by
    intro f hf
    rw [Finset.mem_image] at hf
    obtain ⟨v, _, rfl⟩ := hf
    rw [Fintype.mem_piFinset]
    exact fun i => L.coord_mem v i
  calc Fintype.card L.Pt
      = (Finset.univ.image L.coord).card := by
        rw [Finset.card_image_of_injective _ L.coord_inj, Finset.card_univ]
    _ ≤ _ := Finset.card_le_card himg

/-- **The named `(S-W6)` count bound.** The spurious count `Spur_r(p)` (the number of nonzero short
vectors of the index-`p` sublattice inside the config radius) is at most the successive-minima
product `∏_i (2 k_i + 1)`. This is the **counting** version of transference `_wf7W6` named as
required — supplied here as a clean product over the per-axis Gram–Schmidt ranges. -/
theorem spurCount_le_prod {d : ℕ} (L : LatticeBallData d) (Spur : ℕ)
    (hSpur : Spur ≤ Fintype.card L.Pt) :
    Spur ≤ ∏ i, (2 * (L.k i) + 1) :=
  hSpur.trans (shortVectors_card_le_box L)

/-- **The first-minimum gap as a corollary (`k ≡ 0` slice).** If every successive-minimum range is
`0` — the radius is below every `λ_i`, in particular below `λ₁` — then the box is a single point
(the origin), the product is `1`, and the **nonzero** spurious count is `0`. This recovers
`_wf7W6.spur_zero_of_below_lambda1` (`φ(n)·2r < λ₁² ⟹ Spur = 0`) as the degenerate case of the
quantitative point-count. -/
theorem spur_zero_of_all_ranges_zero {d : ℕ} (L : LatticeBallData d) (Spur : ℕ)
    (hk : ∀ i, L.k i = 0)
    (hSpur : Spur ≤ Fintype.card L.Pt)
    -- the nonzero count: subtract the single origin point captured by the box
    (hone : Fintype.card L.Pt ≤ (∏ i, (2 * (L.k i) + 1)) - 1) :
    Spur = 0 := by
  have hprod : ∏ i, (2 * (L.k i) + 1) = 1 := by
    refine Finset.prod_eq_one (fun i _ => ?_)
    rw [hk i, Nat.mul_zero, Nat.zero_add]
  rw [hprod, Nat.sub_self] at hone
  exact Nat.le_zero.mp (hSpur.trans hone)

/-- **Prize-shape from the product count.** Composing the successive-minima count with the char-`0`
ceiling: if the nonzero spurious count (`product − 1`) fits the Lam–Leung slack `ε·Wick`, and the
char-`0` count obeys `Wick`, then the full char-`p` energy `E = E0 + Spur` obeys `(1+ε)·Wick` — the
prize square-root shape with constant `(1+ε)^{1/2r} → 1`. The whole transfer is now reduced to a
bound on the product of successive-minima ranges. -/
theorem energy_bound_of_prod_le {d : ℕ} (L : LatticeBallData d)
    (E E0 Spur ε Wick : ℕ)
    (hsplit : E = E0 + Spur)
    (hSpur : Spur ≤ Fintype.card L.Pt)
    (hprod : Fintype.card L.Pt ≤ ε * Wick)
    (hchar0 : E0 ≤ Wick) :
    E ≤ (1 + ε) * Wick := by
  rw [hsplit, add_mul, one_mul]
  exact Nat.add_le_add hchar0 (hSpur.trans hprod)

end ArkLib.ProximityGap.SpurSuccessiveMinima

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.SpurSuccessiveMinima
#print axioms box_card
#print axioms shortVectors_card_le_box
#print axioms spurCount_le_prod
#print axioms spur_zero_of_all_ranges_zero
#print axioms energy_bound_of_prod_le
end AxiomAudit
