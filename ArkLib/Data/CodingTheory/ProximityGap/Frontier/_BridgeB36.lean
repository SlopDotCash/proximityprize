/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Lagrange

/-!
# Bridge B36 — divided-difference vanishing ⟺ RS membership (target X, #444)

**Claim (spec B36).** Divided-difference vanishing on `s` distinct nodes is equivalent to the
word interpolating a polynomial of degree `< k = #s − 1`, i.e. Reed–Solomon membership at
dimension `k`.

**Object.** Over a field `F`, a *word* is a value map `r : ι → F` evaluated at distinct nodes
`v i` for `i ∈ s` (`Set.InjOn v s`). The **top-order divided difference** of `r` over the `#s`
nodes is the classical Newton/Lagrange leading-coefficient sum

  `DD s v r = ∑_{i ∈ s} r i / ∏_{j ∈ s.erase i} (v i − v j)`.

This is the leading coefficient of the unique interpolant of degree `< #s`. The bridge says:
`DD s v r = 0` ⟺ that interpolant has degree `< #s − 1` ⟺ the word agrees on `s` with a
polynomial of degree `< #s − 1` (= an `RS[#s−1]` codeword).

**What is proven (all axiom-clean, from `Mathlib.LinearAlgebra.Lagrange`):**

* `coeff_interpolate_top` — the leading-coefficient = divided-difference identity:
  `(interpolate s v r).coeff (#s − 1) = DD s v r`. This is the term-by-term content of
  `Lagrange.interpolate_eq_sum`: each Lagrange-form term is `C (r i / ∏ …) · ∏_{j≠i}(X − C (v j))`,
  a monic polynomial of degree `#s − 1`, so its top coefficient is exactly the scalar
  `r i / ∏_{j≠i}(v i − v j)`.

* `dividedDifference_eq_zero_iff_degree_lt` — the bridge in interpolant form:
  for nonempty `s` and distinct nodes, `DD s v r = 0 ↔ (interpolate s v r).degree < #s − 1`.

* `dividedDifference_eq_zero_iff_rs_member` — the bridge in RS-membership form:
  `DD s v r = 0 ↔ ∃ p : F[X], p.degree < #s − 1 ∧ ∀ i ∈ s, p.eval (v i) = r i`.
  The existential witness, when it exists, is the interpolant itself; conversely any
  low-degree interpolating polynomial *is* the interpolant (uniqueness, `eq_interpolate_iff`),
  so its degree is `< #s − 1` forcing the top coefficient — hence `DD` — to vanish.

This is the definitional bridge `DD_k = 0 ⟺ in RS` of the empirical-formula programme: it is the
exact statement that pins the order of the over-determination depth `m = s − k` to the geometry
of the far line through the period spectrum (it sits *under* `IncidencePeriodBridge.lean`, whose
`lineIncidence` is the count `#{γ : s₀ + γ s₁ ∈ G}` of nodes a far line meets — RS membership of a
windowed word is exactly the `DD = 0` condition here). The character-sum substrate is not
*consumed* by this polynomial fact; this brick is self-contained Lagrange theory, recorded in the
`Frontier/` so the empirical bridge `E1/E3` chain can cite it directly.

Axiom-clean; no field-size or regime hypotheses beyond `Set.InjOn v s` and `s.Nonempty`.
Issue #444.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.BridgeB36

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι → F} (r : ι → F)

/-- **Top-order divided difference** of the word `r` over the nodes `v` on `s`. Classical
Newton/Lagrange form: `DD s v r = ∑_{i ∈ s} r i / ∏_{j ∈ s.erase i} (v i − v j)`. It is the
leading coefficient of the degree `< #s` interpolant (`coeff_interpolate_top`). -/
noncomputable def dividedDifference (s : Finset ι) (v : ι → F) (r : ι → F) : F :=
  ∑ i ∈ s, r i / ∏ j ∈ s.erase i, (v i - v j)

/-- **The leading-coefficient = divided-difference identity.** The coefficient of degree
`#s − 1` of the Lagrange interpolant is exactly the top-order divided difference of the word.
This is the term-by-term content of `Lagrange.interpolate_eq_sum`. -/
theorem coeff_interpolate_top (hvs : Set.InjOn v s) :
    (Lagrange.interpolate s v r).coeff (#s - 1) = dividedDifference s v r := by
  classical
  rw [Lagrange.interpolate_eq_sum, finset_sum_coeff, dividedDifference]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  -- Each term: `C c * ∏_{j ≠ i}(X - C (v j))`, monic of degree `#s − 1`.
  rw [coeff_C_mul]
  -- The product `∏_{j ∈ s.erase i}(X - C (v j))` is monic of natDegree `#(s.erase i) = #s − 1`,
  -- so its coefficient at `#s − 1` is `1`.
  have hcard : #(s.erase i) = #s - 1 := Finset.card_erase_of_mem hi
  have hmon : (∏ j ∈ s.erase i, (X - C (v j))).Monic := monic_prod_X_sub_C v (s.erase i)
  have hdeg : (∏ j ∈ s.erase i, (X - C (v j))).natDegree = #s - 1 := by
    rw [natDegree_finset_prod_X_sub_C_eq_card, hcard]
  have hcoeff : (∏ j ∈ s.erase i, (X - C (v j))).coeff (#s - 1) = 1 := by
    have := hmon.coeff_natDegree
    rwa [hdeg] at this
  rw [hcoeff, mul_one]

/-- The interpolant always has degree `≤ #s − 1` (Mathlib `degree_interpolate_le`), restated
in `Nat`-cast form for the `degree < #s − 1 ↔ coeff (#s−1) = 0` argument. -/
theorem degree_interpolate_le' (hvs : Set.InjOn v s) :
    (Lagrange.interpolate s v r).degree ≤ (↑(#s - 1) : WithBot ℕ) :=
  Lagrange.degree_interpolate_le r hvs

/-- **Bridge (interpolant form).** For distinct nodes on a nonempty window, the top-order
divided difference of the word vanishes **iff** its interpolant has degree `< #s − 1`. -/
theorem dividedDifference_eq_zero_iff_degree_lt
    (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    dividedDifference s v r = 0 ↔ (Lagrange.interpolate s v r).degree < (#s - 1 : ℕ) := by
  classical
  set p := Lagrange.interpolate s v r with hp
  have hle : p.degree ≤ (↑(#s - 1) : WithBot ℕ) := degree_interpolate_le' r hvs
  constructor
  · -- `DD = 0` ⟹ top coeff is `0` and degree `≤ #s−1`, so degree `< #s−1`.
    intro hDD
    have htop : p.coeff (#s - 1) = 0 := by
      rw [hp, coeff_interpolate_top r hvs, hDD]
    -- All higher coefficients vanish (degree ≤ #s−1) and the `#s−1` one too.
    rw [degree_lt_iff_coeff_zero]
    intro m hm
    rcases lt_or_eq_of_le hm with hlt | heq
    · exact coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hle (by exact_mod_cast hlt))
    · rw [← heq]; exact htop
  · -- degree `< #s−1` ⟹ its `(#s−1)`-coefficient is `0` = `DD`.
    intro hdeg
    have htop : p.coeff (#s - 1) = 0 :=
      coeff_eq_zero_of_degree_lt (by exact_mod_cast hdeg)
    rw [← coeff_interpolate_top r hvs, ← hp, htop]

/-- **Bridge (RS-membership form, target X).** For distinct nodes on a nonempty window, the
top-order divided difference of the word vanishes **iff** the word agrees on `s` with some
polynomial of degree `< #s − 1` — i.e. iff the windowed word is a codeword of `RS[#s − 1]`. -/
theorem dividedDifference_eq_zero_iff_rs_member
    (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    dividedDifference s v r = 0 ↔
      ∃ p : F[X], p.degree < (#s - 1 : ℕ) ∧ ∀ i ∈ s, p.eval (v i) = r i := by
  classical
  rw [dividedDifference_eq_zero_iff_degree_lt r hvs hs]
  constructor
  · -- The interpolant itself is the witness; it matches `r` on `s` by `eval_interpolate_at_node`.
    intro hdeg
    exact ⟨Lagrange.interpolate s v r, hdeg,
      fun i hi => Lagrange.eval_interpolate_at_node r hvs hi⟩
  · -- Any low-degree interpolating polynomial IS the interpolant (uniqueness), so its degree
    -- bound transfers to the interpolant.
    rintro ⟨p, hpdeg, hpeval⟩
    have hpdeg' : p.degree < #s :=
      lt_trans hpdeg (by exact_mod_cast Nat.sub_lt hs.card_pos Nat.one_pos)
    have hpeq : p = Lagrange.interpolate s v r :=
      (Lagrange.eq_interpolate_iff r hvs).mp ⟨hpdeg', hpeval⟩
    rwa [hpeq] at hpdeg

end ArkLib.ProximityGap.BridgeB36

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.BridgeB36.coeff_interpolate_top
#print axioms ArkLib.ProximityGap.BridgeB36.dividedDifference_eq_zero_iff_degree_lt
#print axioms ArkLib.ProximityGap.BridgeB36.dividedDifference_eq_zero_iff_rs_member
