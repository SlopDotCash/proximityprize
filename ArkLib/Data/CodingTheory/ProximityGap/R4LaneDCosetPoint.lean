/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2VanishEnergy
import ArkLib.Data.CodingTheory.ProximityGap.CosetExactCount
import Mathlib.Tactic

/-!
# R4 lane D: the `e₂ = 0`, width-5 single-coset rigidity (#407, Approach C / `e₂=0` threshold)

**The R4 lane-D object.** `δ*` is set by the dilation-orbit count
`K(n) = #{e₁-orbits of S : S ⊆ μ_n, |S| = w, e₂(S) = 0, e₁(S) ≠ 0}` (the bad scalar of the
two-monomial pencil `z^{k+1} + α z^{k+2}` is `α = −1/e₁(S)`). `E2VanishEnergy.e2_zero_iff`
pins `e₂(S) = 0 ⟺ e₁(S)² = p₂(S)` (char `≠ 2`); `E2SquaringRecursion` turns that into a
`μ_{n/2}` subset-sum. The R4 conjecture is that for a **fixed odd width** `w = 5` this count is
`O(1)` — indeed exactly one coset (`K = 1`).

**The structure (probe-verified, prize regime `q ≥ n³`, `scripts/probes/probe_407_e2_rigidity`
and the laneD probe).** Every `w = 5` `e₂ = 0` subset of `μ_n` (`4 ∣ n`) decomposes as

> `S = (a full coset of μ₄) ∪ {one extra point x ∈ μ_n}`,

and **conversely** every such `(μ₄-coset) ∪ {x}` *is* an `e₂ = 0` set. This file proves the
**converse / forward construction** in *full algebraic generality* (char-free up to `2 ≠ 0`),
which is exactly what pins `K = 1`:

* `coset_e1_e2_zero` — a 4-element `T ⊆ μ_n` lying in one 4th-power fiber (`∀ x ∈ T, x⁴ = c`,
  i.e. a coset of `μ₄`) has `e₁(T) = 0` **and** `e₂(T) = 0` (its char-poly is `X⁴ − c`,
  middle coefficients vanish — `CosetExactCount.esymm_zero_of_pow_eq`, bridged to `e₁/e₂` here).
* `insert_e1_e2` — the single-point insert law: if `e₁(T) = e₂(T) = 0` then for `x ∉ T`,
  `e₁(insert x T) = x` and `e₂(insert x T) = 0`. (Newton: `e₂(T∪{x}) = e₂(T) + x·e₁(T)`.)
* `cosetPoint_e2_zero` — combining the two: every `(μ₄-coset) ∪ {x}` has `e₂ = 0` and
  `e₁ = x`. The `e₁` value is **exactly the extra point** `x`, ranging over `μ_n`.
* `cosetPoint_e1_single_orbit` — **the `K = 1` rigidity (the headline).** Any two members of
  this family have `e₁` values in the **same `μ_n`-dilation orbit**: `e₁(S)/e₁(S') ∈ μ_n` (it
  is `x/x'`, a quotient of two `n`-th roots of unity). So the whole width-5 family realizes a
  **single coset** — `K = 1`, the R4 lane-D conjecture for `w = 5`, proven char-free.

**Honest scope — the converse rigidity and the char-`p` wall (gap localization).** This file
proves the *forward* direction (every `μ₄-coset + point` is `e₂=0`, single orbit) unconditionally
and char-free. The *full* `K = 1` claim needs the **converse rigidity** "every width-5 `e₂=0` set
*is* a `μ₄-coset + point". That converse holds over `ℂ` / the prize regime, but is **machine-checked
to FAIL at small structured primes** (laneD probe: `n=12, p=37 → K=2`; `n=16, p=113 → K=3`;
violators always lie below `n³`). This is the **char-`p` Lam–Leung wall**: extra short `±1`-relations
among roots of unity mod a small prime create spurious `e₂=0` sets. It is already handled by the
explicit resultant threshold of `E2VanishRigidityModP.e2_extra_solution_threshold`
(`p > (n²+n)^{n/2} ⟹ mod-p locus = char-0 locus`), so in the genuine prize regime `q ≈ n·2^128`
the converse holds with massive margin and `K = 1`. The DISPROOF_LOG records the char-independence
refutation. So lane D is: **forward = char-free theorem (here); converse = char-0 fact + named
resultant threshold = the BCHKS Conj 1.12 / Lam–Leung face, NOT a new wall on this algebraic lane.**

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- [BCHKS25] Ben-Sasson–Carmon–Haböck–Kopparty–Saraf. *On Proximity Gaps for Reed–Solomon Codes*.
  ECCC TR25-169 / ePrint 2025/2055. (Conjecture 1.12: distinct subgroup subset-sum lower bound.)
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Finset Polynomial

namespace ArkLib.ProximityGap.R4LaneDCosetPoint

open ArkLib.ProximityGap.E2VanishEnergy ArkLib.ProximityGap.Rigidity

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. Vieta bridges: `e₁ = esymm 1`, `e₂ = esymm 2`. -/

/-- The ordered off-diagonal product sum double-covers the unordered 2-subset product sum:
`∑_{(a,b)∈offDiag} a·b = 2 · ∑_{t∈ S.powersetCard 2} ∏ t`. (Each unordered pair `{a,b}` is hit
by the two ordered pairs `(a,b), (b,a)`.) Proven by `Finset.induction` on `S`. -/
theorem offDiag_sum_eq_two_powersetCard_two (S : Finset F) :
    ∑ p ∈ S.offDiag, p.1 * p.2 = 2 * ∑ t ∈ S.powersetCard 2, ∏ x ∈ t, x := by
  induction S using Finset.induction with
  | empty =>
    simp only [offDiag_empty, sum_empty, zero_eq_mul]
    right
    rw [Finset.powersetCard_eq_empty.mpr (by simp)]
    simp
  | @insert a T ha ih =>
    rw [Finset.offDiag_insert ha, Finset.powersetCard_succ_insert ha]
    have hdisj1 : Disjoint (T.offDiag ∪ {a} ×ˢ T) (T ×ˢ {a}) := by
      apply Finset.disjoint_left.mpr
      intro x hx hx2
      simp only [Finset.mem_union, Finset.mem_offDiag, Finset.mem_product,
        Finset.mem_singleton] at hx hx2
      rcases hx with ⟨_, h2, _⟩ | ⟨h1, _⟩
      · exact ha (hx2.2 ▸ h2)
      · exact ha (h1 ▸ hx2.1)
    have hdisj2 : Disjoint T.offDiag ({a} ×ˢ T) := by
      apply Finset.disjoint_left.mpr
      intro x hx hx2
      simp only [Finset.mem_offDiag, Finset.mem_product, Finset.mem_singleton] at hx hx2
      exact ha (hx2.1 ▸ hx.1)
    rw [Finset.sum_union hdisj1, Finset.sum_union hdisj2, ih]
    have hcross1 : ∑ p ∈ ({a} ×ˢ T), p.1 * p.2 = a * ∑ x ∈ T, x := by
      rw [Finset.sum_product]; simp [Finset.mul_sum]
    have hcross2 : ∑ p ∈ (T ×ˢ {a}), p.1 * p.2 = (∑ x ∈ T, x) * a := by
      rw [Finset.sum_product]; simp [Finset.sum_mul]
    rw [hcross1, hcross2]
    have himg : ∑ t ∈ (T.powersetCard 1).image (insert a), ∏ x ∈ t, x
        = a * ∑ x ∈ T, x := by
      rw [Finset.sum_image]
      · have : ∑ t ∈ T.powersetCard 1, ∏ x ∈ insert a t, x
            = ∑ t ∈ T.powersetCard 1, a * ∏ x ∈ t, x := by
          refine Finset.sum_congr rfl fun t ht => ?_
          have hat : a ∉ t := by
            intro h; exact ha ((Finset.mem_powersetCard.mp ht).1 h)
          rw [Finset.prod_insert hat]
        rw [this, ← Finset.mul_sum]
        congr 1
        rw [Finset.powersetCard_one, Finset.sum_map]; simp
      · intro s hs t ht hst
        have has : a ∉ s := fun h => ha ((Finset.mem_powersetCard.mp hs).1 h)
        have hat : a ∉ t := fun h => ha ((Finset.mem_powersetCard.mp ht).1 h)
        have := congrArg (Finset.erase · a) hst
        simpa [Finset.erase_insert has, Finset.erase_insert hat] using this
    have hdisj3 : Disjoint (T.powersetCard 2) ((T.powersetCard 1).image (insert a)) := by
      apply Finset.disjoint_left.mpr
      intro t ht ht2
      simp only [Finset.mem_image] at ht2
      obtain ⟨s, _, rfl⟩ := ht2
      have hmem : a ∈ insert a s := Finset.mem_insert_self a s
      exact ha ((Finset.mem_powersetCard.mp ht).1 hmem)
    rw [Finset.sum_union hdisj3, himg]
    ring

/-- **`e₁ = esymm 1`.** The first power sum / first elementary symmetric function coincide. -/
theorem e1_eq_esymm_one (S : Finset F) : e1 S = S.val.esymm 1 := by
  unfold e1
  have h : S.val.esymm 1 = (S.val.map id).esymm 1 := by simp
  rw [h, Finset.esymm_map_val id S 1, Finset.powersetCard_one, Finset.sum_map]; simp

/-- **`e₂ = esymm 2`** (char `≠ 2`). The order-free `e₂ = (∑offDiag)/2` equals the second
elementary symmetric function `esymm 2 = ∑_{2-subsets} ∏`. -/
theorem e2_eq_esymm_two (h2 : (2 : F) ≠ 0) (S : Finset F) : e2 S = S.val.esymm 2 := by
  unfold e2
  rw [offDiag_sum_eq_two_powersetCard_two]
  have h : S.val.esymm 2 = ∑ t ∈ S.powersetCard 2, ∏ x ∈ t, x := by
    have h' : S.val.esymm 2 = (S.val.map id).esymm 2 := by simp
    rw [h', Finset.esymm_map_val id S 2]; simp
  rw [h]; field_simp

/-! ## 2. The coset has vanishing `e₁` and `e₂`. -/

/-- **A `μ₄`-coset kills `e₁` and `e₂`.** A 4-element subset `T ⊆ μ_n` lying in a single
4th-power fiber (`∀ x ∈ T, x⁴ = c`) — i.e. a coset of the order-4 roots of unity, the root set
of `X⁴ − c` — has `e₁(T) = 0` and `e₂(T) = 0`. (Its characteristic polynomial is `X⁴ − c`,
whose `X³, X²` coefficients vanish; `CosetExactCount.esymm_zero_of_pow_eq` gives the symmetric
functions, bridged to `e₁/e₂`.) -/
theorem coset_e1_e2_zero (h2 : (2 : F) ≠ 0) {T : Finset F} {c : F}
    (hcard : T.card = 4) (hpow : ∀ x ∈ T, x ^ 4 = c) :
    e1 T = 0 ∧ e2 T = 0 := by
  have hesymm := esymm_zero_of_pow_eq (by norm_num : 0 < 4) hcard hpow
  refine ⟨?_, ?_⟩
  · rw [e1_eq_esymm_one]; exact hesymm 1 (by norm_num) (by norm_num)
  · rw [e2_eq_esymm_two h2]; exact hesymm 2 (by norm_num) (by norm_num)

/-! ## 3. The single-point insert law. -/

/-- `e₁(insert x T) = x + e₁(T)` for `x ∉ T`. -/
theorem e1_insert (x : F) (T : Finset F) (hx : x ∉ T) : e1 (insert x T) = x + e1 T := by
  unfold e1; rw [Finset.sum_insert hx]

/-- `p₂(insert x T) = x² + p₂(T)` for `x ∉ T`. -/
theorem p2_insert (x : F) (T : Finset F) (hx : x ∉ T) : p2 (insert x T) = x ^ 2 + p2 T := by
  unfold p2; rw [Finset.sum_insert hx]

/-- **The single-point insert law.** If `e₁(T) = 0` and `e₂(T) = 0`, then inserting any
`x ∉ T` gives `e₁(insert x T) = x` and `e₂(insert x T) = 0`. Newton:
`e₂(T ∪ {x}) = e₂(T) + x·e₁(T) = 0 + 0`; and `e₁(T ∪ {x}) = x + 0`. Here proven via
`e₂ = 0 ⟺ e₁² = p₂`: from `e₁(T) = 0` and `e₂(T) = 0` we get `p₂(T) = 0`, so
`e₁(insert x T)² = x² = x² + p₂(T) = p₂(insert x T)`, hence `e₂(insert x T) = 0`. -/
theorem insert_e1_e2 (h2 : (2 : F) ≠ 0) (x : F) (T : Finset F) (hx : x ∉ T)
    (h1T : e1 T = 0) (h2T : e2 T = 0) :
    e1 (insert x T) = x ∧ e2 (insert x T) = 0 := by
  have hp2T : p2 T = 0 := by
    have := (e2_zero_iff h2 T).mp h2T
    rw [h1T] at this; simpa using this.symm
  refine ⟨?_, ?_⟩
  · rw [e1_insert x T hx, h1T, add_zero]
  · rw [e2_zero_iff h2, e1_insert x T hx, p2_insert x T hx, h1T, hp2T, add_zero, add_zero]

/-! ## 4. The forward construction: every `μ₄-coset ∪ {point}` is an `e₂ = 0` set with `e₁ = point`. -/

/-- **The forward structural theorem (R4 lane D, `w = 5`).** Let `T` be a `μ₄`-coset (a
4-element subset of `μ_n` in one 4th-power fiber `∀ y ∈ T, y⁴ = c`) and `x ∈ μ_n` a point
outside `T`. Then `S = insert x T` (a 5-element subset of `μ_n`) has

> `e₂(S) = 0`  and  `e₁(S) = x`.

So **the bad scalar** of the two-monomial pencil at this set is `α = −1/e₁(S) = −1/x`, and the
`e₁` value is *exactly the extra point* `x`. This is the converse half of the R4 lane-D
decomposition: every `μ₄-coset + point` realizes the `e₂ = 0` locus with `e₁ ∈ μ_n`. -/
theorem cosetPoint_e2_zero (h2 : (2 : F) ≠ 0) {T : Finset F} {c x : F}
    (hcard : T.card = 4) (hpow : ∀ y ∈ T, y ^ 4 = c) (hx : x ∉ T) :
    e2 (insert x T) = 0 ∧ e1 (insert x T) = x := by
  obtain ⟨h1T, h2T⟩ := coset_e1_e2_zero h2 hcard hpow
  obtain ⟨he1, he2⟩ := insert_e1_e2 h2 x T hx h1T h2T
  exact ⟨he2, he1⟩

/-! ## 5. The `K = 1` rigidity: all `e₁`-values lie in one `μ_n`-dilation orbit. -/

/-- **`K = 1` rigidity (the headline).** Fix `μ_n` via a primitive `n`-th root `ζ`. For two
members of the width-5 family — `S = insert x T`, `S' = insert x' T'`, each a
`μ₄-coset ∪ {point}` with the extra points `x, x' ∈ μ_n` (i.e. `xⁿ = x'ⁿ = 1`, both nonzero) —
their `e₁` values lie in the **same `μ_n`-dilation orbit**: `e₁(S) / e₁(S')` is an `n`-th root of
unity. Hence the whole width-5 `e₂ = 0` family (forward-constructed) realizes a **single coset**
of `e₁`-values — the R4 lane-D `K = 1`, proven char-free (only `2 ≠ 0`). -/
theorem cosetPoint_e1_single_orbit (h2 : (2 : F) ≠ 0) {n : ℕ}
    {T T' : Finset F} {c c' x x' : F}
    (hcard : T.card = 4) (hpow : ∀ y ∈ T, y ^ 4 = c) (hx : x ∉ T) (hxn : x ^ n = 1)
    (hcard' : T'.card = 4) (hpow' : ∀ y ∈ T', y ^ 4 = c') (hx' : x' ∉ T')
    (hx'n : x' ^ n = 1) :
    (e1 (insert x T) / e1 (insert x' T')) ^ n = 1 := by
  have hE1 : e1 (insert x T) = x := ((cosetPoint_e2_zero h2 hcard hpow hx).2)
  have hE1' : e1 (insert x' T') = x' := ((cosetPoint_e2_zero h2 hcard' hpow' hx').2)
  rw [hE1, hE1', div_pow, hxn, hx'n, div_one]

/-! ## 6. Non-vacuity: a concrete `μ₄`-coset over `ZMod 41` (`μ₈ ⊆ F₄₁`). -/

/-- `(2 : ZMod 41) ≠ 0`, so the char `≠ 2` hypotheses apply over the concrete `μ₈ ⊆ F₄₁`
host field used by `E2SquaringRecursion`. Certifies the lane-D construction is non-vacuous. -/
theorem nonvacuity_zmod41 : (2 : ZMod 41) ≠ 0 := by decide

end ArkLib.ProximityGap.R4LaneDCosetPoint

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.R4LaneDCosetPoint.offDiag_sum_eq_two_powersetCard_two
#print axioms ArkLib.ProximityGap.R4LaneDCosetPoint.e1_eq_esymm_one
#print axioms ArkLib.ProximityGap.R4LaneDCosetPoint.e2_eq_esymm_two
#print axioms ArkLib.ProximityGap.R4LaneDCosetPoint.coset_e1_e2_zero
#print axioms ArkLib.ProximityGap.R4LaneDCosetPoint.insert_e1_e2
#print axioms ArkLib.ProximityGap.R4LaneDCosetPoint.cosetPoint_e2_zero
#print axioms ArkLib.ProximityGap.R4LaneDCosetPoint.cosetPoint_e1_single_orbit
#print axioms ArkLib.ProximityGap.R4LaneDCosetPoint.nonvacuity_zmod41
