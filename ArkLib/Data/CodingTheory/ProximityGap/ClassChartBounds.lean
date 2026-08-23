/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.TopDirectionLineCount

/-!
# Issue #232 — class-chart bounds: scaling orbits and the Aliev–Smyth decomposition (O51)

The provable parts of the DISPROOF_LOG **O51** class-chart program — the extension of the
tower/point-fiber theory (`LamLeungTwoPow.lean`, `TopDirectionLineCount.lean`) from the
zero syndrome class `ē = 0` toward *all* top-window syndrome classes.

**The object.** `psumFiber D₀ w t a` is the power-sum fiber
`{S ⊆ D₀ : |S| = w, ∀ j ∈ [1, t], p_j(S) = a j}` — by the Newton bridge
(`esymm_window_iff_psum_window`, LamLeungTwoPow.lean) this carries the same information
as the elementary-symmetric chart away from small characteristic, and by
`zero_fiber_filter_eq` (TopDirectionLineCount.lean) the `a = 0` fiber *is* the
syndrome-side list at the unit syndrome.

**1. The weighted-scaling orbit theorem** (`psumFiber_scaling_card`,
`psumFiber_orbit_card`): for `λ ≠ 0` the map `S ↦ λ·S` is a bijection from the
`(a₁, …, a_t)`-fiber onto the `(λ·a₁, λ²·a₂, …, λ^t·a_t)`-fiber — fiber *cardinality* is
constant on weighted-projective orbits of the parameter chart, and on scaling-invariant
domains (`μ_n`, `F_q^×`, `F_q`) the orbit theorem holds with the domain fixed. The zero
class is the unique fixed point (`zero_fiber_scaling_mem`). Consequence
(`psumFiber_card_le_of_orbit_rep`): any uniform fiber bound need only be certified on a
transversal of the weighted-projective orbits.

**2. The conditional Aliev–Smyth decomposition** (`nonzero_fiber_card_le`): every member
of a fiber is a point of the torsion locus of the variety
`V(p₁ − a₁, …, p_t − a_t) ⊆ 𝔾_m^w` (when `D₀` consists of roots of unity). Aliev–Smyth
(Thm 1.1, arXiv:0704.1747: the number of maximal torsion cosets on a degree-`d`
hypersurface in `𝔾_m^n` is `≤ c₁(n)·d^{c₂(n)}`, explicit constants) bounds the *isolated*
torsion points uniformly in `a` and in the field; the positive-dimensional torsion cosets
are the structured "coset-family" members, counted by the tower machinery
(O46–O50, per coset). Here the input is packaged as the named hypotheses
`ASIsolatedBound` / `CosetFamilyBound` and the decomposition
`fiber = isolated ⊔ coset-family ⟹ |fiber| ≤ C_AS + B` is machine-checked. The
constants stay abstract: formalizing Aliev–Smyth itself (toric geometry + lattice point
counting) is far out of scope.

**3. Kernel-checked instance at `ZMod 13`, `w = 3`, `t = 2`** — with an honest
correction to the O51-probe expectation. The probe (μ₁₆/F₂₅₇, `w = 8`, `t = 3`) found
every nonzero class `≤ 2` with the zero class strictly maximal; at the *small* scale
`ZMod 13`, `w = 3`, `t = 2` the strict dichotomy **fails**: exhaustive kernel check gives
zero-fiber card `4` (`zero_psum_fiber_F13`, matching `zero_fiber_instance` of
TopDirectionLineCount.lean through Newton at `char ≠ 2`), every nonzero fiber `≤ 4`
(`nonzero_fiber_card_le_four_F13`), and the twelve maximal nonzero classes are exactly
ONE weighted-projective orbit — the orbit of `(p₁, p₂) = (5, 4)`
(`nonzero_fiber_le_two_or_rep_orbit_F13`); every class off that orbit has fiber `≤ 2`.
This is the orbit theorem of part 1 visible in the kernel: fiber cardinality is an orbit
invariant, and the part-1 theorem then pins the whole orbit from the single decided
representative (`orbit_of_rep_card_F13`). Distribution (numerics, exhaustive):
78 classes of card 1, 78 of card 2, 12 of card 4, zero class 4.

Everything is axiom-clean (`[propext, Classical.choice, Quot.sound]`, 0 sorry); parts 2's
constants are named hypotheses by design, with no instance claimed.
-/

namespace ClassChart

open Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The power-sum class fiber -/

/-- The window predicate is decidable. (Declared explicitly: the def-site instance search
wanders into `Fintype.decidableForallFintype` and fails; this is the direct route through
`Finset.decidableDforallFinset`, and it is kernel-reducible — `decide` works through it.) -/
instance psumPred_decidable (t : ℕ) (a : ℕ → F) :
    DecidablePred fun S : Finset F => ∀ j ∈ Finset.Icc 1 t, ∑ x ∈ S, x ^ j = a j :=
  fun _ => Finset.decidableDforallFinset

/-- The `(w, t)`-power-sum fiber over the domain `D₀`: weight-`w` supports whose first
`t` power sums hit the prescribed class parameters `a 1, …, a t`. -/
def psumFiber (D₀ : Finset F) (w t : ℕ) (a : ℕ → F) : Finset (Finset F) :=
  (D₀.powersetCard w).filter fun S => ∀ j ∈ Finset.Icc 1 t, ∑ x ∈ S, x ^ j = a j

lemma mem_psumFiber {D₀ : Finset F} {w t : ℕ} {a : ℕ → F} {S : Finset F} :
    S ∈ psumFiber D₀ w t a ↔
      S ⊆ D₀ ∧ S.card = w ∧ ∀ j ∈ Finset.Icc 1 t, ∑ x ∈ S, x ^ j = a j := by
  simp [psumFiber, Finset.mem_powersetCard, and_assoc]

/-- Pointwise weighted scaling of power sums: `p_j(λ·S) = λ^j · p_j(S)`.

Copied verbatim (with provenance) from `fiber_scaling` in
`ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean` (DISPROOF_LOG O56) — that
file has no `.olean`, so it cannot be imported here. -/
theorem fiber_scaling (S : Finset F) {l : F} (hl : l ≠ 0) (j : ℕ) :
    ∑ x ∈ S.image (l * ·), x ^ j = l ^ j * ∑ x ∈ S, x ^ j := by
  rw [Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ hl h), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_pow]

/-! ## Part 1 — the weighted-scaling fiber bijection, as a card equality -/

/-- **The weighted-scaling fiber bijection** (O51, set level): for `λ ≠ 0` the map
`S ↦ λ·S` carries the `(a₁, …, a_t)`-fiber over `D₀` bijectively onto the
`(λ·a₁, λ²·a₂, …, λ^t·a_t)`-fiber over `λ·D₀` — as a cardinality identity. Fiber size is
a weighted-projective orbit invariant of the class chart. -/
theorem psumFiber_scaling_card (D₀ : Finset F) {l : F} (hl : l ≠ 0) (w t : ℕ) (a : ℕ → F) :
    (psumFiber D₀ w t a).card
      = (psumFiber (D₀.image (l * ·)) w t fun j => l ^ j * a j).card := by
  refine Finset.card_bij (fun S _ => S.image (l * ·)) ?_ ?_ ?_
  · -- the scaled support lands in the scaled fiber
    intro S hS
    obtain ⟨hsub, hcard, hsum⟩ := mem_psumFiber.mp hS
    refine mem_psumFiber.mpr ⟨Finset.image_subset_image hsub,
      (Finset.card_image_of_injective S (mul_right_injective₀ hl)).trans hcard,
      fun j hj => ?_⟩
    rw [fiber_scaling S hl j, hsum j hj]
  · -- injectivity: scaling by a unit is injective on supports
    intro S _ T _ h
    exact Finset.image_injective (mul_right_injective₀ hl) h
  · -- surjectivity: descale by `λ⁻¹`
    intro T hT
    obtain ⟨hsub, hcard, hsum⟩ := mem_psumFiber.mp hT
    have hinv : l⁻¹ ≠ 0 := inv_ne_zero hl
    refine ⟨T.image (l⁻¹ * ·), mem_psumFiber.mpr ⟨?_, ?_, fun j hj => ?_⟩, ?_⟩
    · -- the descaled support lies in `D₀`
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (hsub hx)
      rwa [inv_mul_cancel_left₀ hl]
    · exact (Finset.card_image_of_injective T (mul_right_injective₀ hinv)).trans hcard
    · -- its power sums hit the original class parameters
      rw [fiber_scaling T hinv j, hsum j hj, inv_pow, ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero j hl), one_mul]
    · -- rescaling recovers `T`
      show (T.image (l⁻¹ * ·)).image (l * ·) = T
      rw [Finset.image_image]
      have hcomp : ((l * ·) ∘ (l⁻¹ * ·)) = (id : F → F) :=
        funext fun x => mul_inv_cancel_left₀ hl x
      rw [hcomp, Finset.image_id]

/-- **The orbit theorem on scaling-invariant domains** (`μ_n`, `F_q^×`, all of `F_q`):
fibers over weighted-projectively equivalent class parameters have equal cardinality. -/
theorem psumFiber_orbit_card {D₀ : Finset F} {l : F} (hl : l ≠ 0)
    (hD : D₀.image (l * ·) = D₀) (w t : ℕ) (a : ℕ → F) :
    (psumFiber D₀ w t fun j => l ^ j * a j).card = (psumFiber D₀ w t a).card := by
  conv_rhs => rw [psumFiber_scaling_card D₀ hl w t a]
  rw [hD]

/-- The zero class is a fixed point of the weighted scaling action: on a
scaling-invariant domain, `S ↦ λ·S` maps the zero fiber into itself (consistent with the
zero fiber being the extremal class, O51 probe). -/
theorem zero_fiber_scaling_mem {D₀ : Finset F} {l : F} (hl : l ≠ 0)
    (hD : D₀.image (l * ·) = D₀) {w t : ℕ} {S : Finset F}
    (hS : S ∈ psumFiber D₀ w t 0) : S.image (l * ·) ∈ psumFiber D₀ w t 0 := by
  obtain ⟨hsub, hcard, hsum⟩ := mem_psumFiber.mp hS
  refine mem_psumFiber.mpr ⟨?_, ?_, fun j hj => ?_⟩
  · rw [← hD]; exact Finset.image_subset_image hsub
  · exact (Finset.card_image_of_injective S (mul_right_injective₀ hl)).trans hcard
  · rw [fiber_scaling S hl j, hsum j hj]
    simp

omit [DecidableEq F] in
/-- Nonzero class parameters stay nonzero along the weighted scaling action: the orbit
structure respects the zero/nonzero chart decomposition. -/
lemma scaled_params_nonzero {l : F} (hl : l ≠ 0) {t : ℕ} {a : ℕ → F}
    (ha : ∃ j ∈ Finset.Icc 1 t, a j ≠ 0) :
    ∃ j ∈ Finset.Icc 1 t, l ^ j * a j ≠ 0 := by
  obtain ⟨j, hj, hja⟩ := ha
  exact ⟨j, hj, mul_ne_zero (pow_ne_zero j hl) hja⟩

/-- **Transversal reduction**: a fiber-cardinality bound certified at one orbit
representative holds on the whole weighted-projective orbit. Uniform class-chart bounds
(part 2) need only be verified on a transversal. -/
theorem psumFiber_card_le_of_orbit_rep {D₀ : Finset F} {l : F} (hl : l ≠ 0)
    (hD : D₀.image (l * ·) = D₀) {w t : ℕ} {a : ℕ → F} {K : ℕ}
    (hK : (psumFiber D₀ w t a).card ≤ K) :
    (psumFiber D₀ w t fun j => l ^ j * a j).card ≤ K := by
  rw [psumFiber_orbit_card hl hD w t a]
  exact hK

/-! ## Part 2 — the conditional Aliev–Smyth uniform bound

`IsCosetFam` is the structural predicate ("`S` lies in a positive-dimensional torsion
coset family of the fiber variety" — concretely: `S` contains a union of nontrivial
`μ_d`-cosets, the shape classified by the tower theory). The two named hypotheses
package, respectively, Aliev–Smyth Thm 1.1 (arXiv:0704.1747) applied to the isolated
torsion points of `V(p₁ − a₁, …, p_t − a_t) ⊆ 𝔾_m^w`, and the per-coset tower count
(O46–O50). Neither is claimed here; the decomposition theorem is what is proved. -/

section AlievSmyth

variable {IsCosetFam : Finset F → Prop} [DecidablePred IsCosetFam]

/-- **Named hypothesis (Aliev–Smyth, Thm 1.1 of arXiv:0704.1747)**: the *isolated* part
of every nonzero-class fiber — members outside all positive-dimensional torsion coset
families — has cardinality at most `C`, uniformly in the class parameters. A–S give this
with the explicit field-independent constant `C = c₁(w)·d^{c₂(w)}` for the fiber variety;
the constant stays abstract here. -/
def ASIsolatedBound (D₀ : Finset F) (w t : ℕ) (IsCosetFam : Finset F → Prop)
    [DecidablePred IsCosetFam] (C : ℕ) : Prop :=
  ∀ a : ℕ → F, (∃ j ∈ Finset.Icc 1 t, a j ≠ 0) →
    ((psumFiber D₀ w t a).filter fun S => ¬ IsCosetFam S).card ≤ C

/-- **Named hypothesis (per-coset tower count, O46–O50)**: the coset-family part of every
nonzero-class fiber has cardinality at most `B` (on 2-power-torsion domains the tower
machinery gives `B = 2^{O(1/η)}` componentwise). -/
def CosetFamilyBound (D₀ : Finset F) (w t : ℕ) (IsCosetFam : Finset F → Prop)
    [DecidablePred IsCosetFam] (B : ℕ) : Prop :=
  ∀ a : ℕ → F, (∃ j ∈ Finset.Icc 1 t, a j ≠ 0) →
    ((psumFiber D₀ w t a).filter fun S => IsCosetFam S).card ≤ B

/-- **The conditional uniform class-chart bound** (O51 program, decomposition step):
under the named Aliev–Smyth isolated bound and the coset-family count, *every*
nonzero-class fiber has cardinality at most `C + B` — uniformly over the whole nonzero
chart. The fiber splits exactly into its coset-family and isolated parts. -/
theorem nonzero_fiber_card_le {D₀ : Finset F} {w t : ℕ} {C B : ℕ}
    (hAS : ASIsolatedBound D₀ w t IsCosetFam C)
    (hCoset : CosetFamilyBound D₀ w t IsCosetFam B)
    {a : ℕ → F} (ha : ∃ j ∈ Finset.Icc 1 t, a j ≠ 0) :
    (psumFiber D₀ w t a).card ≤ C + B := by
  have key : (psumFiber D₀ w t a).card
      = ((psumFiber D₀ w t a).filter fun S => IsCosetFam S).card
        + ((psumFiber D₀ w t a).filter fun S => ¬ IsCosetFam S).card :=
    (Finset.card_filter_add_card_filter_not (s := psumFiber D₀ w t a)
      fun S => IsCosetFam S).symm
  rw [key, add_comm]
  exact add_le_add (hAS a ha) (hCoset a ha)

/-- The orbit-transversal form: on a scaling-invariant domain the conditional bound at a
class transfers verbatim to its entire weighted-projective orbit (weld of parts 1+2). -/
theorem nonzero_fiber_card_le_orbit {D₀ : Finset F} {w t : ℕ} {C B : ℕ}
    (hAS : ASIsolatedBound D₀ w t IsCosetFam C)
    (hCoset : CosetFamilyBound D₀ w t IsCosetFam B)
    {a : ℕ → F} (ha : ∃ j ∈ Finset.Icc 1 t, a j ≠ 0)
    {l : F} (hl : l ≠ 0) (hD : D₀.image (l * ·) = D₀) :
    (psumFiber D₀ w t fun j => l ^ j * a j).card ≤ C + B :=
  psumFiber_card_le_of_orbit_rep hl hD (nonzero_fiber_card_le hAS hCoset ha)

end AlievSmyth

/-! ## Part 3 — kernel-checked instance: `ZMod 13`, `w = 3`, `t = 2`

The honest small-scale picture (exhaustive): the strict O51-probe dichotomy ("every
nonzero class `≤ 2`") FAILS here — twelve nonzero classes have fiber card `4`, tying the
zero class — but those twelve are exactly ONE weighted-projective orbit (the orbit of
`(p₁, p₂) = (5, 4)`), every off-orbit nonzero class has card `≤ 2`, and the part-1 orbit
theorem pins the whole orbit from one decided representative. -/

section KernelInstance

/-- The zero-class fiber of 3-subsets of `F₁₃` at window `t = 2` has exactly `4`
members — the power-sum form of `zero_fiber_instance` (TopDirectionLineCount.lean),
matching through Newton at `char ≠ 2, 3`. Kernel-checked. -/
theorem zero_psum_fiber_F13 :
    (psumFiber (Finset.univ : Finset (ZMod 13)) 3 2 0).card = 4 := by
  decide

set_option maxHeartbeats 4000000 in
/-- Every nonzero class of `F₁₃` 3-subsets at window `t = 2` has fiber card `≤ 4` — the
zero class is *among* the maxima but (at this small scale, unlike the O51 probe) not
strictly above all nonzero classes. Kernel-checked over all 168 nonzero classes. -/
theorem nonzero_fiber_card_le_four_F13 :
    ∀ a₁ a₂ : ZMod 13, (a₁ ≠ 0 ∨ a₂ ≠ 0) →
      (psumFiber (Finset.univ : Finset (ZMod 13)) 3 2
        fun j => if j = 1 then a₁ else a₂).card ≤ 4 := by
  decide

set_option maxHeartbeats 4000000 in
/-- **The maximal nonzero classes are a single weighted-projective orbit**: every
nonzero class of `F₁₃` 3-subsets either has fiber card `≤ 2` (the O51-probe behaviour)
or lies on the weighted orbit `{(5λ, 4λ²) : λ ≠ 0}` of the representative
`(p₁, p₂) = (5, 4)`. Fiber cardinality really is an orbit invariant of the chart, with
exactly one exceptional nonzero orbit at this scale. Kernel-checked. -/
theorem nonzero_fiber_le_two_or_rep_orbit_F13 :
    ∀ a₁ a₂ : ZMod 13, (a₁ ≠ 0 ∨ a₂ ≠ 0) →
      (psumFiber (Finset.univ : Finset (ZMod 13)) 3 2
        fun j => if j = 1 then a₁ else a₂).card ≤ 2 ∨
      ∃ l : ZMod 13, l ≠ 0 ∧ a₁ = 5 * l ∧ a₂ = 4 * l ^ 2 := by
  decide

/-- The part-1 orbit theorem in action: deciding the single representative `(5, 4)`
(fiber card `4`) pins the fiber card of its *entire* weighted-projective orbit — no
further kernel enumeration. -/
theorem orbit_of_rep_card_F13 {l : ZMod 13} (hl : l ≠ 0) :
    (psumFiber (Finset.univ : Finset (ZMod 13)) 3 2
      fun j => l ^ j * (if j = 1 then 5 else 4)).card = 4 := by
  have hrep : (psumFiber (Finset.univ : Finset (ZMod 13)) 3 2
      fun j => if j = 1 then 5 else 4).card = 4 := by decide
  have hD : (Finset.univ : Finset (ZMod 13)).image (l * ·) = Finset.univ :=
    Finset.image_univ_of_surjective fun y => ⟨l⁻¹ * y, mul_inv_cancel_left₀ hl y⟩
  exact (psumFiber_orbit_card hl hD 3 2 fun j => if j = 1 then 5 else 4).trans hrep

end KernelInstance

end ClassChart
