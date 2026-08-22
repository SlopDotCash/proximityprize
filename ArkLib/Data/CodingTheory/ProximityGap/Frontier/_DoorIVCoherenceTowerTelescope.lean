/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Door-(iv): the dyadic coherence tower telescopes EXACTLY to root = (∏ coherences)·leafMass (#444)

The prize is localized (`_DoorIVHalfMassFactorization`) to the worst-frequency period
`η_b = Σ_{y∈μ_n} e_p(b·y)`, which splits recursively down the `a = log₂ n` levels of the dyadic
subgroup tower `μ_n ⊃ μ_{n/2} ⊃ … ⊃ μ_1`.  At each level the total `L¹` mass of the nodes is some
`M_j ≥ 0`, with `M_0 = ‖η_b‖` (one root block) and `M_a = Σ_{leaves} 1 = n` (the leaf masses are the
`n` unit phases).  The per-level **coherence ratio** is `ρ_j = M_j / M_{j+1} ∈ [0,1]` (each parent
mass is at most the child half-mass, by the triangle inequality `‖A+B‖ ≤ ‖A‖+‖B‖`).

The companion refutation file `_DoorIVCoherenceTowerCollapse` proves that, at the worst `b`, this
coherence product is bounded BELOW by a fixed-width constant (`c^K`), so the tower-product shape cannot
supply a `√`-saving — a precisely-mapped DEAD lever.  But that file only ever USES the product-bound
shape `‖root‖ ≤ (∏ ρ_step)·(Σ leaf-masses)` as prose; the **exact algebraic identity** that licenses
relocating the prize onto the product is not itself recorded anywhere.  This file supplies exactly that
missing reduction rung, kernel-clean:

* `coherenceProduct_mul_getLast`: for any chain of POSITIVE masses, the product of consecutive
  `parent/child` ratios times the last mass equals the first mass — `(∏_j M_j/M_{j+1})·M_last = M_first`.
  This is the load-bearing telescope behind "the prize size = (∏ coherences) × leaf-mass-sum", confirmed
  to machine precision by `probe_dooriv_coherence_tower_product.py` (residual `~1e-16`).
* `root_eq_coherenceProduct_mul_leaf`: the door-(iv)-facing restatement — root mass equals the
  coherence-product times the leaf mass.
* `coherenceProduct_eq_root_div_leaf`: the coherence product is EXACTLY `root/leaf` (e.g. at the prize
  worst-`b`, `‖η_{b*}‖ / n`), so a `√`-saving REQUIRES the product `≤ 1/√n` — there is no other lever
  inside the tower than driving this product down, which `_DoorIVCoherenceTowerCollapse` then shows the
  worst-`b` tower cannot do (upper levels pinned at ratio `1`).

Scope: pure ordered-field telescope algebra.  No CORE / cancellation / anti-concentration / moment /
completion / capacity claim — this is the faithful algebraic bridge that makes "the prize is the
coherence-tower product times the leaf mass" a kernel-checked identity rather than a prose assertion.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope

/-- The list of consecutive `parent/child` coherence ratios along a mass chain.  For a head (parent)
mass `a` and a tail beginning with the child mass `b`, the first ratio is `a / b` and the rest recurses
on the tail.  For `M = [M₀, M₁, …, M_a]` this is `[M₀/M₁, M₁/M₂, …, M_{a-1}/M_a]`; multiplying its
product by the LAST (leaf) mass `M_a` recovers the FIRST (root) mass `M₀` (the telescope below).
This is the `‖parent‖ / (‖left‖+‖right‖)` coherence orientation of `_DoorIVHalfMassFactorization`. -/
noncomputable def stepRatios : List ℝ → List ℝ
  | [] => []
  | [_] => []
  | a :: b :: t => (a / b) :: stepRatios (b :: t)

/-- The coherence-tower product is the product of all consecutive `parent/child` ratios. -/
noncomputable def coherenceProduct (M : List ℝ) : ℝ := (stepRatios M).prod

@[simp] theorem stepRatios_nil : stepRatios [] = [] := rfl

@[simp] theorem stepRatios_singleton (a : ℝ) : stepRatios [a] = [] := rfl

theorem stepRatios_cons_cons (a b : ℝ) (t : List ℝ) :
    stepRatios (a :: b :: t) = (a / b) :: stepRatios (b :: t) := rfl

@[simp] theorem coherenceProduct_singleton (a : ℝ) : coherenceProduct [a] = 1 := by
  simp [coherenceProduct]

/-- **The telescope identity.**  For any chain of POSITIVE masses `M = a :: t`, the product of the
consecutive ratios `∏ M_{j+1}/M_j`, multiplied by the LAST mass `M_a`, equals the FIRST mass `a`.
Every intermediate mass cancels, leaving only the endpoints.  This is the exact algebra behind
"root mass = (∏ coherences) × leaf mass". -/
theorem coherenceProduct_mul_getLast :
    ∀ (a : ℝ) (t : List ℝ), (∀ x ∈ a :: t, 0 < x) →
      coherenceProduct (a :: t) * (a :: t).getLast (by simp) = a := by
  intro a t
  induction t generalizing a with
  | nil =>
    intro _
    simp
  | cons b s ih =>
    intro hpos
    have ha : 0 < a := hpos a (by simp)
    have hb : 0 < b := hpos b (by simp)
    have hpos' : ∀ x ∈ b :: s, 0 < x := fun x hx => hpos x (by simp [hx])
    have hih := ih b hpos'
    have hlast : (a :: b :: s).getLast (by simp) = (b :: s).getLast (by simp) :=
      List.getLast_cons (by simp)
    have hcp : coherenceProduct (a :: b :: s) = (a / b) * coherenceProduct (b :: s) := by
      simp [coherenceProduct, stepRatios_cons_cons]
    rw [hcp, hlast]
    calc (a / b) * coherenceProduct (b :: s) * (b :: s).getLast (by simp)
        = (a / b) * (coherenceProduct (b :: s) * (b :: s).getLast (by simp)) := by ring
      _ = (a / b) * b := by rw [hih]
      _ = a := by field_simp

/-- **Root mass = coherence product × leaf mass** (door-(iv)-facing restatement).  For a positive mass
chain, the root (first) mass equals the coherence product times the leaf (last) mass.  Together with
`_DoorIVHalfMassFactorization`, this says the prize size `‖η_b‖` is exactly the coherence-tower product
times the leaf mass `n`. -/
theorem root_eq_coherenceProduct_mul_leaf (a : ℝ) (t : List ℝ)
    (hpos : ∀ x ∈ a :: t, 0 < x) :
    a = coherenceProduct (a :: t) * (a :: t).getLast (by simp) :=
  (coherenceProduct_mul_getLast a t hpos).symm

/-- **The coherence product is exactly root / leaf.**  Since the leaf mass is positive, the
coherence-tower product equals `M_first / M_last` — e.g. at the prize worst-`b`, `‖η_{b*}‖ / n`.  Hence
a `√`-saving `‖η‖ ≤ √(n·log)` forces the product `≤ √(log/n)`; the ONLY lever inside the tower is
driving this product down, which `_DoorIVCoherenceTowerCollapse` shows the worst-`b` tower cannot do. -/
theorem coherenceProduct_eq_root_div_leaf (a : ℝ) (t : List ℝ)
    (hpos : ∀ x ∈ a :: t, 0 < x) :
    coherenceProduct (a :: t) = a / (a :: t).getLast (by simp) := by
  have hlast_pos : 0 < (a :: t).getLast (by simp) :=
    hpos _ (List.getLast_mem (by simp))
  have h := coherenceProduct_mul_getLast a t hpos
  field_simp
  linarith [h]

/-- **Bound transfer to the coherence product.**  On a positive mass chain, any raw root-mass
certificate `M₀ ≤ B` is EXACTLY the same statement as the product certificate
`(∏ρ_j) ≤ B/M_leaf`.  This is the door-(iv) reduction interface: a prize-scale estimate for the
Gauss period can only enter the dyadic tower by proving the corresponding small product of level
coherences. -/
theorem root_le_bound_iff_coherenceProduct_le_bound_div_leaf (a B : ℝ) (t : List ℝ)
    (hpos : ∀ x ∈ a :: t, 0 < x) :
    a ≤ B ↔ coherenceProduct (a :: t) ≤ B / (a :: t).getLast (by simp) := by
  have hlast_pos : 0 < (a :: t).getLast (by simp) :=
    hpos _ (List.getLast_mem (by simp))
  rw [coherenceProduct_eq_root_div_leaf a t hpos]
  exact (div_le_div_iff_of_pos_right hlast_pos).symm

/-- Family form of the product-threshold interface.  A pointwise raw root bound along a family of
positive coherence towers is exactly the pointwise normalized product bound against `B i / leaf_i`.
This is the batch form consumed by asymptotic door-(iv) reductions: uniform control of the roots can
only enter this tower through uniform control of the products. -/
theorem rootFamily_le_bound_iff_coherenceProductFamily_le_bound_div_leaf {ι : Type*}
    (a B : ι → ℝ) (t : ι → List ℝ)
    (hpos : ∀ i, ∀ x ∈ a i :: t i, 0 < x) :
    (∀ i, a i ≤ B i) ↔
      ∀ i, coherenceProduct (a i :: t i) ≤ B i / (a i :: t i).getLast (by simp) := by
  constructor
  · intro h i
    exact (root_le_bound_iff_coherenceProduct_le_bound_div_leaf (a i) (B i) (t i) (hpos i)).mp
      (h i)
  · intro h i
    exact (root_le_bound_iff_coherenceProduct_le_bound_div_leaf (a i) (B i) (t i) (hpos i)).mpr
      (h i)

/-- Contrapositive product interface: if the coherence product stays above the target normalized
threshold `B/M_leaf`, then the root mass cannot satisfy the raw bound `B`.  This is the formal version
of the probe verdict: a tower whose product is bounded below by a fixed-width constant cannot by itself
supply a `√n` saving. -/
theorem not_root_le_bound_of_bound_div_leaf_lt_coherenceProduct (a B : ℝ) (t : List ℝ)
    (hpos : ∀ x ∈ a :: t, 0 < x)
    (hprod : B / (a :: t).getLast (by simp) < coherenceProduct (a :: t)) :
    ¬ a ≤ B := by
  intro hroot
  have hle := (root_le_bound_iff_coherenceProduct_le_bound_div_leaf a B t hpos).mp hroot
  linarith

/-- Family contrapositive: one tower whose coherence product exceeds its normalized target refutes the
corresponding pointwise raw family bound.  This packages the exact failure certificate probes report:
a single adversarial `b` with product above threshold is enough to kill the claimed family root cap. -/
theorem not_rootFamily_le_bound_of_exists_bound_div_leaf_lt_coherenceProduct {ι : Type*}
    (a B : ι → ℝ) (t : ι → List ℝ)
    (hpos : ∀ i, ∀ x ∈ a i :: t i, 0 < x)
    (hbad : ∃ i, B i / (a i :: t i).getLast (by simp) < coherenceProduct (a i :: t i)) :
    ¬ ∀ i, a i ≤ B i := by
  rintro hroot
  rcases hbad with ⟨i, hi⟩
  exact not_root_le_bound_of_bound_div_leaf_lt_coherenceProduct (a i) (B i) (t i) (hpos i) hi
    (hroot i)

/-- **Lower-product floor obstruction.**  If an external tower-collapse argument proves a product floor
`c ≤ ∏ρ_j`, then any advertised raw root bound `a ≤ B` must have normalized target at least that floor:
`c ≤ B/M_leaf`.  Equivalently, if `B/M_leaf < c`, the raw root bound is impossible.  This is the exact
consumer for `_DoorIVCoherenceTowerCollapse`: fixed-width bottom damping leaves a constant product floor,
so a target requiring a smaller product cannot be certified by the dyadic tower. -/
theorem not_root_le_bound_of_bound_div_leaf_lt_product_floor (a B c : ℝ) (t : List ℝ)
    (hpos : ∀ x ∈ a :: t, 0 < x)
    (hfloor : c ≤ coherenceProduct (a :: t))
    (htarget : B / (a :: t).getLast (by simp) < c) :
    ¬ a ≤ B := by
  exact not_root_le_bound_of_bound_div_leaf_lt_coherenceProduct a B t hpos
    (htarget.trans_le hfloor)

/-- Family version of the lower-product obstruction.  One tower with a product floor above its
normalized target refutes the corresponding pointwise family root bound. -/
theorem not_rootFamily_le_bound_of_exists_product_floor_above_target {ι : Type*}
    (a B floor : ι → ℝ) (t : ι → List ℝ)
    (hpos : ∀ i, ∀ x ∈ a i :: t i, 0 < x)
    (hbad : ∃ i,
      floor i ≤ coherenceProduct (a i :: t i) ∧
        B i / (a i :: t i).getLast (by simp) < floor i) :
    ¬ ∀ i, a i ≤ B i := by
  intro hroot
  rcases hbad with ⟨i, hfloor, htarget⟩
  exact not_root_le_bound_of_bound_div_leaf_lt_product_floor (a i) (B i) (floor i) (t i)
    (hpos i) hfloor htarget (hroot i)

/-- **Product floor transfers to a raw root floor.**  On a positive tower, a lower bound
`c ≤ ∏ρ_j` forces the raw root mass to be at least `c * M_leaf`.  This is the raw-scale form of the
fixed-width bottom-slack obstruction: a coherence product bounded below by a constant keeps the root at
least a constant fraction of the leaf mass. -/
theorem root_ge_product_floor_mul_leaf (a c : ℝ) (t : List ℝ)
    (hpos : ∀ x ∈ a :: t, 0 < x)
    (hfloor : c ≤ coherenceProduct (a :: t)) :
    c * (a :: t).getLast (by simp) ≤ a := by
  have hleaf_pos : 0 < (a :: t).getLast (by simp) :=
    hpos _ (List.getLast_mem (by simp))
  calc
    c * (a :: t).getLast (by simp)
        ≤ coherenceProduct (a :: t) * (a :: t).getLast (by simp) :=
          mul_le_mul_of_nonneg_right hfloor (le_of_lt hleaf_pos)
    _ = a := by rw [← root_eq_coherenceProduct_mul_leaf a t hpos]

/-- Raw-scale obstruction: if a proposed root cap `B` lies below the floor `c * M_leaf` forced by a
coherence-product lower bound, then the cap is impossible. -/
theorem not_root_le_bound_of_product_floor_mul_leaf_gt (a B c : ℝ) (t : List ℝ)
    (hpos : ∀ x ∈ a :: t, 0 < x)
    (hfloor : c ≤ coherenceProduct (a :: t))
    (hB : B < c * (a :: t).getLast (by simp)) :
    ¬ a ≤ B := by
  intro hroot
  have hroot_floor := root_ge_product_floor_mul_leaf a c t hpos hfloor
  exact (not_lt_of_ge (le_trans hroot_floor hroot)) hB

/-- Family raw-scale obstruction from one bad tower: a product floor whose raw leaf-scaled value exceeds
`B i` refutes the pointwise family cap. -/
theorem not_rootFamily_le_bound_of_exists_product_floor_mul_leaf_gt {ι : Type*}
    (a B floor : ι → ℝ) (t : ι → List ℝ)
    (hpos : ∀ i, ∀ x ∈ a i :: t i, 0 < x)
    (hbad : ∃ i,
      floor i ≤ coherenceProduct (a i :: t i) ∧
        B i < floor i * (a i :: t i).getLast (by simp)) :
    ¬ ∀ i, a i ≤ B i := by
  intro hroot
  rcases hbad with ⟨i, hfloor, hB⟩
  exact not_root_le_bound_of_product_floor_mul_leaf_gt (a i) (B i) (floor i) (t i)
    (hpos i) hfloor hB (hroot i)

/-- Each consecutive ratio in a coherence tower is nonneg when the masses are positive; this is the
sign discipline behind reading the ratios as coherences `∈ [0,1]` (the `≤ 1` half is the triangle
inequality, supplied by `_DoorIVHalfMassFactorization`). -/
theorem stepRatios_nonneg :
    ∀ (M : List ℝ), (∀ x ∈ M, 0 < x) → ∀ r ∈ stepRatios M, 0 ≤ r := by
  intro M
  induction M with
  | nil => intro _ r hr; simp [stepRatios] at hr
  | cons a t ih =>
    cases t with
    | nil => intro _ r hr; simp [stepRatios] at hr
    | cons b s =>
      intro hpos r hr
      have ha : 0 < a := hpos a (by simp)
      have hb : 0 < b := hpos b (by simp)
      have hpos' : ∀ x ∈ b :: s, 0 < x := fun x hx => hpos x (by simp [hx])
      rw [stepRatios_cons_cons, List.mem_cons] at hr
      rcases hr with hr | hr
      · rw [hr]; exact le_of_lt (div_pos ha hb)
      · exact ih hpos' r hr

end ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope

#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.coherenceProduct_mul_getLast
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.root_eq_coherenceProduct_mul_leaf
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.coherenceProduct_eq_root_div_leaf
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.root_le_bound_iff_coherenceProduct_le_bound_div_leaf
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.rootFamily_le_bound_iff_coherenceProductFamily_le_bound_div_leaf
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.not_root_le_bound_of_bound_div_leaf_lt_coherenceProduct
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.not_rootFamily_le_bound_of_exists_bound_div_leaf_lt_coherenceProduct
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.not_root_le_bound_of_bound_div_leaf_lt_product_floor
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.not_rootFamily_le_bound_of_exists_product_floor_above_target
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.root_ge_product_floor_mul_leaf
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.not_root_le_bound_of_product_floor_mul_leaf_gt
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.not_rootFamily_le_bound_of_exists_product_floor_mul_leaf_gt
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerTelescope.stepRatios_nonneg
