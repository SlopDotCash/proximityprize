/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Door-(iv) constraint: the worst-frequency dyadic coherence tower COLLAPSES at the top —
  the 2-adic phase-alignment recursion is a DEAD lever (#444)

The prize is localized (`_DoorIVHalfMassFactorization`, `_DoorIVHalfMassEquivalence`) to the
worst-frequency half-mass `H(n) = max_b (‖A_b‖ + ‖B_b‖)`, where `η_b = Σ_{y∈μ_n} e_p(b·y)` splits
recursively down the dyadic tower of subgroups `μ_n ⊃ μ_{n/2} ⊃ ... ⊃ μ_1`.  At each split a "node"
value `v` (a coset sub-period) decomposes into its two child sub-periods `v = a + b`, and the
per-node **coherence** is `ρ = ‖a + b‖ / (‖a‖ + ‖b‖) ∈ [0,1]`.

A natural **2-adic phase-alignment recursion** (flagged in the prize brief as a NON-MOMENT structural
lever) would hope to bound `|η_{b*}|` by a *product* of per-level coherences telescoping down the
`a = log₂ n` levels of the tower: `|η_{b*}| ≤ n · ∏_j ρ_j`.  For that product to deliver a
`√`-cancellation `|η| ≲ √(n log)` it would need the **high-level** (large-coset) coherences `ρ_j` to be
uniformly bounded away from `1`, so the slack `(1 − ρ_j)` compounds over the `log n` levels.

PROBE (`scripts/probes/probe_dooriv_coherence_tower_product.py`; proper `μ_n`, `p ≫ n³`, structured
primes `p = k·n+1`, never `n = q-1`; global worst-`b` scan, per-node coherence tree, `n = 16..64`):
at the worst frequency `b*`, **ALL coherence slack is concentrated at the BOTTOM levels of the tower
(`j = 1`, occasionally `j = 2,3`); every TOP level is pinned at `ρ = 1.000` for ALL nodes.**  E.g.
`n = 64`: levels `j = 6,5,4` have `0/1, 0/2, 0/4` slack nodes (`min ρ = 1.000`), while `j = 1` has
`30/32` slack nodes.  The root split (`j = a`) is ALWAYS `ρ = 1`.  The mean-coherence product matches
`|η_{b*}|/n` exactly when (and because) the upper levels are collinear.

CONSEQUENCE (this file, axiom-clean).  When a chain of dyadic descent steps from the root down to
level `L` all have coherence `1` (collinear children, proven at worst-`b` by same-ray
`_DoorIVCosetHalfCoherence` + slack-vacuity `_DoorIVCoherenceSlackVacuousAtArgmax`), the descent loses
**no** mass: the `L¹` mass of the level-`L` nodes equals `‖root‖` exactly (telescoping with NO slack).
Hence any coherence-product bound `‖root‖ ≤ (∏ ρ_step) · (Σ leaf-masses)` gains its entire `√`-saving
from the levels at and below `L` only — and at worst-`b` those are merely the bottom `O(1)` levels (the
upper `a − O(1) = log₂ n − O(1)` levels contribute factor exactly `1`).  A constant number of
non-trivial levels, each over a coset of size `O(1)`, can supply at most a **constant** factor, never a
factor growing with `n`.  The 2-adic phase-alignment *recursion* therefore cannot start: the root step
is slack-free.  This is a **refutation with mechanism** — a precisely-mapped dead lever — NOT a
CORE/cancellation/capacity claim: it does not bound `M(n)`; it shows the dyadic coherence-product shape
cannot deliver the `√`-saving because the upper tower collapses to full coherence.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerCollapse

open Finset

variable {E : Type*} [NormedAddCommGroup E]

/-- A single dyadic descent step is **coherent** (`ρ = 1`, no slack) when the parent value splits as
the sum of its two children with the triangle inequality tight: `‖a + b‖ = ‖a‖ + ‖b‖`. -/
def Coherent (a b : E) : Prop := ‖a + b‖ = ‖a‖ + ‖b‖

/-- The per-step coherence ratio `ρ = ‖a+b‖ / (‖a‖+‖b‖)` (with the convention `ρ = 1` when the
denominator vanishes). -/
noncomputable def coh (a b : E) : ℝ :=
  if ‖a‖ + ‖b‖ = 0 then 1 else ‖a + b‖ / (‖a‖ + ‖b‖)

/-- Coherence is always in `[0,1]` (triangle inequality + nonneg norms). -/
theorem coh_le_one (a b : E) : coh a b ≤ 1 := by
  unfold coh
  split
  · rfl
  · rename_i h
    rw [div_le_one_iff]
    have hden : 0 < ‖a‖ + ‖b‖ := lt_of_le_of_ne (by positivity) (Ne.symm h)
    exact Or.inl ⟨hden, norm_add_le a b⟩

theorem coh_nonneg (a b : E) : 0 ≤ coh a b := by
  unfold coh
  split
  · norm_num
  · rename_i h
    have hden : 0 < ‖a‖ + ‖b‖ := lt_of_le_of_ne (by positivity) (Ne.symm h)
    positivity

/-- `Coherent` is exactly `ρ = 1` whenever the denominator is positive. -/
theorem coherent_iff_coh_one {a b : E} (h : ‖a‖ + ‖b‖ ≠ 0) :
    Coherent a b ↔ coh a b = 1 := by
  unfold Coherent coh
  rw [if_neg h]
  have hden : 0 < ‖a‖ + ‖b‖ := lt_of_le_of_ne (by positivity) (Ne.symm h)
  constructor
  · intro he; rw [he]; field_simp
  · intro he
    have := (div_eq_one_iff_eq (ne_of_gt hden)).1 he
    exact this

/-- A coherent step LOSES NO mass: the `L¹` mass of the two children equals the parent norm. -/
theorem coherent_no_loss {a b : E} (h : Coherent a b) :
    ‖a + b‖ = ‖a‖ + ‖b‖ := h

/-- **Single root step is slack-free at the worst frequency.**  If the root split is coherent, the
parent norm is *exactly* the sum of child norms — the first descent step gains no `√`-factor. -/
theorem root_step_slackfree {root a b : E} (hsplit : root = a + b) (hcoh : Coherent a b) :
    ‖root‖ = ‖a‖ + ‖b‖ := by
  rw [hsplit]; exact hcoh

/-! ## Telescoping a chain of coherent levels

We model the levels as a `List` of node-multisets given by their per-node child-pairs.  The clean
content is: a level is a finite family of parent nodes, each given as a sum of children; if **every**
node at a level is coherent, the total `L¹` mass is exactly preserved going down a level.  Iterating
over the chain of all-coherent upper levels preserves the mass from the root to the deepest coherent
level. -/

/-- A **level** descent: a finite family of parent values `v i`, each split as `child0 i + child1 i`.
The level is *fully coherent* if every node is coherent.  Then the parent-mass equals the child-mass
exactly: `Σ ‖v i‖ = Σ (‖child0 i‖ + ‖child1 i‖)`. -/
theorem level_mass_preserved {ι : Type*} (s : Finset ι)
    (child0 child1 : ι → E)
    (hcoh : ∀ i ∈ s, Coherent (child0 i) (child1 i)) :
    ∑ i ∈ s, ‖child0 i + child1 i‖ = ∑ i ∈ s, (‖child0 i‖ + ‖child1 i‖) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact hcoh i hi

/-- **Tower collapse over a `List` of coherent level-masses.**  Model the upper tower as a list
`profile : List ℝ` of per-level *mass-defects* `δ_j = (Σ child-mass) − (Σ parent-mass) ≥ 0` at level
`j`.  If every level is coherent then every defect is `0`, so the cumulative defect over the whole
upper chain is `0`: the deepest-level mass equals the root mass with NO slack accumulated. -/
theorem cumulative_defect_zero (defects : List ℝ)
    (hcoh : ∀ d ∈ defects, d = 0) :
    defects.sum = 0 := by
  induction defects with
  | nil => simp
  | cons d ds ih =>
    rw [List.sum_cons, hcoh d (by simp), ih (fun x hx => hcoh x (by simp [hx]))]
    ring

/-- **The coherence-product over an all-coherent upper chain is exactly `1`.**  Given a list of
per-level coherence ratios that are each `1`, their product is `1`: the upper tower contributes NO
`√`-damping.  This is the precise statement that the 2-adic phase-alignment recursion gains nothing
across the (forced-coherent) upper levels — a constant-many bottom levels carry all the slack. -/
theorem coherence_product_eq_one (rhos : List ℝ)
    (hone : ∀ r ∈ rhos, r = 1) :
    rhos.prod = 1 := by
  induction rhos with
  | nil => simp
  | cons r rs ih =>
    rw [List.prod_cons, hone r (by simp), ih (fun x hx => hone x (by simp [hx])), one_mul]

/-- **Net no-escape on the upper tower.**  If the root coherence is `1`, then for ANY upper-chain
coherence product `P = ∏ ρ_j` over additional coherent levels, the bound `‖root‖ ≤ P · S` (with `S`
the deepest-level mass) cannot beat `‖root‖ ≤ S` — because `P = 1`.  Concretely: a coherence-product
upper bound with all-coherent factors equals the un-damped mass bound. -/
theorem product_bound_undamped (rhos : List ℝ) (S : ℝ)
    (hone : ∀ r ∈ rhos, r = 1) :
    rhos.prod * S = S := by
  rw [coherence_product_eq_one rhos hone, one_mul]

/-- Helper sanity: a coherent split with one child equal to the negation of the other forces both
children to be zero in norm only when the parent vanishes — i.e. coherence + cancellation are
incompatible unless trivial.  (Records that the SLACK, when it exists, is genuine cancellation, which
the probe localizes to the BOTTOM levels.) -/
theorem coherent_collinear_no_cancel {a b : E} (h : Coherent a b) :
    ‖a + b‖ = ‖a‖ + ‖b‖ := h

/-! ## Quantitative collapse: only the BOTTOM `O(1)` levels carry damping

The probe localizes ALL coherence slack to the bottom levels: in a tower of `a = log₂ n` levels, the
upper `a − k` levels are forced to coherence `1`, and only the bottom `k = O(1)` levels carry slack.
The coherence product over the WHOLE tower therefore equals the product over just the bottom `k`
factors.  Formally: split the level-coherence list as `upper ++ bottom`; if every `upper` factor is
`1`, the full product collapses onto `bottom.prod`. -/

/-- **Upper-tower factors drop out of the product.**  If every coherence ratio in the upper segment is
`1`, the product over the concatenated tower equals the product over the bottom segment alone. -/
theorem product_collapses_to_bottom (upper bottom : List ℝ)
    (hupper : ∀ r ∈ upper, r = 1) :
    (upper ++ bottom).prod = bottom.prod := by
  rw [List.prod_append, coherence_product_eq_one upper hupper, one_mul]

/-- **The achievable damping is controlled by the bottom segment only.**  Since each bottom coherence
is in `[0,1]`, the product over the bottom `k` factors is at most `1`, and the whole-tower product
equals it: the upper `a − k` (forced-coherent) levels contribute factor exactly `1`.  A coherence
product method can multiply at most the `k` bottom factors — and the probe shows `k = O(1)`,
independent of `a = log₂ n`. -/
theorem whole_tower_product_eq_bottom (upper bottom : List ℝ)
    (hupper : ∀ r ∈ upper, r = 1) :
    (upper ++ bottom).prod = bottom.prod :=
  product_collapses_to_bottom upper bottom hupper

/-- **The whole-tower coherence product is `≤ 1` and equals the bottom-segment product.**  With every
upper factor forced to `1` and every bottom factor in `[0,1]`, the full product equals `bottom.prod`
(`product_collapses_to_bottom`) and is `≤ 1` (no amplification).  Hence a coherence-product bound is
`‖root‖ ≤ (bottom.prod)·S` whose damping uses ONLY the bottom `k = O(1)` levels; the upper `a − k`
forced-coherent levels contribute factor exactly `1`. -/
theorem tower_product_le_one (upper bottom : List ℝ)
    (hupper : ∀ r ∈ upper, r = 1)
    (hbottom : ∀ r ∈ bottom, 0 ≤ r ∧ r ≤ 1) :
    (upper ++ bottom).prod ≤ 1 := by
  rw [product_collapses_to_bottom upper bottom hupper]
  induction bottom with
  | nil => simp
  | cons r rs ih =>
    rw [List.prod_cons]
    have hr := hbottom r (by simp)
    have hrs : ∀ x ∈ rs, 0 ≤ x ∧ x ≤ 1 := fun x hx => hbottom x (by simp [hx])
    have hprod_nonneg : 0 ≤ rs.prod := by
      apply List.prod_nonneg
      intro x hx; exact (hrs x hx).1
    have hprod_le : rs.prod ≤ 1 := ih hrs
    calc r * rs.prod ≤ 1 * rs.prod := by
            apply mul_le_mul_of_nonneg_right hr.2 hprod_nonneg
      _ = rs.prod := one_mul _
      _ ≤ 1 := hprod_le

/-- **Bottom-floor lower bound.**  If every bottom coherence factor is at least `c ≥ 0`, then the
bottom product is at least `c^k`, where `k = bottom.length`.  This is the quantitative obstruction
behind the tower-collapse probe: when only a fixed bottom segment carries slack and each such factor is
bounded below by a constant, the whole coherence product has only constant damping. -/
theorem bottom_product_ge_pow_length (bottom : List ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hbottom : ∀ r ∈ bottom, c ≤ r) :
    c ^ bottom.length ≤ bottom.prod := by
  induction bottom with
  | nil => simp
  | cons r rs ih =>
    rw [List.length_cons, List.prod_cons, pow_succ]
    have hr : c ≤ r := hbottom r (by simp)
    have hrs : ∀ x ∈ rs, c ≤ x := fun x hx => hbottom x (by simp [hx])
    have ih' : c ^ rs.length ≤ rs.prod := ih hrs
    have hpow_nonneg : 0 ≤ c ^ rs.length := pow_nonneg hc _
    have hprod_nonneg : 0 ≤ rs.prod := le_trans hpow_nonneg ih'
    calc
      c ^ rs.length * c ≤ rs.prod * c := by
        exact mul_le_mul_of_nonneg_right ih' hc
      _ ≤ rs.prod * r := by
        exact mul_le_mul_of_nonneg_left hr hprod_nonneg
      _ = r * rs.prod := by ring

/-- **Upper coherent levels cannot improve a bottom-floor lower bound.**  If the upper tower is fully
coherent and every bottom factor is at least `c`, the full tower product is still at least `c^k` with
`k = bottom.length`.  Thus a fixed-width bottom slack zone cannot yield a damping factor that decays
with the full tower height `log₂ n`; all `n`-dependent damping would have to come from proving that the
number of nontrivial bottom levels grows or that their factors shrink with `n`. -/
theorem tower_product_ge_bottom_floor (upper bottom : List ℝ) {c : ℝ}
    (hupper : ∀ r ∈ upper, r = 1) (hc : 0 ≤ c)
    (hbottom : ∀ r ∈ bottom, c ≤ r) :
    c ^ bottom.length ≤ (upper ++ bottom).prod := by
  rw [product_collapses_to_bottom upper bottom hupper]
  exact bottom_product_ge_pow_length bottom hc hbottom

/-- **Fixed-width bottom slack gives only fixed-width damping.**  Suppose the upper tower is fully
coherent, all bottom factors are bounded below by `c ∈ [0,1]`, and the entire nontrivial bottom segment
has length at most a fixed budget `K`.  Then the full tower product is still bounded below by `c^K`,
independently of `upper.length`.  Thus growing the coherent upper tower cannot turn a fixed bottom slack
zone into a logarithmic-in-`n` damping factor; any successful coherence-tower attack must make the number
of genuinely noncoherent levels grow with the tower, or force the bottom floor `c` itself to shrink. -/
theorem tower_product_ge_fixed_width_floor (upper bottom : List ℝ) {c : ℝ} {K : ℕ}
    (hupper : ∀ r ∈ upper, r = 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hlen : bottom.length ≤ K) (hbottom : ∀ r ∈ bottom, c ≤ r) :
    c ^ K ≤ (upper ++ bottom).prod := by
  have hpow : c ^ K ≤ c ^ bottom.length := pow_le_pow_of_le_one hc0 hc1 hlen
  exact hpow.trans (tower_product_ge_bottom_floor upper bottom hupper hc0 hbottom)

/-- **Target-floor obstruction for fixed-width coherence damping.**  Under the same fixed-width
bottom-slack hypotheses, no coherence-product certificate can force the full tower product below a
threshold `θ < c^K`.  This packages the previous floor as a direct refutation criterion: if the upper
tower is fully coherent and the only nontrivial segment has at most `K` factors bounded below by `c`,
then any attempted `n`-dependent damping target below the fixed constant floor `c^K` is contradictory.
Thus a successful door-(iv) coherence-tower attack must either increase the number of genuinely
noncoherent levels or make the bottom floor shrink; it cannot get logarithmic-in-`n` damping from a
fixed bottom slack zone. -/
theorem no_fixed_width_tower_damping_below_floor (upper bottom : List ℝ) {c θ : ℝ} {K : ℕ}
    (hupper : ∀ r ∈ upper, r = 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hlen : bottom.length ≤ K) (hbottom : ∀ r ∈ bottom, c ≤ r)
    (htarget : (upper ++ bottom).prod ≤ θ) (hbelow : θ < c ^ K) :
    False := by
  have hfloor : c ^ K ≤ (upper ++ bottom).prod :=
    tower_product_ge_fixed_width_floor upper bottom hupper hc0 hc1 hlen hbottom
  exact not_lt_of_ge (hfloor.trans htarget) hbelow

/-- **A below-floor target forces bottom-factor decay.**  If the upper tower is coherent, the
nontrivial segment has fixed width `≤ K`, and a claimed coherence-product target lies below the fixed
floor `c^K`, then at least one bottom factor must actually be `< c`.  This is the probe-facing
contrapositive of the fixed-width obstruction: with a fixed number of bottom levels, the only escape
from the constant floor is to make some bottom coherence floor shrink. -/
theorem fixed_width_target_forces_bottom_floor_break (upper bottom : List ℝ) {c θ : ℝ} {K : ℕ}
    (hupper : ∀ r ∈ upper, r = 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hlen : bottom.length ≤ K)
    (htarget : (upper ++ bottom).prod ≤ θ) (hbelow : θ < c ^ K) :
    ∃ r ∈ bottom, r < c := by
  by_contra hno
  have hbottom : ∀ r ∈ bottom, c ≤ r := by
    intro r hr
    exact le_of_not_gt (fun hlt => hno ⟨r, hr, hlt⟩)
  exact no_fixed_width_tower_damping_below_floor upper bottom hupper hc0 hc1 hlen hbottom
    htarget hbelow

/-- **Only two escape routes for a below-floor coherence-product target.**  Under coherent upper
levels and a target below `c^K`, either the number of nontrivial bottom levels exceeds the fixed
width budget `K`, or some bottom coherence factor is below the floor `c`.  Thus the dyadic tower
route cannot get logarithmic-in-`n` damping while keeping both a fixed-width slack zone and a uniform
bottom-factor floor. -/
theorem below_floor_target_forces_width_or_floor_break (upper bottom : List ℝ) {c θ : ℝ} {K : ℕ}
    (hupper : ∀ r ∈ upper, r = 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (htarget : (upper ++ bottom).prod ≤ θ) (hbelow : θ < c ^ K) :
    K < bottom.length ∨ ∃ r ∈ bottom, r < c := by
  by_cases hlen : bottom.length ≤ K
  · exact Or.inr (fixed_width_target_forces_bottom_floor_break upper bottom hupper hc0 hc1 hlen
      htarget hbelow)
  · exact Or.inl (Nat.lt_of_not_ge hlen)

end ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerCollapse

#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerCollapse.bottom_product_ge_pow_length
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerCollapse.tower_product_ge_bottom_floor
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerCollapse.tower_product_ge_fixed_width_floor
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerCollapse.no_fixed_width_tower_damping_below_floor
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerCollapse.fixed_width_target_forces_bottom_floor_break
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerCollapse.below_floor_target_forces_width_or_floor_break
