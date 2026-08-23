/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NovelAntiConcentration
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup

/-!
# `_DoorIVValueShiftHistogramObstruction`: the value-shift route needs a `+s`-periodic histogram (#444)

Door-(iv) Lane 3 constraint lemma. Extends `_NovelAntiConcentration`.

## Context

`_NovelAntiConcentration.charP_energy_of_shift` is the genuine `L^∞` anti-concentration mechanism
that ESCAPES the moment obstruction: IF the value map `val : T → ZMod p` admits a `ValueShift` of
additive step-order `m`, THEN the wraparound fiber is `≤ #T / m`, which at `m ≈ p` is the
prize-strength bound. Its docstring isolates the SINGLE open input as:

> "does the shift action have a large free part for `μ_n`'s value map?"

This file LOCKS that input as a constraint. It records the exact obligation a value-shift imposes —
**the fiber-cardinality histogram `a ↦ fiberCard val a` must be invariant under `+s`** — and the
contrapositive obstruction: a single pair of residues with unequal fiber mass `fiberCard val a ≠
fiberCard val (a+s)` already RULES OUT every value-shift of step `s`. Hence the spreading mechanism
can only deliver order `> 1` if the histogram is genuinely `+s`-periodic.

## Probe verdict (probe-first, reproducible)

For the prize energy value map `val(t) = Σ_{i<r} x_i − Σ_{i<r} y_i` over `t ∈ μ_n^{2r}`
(thin 2-power subgroup `μ_n ⊊ F_p^*`, `n = 2^a`, `p ≡ 1 mod n`, `p ≫ n³`, NEVER `n = q−1`):

* The value-SET `V_r` FILLS the field `ZMod p` for every `r ≥ 2` — so the value-set's additive
  stabilizer is the full field (`p` prime ⟹ stabilizer is `{0}` or all of `ZMod p`).
* BUT the fiber-cardinality histogram is NEVER `+s`-invariant for any unit `s`: it is sharply
  non-flat and non-periodic (e.g. `p=97, n=8, r=3`: fiber masses range `min=1505, max=5600`; the
  largest `+s`-period is `1` at every tested `(p,n,r)`).

So although `V_r` is `+s`-symmetric for `s` of full order, that symmetry does NOT lift to a
tuple-permutation realizing a fixed shift: a value-shift demands the strictly stronger
fiber-CARDINALITY periodicity, which fails. **The only value-shift of the prize value map is the
trivial one (`s = 0`, order `1`), and the spreading mechanism then gives `≤ #T/1 = #T` — no bound.**

VERDICT: the value-shift / free-part route of `charP_energy_of_shift` does NOT escape to a useful
bound for the prize value map. To use spreading at order `> 1` one must first exhibit a
`+s`-periodic fiber histogram, which the prize geometry refutes. No CORE, cancellation, completion,
moment-saving, or capacity claim.

## Statements

* `valueShift_histogram_periodic` : a `ValueShift` of step `s` forces `fiberCard val a =
  fiberCard val (a+s)` for all `a` (the histogram is `+s`-invariant). [packages `fiberCard_shift_eq`
  as the obstruction it really is].
* `no_valueShift_of_histogram_witness` : if some `a` has `fiberCard val a ≠ fiberCard val (a+s)`,
  then NO `ValueShift` with that step `s` exists.
* `valueShift_step_zero_of_no_periodicity` : if for every nonzero step `s` the histogram fails
  `+s`-periodicity, then every `ValueShift` has step `s = 0`.
* `shift_spreading_trivial_of_step_zero` : a step-`0` value-shift gives only the trivial spreading
  bound (`fiberCard val 0 ≤ #T`), i.e. no improvement.
* `realizableStep_all_or_nothing` : the realizable value-shift steps form an additive subgroup of
  `ZMod p`; for `p` prime it is `{0}` or all of `ZMod p`, so the shift free part is ALL-OR-NOTHING.
  One histogram witness collapses the entire group to `{0}`, putting the prize value map firmly in
  the no-free-part case.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.show false

namespace ArkLib.ProximityGap.Frontier.DoorIVValueShiftHistogramObstruction

open Finset
open ArkLib.ProximityGap.Frontier.NovelAntiConcentration

variable {T : Type*} [Fintype T] [DecidableEq T] {p : ℕ}

/-- **A value-shift forces its fiber histogram to be `+s`-periodic.** This is exactly the obligation
a `ValueShift` imposes: the per-residue fiber mass at `a` equals the mass at `a + s`. It is the
re-packaging of `fiberCard_shift_eq` as the necessary condition for the shift to exist. -/
theorem valueShift_histogram_periodic (val : T → ZMod p) (vs : ValueShift val) (a : ZMod p) :
    fiberCard val a = fiberCard val (a + vs.s) :=
  fiberCard_shift_eq val vs a

/-- **The contrapositive obstruction.** If a single residue `a` has fiber mass differing from the
mass at `a + s`, then NO `ValueShift` whose step equals `s` can exist. A non-periodic histogram is a
kernel-checkable certificate against the value-shift route at that step. -/
theorem no_valueShift_of_histogram_witness (val : T → ZMod p) (s : ZMod p) (a : ZMod p)
    (hne : fiberCard val a ≠ fiberCard val (a + s)) :
    ¬ ∃ vs : ValueShift val, vs.s = s := by
  rintro ⟨vs, rfl⟩
  exact hne (valueShift_histogram_periodic val vs a)

/-- **No nonzero step survives a globally non-periodic histogram.** If for every nonzero candidate
step `s` there is a witness residue with unequal fiber mass at `a` and `a + s`, then every
`ValueShift` of `val` has step `s = 0`. This is the exact collapse the prize probe exhibits: the
fiber histogram is `+s`-non-periodic for all `s ≠ 0`, so the only available shift is trivial. -/
theorem valueShift_step_zero_of_no_periodicity (val : T → ZMod p)
    (hno : ∀ s : ZMod p, s ≠ 0 → ∃ a : ZMod p, fiberCard val a ≠ fiberCard val (a + s))
    (vs : ValueShift val) :
    vs.s = 0 := by
  by_contra hs
  obtain ⟨a, ha⟩ := hno vs.s hs
  exact ha (valueShift_histogram_periodic val vs a)

/-- **A step-`0` value-shift gives only the trivial spreading bound.** When the only available
value-shift has step `s = 0`, the spreading mechanism `fiberCard_zero_le_of_shift_order` runs at
order `m = 1`, yielding `fiberCard val 0 ≤ #T`, the vacuous ceiling. The anti-concentration route
delivers no improvement. -/
theorem shift_spreading_trivial_of_step_zero (val : T → ZMod p) :
    fiberCard val 0 ≤ Fintype.card T := by
  classical
  have : Fiber val 0 ⊆ (Finset.univ : Finset T) := Finset.subset_univ _
  calc fiberCard val 0 = (Fiber val 0).card := rfl
    _ ≤ (Finset.univ : Finset T).card := Finset.card_le_card this
    _ = Fintype.card T := Finset.card_univ

/-- **The full obstruction, assembled.** If the fiber histogram of `val` is `+s`-non-periodic for
every nonzero step, then every value-shift is trivial and the spreading mechanism collapses to the
vacuous ceiling `fiberCard val 0 ≤ #T`. So under the prize-geometry probe verdict, the value-shift
route of `charP_energy_of_shift` cannot produce a sub-`#T` bound on the wraparound. -/
theorem valueShift_route_vacuous_of_no_periodicity (val : T → ZMod p)
    (hno : ∀ s : ZMod p, s ≠ 0 → ∃ a : ZMod p, fiberCard val a ≠ fiberCard val (a + s))
    (vs : ValueShift val) :
    vs.s = 0 ∧ fiberCard val 0 ≤ Fintype.card T :=
  ⟨valueShift_step_zero_of_no_periodicity val hno vs, shift_spreading_trivial_of_step_zero val⟩

/-! ## The realizable-step set is an additive subgroup: value-shifts are all-or-nothing.

The steps `s` for which a `ValueShift` of step `s` exists are closed under negation and addition
(compose / invert the underlying tuple permutations). Hence they form an additive subgroup of
`ZMod p`. For `p` prime that subgroup is either `{0}` or all of `ZMod p`: the value-shift free part
is ALL-OR-NOTHING. Combined with the histogram obstruction above, ONE witness residue with unequal
fiber mass collapses the ENTIRE realizable-step group to `{0}`. -/

/-- **Compose two value-shifts.** If `val` admits shifts of steps `s₁` and `s₂`, it admits a shift
of step `s₁ + s₂` (apply one permutation after the other). -/
def ValueShift.comp (val : T → ZMod p) (vs₁ vs₂ : ValueShift val) : ValueShift val where
  g := vs₁.g.trans vs₂.g
  s := vs₁.s + vs₂.s
  shift := by
    intro t
    show val (vs₂.g (vs₁.g t)) = val t + (vs₁.s + vs₂.s)
    rw [vs₂.shift (vs₁.g t), vs₁.shift t, add_assoc]

/-- **Invert a value-shift.** If `val` admits a shift of step `s`, it admits a shift of step `-s`
(use the inverse permutation). -/
def ValueShift.inv (val : T → ZMod p) (vs : ValueShift val) : ValueShift val where
  g := vs.g.symm
  s := -vs.s
  shift := by
    intro t
    have h := vs.shift (vs.g.symm t)
    rw [Equiv.apply_symm_apply] at h
    rw [h]
    ring

/-- **The realizable-step set is closed under negation.** -/
theorem realizableStep_neg (val : T → ZMod p) (s : ZMod p)
    (h : ∃ vs : ValueShift val, vs.s = s) :
    ∃ vs : ValueShift val, vs.s = -s := by
  obtain ⟨vs, rfl⟩ := h
  exact ⟨ValueShift.inv val vs, rfl⟩

/-- **The realizable-step set is closed under addition.** -/
theorem realizableStep_add (val : T → ZMod p) (s₁ s₂ : ZMod p)
    (h₁ : ∃ vs : ValueShift val, vs.s = s₁) (h₂ : ∃ vs : ValueShift val, vs.s = s₂) :
    ∃ vs : ValueShift val, vs.s = s₁ + s₂ := by
  obtain ⟨vs₁, rfl⟩ := h₁
  obtain ⟨vs₂, rfl⟩ := h₂
  exact ⟨ValueShift.comp val vs₁ vs₂, rfl⟩

/-- **The realizable-step set always contains `0`** (the identity permutation shifts by `0`). -/
theorem realizableStep_zero (val : T → ZMod p) :
    ∃ vs : ValueShift val, vs.s = (0 : ZMod p) :=
  ⟨{ g := Equiv.refl T, s := 0, shift := by intro t; simp }, rfl⟩

/-- **All-or-nothing (the sharp dichotomy).** The realizable-step set is an additive subgroup of
`ZMod p`. So if even ONE nonzero step `s ≠ 0` is realizable, then because the subgroup generated by
a nonzero element of a field of prime order is the whole field, EVERY step `t` is realizable. The
value-shift free part is therefore all-or-nothing: either only `s = 0` works, or every `s` works.

This is the structural sharpening of the histogram obstruction: there is no "partial" free part to
harvest. A single histogram witness (`fiberCard a ≠ fiberCard (a+s)` for some `s ≠ 0`) does not just
kill the step `s`; via `no_valueShift_of_histogram_witness` it kills `s`, and since the realizable
set is a subgroup, the prize value map sits in the `{0}`-only case wholesale. -/
theorem realizableStep_all_or_nothing [Fact (Nat.Prime p)] (val : T → ZMod p)
    (s : ZMod p) (hs : s ≠ 0) (hreal : ∃ vs : ValueShift val, vs.s = s) :
    ∀ t : ZMod p, ∃ vs : ValueShift val, vs.s = t := by
  -- the realizable-step set is the carrier of an AddSubgroup of ZMod p
  let H : AddSubgroup (ZMod p) :=
    { carrier := {x | ∃ vs : ValueShift val, vs.s = x}
      zero_mem' := realizableStep_zero val
      add_mem' := fun {a b} ha hb => realizableStep_add val a b ha hb
      neg_mem' := fun {a} ha => realizableStep_neg val a ha }
  have hsH : s ∈ H := hreal
  -- a nonzero element of a field is a unit; for any `t`, `t = (t * s⁻¹) * s`, and `H` being a
  -- subgroup that contains `s` contains `c • s` for any `c : ZMod p` via the `zsmul`/field action.
  -- We rewrite `t = (t * s⁻¹) * s` and show `(t * s⁻¹) * s ∈ H` using that `H` absorbs ring
  -- multiplication by `s` on the contained generator: in the field `ZMod p`, `c * s = (c * s⁻¹') ...`
  -- Direct route: every `t` equals `(t * s⁻¹) * s`; and the map `c ↦ c * s` is surjective (s a unit),
  -- so it suffices to show `H` is closed under `c ↦ c * s` from `s ∈ H`. That closure is exactly
  -- `AddSubgroup.zmultiples s = ⊤` in a prime field, which we get from order = card.
  intro t
  -- `s` generates all of `ZMod p` additively because its additive order is `p = card (ZMod p)`.
  have hp : Nat.Prime p := (Fact.out : Nat.Prime p)
  have hgen : AddSubgroup.zmultiples s = (⊤ : AddSubgroup (ZMod p)) := by
    -- additive order of a nonzero element of ZMod p (prime) is p
    have hord : addOrderOf s = p := by
      have hdvd : addOrderOf s ∣ p := by
        have h := addOrderOf_dvd_card (x := s)
        rwa [ZMod.card] at h
      rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h1 | hpp
      · exfalso
        rw [AddMonoid.addOrderOf_eq_one_iff] at h1
        exact hs h1
      · exact hpp
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples, hord, Nat.card_eq_fintype_card, ZMod.card]
  have htmem : t ∈ AddSubgroup.zmultiples s := by rw [hgen]; trivial
  rw [AddSubgroup.mem_zmultiples_iff] at htmem
  obtain ⟨z, hz⟩ := htmem
  -- `z • s ∈ H` since `H` contains `s` and is a subgroup (closed under zsmul)
  have hmem : z • s ∈ H := AddSubgroup.zsmul_mem H hsH z
  rwa [hz] at hmem


/-- **Nontrivial value-shift forces a flat histogram.** In a prime field, one nonzero realizable
step makes every step realizable by `realizableStep_all_or_nothing`; applying histogram periodicity
with the step `b - a` shows every two fibers have equal cardinality. Thus the only way the
value-shift route can have a genuine free part is if the value map is perfectly equidistributed
across residues. The prize probes exhibit non-flat histograms, so they sit in the trivial-shift case. -/
theorem nontrivial_valueShift_forces_flat_histogram [Fact (Nat.Prime p)] (val : T → ZMod p)
    {s : ZMod p} (hs : s ≠ 0) (hreal : ∃ vs : ValueShift val, vs.s = s) :
    ∀ a b : ZMod p, fiberCard val a = fiberCard val b := by
  intro a b
  obtain ⟨vs, hvs⟩ := realizableStep_all_or_nothing val s hs hreal (b - a)
  have hper := valueShift_histogram_periodic val vs a
  rw [hvs] at hper
  convert hper using 2
  ring

/-- **Single-witness collapse (contrapositive form).** In a prime field, because realizable steps are
all-or-nothing, a single nonzero step with a non-periodic fiber histogram forces every value-shift to
have trivial step `0`. This is stronger than requiring a separate histogram witness for every nonzero
step: one failed nonzero step rules out the all-steps case. -/
theorem valueShift_step_zero_of_one_histogram_witness [Fact (Nat.Prime p)] (val : T → ZMod p)
    {s a : ZMod p} (hne : fiberCard val a ≠ fiberCard val (a + s)) (vs : ValueShift val) :
    vs.s = 0 := by
  by_contra hvs
  have hall : ∀ t : ZMod p, ∃ vs' : ValueShift val, vs'.s = t :=
    realizableStep_all_or_nothing val vs.s hvs ⟨vs, rfl⟩
  exact (no_valueShift_of_histogram_witness val s a hne) (hall s)

/-- **Single-witness vacuity.** In a prime field, one nonzero histogram mismatch already collapses the
value-shift spreading mechanism to the trivial ceiling. -/
theorem valueShift_route_vacuous_of_one_histogram_witness [Fact (Nat.Prime p)] (val : T → ZMod p)
    {s a : ZMod p} (hne : fiberCard val a ≠ fiberCard val (a + s)) (vs : ValueShift val) :
    vs.s = 0 ∧ fiberCard val 0 ≤ Fintype.card T :=
  ⟨valueShift_step_zero_of_one_histogram_witness val hne vs,
    shift_spreading_trivial_of_step_zero val⟩

end ArkLib.ProximityGap.Frontier.DoorIVValueShiftHistogramObstruction

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
section AxiomAudit
open ArkLib.ProximityGap.Frontier.DoorIVValueShiftHistogramObstruction
#print axioms valueShift_histogram_periodic
#print axioms no_valueShift_of_histogram_witness
#print axioms valueShift_step_zero_of_no_periodicity
#print axioms shift_spreading_trivial_of_step_zero
#print axioms valueShift_route_vacuous_of_no_periodicity
#print axioms realizableStep_neg
#print axioms realizableStep_add
#print axioms realizableStep_zero
#print axioms realizableStep_all_or_nothing
#print axioms nontrivial_valueShift_forces_flat_histogram
#print axioms valueShift_step_zero_of_one_histogram_witness
#print axioms valueShift_route_vacuous_of_one_histogram_witness
end AxiomAudit
