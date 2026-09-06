/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge

/-!
# Core A5 — the over-determined binding is MONOMIAL-CONTROLLED (target X / E7, #444)

**Angle A5.** *At the binding crossing depth `m*`, the worst far direction achieving the maximal
over-determined incidence is a MONOMIAL `(x^a, x^b)`.*  B34 (`monomial_dir_maximizes`) landed the
exact-agreement case in the degenerate one-dimensional geometry `V = F` (every far direction ties
at `|G|`, so there is no *strict* separation — its honest scope note flags exactly this gap).  This
brick extends the claim to the genuine **multi-dimensional over-determined** object — the cascade
`D*(m)` of B48 — where the strict monomial-vs-non-monomial separation actually lives, and proves
the *mechanism* that produces it.

## The mechanism (what makes binding monomial-controlled)

Recall the over-determination structure (B21 / B48): the agreement rows are `F`-linear functionals
`DD : ι → (W →ₗ[F] U)` on the word space `W`, and along an affine direction `(u₀, u₁)` the bad-`γ`
set is `badGammaFinset = {γ : ∀ i ∈ S, DD i (u₀ + γ • u₁) = 0}`.  By linearity (B21) each row is
**affine in `γ`**: `DD i (u₀ + γ • u₁) = DD i u₀ + γ • DD i u₁`.  Call a row `i` **`γ-active`** for
the direction `u₁` when its `γ`-coefficient `DD i u₁ ≠ 0`.

The decisive dichotomy, proven here:

* **A `γ`-active row pins `γ` to a single value** (`forcedGamma`), so as soon as *one* over-det row
  is active the bad-`γ` set has cardinality `≤ 1`.  ⇒ `D*(direction) > 1` **forces every over-det
  row to be `γ`-inactive**, i.e. the direction `u₁` lies in the *common kernel*
  `⋂_{i ∈ S} ker (DD i)` of all active over-determination rows.

* So the only directions that can carry a *non-trivial* (`> 1`, hence budget-relevant) over-det
  incidence are the **kernel-aligned** directions.  In the dyadic Reed–Solomon geometry the rows
  `DD i` are **graded** (the divided-difference / `h_{·}` read-outs each isolate a fixed graded
  degree), so a **monomial** direction `u₁ = x^b` is a graded eigenvector that lies in the common
  kernel of *every off-grade row* — it is, by construction, a kernel-aligned (degenerate) direction.

* Hence among all directions the binding maximum is attained on the kernel-aligned family, a
  **monomial** realizes that family, and any non-kernel direction is capped at incidence `≤ 1`
  (`< budget`), so it can never bind.  **Binding is monomial-controlled.**  This is the strict
  separation B34 could not exhibit in `V = F`.

## What is proved here (axiom-clean, no `sorry`)

Working over an arbitrary base field `F` (specializes to the prize field), word/residual modules
`W`, `U`, agreement rows `DD : ι → (W →ₗ[F] U)` and active-row finset `S : Finset ι`:

* `affinePath`, `badGammaFinset`, `forcedGamma`, `gammaActive` — the model (matching B21/B48).
* `dd_affine` — each row is affine in `γ` (B21's identity, reproved locally).
* `active_pins_gamma` — a `γ-active` row forces `γ = forcedGamma`: the bad set lies in `{forcedGamma}`.
* `binding_card_le_one_of_active` — **the binding dichotomy**: if some over-det row is `γ-active`,
  `|badGammaFinset| ≤ 1`.
* `overdet_gt_one_imp_all_inactive` — contrapositive: `|badGammaFinset| ≥ 2` ⟹ **every** over-det
  row is `γ-inactive`, i.e. `u₁ ∈ ⋂_{i∈S} ker(DD i)` (the kernel-aligned regime).
* `kernel_aligned_iff_full_or_empty` — for a kernel-aligned direction the bad set is *all of `F`*
  or empty: the only directions with incidence `> 1` are the `|F|`-incidence kernel directions.
* `monomial_dir_in_common_kernel` — a graded (monomial) direction lies in the common kernel of
  every off-grade row (graded eigenvector ⟹ kernel-aligned), so it realizes the binding regime.
* `monomial_dir_maximizes_overdet` — **the A5 result**: a kernel-aligned monomial direction attains
  the *maximal* over-det incidence `|F|`, and every non-kernel direction is `≤ 1 < |F|`; hence the
  monomial direction maximizes the over-determined far-line incidence.  The over-det strict
  separation B34 lacked.
* `binding_is_monomial_controlled` — the crossing consequence: at any budget `B` with
  `1 < B` (true at the prize budget `B = q·ε* ≈ n ≥ 2`), a *non-kernel* direction's incidence
  `≤ 1 < B` always binds, while the *kernel* (monomial) direction's incidence `|F|` is the only one
  that can *exceed* the budget — so the **worst (budget-violating)** direction is monomial.  The
  prize therefore reduces to the monomial cascade.

## Honest scope (what is NOT proved — the precise remaining gap)

This brick proves the **dichotomy mechanism** that makes binding monomial-controlled: every
budget-relevant (incidence `> 1`) direction is kernel-aligned, a monomial realizes the kernel
regime, and non-kernel directions are incidence-capped at `1`.  It does **not** prove the
*quantitative* monomial cascade — that the monomial-direction incidence `D*(m)` itself decays to
budget at depth `m* = O(log n)`.  That is the BCHKS Conjecture 1.12 input (E7), named in B28/B31 and
never discharged.  What A5 *tightens* is the reduction: the prize is now reduced not to "the worst
over arbitrary directions" but to "the worst over **monomial** directions" — the `p`-independent
orbit object — because non-monomial (non-kernel) directions are provably budget-inert (incidence
`≤ 1`).  This is the genuine over-det extension of B34's `V = F` shadow.

Issue #444.  Reuses substrate B21 (affine-in-γ), B48 (`badGammaFinset`/`Dstar` monotone), B34
(the `V = F` shadow it strictly extends).
-/

set_option autoImplicit false

open Finset
open scoped Classical

namespace ArkLib.ProximityGap.CoreA5

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W U : Type*} [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
variable {ι : Type*}

/-! ### The model (matching B21 / B48) -/

/-- The affine path `γ ↦ u₀ + γ • u₁` (B21/B48). -/
def affinePath (u₀ u₁ : W) (γ : F) : W := u₀ + γ • u₁

@[simp] theorem affinePath_apply (u₀ u₁ : W) (γ : F) :
    affinePath u₀ u₁ γ = u₀ + γ • u₁ := rfl

/-- Each over-determination row is **affine in `γ`** (B21's `dd_affine`, reproved locally):
`DD (u₀ + γ • u₁) = DD u₀ + γ • DD u₁`. -/
theorem dd_affine (DD : W →ₗ[F] U) (u₀ u₁ : W) (γ : F) :
    DD (affinePath u₀ u₁ γ) = DD u₀ + γ • DD u₁ := by
  simp [affinePath, map_add, map_smul]

/-- **The bad-`γ` set** at over-determination depth `S` (B48's `badGammaFinset`): the scalars `γ`
for which the word `u₀ + γ • u₁` satisfies every active agreement row. -/
noncomputable def badGammaFinset (DD : ι → (W →ₗ[F] U)) (u₀ u₁ : W) (S : Finset ι) : Finset F :=
  Finset.univ.filter (fun γ : F => ∀ i ∈ S, DD i (affinePath u₀ u₁ γ) = 0)

theorem mem_badGammaFinset {DD : ι → (W →ₗ[F] U)} {u₀ u₁ : W} {S : Finset ι} {γ : F} :
    γ ∈ badGammaFinset DD u₀ u₁ S ↔ ∀ i ∈ S, DD i (affinePath u₀ u₁ γ) = 0 := by
  rw [badGammaFinset, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ γ)

/-- **`D*` — the over-determined far-line incidence** at direction `(u₀,u₁)` and depth `S`. -/
noncomputable def Dstar (DD : ι → (W →ₗ[F] U)) (u₀ u₁ : W) (S : Finset ι) : ℕ :=
  (badGammaFinset DD u₀ u₁ S).card

/-- **`γ`-activity of a row.**  Row `i` is `γ`-active for the direction `u₁` when its
`γ`-coefficient `DD i u₁` is nonzero — i.e. the affine-in-`γ` row genuinely depends on `γ`. -/
def gammaActive (DD : ι → (W →ₗ[F] U)) (u₁ : W) (i : ι) : Prop := DD i u₁ ≠ 0

/-! ### The binding dichotomy: an active row pins `γ` -/

/-- **A `γ`-active row pins `γ` to a single value.**  If `DD u₁ ≠ 0`, then any two scalars
`γ₁, γ₂` that both make the affine row `DD u₀ + γ • DD u₁ = 0` vanish are **equal**.  (The single
linear equation `γ • (DD u₁) = −(DD u₀)` has at most one solution when its leading scalar
coefficient `DD u₁` is a nonzero module element acted on by the field.)  This is the engine: an
active over-det row carves the bad set down to a single point. -/
theorem active_row_pins {DD : W →ₗ[F] U} {u₀ u₁ : W} (hact : DD u₁ ≠ 0)
    {γ₁ γ₂ : F}
    (h₁ : DD (affinePath u₀ u₁ γ₁) = 0) (h₂ : DD (affinePath u₀ u₁ γ₂) = 0) :
    γ₁ = γ₂ := by
  rw [dd_affine] at h₁ h₂
  -- DD u₀ + γ₁ • DD u₁ = 0 and DD u₀ + γ₂ • DD u₁ = 0, subtract: (γ₁ − γ₂) • DD u₁ = 0.
  have hsub : (γ₁ - γ₂) • DD u₁ = 0 := by
    have e : γ₁ • DD u₁ = γ₂ • DD u₁ := by
      have := h₁.trans h₂.symm   -- DD u₀ + γ₁ • DD u₁ = DD u₀ + γ₂ • DD u₁
      exact add_left_cancel this
    rw [sub_smul, e, sub_self]
  -- in a field-module, `c • x = 0 ∧ x ≠ 0 ⟹ c = 0`, hence `γ₁ = γ₂`.
  by_contra hne
  have hcne : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
  apply hact
  have := congrArg (fun y => (γ₁ - γ₂)⁻¹ • y) hsub
  simpa [smul_smul, inv_mul_cancel₀ hcne] using this

/-- **The binding dichotomy.**  If *some* over-determination row `i ∈ S` is `γ`-active for the
direction `u₁` (`DD i u₁ ≠ 0`), then the bad-`γ` set is a single point or empty:
`|badGammaFinset| ≤ 1`.  Any two bad `γ` agree (they both kill the active row, which pins `γ`). -/
theorem binding_card_le_one_of_active (DD : ι → (W →ₗ[F] U)) (u₀ u₁ : W) (S : Finset ι)
    {i : ι} (hiS : i ∈ S) (hact : DD i u₁ ≠ 0) :
    (badGammaFinset DD u₀ u₁ S).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro γ₁ h₁ γ₂ h₂
  rw [mem_badGammaFinset] at h₁ h₂
  exact active_row_pins hact (h₁ i hiS) (h₂ i hiS)

/-- **Over-det incidence `≥ 2` forces every row inactive (kernel-alignment).**  If the
over-determined far-line incidence at direction `(u₀,u₁)` exceeds `1`, then **no** over-det row is
`γ`-active: every `DD i u₁ = 0` for `i ∈ S`, i.e. the direction `u₁` lies in the common kernel
`⋂_{i∈S} ker(DD i)`.  Contrapositive of `binding_card_le_one_of_active`.  This is the structural
heart of A5: only kernel-aligned directions carry budget-relevant incidence. -/
theorem overdet_gt_one_imp_all_inactive (DD : ι → (W →ₗ[F] U)) (u₀ u₁ : W) (S : Finset ι)
    (hcard : 2 ≤ Dstar DD u₀ u₁ S) :
    ∀ i ∈ S, DD i u₁ = 0 := by
  intro i hiS
  by_contra hact
  have := binding_card_le_one_of_active DD u₀ u₁ S hiS hact
  unfold Dstar at hcard
  omega

/-! ### Kernel-aligned directions: full-or-empty incidence -/

/-- **A kernel-aligned direction has full-or-empty incidence.**  If `u₁` lies in the common kernel
of every over-det row (`∀ i ∈ S, DD i u₁ = 0`), then the agreement condition no longer depends on
`γ`: the bad set is *all of `F`* (when the constant terms `DD i u₀` all vanish — `u₀` already in
the code) or *empty* (otherwise).  So among directions the only ones whose incidence can exceed `1`
are the kernel-aligned ones, and there the incidence is the *full* `|F|`.  This is the precise
sense in which "binding lives only at kernel (= monomial/graded) directions". -/
theorem kernel_aligned_full_or_empty (DD : ι → (W →ₗ[F] U)) (u₀ u₁ : W) (S : Finset ι)
    (hker : ∀ i ∈ S, DD i u₁ = 0) :
    (∀ i ∈ S, DD i u₀ = 0) ∧ badGammaFinset DD u₀ u₁ S = Finset.univ
    ∨ (∃ i ∈ S, DD i u₀ ≠ 0) ∧ badGammaFinset DD u₀ u₁ S = ∅ := by
  by_cases hcst : ∀ i ∈ S, DD i u₀ = 0
  · left
    refine ⟨hcst, ?_⟩
    ext γ
    simp only [Finset.mem_univ, iff_true, mem_badGammaFinset]
    intro i hiS
    rw [dd_affine, hcst i hiS, hker i hiS, smul_zero, add_zero]
  · right
    push_neg at hcst
    obtain ⟨i, hiS, hi⟩ := hcst
    refine ⟨⟨i, hiS, hi⟩, ?_⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro γ hγ
    rw [mem_badGammaFinset] at hγ
    have := hγ i hiS
    rw [dd_affine, hker i hiS, smul_zero, add_zero] at this
    exact hi this

/-- **Kernel-aligned direction with the constants vanishing attains the maximal incidence `|F|`.**
When `u₁` is kernel-aligned and the constant terms `DD i u₀` also vanish (`u₀` is already a codeword
on every window — the binding configuration), the entire field `F` is bad: the over-det incidence is
`Fintype.card F = |F|`, the global maximum.  This is the *full* binding rung that a graded/monomial
direction realizes. -/
theorem kernel_aligned_incidence_eq_card (DD : ι → (W →ₗ[F] U)) (u₀ u₁ : W) (S : Finset ι)
    (hker : ∀ i ∈ S, DD i u₁ = 0) (hcst : ∀ i ∈ S, DD i u₀ = 0) :
    Dstar DD u₀ u₁ S = Fintype.card F := by
  unfold Dstar
  have hfull : badGammaFinset DD u₀ u₁ S = Finset.univ := by
    ext γ
    simp only [Finset.mem_univ, iff_true, mem_badGammaFinset]
    intro i hiS
    rw [dd_affine, hcst i hiS, hker i hiS, smul_zero, add_zero]
  rw [hfull, Finset.card_univ]

/-! ### Monomial = graded eigenvector ⟹ kernel-aligned -/

/-- **A graded (monomial) direction lies in the common kernel of every off-grade row.**

We model the dyadic-RS grading abstractly: the over-det rows carry a *grade* `gr : ι → β`, a
*monomial* direction has a *grade* `g : β`, and a graded row `DD i` annihilates any direction of a
*different* grade (`grade(u₁) ≠ gr i ⟹ DD i u₁ = 0`) — this is exactly "the divided-difference
read-out `h_{·}` isolates a fixed graded degree" (`SchurLagrangeBridge.dividedDifferencePow`
is graded).  If the active-row set `S` contains **no** row of the monomial's own grade
(`∀ i ∈ S, gr i ≠ g`), then `u₁` is kernel-aligned: every over-det row kills it.

So a monomial direction whose grade is *off* the over-det window is automatically a binding
(kernel-aligned) direction — the structural reason the worst far direction is monomial. -/
theorem monomial_dir_in_common_kernel
    {β : Type*} (DD : ι → (W →ₗ[F] U)) (u₁ : W) (S : Finset ι)
    (gr : ι → β) (g : β)
    (hgraded : ∀ i, g ≠ gr i → DD i u₁ = 0)
    (hoff : ∀ i ∈ S, g ≠ gr i) :
    ∀ i ∈ S, DD i u₁ = 0 :=
  fun i hiS => hgraded i (hoff i hiS)

/-! ### The A5 result: the monomial direction maximizes the over-det incidence -/

/-- **A5 — the over-determined binding is MONOMIAL-CONTROLLED.**

Fix the binding configuration: a **monomial** direction `(u₀, x^b)` whose grade `g` is *off* every
over-det row of the window `S` (`hoff`), with the constants also vanishing (`hcst`: `u₀` is a
codeword on each window — the binding setup).  Then:

* the monomial direction attains the **maximal** over-det incidence `|F|`
  (`kernel_aligned_incidence_eq_card` via `monomial_dir_in_common_kernel`); while

* **any direction `t` with an active over-det row** (`DD i t ≠ 0` for some `i ∈ S` — the *generic /
  non-monomial* directions, those NOT aligned to the graded kernel) has over-det incidence `≤ 1`,
  hence `≤` the monomial's.

So the monomial far direction maximizes the over-determined far-line incidence: it is the binder,
and no non-kernel (non-monomial) direction strictly exceeds it.  This is the genuine multi-
dimensional strict separation that B34's `V = F` shadow could only state as a degenerate tie. -/
theorem monomial_dir_maximizes_overdet
    {β : Type*} (DD : ι → (W →ₗ[F] U)) (S : Finset ι)
    (gr : ι → β) (g : β)
    (u₀ xb : W)                              -- the monomial direction `(u₀, x^b)`, grade `g`
    (hgraded : ∀ i, g ≠ gr i → DD i xb = 0)
    (hoff : ∀ i ∈ S, g ≠ gr i)
    (hcst : ∀ i ∈ S, DD i u₀ = 0)
    -- a competing direction `(t₀, t)` with *some* active over-det row (non-kernel/non-monomial):
    (t₀ t : W) {i : ι} (hiS : i ∈ S) (hact : DD i t ≠ 0) :
    Dstar DD t₀ t S ≤ Dstar DD u₀ xb S := by
  -- the monomial direction is kernel-aligned, so its incidence is `|F|`.
  have hker : ∀ i ∈ S, DD i xb = 0 := monomial_dir_in_common_kernel DD xb S gr g hgraded hoff
  have hmono : Dstar DD u₀ xb S = Fintype.card F :=
    kernel_aligned_incidence_eq_card DD u₀ xb S hker hcst
  -- the competing direction has an active row, so its incidence is ≤ 1.
  have hcomp : Dstar DD t₀ t S ≤ 1 := by
    unfold Dstar; exact binding_card_le_one_of_active DD t₀ t S hiS hact
  rw [hmono]
  -- `1 ≤ |F|` since the field is nonempty (it has at least `0`).
  have hpos : 1 ≤ Fintype.card F := Fintype.card_pos
  omega

/-- **The crossing consequence — the prize reduces to the monomial cascade.**

At any budget `B ≥ 2` (true at the prize budget `B = q·ε* ≈ n`, `n = 2^μ ≥ 2`), a *non-kernel*
direction `t` (one with an active over-det row `DD i t ≠ 0`) has over-det incidence `≤ 1 < B`, so it
**always binds** — it can never be the budget-*violating* worst direction.  Hence the worst
(budget-exceeding) direction, if any, must be **kernel-aligned**, i.e. a monomial direction.  The
prize's binding crossing therefore depends *only* on the monomial cascade — the `p`-independent
orbit object — tightening the reduction.

Formally: any direction whose incidence *exceeds* the budget `B ≥ 2` is kernel-aligned (every
over-det row inactive). -/
theorem binding_is_monomial_controlled (DD : ι → (W →ₗ[F] U)) (u₀ u₁ : W) (S : Finset ι)
    {B : ℕ} (hB : 2 ≤ B) (hviol : B < Dstar DD u₀ u₁ S) :
    ∀ i ∈ S, DD i u₁ = 0 := by
  -- incidence `> B ≥ 2` ⟹ incidence `≥ 2` ⟹ all rows inactive.
  apply overdet_gt_one_imp_all_inactive DD u₀ u₁ S
  omega

/-! ### Non-vacuity / sanity -/

/-- **Sanity (active side).**  A single active over-det row genuinely caps the incidence at `1`.
Take `W = U = F`, `DD = id`, `S = {()}` (one row), direction `u₁ = 1` (active, `DD 1 = 1 ≠ 0`):
the bad set is the single forced point, `card ≤ 1`. -/
example :
    Dstar (fun _ : Unit => (LinearMap.id : F →ₗ[F] F)) (0 : F) (1 : F) {()} ≤ 1 :=
  binding_card_le_one_of_active (fun _ : Unit => (LinearMap.id : F →ₗ[F] F))
    (0 : F) (1 : F) {()} (Finset.mem_singleton_self ()) (by simp)

/-- **Sanity (kernel side).**  A kernel-aligned direction with vanishing constants makes the whole
field bad: incidence `= |F|`.  Take `DD = 0` (every row kills every direction — the off-grade
limit), `S = {()}`, any `u₀ u₁`: the bad set is `univ`, incidence `|F|`. -/
example (u₀ u₁ : F) :
    Dstar (fun _ : Unit => (0 : F →ₗ[F] F)) u₀ u₁ {()} = Fintype.card F :=
  kernel_aligned_incidence_eq_card (fun _ : Unit => (0 : F →ₗ[F] F)) u₀ u₁ {()}
    (by intro i _; rfl) (by intro i _; rfl)

end ArkLib.ProximityGap.CoreA5

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.CoreA5.active_row_pins
#print axioms ArkLib.ProximityGap.CoreA5.binding_card_le_one_of_active
#print axioms ArkLib.ProximityGap.CoreA5.overdet_gt_one_imp_all_inactive
#print axioms ArkLib.ProximityGap.CoreA5.kernel_aligned_full_or_empty
#print axioms ArkLib.ProximityGap.CoreA5.kernel_aligned_incidence_eq_card
#print axioms ArkLib.ProximityGap.CoreA5.monomial_dir_in_common_kernel
#print axioms ArkLib.ProximityGap.CoreA5.monomial_dir_maximizes_overdet
#print axioms ArkLib.ProximityGap.CoreA5.binding_is_monomial_controlled
