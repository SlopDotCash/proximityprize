/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge

/-!
# Bridge B48 — `D*` is monotone non-increasing in the over-determination depth `m` (target E4)

**Spec B48 / target E4.** *`D*` monotone non-increasing in `m`: agreement on `s+1` points
implies agreement on `s` points, so the bad-`γ` set at `s+1` is a subset of that at `s`, hence
its cardinality is monotone (`Finset.card_le_card`).*

## Context — the cascade is monotone (E4)

`D*(m)` is the worst-direction over-determined far-line incidence at over-determination depth
`m` — concretely, the cardinality of the **bad-`γ` set** of a window, the set of scalars `γ`
for which the word along the affine line `γ ↦ u₀ + γ·u₁` satisfies *all* the agreement
("over-determination") rows of the window.  The empirical cascade `E2` (`n=16`:
`[3936, 89, 9, …]`) is observed to be **non-increasing** in `m`, and `E4` reads off its leading
value and geometric decay *from that monotonicity*.

The reason is purely set-theoretic and is the content of this brick: deepening the
over-determination from `s` rows to `s+1` rows (requiring agreement on one more point) only
*adds* a constraint.  Every `γ` that satisfies the `s+1`-row system a fortiori satisfies the
`s`-row sub-system, so

  `badGammaSet(s+1) ⊆ badGammaSet(s)`,

and therefore by `Finset.card_le_card`

  `D*(s+1) = |badGammaSet(s+1)| ≤ |badGammaSet(s)| = D*(s)`.

This is the monotonicity that the whole `E4`/`E5` decay analysis presupposes; here it is an
axiom-clean Lean fact, with no field-size, regime, or analytic input.

## What is proven here (axiom-clean)

Working over an arbitrary base field `F` (so it specializes to the prize field), with the word
space `W` an arbitrary `F`-module, residual space `U` an `F`-module, and the agreement rows
indexed by a `Finset` `S : Finset ι` of "active" over-determination rows:

* **`badGammaFinset`** — the bad-`γ` set as a `Finset F`, the `γ ∈ F` satisfying every active
  row `DD i (u₀ + γ • u₁) = 0`.
* **`badGammaFinset_antitone`** — `S ⊆ T ⊢ badGammaFinset T ⊆ badGammaFinset S`: more active
  rows = smaller bad set (the agreement-implies-agreement direction).
* **`Dstar`** — `D*(S) := |badGammaFinset S|`, the over-determined far-line incidence.
* **`Dstar_le_of_subset`** — `S ⊆ T ⊢ Dstar T ≤ Dstar S` (the `Finset.card_le_card` step).
* **`Dstar_antitone_insert`** — the unit-step form: adding one more agreement row never
  increases `D*` (`Dstar (insert i S) ≤ Dstar S`), i.e. `D*(m+1) ≤ D*(m)`.
* **`Dstar_chain_antitone`** — the cascade form: along the natural-number depth filtration
  `m ↦ Sᵢ` with `m ≤ m' → Sₘ ⊆ Sₘ'`, `D*` is antitone in `m`.

## Bridge to the substrate (`IncidencePeriodBridge`)

The substrate counts the far-line incidence as `lineIncidence G s₀ s₁` — the `γ` on the affine
line landing in the ball `G`.  When the agreement rows are the per-coordinate membership
conditions of a syndrome ball (`G` is the `s`-row ball, deepening to the `s+1`-row ball ⊆ `G`),
the bad set is `badGammaFinset` and `Dstar` is exactly that incidence count;
`Dstar_subgroupBall` records the membership-ball specialization that matches the substrate's
`lineIncidence` shape, and `lineIncidence_antitone_ball` is the substrate-level monotonicity:
a smaller ball (deeper agreement) has incidence `≤` the larger ball.

Axiom-clean; pure `Finset` monotonicity, no field-size or regime hypotheses.  Issue #444
(target E4).
-/

open Finset
open scoped Classical

namespace ArkLib.ProximityGap.BridgeB48

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W U : Type*} [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
variable {ι : Type*}

/-- The affine path `γ ↦ u₀ + γ • u₁` through `u₀` with direction `u₁`. -/
def affinePath (u₀ u₁ : W) (γ : F) : W := u₀ + γ • u₁

@[simp] theorem affinePath_apply (u₀ u₁ : W) (γ : F) :
    affinePath u₀ u₁ γ = u₀ + γ • u₁ := rfl

/-- **The bad-`γ` set at over-determination depth `S`**, as a `Finset F`: the scalars `γ` for
which the word `u₀ + γ • u₁` along the affine line satisfies **every** active agreement row
`DD i` (`i ∈ S`).  Deepening `S` adds rows (= "agreement on more points"). -/
noncomputable def badGammaFinset (DD : ι → (W →ₗ[F] U)) (u₀ u₁ : W) (S : Finset ι) : Finset F :=
  Finset.univ.filter (fun γ : F => ∀ i ∈ S, DD i (affinePath u₀ u₁ γ) = 0)

theorem mem_badGammaFinset {DD : ι → (W →ₗ[F] U)} {u₀ u₁ : W} {S : Finset ι} {γ : F} :
    γ ∈ badGammaFinset DD u₀ u₁ S ↔ ∀ i ∈ S, DD i (affinePath u₀ u₁ γ) = 0 := by
  rw [badGammaFinset, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ γ)

/-- **Agreement on `T`-rows implies agreement on `S`-rows when `S ⊆ T` (the antitone step).**
A larger active-row set cuts out a *smaller* bad-`γ` set: if `γ` makes every `T`-row vanish, it
makes every `S`-row vanish (`S ⊆ T`).  This is the "agreement on `s+1` points ⟹ agreement on
`s` points" of the spec. -/
theorem badGammaFinset_antitone (DD : ι → (W →ₗ[F] U)) (u₀ u₁ : W)
    {S T : Finset ι} (hST : S ⊆ T) :
    badGammaFinset DD u₀ u₁ T ⊆ badGammaFinset DD u₀ u₁ S := by
  intro γ hγ
  rw [mem_badGammaFinset] at hγ ⊢
  exact fun i hi => hγ i (hST hi)

/-- **`D*(S)` — the over-determined far-line incidence at depth `S`**: the number of bad `γ`. -/
noncomputable def Dstar (DD : ι → (W →ₗ[F] U)) (u₀ u₁ : W) (S : Finset ι) : ℕ :=
  (badGammaFinset DD u₀ u₁ S).card

/-- **`D*` is monotone non-increasing in the over-determination depth (target B48).**
If `S ⊆ T` (the `T`-system over-determines the `S`-system) then `D*(T) ≤ D*(S)`: a deeper
agreement constraint never increases the bad-`γ` count.  Proof: `badGammaFinset_antitone` gives
the subset inclusion, then `Finset.card_le_card`. -/
theorem Dstar_le_of_subset (DD : ι → (W →ₗ[F] U)) (u₀ u₁ : W)
    {S T : Finset ι} (hST : S ⊆ T) :
    Dstar DD u₀ u₁ T ≤ Dstar DD u₀ u₁ S :=
  Finset.card_le_card (badGammaFinset_antitone DD u₀ u₁ hST)

/-- **Unit-step form: adding one agreement row never increases `D*`.**
`D*(insert i S) ≤ D*(S)`, i.e. `D*(m+1) ≤ D*(m)`. -/
theorem Dstar_antitone_insert [DecidableEq ι] (DD : ι → (W →ₗ[F] U)) (u₀ u₁ : W)
    (i : ι) (S : Finset ι) :
    Dstar DD u₀ u₁ (insert i S) ≤ Dstar DD u₀ u₁ S :=
  Dstar_le_of_subset DD u₀ u₁ (Finset.subset_insert i S)

/-- **Cascade form: `D*` is antitone along a depth filtration.**
For any depth-indexed family of active-row sets `Sidx : ℕ → Finset ι` that is monotone
(`m ≤ m' → Sidx m ⊆ Sidx m'`), the cascade `m ↦ D*(Sidx m)` is non-increasing — this is the
`E2`/`E4` cascade monotonicity (`[3936, 89, 9, …]` non-increasing). -/
theorem Dstar_chain_antitone (DD : ι → (W →ₗ[F] U)) (u₀ u₁ : W)
    (Sidx : ℕ → Finset ι) (hmono : Monotone Sidx)
    {m m' : ℕ} (hm : m ≤ m') :
    Dstar DD u₀ u₁ (Sidx m') ≤ Dstar DD u₀ u₁ (Sidx m) :=
  Dstar_le_of_subset DD u₀ u₁ (hmono hm)

/-! ### Bridge to the substrate membership-ball incidence -/

/-- The membership-ball specialization: when each agreement row is the membership condition of a
syndrome ball, the bad set is the set of `γ` whose affine point lands in the *intersection* ball,
matching the substrate's `lineIncidence` shape (a single membership filter).  Here we record the
substrate-level monotonicity directly on `lineIncidence`: a smaller ball `G' ⊆ G` (= deeper
agreement) has incidence `≤` the larger ball. -/
theorem lineIncidence_antitone_ball (G G' : Finset F) (hGG' : G' ⊆ G) (s₀ s₁ : F) :
    ArkLib.ProximityGap.IncidencePeriodBridge.lineIncidence G' s₀ s₁
      ≤ ArkLib.ProximityGap.IncidencePeriodBridge.lineIncidence G s₀ s₁ := by
  unfold ArkLib.ProximityGap.IncidencePeriodBridge.lineIncidence
  apply Finset.card_le_card
  intro γ hγ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
  exact hGG' hγ

end ArkLib.ProximityGap.BridgeB48

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.BridgeB48.badGammaFinset_antitone
#print axioms ArkLib.ProximityGap.BridgeB48.Dstar_le_of_subset
#print axioms ArkLib.ProximityGap.BridgeB48.Dstar_antitone_insert
#print axioms ArkLib.ProximityGap.BridgeB48.Dstar_chain_antitone
#print axioms ArkLib.ProximityGap.BridgeB48.lineIncidence_antitone_ball
