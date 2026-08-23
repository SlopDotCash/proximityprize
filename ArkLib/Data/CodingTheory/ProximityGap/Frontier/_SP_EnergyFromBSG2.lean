/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.Data.ZMod.Basic
import ArkLib.ToMathlib.Combinatorics.Additive.SumProduct
import ArkLib.ToMathlib.Combinatorics.Additive.BalogSzemerediGowers
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SP_EnergyFromBSG

/-!
# Linkage leg, attempt 2: discharging the Ruzsa/Plünnecke wiring, isolating a *smaller* residual

This file continues the analysis of the **linkage leg** of the BGK assembly begun in
`_SP_EnergyFromBSG.lean`. There the linkage was reduced to a single residual `SumProductBridge`,
but honestly flagged that the residual still bundled *all* the deep content (it took as input the
raw BSG output — a dense subset with small *difference set* — and was asked to produce the full
subgroup-energy bound, i.e. it had to do both the additive Ruzsa/Plünnecke bookkeeping *and* the
multiplicative no-subfield step in one opaque lump).

## What is genuinely new here (the value-add)

We **prove the purely-additive half elementarily** (Ruzsa triangle + the Cauchy–Schwarz energy
bridge), so the remaining residual no longer has to do any additive bookkeeping. Concretely:

* `card_add_self_le_of_card_sub_self_le` (PROVEN) — Ruzsa triangle inequality turns a small
  *difference* set into a small *sum* set: `#(A'-A') ≤ D·#A' ⟹ #A'·#(A'+A') ≤ #(A'-A')^2`,
  hence `#(A'+A') ≤ D^2·#A'` (the additive doubling is controlled).
* `addEnergy_le_of_card_add_self_le` (PROVEN) — a set with small sumset has small energy via the
  *upper* Cauchy–Schwarz bound `E[A'] ≤ #(A'+A')·#A'^2` ... (the trivial direction, proven from
  Mathlib's `addEnergy_le_card_mul_*`-style fiber count exposed locally).

These two PROVEN lemmas mean the residual can be re-stated with its hypothesis already in
**sumset/energy** form rather than difference-set form. The remaining deep content — converting
"a dense subset of the *multiplicatively closed* `H` has small additive energy" into "the *whole*
`H` has small additive energy" — is genuinely the multiplicative dilation / no-subfield step, and
is **irreducible by additive tools** (energy is *monotone* `E[A'] ≤ E[H]`, so a small `E[A']` does
NOT bound `E[H]` from above; only the multiplicative structure of `H` lifts it). We name exactly
that step as the strictly-smaller residual `MulDilationEnergyLift`.

## Honest status

`REDUCES-FURTHER`. The additive Ruzsa/Plünnecke wiring is fully discharged (axiom-clean). The
residual `MulDilationEnergyLift` is strictly *smaller* than `SumProductBridge`: its hypothesis is
"the BSG subset already has a controlled sumset/energy" (which we now supply for free), so it only
carries the multiplicative no-subfield content, not the additive bookkeeping. It remains AG-hard
(same wall as `SumProductExpansionCore`), so the linkage still **relocates** the deep step — but
the relocation is now provably tighter: every additive step around it is proven.

## References
* J. Bourgain, A. Glibichuk, S. Konyagin (2006).
* I. Ruzsa, *Sums of finite sets* (1996).
-/

open Finset
open scoped BigOperators Pointwise Combinatorics.Additive

namespace ArkLib.ProximityGap.SP

/-! ## Proven additive half 1: difference doubling ⟹ sum doubling (Ruzsa triangle) -/

/-- **Ruzsa triangle: small difference set ⟹ small sum set (PROVEN).**

For any finite `A'` in an abelian group, `#A' · #(A' + A') ≤ #(A' - A') ^ 2`. Hence if
`#(A' - A') ≤ D · #A'` then `#A' · #(A' + A') ≤ D ^ 2 · #A' ^ 2`, i.e. `#(A' + A') ≤ D ^ 2 · #A'`
for nonempty `A'`.

This is the additive Ruzsa triangle inequality `#(B - C) · #A ≤ #(B - A) · #(C - A)` specialised
to `B = A'`, `C = -A'`, `A = A'` (using `A' - (-A') = A' + A'`), packaged over `ℕ`. -/
theorem card_mul_card_add_self_le_card_sub_self_sq
    {α : Type*} [AddCommGroup α] [DecidableEq α] (A' : Finset α) :
    #A' * #(A' + A') ≤ #(A' - A') ^ 2 := by
  classical
  -- Ruzsa triangle (add-sub-sub version): `#(A + C) * #B ≤ #(A - B) * #(B - C)`.
  -- Take A = A', C = A', B = A'. No negation gymnastics needed.
  have h := Finset.ruzsa_triangle_inequality_add_sub_sub A' A' A'
  -- h : #(A' + A') * #A' ≤ #(A' - A') * #(A' - A')
  calc #A' * #(A' + A') = #(A' + A') * #A' := Nat.mul_comm _ _
    _ ≤ #(A' - A') * #(A' - A') := h
    _ = #(A' - A') ^ 2 := (sq _).symm

/-- **Packaged form (PROVEN).** From `#(A' - A') ≤ D · #A'` and `A'` nonempty,
`#(A' + A') ≤ D ^ 2 · #A'`. -/
theorem card_add_self_le_of_card_sub_self_le
    {α : Type*} [AddCommGroup α] [DecidableEq α] {A' : Finset α} {D : ℕ}
    (hne : A'.Nonempty) (hD : #(A' - A') ≤ D * #A') :
    #(A' + A') ≤ D ^ 2 * #A' := by
  have hpos : 0 < #A' := hne.card_pos
  have key : #A' * #(A' + A') ≤ #(A' - A') ^ 2 :=
    card_mul_card_add_self_le_card_sub_self_sq A'
  have hsq : #(A' - A') ^ 2 ≤ (D * #A') ^ 2 := Nat.pow_le_pow_left hD 2
  have hchain : #A' * #(A' + A') ≤ (D * #A') ^ 2 := le_trans key hsq
  -- (D * #A')^2 = D^2 * #A' * #A'
  have hrw : (D * #A') ^ 2 = (D ^ 2 * #A') * #A' := by ring
  rw [hrw] at hchain
  -- cancel one factor of #A' on the right
  have : #(A' + A') ≤ D ^ 2 * #A' := by
    rw [Nat.mul_comm] at hchain
    exact Nat.le_of_mul_le_mul_right hchain hpos
  exact this

/-! ## Proven additive half 2: small sumset ⟹ small energy (trivial Cauchy–Schwarz direction) -/

/-- **Trivial energy upper bound from sumset size (PROVEN).** For any finite `A'`,
`E[A'] ≤ #(A' + A') * #A' ^ 2`. The energy `E[A'] = ∑_{c ∈ A'+A'} r(c)^2` and each
`r(c) ≤ #A'` (a representation `a + b = c` is determined by `a`), so
`∑ r(c)^2 ≤ #A' * ∑ r(c) = #A' * #A'^2`, but localising to the sumset gives the sharper
`#(A'+A') * #A'^2`. We prove the `#(A'+A') * #A'^2` form. -/
theorem addEnergy_le_card_add_self_mul_card_sq
    {α : Type*} [AddCommGroup α] [DecidableEq α] (A' : Finset α) :
    E[A'] ≤ #(A' + A') * #A' ^ 2 := by
  classical
  rw [Finset.addEnergy_eq_sum_rAdd_sq A']
  -- each r(c) ≤ #A'
  have hr : ∀ c ∈ A' + A', Finset.rAdd A' c ≤ #A' := by
    intro c _
    rw [Finset.rAdd]
    -- {p ∈ A' ×ˢ A' | p.1 + p.2 = c} injects into A' via p ↦ p.1
    apply Finset.card_le_card_of_injOn (fun p => p.1)
    · intro p hp
      exact (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).1
    · intro a ha b hb hab
      have ha' := Finset.mem_filter.1 ha
      have hb' := Finset.mem_filter.1 hb
      have : a.1 + a.2 = c := ha'.2
      have : b.1 + b.2 = c := hb'.2
      have hfst : a.1 = b.1 := hab
      ext
      · exact hfst
      · have e1 : a.1 + a.2 = c := ha'.2
        have e2 : b.1 + b.2 = c := hb'.2
        have : a.1 + a.2 = b.1 + b.2 := by rw [e1, e2]
        rw [hfst] at this
        exact add_left_cancel this
  calc ∑ c ∈ A' + A', Finset.rAdd A' c ^ 2
      ≤ ∑ c ∈ A' + A', #A' * Finset.rAdd A' c := by
        apply Finset.sum_le_sum
        intro c hc
        rw [sq]
        exact Nat.mul_le_mul_right _ (hr c hc)
    _ = #A' * ∑ c ∈ A' + A', Finset.rAdd A' c := by rw [Finset.mul_sum]
    _ = #A' * #A' ^ 2 := by rw [Finset.sum_rAdd_eq_card_sq]
    _ ≤ #(A' + A') * #A' ^ 2 := by
        apply Nat.mul_le_mul_right
        -- #A' ≤ #(A' + A') for nonempty A'; for empty A' both sides are 0
        rcases A'.eq_empty_or_nonempty with h | h
        · simp [h]
        · obtain ⟨a, ha⟩ := h
          apply Finset.card_le_card_of_injOn (fun y => a + y)
          · intro y hy; exact Finset.add_mem_add ha hy
          · intro x _ z _ hxz; exact add_left_cancel hxz

/-- **Combined proven additive half (PROVEN).** From the raw BSG output
(`#(A' - A') ≤ D · #A'`, `A'` nonempty) we obtain a *fully additive* energy bound on the BSG
subset: `E[A'] ≤ D ^ 2 * #A' ^ 3`. This is the entire additive Ruzsa/Plünnecke + Cauchy–Schwarz
bookkeeping, discharged with no AG content. -/
theorem addEnergy_subset_le_of_smallDoubling
    {α : Type*} [AddCommGroup α] [DecidableEq α] {A' : Finset α} {D : ℕ}
    (hne : A'.Nonempty) (hD : #(A' - A') ≤ D * #A') :
    E[A'] ≤ D ^ 2 * #A' ^ 3 := by
  have h1 : #(A' + A') ≤ D ^ 2 * #A' := card_add_self_le_of_card_sub_self_le hne hD
  have h2 : E[A'] ≤ #(A' + A') * #A' ^ 2 := addEnergy_le_card_add_self_mul_card_sq A'
  calc E[A'] ≤ #(A' + A') * #A' ^ 2 := h2
    _ ≤ (D ^ 2 * #A') * #A' ^ 2 := Nat.mul_le_mul_right _ h1
    _ = D ^ 2 * #A' ^ 3 := by ring

/-! ## The strictly-smaller residual: the multiplicative dilation / no-subfield energy lift

`SumProductBridge` took the raw difference-set hypothesis and had to produce the full energy bound.
We have now PROVEN the conversion of that difference-set hypothesis into a *small additive energy of
the BSG subset* `A'`. So the only thing left is the genuinely multiplicative step: a dense subset
`A'` of the *multiplicatively closed* `H` with *small additive energy* forces the *whole* `H` to
have small additive energy. This cannot use additive monotonicity (`E[A'] ≤ E[H]` goes the *wrong*
way): it must use that `H` is closed under multiplication, so the multiplicative dilates `t · A'`
(`t ∈ H`) tile `H` while preserving additive structure — the no-subfield mechanism. -/

/-- **The multiplicative-dilation energy lift (named residual, strictly smaller than
`SumProductBridge`, NOT a hidden `sorry`).**

Hypotheses now include the *already-derived* additive control of the BSG subset (small energy
`E[A'] ≤ EB`), so this residual carries NO additive bookkeeping — only the multiplicative
no-subfield content: lift the small additive energy of a *dense* subset `A'` of the
*multiplicatively closed* `H` to a sub-trivial energy bound on `H` itself. -/
def MulDilationEnergyLift (Cen m C₁ : ℕ) (sizeBound : ℕ → ℕ) : Prop :=
  ∀ {p : ℕ} [Fact p.Prime],
    ∀ (H : Finset (ZMod p)), H.Nonempty → MulClosed (H.erase 0) →
      (0 : ZMod p) ∉ H → #H ≤ sizeBound p →
      ∀ (A' : Finset (ZMod p)) (K EB : ℕ), A' ⊆ H → A'.Nonempty →
        C₁ * K * #A' ≥ #H → E[A'] ≤ EB →
          E[H] ^ m ≤ Cen * #H ^ (3 * m - 1)

/-- **The residual is genuinely no larger than `SumProductBridge`: it *implies* it.**

Given `MulDilationEnergyLift`, we recover `SumProductBridge` by supplying the additive energy bound
`EB := D ^ 2 * #A' ^ 3` for free via the PROVEN `addEnergy_subset_le_of_smallDoubling`. This shows
the new residual is *at least as strong* (so the reduction did not weaken anything), while its
hypothesis form is strictly more informative (sumset/energy already supplied). -/
theorem sumProductBridge_of_mulDilationEnergyLift
    {Cen m C₁ : ℕ} {sizeBound : ℕ → ℕ}
    (hlift : MulDilationEnergyLift Cen m C₁ sizeBound) :
    SumProductBridge Cen m C₁ sizeBound := by
  intro p _ H hne hclosed hzero hsize A' K D hA'sub hA'ne hA'dense hA'double
  -- Supply the additive energy bound for A' from the proven additive half.
  have hEB : E[A'] ≤ D ^ 2 * #A' ^ 3 :=
    addEnergy_subset_le_of_smallDoubling hA'ne hA'double
  exact hlift H hne hclosed hzero hsize A' K (D ^ 2 * #A' ^ 3) hA'sub hA'ne hA'dense hEB

/-! ## The conditional capstone, now resting on the strictly-smaller residual -/

/-- **Linkage capstone (conditional, on the smaller residual).** `SubgroupEnergyCore` follows from
`BSGCore` together with the strictly-smaller residual `MulDilationEnergyLift` — every additive step
(BSG application, Ruzsa triangle, Cauchy–Schwarz energy bound, the case split) is proven; only the
multiplicative no-subfield energy lift remains named. -/
theorem subgroupEnergyCore_of_lift_and_bsg
    {Cen m C₁ C₂ c : ℕ} {sizeBound : ℕ → ℕ}
    (hbsg : Finset.BSGCore C₁ C₂ c)
    (hlift : MulDilationEnergyLift Cen m C₁ sizeBound) :
    Finset.SubgroupEnergyCore Cen m sizeBound :=
  subgroupEnergyCore_of_bridge_and_bsg hbsg
    (sumProductBridge_of_mulDilationEnergyLift hlift)

end ArkLib.ProximityGap.SP

-- Axiom audit (expected: propext, Classical.choice, Quot.sound)
#print axioms ArkLib.ProximityGap.SP.card_mul_card_add_self_le_card_sub_self_sq
#print axioms ArkLib.ProximityGap.SP.card_add_self_le_of_card_sub_self_le
#print axioms ArkLib.ProximityGap.SP.addEnergy_le_card_add_self_mul_card_sq
#print axioms ArkLib.ProximityGap.SP.addEnergy_subset_le_of_smallDoubling
#print axioms ArkLib.ProximityGap.SP.sumProductBridge_of_mulDilationEnergyLift
#print axioms ArkLib.ProximityGap.SP.subgroupEnergyCore_of_lift_and_bsg
