/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Data.ZMod.Basic
import ArkLib.ToMathlib.Combinatorics.Additive.HigherEnergy

/-!
# The sum-product theorem over `ZMod p` (subgroup-energy form)

The **sum-product theorem** of Bourgain–Katz–Tao / Konyagin states that a set `A ⊆ 𝔽_p` that is
not too large cannot be simultaneously additively and multiplicatively structured:

  `max (#(A + A), #(A * A)) ≥ c · #A ^ (1 + δ)`     (for some absolute `δ > 0`).

The case the Bourgain–Glibichuk–Konyagin (BGK) character-sum machinery actually consumes is the
specialization to a **multiplicative subgroup** `H ≤ 𝔽_p^×`. There `#(H * H) = #H` exactly (`H` is
multiplicatively closed), so the multiplicative side gives *no* expansion; the sum-product theorem
forces the *additive* side to expand,

  `#(H + H) ≥ c · #H ^ (1 + δ)`,

and via the Cauchy–Schwarz energy bound `#H ^ 4 ≤ #(H + H) · E[H]` this turns into the
**additive-energy upper bound** BGK needs:

  `E[H] ≤ c⁻¹ · #H ^ (3 - δ)`.

## What is proven here (axiom-clean)

* `MulClosed` — a multiplicatively closed finset (closure under the group operation).
* `MulClosed.mul_self_subset`, `card_le_card_mul_self_of_mulClosed`,
  `card_mul_self_eq_of_mulClosed` — a finite multiplicatively closed nonempty subset of a group
  satisfies `#(H * H) = #H`. (The multiplicative side genuinely does not expand.)
* `card_pow_four_le_card_add_mul_addEnergy` — the Cauchy–Schwarz bridge `#H ^ 4 ≤ #(H + H) · E[H]`,
  i.e. `E[H] ≥ #H ^ 4 / #(H + H)` (a thin restatement of Mathlib's `le_card_add_mul_addEnergy`).
* `card_pow_four_le_card_add_mul_of_addEnergy_le` — the packaged form `E[H] ≤ B ⟹ #H ^ 4 ≤
  #(H + H) · B` (small energy forces a large sumset).
* `card_add_pow_ge_of_energyCore` — the *proven* elementary direction: the energy core and the
  Cauchy–Schwarz bridge together imply a sumset lower bound (closing the energy ⇄ expansion loop).

## What is carried as a named open core (NOT a hidden `sorry`)

* `SumProductExpansionCore` — the deep sum-product expansion for multiplicative subgroups:
  `#(H + H) ≥ #H ^ (1 + δ)` (cleared of division: `#H ^ (k + 1) ≤ Cden · #(H + H) ^ k` with the
  exponent `1 + δ = (k + 1) / k`). This is the AG-flavoured Bourgain–Katz–Tao / Rudnev incidence
  content absent from Mathlib.
* `SubgroupEnergyCore` — the end-product energy bound `E[H] ^ m ≤ Cen · #H ^ (3 m - 1)`
  (`E[H] ≤ Cen ^ (1/m) #H ^ (3 - 1/m)`). It is exposed as its own core because deriving an energy
  *upper* bound from sumset *expansion* runs through Balog–Szemerédi–Gowers, not just Cauchy–Schwarz.
* `subgroup_addEnergy_le` — the conditional theorem delivering the sub-trivial energy bound BGK
  consumes, from `SubgroupEnergyCore`.

The honest convention (mirroring `BalogSzemerediGowers.BSGCore`): the elementary reductions and the
Cauchy–Schwarz bridge are fully proven; the single deep incidence-geometry step is a clearly named
`def … Core : Prop`, consumed only by *conditional* theorems.

## References

* J. Bourgain, N. Katz, T. Tao, *A sum-product estimate in finite fields, and applications* (2004).
* S. V. Konyagin, *A sum-product estimate in fields of prime order* (2003).
* M. Rudnev, *On the number of incidences between points and planes in three dimensions* (2018).
-/

open Finset
open scoped Combinatorics.Additive BigOperators Pointwise

namespace Finset

/-! ## Multiplicatively closed sets and the non-expansion of the product side -/

section MulClosed

variable {α : Type*} [DecidableEq α]

/-- A finset is **multiplicatively closed** when it is closed under the group operation: the product
of two members is again a member. For a multiplicative subgroup `H ≤ G` viewed as a finset this
holds (together with nonemptiness). -/
def MulClosed [Mul α] (H : Finset α) : Prop := ∀ ⦃a⦄, a ∈ H → ∀ ⦃b⦄, b ∈ H → a * b ∈ H

variable [Group α] {H : Finset α}

/-- A multiplicatively closed set has `H * H ⊆ H`. -/
lemma MulClosed.mul_self_subset (hH : MulClosed H) : H * H ⊆ H := by
  intro x hx
  rw [mem_mul] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact hH ha hb

/-- Lower bound `#H ≤ #(H * H)` for a nonempty multiplicatively closed set: left translation
`y ↦ h₀ * y` by a fixed `h₀ ∈ H` maps `H` *injectively* into `H * H`. (Injectivity uses only the
group structure; membership in `H * H` uses closure.) -/
lemma card_le_card_mul_self_of_mulClosed (hH : MulClosed H) (hne : H.Nonempty) :
    #H ≤ #(H * H) := by
  obtain ⟨h₀, hh₀⟩ := hne
  apply card_le_card_of_injOn (fun y => h₀ * y)
  · intro y hy
    exact mem_mul.2 ⟨h₀, hh₀, y, hy, rfl⟩
  · intro a _ b _ hab
    exact mul_left_cancel hab

/-- **The product side does not expand.** A nonempty multiplicatively closed subset of a group
satisfies `#(H * H) = #H`: closure gives `H * H ⊆ H` (so `#(H * H) ≤ #H`), and injective left
translation gives `#H ≤ #(H * H)`. This is *why* the sum-product theorem forces the additive side
to carry all the expansion for a multiplicative subgroup. -/
lemma card_mul_self_eq_of_mulClosed (hH : MulClosed H) (hne : H.Nonempty) :
    #(H * H) = #H :=
  le_antisymm (card_le_card hH.mul_self_subset) (card_le_card_mul_self_of_mulClosed hH hne)

end MulClosed

/-! ## The Cauchy–Schwarz bridge between sumset size and additive energy -/

section Bridge

variable {α : Type*} [AddCommGroup α] [DecidableEq α] (H : Finset α)

/-- **Cauchy–Schwarz energy bridge.** For any finset `H` in an abelian group,
`#H ^ 4 ≤ #(H + H) · E[H]`. This is the additive specialization of Mathlib's
`le_card_add_mul_addEnergy` (`#s ^ 2 · #t ^ 2 ≤ #(s + t) · E[s, t]`) at `s = t = H`. Rearranged it
says `E[H] ≥ #H ^ 4 / #(H + H)`: a *small* sumset forces *large* energy.

For the sum-product application we use the contrapositive (`card_pow_four_le_card_add_mul_of_addEnergy_le`
below): *small* energy forces a *large* sumset, hence the additive expansion `#(H+H) ≥ #H^{1+δ}` is
exactly an energy upper bound `E[H] ≤ #H^{3-δ}`. -/
lemma card_pow_four_le_card_add_mul_addEnergy :
    #H ^ 4 ≤ #(H + H) * E[H] := by
  have h := le_card_add_mul_addEnergy H H
  -- `#H ^ 2 * #H ^ 2 ≤ #(H + H) * E[H, H]`, and `H + H = H + H`, `E[H, H] = E[H]`.
  calc #H ^ 4 = #H ^ 2 * #H ^ 2 := by ring
    _ ≤ #(H + H) * E[H] := h

/-- **Sumset lower bound from an energy upper bound (the BGK direction).** If `E[H] ≤ B` and `H` is
nonempty, then `#H ^ 4 ≤ #(H + H) · B`, i.e. `#(H + H) ≥ #H ^ 4 / B`. Concretely: if the additive
energy is small (`B = #H ^ (3 - δ)`), the sumset is large (`#(H+H) ≥ #H ^ (1 + δ)`), and conversely.
This is the algebraic core of the sum-product ↔ energy equivalence; it is fully proven from the
Cauchy–Schwarz bridge. -/
lemma card_pow_four_le_card_add_mul_of_addEnergy_le {B : ℕ} (hB : E[H] ≤ B) :
    #H ^ 4 ≤ #(H + H) * B :=
  (card_pow_four_le_card_add_mul_addEnergy H).trans (Nat.mul_le_mul_left _ hB)

end Bridge

/-! ## The deep sum-product core and the conditional subgroup-energy theorem -/

section SumProduct

/-- **The deep sum-product expansion core**, carried as a named open hypothesis (NOT a hidden
`sorry`). It packages the Bourgain–Katz–Tao / Konyagin sum-product theorem in the form BGK consumes:
for a multiplicative subgroup `H ≤ 𝔽_p^×` that is not too large, the *additive* sumset expands.

We phrase it cleared of division. The expansion exponent `1 + δ` is written `(k + 1) / k` for a
fixed `k ≥ 1` (so `δ = 1 / k > 0`), and the bound `#(H + H) ≥ Cnum⁻¹ #H ^ ((k+1)/k)` becomes the
polynomial inequality

  `#H ^ (k + 1) ≤ Cden · #(H + H) ^ k`.

The size restriction (`#H ≤ p ^ (1 - ε)`, i.e. `H` is a *proper* subgroup bounded away from the
whole field) is bundled as the hypothesis `hsize : #H ≤ sizeBound`. The constants `Cden, k` and the
bound function `sizeBound` are explicit parameters so a downstream discharge (a future Rudnev /
incidence formalization) may fix them; the canonical BKT form has `δ` a small absolute constant.

This is the genuinely AG-heavy content (point–plane incidences / the no-subfield argument) absent
from Mathlib — see `RudnevIncidence.lean`. -/
def SumProductExpansionCore (Cden k : ℕ) (sizeBound : ℕ → ℕ) : Prop :=
  ∀ {p : ℕ} [Fact p.Prime],
    ∀ (H : Finset (ZMod p)), H.Nonempty → MulClosed (H.erase 0) →
      (0 : ZMod p) ∉ H → #H ≤ sizeBound p →
        #H ^ (k + 1) ≤ Cden * #(H + H) ^ k

/-- Restatement of the sum-product core for a fixed subgroup (mere application). -/
theorem card_pow_succ_le_of_core {Cden k : ℕ} {sizeBound : ℕ → ℕ}
    (hcore : SumProductExpansionCore Cden k sizeBound)
    {p : ℕ} [Fact p.Prime] (H : Finset (ZMod p))
    (hne : H.Nonempty) (hclosed : MulClosed (H.erase 0)) (hzero : (0 : ZMod p) ∉ H)
    (hsize : #H ≤ sizeBound p) :
    #H ^ (k + 1) ≤ Cden * #(H + H) ^ k :=
  hcore H hne hclosed hzero hsize

/-- **The deep subgroup additive-energy core**, carried as a named open hypothesis (NOT a hidden
`sorry`). This is the inequality the BGK character-sum machinery actually consumes: the additive
energy of a (bounded) multiplicative subgroup is *sub-trivial*,

  `E[H] ≤ Cen · #H ^ (3 - δ')`     (`δ' > 0`).

Cleared of fractional exponents (writing `3 - δ' = (3 m - 1) / m` for a fixed `m ≥ 1`), this reads

  `E[H] ^ m ≤ Cen · #H ^ (3 * m - 1)`.

**Why this is a separate core and not derivable from `SumProductExpansionCore` here.** The
Cauchy–Schwarz bridge `#H ^ 4 ≤ #(H + H) · E[H]` only *lower*-bounds the energy from a *small*
sumset; turning a sumset *expansion* (`#(H+H)` large) into an energy *upper* bound is the converse
implication, which genuinely runs through Balog–Szemerédi–Gowers (a large energy would, via BSG,
extract a dense subset with a *small* difference set, contradicting sum-product expansion). That
BSG step is itself carried as `BalogSzemerediGowers.BSGCore`. We therefore expose the end-product
energy bound directly as its own named core, the honest convention for a multi-theorem assembly. -/
def SubgroupEnergyCore (Cen m : ℕ) (sizeBound : ℕ → ℕ) : Prop :=
  ∀ {p : ℕ} [Fact p.Prime],
    ∀ (H : Finset (ZMod p)), H.Nonempty → MulClosed (H.erase 0) →
      (0 : ZMod p) ∉ H → #H ≤ sizeBound p →
        E[H] ^ m ≤ Cen * #H ^ (3 * m - 1)

/-- **Subgroup additive-energy upper bound (conditional on the named energy core).**

Given the deep `SubgroupEnergyCore` and the hypotheses that `H ⊆ 𝔽_p` is a nonempty multiplicative
subgroup (`0 ∉ H`, closed under `*`) of bounded size, the additive energy obeys the sub-trivial
bound `E[H] ^ m ≤ Cen · #H ^ (3 m - 1)`, i.e. `E[H] ≤ Cen ^ (1/m) · #H ^ ((3m-1)/m) = #H ^ (3 - 1/m)`
up to the constant — strictly below the trivial `E[H] ≤ #H ^ 3` (`addREnergy_le` at `r = 2` gives
`E[H] ≤ #H ^ 3`). This is the exact input to the BGK character-sum estimate. -/
theorem subgroup_addEnergy_le {Cen m : ℕ} {sizeBound : ℕ → ℕ}
    (hcore : SubgroupEnergyCore Cen m sizeBound)
    {p : ℕ} [Fact p.Prime] (H : Finset (ZMod p))
    (hne : H.Nonempty) (hclosed : MulClosed (H.erase 0)) (hzero : (0 : ZMod p) ∉ H)
    (hsize : #H ≤ sizeBound p) :
    E[H] ^ m ≤ Cen * #H ^ (3 * m - 1) :=
  hcore H hne hclosed hzero hsize

/-- **Sumset lower bound from the energy core (proven elementary direction).**

The *contrapositive* combination of the energy bound and the Cauchy–Schwarz bridge IS elementary:
from `E[H] ^ m ≤ Cen · #H ^ (3 m - 1)` and `#H ^ 4 ≤ #(H + H) · E[H]` one derives a *lower* bound on
the sumset,

  `#H ^ (4 m) ≤ (#(H + H)) ^ m · E[H] ^ m ≤ Cen · (#(H + H)) ^ m · #H ^ (3 m - 1)`,

hence `#(H + H) ^ m · Cen ≥ #H ^ (4 m) / #H ^ (3 m - 1) = #H ^ (m + 1)` (for `m ≥ 1`), i.e.
`#(H + H) ≥ Cen ^ (-1/m) #H ^ ((m+1)/m) = #H ^ (1 + 1/m)`: the energy bound and the sum-product
expansion are equivalent, and this proven derivation closes the loop without re-assuming
`SumProductExpansionCore`. -/
theorem card_add_pow_ge_of_energyCore {Cen m : ℕ} {sizeBound : ℕ → ℕ}
    (hcore : SubgroupEnergyCore Cen m sizeBound)
    {p : ℕ} [Fact p.Prime] (H : Finset (ZMod p)) (hm : 1 ≤ m)
    (hne : H.Nonempty) (hclosed : MulClosed (H.erase 0)) (hzero : (0 : ZMod p) ∉ H)
    (hsize : #H ≤ sizeBound p) :
    #H ^ (4 * m) ≤ Cen * #(H + H) ^ m * #H ^ (3 * m - 1) := by
  -- Cauchy–Schwarz, raised to the `m`-th power.
  have hCS : #H ^ 4 ≤ #(H + H) * E[H] := card_pow_four_le_card_add_mul_addEnergy H
  have hCSk : (#H ^ 4) ^ m ≤ (#(H + H) * E[H]) ^ m := Nat.pow_le_pow_left hCS m
  rw [← pow_mul, mul_pow] at hCSk
  -- hCSk : #H ^ (4 * m) ≤ #(H + H) ^ m * E[H] ^ m
  -- Energy core.
  have hE : E[H] ^ m ≤ Cen * #H ^ (3 * m - 1) :=
    subgroup_addEnergy_le hcore H hne hclosed hzero hsize
  calc #H ^ (4 * m)
      ≤ #(H + H) ^ m * E[H] ^ m := hCSk
    _ ≤ #(H + H) ^ m * (Cen * #H ^ (3 * m - 1)) := by gcongr
    _ = Cen * #(H + H) ^ m * #H ^ (3 * m - 1) := by ring

end SumProduct

end Finset

-- Axiom audit (expected: propext, Classical.choice, Quot.sound)
#print axioms Finset.MulClosed.mul_self_subset
#print axioms Finset.card_le_card_mul_self_of_mulClosed
#print axioms Finset.card_mul_self_eq_of_mulClosed
#print axioms Finset.card_pow_four_le_card_add_mul_addEnergy
#print axioms Finset.card_pow_four_le_card_add_mul_of_addEnergy_le
#print axioms Finset.card_pow_succ_le_of_core
#print axioms Finset.subgroup_addEnergy_le
#print axioms Finset.card_add_pow_ge_of_energyCore
