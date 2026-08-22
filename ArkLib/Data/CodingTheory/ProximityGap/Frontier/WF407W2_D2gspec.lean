/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# WF407-W2 thread D2-gspec — the genuine-E₂-defect g-spectrum carries NO sub-energy localization

**Thread.** #407 wf407-w2/D2-gspec (T09 follow-up). T09 observed that the *product-unit*
`g = x₁·x₂/(y₁·y₂)` of a genuine `E₂` defect (`x₁+x₂ = y₁+y₂`, non-trivial, non-antipodal) lands in
only `4`–`6` clustered values of `μ_n` at `n = 16, 32`, all inside `μ_n`. The *hope*: if the
g-spectrum `G` is `O(1)` independent of `n`, the genuine-defect count re-localizes to a **bounded**
union of dilate-incidences `∑_{g∈G} |μ_n ∩ g·μ_n|` over a fixed small `g`-set — a route *around*
the additive-energy wall.

**Verdict: `refuted` (machine-checked countermodel, `scripts/probes/wf407w2_D2-gspec_*.py`).** The
g-localization is NOT a lever, for two independent reasons surfaced by exact enumeration at
`n = 16, 32, 64, 128, 256`:

1. **`|G|` grows linearly in `n`** (least-squares slope `≈ 0.22`, i.e. `|G| ≈ n/4.5`), **not**
   `O(1)`. The `4`–`6` values at `n = 16, 32` were a small-`n` artifact (a single Galois orbit);
   at `n = 256`, `|G| = 50`–`60` over several primes.
2. **Every `g ∈ G` lies in `μ_n`** (measured at all `n`), so the dilate incidence is **trivial**:
   `g·μ_n = μ_n`, hence `|μ_n ∩ g·μ_n| = |μ_n| = n` for *every* `g`. The "localized incidence"
   carries no localization — each term is the full `n`.

Combining (1)+(2): the localized sum is `∑_{g∈G} |μ_n ∩ g·μ_n| = |G|·n = Θ(n²)` (verified exactly:
`lever == |G|·n` every row), equal to a constant fraction (`≈ 1/4`) of the full additive-energy
excess. It **recovers** the energy scale; it does not beat it. The genuine count is `Θ(|G|·n) =
Θ(n²) = Θ(excess)` (`excess/genuine ≈ 8`, constant). The g-spectrum just re-indexes the energy
excess by its dominant dilate frequencies, all of which are in `μ_n` — exactly Cauchy–Schwarz.

**What this Lean file proves (axiom-clean).** The decisive *algebraic* fact behind reason (2): a
subgroup dilated by one of its own elements returns the subgroup, so a self-dilate incidence is the
full order. Formalized in full generality below (`Subgroup.smul_self`,
`selfDilate_incidence_eq_card`): for any group `H` and `g ∈ H`, `g • (H : Set) = H`, hence the
"dilate incidence" `|H ∩ g•H| = |H|`. This is exactly why the g-localization (whose `G ⊆ μ_n`)
gives `|μ_n ∩ g·μ_n| = n` per term and therefore `Θ(n²)` total — it cannot localize below the
energy. **No bound below the wall is claimed; the bound is recovered, not beaten.**

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArkLib.ProximityGap.WF407W2.D2gspec

open scoped Pointwise

/-! ## §1  A subgroup dilated by one of its own elements is itself (the no-localization core). -/

/-- **Self-dilate stability (set form).** For a subgroup `H` of a group `G` and `g ∈ H`, the
pointwise left translate `g • (H : Set G)` equals `(H : Set G)`. This is the algebraic reason the
genuine-`E₂`-defect "dilate incidence" `|μ_n ∩ g·μ_n|` is the *full* order `|μ_n| = n` (no
localization) whenever the product-unit `g` lies in `μ_n` — which the probes measured for the
entire g-spectrum at every `n`. -/
theorem Subgroup.smul_self {G : Type*} [Group G] (H : Subgroup G) {g : G} (hg : g ∈ H) :
    g • (H : Set G) = (H : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact H.mul_mem hg hy
  · intro hx
    refine ⟨g⁻¹ * x, H.mul_mem (H.inv_mem hg) hx, ?_⟩
    simp [mul_inv_cancel_left]

/-- **The dilate incidence equals the full subgroup (intersection form).** For `g ∈ H`,
`(g • (H : Set G)) ∩ (H : Set G) = (H : Set G)`: the self-dilate intersection is the whole
subgroup. Numerically: `|μ_n ∩ g·μ_n| = |μ_n|`. -/
theorem selfDilate_inter_eq {G : Type*} [Group G] (H : Subgroup G) {g : G} (hg : g ∈ H) :
    (g • (H : Set G)) ∩ (H : Set G) = (H : Set G) := by
  rw [Subgroup.smul_self H hg, Set.inter_self]

/-- **The dilate incidence equals the full order (finite Finset form).** For a finite subgroup-as-
`Finset` closed under multiplication by `g` (i.e. `g`-translation maps it into itself), the dilate
incidence `|s ∩ g•s| = |s|`. This is the per-term value in `∑_{g∈G}|μ_n ∩ g·μ_n|`: with every
`g ∈ μ_n`, each term is `n`, so the sum is `|G|·n` — no sub-energy localization. -/
theorem selfDilate_card_eq {G : Type*} [Group G] [DecidableEq G]
    (s : Finset G) (g : G)
    (hstab : ∀ x ∈ s, g * x ∈ s) (hsurj : ∀ y ∈ s, g⁻¹ * y ∈ s) :
    (s.image (fun x => g * x) ∩ s).card = s.card := by
  have himg : s.image (fun x => g * x) = s := by
    apply Finset.Subset.antisymm
    · intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      exact hstab x hx
    · intro y hy
      refine Finset.mem_image.mpr ⟨g⁻¹ * y, hsurj y hy, ?_⟩
      simp [mul_inv_cancel_left]
  rw [himg, Finset.inter_self]

/-! ## §2  The localized sum is `|G|·n` (named identity; the refutation lever). -/

/-- **Localized-sum identity (the refutation, abstract form).** If every `g` in a finite index set
`G` self-dilates the subgroup-Finset `s` to itself (incidence `= |s|`), then the localized sum
`∑_{g∈G} |s ∩ g•s| = |G|·|s|`. With the measured facts `G ⊆ μ_n` (so the hypothesis holds) and
`|G| = Θ(n)`, `|s| = n`, this is `Θ(n²)` — the additive-energy scale. The g-localization recovers
the energy, it does not beat it. -/
theorem localizedSum_eq_card_mul_card {G : Type*} [Group G] [DecidableEq G]
    (s : Finset G) (Gset : Finset G)
    (hstab : ∀ g ∈ Gset, ∀ x ∈ s, g * x ∈ s)
    (hsurj : ∀ g ∈ Gset, ∀ y ∈ s, g⁻¹ * y ∈ s) :
    ∑ g ∈ Gset, (s.image (fun x => g * x) ∩ s).card = Gset.card * s.card := by
  rw [Finset.sum_congr rfl (fun g hg => selfDilate_card_eq s g (hstab g hg) (hsurj g hg))]
  rw [Finset.sum_const, smul_eq_mul]

end ArkLib.ProximityGap.WF407W2.D2gspec

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.WF407W2.D2gspec
#print axioms Subgroup.smul_self
#print axioms selfDilate_inter_eq
#print axioms selfDilate_card_eq
#print axioms localizedSum_eq_card_mul_card
end AxiomAudit
