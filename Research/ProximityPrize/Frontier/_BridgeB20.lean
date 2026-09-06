/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge
import Mathlib.Data.Finset.Powerset

/-!
# Bridge B20 (target E4) — `D*(1) ≤ C(n, k+1)` on the substrate `lineIncidence`

**Spec B20 / E4** (kb `deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`). The leading
rung of the binding cascade is `D*(1) ≈ n³` (`ρ = 1/4`, n=16: `3936 ≈ 16³`). Its elementary
*combinatorial ceiling* — the content of this bridge — is

  `D*(1)  ≤  C(n, k+1)`,

"each `(k+1)`-subset of the evaluation domain yields at most one bad scalar `γ`".

**What is fresh here vs. an abstract counting brick.** This file states the ceiling **directly
about the substrate object** `IncidencePeriodBridge.lineIncidence G s₀ s₁`, i.e. about the actual
far-line incidence count `#{γ : F | s₀ + γ·s₁ ∈ G}` defined in
`IncidencePeriodBridge.lean` (substrate P2). The bad-`γ` set is therefore not an opaque
`B : Finset γ` but the concrete `Finset.univ.filter (fun γ => s₀ + γ·s₁ ∈ G)` that `lineIncidence`
is the cardinality of. The bridge says: any support map that is injective on *that* filter and
lands in the `(k+1)`-subsets caps the incidence by `C(n, k+1)`.

**The geometric input (taken as hypotheses, the over-determination pin).** A bad `γ` witnesses a
degree-`<k` codeword of `RS[k]` whose agreement set with the syndrome, at over-determination depth
`m = 1`, has size `k+1`. A degree-`<k` polynomial is pinned by any `k` of those points, so the
size-`(k+1)` agreement support **determines** the codeword, hence `γ`: the support map is injective
on the bad set. These two facts (size-`(k+1)`; injectivity) are the geometry and are supplied as
hypotheses `hsize`, `hinj`; the bridge is the clean counting closure into `C(n, k+1)`.

Two forms are proved:

* `lineIncidence_le_card_powersetCard` — over an arbitrary domain `Finset F` containing `G`'s
  evaluation points, against `powersetCard (k+1) domain`.
* `lineIncidence_le_choose` — the closed form `lineIncidence ≤ C(|domain|, k+1)`, and (specialized
  to `domain = univ`, `n = |F|`) `lineIncidence ≤ C(n, k+1)` — the E4 leading-rung ceiling literally.

Axiom-clean; consumes `IncidencePeriodBridge.lineIncidence` and pure
`Finset.card_le_card_of_injOn` + `card_powersetCard`. Issue #444.
-/

open Finset
open ArkLib.ProximityGap.IncidencePeriodBridge

namespace ArkLib.ProximityGap.BridgeB20

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The bad-`γ` set whose cardinality **is** `lineIncidence G s₀ s₁` (substrate P2):
`{γ ∈ F | s₀ + γ·s₁ ∈ G}`. Naming it lets the counting closure speak about the substrate's own
incidence object rather than an abstract finset. -/
noncomputable def badGammaSet (G : Finset F) (s₀ s₁ : F) : Finset F :=
  Finset.univ.filter (fun γ : F => s₀ + γ * s₁ ∈ G)

/-- The named bad set has cardinality exactly the substrate `lineIncidence`. (Definitional, but we
record it so the ceiling below is *visibly* a bound on `lineIncidence`.) -/
theorem card_badGammaSet (G : Finset F) (s₀ s₁ : F) :
    (badGammaSet G s₀ s₁).card = lineIncidence G s₀ s₁ := rfl

/-- **B20 / E4 — the depth-one ceiling on the substrate incidence (powerset form).**

Let `domain : Finset pt` be the (size-`n`) evaluation index domain and
`supp : F → Finset pt` the agreement-support map. Suppose every bad scalar
`γ ∈ badGammaSet G s₀ s₁` (i.e. every `γ` counted by `lineIncidence G s₀ s₁`) has agreement support
a size-`(k+1)` subset of `domain` (`hsub`, `hsize`) and that `supp` is **injective on the bad set**
(`hinj`, the over-determination pin). Then

  `lineIncidence G s₀ s₁ ≤ #(powersetCard (k+1) domain) = C(n, k+1)`.

This is exactly "each `(k+1)`-subset yields at most one bad `γ`", now applied to the substrate
far-line incidence. -/
theorem lineIncidence_le_card_powersetCard {pt : Type*}
    (G : Finset F) (s₀ s₁ : F) (domain : Finset pt) (supp : F → Finset pt) (k : ℕ)
    (hsub : ∀ γ ∈ badGammaSet G s₀ s₁, supp γ ⊆ domain)
    (hsize : ∀ γ ∈ badGammaSet G s₀ s₁, (supp γ).card = k + 1)
    (hinj : Set.InjOn supp (badGammaSet G s₀ s₁ : Set F)) :
    lineIncidence G s₀ s₁ ≤ (domain.powersetCard (k + 1)).card := by
  rw [← card_badGammaSet G s₀ s₁]
  refine Finset.card_le_card_of_injOn supp ?_ hinj
  intro γ hγ
  rw [mem_coe, mem_powersetCard]
  exact ⟨hsub γ hγ, hsize γ hγ⟩

/-- **B20 / E4 — the closed-form ceiling on the substrate incidence.**  Same hypotheses, with the
right side as the binomial coefficient `C(|domain|, k+1)`. -/
theorem lineIncidence_le_choose {pt : Type*}
    (G : Finset F) (s₀ s₁ : F) (domain : Finset pt) (supp : F → Finset pt) (k : ℕ)
    (hsub : ∀ γ ∈ badGammaSet G s₀ s₁, supp γ ⊆ domain)
    (hsize : ∀ γ ∈ badGammaSet G s₀ s₁, (supp γ).card = k + 1)
    (hinj : Set.InjOn supp (badGammaSet G s₀ s₁ : Set F)) :
    lineIncidence G s₀ s₁ ≤ Nat.choose domain.card (k + 1) := by
  have h := lineIncidence_le_card_powersetCard G s₀ s₁ domain supp k hsub hsize hinj
  rwa [card_powersetCard] at h

/-- **B20 / E4 — the cascade form `D*(1) ≤ C(n, k+1)`.**  Specializing the domain to the full
index set `Fin n` (the `n`-point evaluation domain) and naming `D = lineIncidence G s₀ s₁`,
`n = |Fin n|`, the over-determination injection gives the E4 leading-rung ceiling literally:

  `D*(1) = lineIncidence G s₀ s₁ ≤ Nat.choose n (k + 1)`.

No `⊆ domain` hypothesis is needed: every subset of `Fin n` lies in `univ`. -/
theorem Dstar1_le_choose {n : ℕ}
    (G : Finset F) (s₀ s₁ : F) (supp : F → Finset (Fin n)) (k D : ℕ)
    (hD : D = lineIncidence G s₀ s₁)
    (hsize : ∀ γ ∈ badGammaSet G s₀ s₁, (supp γ).card = k + 1)
    (hinj : Set.InjOn supp (badGammaSet G s₀ s₁ : Set F)) :
    D ≤ Nat.choose n (k + 1) := by
  subst hD
  have h := lineIncidence_le_choose G s₀ s₁ (Finset.univ : Finset (Fin n)) supp k
    (fun γ _ => Finset.subset_univ _) hsize hinj
  rwa [Finset.card_univ, Fintype.card_fin] at h

/-- **Concrete sanity instance.**  `n = 16`, `k = 4`: the depth-one ceiling is `C(16,5) = 4368`,
which dominates the measured leading rung `D*(1) = 3936` of the n=16 cascade (E2/E4). -/
example : (3936 : ℕ) ≤ Nat.choose 16 5 := by decide

end ArkLib.ProximityGap.BridgeB20

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BridgeB20.card_badGammaSet
#print axioms ArkLib.ProximityGap.BridgeB20.lineIncidence_le_card_powersetCard
#print axioms ArkLib.ProximityGap.BridgeB20.lineIncidence_le_choose
#print axioms ArkLib.ProximityGap.BridgeB20.Dstar1_le_choose
