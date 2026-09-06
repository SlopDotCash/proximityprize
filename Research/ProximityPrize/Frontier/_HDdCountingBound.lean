/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (standalone issue #1)
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Span.Basic

/-!
# HDd — the block-diagonal counting rank bound

The generic linear algebra behind the counting certificates of
`scripts/probes/hdinf_cap_search.py` / `hdspec_search.py` / `hd_fast_bound.py`: if a family of
vectors `Φ i : ρ → F` is block-supported — column `i` of block `β i` is supported on rows `r`
with `β' r = β i` — then

    rank (span Φ) ≤ Σ_b min |β⁻¹ b| |β'⁻¹ b|.

The probes compute exactly the right-hand side (with `β, β'` the `(g₁, g₂)` invariants of the
hidden-derivative node substitution and over-counting supersets of the realizable rows, which
only increases the bound), so this lemma is the missing formal link between an integer
certificate `dim > n · Σ min(rows, cols)` and the rank hypothesis of `exists_interpolant_d`.
The remaining (bookkeeping) step, not in this file, is the invariance lemma for
`contactSubstD` that exhibits `β, β'` for the concrete node maps.

Everything is field-uniform: no characteristic enters, matching the field-independence of the
counting certificates.
-/

namespace ArkLib.ProximityGap.Frontier.HD1Contact

open Module Submodule

variable {F : Type*} [Field F]

section Main

variable {ι ρ B : Type*} [Fintype ι] [Fintype ρ] [DecidableEq B] [DecidableEq ρ]

/-- Functions `ρ → F` vanishing off a finset `s`. -/
def supportedOn (s : Finset ρ) : Submodule F (ρ → F) where
  carrier := {f | ∀ r, r ∉ s → f r = 0}
  add_mem' hf hg r hr := by simp [hf r hr, hg r hr]
  zero_mem' r _ := rfl
  smul_mem' c f hf r hr := by simp [hf r hr]

theorem finrank_supportedOn_le (s : Finset ρ) :
    finrank F (supportedOn (F := F) s) ≤ s.card := by
  classical
  have hinj : Function.Injective
      ((LinearMap.funLeft F F (Subtype.val : {r // r ∈ s} → ρ)).comp
        (supportedOn (F := F) s).subtype) := by
    intro f g hfg
    ext r
    by_cases hr : r ∈ s
    · exact congrFun hfg ⟨r, hr⟩
    · rw [f.2 r hr, g.2 r hr]
  calc finrank F (supportedOn (F := F) s)
      ≤ finrank F ({r // r ∈ s} → F) := LinearMap.finrank_le_finrank_of_injective hinj
    _ = s.card := by simp

/-- The span of finitely many vectors supported on `s` has rank at most `min #vectors #s`. -/
theorem finrank_span_image_le_min (Φ : ι → ρ → F) (t : Finset ι) (s : Finset ρ)
    (hsupp : ∀ i ∈ t, ∀ r, r ∉ s → Φ i r = 0) :
    finrank F (span F (Φ '' t)) ≤ min t.card s.card := by
  classical
  refine le_min ?_ ?_
  · calc finrank F (span F (Φ '' t)) ≤ (t.image Φ).card := by
          simpa [Finset.coe_image] using finrank_span_finset_le_card (t.image Φ)
      _ ≤ t.card := Finset.card_image_le
  · have hle : span F (Φ '' t) ≤ supportedOn (F := F) s := by
      rw [span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact fun r hr => hsupp i (by simpa using hi) r hr
    calc finrank F (span F (Φ '' t)) ≤ finrank F (supportedOn (F := F) s) :=
          Submodule.finrank_mono hle
      _ ≤ s.card := finrank_supportedOn_le s

/-- Rank of a finite sup is at most the sum of the ranks. -/
theorem finrank_finset_sup_le {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {γ : Type*} [DecidableEq γ] (u : Finset γ)
    (p : γ → Submodule F V) :
    finrank F ↥(u.sup p) ≤ ∑ b ∈ u, finrank F ↥(p b) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert a u ha ih =>
    rw [Finset.sup_insert, Finset.sum_insert ha]
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (p a) (u.sup p)
    omega

/-- **The block-diagonal counting rank bound.**  If column `i` is supported on the rows of its
block (`β' r ≠ β i → Φ i r = 0`), then the rank of the span of all columns is at most
`Σ_b min |β⁻¹ b| |β'⁻¹ b|`, summed over the blocks that occur. -/
theorem finrank_span_range_le_sum_min (Φ : ι → ρ → F) (β : ι → B) (β' : ρ → B)
    (hsupp : ∀ i r, β' r ≠ β i → Φ i r = 0) :
    finrank F (span F (Set.range Φ)) ≤
      ∑ b ∈ Finset.univ.image β,
        min (Finset.univ.filter (fun i => β i = b)).card
            (Finset.univ.filter (fun r => β' r = b)).card := by
  classical
  have hspan_le : span F (Set.range Φ) ≤
      (Finset.univ.image β).sup
        (fun b => span F (Φ '' (Finset.univ.filter (fun i => β i = b)))) := by
    rw [span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : Φ i ∈ span F (Φ '' (Finset.univ.filter (fun i' => β i' = β i))) :=
      subset_span ⟨i, by simp, rfl⟩
    exact Finset.le_sup (f := fun b => span F (Φ '' (Finset.univ.filter (fun i' => β i' = b))))
      (Finset.mem_image_of_mem β (Finset.mem_univ i)) h1
  calc finrank F (span F (Set.range Φ))
      ≤ finrank F ↥((Finset.univ.image β).sup
          (fun b => span F (Φ '' (Finset.univ.filter (fun i => β i = b))))) :=
        Submodule.finrank_mono hspan_le
    _ ≤ ∑ b ∈ Finset.univ.image β,
          finrank F ↥(span F (Φ '' (Finset.univ.filter (fun i => β i = b)))) :=
        finrank_finset_sup_le _ _
    _ ≤ ∑ b ∈ Finset.univ.image β,
          min (Finset.univ.filter (fun i => β i = b)).card
              (Finset.univ.filter (fun r => β' r = b)).card := by
        refine Finset.sum_le_sum fun b _ => ?_
        refine finrank_span_image_le_min Φ _ _ ?_
        intro i hi r hr
        refine hsupp i r ?_
        have hib : β i = b := by simpa using (Finset.mem_filter.mp hi).2
        intro hcontra
        exact hr (by simp [hcontra, hib])

end Main

section Restriction

variable {ι ρ' : Type*} [Fintype ι]

/-- Functions `ρ' → F` vanishing off a finset (no finiteness of `ρ'` required). -/
def supportedOn' (s : Finset ρ') : Submodule F (ρ' → F) where
  carrier := {f | ∀ r, r ∉ s → f r = 0}
  add_mem' hf hg r hr := by simp [hf r hr, hg r hr]
  zero_mem' r _ := rfl
  smul_mem' c f hf r hr := by simp [hf r hr]

/-- **Restriction preserves rank.**  A family of vectors supported on a finite row set `R`
has the same span rank as its restriction to `R`; this reduces the (infinite-index) node
maps to the finite-row setting of `finrank_span_range_le_sum_min`. -/
theorem finrank_span_range_eq_restrict [DecidableEq ρ'] (Φ : ι → ρ' → F) (R : Finset ρ')
    (hsupp : ∀ i, ∀ r, r ∉ R → Φ i r = 0)
    [FiniteDimensional F (Submodule.span F (Set.range Φ))] :
    finrank F (span F (Set.range Φ)) =
      finrank F (span F (Set.range fun i => fun r : {x // x ∈ R} => Φ i (r : ρ'))) := by
  classical
  set res : (ρ' → F) →ₗ[F] ({x // x ∈ R} → F) :=
    LinearMap.funLeft F F (Subtype.val : {x // x ∈ R} → ρ')
  have hmap : (span F (Set.range Φ)).map res =
      span F (Set.range fun i => fun r : {x // x ∈ R} => Φ i (r : ρ')) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hker : ∀ f ∈ span F (Set.range Φ), res f = 0 → f = 0 := by
    intro f hf hres
    have hsub : f ∈ supportedOn' (F := F) R := by
      have : span F (Set.range Φ) ≤ supportedOn' (F := F) R := by
        rw [span_le]
        rintro _ ⟨i, rfl⟩
        exact fun r hr => hsupp i r hr
      exact this hf
    ext r
    by_cases hr : r ∈ R
    · exact congrFun hres ⟨r, hr⟩
    · exact hsub r hr
  have hinj : Function.Injective (res.domRestrict (span F (Set.range Φ))) := by
    intro f g hfg
    have h0 : res ((f : ρ' → F) - g) = 0 := by
      have h1 : res (f : ρ' → F) = res (g : ρ' → F) := by
        simpa [LinearMap.domRestrict_apply] using hfg
      simp [map_sub, h1]
    have hmem : ((f : ρ' → F) - g) ∈ span F (Set.range Φ) :=
      Submodule.sub_mem _ f.2 g.2
    exact Subtype.ext (sub_eq_zero.mp (hker _ hmem h0))
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (res.domRestrict (span F (Set.range Φ)))
  rw [LinearMap.ker_eq_bot.mpr hinj, finrank_bot, add_zero,
    LinearMap.range_domRestrict, hmap] at hrn
  exact hrn.symm

end Restriction

end ArkLib.ProximityGap.Frontier.HD1Contact

#print axioms ArkLib.ProximityGap.Frontier.HD1Contact.finrank_span_range_le_sum_min
