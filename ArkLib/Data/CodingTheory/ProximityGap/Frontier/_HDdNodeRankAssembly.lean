/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (standalone issue #1)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HDdOriginGrading
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HDdCountingBound

/-!
# HDd — assembly: the origin node functionals are bounded by the block count

`originNodeFamily_rank_le_blockCount`: for a finite monomial family `M`, the span of the
low-truncated origin node functionals

    Φ μ := (ν ↦ if ν₀ + ν₁ < m then coeff ν (contactSubstD d 0 0 (monomial μ 1)) else 0)

has rank at most `Σ_b min |M_b| |R_b|`, where `R` is the finite set of low keys hit by the
substituted monomials and the blocks are the `(g₁, g₂)` pair degrees (input `pairDeg wIn`,
output `Finsupp.weight (wOut d)`).  The functionals `Φ μ` are the coordinates of
`nodeMapD d 0 0 m (monomial μ 1)` extended by zero, so this is the origin node rank bound;
`contactSubstD_translate` transports it to every node on `(a, b₀)`-downward-closed monomial
families, and `exists_interpolant_d` consumes the resulting rank sums.  The probes' integers
count per-block supersets of `M_b`, `R_b`, which only increases the bound
(`Finset.card_le_card` / row-superset), so an audited integer certificate
(`scripts/probes/hdd_certificates.py`) instantiates the hypothesis of the interpolation
theorem at scales where kernel computation is out of reach.
-/

namespace ArkLib.ProximityGap.Frontier.HD1Contact

open Module Submodule

variable {F : Type*} [Field F]

/-- The low-truncated origin node functional of a monomial, extended by zero to all keys. -/
noncomputable def nodeFun (d m : ℕ) (μ : Fin (d + 2) →₀ ℕ) : (Fin (d + 2) →₀ ℕ) → F :=
  fun ν => if ν 0 + ν 1 < m then
    MvPolynomial.coeff ν (contactSubstD d (0 : F) 0 (MvPolynomial.monomial μ 1)) else 0

/-- The finite set of low-index keys hit by the substituted monomials of `M`. -/
noncomputable def hitKeys (d m : ℕ) (M : Finset (Fin (d + 2) →₀ ℕ)) :
    Finset (Fin (d + 2) →₀ ℕ) :=
  M.biUnion fun μ =>
    (contactSubstD d (0 : F) 0 (MvPolynomial.monomial μ (1 : F))).support.filter
      fun ν => ν 0 + ν 1 < m

theorem nodeFun_eq_zero_of_not_hitKey (d m : ℕ) (M : Finset (Fin (d + 2) →₀ ℕ))
    {μ : Fin (d + 2) →₀ ℕ} (hμ : μ ∈ M) {ν : Fin (d + 2) →₀ ℕ}
    (hν : ν ∉ hitKeys (F := F) d m M) : nodeFun (F := F) d m μ ν = 0 := by
  unfold nodeFun
  split_ifs with hlow
  · by_contra hne
    exact hν (Finset.mem_biUnion.mpr ⟨μ, hμ,
      Finset.mem_filter.mpr ⟨MvPolynomial.mem_support_iff.mpr hne, hlow⟩⟩)
  · rfl

theorem nodeFun_block (d m : ℕ) {μ ν : Fin (d + 2) →₀ ℕ}
    (hne : nodeFun (F := F) d m μ ν ≠ 0) :
    Finsupp.weight (wOut d) ν = pairDeg (wIn d) μ := by
  unfold nodeFun at hne
  split_ifs at hne with hlow
  · exact weightedDegree_of_mem_support_contactSubstD d μ 1 ν
      (MvPolynomial.mem_support_iff.mpr hne)
  · exact absurd rfl hne

/-- **Origin node rank ≤ block count.** -/
theorem originNodeFamily_rank_le_blockCount (d m : ℕ)
    (M : Finset (Fin (d + 2) →₀ ℕ)) :
    finrank F (span F (Set.range fun μ : {x // x ∈ M} => nodeFun (F := F) d m μ.1)) ≤
      ∑ b ∈ M.image (fun μ => pairDeg (wIn d) μ),
        min (M.filter fun μ => pairDeg (wIn d) μ = b).card
            ((hitKeys (F := F) d m M).filter
              fun ν => Finsupp.weight (wOut d) ν = b).card := by
  classical
  set R : Finset (Fin (d + 2) →₀ ℕ) := hitKeys (F := F) d m M with hR
  haveI : FiniteDimensional F
      (span F (Set.range fun μ : {x // x ∈ M} => nodeFun (F := F) d m μ.1)) :=
    FiniteDimensional.span_of_finite F (Set.finite_range _)
  -- restrict to the finite hit-key set
  rw [finrank_span_range_eq_restrict (fun μ : {x // x ∈ M} => nodeFun (F := F) d m μ.1) R
    (fun i r hr => nodeFun_eq_zero_of_not_hitKey d m M i.2 hr)]
  -- block bound on the restricted family
  refine le_trans (finrank_span_range_le_sum_min
    (fun (i : {x // x ∈ M}) (r : {x // x ∈ R}) => nodeFun (F := F) d m i.1 r.1)
    (fun i => pairDeg (wIn d) i.1)
    (fun r => Finsupp.weight (wOut d) r.1)
    (fun i r hne => by
      by_contra hval
      exact hne (nodeFun_block d m hval))) ?_
  -- convert subtype-filter cardinalities and images to Finset-filter form
  have hcard : ∀ {α : Type} [DecidableEq α] (S : Finset α) (p : α → Prop)
      [DecidablePred p],
      (Finset.univ.filter fun i : {x // x ∈ S} => p i.1).card = (S.filter p).card := by
    intro α _ S p _
    rw [Finset.univ_eq_attach, Finset.filter_attach, Finset.card_map, Finset.card_attach]
  have himg : ∀ {α β' : Type} [DecidableEq α] [DecidableEq β'] (S : Finset α)
      (f : α → β'),
      (Finset.univ.image fun i : {x // x ∈ S} => f i.1) = S.image f := by
    intro α β' _ _ S f
    rw [Finset.univ_eq_attach]
    calc S.attach.image (fun i => f i.1)
        = (S.attach.image Subtype.val).image f := by rw [Finset.image_image]; rfl
      _ = S.image f := by rw [Finset.attach_image_val]
  rw [himg]
  refine le_of_eq (Finset.sum_congr rfl fun b _ => ?_)
  beta_reduce
  congr 1
  · exact hcard M (fun μ => pairDeg (wIn d) μ = b)
  · exact hcard R (fun ν => Finsupp.weight (wOut d) ν = b)

end ArkLib.ProximityGap.Frontier.HD1Contact

#print axioms ArkLib.ProximityGap.Frontier.HD1Contact.originNodeFamily_rank_le_blockCount
