/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SinglePencilQIndependence

/-!
# Issue #407 — the general-stack packing bound (residual (1) of the bad-scalar q-independence lane).

`SinglePencilQIndependence.lean` proved the packing bound `#bad · C(a, k+1) ≤ C(|μ|, k+1)` for the
**monomial** single-poly stack `Q₀ + γ·Xᵏ`. Its residual (1) was: the packing pinning was tied to
`Xᵏ` (the difference `C(γ−γ')Xᵏ − (W−W')` has degree exactly `k`, giving threshold `k`); the
**general direction** `Q₁` needed `deg Q₁` control.

This file closes residual (1) for the genuine far direction. For ANY direction polynomial `Q₁` with
`deg Q₁ = d ≥ k`, the bad scalars `k`-pack at threshold `d`:

> **`mca_badscalar_packing_general`.** For the pencil `Q₀ + γ·Q₁` with `Q₁` of natDegree `d ≥ k`
> (the genuine far direction; the near case `d < k` is the degenerate joint-agreement case excluded
> by `¬pairJoint`), the bad scalars (`Q₀ + γ·Q₁` agrees with a degree-`<k` codeword on `≥ a` points
> of `μ`, `d < a`) satisfy `#bad · C(a, d+1) ≤ C(|μ|, d+1)`, independent of `|F|`.

**Mechanism (the degree-`d` pinning).** If two bad scalars `γ ≠ γ'` have witness `a`-subsets
`S, S'` meeting in `I` with `|I| > d`, then `∏_{ζ∈I}(X − ζ)` (degree `|I| > d`) divides both
corrected pencils, hence their difference `D = C(γ−γ')·Q₁ − (W − W')`. Now `deg D ≤ max(d, k−1) = d`
(since `deg(W−W') < k ≤ d`), so the higher-degree product forces `D = 0`. Then
`C(γ−γ')·Q₁ = W − W'`, whose LHS has degree exactly `d` (as `γ ≠ γ'`) while the RHS has degree
`< k ≤ d` — a contradiction. Hence `γ = γ'`, and the witness `a`-subsets `d`-pack, so the packing
bound applies with `(k+1) ↦ (d+1)`.

This is strictly stronger than the monomial case (`d = k` recovers `mca_badscalar_packing` exactly)
and removes the `Xᵏ`-specific reasoning: the only structural input is `deg Q₁ = d ≥ k` and the
degree comparison, never the shape of `Q₁`. All `sorry`-free, axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
-/

set_option linter.style.longLine false


open Polynomial Finset

namespace ArkLib.ProximityGap.GeneralPencilPacking

open ArkLib.ProximityGap.SinglePencilQIndependence

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- The product of `(X − ζ)` over a finset of roots of `P` divides `P` (local copy). -/
private theorem prodXsubC_dvd_of_roots (P : F[X]) (S : Finset F)
    (hS : ∀ ζ ∈ S, P.eval ζ = 0) : (∏ ζ ∈ S, (X - C ζ)) ∣ P := by
  apply Finset.prod_dvd_of_coprime
  · intro a _ b _ hab
    exact Polynomial.pairwise_coprime_X_sub_C Function.injective_id (by simpa using hab)
  · intro ζ hζ; rw [Polynomial.dvd_iff_isRoot]; simpa using hS ζ hζ

omit [Fintype F] [DecidableEq F] in
/-- `natDegree (∏_{ζ∈S} (X − ζ)) = |S|` (local copy). -/
private theorem prodXsubC_natDegree (S : Finset F) :
    (∏ ζ ∈ S, (X - C ζ)).natDegree = S.card := by
  rw [Polynomial.natDegree_prod _ _ (fun ζ _ => X_sub_C_ne_zero ζ),
    Finset.sum_congr rfl (fun ζ _ => Polynomial.natDegree_X_sub_C ζ),
    Finset.sum_const, smul_eq_mul, mul_one]

open Classical in
/-- **The general-direction packing bound (residual (1) closed for the far case).**
For the pencil `Q₀ + γ·Q₁` with `Q₁` of natDegree `d` and `k ≤ d < a`, the bad scalars
(`Q₀ + γ·Q₁` agrees with a degree-`<k` codeword on `≥ a` points of `μ`) satisfy
`#bad · C(a, d+1) ≤ C(|μ|, d+1)`, independent of `|F|`. Witness `a`-subsets of distinct bad scalars
`d`-pack (`|S ∩ S'| ≤ d`), since `C(γ−γ')·Q₁ − (W−W')` has degree exactly `d`. -/
theorem mca_badscalar_packing_general (Q0 Q1 : F[X]) (μ : Finset F) (k d a : ℕ)
    (hQ1ne : Q1 ≠ 0) (hQ1deg : Q1.natDegree = d) (hkd : k ≤ d) (hda : d < a) :
    (Finset.univ.filter (fun γ : F =>
        ∃ W : F[X], W.natDegree < k ∧
          a ≤ (μ.filter (fun ζ => (Q0 + C γ * Q1 - W).eval ζ = 0)).card)).card
        * (a.choose (d + 1))
      ≤ (μ.card).choose (d + 1) := by
  classical
  set bad := Finset.univ.filter (fun γ : F =>
      ∃ W : F[X], W.natDegree < k ∧
        a ≤ (μ.filter (fun ζ => (Q0 + C γ * Q1 - W).eval ζ = 0)).card) with hbad
  -- for each bad γ, choose a codeword W and an a-subset S of agreement points
  have hwit : ∀ γ ∈ bad, ∃ W : F[X], ∃ S : Finset F, S ⊆ μ ∧ S.card = a ∧ W.natDegree < k ∧
      ∀ ζ ∈ S, (Q0 + C γ * Q1 - W).eval ζ = 0 := by
    intro γ hγ
    obtain ⟨W, hWdeg, hcard⟩ := (Finset.mem_filter.mp hγ).2
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard
    exact ⟨W, S, hSsub.trans (Finset.filter_subset _ _), hScard, hWdeg,
      fun ζ hζ => (Finset.mem_filter.mp (hSsub hζ)).2⟩
  choose Wp Sp hSsub hScard hWdeg hvan using hwit
  -- pinning: an intersection of more than d points forces the scalars equal
  have hpin : ∀ γ (hγ : γ ∈ bad) γ' (hγ' : γ' ∈ bad),
      d < (Sp γ hγ ∩ Sp γ' hγ').card → γ = γ' := by
    intro γ hγ γ' hγ' hgt
    by_contra hne
    set I := Sp γ hγ ∩ Sp γ' hγ' with hI
    set D := C (γ - γ') * Q1 - (Wp γ hγ - Wp γ' hγ') with hD
    have hd1 : (∏ ζ ∈ I, (X - C ζ)) ∣ (Q0 + C γ * Q1 - Wp γ hγ) :=
      prodXsubC_dvd_of_roots _ I (fun ζ hζ => hvan γ hγ ζ (Finset.mem_inter.mp hζ).1)
    have hd2 : (∏ ζ ∈ I, (X - C ζ)) ∣ (Q0 + C γ' * Q1 - Wp γ' hγ') :=
      prodXsubC_dvd_of_roots _ I (fun ζ hζ => hvan γ' hγ' ζ (Finset.mem_inter.mp hζ).2)
    have hdD : (∏ ζ ∈ I, (X - C ζ)) ∣ D := by
      have hs := dvd_sub hd1 hd2
      have he : (Q0 + C γ * Q1 - Wp γ hγ) - (Q0 + C γ' * Q1 - Wp γ' hγ') = D := by
        rw [hD, map_sub]; ring
      rwa [he] at hs
    -- D ≠ 0: its leading (degree-d) coefficient is (γ−γ')·(leading coeff of Q1) ≠ 0
    have hCne : C (γ - γ') ≠ 0 := by
      rw [Ne, Polynomial.C_eq_zero]; exact sub_ne_zero.mpr hne
    have hCQ1deg : (C (γ - γ') * Q1).natDegree = d := by
      rw [Polynomial.natDegree_C_mul (sub_ne_zero.mpr hne), hQ1deg]
    have hWdiffdeg : (Wp γ hγ - Wp γ' hγ').natDegree < k :=
      lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
        (by rw [Nat.max_lt]; exact ⟨hWdeg γ hγ, hWdeg γ' hγ'⟩)
    -- coeff d of D = (γ−γ')·(leadingCoeff Q1), nonzero
    have hDd : D.coeff d = (γ - γ') * Q1.leadingCoeff := by
      rw [hD, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hWdiffdeg hkd),
        sub_zero, ← hQ1deg, Polynomial.coeff_natDegree]
    have hDne : D ≠ 0 := by
      intro h
      rw [h, Polynomial.coeff_zero] at hDd
      exact hne (sub_eq_zero.mp (by
        rcases mul_eq_zero.mp hDd.symm with h1 | h2
        · exact h1
        · exact absurd (Polynomial.leadingCoeff_eq_zero.mp h2) hQ1ne))
    have hDdeg : D.natDegree ≤ d := by
      rw [hD]
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      rw [Nat.max_le]
      exact ⟨le_of_eq hCQ1deg, le_trans (le_of_lt hWdiffdeg) hkd⟩
    have hle := Polynomial.natDegree_le_of_dvd hdD hDne
    rw [prodXsubC_natDegree] at hle
    have hIle : I.card ≤ d := le_trans hle hDdeg
    omega
  -- the family of witnesses d-packs and is injective
  set G := bad.attach.image (fun p => Sp p.1 p.2) with hG
  have hinj : Set.InjOn (fun p : {x // x ∈ bad} => Sp p.1 p.2) bad.attach := by
    intro p _ q _ heq
    have hpq : Sp p.1 p.2 = Sp q.1 q.2 := heq
    have hkk : d < (Sp p.1 p.2 ∩ Sp q.1 q.2).card := by
      rw [← hpq, Finset.inter_self, hScard p.1 p.2]; omega
    exact Subtype.ext (hpin p.1 p.2 q.1 q.2 hkk)
  have hGcard : G.card = bad.card := by
    rw [hG, Finset.card_image_of_injOn hinj, Finset.card_attach]
  have hGfacts : (∀ S ∈ G, S ⊆ μ) ∧ (∀ S ∈ G, S.card = a) := by
    constructor <;> (intro S hS; rw [hG, Finset.mem_image] at hS; obtain ⟨p, _, rfl⟩ := hS)
    · exact hSsub p.1 p.2
    · exact hScard p.1 p.2
  have hGinter : ∀ S ∈ G, ∀ S' ∈ G, S ≠ S' → (S ∩ S').card ≤ d := by
    intro S hS S' hS' hne
    rw [hG, Finset.mem_image] at hS hS'
    obtain ⟨p, _, rfl⟩ := hS; obtain ⟨q, _, rfl⟩ := hS'
    by_contra hgt
    have hpeq : p.1 = q.1 := hpin p.1 p.2 q.1 q.2 (not_le.mp hgt)
    exact hne (by rw [show p = q from Subtype.ext hpeq])
  have := packing_card_mul_le (k := d) μ G hGfacts.1 hGfacts.2 hGinter
  rwa [hGcard] at this

open Classical in
/-- **Explicit divided form for the general direction.** `#bad ≤ C(|μ|, d+1) / C(a, d+1)`
for any far direction `Q₁` of natDegree `d`, `k ≤ d < a`. Reduces to the monomial
`mca_badscalar_packing_div` when `Q₁ = Xᵏ` (`d = k`). -/
theorem mca_badscalar_packing_general_div (Q0 Q1 : F[X]) (μ : Finset F) (k d a : ℕ)
    (hQ1ne : Q1 ≠ 0) (hQ1deg : Q1.natDegree = d) (hkd : k ≤ d) (hda : d < a) :
    (Finset.univ.filter (fun γ : F =>
        ∃ W : F[X], W.natDegree < k ∧
          a ≤ (μ.filter (fun ζ => (Q0 + C γ * Q1 - W).eval ζ = 0)).card)).card
      ≤ (μ.card).choose (d + 1) / (a.choose (d + 1)) := by
  rw [Nat.le_div_iff_mul_le (Nat.choose_pos (by omega))]
  exact mca_badscalar_packing_general Q0 Q1 μ k d a hQ1ne hQ1deg hkd hda

end ArkLib.ProximityGap.GeneralPencilPacking

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.GeneralPencilPacking.mca_badscalar_packing_general
#print axioms ArkLib.ProximityGap.GeneralPencilPacking.mca_badscalar_packing_general_div
