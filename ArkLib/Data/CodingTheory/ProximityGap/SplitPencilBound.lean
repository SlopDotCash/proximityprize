/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilAbsorption

/-!
# The split-pencil bound (#371, G1 brick)

**At most `⌊n/w⌋ + 1` domain-split polynomials fit in a pencil through a
domain-nonvanishing degree-`w` member.**

Setting: `dom : Fin n ↪ F`, a pencil `{a·f + b·g}` with `g.natDegree = w ≥ 1` and
`g` nonvanishing on the domain.  A *split member* for an index set `T` is a nonzero
constant multiple of the vanishing polynomial `m_T = ∏_{i ∈ T}(X − dom i)` lying in
the pencil.  Results:

* `pencil_split_disjoint` — distinct realized `T`s are **pairwise disjoint**: two
  distinct split members are independent, hence express `g` as a combination
  (`g_combination`), so a common root would make `g` vanish on the domain;
* `pencil_split_small_unique` — at most one realized `T` has `|T| < w` (else `g`
  itself would have degree `< w`);
* **`pencil_split_card_le_of_degree_le_card`** — if every realized member has
  `|T| ≥ w`, the small-member exception vanishes and the family has size `≤ n / w`;
* **`pencil_split_card_le`** — any family `𝒯` of realized index sets has
  `𝒯.card ≤ n / w + 1`.

Sharpness: the μ_w-coset pencil `{X^w − a}` on a smooth domain realizes `n/w`
disjoint split members (cosets of μ_w in μ_n), matching the in-tree strip value
`n/(b−1)` at `b−1 = w`; probe record `probe_fiber_census.py` (f*(12,4) = 3 = n/w,
attained by a partition of μ₁₂).  Role: the counting engine for the fiber
linearization of the WB window residual (`WindowRationalBounded`), where bad
scalars' witness complements land in the pencil `⟨m̂₁, ℓ₀⟩` mod `ℓ₀`.
-/

open Finset Polynomial

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [DecidableEq F]
variable {n : ℕ}

/-- The vanishing polynomial of an index set, through the domain embedding. -/
noncomputable def vanishingPoly (dom : Fin n ↪ F) (T : Finset (Fin n)) : F[X] :=
  ∏ i ∈ T, (X - C (dom i))

theorem vanishingPoly_monic (dom : Fin n ↪ F) (T : Finset (Fin n)) :
    (vanishingPoly dom T).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (dom i)

theorem vanishingPoly_ne_zero (dom : Fin n ↪ F) (T : Finset (Fin n)) :
    vanishingPoly dom T ≠ 0 :=
  (vanishingPoly_monic dom T).ne_zero

theorem vanishingPoly_natDegree (dom : Fin n ↪ F) (T : Finset (Fin n)) :
    (vanishingPoly dom T).natDegree = T.card := by
  rw [vanishingPoly, natDegree_prod _ _ (fun i _ => X_sub_C_ne_zero (dom i))]
  simp [natDegree_X_sub_C]

theorem vanishingPoly_eval_eq_zero (dom : Fin n ↪ F) {T : Finset (Fin n)}
    {i : Fin n} (hi : i ∈ T) : (vanishingPoly dom T).eval (dom i) = 0 := by
  rw [vanishingPoly, eval_prod]
  exact Finset.prod_eq_zero hi (by simp)

/-- Roots recover the index set: `vanishingPoly` is injective. -/
theorem vanishingPoly_inj (dom : Fin n ↪ F) {T₁ T₂ : Finset (Fin n)}
    (h : vanishingPoly dom T₁ = vanishingPoly dom T₂) : T₁ = T₂ := by
  have key : ∀ {A B : Finset (Fin n)},
      vanishingPoly dom A = vanishingPoly dom B → A ⊆ B := by
    intro A B hAB i hi
    by_contra hni
    have h1 : (vanishingPoly dom B).eval (dom i) = 0 := by
      rw [← hAB]
      exact vanishingPoly_eval_eq_zero dom hi
    rw [vanishingPoly, eval_prod, Finset.prod_eq_zero_iff] at h1
    obtain ⟨j, hj, hij⟩ := h1
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hij
    exact hni (dom.injective hij ▸ hj)
  exact Finset.Subset.antisymm (key h) (key h.symm)

/-- `T` is realized as a split member of the pencil `{a·f + b·g}`. -/
def SplitMember (dom : Fin n ↪ F) (f g : F[X]) (T : Finset (Fin n)) : Prop :=
  ∃ c : F, c ≠ 0 ∧ ∃ a b : F, C c * vanishingPoly dom T = C a * f + C b * g

section Pencil

variable {dom : Fin n ↪ F} {f g : F[X]}

/-- **The combination lemma.**  Two split members at distinct index sets express
`g` as a two-term combination of their vanishing polynomials. -/
theorem g_combination {T₁ T₂ : Finset (Fin n)} (hne : T₁ ≠ T₂)
    (h₁ : SplitMember dom f g T₁) (h₂ : SplitMember dom f g T₂) :
    ∃ s t : F, g = C s * vanishingPoly dom T₁ + C t * vanishingPoly dom T₂ := by
  obtain ⟨c₁, hc₁, a₁, b₁, hM₁⟩ := h₁
  obtain ⟨c₂, hc₂, a₂, b₂, hM₂⟩ := h₂
  set m₁ := vanishingPoly dom T₁ with hm₁
  set m₂ := vanishingPoly dom T₂ with hm₂
  -- The coefficient vectors are independent: Δ ≠ 0.
  have hΔ : a₁ * b₂ - a₂ * b₁ ≠ 0 := by
    intro hΔ0
    -- Dependent rows ⟹ the members are proportional ⟹ m₁ = m₂ ⟹ T₁ = T₂.
    have hv₁ : ¬(a₁ = 0 ∧ b₁ = 0) := by
      rintro ⟨rfl, rfl⟩
      apply mul_ne_zero (C_ne_zero.mpr hc₁) (vanishingPoly_ne_zero dom T₁)
      rw [hM₁]
      simp
    -- extract λ with (a₂, b₂) = λ • (a₁, b₁)
    have hlam : ∃ lam : F, a₂ = lam * a₁ ∧ b₂ = lam * b₁ := by
      by_cases ha₁ : a₁ = 0
      · have hb₁ : b₁ ≠ 0 := fun hb => hv₁ ⟨ha₁, hb⟩
        have h1 : a₂ * b₁ = 0 := by
          rw [ha₁] at hΔ0
          linear_combination (-1 : F) * hΔ0
        have ha₂ : a₂ = 0 := by
          rcases mul_eq_zero.mp h1 with h | h
          · exact h
          · exact absurd h hb₁
        refine ⟨b₂ * b₁⁻¹, ?_, ?_⟩
        · rw [ha₁, mul_zero, ha₂]
        · rw [mul_assoc, inv_mul_cancel₀ hb₁, mul_one]
      · have h1 : a₁ * b₂ = a₂ * b₁ := by linear_combination hΔ0
        refine ⟨a₂ * a₁⁻¹, ?_, ?_⟩
        · rw [mul_assoc, inv_mul_cancel₀ ha₁, mul_one]
        · calc b₂ = a₁⁻¹ * (a₁ * b₂) := by
                rw [← mul_assoc, inv_mul_cancel₀ ha₁, one_mul]
            _ = a₁⁻¹ * (a₂ * b₁) := by rw [h1]
            _ = a₂ * a₁⁻¹ * b₁ := by ring
    obtain ⟨lam, hla, hlb⟩ := hlam
    -- M₂ = λ · M₁
    have hMM : C c₂ * m₂ = C (lam * c₁) * m₁ := by
      rw [hM₂, hla, hlb]
      calc C (lam * a₁) * f + C (lam * b₁) * g
          = C lam * (C a₁ * f + C b₁ * g) := by
            simp only [C_mul]
            ring
        _ = C lam * (C c₁ * m₁) := by rw [← hM₁]
        _ = C (lam * c₁) * m₁ := by
            simp only [C_mul]
            ring
    -- compare leading data: m₂ = (c₂⁻¹ λ c₁) m₁ with both monic forces m₁ = m₂
    have hm2eq : m₂ = C (c₂⁻¹ * (lam * c₁)) * m₁ := by
      calc m₂ = C (c₂⁻¹ * c₂) * m₂ := by rw [inv_mul_cancel₀ hc₂, C_1, one_mul]
        _ = C c₂⁻¹ * (C c₂ * m₂) := by
            simp only [C_mul]
            ring
        _ = C c₂⁻¹ * (C (lam * c₁) * m₁) := by rw [hMM]
        _ = C (c₂⁻¹ * (lam * c₁)) * m₁ := by
            simp only [C_mul]
            ring
    have hconst : c₂⁻¹ * (lam * c₁) = 1 := by
      have hmon₁ := vanishingPoly_monic dom T₁
      have hmon₂ := vanishingPoly_monic dom T₂
      have hlc := congrArg Polynomial.leadingCoeff hm2eq
      rw [leadingCoeff_mul, leadingCoeff_C, hmon₂.leadingCoeff,
        hmon₁.leadingCoeff, mul_one] at hlc
      exact hlc.symm
    rw [hconst, C_1, one_mul] at hm2eq
    exact hne (vanishingPoly_inj dom hm2eq.symm)
  -- Solve the 2×2 system for g.
  set Δ := a₁ * b₂ - a₂ * b₁ with hΔdef
  refine ⟨-(Δ⁻¹ * a₂ * c₁), Δ⁻¹ * a₁ * c₂, ?_⟩
  have key : C a₁ * (C c₂ * m₂) - C a₂ * (C c₁ * m₁) = C Δ * g := by
    rw [hM₁, hM₂, hΔdef]
    simp only [C_sub, C_mul]
    ring
  have hg : g = C Δ⁻¹ * (C a₁ * (C c₂ * m₂) - C a₂ * (C c₁ * m₁)) := by
    rw [key, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hΔ, C_1, one_mul]
  rw [hg]
  simp only [C_mul, C_neg]
  ring

/-- **Pairwise disjointness**: distinct realized index sets cannot share a point —
`g` would vanish there. -/
theorem pencil_split_disjoint (hgeval : ∀ i : Fin n, g.eval (dom i) ≠ 0)
    {T₁ T₂ : Finset (Fin n)} (hne : T₁ ≠ T₂)
    (h₁ : SplitMember dom f g T₁) (h₂ : SplitMember dom f g T₂) :
    Disjoint T₁ T₂ := by
  rw [Finset.disjoint_left]
  intro i hi₁ hi₂
  obtain ⟨s, t, hg⟩ := g_combination hne h₁ h₂
  apply hgeval i
  rw [hg]
  simp [vanishingPoly_eval_eq_zero dom hi₁, vanishingPoly_eval_eq_zero dom hi₂]

/-- **Small-member uniqueness**: at most one realized index set has size `< w`,
where `w = g.natDegree`. -/
theorem pencil_split_small_unique
    {T₁ T₂ : Finset (Fin n)} (hne : T₁ ≠ T₂)
    (h₁ : SplitMember dom f g T₁) (h₂ : SplitMember dom f g T₂)
    (hs₁ : T₁.card < g.natDegree) (hs₂ : T₂.card < g.natDegree) : False := by
  obtain ⟨s, t, hg⟩ := g_combination hne h₁ h₂
  have hdeg : g.natDegree ≤ max T₁.card T₂.card := by
    calc g.natDegree
        ≤ max (C s * vanishingPoly dom T₁).natDegree
            (C t * vanishingPoly dom T₂).natDegree := hg ▸ natDegree_add_le _ _
      _ ≤ max T₁.card T₂.card := by
          apply max_le_max
          · exact le_trans (natDegree_C_mul_le _ _)
              (le_of_eq (vanishingPoly_natDegree dom T₁))
          · exact le_trans (natDegree_C_mul_le _ _)
              (le_of_eq (vanishingPoly_natDegree dom T₂))
  rcases max_cases T₁.card T₂.card with ⟨hmax, _⟩ | ⟨hmax, _⟩ <;> omega

omit [DecidableEq F] in
open Classical in
/-- **Exact split-pencil bound for large realized members.**  If every split member
has at least `g.natDegree` roots on the domain, the exceptional small-member term in
`pencil_split_card_le` disappears. -/
theorem pencil_split_card_le_of_degree_le_card (hw : 1 ≤ g.natDegree)
    (hgeval : ∀ i : Fin n, g.eval (dom i) ≠ 0)
    (𝒯 : Finset (Finset (Fin n)))
    (h𝒯 : ∀ T ∈ 𝒯, SplitMember dom f g T)
    (hcard : ∀ T ∈ 𝒯, g.natDegree ≤ T.card) :
    𝒯.card ≤ n / g.natDegree := by
  have hmul : g.natDegree * 𝒯.card ≤ n := by
    have hdisj : ∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → Disjoint T₁ T₂ := by
      intro T₁ h₁ T₂ h₂ hne
      exact pencil_split_disjoint hgeval hne (h𝒯 T₁ h₁) (h𝒯 T₂ h₂)
    calc g.natDegree * 𝒯.card = ∑ _T ∈ 𝒯, g.natDegree := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ T ∈ 𝒯, T.card := Finset.sum_le_sum hcard
      _ = (𝒯.biUnion id).card := (Finset.card_biUnion hdisj).symm
      _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  rw [Nat.le_div_iff_mul_le (by omega : 0 < g.natDegree), mul_comm]
  exact hmul

open Classical in
/-- **THE SPLIT-PENCIL BOUND (G1).**  Any family of index sets realized as split
members of a pencil through a domain-nonvanishing polynomial `g` of exact degree
`w ≥ 1` has at most `n / w + 1` elements. -/
theorem pencil_split_card_le (hw : 1 ≤ g.natDegree)
    (hgeval : ∀ i : Fin n, g.eval (dom i) ≠ 0)
    (𝒯 : Finset (Finset (Fin n)))
    (h𝒯 : ∀ T ∈ 𝒯, SplitMember dom f g T) :
    𝒯.card ≤ n / g.natDegree + 1 := by
  set w := g.natDegree with hwdef
  set big := 𝒯.filter (fun T => w ≤ T.card) with hbig
  set small := 𝒯.filter (fun T => ¬ w ≤ T.card) with hsmall
  have hsplit : big.card + small.card = 𝒯.card :=
    Finset.card_filter_add_card_filter_not _
  -- small has at most one element
  have hsmall1 : small.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro T₁ h₁ T₂ h₂
    by_contra hne
    rw [hsmall, Finset.mem_filter] at h₁ h₂
    exact pencil_split_small_unique hne (h𝒯 T₁ h₁.1) (h𝒯 T₂ h₂.1)
      (by omega) (by omega)
  -- big members are pairwise disjoint with card ≥ w, inside Fin n
  have hbigcard : w * big.card ≤ n := by
    have hdisj : ∀ T₁ ∈ big, ∀ T₂ ∈ big, T₁ ≠ T₂ → Disjoint T₁ T₂ := by
      intro T₁ h₁ T₂ h₂ hne
      rw [hbig, Finset.mem_filter] at h₁ h₂
      exact pencil_split_disjoint hgeval hne (h𝒯 T₁ h₁.1) (h𝒯 T₂ h₂.1)
    calc w * big.card = ∑ _T ∈ big, w := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ T ∈ big, T.card := by
          refine Finset.sum_le_sum fun T hT => ?_
          rw [hbig, Finset.mem_filter] at hT
          exact hT.2
      _ = (big.biUnion id).card := (Finset.card_biUnion hdisj).symm
      _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  have hbig_le : big.card ≤ n / w := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < w), mul_comm]
    exact hbigcard
  omega

open Classical in
/-- **Exact-size split-pencil bound.**  If every realized split member has at
least `deg g` domain roots, the small-member exception disappears and the
disjointness packing gives the sharp `n / deg g` count. -/
theorem splitMember_count_le (hw : 1 ≤ g.natDegree)
    (hgeval : ∀ i : Fin n, g.eval (dom i) ≠ 0)
    (𝒯 : Finset (Finset (Fin n)))
    (h𝒯 : ∀ T ∈ 𝒯, SplitMember dom f g T)
    (hcard : ∀ T ∈ 𝒯, g.natDegree ≤ T.card) :
    𝒯.card ≤ n / g.natDegree := by
  classical
  set w := g.natDegree with hwdef
  have hbigcard : w * 𝒯.card ≤ n := by
    have hdisj : ∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → Disjoint T₁ T₂ := by
      intro T₁ h₁ T₂ h₂ hne
      exact pencil_split_disjoint hgeval hne (h𝒯 T₁ h₁) (h𝒯 T₂ h₂)
    calc w * 𝒯.card = ∑ _T ∈ 𝒯, w := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ T ∈ 𝒯, T.card := by
          exact Finset.sum_le_sum fun T hT => by
            rw [hwdef]
            exact hcard T hT
      _ = (𝒯.biUnion id).card := (Finset.card_biUnion hdisj).symm
      _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  rw [Nat.le_div_iff_mul_le (by omega : 0 < w), mul_comm]
  exact hbigcard

end Pencil

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.g_combination
#print axioms ProximityGap.WBPencil.pencil_split_disjoint
#print axioms ProximityGap.WBPencil.pencil_split_small_unique
#print axioms ProximityGap.WBPencil.pencil_split_card_le_of_degree_le_card
#print axioms ProximityGap.WBPencil.pencil_split_card_le
