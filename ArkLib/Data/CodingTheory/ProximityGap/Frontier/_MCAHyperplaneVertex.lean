/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RSRestrictInjOn
import ArkLib.Data.CodingTheory.ProximityGap.MCADeadWitness

/-!
# An MCA witness is an injective hyperplane vertex on `k+1` active coordinates

For a degree-`<k` Reed–Solomon code `C` and a coordinate set `S`, define

`Phi_S(alpha,c) = c|_S - alpha * u1|_S`.

If `S` supports one line explainer `w = u0 + gamma*u1` but does not jointly explain
`(u0,u1)`, then `Phi_S` is injective.  Indeed, a kernel element with `alpha=0` is killed by RS
restriction rigidity on `|S| >= k`; a kernel element with `alpha != 0` would give a codeword
explaining `u1`, and subtracting it from `w` would also explain `u0`, contradicting the MCA
no-joint clause.

Moreover some `(k+1)`-subset `T` of `S` already has this property.  Interpolate `u1` on any
`k`-subset `K` of `S`; nonextendability on all of `S` supplies one failed coordinate `x`, and
`T=K union {x}` is active.  This is the precise hyperplane-vertex / active-pin package for
design-matrix arguments.  It does not by itself improve the global `C(n,k+1)` ownership count.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ProximityGap.Frontier.MCAHyperplaneVertex

open ArkLib.ProximityGap.Frontier.RSRestrictInjOn

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Restrict the affine explainer equation to `S`.  A pair `(alpha,c)` maps to
`c|_S - alpha*u1|_S`. -/
noncomputable def explainerRestriction
    (domain : ι ↪ F) (k : ℕ) (S : Finset ι) (u₁ : ι → F) :
    F × ReedSolomon.code domain k →ₗ[F] (S → F) where
  toFun z := fun i => z.2.1 i.1 - z.1 * u₁ i.1
  map_add' x y := by
    funext i
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' a x := by
    funext i
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    simp [mul_comm, mul_left_comm, mul_assoc]
    ring

/-- If `u1` has no RS extension on `S`, then the explainer restriction map is injective as soon
as `|S| >= k`.  This is the algebraic kernel of the hyperplane-vertex interpretation. -/
theorem explainerRestriction_injective_of_direction_nonextendable
    (domain : ι ↪ F) (k : ℕ) (S : Finset ι) (u₁ : ι → F)
    (hkS : k ≤ S.card)
    (hdir : ¬ ∃ c ∈ ReedSolomon.code domain k, ∀ i ∈ S, c i = u₁ i) :
    Function.Injective (explainerRestriction domain k S u₁) := by
  rw [← LinearMap.ker_eq_bot]
  ext z
  simp only [LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  · intro hz
    have hzcoord : ∀ i ∈ S, z.2.1 i - z.1 * u₁ i = 0 := by
      intro i hi
      have := congrFun hz ⟨i, hi⟩
      simpa [explainerRestriction] using this
    have ha : z.1 = 0 := by
      by_contra ha0
      apply hdir
      let c₁ : ι → F := z.1⁻¹ • z.2.1
      have hc₁ : c₁ ∈ ReedSolomon.code domain k :=
        (ReedSolomon.code domain k).smul_mem _ z.2.2
      refine ⟨c₁, hc₁, ?_⟩
      intro i hi
      have hzi := hzcoord i hi
      have hzc : z.2.1 i = z.1 * u₁ i := sub_eq_zero.mp hzi
      dsimp [c₁]
      rw [hzc, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
    have hcfunc : z.2.1 = 0 := by
      refine rs_restrict_injOn_of_k_le domain k S hkS z.2.2
        ((ReedSolomon.code domain k).zero_mem) ?_
      funext i
      have hzi := hzcoord i.1 i.2
      simpa [ha] using hzi
    apply Prod.ext
    · exact ha
    · exact Subtype.ext hcfunc
  · rintro rfl
    funext i
    simp [explainerRestriction]

/-- One line explainer plus failure of joint agreement forces the direction row `u1` to be
nonextendable by an RS codeword on the same witness set. -/
theorem direction_nonextendable_of_not_pairJoint_and_explainer
    (domain : ι ↪ F) (k : ℕ) (S : Finset ι) (u₀ u₁ : ι → F) (γ : F)
    (hno : ¬ pairJointAgreesOn (ReedSolomon.code domain k : Set (ι → F)) S u₀ u₁)
    (w : ReedSolomon.code domain k)
    (hw : ∀ i ∈ S, w.1 i = u₀ i + γ * u₁ i) :
    ¬ ∃ c ∈ ReedSolomon.code domain k, ∀ i ∈ S, c i = u₁ i := by
  rintro ⟨c₁, hc₁, hc₁S⟩
  let c₀ : ι → F := w.1 - γ • c₁
  have hc₀ : c₀ ∈ ReedSolomon.code domain k :=
    (ReedSolomon.code domain k).sub_mem w.2
      ((ReedSolomon.code domain k).smul_mem γ hc₁)
  apply hno
  refine ⟨c₀, hc₀, c₁, hc₁, ?_⟩
  intro i hi
  refine ⟨?_, hc₁S i hi⟩
  dsimp [c₀]
  rw [hw i hi, hc₁S i hi]
  ring

/-- **MCA hyperplane vertex.** On any RS witness of size at least `k`, the no-joint clause and
one line explainer make `Phi_S` injective. -/
theorem explainerRestriction_injective_of_mca_witness
    (domain : ι ↪ F) (k : ℕ) (S : Finset ι) (u₀ u₁ : ι → F) (γ : F)
    (hkS : k ≤ S.card)
    (hno : ¬ pairJointAgreesOn (ReedSolomon.code domain k : Set (ι → F)) S u₀ u₁)
    (w : ReedSolomon.code domain k)
    (hw : ∀ i ∈ S, w.1 i = u₀ i + γ * u₁ i) :
    Function.Injective (explainerRestriction domain k S u₁) :=
  explainerRestriction_injective_of_direction_nonextendable domain k S u₁ hkS
    (direction_nonextendable_of_not_pairJoint_and_explainer domain k S u₀ u₁ γ hno w hw)

/-- The scalar/codeword explainer on a fixed MCA witness is unique.  This packages both parts,
not just the scalar uniqueness statement. -/
theorem scalar_codeword_explainer_unique
    (domain : ι ↪ F) (k : ℕ) (S : Finset ι) (u₀ u₁ : ι → F)
    (hkS : k ≤ S.card)
    (hno : ¬ pairJointAgreesOn (ReedSolomon.code domain k : Set (ι → F)) S u₀ u₁)
    {γ₁ γ₂ : F} {w₁ w₂ : ReedSolomon.code domain k}
    (h₁ : ∀ i ∈ S, w₁.1 i = u₀ i + γ₁ * u₁ i)
    (h₂ : ∀ i ∈ S, w₂.1 i = u₀ i + γ₂ * u₁ i) :
    γ₁ = γ₂ ∧ w₁ = w₂ := by
  have hinj := explainerRestriction_injective_of_mca_witness
    domain k S u₀ u₁ γ₁ hkS hno w₁ h₁
  have hpairs : (γ₁, w₁) = (γ₂, w₂) := by
    apply hinj
    funext i
    change w₁.1 i.1 - γ₁ * u₁ i.1 = w₂.1 i.1 - γ₂ * u₁ i.1
    rw [h₁ i.1 i.2, h₂ i.1 i.2]
    ring
  exact ⟨congrArg Prod.fst hpairs, congrArg Prod.snd hpairs⟩

/-- **Active `(k+1)`-pin set.** Every MCA witness contains a `(k+1)`-subset on which the
hyperplane-vertex map is already injective.

The set is explicit in principle: choose any `k` witness coordinates, interpolate `u1` there,
and add one witness coordinate where that interpolant fails. -/
theorem exists_active_pin_set
    (domain : ι ↪ F) (k : ℕ) (S : Finset ι) (u₀ u₁ : ι → F) (γ : F)
    (hkS : k ≤ S.card)
    (hno : ¬ pairJointAgreesOn (ReedSolomon.code domain k : Set (ι → F)) S u₀ u₁)
    (w : ReedSolomon.code domain k)
    (hw : ∀ i ∈ S, w.1 i = u₀ i + γ * u₁ i) :
    ∃ T : Finset ι, T ⊆ S ∧ T.card = k + 1 ∧
      Function.Injective (explainerRestriction domain k T u₁) := by
  classical
  have hdir := direction_nonextendable_of_not_pairJoint_and_explainer
    domain k S u₀ u₁ γ hno w hw
  obtain ⟨K, hKS, hKcard⟩ := Finset.exists_subset_card_eq hkS
  obtain ⟨cK, hcK, hcKS⟩ :=
    ReedSolomon.ReedSolomon_interpolate_through_subset (k := k) domain K
      (by rw [hKcard]) u₁
  have hfail : ∃ x ∈ S, cK x ≠ u₁ x := by
    by_contra hall
    push_neg at hall
    exact hdir ⟨cK, hcK, hall⟩
  obtain ⟨x, hxS, hxfail⟩ := hfail
  have hxK : x ∉ K := by
    intro hx
    exact hxfail (hcKS x hx)
  let T : Finset ι := insert x K
  have hTsub : T ⊆ S := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hyK
    · exact hxS
    · exact hKS hyK
  have hTcard : T.card = k + 1 := by
    dsimp [T]
    rw [Finset.card_insert_of_notMem hxK, hKcard]
  have hTdir : ¬ ∃ c ∈ ReedSolomon.code domain k, ∀ i ∈ T, c i = u₁ i := by
    rintro ⟨c, hc, hcT⟩
    have hceq : c = cK := by
      refine rs_restrict_injOn_of_k_le domain k K (by omega) hc hcK ?_
      funext i
      change c i.1 = cK i.1
      rw [hcT i.1 (Finset.mem_insert_of_mem i.2), hcKS i.1 i.2]
    exact hxfail (by rw [← hceq]; exact hcT x (Finset.mem_insert_self x K))
  refine ⟨T, hTsub, hTcard, ?_⟩
  exact explainerRestriction_injective_of_direction_nonextendable domain k T u₁
    (by omega) hTdir

end ProximityGap.Frontier.MCAHyperplaneVertex

#print axioms ProximityGap.Frontier.MCAHyperplaneVertex.explainerRestriction_injective_of_mca_witness
#print axioms ProximityGap.Frontier.MCAHyperplaneVertex.scalar_codeword_explainer_unique
#print axioms ProximityGap.Frontier.MCAHyperplaneVertex.exists_active_pin_set
