/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#1, SW1 lane F3)
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# SW1-F3 — the union-rank residual `hrank`, exactly: a localized span cap REFUTES it

**Target (one-question map F3, SYZ42/SYZ43 `RealizabilityCore` residue).**  For the G87 bridge
family `φ : Fin r × Fin (t − k) → Dual (SyndromePair C)` of a stack `(u₀, u₁)` with witness
configuration `{(γᵢ, Sᵢ)}`, `U := ⋃ Sᵢ`, the strip route needs

> `hrank : finrank (span (range φ)) = 2 (Ucard − k)`,   `Ucard = |U|`.

**Result (refutation-no-go of the formalization; unconditional, every field, every linear
code).**  Each G87 row `ℓᵢⱼ` factors through the restriction `res_{Sᵢ}` and annihilates `C`, so
every bridge functional factors through the *local* syndrome-pair surjection
`ρ_U × ρ_U : (F^ι/C)² ↠ (F^U / C|_U)²`, whose target has dimension exactly `2(|U| − dim C|_U)`
(`finrank_localPair`).  The family also annihilates the stack's own syndrome pair, whose image
under `ρ_U × ρ_U` is nonzero **iff** the stack does not jointly agree with a codeword pair on `U`
(`restrictQ_syndromePair_eq_zero_iff`) — which any `mcaEvent` witness set inside `U` forces.
Hence (`localized_span_cap`, the G86/SYZ20 `plantable_span_cap` argument run on `U` instead of
on `ι`):

> `finrank (span (range φ)) + 1 ≤ 2 (|U| − dim C|_U)`.

With `dim C|_U = k` (automatic for an MDS code once `|U| ≥ k`) this is
`finrank (span (range φ)) ≤ 2(|U| − k) − 1`: **`hrank` at `Ucard = |U|` is FALSE for every
stack that has a single `mcaEvent`-bad scalar whose witness set lies in `U`**
(`bridge_family_violates_hrank`, `hrank_false_of_mcaEvent_witness`).  The rank equality the
strip route wants to *assume* is exactly what the syndrome annihilation *forbids*: the bridge
family can span the doubled local shortening only when the stack is a codeword pair on `U`, i.e.
only when it is not an `mcaEvent` stack at all.

Two further exact facts about the formal residual:

* `forall_form_forces_Ucard_le_k` — the `∀ φ` quantifier of SYZ43
  `realizabilityCore_of_mcaEvent_witnesses.hrank` is unsatisfiable for `Ucard > k` (take
  `φ := 0`).
* `single_block_rank` (probe, see below) — one block is the *graph* `{(ℓ, γℓ)}` of dimension
  `t − k`, not the "doubled" `2(t − k)`-dimensional shortening the map's gloss suggests; two
  blocks with distinct scalars always span exactly `2(t − k)`, whatever the overlap.

**Honest classification.**  Refutation-no-go with countermodel (the countermodel is *every*
`mcaEvent` stack).  Nothing here bears on the truth of the union budget `|U| ≤ n − 1` or on
δ*; it shows the Lean carrier of F3 cannot be discharged and must be re-formalized.  The
companion file `_SW1_F3_MasterHypothesisVacuous.lean` shows the enclosing master hypotheses
(SYZ40/41/42, and so the antecedent of SYZ46's δ* bracket) are contradictory outright.
Probe: `scripts/probes/sw1_f3_union_rank.py`.  KB: `docs/kb/deltastar-sw1-f3-2026-09-05.md`.

`SyndromePair`, `syndromePair`, `pairJointAgreesOn` are restated byte-identically from
`_G87McaEventSyndromeBridge.lean` / `ProximityGap/Errors.lean` (Mathlib-only file by the SW1
machine rules).  Axiom-clean; `#print axioms` at the bottom.  No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SW1F3

open Module Submodule

/-! ## 1. The abstract localized span cap -/

section Abstract

variable {F : Type*} [Field F]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [FiniteDimensional F V']

/-- **Localized span cap.**  If every functional of a family factors through a surjection
`π : V ↠ V'` and annihilates a vector `σ` whose image `π σ` is nonzero, the span of the family
has codimension at least one *inside the dual of `V'`*: `finrank (span) + 1 ≤ finrank V'`.
(SYZ20 `plantable_span_cap` is the case `π = id`.) -/
theorem span_cap_of_factors {D : Type*} (π : V →ₗ[F] V') (hπ : Function.Surjective π)
    {σ : V} (hσ : π σ ≠ 0) (φ : D → Module.Dual F V)
    (hloc : ∀ p, ∀ v, π v = 0 → φ p v = 0) (hann : ∀ p, φ p σ = 0) :
    finrank F (Submodule.span F (Set.range φ)) + 1 ≤ finrank F V' := by
  classical
  have hσ0 : σ ≠ 0 := fun h => hσ (by rw [h, map_zero])
  set K : Submodule F V := LinearMap.ker π ⊔ (F ∙ σ) with hK
  -- every functional of the family lies in the dual annihilator of `K`
  have hsub : Submodule.span F (Set.range φ) ≤ K.dualAnnihilator := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
    intro w hw
    rw [hK, Submodule.mem_sup] at hw
    obtain ⟨y, hy, z, hz, rfl⟩ := hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [map_add, map_smul, hloc p y (LinearMap.mem_ker.mp hy), hann p, smul_zero, add_zero]
  -- `finrank K = finrank (ker π) + 1`
  have hdisj : Disjoint (LinearMap.ker π) (F ∙ σ) := by
    rw [Submodule.disjoint_span_singleton]
    intro h
    exact absurd (LinearMap.mem_ker.mp h) hσ
  have hKdim : finrank F K = finrank F (LinearMap.ker π) + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker π) (F ∙ σ)
    rw [hdisj.eq_bot, finrank_bot, add_zero, finrank_span_singleton hσ0] at h
    rw [hK]; exact h
  -- `finrank (ker π) + finrank V' = finrank V`
  have hker : finrank F (LinearMap.ker π) + finrank F V' = finrank F V := by
    have h := LinearMap.finrank_range_add_finrank_ker π
    rw [LinearMap.range_eq_top.mpr hπ, finrank_top] at h
    omega
  have hann' : finrank F K + finrank F K.dualAnnihilator = finrank F V :=
    Subspace.finrank_add_finrank_dualAnnihilator_eq K
  have hmono : finrank F (Submodule.span F (Set.range φ)) ≤ finrank F K.dualAnnihilator :=
    Submodule.finrank_mono hsub
  omega

/-- **The `∀ φ` form of SYZ43's `hrank` is unsatisfiable above `k`.**  SYZ43
`realizabilityCore_of_mcaEvent_witnesses` quantifies `hrank` over *every* family annihilating
the syndrome pair; the zero family qualifies and has span `⊥`, so the hypothesis forces
`2 (Ucard − k) = 0`, i.e. `Ucard ≤ k`.  That theorem is therefore only ever applicable at
`Ucard ≤ k`, never at an over-budget union. -/
theorem forall_form_forces_Ucard_le_k {D : Type*} (σ : V) {k Ucard : ℕ}
    (h : ∀ φ : D → Module.Dual F V, (∀ p, φ p σ = 0) →
      finrank F (Submodule.span F (Set.range φ)) = 2 * (Ucard - k)) :
    Ucard ≤ k := by
  have h0 := h (fun _ => 0) (fun _ => LinearMap.zero_apply σ)
  have hspan : Submodule.span F (Set.range (fun _ : D => (0 : Module.Dual F V))) = ⊥ := by
    rw [eq_bot_iff, Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    simp
  rw [hspan, finrank_bot] at h0
  omega

end Abstract

/-! ## 2. The syndrome pair, its restriction to `U`, and joint codeword agreement -/

section SyndromePair

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restatement of G87 `SyndromePair` (byte-identical): two copies of the syndrome quotient. -/
abbrev SyndromePair (C : Submodule F (ι → F)) : Type _ :=
  ((ι → F) ⧸ C) × ((ι → F) ⧸ C)

/-- Restatement of G87 `syndromePair` (byte-identical). -/
def syndromePair (C : Submodule F (ι → F)) (u₀ u₁ : ι → F) : SyndromePair C :=
  (C.mkQ u₀, C.mkQ u₁)

/-- Restatement of `ProximityGap.pairJointAgreesOn` (byte-identical, `A := F`). -/
def pairJointAgreesOn (C : Set (ι → F)) (S : Finset ι) (u₀ u₁ : ι → F) : Prop :=
  ∃ v₀ ∈ C, ∃ v₁ ∈ C, ∀ i ∈ S, v₀ i = u₀ i ∧ v₁ i = u₁ i

/-- Joint agreement is monotone in the set: failing it on `S ⊆ U` fails it on `U`. -/
theorem not_pairJointAgreesOn_mono (C : Set (ι → F)) {S U : Finset ι} (hSU : S ⊆ U)
    {u₀ u₁ : ι → F} (h : ¬ pairJointAgreesOn C S u₀ u₁) : ¬ pairJointAgreesOn C U u₀ u₁ := by
  rintro ⟨v₀, hv₀, v₁, hv₁, hagree⟩
  exact h ⟨v₀, hv₀, v₁, hv₁, fun i hi => hagree i (hSU hi)⟩

/-- Coordinate restriction `F^ι → F^U`. -/
def resU (U : Finset ι) : (ι → F) →ₗ[F] ((↥U : Type _) → F) :=
  LinearMap.funLeft F F (fun s : ↥U => (s : ι))

theorem resU_apply (U : Finset ι) (v : ι → F) (s : ↥U) : resU U v s = v s := rfl

/-- The restricted code `C|_U`. -/
def codeRes (C : Submodule F (ι → F)) (U : Finset ι) : Submodule F ((↥U : Type _) → F) :=
  C.map (resU U)

/-- The local syndrome quotient `F^U ⧸ C|_U`. -/
abbrev LocalQuot (C : Submodule F (ι → F)) (U : Finset ι) : Type _ :=
  ((↥U : Type _) → F) ⧸ codeRes C U

/-- The local syndrome surjection `ρ_U : F^ι ⧸ C → F^U ⧸ C|_U`. -/
def restrictQ (C : Submodule F (ι → F)) (U : Finset ι) :
    ((ι → F) ⧸ C) →ₗ[F] LocalQuot C U :=
  C.liftQ ((codeRes C U).mkQ ∘ₗ resU U) (by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_map_of_mem hx)

theorem restrictQ_mk (C : Submodule F (ι → F)) (U : Finset ι) (v : ι → F) :
    restrictQ C U (C.mkQ v) = (codeRes C U).mkQ (resU U v) := by
  simp [restrictQ, Submodule.mkQ_apply, Submodule.liftQ_apply]

theorem restrictQ_surjective (C : Submodule F (ι → F)) (U : Finset ι) :
    Function.Surjective (restrictQ C U) := by
  intro y
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (codeRes C U) y
  obtain ⟨v, rfl⟩ :=
    LinearMap.funLeft_surjective_of_injective F F (fun s : ↥U => (s : ι)) Subtype.val_injective z
  exact ⟨C.mkQ v, restrictQ_mk C U v⟩

/-- The local syndrome quotient has dimension `|U| − dim C|_U`. -/
theorem finrank_localQuot (C : Submodule F (ι → F)) (U : Finset ι) :
    finrank F (LocalQuot C U) + finrank F (codeRes C U) = U.card := by
  have h := Submodule.finrank_quotient_add_finrank (codeRes C U)
  rw [Module.finrank_pi, Fintype.card_coe] at h
  exact h

/-- The local syndrome-pair space has dimension exactly `2(|U| − dim C|_U)`: this is the
*true* ceiling for the `U`-anchored functionals (SYZ22 `doubled_shortening_dim` in quotient
form). -/
theorem finrank_localPair (C : Submodule F (ι → F)) (U : Finset ι) :
    finrank F (LocalQuot C U × LocalQuot C U) = 2 * (U.card - finrank F (codeRes C U)) := by
  rw [Module.finrank_prod]
  have := finrank_localQuot C U
  omega

/-- **The local syndrome pair vanishes iff the stack jointly agrees with a codeword pair on
`U`.**  This is the exact bridge between the `mcaEvent` clause `¬ pairJointAgreesOn` and the
nonvanishing needed by the localized cap. -/
theorem restrictQ_mkQ_eq_zero_iff (C : Submodule F (ι → F)) (U : Finset ι) (u : ι → F) :
    restrictQ C U (C.mkQ u) = 0 ↔ ∃ v ∈ C, ∀ i ∈ U, v i = u i := by
  rw [restrictQ_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, codeRes,
    Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, fun i hi => congrFun h ⟨i, hi⟩⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, funext fun s => h s s.2⟩

theorem restrictQ_syndromePair_eq_zero_iff (C : Submodule F (ι → F)) (U : Finset ι)
    (u₀ u₁ : ι → F) :
    (restrictQ C U).prodMap (restrictQ C U) (syndromePair C u₀ u₁) = 0 ↔
      pairJointAgreesOn (C : Set (ι → F)) U u₀ u₁ := by
  change (restrictQ C U (C.mkQ u₀), restrictQ C U (C.mkQ u₁)) = (0, 0) ↔ _
  rw [Prod.mk.injEq, restrictQ_mkQ_eq_zero_iff, restrictQ_mkQ_eq_zero_iff]
  constructor
  · rintro ⟨⟨v₀, hv₀, h₀⟩, ⟨v₁, hv₁, h₁⟩⟩
    exact ⟨v₀, hv₀, v₁, hv₁, fun i hi => ⟨h₀ i hi, h₁ i hi⟩⟩
  · rintro ⟨v₀, hv₀, v₁, hv₁, h⟩
    exact ⟨⟨v₀, hv₀, fun i hi => (h i hi).1⟩, ⟨v₁, hv₁, fun i hi => (h i hi).2⟩⟩

/-- **The localized span cap on the syndrome-pair space.**  Any family of functionals on
`SyndromePair C` that (a) factors through the local surjection `ρ_U × ρ_U` and (b) annihilates
the syndrome pair of a stack that does *not* jointly agree with a codeword pair on `U` has
`finrank (span) + 1 ≤ 2 (|U| − dim C|_U)`.  In particular it can never reach the doubled local
shortening dimension `2(|U| − k)` that `hrank` demands. -/
theorem localized_span_cap {D : Type*} (C : Submodule F (ι → F)) (U : Finset ι)
    {u₀ u₁ : ι → F} (hnj : ¬ pairJointAgreesOn (C : Set (ι → F)) U u₀ u₁)
    (φ : D → Module.Dual F (SyndromePair C))
    (hloc : ∀ p, ∀ v : SyndromePair C,
      (restrictQ C U).prodMap (restrictQ C U) v = 0 → φ p v = 0)
    (hann : ∀ p, φ p (syndromePair C u₀ u₁) = 0) :
    finrank F (Submodule.span F (Set.range φ)) + 1 ≤ 2 * (U.card - finrank F (codeRes C U)) := by
  have hπ : Function.Surjective ((restrictQ C U).prodMap (restrictQ C U)) := by
    rw [LinearMap.coe_prodMap]
    exact (restrictQ_surjective C U).prodMap (restrictQ_surjective C U)
  have hσ : (restrictQ C U).prodMap (restrictQ C U) (syndromePair C u₀ u₁) ≠ 0 :=
    fun h => hnj ((restrictQ_syndromePair_eq_zero_iff C U u₀ u₁).mp h)
  have := span_cap_of_factors _ hπ hσ φ hloc hann
  rwa [finrank_localPair] at this

end SyndromePair

/-! ## 3. The G87 construction, re-derived with its locality exported

G87 `exists_rowFunctionals` / `exists_bridge_functionals` build the bridge rows as duals of
`(S → F) ⧸ res_S(C)` composed with `res_S`; their statements export annihilation and per-block
independence but *not* the locality.  We re-run the same construction (proof adapted verbatim)
and export the one extra fact the cap needs: each row kills every vector vanishing on `S`. -/

section Construction

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- G87 `exists_rowFunctionals` with locality: the `t − k` rows of one witness kill every
vector vanishing on the witness support `S`. -/
theorem exists_rowFunctionals_local (C : Submodule F (ι → F)) {S : Finset ι} {t : ℕ}
    (hS : S.card = t) {u₀ u₁ : ι → F} {γ : F}
    (hagree : ∃ c ∈ C, ∀ x ∈ S, c x = u₀ x + γ * u₁ x) :
    ∃ ℓ : Fin (t - finrank F C) → Module.Dual F (ι → F),
      LinearIndependent F ℓ ∧
      (∀ j, ∀ x ∈ C, ℓ j x = 0) ∧
      (∀ j, ℓ j (u₀ + γ • u₁) = 0) ∧
      (∀ j, ∀ v : ι → F, (∀ x ∈ S, v x = 0) → ℓ j v = 0) := by
  classical
  obtain ⟨c, hcC, hc⟩ := hagree
  set res : (ι → F) →ₗ[F] ((↥S : Type _) → F) :=
    LinearMap.funLeft F F (fun s : ↥S => (s : ι)) with hres
  set M : Submodule F ((↥S : Type _) → F) := C.map res with hM
  set π : (ι → F) →ₗ[F] (((↥S : Type _) → F) ⧸ M) := M.mkQ.comp res with hπ
  have hπsurj : Function.Surjective π := by
    have h1 : Function.Surjective res :=
      LinearMap.funLeft_surjective_of_injective F F _ Subtype.val_injective
    exact (Submodule.mkQ_surjective M).comp h1
  have hdimS : finrank F ((↥S : Type _) → F) = t := by
    simp [Fintype.card_coe, hS]
  have hqM : finrank F (((↥S : Type _) → F) ⧸ M) + finrank F M =
      finrank F ((↥S : Type _) → F) :=
    Submodule.finrank_quotient_add_finrank M
  have hMle : finrank F M ≤ finrank F C := Submodule.finrank_map_le res C
  have hdual : finrank F (Module.Dual F (((↥S : Type _) → F) ⧸ M)) =
      finrank F (((↥S : Type _) → F) ⧸ M) :=
    Subspace.dual_finrank_eq
  have hbudget : t - finrank F C ≤
      finrank F (Module.Dual F (((↥S : Type _) → F) ⧸ M)) := by omega
  set b := Module.finBasis F (Module.Dual F (((↥S : Type _) → F) ⧸ M)) with hb
  set lam : Fin (t - finrank F C) → Module.Dual F (((↥S : Type _) → F) ⧸ M) :=
    fun j => b (Fin.castLE hbudget j) with hlam
  have hlamli : LinearIndependent F lam :=
    b.linearIndependent.comp _ (Fin.castLE_injective hbudget)
  refine ⟨fun j => (lam j).comp π, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro a ha
    have hlamzero : ∑ j, a j • lam j = 0 := by
      apply LinearMap.ext
      intro q
      obtain ⟨v, rfl⟩ := hπsurj q
      have := congrArg (fun f => f v) ha
      simpa [LinearMap.sum_apply, LinearMap.smul_apply] using this
    exact Fintype.linearIndependent_iff.mp hlamli a hlamzero
  · intro j x hx
    have : π x = 0 := by
      simp only [hπ, LinearMap.comp_apply, Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero M).mpr (Submodule.mem_map_of_mem hx)
    simp [LinearMap.comp_apply, this]
  · intro j
    have hresline : res (u₀ + γ • u₁) = res c := by
      funext s
      have := hc (s : ι) s.2
      simp [hres, LinearMap.funLeft_apply, this]
    have : π (u₀ + γ • u₁) = 0 := by
      simp only [hπ, LinearMap.comp_apply, hresline, Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero M).mpr (Submodule.mem_map_of_mem hcC)
    simp [LinearMap.comp_apply, this]
  · intro j v hv
    have hres0 : res v = 0 := by
      funext s
      simp [hres, LinearMap.funLeft_apply, hv (s : ι) s.2]
    have : π v = 0 := by
      simp only [hπ, LinearMap.comp_apply, hres0, map_zero]
    simp [LinearMap.comp_apply, this]

/-- A functional on `F^ι ⧸ C` induced by a row supported in `S ⊆ U` kills the kernel of the
local surjection `ρ_U`. -/
theorem liftQ_local (C : Submodule F (ι → F)) {S U : Finset ι} (hSU : S ⊆ U)
    (ℓ : Module.Dual F (ι → F)) (hker : C ≤ LinearMap.ker ℓ)
    (hloc : ∀ v : ι → F, (∀ x ∈ S, v x = 0) → ℓ v = 0)
    (q : (ι → F) ⧸ C) (hq : restrictQ C U q = 0) : C.liftQ ℓ hker q = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective C q
  rw [restrictQ_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
  obtain ⟨c, hc, hcv⟩ := Submodule.mem_map.mp hq
  have hvc : ℓ (v - c) = 0 := by
    apply hloc
    intro x hx
    have := congrFun hcv ⟨x, hSU hx⟩
    rw [resU_apply, resU_apply] at this
    simp [this]
  have hsplit : ℓ v = ℓ (v - c) + ℓ c := by rw [map_sub, sub_add_cancel]
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply, hsplit, hvc,
    LinearMap.mem_ker.mp (hker hc), add_zero]

/-- **G87 `exists_bridge_functionals` with locality exported.**  Same statement as G87 (same
index type `Fin r × Fin (t − finrank C)`, same annihilation and per-block independence), plus:
every bridge functional kills the kernel of the local surjection `ρ_U × ρ_U` whenever all
witness supports lie in `U`.  The proof is G87's, verbatim, with the extra conjunct. -/
theorem exists_bridge_functionals_local (C : Submodule F (ι → F)) {r t : ℕ} (U : Finset ι)
    {u₀ u₁ : ι → F} (γ : Fin r → F)
    (hwit : ∀ i, ∃ S : Finset ι, S ⊆ U ∧ S.card = t ∧
      ∃ c ∈ C, ∀ x ∈ S, c x = u₀ x + γ i * u₁ x) :
    ∃ φ : Fin r × Fin (t - finrank F C) → Module.Dual F (SyndromePair C),
      (∀ p, φ p (syndromePair C u₀ u₁) = 0) ∧
      (∀ i, LinearIndependent F fun j => φ (i, j)) ∧
      (∀ p, ∀ v : SyndromePair C,
        (restrictQ C U).prodMap (restrictQ C U) v = 0 → φ p v = 0) := by
  classical
  choose S hSU hS hagree using hwit
  have hrows : ∀ i, ∃ ℓ : Fin (t - finrank F C) → Module.Dual F (ι → F),
      LinearIndependent F ℓ ∧ (∀ j, ∀ x ∈ C, ℓ j x = 0) ∧
      (∀ j, ℓ j (u₀ + γ i • u₁) = 0) ∧
      (∀ j, ∀ v : ι → F, (∀ x ∈ S i, v x = 0) → ℓ j v = 0) :=
    fun i => exists_rowFunctionals_local C (hS i) (hagree i)
  choose ℓ hℓli hℓann hℓline hℓloc using hrows
  have hker : ∀ i j, C ≤ LinearMap.ker (ℓ i j) := fun i j x hx =>
    LinearMap.mem_ker.mpr (hℓann i j x hx)
  set lbar : Fin r → Fin (t - finrank F C) → Module.Dual F ((ι → F) ⧸ C) :=
    fun i j => C.liftQ (ℓ i j) (hker i j) with hlbar
  have hlbar_mk : ∀ i j (v : ι → F), lbar i j (C.mkQ v) = ℓ i j v := by
    intro i j v
    simp [hlbar, Submodule.mkQ_apply, Submodule.liftQ_apply]
  refine ⟨fun p =>
    (lbar p.1 p.2).comp (LinearMap.fst F _ _) +
      γ p.1 • (lbar p.1 p.2).comp (LinearMap.snd F _ _), ?_, ?_, ?_⟩
  · rintro ⟨i, j⟩
    have h1 : lbar i j (C.mkQ u₀) + γ i * lbar i j (C.mkQ u₁) = 0 := by
      rw [hlbar_mk, hlbar_mk]
      have := hℓline i j
      rw [map_add, map_smul] at this
      simpa [smul_eq_mul] using this
    simpa [syndromePair, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, smul_eq_mul] using h1
  · intro i
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have hzero : ∑ j, a j • ℓ i j = 0 := by
      apply LinearMap.ext
      intro v
      have := congrArg (fun f => f ((C.mkQ v, 0) : SyndromePair C)) ha
      simpa [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
        LinearMap.comp_apply, hlbar_mk] using this
    exact Fintype.linearIndependent_iff.mp (hℓli i) a hzero
  · rintro ⟨i, j⟩ ⟨q₀, q₁⟩ hv
    have h₀ : restrictQ C U q₀ = 0 := by
      simpa [LinearMap.prodMap_apply] using congrArg Prod.fst hv
    have h₁ : restrictQ C U q₁ = 0 := by
      simpa [LinearMap.prodMap_apply] using congrArg Prod.snd hv
    have e₀ : lbar i j q₀ = 0 :=
      liftQ_local C (hSU i) (ℓ i j) (hker i j) (hℓloc i j) q₀ h₀
    have e₁ : lbar i j q₁ = 0 :=
      liftQ_local C (hSU i) (ℓ i j) (hker i j) (hℓloc i j) q₁ h₁
    simp [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, e₀, e₁]

end Construction

/-! ## 4. The verdict on `hrank` -/

section Verdict

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The G87 bridge family violates `hrank` at `Ucard = |U|`.**  For any stack with `r`
witnesses whose supports lie in `U` (exactly SYZ43's `hwit`, localized) that does not jointly
agree with a codeword pair on `U`, the G87 construction yields a family with the G87 guarantees
(annihilation, per-block independence) **and** `finrank (span) + 1 ≤ 2 (|U| − dim C|_U)`. -/
theorem bridge_family_violates_hrank (C : Submodule F (ι → F)) {r t : ℕ} (U : Finset ι)
    {u₀ u₁ : ι → F} (γ : Fin r → F)
    (hwit : ∀ i, ∃ S : Finset ι, S ⊆ U ∧ S.card = t ∧
      ∃ c ∈ C, ∀ x ∈ S, c x = u₀ x + γ i * u₁ x)
    (hnj : ¬ pairJointAgreesOn (C : Set (ι → F)) U u₀ u₁) :
    ∃ φ : Fin r × Fin (t - finrank F C) → Module.Dual F (SyndromePair C),
      (∀ p, φ p (syndromePair C u₀ u₁) = 0) ∧
      (∀ i, LinearIndependent F fun j => φ (i, j)) ∧
      finrank F (Submodule.span F (Set.range φ)) + 1 ≤
        2 * (U.card - finrank F (codeRes C U)) := by
  obtain ⟨φ, hann, hblock, hloc⟩ := exists_bridge_functionals_local C U γ hwit
  exact ⟨φ, hann, hblock, localized_span_cap C U hnj φ hloc hann⟩

/-- **`hrank` is false for every `mcaEvent` stack.**  If one witness set `S₀ ⊆ U` carries the
`mcaEvent` clause `¬ pairJointAgreesOn C S₀ u₀ u₁`, and the restriction `C → C|_U` is
injective (`dim C|_U = dim C`, automatic for MDS codes once `|U| ≥ k`), then the G87 bridge
family satisfies `finrank (span) ≠ 2 (|U| − k)` — the SYZ42/SYZ43 residual `hrank` at
`Ucard = |U|` cannot hold.  (Stated for every `U`-local family with the G87 guarantees; the G87
proof constructs such a family.) -/
theorem hrank_false_of_mcaEvent_witness (C : Submodule F (ι → F)) {r t : ℕ} (U : Finset ι)
    {u₀ u₁ : ι → F} (γ : Fin r → F)
    (hwit : ∀ i, ∃ S : Finset ι, S ⊆ U ∧ S.card = t ∧
      ∃ c ∈ C, ∀ x ∈ S, c x = u₀ x + γ i * u₁ x)
    {S₀ : Finset ι} (hS₀U : S₀ ⊆ U)
    (hmca : ¬ pairJointAgreesOn (C : Set (ι → F)) S₀ u₀ u₁)
    (hkU : finrank F (codeRes C U) = finrank F C) :
    ∃ φ : Fin r × Fin (t - finrank F C) → Module.Dual F (SyndromePair C),
      (∀ p, φ p (syndromePair C u₀ u₁) = 0) ∧
      (∀ i, LinearIndependent F fun j => φ (i, j)) ∧
      finrank F (Submodule.span F (Set.range φ)) ≠ 2 * (U.card - finrank F C) := by
  obtain ⟨φ, hann, hblock, hcap⟩ :=
    bridge_family_violates_hrank C U γ hwit (not_pairJointAgreesOn_mono _ hS₀U hmca)
  refine ⟨φ, hann, hblock, ?_⟩
  rw [hkU] at hcap
  omega

/-- **Exact characterization (the honest F3).**  Conversely to the cap: for any `U`-local
family annihilating the syndrome pair, `finrank (span) = 2 (|U| − dim C|_U)` *forces* joint
codeword agreement on `U`.  So `hrank` at `Ucard = |U|` is not a realizability certificate for
an over-budget stack; it is a certificate that the stack is a codeword pair on `U`. -/
theorem pairJoint_of_hrank {D : Type*} (C : Submodule F (ι → F)) (U : Finset ι)
    {u₀ u₁ : ι → F} (φ : D → Module.Dual F (SyndromePair C))
    (hloc : ∀ p, ∀ v : SyndromePair C,
      (restrictQ C U).prodMap (restrictQ C U) v = 0 → φ p v = 0)
    (hann : ∀ p, φ p (syndromePair C u₀ u₁) = 0)
    (hrank : finrank F (Submodule.span F (Set.range φ)) =
      2 * (U.card - finrank F (codeRes C U))) :
    pairJointAgreesOn (C : Set (ι → F)) U u₀ u₁ := by
  by_contra hnj
  have := localized_span_cap C U hnj φ hloc hann
  omega

end Verdict

end ArkLib.ProximityGap.SW1F3

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SW1F3.span_cap_of_factors
#print axioms ArkLib.ProximityGap.SW1F3.forall_form_forces_Ucard_le_k
#print axioms ArkLib.ProximityGap.SW1F3.restrictQ_surjective
#print axioms ArkLib.ProximityGap.SW1F3.finrank_localPair
#print axioms ArkLib.ProximityGap.SW1F3.restrictQ_syndromePair_eq_zero_iff
#print axioms ArkLib.ProximityGap.SW1F3.localized_span_cap
#print axioms ArkLib.ProximityGap.SW1F3.exists_rowFunctionals_local
#print axioms ArkLib.ProximityGap.SW1F3.liftQ_local
#print axioms ArkLib.ProximityGap.SW1F3.exists_bridge_functionals_local
#print axioms ArkLib.ProximityGap.SW1F3.bridge_family_violates_hrank
#print axioms ArkLib.ProximityGap.SW1F3.hrank_false_of_mcaEvent_witness
#print axioms ArkLib.ProximityGap.SW1F3.pairJoint_of_hrank
