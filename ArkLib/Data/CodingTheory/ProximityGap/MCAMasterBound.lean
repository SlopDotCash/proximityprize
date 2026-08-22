/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# Pencil–subspace incidence master bound for the MCA bad-scalar count

This file proves a clean, fully general upper bound on the number of "bad scalars" of a
syndrome pencil — the combinatorial heart of the **mutual correlated agreement (MCA)
extremal count** `E(a)` on the syndrome plane (ABF26 §4, Grand Challenge 1 surface,
issue #141).

Via the validated syndrome-plane reduction, a scalar `γ` is MCA-bad at agreement level
`a` (with `e* := min(n-a, n-k-1)`) exactly when the pencil point `s₀ + γ • s₁` lands in
some span `V_E = span {hᵢ : i ∈ E}` of `e*` parity columns that does **not** contain `s₁`.
The key observation is a one-line **projective injectivity**: two distinct bad scalars can
never share the same witnessing subspace `V`, because their difference
`(γ - γ') • s₁ = (s₀ + γ•s₁) - (s₀ + γ'•s₁) ∈ V` together with invertibility of `γ - γ'`
would force `s₁ ∈ V`.  Hence the bad set injects into the subspace family, giving

  `E(a) ≤ C(n, e*)`   (`ncard_badScalars_le_choose`),

a **uniform master bound valid in every agreement band**, for every MDS code and every
evaluation domain.  This complements the exact `E(a) = n-a+1` law of the unique-decoding
band (`3e ≤ r`) and the CS25 volume bound: in the UDR band (`e*` bounded) it is polynomial
in `n`, the form Grand Challenge 1's `mcaConjecture` asks for.

## Main results

* `ncard_badScalars_le` — abstract form: for any field `K`, module `M`, syndromes
  `s₀ s₁ : M`, and finite subspace family `𝒱`, the bad-scalar set
  `{γ | ∃ V ∈ 𝒱, s₀ + γ•s₁ ∈ V ∧ s₁ ∉ V}` has `ncard ≤ 𝒱.card`.
* `ncard_badScalars_le_choose` — the binomial master bound: when the family is the
  `e`-subset-indexed spans over a finite index type `ι`, the count is `≤ C(|ι|, e)`.
-/

open Set

namespace ArkLib.MCAMasterBound


/-- **Master bound (abstract projective injectivity).**
For syndromes `s₀ s₁ : M` over a field `K` and a finite family `𝒱` of subspaces, the set of
"bad scalars" `γ` for which the pencil point `s₀ + γ • s₁` lands in some member `V ∈ 𝒱` that
does *not* contain `s₁` has cardinality at most `|𝒱|`.

Reason: two distinct bad scalars `γ ≠ γ'` cannot use the same witnessing `V`, because then
`(γ - γ') • s₁ = (s₀+γ•s₁) - (s₀+γ'•s₁) ∈ V`, and `γ - γ'` is an invertible scalar, forcing
`s₁ ∈ V` — contradicting `s₁ ∉ V`.  So the choice of witness is injective into `𝒱`. -/
theorem ncard_badScalars_le {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (s₀ s₁ : M) (𝒱 : Finset (Submodule K M)) :
    {γ : K | ∃ V ∈ 𝒱, s₀ + γ • s₁ ∈ V ∧ s₁ ∉ V}.ncard ≤ 𝒱.card := by
  classical
  set B := {γ : K | ∃ V ∈ 𝒱, s₀ + γ • s₁ ∈ V ∧ s₁ ∉ V} with hB
  have hwit : ∀ γ ∈ B, ∃ V, V ∈ 𝒱 ∧ (s₀ + γ • s₁ ∈ V ∧ s₁ ∉ V) := fun γ hγ => hγ
  choose! F hFmem hFin hFnotin using hwit
  have hmaps : ∀ γ ∈ B, F γ ∈ (↑𝒱 : Set (Submodule K M)) := fun γ hγ => hFmem γ hγ
  have hinj : Set.InjOn F B := by
    intro γ hγ γ' hγ' hFF
    by_contra hne
    have h1 : s₀ + γ • s₁ ∈ F γ := hFin γ hγ
    have h2 : s₀ + γ' • s₁ ∈ F γ := by rw [hFF]; exact hFin γ' hγ'
    have hdiff : (γ - γ') • s₁ ∈ F γ := by
      have hm := (F γ).sub_mem h1 h2
      have he : (γ - γ') • s₁ = (s₀ + γ • s₁) - (s₀ + γ' • s₁) := by rw [sub_smul]; abel
      rw [he]; exact hm
    have hs1 : s₁ ∈ F γ := by
      have hne' : γ - γ' ≠ 0 := sub_ne_zero.mpr hne
      have := (F γ).smul_mem (γ - γ')⁻¹ hdiff
      rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at this
    exact hFnotin γ hγ hs1
  have hcard : B.ncard ≤ (↑𝒱 : Set (Submodule K M)).ncard :=
    Set.ncard_le_ncard_of_injOn F hmaps hinj 𝒱.finite_toSet
  rwa [Set.ncard_coe_finset] at hcard

/-- **Binomial master bound for the MCA bad-scalar count.**
When the subspace family is indexed by the `e`-element subsets `E` of a finite index type
`ι` (think: `V E = span {parity columns hᵢ : i ∈ E}`), the number of bad scalars is at most
`C(|ι|, e)` — the count of `e`-subsets.  Combined with the syndrome-plane reduction this is
exactly the master bound `E(a) ≤ C(n, e*)` (`e* = min(n−a, n−k−1)`) on the MCA extremal
count, valid in **every** agreement band, for every MDS code and every evaluation domain. -/
theorem ncard_badScalars_le_choose {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [DecidableEq ι] [Fintype ι] (s₀ s₁ : M) (e : ℕ) (V : Finset ι → Submodule K M) :
    {γ : K | ∃ E : Finset ι, E.card = e ∧ s₀ + γ • s₁ ∈ V E ∧ s₁ ∉ V E}.ncard
      ≤ (Fintype.card ι).choose e := by
  classical
  set B := {γ : K | ∃ E : Finset ι, E.card = e ∧ s₀ + γ • s₁ ∈ V E ∧ s₁ ∉ V E} with hB
  set 𝒱 : Finset (Submodule K M) := (Finset.univ.powersetCard e).image V with h𝒱
  have hwit : ∀ γ ∈ B, ∃ E : Finset ι, E.card = e ∧ s₀ + γ • s₁ ∈ V E ∧ s₁ ∉ V E :=
    fun γ hγ => hγ
  choose! E hEcard hEin hEnot using hwit
  have hmaps : ∀ γ ∈ B, V (E γ) ∈ (↑𝒱 : Set (Submodule K M)) := by
    intro γ hγ
    rw [Finset.mem_coe, h𝒱, Finset.mem_image]
    exact ⟨E γ, by rw [Finset.mem_powersetCard]; exact ⟨Finset.subset_univ _, hEcard γ hγ⟩, rfl⟩
  have hinj : Set.InjOn (fun γ => V (E γ)) B := by
    intro γ hγ γ' hγ' hVV
    simp only at hVV
    by_contra hne
    have h1 : s₀ + γ • s₁ ∈ V (E γ) := hEin γ hγ
    have h2 : s₀ + γ' • s₁ ∈ V (E γ) := by rw [hVV]; exact hEin γ' hγ'
    have hdiff : (γ - γ') • s₁ ∈ V (E γ) := by
      have hm := (V (E γ)).sub_mem h1 h2
      have he : (γ - γ') • s₁ = (s₀ + γ • s₁) - (s₀ + γ' • s₁) := by rw [sub_smul]; abel
      rw [he]; exact hm
    have hs1 : s₁ ∈ V (E γ) := by
      have hne' : γ - γ' ≠ 0 := sub_ne_zero.mpr hne
      have := (V (E γ)).smul_mem (γ - γ')⁻¹ hdiff
      rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at this
    exact hEnot γ hγ hs1
  have hcard : B.ncard ≤ (↑𝒱 : Set (Submodule K M)).ncard :=
    Set.ncard_le_ncard_of_injOn (fun γ => V (E γ)) hmaps hinj 𝒱.finite_toSet
  rw [Set.ncard_coe_finset] at hcard
  refine hcard.trans ?_
  calc 𝒱.card ≤ (Finset.univ.powersetCard e).card := Finset.card_image_le
    _ = (Fintype.card ι).choose e := by
        simp [Finset.card_powersetCard, Finset.card_univ]

/-- **Degenerate (rank-≤1) pencil bound.**  If the syndromes are linearly dependent
(`s₀ ∈ span {s₁}`, i.e. the pencil is not a genuine projective line) then there is at most
one bad scalar.  This is the companion of `ncard_badScalars_le`: the syndrome-plane analysis
splits into the rank-≤1 case handled here (`≤ 1`) and the rank-2 case bounded by the master
bound — exactly the "WLOG the pencil is a genuine line" reduction of the UDR-ladder proof.

Reason: `s₀ = c • s₁`, so `s₀ + γ • s₁ = (c + γ) • s₁`; if it lies in `V` with `s₁ ∉ V`
then `c + γ = 0` (else dividing by the unit `c + γ` puts `s₁ ∈ V`), pinning `γ = -c`. -/
theorem ncard_badScalars_le_one_of_dependent {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] (s₀ s₁ : M) (𝒱 : Finset (Submodule K M))
    (hdep : s₀ ∈ Submodule.span K {s₁}) :
    {γ : K | ∃ V ∈ 𝒱, s₀ + γ • s₁ ∈ V ∧ s₁ ∉ V}.ncard ≤ 1 := by
  classical
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hdep
  have hsub : {γ : K | ∃ V ∈ 𝒱, s₀ + γ • s₁ ∈ V ∧ s₁ ∉ V} ⊆ {(-c : K)} := by
    intro γ hγ
    obtain ⟨V, _hV, hmem, hnot⟩ := hγ
    have hpenc : s₀ + γ • s₁ = (c + γ) • s₁ := by rw [← hc, add_smul]
    rw [hpenc] at hmem
    rw [Set.mem_singleton_iff]
    by_contra hγne
    have hcg : c + γ ≠ 0 := fun h => hγne (by linear_combination h)
    apply hnot
    have hs := V.smul_mem (c + γ)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hcg, one_smul] at hs
  calc {γ : K | ∃ V ∈ 𝒱, s₀ + γ • s₁ ∈ V ∧ s₁ ∉ V}.ncard
      ≤ ({(-c : K)} : Set K).ncard := Set.ncard_le_ncard hsub (Set.finite_singleton _)
    _ = 1 := Set.ncard_singleton _

open scoped Classical in
/-- **MDS-genericity incidence bound** (sharpening engine).  If every `(d+1)`-element
subfamily of `w : ι → M` is linearly independent — the defining genericity of an MDS dual,
where every `r` parity columns are independent — then any subspace `W` of dimension `≤ d`
contains at most `d` of the vectors `w i`.

Reason: `d+1` vectors `w i` inside `W` would be a linearly independent set (genericity) of
size `d+1` living in a space of dimension `≤ d`, which is impossible.

This sharpens the master bound below capacity: at agreement `a = n-1` (so `e* = 1`) the bad
patterns are single columns `span {hᵢ}`, and the bad scalars inject into the columns lying in
the `2`-dimensional syndrome pencil `Π`; for `r ≥ 3` at most `2` columns lie in `Π`, giving
the secant value `E(n-1) ≤ 2` — far below the master bound `C(n,1) = n`. -/
theorem card_indices_mem_le_of_general_position
    {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M] [Module.Finite K M]
    [Fintype ι] [DecidableEq ι] (w : ι → M) (W : Submodule K M) (d : ℕ)
    (hWd : Module.finrank K W ≤ d)
    (hgen : ∀ s : Finset ι, s.card = d + 1 → LinearIndependent K (fun i : ↥s => w ↑i)) :
    (Finset.univ.filter (fun i => w i ∈ W)).card ≤ d := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨s, hsub, hcard⟩ :=
    Finset.exists_subset_card_eq (n := d + 1)
      (show d + 1 ≤ (Finset.univ.filter (fun i => w i ∈ W)).card by omega)
  have hmem : ∀ i ∈ s, w i ∈ W := fun i hi => (Finset.mem_filter.mp (hsub hi)).2
  have hind : LinearIndependent K (fun i : ↥s => w ↑i) := hgen s hcard
  let v' : ↥s → W := fun i => ⟨w ↑i, hmem ↑i i.2⟩
  have hsubtype : (W.subtype) ∘ v' = (fun i : ↥s => w ↑i) := rfl
  have hv' : LinearIndependent K v' := by
    have h := hind
    rw [← hsubtype] at h
    exact h.of_comp W.subtype
  have hcardle : Fintype.card ↥s ≤ Module.finrank K W := hv'.fintype_card_le_finrank
  rw [Fintype.card_coe, hcard] at hcardle
  omega

open scoped Classical in
/-- **Secant bound** `E(n-1) ≤ 2`: at agreement one below the length, with a genuine pencil
(`s₀ + γ•s₁ ≠ 0`, i.e. `s₀ ∉ span{s₁}`) and MDS genericity (every 3 of the parity columns
independent, i.e. dual distance `r ≥ 3`), there are at most 2 bad scalars — far below the
master bound `C(n,1) = n`. -/
theorem ncard_badScalars_singleton_le_two
    {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M] [Module.Finite K M]
    [Fintype ι] [DecidableEq ι] [Nonempty ι] (s₀ s₁ : M) (h : ι → M)
    (hpen : ∀ γ : K, s₀ + γ • s₁ ≠ 0)
    (hgen : ∀ t : Finset ι, t.card = 3 → LinearIndependent K (fun i : ↥t => h ↑i)) :
    {γ : K | ∃ i : ι, s₀ + γ • s₁ ∈ Submodule.span K {h i} ∧ s₁ ∉ Submodule.span K {h i}}.ncard
      ≤ 2 := by
  classical
  set pencil := Submodule.span K ({s₀, s₁} : Set M) with hpencil
  set B := {γ : K | ∃ i : ι, s₀ + γ • s₁ ∈ Submodule.span K {h i} ∧ s₁ ∉ Submodule.span K {h i}}
    with hB
  have hwit : ∀ γ ∈ B, ∃ i, s₀ + γ • s₁ ∈ Submodule.span K {h i} ∧ s₁ ∉ Submodule.span K {h i} :=
    fun γ hγ => hγ
  choose! wi hwin hwinot using hwit
  have himg : ∀ γ ∈ B, wi γ ∈ Finset.univ.filter (fun i => h i ∈ pencil) := by
    intro γ hγ
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hwin γ hγ)
    have hc0 : c ≠ 0 := fun h0 => hpen γ (by rw [h0, zero_smul] at hc; exact hc.symm)
    have hheq : h (wi γ) = c⁻¹ • (s₀ + γ • s₁) := by
      rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [hheq]
    exact pencil.smul_mem _ (add_mem (Submodule.subset_span (by simp))
      (pencil.smul_mem _ (Submodule.subset_span (by simp))))
  have hinj : Set.InjOn wi B := by
    intro γ hγ γ' hγ' hww
    by_contra hne
    have h1 : s₀ + γ • s₁ ∈ Submodule.span K {h (wi γ)} := hwin γ hγ
    have h2 : s₀ + γ' • s₁ ∈ Submodule.span K {h (wi γ)} := by rw [hww]; exact hwin γ' hγ'
    have hdiff : (γ - γ') • s₁ ∈ Submodule.span K {h (wi γ)} := by
      have hm := (Submodule.span K {h (wi γ)}).sub_mem h1 h2
      have he : (γ - γ') • s₁ = (s₀ + γ • s₁) - (s₀ + γ' • s₁) := by rw [sub_smul]; abel
      rw [he]; exact hm
    have hs1 : s₁ ∈ Submodule.span K {h (wi γ)} := by
      have hne' : γ - γ' ≠ 0 := sub_ne_zero.mpr hne
      have hsm := (Submodule.span K {h (wi γ)}).smul_mem (γ - γ')⁻¹ hdiff
      rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at hsm
    exact hwinot γ hγ hs1
  have hfin2 : Module.finrank K pencil ≤ 2 := by
    have h1 := finrank_span_le_card (R := K) ({s₀, s₁} : Set M)
    have h2 : ({s₀, s₁} : Set M).toFinset.card ≤ 2 := by
      rw [Set.toFinset_insert, Set.toFinset_singleton]
      exact (Finset.card_insert_le _ _).trans (by simp)
    exact le_trans h1 h2
  have hgenf : (Finset.univ.filter (fun i => h i ∈ pencil)).card ≤ 2 :=
    card_indices_mem_le_of_general_position h pencil 2 hfin2 (fun t ht => hgen t ht)
  calc B.ncard
      ≤ (↑(Finset.univ.filter (fun i => h i ∈ pencil)) : Set ι).ncard :=
        Set.ncard_le_ncard_of_injOn wi (fun γ hγ => Finset.mem_coe.mpr (himg γ hγ)) hinj
          (Finset.finite_toSet _)
    _ = (Finset.univ.filter (fun i => h i ∈ pencil)).card := Set.ncard_coe_finset _
    _ ≤ 2 := hgenf

end ArkLib.MCAMasterBound
