/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.Connections.GKL24MaxDomainExists

/-!
# GKL24 sunflower core: the common agreement core of two bad lines is a joint-agreement domain

This file supplies the missing *distinct-codeword* sunflower-core fact behind GKL24 Lemma 1
(issue #363).  `GKL24MaxDomainExists.lean` proves `lineAgreeSet_inter_eq` for a **single fixed**
codeword `w`; the genuine sunflower step of the maximal-domain argument needs the **distinct**-
codeword version, where each bad combiner `γ` carries its *own* close codeword `wOf γ`.

The kernel proved here:

* `pairJointAgreesOn_inter_lineAgreeSet` — for distinct combiners `γ ≠ γ'` and codewords
  `wγ, wγ' ∈ MC`, the overlap `lineAgreeSet wγ γ ∩ lineAgreeSet wγ' γ'` is a **joint-agreement
  domain**: on the overlap the pair `(u₀, u₁)` is reconstructed from the two lines by linear
  algebra — `u₁ = (wγ − wγ')/(γ − γ')` and `u₀ = wγ − γ·u₁` are codewords of `MC`.

  This is exactly why the *common core* of two bad lines is absorbed by any **maximal**
  joint-agreement domain (`maxCorrAgreeDomain`): the core is itself a correlated-agreement domain
  once it is large, so maximality forces it inside `D`.

Two assembly corollaries:

* `lineAgreeSet_inter_card_ge_pn` / `corrAgreeDomain_inter_lineAgreeSet` — the Bonferroni size
  bound (`2δ ≤ p ≤ 1`) lifts the kernel to a full `corrAgreeDomain` at rate `p` for two
  bad-witness combiners.  This discharges, for the *decoded* codewords `wOf γ := wγ`, the pairwise
  `(1−p)·n` intersection clause of `GKL24MaxDomainWitnessCoverFalseAsStated` directly — no maximality
  argument is needed for the *size* of the intersection, only Bonferroni.

* `corrAgreeDomain_subset_lineAgreeSet_lineCombiner` — from a correlated-agreement domain `D`
  witnessed by codewords `(a, b)`, the line combiner `wOf γ := a + γ·b ∈ MC` satisfies
  `D ⊆ lineAgreeSet (wOf γ) γ` for **every** `γ`; hence (via `corrAgreeDomain_subset_inter_card`)
  the pairwise intersection clause holds for the combiner codewords as well.

Together with the in-tree maximal-domain existence and petal machinery, these isolate what the
retired over-strong surface (`GKL24MaxDomainWitnessCoverFalseAsStated`, file
`GKL24PetalWitnessCover.lean`) would need under repaired side conditions: the **strict-expansion**
clause `D ⊂ lineAgreeSet (wOf γ) γ` for a maximal `D` — equivalently, that the maximal
joint-agreement domain lands strictly inside each bad line's agreement set — plus the
close-codeword carrier `T`.

## References

* [GKL24] Guruswami, Kumar, Liu. Agree-domain intersection / first-moment count (Lemma 1).
* [GCXK25] Gao, Cai, Xu, Kan. *From List-Decodability to Proximity Gaps*. eprint 2025/870.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open scoped NNReal
open Finset Code

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **GKL24 sunflower core (distinct combiners).**  On the overlap of two line-agreement sets for
distinct combiners `γ ≠ γ'` and codewords `wγ, wγ' ∈ MC`, the pair `(u₀, u₁)` jointly agrees with
codewords of `MC`.  The reconstruction is pure linear algebra: where both lines equal `(u₀,u₁)`,
their difference pins `u₁ = (γ − γ')⁻¹ · (wγ − wγ')` and then `u₀ = wγ − γ · u₁`, both codewords.

This is the distinct-codeword analogue of `lineAgreeSet_inter_eq` (single fixed `w`), and the
reason the common core of two bad lines is a correlated-agreement domain. -/
theorem pairJointAgreesOn_inter_lineAgreeSet
    (MC : Submodule F (ι → F)) {u₀ u₁ wγ wγ' : ι → F} {γ γ' : F} (hγ : γ ≠ γ')
    (hwγ : wγ ∈ MC) (hwγ' : wγ' ∈ MC) :
    pairJointAgreesOn (MC : Set (ι → F))
      (lineAgreeSet u₀ u₁ wγ γ ∩ lineAgreeSet u₀ u₁ wγ' γ') u₀ u₁ := by
  have hsub : (γ - γ') ≠ 0 := sub_ne_zero.mpr hγ
  -- the reconstructed second row, a codeword
  set b : ι → F := (γ - γ')⁻¹ • (wγ - wγ') with hb
  have hbmem : b ∈ MC := MC.smul_mem _ (MC.sub_mem hwγ hwγ')
  -- the reconstructed first row, a codeword
  refine ⟨wγ - γ • b, MC.sub_mem hwγ (MC.smul_mem _ hbmem), b, hbmem, ?_⟩
  intro i hi
  rw [Finset.mem_inter, mem_lineAgreeSet_iff, mem_lineAgreeSet_iff] at hi
  obtain ⟨h1, h2⟩ := hi
  -- second row: b i = u₁ i
  have hbi : b i = u₁ i := by
    have hdiff : wγ i - wγ' i = (γ - γ') • u₁ i := by
      rw [h1, h2, sub_smul]; abel
    rw [hb, Pi.smul_apply, Pi.sub_apply, hdiff, smul_smul, inv_mul_cancel₀ hsub, one_smul]
  -- first row: (wγ - γ • b) i = u₀ i
  refine ⟨?_, hbi⟩
  rw [Pi.sub_apply, Pi.smul_apply, hbi, h1]
  abel

/-- **The common core of two bad lines is large.**  Bonferroni: if both line-agreement sets have
size `≥ (1−δ)·n` (as for two bad-witness combiners) and `2δ ≤ p ≤ 1`, then their overlap has size
`≥ (1−p)·n`.  This is exactly the pairwise `(1−p)·n` intersection clause of
`GKL24MaxDomainWitnessCoverFalseAsStated` for the decoded codewords — no maximality needed. -/
theorem lineAgreeSet_inter_card_ge_pn
    {δ p : ℝ≥0} {u₀ u₁ wγ wγ' : ι → F} {γ γ' : F}
    (hp1 : p ≤ 1) (h2δp : 2 * δ ≤ p)
    (hAγ : ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ ((lineAgreeSet u₀ u₁ wγ γ).card : ℝ≥0))
    (hAγ' : ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ ((lineAgreeSet u₀ u₁ wγ' γ').card : ℝ≥0)) :
    ((1 - p) * Fintype.card ι : ℝ≥0)
      ≤ (((lineAgreeSet u₀ u₁ wγ γ ∩ lineAgreeSet u₀ u₁ wγ' γ').card : ℕ) : ℝ≥0) := by
  have hδ1 : δ ≤ 1 := by
    calc δ ≤ 2 * δ := by rw [two_mul]; exact le_add_self
      _ ≤ p := h2δp
      _ ≤ 1 := hp1
  -- ℕ Bonferroni: |A| + |B| ≤ n + |A ∩ B|
  have hbon : (lineAgreeSet u₀ u₁ wγ γ).card + (lineAgreeSet u₀ u₁ wγ' γ').card
      ≤ Fintype.card ι + (lineAgreeSet u₀ u₁ wγ γ ∩ lineAgreeSet u₀ u₁ wγ' γ').card := by
    have h := Finset.card_union_add_card_inter
      (lineAgreeSet u₀ u₁ wγ γ) (lineAgreeSet u₀ u₁ wγ' γ')
    have hu : (lineAgreeSet u₀ u₁ wγ γ ∪ lineAgreeSet u₀ u₁ wγ' γ').card ≤ Fintype.card ι := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
    omega
  -- move to ℝ where subtraction is genuine
  rw [← NNReal.coe_le_coe]
  have hgoal_eq : (((1 - p) * Fintype.card ι : ℝ≥0) : ℝ)
      = (1 - (p : ℝ)) * (Fintype.card ι : ℝ) := by
    rw [NNReal.coe_mul, NNReal.coe_sub hp1, NNReal.coe_one, NNReal.coe_natCast]
  rw [hgoal_eq, NNReal.coe_natCast]
  have hAγℝ : (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) ≤ (lineAgreeSet u₀ u₁ wγ γ).card := by
    have := (NNReal.coe_le_coe.mpr hAγ); rwa [NNReal.coe_mul, NNReal.coe_sub hδ1, NNReal.coe_one,
      NNReal.coe_natCast] at this
  have hAγ'ℝ : (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) ≤ (lineAgreeSet u₀ u₁ wγ' γ').card := by
    have := (NNReal.coe_le_coe.mpr hAγ'); rwa [NNReal.coe_mul, NNReal.coe_sub hδ1, NNReal.coe_one,
      NNReal.coe_natCast] at this
  have hbonℝ : ((lineAgreeSet u₀ u₁ wγ γ).card : ℝ) + (lineAgreeSet u₀ u₁ wγ' γ').card
      ≤ (Fintype.card ι : ℝ) + (lineAgreeSet u₀ u₁ wγ γ ∩ lineAgreeSet u₀ u₁ wγ' γ').card := by
    exact_mod_cast hbon
  have h2δpℝ : 2 * (δ : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2δp
  have hn0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hkey : 2 * (δ : ℝ) * (Fintype.card ι : ℝ) ≤ (p : ℝ) * (Fintype.card ι : ℝ) :=
    mul_le_mul_of_nonneg_right h2δpℝ hn0
  nlinarith [hAγℝ, hAγ'ℝ, hbonℝ, hkey]

/-- **The common core of two bad lines is a correlated-agreement domain.**  Combining the sunflower
core (`pairJointAgreesOn_inter_lineAgreeSet`) with the Bonferroni size bound
(`lineAgreeSet_inter_card_ge_pn`): for two bad-witness combiners `γ ≠ γ'` (line-agreement
`≥ (1−δ)·n`) with `2δ ≤ p ≤ 1`, the overlap is a `corrAgreeDomain` at rate `p`. -/
theorem corrAgreeDomain_inter_lineAgreeSet
    (MC : Submodule F (ι → F)) {δ p : ℝ≥0} {u₀ u₁ wγ wγ' : ι → F} {γ γ' : F} (hγ : γ ≠ γ')
    (hwγ : wγ ∈ MC) (hwγ' : wγ' ∈ MC) (hp1 : p ≤ 1) (h2δp : 2 * δ ≤ p)
    (hAγ : ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ ((lineAgreeSet u₀ u₁ wγ γ).card : ℝ≥0))
    (hAγ' : ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ ((lineAgreeSet u₀ u₁ wγ' γ').card : ℝ≥0)) :
    corrAgreeDomain MC p u₀ u₁
      (lineAgreeSet u₀ u₁ wγ γ ∩ lineAgreeSet u₀ u₁ wγ' γ') :=
  ⟨lineAgreeSet_inter_card_ge_pn hp1 h2δp hAγ hAγ',
   pairJointAgreesOn_inter_lineAgreeSet MC hγ hwγ hwγ'⟩

/-- **The combiner codeword of a correlated-agreement domain.**  From `(a, b)` witnessing the joint
agreement on a correlated-agreement domain `D`, the combiner `a + γ·b ∈ MC` has line-agreement set
containing `D` for **every** combiner `γ`: on `D` both rows are pinned, so `(a + γ·b) = u₀ + γ·u₁`
there.  This is the construction making the residual's `wOf` well-defined and its `D ⊆ lineAgreeSet`
and pairwise-intersection clauses immediate (the latter via `corrAgreeDomain_subset_inter_card`). -/
theorem corrAgreeDomain_subset_lineAgreeSet_lineCombiner
    {MC : Submodule F (ι → F)} {p : ℝ≥0} {u₀ u₁ : ι → F} {D : Finset ι}
    (hD : corrAgreeDomain MC p u₀ u₁ D) :
    ∃ a ∈ MC, ∃ b ∈ MC, ∀ γ : F, D ⊆ lineAgreeSet u₀ u₁ (a + γ • b) γ := by
  obtain ⟨-, a, ha, b, hb, hab⟩ := hD
  refine ⟨a, ha, b, hb, fun γ i hi => ?_⟩
  rw [mem_lineAgreeSet_iff, Pi.add_apply, Pi.smul_apply]
  obtain ⟨ha', hb'⟩ := hab i hi
  rw [ha', hb']

/-- **Strict expansion reduces to containment, for bad witnesses.**  If `γ` is a bad witness of a
codeword `w` (so its agreement set `S` of size `≥ (1−δ)·n` carries the line but is **not** a
joint-agreement set) and a joint-agreement domain `D` is contained in `lineAgreeSet w γ`, then the
containment is **strict**: `D ⊊ lineAgreeSet w γ`.

Reason: if `D = lineAgreeSet w γ`, then `S ⊆ lineAgreeSet w γ = D`, and joint agreement on `D`
restricts to joint agreement on `S` (the agreeing codeword pair agrees on every subset) —
contradicting `¬ pairJointAgreesOn S`.  This discharges the residual's strict-expansion clause from
the bare **containment** `D ⊆ lineAgreeSet (wOf γ) γ`; no cardinality comparison is needed. -/
theorem ssubset_lineAgreeSet_of_subset_of_pairJointAgreesOn
    {MC : Submodule F (ι → F)} {δ : ℝ≥0} {u₀ u₁ w : ι → F} {γ : F} {D : Finset ι}
    (hγ : γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w)
    (hDsub : D ⊆ lineAgreeSet u₀ u₁ w γ)
    (hDjoint : pairJointAgreesOn (MC : Set (ι → F)) D u₀ u₁) :
    D ⊂ lineAgreeSet u₀ u₁ w γ := by
  classical
  rw [mcaBadWitness, Finset.mem_filter] at hγ
  obtain ⟨S, _hScard, hSagree, hSnojoint⟩ := hγ.2
  have hSsub : S ⊆ lineAgreeSet u₀ u₁ w γ := fun i hi => by
    rw [mem_lineAgreeSet_iff]; exact hSagree i hi
  refine lt_of_le_of_ne (Finset.le_iff_subset.mpr hDsub) (fun hEq => hSnojoint ?_)
  -- `D = lineAgreeSet`, so `S ⊆ D`, and joint agreement on `D` restricts to `S`.
  obtain ⟨v₀, hv₀, v₁, hv₁, hagree⟩ := hDjoint
  exact ⟨v₀, hv₀, v₁, hv₁, fun i hi => hagree i (hEq ▸ hSsub hi)⟩

/-- **The strict witness-cover false surface reduces to the non-strict (subset) cover.**  A
provider for
`GKL24MaxCorrStrictWitnessCoverFalseAsStated` (file `GKL24FirstMoment.lean`, previously with no
reduction theorems): it suffices to supply, per stack, a close-codeword carrier `T` and, for each
`w ∈ T`, a maximal correlated-agreement domain `D` merely **contained** in (not strictly expanded
by) each bad line-agreement set `lineAgreeSet w γ`.  The strict expansion is then automatic
(`ssubset_lineAgreeSet_of_subset_of_pairJointAgreesOn`), since `D` is a joint-agreement domain (part
of `maxCorrAgreeDomain`) and each `γ`'s witness is non-joint.

This removes the strictness obligation from the hard GKL24 input: only the *containment* of the
maximal domain in every bad witness's agreement set remains. -/
theorem GKL24MaxCorrStrictWitnessCoverFalseAsStated_of_subset_cover
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) {B_T : ℝ}
    (hcover : ∀ u : WordStack F (Fin 2) ι,
      ∃ T : Finset (ι → F),
        (∀ w ∈ T, w ∈ (MC : Set (ι → F))) ∧
        mcaBad (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) ⊆
          T.biUnion (fun w =>
            mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w) ∧
        (T.card : ℝ) ≤ B_T ∧
        ∀ w ∈ T, ∃ D : Finset ι, maxCorrAgreeDomain MC p (u 0) (u 1) D ∧
          ∀ γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w,
            D ⊆ lineAgreeSet (u 0) (u 1) w γ) :
    GKL24MaxCorrStrictWitnessCoverFalseAsStated MC δ p B_T := by
  intro u
  obtain ⟨T, hTsub, hcov, hcard, hT⟩ := hcover u
  refine ⟨T, hTsub, hcov, hcard, fun w hw => ?_⟩
  obtain ⟨D, hD, hDsub⟩ := hT w hw
  exact ⟨D, hD, fun γ hγ =>
    ssubset_lineAgreeSet_of_subset_of_pairJointAgreesOn hγ (hDsub γ hγ) hD.1.2⟩

/-- **The common zero set IS the maximal correlated-agreement domain, for a multi-witness codeword.**
When a codeword `w` has two distinct bad witnesses `γ ≠ γ'`, the common zero set
`C₀ = {i : u₁ᵢ = 0 ∧ wᵢ = u₀ᵢ}` is a `maxCorrAgreeDomain` at rate `p`:

* it is a correlated-agreement domain — joint via `(w, 0)` (`pairJointAgreesOn_common`), and large
  (`|C₀| = |lineAgreeSet w γ ∩ lineAgreeSet w γ'| ≥ (1−p)·n`, Bonferroni + `2δ ≤ p`);
* it is **maximal** — any correlated-agreement domain `E ⊇ C₀` agrees with codewords `(v₀, v₁)` on
  `E`; on `C₀` then `v₁ = 0` and `v₀ = w`, so by the code-determination hypothesis `hCodeDet`
  (codewords agreeing on `C₀` coincide — a Johnson-regime `p·n < minDist` consequence, since
  `|C₀| ≥ (1−p)n`) we get `v₁ ≡ 0` and `v₀ ≡ w`, forcing `E ⊆ C₀`.

This is the structural heart of GKL24 Lemma 1's per-codeword maximal domain in the regime where it
is satisfiable: `C₀` discharges the residual's `maxCorrAgreeDomain` and (being contained in every
`lineAgreeSet w γ`) the strict-expansion clause via
`ssubset_lineAgreeSet_of_subset_of_pairJointAgreesOn`. -/
theorem maxCorrAgreeDomain_commonZero_of_two_witnesses
    {MC : Submodule F (ι → F)} {δ p : ℝ≥0} {u₀ u₁ w : ι → F} (hw : w ∈ MC)
    {γ γ' : F} (hγ : γ ≠ γ')
    (hbad : γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w)
    (hbad' : γ' ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w)
    (hp1 : p ≤ 1) (h2δp : 2 * δ ≤ p)
    (hCodeDet : ∀ a ∈ MC, ∀ b ∈ MC,
      (∀ i ∈ Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i), a i = b i) → a = b) :
    maxCorrAgreeDomain MC p u₀ u₁
      (Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i)) := by
  classical
  set C₀ := Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i) with hC₀def
  have hC₀eq : C₀ = lineAgreeSet u₀ u₁ w γ ∩ lineAgreeSet u₀ u₁ w γ' :=
    (lineAgreeSet_inter_eq u₀ u₁ w hγ).symm
  have hjoint : pairJointAgreesOn (MC : Set (ι → F)) C₀ u₀ u₁ := pairJointAgreesOn_common hw
  have hcard : ((1 - p) * Fintype.card ι : ℝ≥0) ≤ (C₀.card : ℝ≥0) := by
    rw [hC₀eq]
    exact lineAgreeSet_inter_card_ge_pn hp1 h2δp
      (card_lineAgreeSet_ge_of_mem_mcaBadWitness (MC := MC) hbad)
      (card_lineAgreeSet_ge_of_mem_mcaBadWitness (MC := MC) hbad')
  refine ⟨⟨hcard, hjoint⟩, fun E hC₀E hE => ?_⟩
  obtain ⟨_, v₀, hv₀, v₁, hv₁, hagreeE⟩ := hE
  have hv1zero : v₁ = 0 := by
    refine hCodeDet v₁ hv₁ 0 MC.zero_mem (fun i hi => ?_)
    have hmem := hi
    rw [hC₀def, Finset.mem_filter] at hmem
    rw [Pi.zero_apply, (hagreeE i (hC₀E hi)).2]; exact hmem.2.1
  have hv0w : v₀ = w := by
    refine hCodeDet v₀ hv₀ w hw (fun i hi => ?_)
    have hmem := hi
    rw [hC₀def, Finset.mem_filter] at hmem
    rw [(hagreeE i (hC₀E hi)).1]; exact hmem.2.2.symm
  intro i hiE
  rw [hC₀def, Finset.mem_filter]
  refine ⟨Finset.mem_univ i, ?_, ?_⟩
  · rw [← (hagreeE i hiE).2, hv1zero, Pi.zero_apply]
  · rw [← (hagreeE i hiE).1, hv0w]

/-- **Per-codeword discharge for multi-witness codewords.**  Combining
`maxCorrAgreeDomain_commonZero_of_two_witnesses` with the strict-expansion lemma: if every bad
witness `γ` of `w` is paired (some other witness exists) and `hCodeDet` holds, then `C₀` witnesses
the historical surface's per-`w` clause — a maximal domain strictly expanded by every
`lineAgreeSet w γ`. -/
theorem exists_maxCorrAgreeDomain_strict_of_two_witnesses
    {MC : Submodule F (ι → F)} {δ p : ℝ≥0} {u₀ u₁ w : ι → F} (hw : w ∈ MC)
    {γ₀ γ₀' : F} (hγ : γ₀ ≠ γ₀')
    (hbad₀ : γ₀ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w)
    (hbad₀' : γ₀' ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w)
    (hp1 : p ≤ 1) (h2δp : 2 * δ ≤ p)
    (hCodeDet : ∀ a ∈ MC, ∀ b ∈ MC,
      (∀ i ∈ Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i), a i = b i) → a = b) :
    ∃ D : Finset ι, maxCorrAgreeDomain MC p u₀ u₁ D ∧
      ∀ γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w,
        D ⊂ lineAgreeSet u₀ u₁ w γ := by
  classical
  set C₀ := Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i) with hC₀def
  have hmax := maxCorrAgreeDomain_commonZero_of_two_witnesses hw hγ hbad₀ hbad₀' hp1 h2δp hCodeDet
  refine ⟨C₀, hmax, fun γ hγbad => ?_⟩
  -- C₀ ⊆ lineAgreeSet w γ: on C₀, u₁ = 0 and w = u₀, so w = u₀ + γ • u₁
  have hsub : C₀ ⊆ lineAgreeSet u₀ u₁ w γ := by
    intro i hi
    rw [hC₀def, Finset.mem_filter] at hi
    rw [mem_lineAgreeSet_iff, hi.2.1, smul_zero, add_zero]; exact hi.2.2
  exact ssubset_lineAgreeSet_of_subset_of_pairJointAgreesOn hγbad hsub hmax.1.2

end ProximityGap

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.pairJointAgreesOn_inter_lineAgreeSet
#print axioms ProximityGap.lineAgreeSet_inter_card_ge_pn
#print axioms ProximityGap.corrAgreeDomain_inter_lineAgreeSet
#print axioms ProximityGap.corrAgreeDomain_subset_lineAgreeSet_lineCombiner
#print axioms ProximityGap.ssubset_lineAgreeSet_of_subset_of_pairJointAgreesOn
#print axioms ProximityGap.GKL24MaxCorrStrictWitnessCoverFalseAsStated_of_subset_cover
#print axioms ProximityGap.maxCorrAgreeDomain_commonZero_of_two_witnesses
#print axioms ProximityGap.exists_maxCorrAgreeDomain_strict_of_two_witnesses
