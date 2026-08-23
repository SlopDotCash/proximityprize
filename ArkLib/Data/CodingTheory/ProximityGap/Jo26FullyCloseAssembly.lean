/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Jo26DeviationKernels

/-!
# S2(b′) assembly, fully-close case: the deviation-kernel dominating family (#357)

`Jo26DeviationKernels.lean` proved that in the CA-explained regime every proper
obstruction subspace is `⊥` or pinned by a single nonzero deviation covector.  This
file assembles that pinning into an actual `ObstructionBound` instance:

* `devKernel` — the kernel `{λ : λ₀·e₀ + λ₁·e₁ = 0}` of a covector `e : Fin 2 → A`,
  as a submodule of `F²`; proper iff `e ≠ 0` (`devKernel_ne_top_of_ne_zero`).
* `proper_le_span_of_mem` — a proper submodule of `F²` containing a nonzero vector
  *equals* its span (factored from `proper_eq_bot_or_span`); used to upgrade the
  pinning `K_T ≤ devKernel e` to *membership* `K_T = devKernel e`.
* **`obstructionBound_of_fullyClose`** — the dominating family
  `{⊥} ∪ {devKernel(deviation U c j i) : deviation ≠ 0}` has at most `l·n + 1`
  members — **field-independent** — and captures every bad-seed obstruction.  Under
  `l·n + 1 ≤ q` (automatic in the deployed regime `q ≥ 2^128 ≫ n·l`),
  `ObstructionBound` holds, and with it generator-MCA interleaving exactness.

Named inputs (both shaped exactly like the in-tree CA-below-Johnson surfaces):
`hexp` — each row is explained by a codeword pair on a common set `S*` (per-row
correlated agreement, intersected); `hforce` — agreement on `T ∩ S*` forces codeword
equality for witness-sized `T` (the code-distance threshold).
-/

open Finset NNReal Code
open scoped BigOperators

namespace ProximityGap.Jo26Obstruction

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The kernel of a covector `e : Fin 2 → A`: combiners `λ` with
`λ₀·e₀ + λ₁·e₁ = 0`.  A submodule of `F²`. -/
def devKernel (e : Fin 2 → A) : Submodule F (Fin 2 → F) where
  carrier := {lam | ∑ k, lam k • e k = 0}
  zero_mem' := by simp
  add_mem' := by
    intro lam mu hlam hmu
    have : ∑ k, (lam + mu) k • e k
        = (∑ k, lam k • e k) + ∑ k, mu k • e k := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [Pi.add_apply, add_smul]
    simp only [Set.mem_setOf_eq] at hlam hmu ⊢
    rw [this, hlam, hmu, add_zero]
  smul_mem' := by
    intro a lam hlam
    have : ∑ k, (a • lam) k • e k = a • ∑ k, lam k • e k := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => by
        rw [Pi.smul_apply, smul_smul, smul_eq_mul]
    simp only [Set.mem_setOf_eq] at hlam ⊢
    rw [this, hlam, smul_zero]

/-- The kernel of a NONZERO covector is proper: a basis vector escapes. -/
theorem devKernel_ne_top_of_ne_zero {e : Fin 2 → A} (he : e ≠ 0) :
    (devKernel (F := F) e) ≠ ⊤ := by
  intro htop
  apply he
  funext k
  fin_cases k
  · have h0 : (fun k' : Fin 2 => if k' = 0 then (1 : F) else 0)
        ∈ devKernel (F := F) e := by rw [htop]; trivial
    simpa [devKernel, Fin.sum_univ_two] using h0
  · have h1 : (fun k' : Fin 2 => if k' = 1 then (1 : F) else 0)
        ∈ devKernel (F := F) e := by rw [htop]; trivial
    simpa [devKernel, Fin.sum_univ_two] using h1

/-- Membership in `devKernel` is the kill condition. -/
theorem mem_devKernel_iff {e : Fin 2 → A} {lam : Fin 2 → F} :
    lam ∈ devKernel (F := F) e ↔ ∑ k, lam k • e k = 0 := Iff.rfl

omit [Fintype F] [DecidableEq F] in
/-- A proper submodule of `F²` containing a nonzero vector equals its span
(factored from the ≤-direction of `proper_eq_bot_or_span`). -/
theorem proper_eq_span_of_mem {K : Submodule F (Fin 2 → F)} (hK : K ≠ ⊤)
    {lam : Fin 2 → F} (hlam : lam ∈ K) (hlam0 : lam ≠ 0) :
    K = Submodule.span F {lam} := by
  rcases proper_eq_bot_or_span K hK with hbot | ⟨mu, hmu0, hmuK, hspan⟩
  · exact absurd (hbot ▸ hlam) (by simpa using hlam0)
  · -- K = span mu and lam ∈ K nonzero ⟹ span lam = span mu
    rw [hspan]
    have hlam' : lam ∈ Submodule.span F {mu} := hspan ▸ hlam
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hlam'
    have ha0 : a ≠ 0 := by
      intro h
      apply hlam0
      rw [← ha, h, zero_smul]
    apply le_antisymm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      rw [show mu = a⁻¹ • lam by rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self lam)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      rw [← ha]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self mu)

open Classical in
/-- **The fully-close case of S2(b′), assembled.**  If every row of the stack is
explained by codeword pairs on a common set `S*`, and agreement on `T ∩ S*` forces
codeword equality for every witness-sized `T`, then the deviation-kernel family
`{⊥} ∪ {devKernel(deviation U c j i)}` dominates every bad-seed obstruction.  Its
size is at most `l·n + 1` — independent of the field — so in any field with
`l·n + 1 ≤ q` the `ObstructionBound` holds, and with it (via
`epsMCAG_interleaved_eq_of_obstructionBound`) generator-MCA interleaving exactness. -/
theorem obstructionBound_of_fullyClose
    (C : Submodule F (ι → A)) (δ : ℝ≥0) {l : ℕ}
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F)
    (U : Fin l → ι → Fin 2 → A) (c : Fin l → Fin 2 → ι → A) (Sstar : Finset ι)
    (hcw : ∀ j k, c j k ∈ (C : Set (ι → A)))
    (hexp : ∀ j k, ∀ i ∈ Sstar, c j k i = U j i k)
    (hforce : ∀ T : Finset ι, (T.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
      ∀ w ∈ (C : Set (ι → A)), ∀ w' ∈ (C : Set (ι → A)),
      (∀ i ∈ T ∩ Sstar, w i = w' i) → w = w')
    (hcard : l * Fintype.card ι + 1 ≤ Fintype.card F) :
    ObstructionBound C δ G U := by
  set Img := (Finset.univ : Finset (Fin l × ι)).image
    (fun p => devKernel (F := F) (deviation U c p.1 p.2)) with hImg
  refine ⟨insert ⊥ (Img.filter (fun K => K ≠ ⊤)), ?_, ?_, ?_⟩
  · calc (insert ⊥ (Img.filter (fun K => K ≠ ⊤))).card
        ≤ (Img.filter (fun K => K ≠ ⊤)).card + 1 := Finset.card_insert_le _ _
      _ ≤ Img.card + 1 := by
          have := Finset.card_filter_le Img (fun K => K ≠ ⊤)
          omega
      _ ≤ (Finset.univ : Finset (Fin l × ι)).card + 1 := by
          have := Finset.card_image_le (s := (Finset.univ : Finset (Fin l × ι)))
            (f := fun p => devKernel (F := F) (deviation U c p.1 p.2))
          rw [hImg]
          omega
      _ = l * Fintype.card ι + 1 := by
          rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      _ ≤ Fintype.card F := hcard
  · intro K hK
    rcases Finset.mem_insert.mp hK with h | h
    · subst h
      intro htop
      have h1 : (fun k : Fin 2 => if k = 0 then (1 : F) else 0)
          ∈ (⊥ : Submodule F (Fin 2 → F)) := by rw [htop]; trivial
      have h0 := congrFun ((Submodule.mem_bot F).mp h1) 0
      simp at h0
    · exact (Finset.mem_filter.mp h).2
  · intro ω hω
    obtain ⟨T, hW⟩ := hω
    refine ⟨T, hW, ?_⟩
    have hproper : jointStackSubmodule C T U ≠ ⊤ :=
      jointStackSubmodule_ne_top C U hW.2.2
    rcases proper_eq_bot_or_span _ hproper with hbot | ⟨lam, hlam0, hlamK, hspan⟩
    · rw [hbot]
      exact Finset.mem_insert_self _ _
    · rcases obstruction_line_pinned_by_deviation C hcw hexp
        (hforce T hW.1) hproper with hbot | ⟨j, i, _, hdev, hkillall⟩
      · exact absurd (hbot ▸ hlamK) (by simpa using hlam0)
      · -- K_T = span lam = devKernel(deviation): membership in the image
        have hker : lam ∈ devKernel (F := F) (deviation U c j i) :=
          (mem_devKernel_iff).mpr (hkillall lam hlamK)
        have hkprop : devKernel (F := F) (deviation U c j i) ≠ ⊤ :=
          devKernel_ne_top_of_ne_zero hdev
        have hkeq : devKernel (F := F) (deviation U c j i)
            = Submodule.span F {lam} := proper_eq_span_of_mem hkprop hker hlam0
        have hKT : jointStackSubmodule C T U
            = devKernel (F := F) (deviation U c j i) := by
          rw [hspan, hkeq]
        rw [hKT]
        refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨?_, hkprop⟩)
        rw [hImg]
        exact Finset.mem_image.mpr ⟨(j, i), Finset.mem_univ _, rfl⟩

end ProximityGap.Jo26Obstruction

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Jo26Obstruction.devKernel_ne_top_of_ne_zero
#print axioms ProximityGap.Jo26Obstruction.proper_eq_span_of_mem
#print axioms ProximityGap.Jo26Obstruction.obstructionBound_of_fullyClose
