/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Jo26InterleavingBound

/-!
# The generator dichotomy: when the `A(q,s)` factor is removable (issue #334, A3)

[Jo26] Theorem 4.2 charges the field-size factor `A(q,s) = (q^s−1)/(q^{s−1}(q−1))` for
arbitrary coefficient generators, and Remark 4.3 notes the factor is sharp at a single
codimension-1 obstruction (`SubspaceAvoidance.card_linearForm_kernel_eq`). The in-tree
affine-line/small-seed results (`epsMCA_interleaved_eq` and the exactness fences) show the
factor *vanishes* for special generators. This file formalizes the boundary:

* `UniformObstruction` — the per-stack predicate: the bad-seed subspaces `K_ω` of [Jo26]
  Lemma 4.1 (`jointStackSubmodule` at per-seed witness sets) admit a **common proper
  cover indexed by the field** — the exact hypothesis shape of the covering lemma
  ([Jo26] Lemma 3.2, `exists_nonzero_notMem_of_proper_family`).
* `epsMCAG_interleaved_le_of_uniformObstruction` — **the factor-removal theorem**: under
  uniform obstruction at every stack, the interleaving bound is *exact* on the upper side —
  `ε_G(C^{≡s}, δ) ≤ ε_G(C, δ)`, no `A(q,s)` loss (one nonzero `λ` preserves **all** bad seeds
  simultaneously, so the seed-set inclusion replaces the averaging argument).
* `uniformObstruction_of_seedIndexed` — the sufficient criterion instantiating the in-tree
  small-seed situation: if the seed space embeds into `F` and each seed's obstruction is
  proper, the family `K : F → _` (junk-completed off the embedding's range by `⊥`) is a
  uniform obstruction. The affine line (`Ω = F`) is the canonical instance.

**Quantifier honesty.** `UniformObstruction` quantifies per stack `U`, choosing one witness
set per bad seed (as Lemma 4.1 does); the factor-removal theorem needs it for every stack.
The sharpness side — generators where uniform obstruction *fails* and `A(q,s)` is attained —
is the codimension-1 content of `SubspaceAvoidance.card_linearForm_kernel_eq`: a single
proper subspace can absorb at most `q^{s−1}` combiners, so `q` genuinely-distinct
codimension-1 obstructions can exhaust the nonzero combiners; the formal matching *generator*
construction is left open (recorded in the docstring, not fabricated).
-/

open Finset NNReal Code
open scoped ProbabilityTheory BigOperators NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Uniform obstruction** (issue #334, A3): for the stack `U` over the interleaved code, an
`F`-indexed family of proper subspaces covers every bad seed's Lemma-4.1 obstruction: for each
`G`-MCA-bad seed `ω` there is a witness set whose joint-stack submodule lies inside some member
of the family. This is exactly the hypothesis shape consumed by the covering lemma
([Jo26] Lemma 3.2). -/
def UniformObstruction {l s : ℕ} {Ω : Type} [Fintype Ω]
    (G : Ω → Fin l → F) (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (U : Fin l → ι → Fin s → A) : Prop :=
  ∃ K : F → Submodule F (Fin s → F), (∀ γ, K γ ≠ ⊤) ∧
    ∀ ω : Ω, mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω) →
      ∃ T : Finset ι, mcaWitnessG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω) T ∧
        ∃ γ : F, jointStackSubmodule C T U ≤ K γ

/-- **The factor-removal theorem** (issue #334, A3): under uniform obstruction at every stack,
the generator-MCA interleaving bound is exact on the upper side — `ε_G(C^{≡s}, δ) ≤ ε_G(C, δ)`,
with **no** `A(q,s)` factor. The covering lemma produces one nonzero `λ` avoiding every member
of the common cover, hence every bad seed's obstruction: the bad-seed set of the interleaved
stack *embeds* into the bad-seed set of the single `λ`-combined base stack, and the
probability inequality is monotonicity, not averaging. -/
theorem epsMCAG_interleaved_le_of_uniformObstruction
    {l s : ℕ} (hs : 1 ≤ s) {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (G : Ω → Fin l → F) (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (hU : ∀ U : Fin l → ι → Fin s → A, UniformObstruction G C δ U) :
    epsMCAG (A := Fin s → A) ((C : Set (ι → A))^⋈ (Fin s)) δ G
      ≤ epsMCAG (A := A) (C : Set (ι → A)) δ G := by
  classical
  unfold epsMCAG
  apply iSup_le
  intro U
  obtain ⟨K, hKproper, hKcover⟩ := hU U
  -- One nonzero λ avoiding every member of the cover.
  obtain ⟨lam, _hlam0, hlamK⟩ := exists_nonzero_notMem_of_proper_family hs K hKproper
  -- Every interleaved-bad seed is base-bad for the λ-combined stack.
  have h_imp : ∀ ω : Ω, mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω) →
      mcaEventG (C : Set (ι → A)) δ (fun j i => ∑ k, lam k • U j i k) (G ω) := by
    intro ω hbad
    obtain ⟨T, hW, γ, hle⟩ := hKcover ω hbad
    have hnotin : lam ∉ jointStackSubmodule C T U :=
      fun hmem => hlamK γ (hle hmem)
    exact ⟨T, jo26_mcaWitnessG_combine C δ hW hnotin⟩
  refine le_trans (Pr_le_Pr_of_implies _ _ _ h_imp) ?_
  exact le_iSup
    (fun v : Code.WordStack A (Fin l) ι =>
      Pr_{let ω ← $ᵖ Ω}[mcaEventG (C : Set (ι → A)) δ v (G ω)])
    (fun j i => ∑ k, lam k • U j i k)

/-- **The exact two-sided invariance under uniform obstruction**: combining the factor-removal
upper side with the zero-padding lower side of [Jo26] Theorem 4.2 — for uniformly-obstructed
generators, interleaving leaves the generator-MCA error *exactly* invariant, the generalization
of the in-tree affine-line exactness (`epsMCA_interleaved_eq`). -/
theorem epsMCAG_interleaved_eq_of_uniformObstruction
    {l s : ℕ} (hs : 1 ≤ s) [NeZero s] {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (G : Ω → Fin l → F) (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (hU : ∀ U : Fin l → ι → Fin s → A, UniformObstruction G C δ U) :
    epsMCAG (A := Fin s → A) ((C : Set (ι → A))^⋈ (Fin s)) δ G
      = epsMCAG (A := A) (C : Set (ι → A)) δ G :=
  le_antisymm
    (epsMCAG_interleaved_le_of_uniformObstruction hs G C δ hU)
    (jo26_epsMCAG_le_interleaved C s δ G)

/-- **The seed-indexed sufficient criterion** (the small-seed/affine-line situation): if the
seed space embeds into the field and each bad seed's Lemma-4.1 obstruction is chosen
per-seed, the `F`-indexed family obtained by transporting along the embedding (and junking to
`⊥ ≠ ⊤` off its range) is a uniform obstruction. In particular every generator with `Ω ↪ F`
(e.g. the affine line `Ω = F`, `G γ = (1, γ)`) has the factor-free interleaving bound. -/
theorem uniformObstruction_of_seedIndexed
    {l s : ℕ} (hs : 1 ≤ s) {Ω : Type} [Fintype Ω]
    (e : Ω ↪ F) (G : Ω → Fin l → F) (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (U : Fin l → ι → Fin s → A)
    (hwitness : ∀ ω : Ω, mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω) →
      ∃ T : Finset ι, mcaWitnessG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω) T ∧
        jointStackSubmodule C T U ≠ ⊤) :
    UniformObstruction G C δ U := by
  classical
  -- Choose one witness per bad seed; transport along the embedding; junk to ⊥ off-range.
  choose T hT hTne using hwitness
  have hbot : (⊥ : Submodule F (Fin s → F)) ≠ ⊤ := by
    haveI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
    exact bot_ne_top
  refine ⟨fun γ =>
    if h : ∃ ω, e ω = γ ∧ mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω)
    then jointStackSubmodule C (T h.choose h.choose_spec.2) U
    else ⊥, ?_, ?_⟩
  · intro γ
    beta_reduce
    by_cases h : ∃ ω, e ω = γ ∧ mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω)
    · rw [dif_pos h]
      exact hTne _ _
    · rw [dif_neg h]
      exact hbot
  · intro ω hbad
    refine ⟨T ω hbad, hT ω hbad, e ω, ?_⟩
    have hex : ∃ ω', e ω' = e ω ∧ mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω') :=
      ⟨ω, rfl, hbad⟩
    beta_reduce
    rw [dif_pos hex]
    -- The chosen ω' has e ω' = e ω, so ω' = ω by injectivity; the submodules coincide
    -- (the witness-set choices agree by proof irrelevance).
    have hTeq : T hex.choose hex.choose_spec.2 = T ω hbad := by
      have hω' : hex.choose = ω := e.injective hex.choose_spec.1
      congr 1
    exact le_of_eq (congrArg (fun t => jointStackSubmodule C t U) hTeq).symm

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.epsMCAG_interleaved_le_of_uniformObstruction
#print axioms ProximityGap.epsMCAG_interleaved_eq_of_uniformObstruction
#print axioms ProximityGap.uniformObstruction_of_seedIndexed
