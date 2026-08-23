/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Jo26InterleavingBound
import ArkLib.Data.CodingTheory.ProximityGap.Jo26GeneratorMCA

/-!
# Obstruction-count exactness for generator MCA (issue #357, hypothesis S2(a))

[Jo26] Theorem 4.2 pays the factor `A(q,s) = (q^s−1)/(q^{s−1}(q−1))` for arbitrary
coefficient generators, and Theorem 4.4 removes it only for small seed sets
(`|Ω| ≤ q`).  The factor enters through the *averaging* step: each bad seed `ω` of an
interleaved stack `U` is preserved by every combiner outside a proper subspace
`K_ω = jointStackSubmodule C T_ω U` ([Jo26] Lemma 4.1, in-tree as
`jo26_bad_seed_preservation`), and with no further information one can only average
over combiners.

This file isolates the structural reason the factor can disappear: **`K_ω` depends on
the seed only through its witness set `T_ω`** — the stack `U` is fixed throughout.  So
what matters is not `|Ω|` but the number of *distinct obstruction subspaces* the stack
can realize.  If a dominating family of at most `q = |F|` proper subspaces captures
every bad seed's obstruction, the covering lemma (`[Jo26] Lemma 3.2`, in-tree as
`exists_nonzero_notMem_of_proper_family_of_card_le`) produces a **single** nonzero
combiner preserving *all* bad seeds simultaneously — no averaging, no factor:

  `epsMCAG (C^⋈s) δ G = epsMCAG C δ G`  for **every** generator `G`, any seed set.

The hypothesis is stated as `ObstructionBound`: every stack admits a `≤ q`-element
family of proper subspaces such that every bad seed has *some* witness whose
obstruction subspace lies in the family.  Note the order of quantifiers: the family may
depend on the stack (and on `δ`, `G`), but not on the seed.

At `s = 2` the proper subspaces of `F²` are `⊥` and the `q+1` lines, so the hypothesis
follows from a *missing-line* statement — no single stack realizes all `q+1` lines as
bad-seed obstructions (hypothesis S2(b), open; the in-tree proportionality trap
`A3ProportionalityTrap.lean` proves it for the affine design class, and the
adversarial-generator probes observe exact equality on every instance).  The corollary
`epsMCAG_interleaved_eq_of_missing_line` packages this reduction.

Everything here is unconditional except the named `ObstructionBound` input; the
theorems convert the open combinatorial question S2(b) into exactly that input.

## References

- [Jo26] ePrint 2026/891, §3–4.
- Issue #357 (campaign slate, hypothesis S2).
-/

open Finset NNReal Code
open scoped ProbabilityTheory BigOperators

namespace ProximityGap.Jo26Obstruction

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The obstruction-count hypothesis.**  For the stack `U` (over the `s`-fold
interleaving of `C`), radius `δ`, and generator `G`: there is a family `Ks` of at most
`q = |F|` proper subspaces of `F^s` such that every `G`-MCA-bad seed has some witness
`T` whose obstruction subspace `jointStackSubmodule C T U` belongs to `Ks`.

This is the precise residue of [Jo26] Theorem 4.4's `|Ω| ≤ q` hypothesis once the
seed-blindness of `jointStackSubmodule` is taken into account: the bound is on
*distinct realizable obstructions*, not on the seed set. -/
def ObstructionBound (C : Submodule F (ι → A)) (δ : ℝ≥0) {l s : ℕ}
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F)
    (U : Fin l → ι → Fin s → A) : Prop :=
  ∃ Ks : Finset (Submodule F (Fin s → F)),
    Ks.card ≤ Fintype.card F ∧
    (∀ K ∈ Ks, K ≠ ⊤) ∧
    ∀ ω : Ω, mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω) →
      ∃ T : Finset ι,
        mcaWitnessG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω) T ∧
        jointStackSubmodule C T U ∈ Ks

open Classical in
/-- **One combiner preserves every bad seed.**  Under `ObstructionBound`, there is a
single nonzero `λ ∈ F^s` such that every `G`-MCA-bad seed of the interleaved stack `U`
stays bad for the `λ`-row-combined base stack.  This is the covering lemma applied to
the dominating obstruction family, composed with the witness-level combination step
`jo26_mcaWitnessG_combine`. -/
theorem exists_combiner_preserving_all_bad_seeds
    (C : Submodule F (ι → A)) (δ : ℝ≥0) {l s : ℕ} [NeZero s]
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F)
    (U : Fin l → ι → Fin s → A)
    (hOB : ObstructionBound C δ G U)
    (hbad : ∃ ω : Ω, mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω)) :
    ∃ lam : Fin s → F, lam ≠ 0 ∧
      ∀ ω : Ω, mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω) →
        mcaEventG (C : Set (ι → A)) δ (fun j i => ∑ k, lam k • U j i k) (G ω) := by
  obtain ⟨Ks, hcard, hproper, hcapture⟩ := hOB
  -- the family is nonempty: a bad seed's obstruction lies in it
  obtain ⟨ω₀, hω₀⟩ := hbad
  obtain ⟨T₀, _, hT₀⟩ := hcapture ω₀ hω₀
  haveI : Nonempty ↥(Ks : Finset (Submodule F (Fin s → F))) :=
    ⟨⟨jointStackSubmodule C T₀ U, hT₀⟩⟩
  -- covering: one nonzero combiner avoids every member of the family
  obtain ⟨lam, hlam0, hlam⟩ :=
    ProximityGap.Jo26Gen.exists_nonzero_notMem_of_proper_family_of_card_le
      (Ω := ↥(Ks : Finset (Submodule F (Fin s → F))))
      (t := s) (NeZero.pos s)
      (by simpa [Fintype.card_coe] using hcard)
      (fun K => (K : Submodule F (Fin s → F)))
      (fun K => hproper K.1 K.2)
  refine ⟨lam, hlam0, fun ω hω => ?_⟩
  obtain ⟨T, hW, hKmem⟩ := hcapture ω hω
  exact ⟨T, jo26_mcaWitnessG_combine C δ hW (hlam ⟨jointStackSubmodule C T U, hKmem⟩)⟩

open Classical in
/-- **Obstruction-count exactness ([Jo26] Theorem 4.2 with the factor removed).**
If every stack satisfies `ObstructionBound`, the generator-MCA error of the `s`-fold
interleaving equals that of the base code — for **every** coefficient generator, with
no constraint on the seed set.  This strictly subsumes the `|Ω| ≤ q` exactness of
[Jo26] Theorem 4.4 (whose proof in effect dominates the obstructions by the `≤ |Ω|`
witness-wise subspaces) and removes the `A(q,s)` factor of Theorem 4.2 whenever the
obstruction geometry, rather than the seed count, is the binding constraint. -/
theorem epsMCAG_interleaved_eq_of_obstructionBound
    (C : Submodule F (ι → A)) (s : ℕ) [NeZero s] (δ : ℝ≥0) {l : ℕ}
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F)
    (hOB : ∀ U : Fin l → ι → Fin s → A, ObstructionBound C δ G U) :
    epsMCAG (A := Fin s → A) ((C : Set (ι → A))^⋈ (Fin s)) δ G
      = epsMCAG (A := A) (C : Set (ι → A)) δ G := by
  refine le_antisymm ?_ (jo26_epsMCAG_le_interleaved C s δ G)
  unfold epsMCAG
  refine iSup_le fun U => ?_
  by_cases hbad : ∃ ω : Ω, mcaEventG ((C : Set (ι → A))^⋈ (Fin s)) δ U (G ω)
  · obtain ⟨lam, _, hpres⟩ :=
      exists_combiner_preserving_all_bad_seeds C δ G U (hOB U) hbad
    refine le_trans (Pr_le_Pr_of_implies _ _ _ hpres) ?_
    exact le_iSup
      (fun f : Fin l → ι → A =>
        Pr_{let ω ← $ᵖ Ω}[mcaEventG (C : Set (ι → A)) δ f (G ω)])
      (fun j i => ∑ k, lam k • U j i k)
  · -- no bad seed: the interleaved term is dominated by any base term
    refine le_trans
      (Pr_le_Pr_of_implies _ _
        (fun ω => mcaEventG (C : Set (ι → A)) δ (fun _ _ => (0 : A)) (G ω))
        (fun ω h => absurd ⟨ω, h⟩ hbad))
      ?_
    exact le_iSup
      (fun f : Fin l → ι → A =>
        Pr_{let ω ← $ᵖ Ω}[mcaEventG (C : Set (ι → A)) δ f (G ω)])
      (fun _ _ => (0 : A))

/-! ### The `s = 2` reduction: missing lines

At `s = 2` every proper subspace of `F²` is contained in a line (`⊥ ≤` anything), and
there are exactly `q+1` lines.  So `ObstructionBound` follows from: *the obstruction
subspaces of one stack miss at least one line*.  This converts hypothesis S2(b) — a
purely combinatorial statement about joint-agreement geometry — into the exactness
input. -/

/-- **The missing-line hypothesis (S2(b)) for a stack.**  Some line of `F²` (recorded
by a subspace `K₀` that is proper and not below any realized obstruction) bounds no
bad-seed obstruction of `U`: there is a proper subspace `K₀ ⊊ F²` such that every
bad seed has a witness whose obstruction is contained in one of at most `q` proper
subspaces.  We state it directly as the existence of a `≤ q` dominating family, since
"all obstructions avoid one line" pins the family to the remaining `q` lines. -/
def MissingLine (C : Submodule F (ι → A)) (δ : ℝ≥0) {l : ℕ}
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F)
    (U : Fin l → ι → Fin 2 → A) : Prop :=
  ∃ Ls : Finset (Submodule F (Fin 2 → F)),
    Ls.card ≤ Fintype.card F ∧
    (∀ K ∈ Ls, K ≠ ⊤) ∧
    ∀ ω : Ω, mcaEventG ((C : Set (ι → A))^⋈ (Fin 2)) δ U (G ω) →
      ∃ T : Finset ι,
        mcaWitnessG ((C : Set (ι → A))^⋈ (Fin 2)) δ U (G ω) T ∧
        jointStackSubmodule C T U ∈ Ls

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] [DecidableEq A] in
/-- At `s = 2`, the missing-line hypothesis **is** the obstruction bound (definitional
repackaging; kept as a named bridge so S2(b) work targets `MissingLine` directly). -/
theorem obstructionBound_of_missingLine
    (C : Submodule F (ι → A)) (δ : ℝ≥0) {l : ℕ}
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F)
    (U : Fin l → ι → Fin 2 → A) (h : MissingLine C δ G U) :
    ObstructionBound C δ G U := h

open Classical in
/-- **Exactness from missing lines (the S2 reduction, `s = 2`).**  If every 2-column
stack misses a line, generator-MCA interleaving is exact for every generator. -/
theorem epsMCAG_interleaved_eq_of_missingLine
    (C : Submodule F (ι → A)) (δ : ℝ≥0) {l : ℕ}
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F)
    (hML : ∀ U : Fin l → ι → Fin 2 → A, MissingLine C δ G U) :
    epsMCAG (A := Fin 2 → A) ((C : Set (ι → A))^⋈ (Fin 2)) δ G
      = epsMCAG (A := A) (C : Set (ι → A)) δ G :=
  epsMCAG_interleaved_eq_of_obstructionBound C 2 δ G
    (fun U => obstructionBound_of_missingLine C δ G U (hML U))

end ProximityGap.Jo26Obstruction

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Jo26Obstruction.exists_combiner_preserving_all_bad_seeds
#print axioms ProximityGap.Jo26Obstruction.epsMCAG_interleaved_eq_of_obstructionBound
#print axioms ProximityGap.Jo26Obstruction.epsMCAG_interleaved_eq_of_missingLine
