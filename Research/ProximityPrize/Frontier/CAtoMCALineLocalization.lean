/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# B4 at lines: the CA ⇒ MCA collapse, localized and floored (#466 Lane W3)

**The open problem** (ABF26 §5 / Crites–Stewart flag, dossier v3 §6): does a good
correlated-agreement (CA) bound imply a good mutual-correlated-agreement (MCA) bound —
"unknown even for lines"?  This file makes the first movement on the line case (`m = 2`
stacks), in three steps, all axiom-clean:

1. **Per-scalar trichotomy** (`mcaEvent_of_line_close_of_not_jointProximity`,
   `mcaEvent_iff_line_close_of_not_jointProximity`,
   `line_close_imp_mcaEvent_or_jointProximity`): for a stack that is *not* jointly
   `δ`-close, a scalar `γ` fires `mcaEvent` **iff** its line point `u₀ + γ•u₁` is
   `δ`-close to `C`.  So per-scalar, CA-bad = MCA-bad *exactly* on every
   non-jointly-close stack: every close witness set `S` (size `≥ (1−δ)n`) with a joint
   pair on it would certify `jointProximity`.  The requested shape
   "CA-bad ⟹ MCA-bad ∨ joint-agreement-everywhere" is the trichotomy corollary, and the
   third case is *classified*: it is precisely `jointProximity` of the stack (the
   in-tree probability forms `mcaEvent_probability_le_epsCA_of_not_jointProximity` /
   `epsMCA_restricted_le_epsCA` are the `≤` shadows of this per-scalar identity).

2. **Exact localization identity** (`epsMCA_eq_max_epsCA_jointlyProximateContribution`):
   `ε_mca(C, δ) = max (ε_ca(C, δ, δ)) (jointlyProximateContribution C δ)` for any
   linear code.  The `≤` half is in-tree (`Errors.lean`); this file adds the matching
   `≥` (`jointlyProximateContribution_le_epsMCA` + `epsCA_le_epsMCA`), upgrading the
   bracket to an identity.  **Consequence: B4 at lines is *equivalent* to bounding the
   jointly-proximate contribution** — the collapse holds with constant `κ` iff
   `jointlyProximateContribution C δ ≤ κ · ε_ca` (below UDR the in-tree
   `jointlyProximateContribution_le_card_div_udr` pins it at `⌊δn⌋/|F|`; the window is
   the open part).

3. **The window floor — B4's obstruction, exhibited**
   (`mcaEvent_of_vanishing_outside_support`, `jointProximity_of_vanishing_outside_support`,
   `jointlyProximateContribution_ge_of_supported_stack`, `epsMCA_ge_of_supported_stack`):
   a jointly-close stack in *shifted normal form* — both rows supported on a set `E`
   with `|Eᶜ| ≥ (1−δ)n` — fires `mcaEvent` at every **ratio scalar** `γ` with
   `u₀ i₀ + γ • u₁ i₀ = 0`, `u₁ i₀ ≠ 0`, `i₀ ∈ E`, *provided no nonzero codeword
   vanishes off `E`* (for RS of dimension `k`, automatic whenever `|Eᶜ| ≥ k`, i.e. in
   the **entire window** `δ < 1 − ρ`, far beyond UDR).  Witness: `S = insert i₀ Eᶜ`
   with the zero codeword; any joint pair on `S` forces the direction row's explainer
   to vanish off `E`, hence to be `0`, contradicting `u₁ i₀ ≠ 0`.  Generic values give
   `⌊δn⌋` distinct ratio scalars, so `jointlyProximateContribution ≥ ⌊δn⌋/|F|`
   throughout the window — the in-tree UDR ceiling `⌊δn⌋/|F|` is **tight**, and any
   CA ⇒ MCA transfer at lines must carry at least this additive `~δn/q` term.

4. **The below-gate ratio-scalar law** (`badScalar_is_ratio_of_supported_below_gate`,
   `badScalar_card_le_support_of_below_gate`): on an `E`-supported stack over a code whose
   nonzero codewords have at most `z` zeros (RS of dimension `k`: `z = k−1`), below the
   **excess gate** `z + |E| < (1−δ)n` every MCA-bad scalar is a *ratio scalar* and the bad
   set injects into `E`.  With §3 this pins the per-stack bad set *exactly* below the gate.

**Probe** (`scripts/probes/probe_466_ca_vs_mca.py` →
`scripts/probes/_out_466_ca_vs_mca.txt`, exact per-scalar enumeration at `n = 8, 16`,
two primes each, window-interior agreement `a`, brute-force cross-validated at `n = 8`):
the per-scalar identity holds exactly (CA-minus-MCA gap `≡ 0` on every non-jointly-close
stack tested), designed sparse stacks fire exactly their `⌊δn⌋` ratio scalars, the gate
of §4 is empirically **sharp** (zero excess fires at `k=2, a=5` where the gate holds; one
excess fire found exactly at the boundary `a − |E| = k − 1`), and past the gate the
**excess channel opens wide**: jointly-close stacks fire far beyond `⌊δn⌋` via nonzero
witnesses (`J = 57` vs `e = 4` at `n=8,k=3,a=4`; `J ≈ 4200` vs `e = 11` at `n=16,k=4,a=5`;
antipodal monomial stacks fire exactly `n = 16` all-excess scalars at `n=16, a ∈ {6,7}`).
See `docs/kb/deltastar-466-w3-b4-ca-vs-mca-lines-2026-07-02.md` for the full table.

What stays open (honest scope): the *upper* bound on `jointlyProximateContribution` in
the window (beyond the gate).  Nothing here claims the collapse; the identity reduces B4
at lines to that single named quantity, the floor shows it cannot be beaten below
`⌊δn⌋/|F|`, and the probe data keep `κ = 1` (`ε_mca = ε_ca` at lines) consistent — a
conjecture, not a theorem.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated
  Agreement*. 2026. §4–5.  Issue #466 lane W3 (B4).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ProximityGap.B4Lines

open NNReal Code ProximityGap
open scoped ProbabilityTheory BigOperators ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## 1. The per-scalar trichotomy -/

/-- **Per-scalar CA-bad ⟹ MCA-bad on non-jointly-close stacks.** If the stack `u` is not
jointly `δ`-close to `C` and the line point at `γ` is `δ`-close, then `mcaEvent` fires at
`γ`: the close witness set `S` has size `≥ (1−δ)n`, and a joint codeword pair agreeing on
`S` would certify `jointAgreement` hence `jointProximity` — contradiction.  (This is the
per-scalar core of the in-tree `epsCA_le_epsMCA`, extracted as a named statement; it needs
no linearity of `C`.) -/
theorem mcaEvent_of_line_close_of_not_jointProximity
    (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) (γ : F)
    (hjp : ¬ jointProximity (C := C) (u := u) δ)
    (h_line : δᵣ(u 0 + γ • u 1, C) ≤ δ) :
    mcaEvent C δ (u 0) (u 1) γ := by
  classical
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist] at h_line
  obtain ⟨w, hw_mem, hw_close⟩ := h_line
  rw [relCloseToWord_iff_exists_agreementCols] at hw_close
  obtain ⟨S, hS_card_nat, h_word_agree⟩ := hw_close
  have hS_card_real : (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι :=
    (relDist_floor_bound_iff_complement_bound _ _ _).mp hS_card_nat
  refine ⟨S, hS_card_real, ⟨w, hw_mem, fun i hi ↦ ((h_word_agree i).1 hi).symm⟩, ?_⟩
  intro h_pair
  apply hjp
  rw [← jointAgreement_iff_jointProximity]
  obtain ⟨v₀, hv₀_mem, v₁, hv₁_mem, h_pair_agree⟩ := h_pair
  refine ⟨S, hS_card_real, finMapTwoWords v₀ v₁, ?_⟩
  intro i
  refine ⟨?_, ?_⟩
  · fin_cases i
    · exact hv₀_mem
    · exact hv₁_mem
  · intro j hj
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    fin_cases i
    · exact (h_pair_agree j hj).1
    · exact (h_pair_agree j hj).2

/-- **Per-scalar identity on non-jointly-close stacks: MCA-bad ⟺ line-close.** Combined
with `mcaEvent_imp_relCloseToCode`, the bad-scalar sets of CA and MCA coincide *scalar by
scalar* on every stack that is not jointly `δ`-close.  The entire CA-vs-MCA gap at lines
therefore lives on the jointly-close stacks (where the `ε_ca` body is `0`). -/
theorem mcaEvent_iff_line_close_of_not_jointProximity
    (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) (γ : F)
    (hjp : ¬ jointProximity (C := C) (u := u) δ) :
    mcaEvent C δ (u 0) (u 1) γ ↔ δᵣ(u 0 + γ • u 1, C) ≤ δ :=
  ⟨mcaEvent_imp_relCloseToCode C δ (u 0) (u 1) γ,
    mcaEvent_of_line_close_of_not_jointProximity C δ u γ hjp⟩

/-- **The trichotomy, in the shape B4 asks for.** Every CA-bad scalar (line `δ`-close) is
MCA-bad **or** the stack itself is jointly `δ`-close ("joint agreement everywhere") — and
the third case is classified: it is exactly `jointProximity`, the `γ`-independent stack
condition under which `ε_ca` assigns the stack probability `0`. -/
theorem line_close_imp_mcaEvent_or_jointProximity
    (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) (γ : F)
    (h_line : δᵣ(u 0 + γ • u 1, C) ≤ δ) :
    mcaEvent C δ (u 0) (u 1) γ ∨ jointProximity (C := C) (u := u) δ := by
  classical
  by_cases hjp : jointProximity (C := C) (u := u) δ
  · exact Or.inr hjp
  · exact Or.inl (mcaEvent_of_line_close_of_not_jointProximity C δ u γ hjp h_line)

/-! ## 2. The exact localization identity -/

open Classical in
/-- The jointly-proximate contribution is itself part of the `ε_mca` supremum. -/
theorem jointlyProximateContribution_le_epsMCA (C : Set (ι → A)) (δ : ℝ≥0) :
    jointlyProximateContribution (F := F) C δ ≤ epsMCA (F := F) C δ := by
  unfold jointlyProximateContribution epsMCA
  apply iSup_mono
  intro u
  by_cases hjp : jointProximity (C := C) (u := u) δ
  · rw [if_pos hjp]
  · rw [if_neg hjp]
    exact zero_le _

open Classical in
/-- **The B4 localization identity at lines.** For any linear code,

`ε_mca(C, δ) = max (ε_ca(C, δ, δ)) (jointlyProximateContribution C δ)`.

The `≤` half is the in-tree `epsMCA_le_max_epsCA_jointlyProximateContribution`; the `≥`
half is `epsCA_le_epsMCA` together with `jointlyProximateContribution_le_epsMCA`.  This
upgrades the in-tree bracket to an identity: **the CA ⇒ MCA collapse at lines holds iff
the jointly-proximate contribution is bounded** (below UDR it is `≤ ⌊δn⌋/|F|` in-tree;
the window-regime bound is the open content of B4, and by the floor below it cannot go
under `⌊δn⌋/|F|` there either). -/
theorem epsMCA_eq_max_epsCA_jointlyProximateContribution
    (C : Submodule F (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := A) ((C : Set (ι → A))) δ =
      max (epsCA (F := F) (A := A) ((C : Set (ι → A))) δ δ)
        (jointlyProximateContribution (F := F) ((C : Set (ι → A))) δ) :=
  le_antisymm
    (epsMCA_le_max_epsCA_jointlyProximateContribution (F := F) ((C : Set (ι → A))) δ)
    (max_le (epsCA_le_epsMCA C δ)
      (jointlyProximateContribution_le_epsMCA ((C : Set (ι → A))) δ))

/-! ## 3. The window floor: ratio scalars fire on jointly-close stacks -/

/-- **Ratio-scalar firing lemma (window-valid).** Let `(u₀, u₁)` vanish outside `E` with
`|Eᶜ| ≥ (1−δ)n` (shifted normal form of a jointly-close stack), and suppose no nonzero
codeword of `C` vanishes outside `E` (for RS of dimension `k` this holds whenever
`|Eᶜ| ≥ k` — the whole window `δ < 1 − ρ`, far beyond UDR).  Then any scalar `γ` killing
some coordinate `i₀ ∈ E` of the line (`u₀ i₀ + γ • u₁ i₀ = 0`) with `u₁ i₀ ≠ 0` fires
`mcaEvent`: the witness is `S = insert i₀ Eᶜ` with the zero codeword, and a joint pair on
`S` would force the direction-row explainer to vanish off `E`, hence vanish identically,
contradicting `u₁ i₀ ≠ 0`. -/
theorem mcaEvent_of_vanishing_outside_support
    (C : Set (ι → A)) (h0 : (0 : ι → A) ∈ C) (δ : ℝ≥0) {E : Finset ι} {u₀ u₁ : ι → A}
    (hu₀ : ∀ i ∉ E, u₀ i = 0) (hu₁ : ∀ i ∉ E, u₁ i = 0)
    (hEc : ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (Eᶜ.card : ℝ≥0))
    (hvan : ∀ c ∈ C, (∀ i ∉ E, c i = 0) → c = 0)
    {i₀ : ι} (hi₀ : i₀ ∈ E) {γ : F}
    (hker : u₀ i₀ + γ • u₁ i₀ = 0) (hne : u₁ i₀ ≠ 0) :
    mcaEvent C δ u₀ u₁ γ := by
  classical
  refine ⟨insert i₀ Eᶜ, ?_, ⟨0, h0, ?_⟩, ?_⟩
  · -- size: `|insert i₀ Eᶜ| ≥ |Eᶜ| ≥ (1−δ)n`.
    refine le_trans hEc ?_
    exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card (Finset.subset_insert _ _))
  · -- the zero codeword agrees with the line on `insert i₀ Eᶜ`.
    intro i hi
    rcases Finset.mem_insert.mp hi with h | h
    · subst h
      simpa using hker.symm
    · have hiE : i ∉ E := Finset.mem_compl.mp h
      simp [hu₀ i hiE, hu₁ i hiE]
  · -- no joint pair on the witness set.
    rintro ⟨v₀, hv₀, v₁, hv₁, hagree⟩
    have hv₁E : ∀ i ∉ E, v₁ i = 0 := by
      intro i hiE
      have hiS : i ∈ insert i₀ Eᶜ := Finset.mem_insert_of_mem (Finset.mem_compl.mpr hiE)
      rw [(hagree i hiS).2, hu₁ i hiE]
    have hv₁0 : v₁ = 0 := hvan v₁ hv₁ hv₁E
    apply hne
    have h0i : v₁ i₀ = u₁ i₀ := (hagree i₀ (Finset.mem_insert_self _ _)).2
    rw [hv₁0] at h0i
    simpa using h0i.symm

/-- A stack in shifted normal form (both rows vanish outside `E`, `|Eᶜ| ≥ (1−δ)n`) is
jointly `δ`-close: the zero pair agrees with it on all of `Eᶜ`. -/
theorem jointProximity_of_vanishing_outside_support
    (C : Set (ι → A)) (h0 : (0 : ι → A) ∈ C) (δ : ℝ≥0) {E : Finset ι}
    (u : WordStack A (Fin 2) ι)
    (hu : ∀ r : Fin 2, ∀ i ∉ E, u r i = 0)
    (hEc : ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (Eᶜ.card : ℝ≥0)) :
    jointProximity (C := C) (u := u) δ := by
  classical
  rw [← jointAgreement_iff_jointProximity]
  refine ⟨Eᶜ, hEc, fun _ => 0, ?_⟩
  intro r
  refine ⟨h0, ?_⟩
  intro j hj
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, (hu r j (Finset.mem_compl.mp hj)).symm⟩

open Classical in
/-- The `mcaEvent` mass of any jointly-close stack lower-bounds the jointly-proximate
contribution (its `iSup` body at that stack is the un-gated probability). -/
theorem le_jointlyProximateContribution_of_jointProximity
    (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι)
    (hjp : jointProximity (C := C) (u := u) δ) :
    Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ] ≤
      jointlyProximateContribution (F := F) C δ := by
  unfold jointlyProximateContribution
  refine le_trans ?_ (le_iSup (fun u : WordStack A (Fin 2) ι ↦
    if jointProximity (C := C) (u := u) δ then
      Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ]
    else (0 : ENNReal)) u)
  rw [if_pos hjp]

open Classical in
/-- **Counting form.** A jointly-close stack carrying a finite set `G` of MCA-bad scalars
pushes the jointly-proximate contribution up to `|G|/|F|`. -/
theorem jointlyProximateContribution_ge_card_div
    (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) (G : Finset F)
    (hjp : jointProximity (C := C) (u := u) δ)
    (hG : ∀ γ ∈ G, mcaEvent C δ (u 0) (u 1) γ) :
    (G.card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      jointlyProximateContribution (F := F) C δ := by
  refine le_trans ?_ (le_jointlyProximateContribution_of_jointProximity C δ u hjp)
  rw [prob_uniform_eq_card_filter_div_card]
  have hsub : G ⊆ Finset.filter (fun γ => mcaEvent C δ (u 0) (u 1) γ) Finset.univ := by
    intro γ hγ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hG γ hγ
  have hcard : G.card
      ≤ (Finset.filter (fun γ => mcaEvent C δ (u 0) (u 1) γ) Finset.univ).card :=
    Finset.card_le_card hsub
  simp only [ENNReal.coe_natCast]
  gcongr

open Classical in
/-- **The window floor, packaged.** A shifted-normal-form stack (rows supported on `E`,
`|Eᶜ| ≥ (1−δ)n`, no nonzero codeword vanishing off `E`) whose ratio scalars include a
finite set `G` gives `jointlyProximateContribution C δ ≥ |G|/|F|`.  With generic values on
`E` one takes `|G| = |E| = ⌊δn⌋` distinct ratios, so the in-tree UDR ceiling `⌊δn⌋/|F|`
on the jointly-proximate contribution is **tight**, and it extends as a floor through the
entire window `δ < 1 − ρ`: by the localization identity, no CA ⇒ MCA transfer at lines can
produce an MCA bound below `⌊δn⌋/|F|`. -/
theorem jointlyProximateContribution_ge_of_supported_stack
    (C : Set (ι → A)) (h0 : (0 : ι → A) ∈ C) (δ : ℝ≥0) {E : Finset ι}
    (u : WordStack A (Fin 2) ι)
    (hu : ∀ r : Fin 2, ∀ i ∉ E, u r i = 0)
    (hEc : ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (Eᶜ.card : ℝ≥0))
    (hvan : ∀ c ∈ C, (∀ i ∉ E, c i = 0) → c = 0)
    (G : Finset F)
    (hG : ∀ γ ∈ G, ∃ i₀ ∈ E, u 0 i₀ + γ • u 1 i₀ = 0 ∧ u 1 i₀ ≠ 0) :
    (G.card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      jointlyProximateContribution (F := F) C δ := by
  refine jointlyProximateContribution_ge_card_div C δ u G
    (jointProximity_of_vanishing_outside_support C h0 δ u hu hEc) ?_
  intro γ hγ
  obtain ⟨i₀, hi₀, hker, hne⟩ := hG γ hγ
  exact mcaEvent_of_vanishing_outside_support C h0 δ (hu 0) (hu 1) hEc hvan hi₀ hker hne

open Classical in
/-- The window floor transfers to `ε_mca` itself: the supported-stack ratio scalars give
`ε_mca(C, δ) ≥ |G|/|F|` — for *any* code containing `0` with no nonzero codeword vanishing
off `E`, at *any* radius (in particular throughout the window, where for RS the hypothesis
`hvan` is automatic from `|Eᶜ| ≥ k`). -/
theorem epsMCA_ge_of_supported_stack
    (C : Set (ι → A)) (h0 : (0 : ι → A) ∈ C) (δ : ℝ≥0) {E : Finset ι}
    (u : WordStack A (Fin 2) ι)
    (hu : ∀ r : Fin 2, ∀ i ∉ E, u r i = 0)
    (hEc : ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (Eᶜ.card : ℝ≥0))
    (hvan : ∀ c ∈ C, (∀ i ∉ E, c i = 0) → c = 0)
    (G : Finset F)
    (hG : ∀ γ ∈ G, ∃ i₀ ∈ E, u 0 i₀ + γ • u 1 i₀ = 0 ∧ u 1 i₀ ≠ 0) :
    (G.card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ epsMCA (F := F) C δ :=
  le_trans
    (jointlyProximateContribution_ge_of_supported_stack C h0 δ u hu hEc hvan G hG)
    (jointlyProximateContribution_le_epsMCA C δ)

/-! ## 4. The below-gate ratio-scalar law: where the excess channel *cannot* open

The probe (`_out_466_ca_vs_mca.txt`) exhibits **excess fires** — jointly-close supported
stacks with *more* MCA-bad scalars than `|E|`, witnessed by *nonzero* codewords vanishing on
part of `Eᶜ`.  A nonzero witness must vanish on `≥ (1−δ)n − |E|` off-support points, so if
every nonzero codeword has at most `z` zeros (RS of dimension `k`: `z = k − 1`), the excess
channel is closed whenever `(1−δ)n > z + |E|` — the **excess gate**.  Below the gate this
section proves the *exact* structure: every MCA-bad scalar of an `E`-supported stack is a
**ratio scalar** (`badScalar_is_ratio_of_supported_below_gate`), and the bad set injects
into `E` (`badScalar_card_le_support_of_below_gate`), matching the §3 floor from the other
side.  For tight support `|E| = ⌊δn⌋` the gate reads `a > (n + k − 1)/2` — the UDR line —
so per-stack the dichotomy is: below-gate supported stacks carry *exactly* the `≤ |E|` ratio
scalars, and the probe shows the gate is sharp (excess fires appear as soon as
`a − |E| ≤ k − 1`: `n=8, k=3, a=5, |E|=3` already carries one; deeper in the window the
channel dominates — `53` excess fires at `n=8, k=3, a=4` and `≈ 4190` at `n=16, k=4, a=5`). -/

open Classical in
/-- **Below the excess gate, every bad scalar is a ratio scalar.** Let `(u₀, u₁)` vanish
outside `E`, suppose every nonzero codeword has at most `z` zero coordinates, and let the
gate `z + |E| < (1−δ)n` hold.  Then `mcaEvent` at `γ` forces some `i ∈ E` with `u₁ i ≠ 0`
and `u₀ i + γ • u₁ i = 0`.  Proof: any witness codeword agrees with the line on `S \ E`
where the line vanishes, and `|S \ E| ≥ (1−δ)n − |E| > z` forces the witness to be `0`; then
the line vanishes on all of `S`, and if no `i ∈ S ∩ E` had `u₁ i ≠ 0` the zero pair would
jointly explain `(u₀, u₁)` on `S`, contradicting the `mcaEvent` clause. -/
theorem badScalar_is_ratio_of_supported_below_gate
    (C : Set (ι → A)) (h0 : (0 : ι → A) ∈ C) (δ : ℝ≥0) {E : Finset ι} {u₀ u₁ : ι → A}
    (z : ℕ)
    (hu₀ : ∀ i ∉ E, u₀ i = 0) (hu₁ : ∀ i ∉ E, u₁ i = 0)
    (hzero : ∀ c ∈ C, c ≠ 0 →
      ((Finset.univ.filter (fun i : ι => c i = 0)).card ≤ z))
    (hgate : ((z + E.card : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card ι : ℝ≥0))
    {γ : F} (hmca : mcaEvent C δ u₀ u₁ γ) :
    ∃ i ∈ E, u₁ i ≠ 0 ∧ u₀ i + γ • u₁ i = 0 := by
  classical
  obtain ⟨S, hS, ⟨w, hwC, hwagree⟩, hno⟩ := hmca
  -- gate arithmetic: `z + |E| < |S|`, hence `z < |S \ E|`.
  have hcard : z + E.card < S.card := by
    exact_mod_cast lt_of_lt_of_le hgate hS
  have hsplit : S.card ≤ (S \ E).card + E.card := by
    calc S.card ≤ (S ∪ E).card := Finset.card_le_card Finset.subset_union_left
    _ = (S \ E).card + E.card := (Finset.card_sdiff_add_card S E).symm
  have hSE : z < (S \ E).card := by omega
  -- the witness vanishes on `S \ E` (the line does), so it has `> z` zeros: it is `0`.
  have hwz : (S \ E) ⊆ Finset.univ.filter (fun i : ι => w i = 0) := by
    intro i hi
    obtain ⟨hiS, hiE⟩ := Finset.mem_sdiff.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hwagree i hiS, hu₀ i hiE, hu₁ i hiE, smul_zero, add_zero]
  have hw0 : w = 0 := by
    by_contra hne
    exact absurd (hzero w hwC hne)
      (not_le.mpr (lt_of_lt_of_le hSE (Finset.card_le_card hwz)))
  -- hence the line vanishes on all of `S`.
  have hline : ∀ i ∈ S, u₀ i + γ • u₁ i = 0 := by
    intro i hi
    have h := hwagree i hi
    rw [hw0] at h
    exact h.symm
  -- either some in-support direction value is nonzero (a ratio scalar), or the zero pair
  -- jointly explains the stack on `S` — contradicting `¬ pairJointAgreesOn`.
  by_cases hex : ∃ i ∈ S, i ∈ E ∧ u₁ i ≠ 0
  · obtain ⟨i, hiS, hiE, hne⟩ := hex
    exact ⟨i, hiE, hne, hline i hiS⟩
  · exfalso
    push_neg at hex
    apply hno
    refine ⟨0, h0, 0, h0, fun i hi => ?_⟩
    by_cases hiE : i ∈ E
    · have h1 : u₁ i = 0 := hex i hi hiE
      have h0i : u₀ i = 0 := by
        have := hline i hi
        rwa [h1, smul_zero, add_zero] at this
      exact ⟨h0i.symm, h1.symm⟩
    · exact ⟨(hu₀ i hiE).symm, (hu₁ i hiE).symm⟩

open Classical in
/-- **Below the gate, the bad-scalar set injects into the support: `#bad ≤ |E|`.** Each bad
scalar picks (by the ratio law) a support coordinate `i` with `u₁ i ≠ 0` killing the line;
two scalars sharing the same `i` coincide (`(γ₁ − γ₂) • u₁ i = 0`).  Together with §3
(designed supported stacks fire at every distinct ratio) this is the exact per-stack value
of the B4 obstruction below the gate: the bad set *is* the ratio-scalar set.  The probe
shows sharpness: one step past the gate, nonzero-codeword witnesses already produce excess
bad scalars beyond `|E|`. -/
theorem badScalar_card_le_support_of_below_gate [NoZeroSMulDivisors F A]
    (C : Set (ι → A)) (h0 : (0 : ι → A) ∈ C) (δ : ℝ≥0) {E : Finset ι} {u₀ u₁ : ι → A}
    (z : ℕ)
    (hu₀ : ∀ i ∉ E, u₀ i = 0) (hu₁ : ∀ i ∉ E, u₁ i = 0)
    (hzero : ∀ c ∈ C, c ≠ 0 →
      ((Finset.univ.filter (fun i : ι => c i = 0)).card ≤ z))
    (hgate : ((z + E.card : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card ι : ℝ≥0)) :
    (Finset.univ.filter (fun γ : F => mcaEvent C δ u₀ u₁ γ)).card ≤ E.card := by
  classical
  have key : ∀ γ : F, ∃ i : ι, mcaEvent C δ u₀ u₁ γ →
      (i ∈ E ∧ u₁ i ≠ 0 ∧ u₀ i + γ • u₁ i = 0) := by
    intro γ
    by_cases h : mcaEvent C δ u₀ u₁ γ
    · obtain ⟨i, hiE, hne, hker⟩ :=
        badScalar_is_ratio_of_supported_below_gate C h0 δ z hu₀ hu₁ hzero hgate h
      exact ⟨i, fun _ => ⟨hiE, hne, hker⟩⟩
    · exact ⟨Classical.arbitrary ι, fun hc => absurd hc h⟩
  choose f hf using key
  refine Finset.card_le_card_of_injOn f (fun γ hγ => ?_) ?_
  · exact (hf γ (Finset.mem_filter.mp hγ).2).1
  · intro γ₁ hγ₁ γ₂ hγ₂ heq
    obtain ⟨_, hne₁, hker₁⟩ := hf γ₁ (Finset.mem_filter.mp (by exact_mod_cast hγ₁)).2
    obtain ⟨_, hne₂, hker₂⟩ := hf γ₂ (Finset.mem_filter.mp (by exact_mod_cast hγ₂)).2
    rw [heq] at hker₁ hne₁
    have hsub : (γ₁ - γ₂) • u₁ (f γ₂) = 0 := by
      have := hker₁.trans hker₂.symm
      have h2 : γ₁ • u₁ (f γ₂) = γ₂ • u₁ (f γ₂) := by
        exact add_left_cancel this
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp hsub with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hne₁

end ProximityGap.B4Lines

/-! ## Axiom audit (must be `[propext, Classical.choice, Quot.sound]`, no `sorryAx`) -/
#print axioms ProximityGap.B4Lines.mcaEvent_of_line_close_of_not_jointProximity
#print axioms ProximityGap.B4Lines.mcaEvent_iff_line_close_of_not_jointProximity
#print axioms ProximityGap.B4Lines.line_close_imp_mcaEvent_or_jointProximity
#print axioms ProximityGap.B4Lines.jointlyProximateContribution_le_epsMCA
#print axioms ProximityGap.B4Lines.epsMCA_eq_max_epsCA_jointlyProximateContribution
#print axioms ProximityGap.B4Lines.mcaEvent_of_vanishing_outside_support
#print axioms ProximityGap.B4Lines.jointProximity_of_vanishing_outside_support
#print axioms ProximityGap.B4Lines.le_jointlyProximateContribution_of_jointProximity
#print axioms ProximityGap.B4Lines.jointlyProximateContribution_ge_card_div
#print axioms ProximityGap.B4Lines.jointlyProximateContribution_ge_of_supported_stack
#print axioms ProximityGap.B4Lines.epsMCA_ge_of_supported_stack
#print axioms ProximityGap.B4Lines.badScalar_is_ratio_of_supported_below_gate
#print axioms ProximityGap.B4Lines.badScalar_card_le_support_of_below_gate
