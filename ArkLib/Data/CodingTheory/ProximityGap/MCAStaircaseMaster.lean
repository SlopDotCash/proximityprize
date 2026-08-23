/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAGeneralStaircaseRefuted

/-!
# Round 4 capstone (#357): THE MASTER COLLAPSE — band-`b` at `d ≥ 3b−2`, all `b`, one induction

The staircase programme's collapse theorems (bands 2 and 3) and the conjectured general law
unify into a single recursion. The structural facts that make it work:

* the cored `c*`-elimination at core `X` with residual punctures of size `≤ r` needs only
  `|X| + 3r < d` (`ext_at_general`: the triple combination is supported on `X` and three
  residuals);
* an unextendable residual point is hosted by all but at most one scalar, and **coring at
  it preserves the per-scalar obstruction sets verbatim**:
  `insert j X ∪ (P_a.erase j) = X ∪ P_a`, so the no-joint-explanation hypotheses descend
  unchanged;
* each coring step trades residual size for core size (budget `|X| + 3r` drops by `2`) and
  loses at most one scalar; from `r + 2` scalars the recursion bottoms out at two scalars
  with empty residuals, where the shared-witness pairing kills.

**`collapse_level`** (induction on `r`): `r + 2` distinct bad-scalar data with common core
`X`, residuals `≤ r`, and no nonzero codeword on `≤ |X| + 3r` points — contradiction.

**`badScalar_card_le_of_dist`** (`X = ∅`, `r = b − 1`): every linear code with no nonzero
codeword on `≤ 3(b−1)` points (distance `≥ 3b − 2`) has at most `b` bad scalars per stack
at every radius with `δ·n < b` — **the full linear staircase below `3b − 2`, every band at
once**, with `epsMCA_le_div_card_of_dist : ε_mca ≤ b/|F|`. Sharp at `b = 2, 3, 4`: the
`(b−1)`-tupled-column codes explode at `d = 3b − 3` (the cocycle, doubled-column and
tripled-column refutations).

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCAStaircaseMaster

open ProximityGap.MCABandTwoCollapse

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- Parameterized distance hypothesis: no nonzero codeword on `≤ m` points. -/
def NoWeightLE (C : Submodule F (ι → A)) (m : ℕ) : Prop :=
  ∀ w ∈ C, (∃ T : Finset ι, T.card ≤ m ∧ ∀ i ∉ T, w i = 0) → w = 0

/-- The parameterized extension engine: with agreements off `X ∪ P_x` and the support
budget `|X| + |P₁| + |P₂| + |P₃| ≤ m`, the middle scalar's agreement extends to any point
outside `X ∪ P₁ ∪ P₃`. -/
theorem ext_at_general (C : Submodule F (ι → A)) {m : ℕ} (hC : NoWeightLE C m)
    {γ₁ γ₂ γ₃ : F} (h12 : γ₁ ≠ γ₂) (h13 : γ₁ ≠ γ₃)
    {u₀ u₁ : ι → A} {w₁ w₂ w₃ : ι → A}
    (hw₁ : w₁ ∈ C) (hw₂ : w₂ ∈ C) (hw₃ : w₃ ∈ C)
    {X P₁ P₂ P₃ : Finset ι}
    (hbud : X.card + (P₁.card + (P₂.card + P₃.card)) ≤ m)
    (hag₁ : ∀ j : ι, j ∉ X → j ∉ P₁ → w₁ j = u₀ j + γ₁ • u₁ j)
    (hag₂ : ∀ j : ι, j ∉ X → j ∉ P₂ → w₂ j = u₀ j + γ₂ • u₁ j)
    (hag₃ : ∀ j : ι, j ∉ X → j ∉ P₃ → w₃ j = u₀ j + γ₃ • u₁ j)
    {j : ι} (hjX : j ∉ X) (hj1 : j ∉ P₁) (hj3 : j ∉ P₃) :
    w₂ j = u₀ j + γ₂ • u₁ j := by
  set cstar : ι → A := (γ₁ - γ₃) • (w₁ - w₂) - (γ₁ - γ₂) • (w₁ - w₃) with hcstar
  have hcmem : cstar ∈ C :=
    C.sub_mem (C.smul_mem _ (C.sub_mem hw₁ hw₂)) (C.smul_mem _ (C.sub_mem hw₁ hw₃))
  have hsupp : ∀ i ∉ X ∪ (P₁ ∪ (P₂ ∪ P₃)), cstar i = 0 := by
    intro i hi
    simp only [Finset.mem_union, not_or] at hi
    obtain ⟨hiX, hi1, hi2, hi3⟩ := hi
    show (γ₁ - γ₃) • (w₁ i - w₂ i) - (γ₁ - γ₂) • (w₁ i - w₃ i) = 0
    rw [hag₁ i hiX hi1, hag₂ i hiX hi2, hag₃ i hiX hi3]
    module
  have hcard : (X ∪ (P₁ ∪ (P₂ ∪ P₃))).card ≤ m := by
    have h1 := Finset.card_union_le X (P₁ ∪ (P₂ ∪ P₃))
    have h2 := Finset.card_union_le P₁ (P₂ ∪ P₃)
    have h3 := Finset.card_union_le P₂ P₃
    omega
  have hczero : cstar = 0 := hC cstar hcmem ⟨X ∪ (P₁ ∪ (P₂ ∪ P₃)), hcard, hsupp⟩
  have hz : (γ₁ - γ₃) • (w₁ j - w₂ j) - (γ₁ - γ₂) • (w₁ j - w₃ j) = 0 :=
    congrFun hczero j
  rw [hag₁ j hjX hj1, hag₃ j hjX hj3] at hz
  have hac0 : γ₁ - γ₃ ≠ 0 := sub_ne_zero.mpr h13
  have hXY : (γ₁ - γ₃) • ((u₀ j + γ₁ • u₁ j) - w₂ j)
      = (γ₁ - γ₃) • ((γ₁ - γ₂) • u₁ j) := by
    have hY : (γ₁ - γ₂) • ((u₀ j + γ₁ • u₁ j) - (u₀ j + γ₃ • u₁ j))
        = (γ₁ - γ₃) • ((γ₁ - γ₂) • u₁ j) := by module
    have hXeq := sub_eq_zero.mp hz
    rw [hY] at hXeq
    exact hXeq
  have hcanc := congrArg (fun v => (γ₁ - γ₃)⁻¹ • v) hXY
  simp only [inv_smul_smul₀ hac0] at hcanc
  have hwb_eq : w₂ j = (u₀ j + γ₁ • u₁ j) - (γ₁ - γ₂) • u₁ j := by
    rw [← hcanc]
    abel
  rw [hwb_eq]
  module

open Classical in
/-- **The master recursion** (induction on the residual size `r`). -/
theorem collapse_level (C : Submodule F (ι → A)) {m : ℕ} (hC : NoWeightLE C m)
    (u₀ u₁ : ι → A) :
    ∀ (r : ℕ) (X : Finset ι), X.card + 3 * r ≤ m →
    ∀ (γf : Fin (r + 2) → F) (wf : Fin (r + 2) → ι → A) (Pf : Fin (r + 2) → Finset ι),
      (∀ a b : Fin (r + 2), a ≠ b → γf a ≠ γf b) →
      (∀ a, wf a ∈ C) →
      (∀ a, (Pf a).card ≤ r) →
      (∀ (a) (j : ι), j ∉ X → j ∉ Pf a → wf a j = u₀ j + γf a • u₁ j) →
      (∀ a, ¬ pairJointAgreesOn (C : Set (ι → A)) (Finset.univ \ (X ∪ Pf a)) u₀ u₁) →
      False := by
  intro r
  induction r with
  | zero =>
    intro X hbud γf wf Pf hγ hw hP hag hno
    have hP0 : ∀ a, Pf a = ∅ := fun a => Finset.card_eq_zero.mp (Nat.le_zero.mp (hP a))
    refine hno 0 (pairJoint_of_shared_witness C (hγ 0 1 (by decide)) (hw 0) (hw 1)
      (fun j hj => hag 0 j ?_ ?_) (fun j hj => hag 1 j ?_ ?_))
    · exact fun hjX => (Finset.mem_sdiff.mp hj).2 (Finset.mem_union_left _ hjX)
    · rw [hP0 0]; exact Finset.notMem_empty j
    · exact fun hjX => (Finset.mem_sdiff.mp hj).2 (Finset.mem_union_left _ hjX)
    · rw [hP0 1]; exact Finset.notMem_empty j
  | succ r ih =>
    intro X hbud γf wf Pf hγ hw hP hag hno
    -- two clean scalars (agreeing off X alone) are contradictory
    have hclean2 : ∀ a b : Fin (r + 3), a ≠ b →
        (∀ j : ι, j ∉ X → wf a j = u₀ j + γf a • u₁ j) →
        (∀ j : ι, j ∉ X → wf b j = u₀ j + γf b • u₁ j) → False := by
      intro a b hab hca hcb
      refine hno a (pairJoint_of_shared_witness C (hγ a b hab) (hw a) (hw b)
        (fun j hj => hca j fun hjX =>
          (Finset.mem_sdiff.mp hj).2 (Finset.mem_union_left _ hjX))
        (fun j hj => hcb j fun hjX =>
          (Finset.mem_sdiff.mp hj).2 (Finset.mem_union_left _ hjX)))
    by_cases hexU : ∃ b : Fin (r + 3), ¬ ∀ j : ι, j ∉ X → wf b j = u₀ j + γf b • u₁ j
    case neg =>
      push Not at hexU
      exact hclean2 0 1 (by
        intro h
        have hval := congrArg Fin.val h
        simp at hval) (hexU 0) (hexU 1)
    case pos =>
    obtain ⟨b, hub⟩ := hexU
    -- the unextendable residual point of b
    push Not at hub
    obtain ⟨j, hjX, hjne⟩ := hub
    have hjPb : j ∈ Pf b := by
      by_contra hjb
      exact hjne (hag b j hjX hjb)
    have hdeep : ∀ a c : Fin (r + 3), a ≠ b → a ≠ c → j ∈ Pf a ∨ j ∈ Pf c := by
      intro a c hab hac
      by_contra hcon
      push Not at hcon
      refine hjne (ext_at_general C hC (hγ a b hab) (hγ a c hac) (hw a) (hw b) (hw c)
        ?_ (hag a) (hag b) (hag c) hjX hcon.1 hcon.2)
      refine le_trans ?_ hbud
      have h1 := hP a
      have h2 := hP b
      have h3 := hP c
      omega
    -- the host set has at least r + 2 elements
    have hHcard : r + 2 ≤ (Finset.univ.filter (fun a : Fin (r + 3) => j ∈ Pf a)).card := by
      -- non-hosts number at most one
      have hOle : (Finset.univ.filter (fun a : Fin (r + 3) => ¬ j ∈ Pf a)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha c hc
        rw [Finset.mem_filter] at ha hc
        by_contra hac
        have hab : a ≠ b := by
          rintro rfl
          exact ha.2 hjPb
        rcases hdeep a c hab hac with h | h
        · exact ha.2 h
        · exact hc.2 h
      have hsplit : (Finset.univ.filter (fun a : Fin (r + 3) => j ∈ Pf a)).card
          + (Finset.univ.filter (fun a : Fin (r + 3) => ¬ j ∈ Pf a)).card = r + 3 := by
        have h := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin (r + 3)))) (p := fun a => j ∈ Pf a)
        rwa [Finset.card_univ, Fintype.card_fin] at h
      omega
    -- trim to exactly r + 2 hosts and reindex
    obtain ⟨H', hH'sub, hH'card⟩ := Finset.exists_subset_card_eq hHcard
    set f : Fin (r + 2) → Fin (r + 3) := fun i => (H'.orderIsoOfFin hH'card i : Fin (r + 3))
      with hf
    have hfinj : Function.Injective f := fun i i' hii' => by
      have := (H'.orderIsoOfFin hH'card).injective (Subtype.ext hii')
      exact this
    have hfH : ∀ i, j ∈ Pf (f i) := by
      intro i
      have hmem : (f i) ∈ H' := (H'.orderIsoOfFin hH'card i).2
      have h2 := hH'sub hmem
      rw [Finset.mem_filter] at h2
      exact h2.2
    -- descend
    refine ih (insert j X) ?_ (γf ∘ f) (wf ∘ f) (fun i => (Pf (f i)).erase j)
      (fun a c hac => hγ (f a) (f c) (fun h => hac (hfinj h)))
      (fun a => hw (f a)) (fun a => ?_) (fun a y hyX hyP => ?_) (fun a => ?_)
    · -- budget
      have hXc := Finset.card_insert_le j X
      omega
    · -- residual card
      show ((Pf (f a)).erase j).card ≤ r
      have herase := Finset.card_erase_of_mem (hfH a)
      have hPa := hP (f a)
      omega
    · -- agreements off the new core/residuals
      have hyXold : y ∉ X := fun h => hyX (Finset.mem_insert_of_mem h)
      have hyj : y ≠ j := fun h => hyX (h ▸ Finset.mem_insert_self j X)
      have hyPold : y ∉ Pf (f a) := fun h => hyP (Finset.mem_erase.mpr ⟨hyj, h⟩)
      exact hag (f a) y hyXold hyPold
    · -- the obstruction set is unchanged: insert j X ∪ (Pf (f a)).erase j = X ∪ Pf (f a)
      show ¬ pairJointAgreesOn (C : Set (ι → A))
        (Finset.univ \ (insert j X ∪ (Pf (f a)).erase j)) u₀ u₁
      have hset : insert j X ∪ (Pf (f a)).erase j = X ∪ Pf (f a) := by
        rw [Finset.insert_union]
        rw [← Finset.union_insert]
        rw [Finset.insert_erase (hfH a)]
      rw [hset]
      exact hno (f a)

open Classical in
/-- Band-`b` puncture extraction: a bad scalar at `δ·n < b` yields a puncture set of size
`≤ b − 1`, a codeword agreeing off it, and no joint explanation on its complement. -/
theorem extract_general (C : Submodule F (ι → A)) {b : ℕ} (hb : 1 ≤ b)
    (hnb : b ≤ Fintype.card ι) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < (b : ℝ≥0)) {u₀ u₁ : ι → A} {γ : F}
    (hev : mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ) :
    ∃ (P : Finset ι) (w : ι → A), P.card ≤ b - 1 ∧ w ∈ C ∧
      (∀ j : ι, j ∉ P → w j = u₀ j + γ • u₁ j) ∧
      ¬ pairJointAgreesOn (C : Set (ι → A)) (Finset.univ \ P) u₀ u₁ := by
  obtain ⟨S, hS, ⟨w, hw, hag⟩, hno⟩ := hev
  refine ⟨Finset.univ \ S, w, ?_, hw, fun j hj => ?_, fun hpj => ?_⟩
  · -- the missed set is small
    have hδ1 : δ < 1 := by
      by_contra hge
      push Not at hge
      have hcast : ((b : ℕ) : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := by exact_mod_cast hnb
      have : ((b : ℕ) : ℝ≥0) ≤ δ * (Fintype.card ι : ℝ≥0) := by
        calc ((b : ℕ) : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := hcast
          _ = 1 * (Fintype.card ι : ℝ≥0) := (one_mul _).symm
          _ ≤ δ * (Fintype.card ι : ℝ≥0) := by gcongr
      exact absurd hδ (not_lt.mpr this)
    have hSR : ((1 : ℝ) - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) := by
      have hcast : ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast hS
      rwa [NNReal.coe_sub hδ1.le, NNReal.coe_one] at hcast
    have hδR : (δ : ℝ) * (Fintype.card ι : ℝ) < (b : ℝ) := by exact_mod_cast hδ
    have hsplit : (Finset.univ \ S).card + S.card = Fintype.card ι := by
      have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
      rwa [Finset.card_univ] at h
    have hclaim : (Fintype.card ι : ℝ) - (b : ℝ) < (S.card : ℝ) := by nlinarith
    have hlt : Fintype.card ι < S.card + b := by
      exact_mod_cast (by linarith : (Fintype.card ι : ℝ) < (S.card : ℝ) + (b : ℝ))
    omega
  · refine hag j ?_
    by_contra hjS
    exact hj (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hjS⟩)
  · obtain ⟨v₀, hv₀, v₁, hv₁, hagv⟩ := hpj
    refine hno ⟨v₀, hv₀, v₁, hv₁, fun y hy => hagv y ?_⟩
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, fun hyd => ?_⟩
    exact (Finset.mem_sdiff.mp hyd).2 hy

open Classical in
/-- **THE MASTER STAIRCASE THEOREM:** every linear code with no nonzero codeword supported
on `≤ 3(b−1)` points (distance `≥ 3b − 2`) has at most `b` bad scalars per stack at every
radius with `δ·n < b` — the full linear staircase, every band at once. Sharp at
`b = 2, 3, 4` (the `(b−1)`-tupled-column explosions at `d = 3b − 3`). -/
theorem badScalar_card_le_of_dist (C : Submodule F (ι → A)) (b : ℕ) (hb : 1 ≤ b)
    (hC : NoWeightLE C (3 * (b - 1))) (hnb : b ≤ Fintype.card ι) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < (b : ℝ≥0)) (u : WordStack A (Fin 2) ι) :
    (Finset.filter (fun γ : F =>
        mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ) Finset.univ).card ≤ b := by
  by_contra hgt
  push Not at hgt
  -- a (b+1)-element family of distinct bad scalars
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hgt
  set g : Fin (b + 1) → F :=
    fun i => (T.equivFin.symm (Fin.cast hTcard.symm i) : F) with hg
  have hginj : Function.Injective g := by
    intro i i' hii'
    have h1 := T.equivFin.symm.injective (Subtype.ext hii')
    exact Fin.cast_injective hTcard.symm h1
  have hgbad : ∀ i, mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) (g i) := by
    intro i
    have hmem : (g i) ∈ T := (T.equivFin.symm (Fin.cast hTcard.symm i)).2
    have := hTsub hmem
    rw [Finset.mem_filter] at this
    exact this.2
  -- extract per-scalar puncture data
  choose Pof wof hPcard hwmem hagree hnopair using fun i =>
    extract_general C hb hnb hδ (hgbad i)
  -- feed the master recursion at r = b − 1, X = ∅
  have hb1 : b - 1 + 2 = b + 1 := by omega
  refine collapse_level C hC (u 0) (u 1) (b - 1) ∅ (by simp)
    (fun i => g (Fin.cast hb1 i)) (fun i => wof (Fin.cast hb1 i))
    (fun i => Pof (Fin.cast hb1 i))
    (fun a c hac => ?_) (fun a => hwmem _) (fun a => hPcard _)
    (fun a y hyX hyP => hagree _ y hyP) (fun a => ?_)
  · refine fun h => hac ?_
    have hcast := hginj h
    exact Fin.cast_injective hb1 hcast
  · rw [Finset.empty_union]
    exact hnopair _

open Classical in
/-- `ε_mca(C, δ) ≤ b/|F|` on the whole band `δ·n < b`, for distance `≥ 3b − 2`. -/
theorem epsMCA_le_div_card_of_dist (C : Submodule F (ι → A)) (b : ℕ) (hb : 1 ≤ b)
    (hC : NoWeightLE C (3 * (b - 1))) (hnb : b ≤ Fintype.card ι) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < (b : ℝ≥0)) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      ≤ (b : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast badScalar_card_le_of_dist C b hb hC hnb hδ u

/-! ## Source audit -/

#print axioms ext_at_general
#print axioms collapse_level
#print axioms extract_general
#print axioms badScalar_card_le_of_dist
#print axioms epsMCA_le_div_card_of_dist

end ProximityGap.MCAStaircaseMaster
