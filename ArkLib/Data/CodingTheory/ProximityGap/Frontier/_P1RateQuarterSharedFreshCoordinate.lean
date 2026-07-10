/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCommonFactorArithmetic
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CaptureKernelUD

/-!
# The three-scalar shared-fresh-coordinate configuration at the P1 predecessor

`[rate-quarter-joint-witness-bare-charge]` proved that any over-budget escape charge at the
P1 rate-quarter predecessor has three distinct bad scalars whose event witnesses share one
fresh coordinate outside a known threshold joint-agreement set, and that the bare MCA clauses
cannot exclude this.  This file determines exactly what the configuration forces for
Reed--Solomon (linear) codes, and refutes its bare impossibility.

**Forced structure (proved below, code-generic where possible):**

* *Divided-difference pencil*: witnesses `(S₁,p₁,γ₁)` and `(S₂,p₂,γ₂)` with `γ₁ ≠ γ₂`
  produce codewords `w₁ = (γ₂-γ₁)⁻¹ • (p₂-p₁)` and `w₀ = p₁ - γ₁ • w₁` with
  `p_j = w₀ + γ_j • w₁` and `(w₀,w₁) = (u₀,u₁)` on `S₁ ∩ S₂`.  In particular every pair of
  distinct bad scalars yields a joint explanation on the pairwise witness intersection, which
  at the predecessor has at least `2T - N = 111848108` coordinates.
* *Witness incomparability*: `S₁ ⊆ S₂` is impossible — the pencil would jointly explain the
  stack on `S₁`, contradicting the non-joint clause.
* *Distinct values at the shared coordinate* when `u₁ i ≠ 0`.
* *Absorption dichotomy*: with a known joint pair `(q₀,q₁)` on `J`, if `k ≤ |S₁ ∩ S₂ ∩ J|`
  then the pencil **is** `(q₀,q₁)` and the shared coordinate is absorbed into the maximal
  joint-agreement set.  At P1 this premise is *not* forced (`3T ≤ 2N + k - 1`).
* *Collinear boost*: if the three witness codewords lie on one pencil, that pencil agrees
  with the stack on the whole two-cover region `U` of the witnesses, and
  `3T ≤ N + 2|U|` gives `|U| ≥ 352321537 ≥ k = 2^28`: a collinear shared triple forces a
  joint pencil with beyond-unique-decoding agreement (still below the threshold `T`, so this
  alone does not contradict the non-joint clauses).

**Refutation (kernel-checked below):** the non-absorbed shared-fresh triple is *realizable*
in Reed--Solomon codes.  An explicit `RS[8,2]` stack over `F_11` has a size-4 joint set
`J = {0,1,2,3}`, three distinct bad scalars `1,2,3` at radius `1/2` (threshold `4`) whose
witnesses `{0,4,5,6}, {1,4,5,7}, {2,4,6,7}` all contain the fresh coordinate `4 ∉ J`, and no
joint pair explains `J ∪ {4}`.  Hence no code-generic impossibility proof of the shared-fresh
triple exists; only P1-specific counting can close the branch.

**Sufficient condition, subsequently refuted:** `SharedFreshTripleFree` asserted that at the
literal P1 predecessor no fresh coordinate outside a threshold joint set carries three distinct
bad scalars.  The consumer theorem `badFamily_card_le_N_of_sharedFreshTripleFree` correctly shows
that this condition would close the fixed-witness branch.  However,
`_P1RateQuarterSharedFreshTripleRefuted.lean` constructs `480,946,859` such scalars through one
fresh coordinate on every injective P1 domain.  The proposition is retained here because its
consumer records exactly why the tempting charge argument fails.

Executable certificate: `scripts/probes/probe_rate_quarter_p1_shared_fresh_coordinate.py`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 800000
set_option maxRecDepth 500000

open Finset Polynomial
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped NNReal Polynomial

namespace ProximityGap.SharedFreshPencil

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F]
variable {A : Type} [AddCommGroup A] [Module F A]

attribute [local instance] Classical.propDecidable

/-! ## The divided-difference pencil of two event witnesses -/

/-- The divided-difference direction `(p₂ - p₁)/(γ₂ - γ₁)` of two line codewords. -/
def pencilDir (γ₁ γ₂ : F) (p₁ p₂ : ι → A) : ι → A :=
  (γ₂ - γ₁)⁻¹ • (p₂ - p₁)

/-- The pencil base `p₁ - γ₁ • pencilDir`. -/
def pencilBase (γ₁ γ₂ : F) (p₁ p₂ : ι → A) : ι → A :=
  p₁ - γ₁ • pencilDir γ₁ γ₂ p₁ p₂

theorem pencilDir_mem (C : Submodule F (ι → A)) {γ₁ γ₂ : F} {p₁ p₂ : ι → A}
    (hp₁ : p₁ ∈ C) (hp₂ : p₂ ∈ C) : pencilDir γ₁ γ₂ p₁ p₂ ∈ C :=
  C.smul_mem _ (C.sub_mem hp₂ hp₁)

theorem pencilBase_mem (C : Submodule F (ι → A)) {γ₁ γ₂ : F} {p₁ p₂ : ι → A}
    (hp₁ : p₁ ∈ C) (hp₂ : p₂ ∈ C) : pencilBase γ₁ γ₂ p₁ p₂ ∈ C :=
  C.sub_mem hp₁ (C.smul_mem _ (pencilDir_mem C hp₁ hp₂))

/-- The pencil reproduces the first witness codeword. -/
theorem pencil_reproduces_first (γ₁ γ₂ : F) (p₁ p₂ : ι → A) :
    pencilBase γ₁ γ₂ p₁ p₂ + γ₁ • pencilDir γ₁ γ₂ p₁ p₂ = p₁ :=
  sub_add_cancel _ _

/-- The pencil reproduces the second witness codeword. -/
theorem pencil_reproduces_second {γ₁ γ₂ : F} (hγ : γ₁ ≠ γ₂) (p₁ p₂ : ι → A) :
    pencilBase γ₁ γ₂ p₁ p₂ + γ₂ • pencilDir γ₁ γ₂ p₁ p₂ = p₂ := by
  have hne : γ₂ - γ₁ ≠ 0 := sub_ne_zero_of_ne (Ne.symm hγ)
  set d := pencilDir γ₁ γ₂ p₁ p₂ with hd
  calc
    p₁ - γ₁ • d + γ₂ • d = p₁ + (γ₂ • d - γ₁ • d) := by abel
    _ = p₁ + (γ₂ - γ₁) • d := by rw [sub_smul]
    _ = p₁ + (p₂ - p₁) := by rw [hd, pencilDir, smul_inv_smul₀ hne]
    _ = p₂ := by abel

/-- **Pencil transport.**  On the intersection of the two witness sets, the pencil equals the
received stack. -/
theorem pencil_agrees_on_inter {γ₁ γ₂ : F} (hγ : γ₁ ≠ γ₂)
    {S₁ S₂ : Finset ι} {u₀ u₁ p₁ p₂ : ι → A}
    (h₁ : ∀ i ∈ S₁, p₁ i = u₀ i + γ₁ • u₁ i)
    (h₂ : ∀ i ∈ S₂, p₂ i = u₀ i + γ₂ • u₁ i) :
    ∀ i ∈ S₁ ∩ S₂,
      pencilBase γ₁ γ₂ p₁ p₂ i = u₀ i ∧ pencilDir γ₁ γ₂ p₁ p₂ i = u₁ i := by
  intro i hi
  have hne : γ₂ - γ₁ ≠ 0 := sub_ne_zero_of_ne (Ne.symm hγ)
  obtain ⟨hi₁, hi₂⟩ := Finset.mem_inter.mp hi
  have hdir : pencilDir γ₁ γ₂ p₁ p₂ i = u₁ i := by
    show (γ₂ - γ₁)⁻¹ • (p₂ - p₁) i = u₁ i
    rw [Pi.sub_apply, h₂ i hi₂, h₁ i hi₁,
      add_sub_add_left_eq_sub, ← sub_smul, inv_smul_smul₀ hne]
  refine ⟨?_, hdir⟩
  show p₁ i - γ₁ • pencilDir γ₁ γ₂ p₁ p₂ i = u₀ i
  rw [hdir, h₁ i hi₁, add_sub_cancel_right]

/-- Every pair of distinct bad scalars with event witnesses yields a joint explanation on the
pairwise witness intersection. -/
theorem pairJointAgreesOn_inter (C : Submodule F (ι → A)) {γ₁ γ₂ : F} (hγ : γ₁ ≠ γ₂)
    {S₁ S₂ : Finset ι} {u₀ u₁ p₁ p₂ : ι → A}
    (hp₁ : p₁ ∈ C) (hp₂ : p₂ ∈ C)
    (h₁ : ∀ i ∈ S₁, p₁ i = u₀ i + γ₁ • u₁ i)
    (h₂ : ∀ i ∈ S₂, p₂ i = u₀ i + γ₂ • u₁ i) :
    pairJointAgreesOn (C : Set (ι → A)) (S₁ ∩ S₂) u₀ u₁ :=
  ⟨pencilBase γ₁ γ₂ p₁ p₂, pencilBase_mem C hp₁ hp₂,
    pencilDir γ₁ γ₂ p₁ p₂, pencilDir_mem C hp₁ hp₂,
    pencil_agrees_on_inter hγ h₁ h₂⟩

/-- **Witness incomparability.**  The witness set of a bad scalar is never contained in the
witness set of a different bad scalar: the pencil would jointly explain the stack on it. -/
theorem witness_not_subset (C : Submodule F (ι → A)) {γ₁ γ₂ : F} (hγ : γ₁ ≠ γ₂)
    {S₁ S₂ : Finset ι} {u₀ u₁ p₁ p₂ : ι → A}
    (hp₁ : p₁ ∈ C) (hp₂ : p₂ ∈ C)
    (h₁ : ∀ i ∈ S₁, p₁ i = u₀ i + γ₁ • u₁ i)
    (h₂ : ∀ i ∈ S₂, p₂ i = u₀ i + γ₂ • u₁ i)
    (hno₁ : ¬ pairJointAgreesOn (C : Set (ι → A)) S₁ u₀ u₁) :
    ¬ S₁ ⊆ S₂ := by
  intro hsub
  apply hno₁
  have hinter : S₁ ∩ S₂ = S₁ := Finset.inter_eq_left.mpr hsub
  have := pairJointAgreesOn_inter C hγ hp₁ hp₂ h₁ h₂
  rwa [hinter] at this

/-- **Distinct values at a shared coordinate.**  When the direction row is nonzero at the
shared coordinate, distinct bad scalars have distinct witness-codeword values there. -/
theorem shared_values_distinct [NoZeroSMulDivisors F A] {γ₁ γ₂ : F} (hγ : γ₁ ≠ γ₂)
    {u₀ u₁ p₁ p₂ : ι → A} {i : ι}
    (h₁ : p₁ i = u₀ i + γ₁ • u₁ i) (h₂ : p₂ i = u₀ i + γ₂ • u₁ i)
    (hu : u₁ i ≠ 0) : p₁ i ≠ p₂ i := by
  intro heq
  have hsmul : γ₁ • u₁ i = γ₂ • u₁ i := by
    have := (h₁.symm.trans heq).trans h₂
    exact add_left_cancel this
  have hzero : (γ₁ - γ₂) • u₁ i = 0 := by
    rw [sub_smul, hsmul, sub_self]
  rcases smul_eq_zero.mp hzero with hcoef | hval
  · exact (sub_ne_zero_of_ne hγ) hcoef
  · exact hu hval

/-! ## The absorption dichotomy -/

/-- **Absorption.**  If the code separates on `kk` points (distinct codewords never agree on
`kk` coordinates) and the two witness sets meet a known joint set `J` in at least `kk`
coordinates, then the pencil *is* the known joint pair, and every coordinate of `S₁ ∩ S₂`
(in particular any shared fresh coordinate) is absorbed into the maximal joint-agreement set
of `(q₀,q₁)`. -/
theorem pencil_absorption (C : Submodule F (ι → A)) (kk : ℕ)
    (hsep : ∀ v ∈ C, ∀ w ∈ C, ∀ D : Finset ι,
      kk ≤ D.card → (∀ x ∈ D, v x = w x) → v = w)
    {γ₁ γ₂ : F} (hγ : γ₁ ≠ γ₂)
    {S₁ S₂ J : Finset ι} {u₀ u₁ p₁ p₂ q₀ q₁ : ι → A}
    (hq₀ : q₀ ∈ C) (hq₁ : q₁ ∈ C)
    (hJ : ∀ e ∈ J, q₀ e = u₀ e ∧ q₁ e = u₁ e)
    (hp₁ : p₁ ∈ C) (hp₂ : p₂ ∈ C)
    (h₁ : ∀ i ∈ S₁, p₁ i = u₀ i + γ₁ • u₁ i)
    (h₂ : ∀ i ∈ S₂, p₂ i = u₀ i + γ₂ • u₁ i)
    (hcard : kk ≤ (S₁ ∩ S₂ ∩ J).card) :
    ∀ i ∈ S₁ ∩ S₂, q₀ i = u₀ i ∧ q₁ i = u₁ i := by
  have hpencil := pencil_agrees_on_inter hγ h₁ h₂
  have hdir : pencilDir γ₁ γ₂ p₁ p₂ = q₁ := by
    apply hsep _ (pencilDir_mem C hp₁ hp₂) _ hq₁ (S₁ ∩ S₂ ∩ J) hcard
    intro x hx
    obtain ⟨hx₁₂, hxJ⟩ := Finset.mem_inter.mp hx
    exact (hpencil x hx₁₂).2.trans (hJ x hxJ).2.symm
  have hbase : pencilBase γ₁ γ₂ p₁ p₂ = q₀ := by
    apply hsep _ (pencilBase_mem C hp₁ hp₂) _ hq₀ (S₁ ∩ S₂ ∩ J) hcard
    intro x hx
    obtain ⟨hx₁₂, hxJ⟩ := Finset.mem_inter.mp hx
    exact (hpencil x hx₁₂).1.trans (hJ x hxJ).1.symm
  intro i hi
  exact ⟨(hbase ▸ (hpencil i hi).1 : q₀ i = u₀ i),
    (hdir ▸ (hpencil i hi).2 : q₁ i = u₁ i)⟩

/-! ## Two-cover counting and the collinear boost -/

/-- The union of the pairwise intersections of three finsets. -/
def pairCover (S₁ S₂ S₃ : Finset ι) : Finset ι :=
  (S₁ ∩ S₂) ∪ (S₁ ∩ S₃) ∪ (S₂ ∩ S₃)

/-- **Two-cover bound**: `|S₁| + |S₂| + |S₃| ≤ n + 2·|pairCover|`. -/
theorem card_three_le_card_add_two_mul_pairCover (S₁ S₂ S₃ : Finset ι) :
    S₁.card + S₂.card + S₃.card ≤
      Fintype.card ι + 2 * (pairCover S₁ S₂ S₃).card := by
  have h12 := Finset.card_union_add_card_inter S₁ S₂
  have h123 := Finset.card_union_add_card_inter (S₁ ∪ S₂) S₃
  have hsub1 : S₁ ∩ S₂ ⊆ pairCover S₁ S₂ S₃ := by
    intro x hx
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hx)))
  have hsub2 : (S₁ ∪ S₂) ∩ S₃ ⊆ pairCover S₁ S₂ S₃ := by
    intro x hx
    obtain ⟨hx₁₂, hx₃⟩ := Finset.mem_inter.mp hx
    rcases Finset.mem_union.mp hx₁₂ with hx₁ | hx₂
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inr (Finset.mem_inter.mpr ⟨hx₁, hx₃⟩))))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hx₂, hx₃⟩))
  have hc1 := Finset.card_le_card hsub1
  have hc2 := Finset.card_le_card hsub2
  have huniv : (S₁ ∪ S₂ ∪ S₃).card ≤ Fintype.card ι := Finset.card_le_univ _
  omega

/-- Pointwise pencil solve: a coordinate shared by two collinear witnesses determines the
pencil value as the stack value. -/
theorem pencil_point_solve [NoZeroSMulDivisors F A] {γa γb : F} (hγ : γa ≠ γb)
    {pa pb w₀ w₁ u₀ u₁ : A}
    (ha : pa = u₀ + γa • u₁) (hb : pb = u₀ + γb • u₁)
    (hwa : pa = w₀ + γa • w₁) (hwb : pb = w₀ + γb • w₁) :
    w₀ = u₀ ∧ w₁ = u₁ := by
  have heqa : u₀ + γa • u₁ = w₀ + γa • w₁ := ha.symm.trans hwa
  have heqb : u₀ + γb • u₁ = w₀ + γb • w₁ := hb.symm.trans hwb
  have e1 : γa • (w₁ - u₁) = u₀ - w₀ := by
    rw [smul_sub, sub_eq_sub_iff_add_eq_add, heqa]
    abel
  have e2 : γb • (w₁ - u₁) = u₀ - w₀ := by
    rw [smul_sub, sub_eq_sub_iff_add_eq_add, heqb]
    abel
  have hzero : (γa - γb) • (w₁ - u₁) = 0 := by
    rw [sub_smul, e1, e2, sub_self]
  have hw₁ : w₁ = u₁ := by
    rcases smul_eq_zero.mp hzero with hcoef | hval
    · exact absurd hcoef (sub_ne_zero_of_ne hγ)
    · exact sub_eq_zero.mp hval
  refine ⟨?_, hw₁⟩
  have := e1
  rw [hw₁, sub_self, smul_zero] at this
  exact (sub_eq_zero.mp this.symm).symm

/-- **Collinear boost.**  If the three witness codewords lie on one pencil `(w₀, w₁)`, that
pencil agrees with the stack on the entire two-cover region. -/
theorem collinear_agrees_on_pairCover [NoZeroSMulDivisors F A]
    {γ₁ γ₂ γ₃ : F} (h12 : γ₁ ≠ γ₂) (h13 : γ₁ ≠ γ₃) (h23 : γ₂ ≠ γ₃)
    {S₁ S₂ S₃ : Finset ι} {u₀ u₁ p₁ p₂ p₃ w₀ w₁ : ι → A}
    (hcol₁ : p₁ = w₀ + γ₁ • w₁) (hcol₂ : p₂ = w₀ + γ₂ • w₁)
    (hcol₃ : p₃ = w₀ + γ₃ • w₁)
    (ha₁ : ∀ i ∈ S₁, p₁ i = u₀ i + γ₁ • u₁ i)
    (ha₂ : ∀ i ∈ S₂, p₂ i = u₀ i + γ₂ • u₁ i)
    (ha₃ : ∀ i ∈ S₃, p₃ i = u₀ i + γ₃ • u₁ i) :
    ∀ x ∈ pairCover S₁ S₂ S₃, w₀ x = u₀ x ∧ w₁ x = u₁ x := by
  have hval : ∀ (γ : F) (p : ι → A), p = w₀ + γ • w₁ → ∀ x, p x = w₀ x + γ • w₁ x := by
    intro γ p hp x
    rw [hp]
    rfl
  intro x hx
  rcases Finset.mem_union.mp hx with hx' | hx23
  · rcases Finset.mem_union.mp hx' with hx12 | hx13
    · obtain ⟨hx₁, hx₂⟩ := Finset.mem_inter.mp hx12
      exact pencil_point_solve h12 (ha₁ x hx₁) (ha₂ x hx₂)
        (hval γ₁ p₁ hcol₁ x) (hval γ₂ p₂ hcol₂ x)
    · obtain ⟨hx₁, hx₃⟩ := Finset.mem_inter.mp hx13
      exact pencil_point_solve h13 (ha₁ x hx₁) (ha₃ x hx₃)
        (hval γ₁ p₁ hcol₁ x) (hval γ₃ p₃ hcol₃ x)
  · obtain ⟨hx₂, hx₃⟩ := Finset.mem_inter.mp hx23
    exact pencil_point_solve h23 (ha₂ x hx₂) (ha₃ x hx₃)
      (hval γ₂ p₂ hcol₂ x) (hval γ₃ p₃ hcol₃ x)

/-! ### Fresh-coordinate extraction and the triple pigeonhole

Local copies of the two small combinatorial facts from
`_P1RateQuarterJointWitnessCharge.lean` (that module's olean is not warmed in this lane; the
statements are verbatim and the consolidation pass should dedupe). -/

/-- A known joint explanation on `J` forces every non-joint witness set to contain a
coordinate outside `J`. -/
theorem exists_fresh_of_not_pairJointAgreesOn (C : Set (ι → A))
    {J S : Finset ι} {u₀ u₁ q₀ q₁ : ι → A}
    (hq₀ : q₀ ∈ C) (hq₁ : q₁ ∈ C)
    (hJ : ∀ i ∈ J, q₀ i = u₀ i ∧ q₁ i = u₁ i)
    (hno : ¬ pairJointAgreesOn C S u₀ u₁) :
    ∃ i ∈ S, i ∉ J := by
  by_contra hempty
  apply hno
  refine ⟨q₀, hq₀, q₁, hq₁, fun i hi ↦ hJ i ?_⟩
  by_contra hiJ
  exact hempty ⟨i, hi, hiJ⟩

/-- If the charged family is larger than twice the fresh-coordinate set, some fresh
coordinate receives at least three charges. -/
theorem exists_coordinate_with_three_charges {G : Finset F} {J : Finset ι}
    (charge : { γ // γ ∈ G } → ι)
    (hfresh : ∀ γ, charge γ ∉ J)
    (hbig : 2 * (Fintype.card ι - J.card) < G.card) :
    ∃ i ∈ (Finset.univ \ J),
      2 < ((Finset.univ : Finset { γ // γ ∈ G }).filter
        (fun γ ↦ charge γ = i)).card := by
  classical
  have hmap : ∀ γ ∈ (Finset.univ : Finset { γ // γ ∈ G }),
      charge γ ∈ (Finset.univ \ J) := by
    intro γ _
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hfresh γ⟩
  have htcard : (Finset.univ \ J).card = Fintype.card ι - J.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  apply Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmap
  rw [htcard, Finset.card_univ, Fintype.card_coe]
  simpa only [Nat.mul_comm] using hbig

end ProximityGap.SharedFreshPencil

/-! ## P1 predecessor instantiation -/

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ProximityGap.SharedFreshPencil
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorArithmetic

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! Local mirrors of the predecessor definitions of
`_P1RateQuarterPredecessorGenericSplit.lean` (definitionally equal `abbrev`s; local copies
because that module's olean is not warmed in this lane). -/

/-- One lattice step below the common-factor bad construction. -/
abbrev predecessorThreshold : ℕ := amplifiedThreshold + 1

abbrev predecessorRadiusNumerator : ℕ := N - predecessorThreshold

noncomputable abbrev predecessorDelta : ℝ≥0 :=
  predecessorRadiusNumerator / N

noncomputable abbrev predecessorCode (dom : Fin N ↪ F) : Submodule F (Fin N → F) :=
  ReedSolomon.code dom k

theorem predecessorThreshold_eq : predecessorThreshold = 592794966 := by
  norm_num [predecessorThreshold, amplifiedThreshold, amplifiedCore, m, r, d]

theorem predecessorDelta_le_one : predecessorDelta ≤ 1 := by
  norm_num [predecessorDelta, predecessorRadiusNumerator,
    predecessorThreshold, amplifiedThreshold, amplifiedCore, N, m, r, d]
  rw [div_le_one] <;> norm_num

theorem agreement_mass_eq_predecessorThreshold :
    (1 - predecessorDelta) * (N : ℝ≥0) = predecessorThreshold := by
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_sub predecessorDelta_le_one]
  push_cast
  norm_num [predecessorDelta, predecessorRadiusNumerator,
    predecessorThreshold, amplifiedThreshold, amplifiedCore, N, m, r, d]

/-- The predecessor Reed--Solomon code separates on `k` points. -/
theorem predecessor_sep (dom : Fin N ↪ F) :
    ∀ v ∈ predecessorCode dom, ∀ w ∈ predecessorCode dom, ∀ D : Finset (Fin N),
      k ≤ D.card → (∀ x ∈ D, v x = w x) → v = w := by
  intro v hv w hw D hcard hagree
  rw [show predecessorCode dom = ReedSolomon.code dom k from rfl,
    ReedSolomon.mem_code_iff_exists_polynomial] at hv hw
  obtain ⟨pv, hpv, rfl⟩ := hv
  obtain ⟨pw, hpw, rfl⟩ := hw
  have hzero : pv - pw = 0 := by
    apply eq_zero_of_degree_lt_of_vanishes_on
      (lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hpv hpw)) D hcard
    intro i hi
    have hx := hagree i hi
    simp only [ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk] at hx
    rw [eval_sub, hx, sub_self]
  rw [sub_eq_zero.mp hzero]

/-! ### Exact predecessor arithmetic for the forced structure -/

/-- Threshold witness sets pairwise intersect in at least `2T - N` coordinates. -/
theorem pairwise_inter_floor {S₁ S₂ : Finset (Fin N)}
    (h₁ : predecessorThreshold ≤ S₁.card) (h₂ : predecessorThreshold ≤ S₂.card) :
    111848108 ≤ (S₁ ∩ S₂).card := by
  have hu := Finset.card_union_add_card_inter S₁ S₂
  have huniv : (S₁ ∪ S₂).card ≤ Fintype.card (Fin N) := Finset.card_le_univ _
  rw [Fintype.card_fin] at huniv
  have hT : predecessorThreshold = 592794966 := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  omega

/-- The absorption premise is **not** forced at P1: witnesses can meet the joint set in
fewer than `k` coordinates (`3T ≤ 2N + k - 1`). -/
theorem absorption_not_forced :
    3 * predecessorThreshold ≤ 2 * N + k - 1 := by
  norm_num [predecessorThreshold_eq, N, k]

/-- Collinear two-cover floor: threshold witnesses of a collinear shared triple force joint
agreement on at least `⌈(3T - N)/2⌉ = 352321537` coordinates. -/
theorem collinear_cover_floor {S₁ S₂ S₃ : Finset (Fin N)}
    (h₁ : predecessorThreshold ≤ S₁.card) (h₂ : predecessorThreshold ≤ S₂.card)
    (h₃ : predecessorThreshold ≤ S₃.card) :
    352321537 ≤ (pairCover S₁ S₂ S₃).card := by
  have hcover := card_three_le_card_add_two_mul_pairCover S₁ S₂ S₃
  rw [Fintype.card_fin] at hcover
  have hT : predecessorThreshold = 592794966 := predecessorThreshold_eq
  have hN : N = 1073741824 := by norm_num [N]
  omega

/-- The collinear floor is beyond the unique-decoding degree bound. -/
theorem k_le_collinear_cover_floor : k ≤ 352321537 := by
  norm_num [k]

/-- **Collinear shared triples at P1.**  Three threshold witnesses of distinct bad scalars
whose codewords lie on a single pencil force a joint pair agreeing with the stack on at least
`352321537 ≥ k` coordinates. -/
theorem collinear_triple_forces_high_joint_agreement (dom : Fin N ↪ F)
    {γ₁ γ₂ γ₃ : F} (h12 : γ₁ ≠ γ₂) (h13 : γ₁ ≠ γ₃) (h23 : γ₂ ≠ γ₃)
    {S₁ S₂ S₃ : Finset (Fin N)} {u₀ u₁ p₁ p₂ p₃ w₀ w₁ : Fin N → F}
    (hT₁ : predecessorThreshold ≤ S₁.card) (hT₂ : predecessorThreshold ≤ S₂.card)
    (hT₃ : predecessorThreshold ≤ S₃.card)
    (hw₀ : w₀ ∈ predecessorCode dom) (hw₁ : w₁ ∈ predecessorCode dom)
    (hcol₁ : p₁ = w₀ + γ₁ • w₁) (hcol₂ : p₂ = w₀ + γ₂ • w₁) (hcol₃ : p₃ = w₀ + γ₃ • w₁)
    (ha₁ : ∀ i ∈ S₁, p₁ i = u₀ i + γ₁ • u₁ i)
    (ha₂ : ∀ i ∈ S₂, p₂ i = u₀ i + γ₂ • u₁ i)
    (ha₃ : ∀ i ∈ S₃, p₃ i = u₀ i + γ₃ • u₁ i) :
    ∃ D : Finset (Fin N), 352321537 ≤ D.card ∧
      w₀ ∈ predecessorCode dom ∧ w₁ ∈ predecessorCode dom ∧
      ∀ x ∈ D, w₀ x = u₀ x ∧ w₁ x = u₁ x :=
  ⟨pairCover S₁ S₂ S₃, collinear_cover_floor hT₁ hT₂ hT₃, hw₀, hw₁,
    collinear_agrees_on_pairCover h12 h13 h23 hcol₁ hcol₂ hcol₃ ha₁ ha₂ ha₃⟩

/-! ### The honest open residual and its consumer -/

/-- One bad scalar with a threshold event witness through the coordinate `i`. -/
def SharedWitnessAt (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F) (i : Fin N) (γ : F) : Prop :=
  ∃ S : Finset (Fin N), i ∈ S ∧ predecessorThreshold ≤ S.card ∧
    (∃ w ∈ (predecessorCode dom : Set (Fin N → F)), ∀ e ∈ S, w e = u₀ e + γ • u₁ e) ∧
    ¬ pairJointAgreesOn (predecessorCode dom : Set (Fin N → F)) S u₀ u₁

/-- **Sufficient proposition (REFUTED at P1).**  At the literal P1 predecessor, no fresh
coordinate outside a threshold joint-agreement set carries three distinct bad scalars.
`_P1RateQuarterSharedFreshTripleRefuted.lean` proves its negation for every injective P1 domain;
the definition remains useful for auditing the conditional consumer below. -/
def SharedFreshTripleFree (dom : Fin N ↪ F) : Prop :=
  ∀ (u₀ u₁ : Fin N → F) (J : Finset (Fin N)),
    predecessorThreshold ≤ J.card →
    pairJointAgreesOn (predecessorCode dom : Set (Fin N → F)) J u₀ u₁ →
    ∀ i : Fin N, i ∉ J →
      ¬ ∃ γ₁ γ₂ γ₃ : F, γ₁ ≠ γ₂ ∧ γ₁ ≠ γ₃ ∧ γ₂ ≠ γ₃ ∧
        SharedWitnessAt dom u₀ u₁ i γ₁ ∧
        SharedWitnessAt dom u₀ u₁ i γ₂ ∧
        SharedWitnessAt dom u₀ u₁ i γ₃

/-- **Consumer.**  The residual closes the fixed-witness branch: any stack admitting a
threshold joint-agreement set has at most `N` bad scalars at the predecessor radius. -/
theorem badFamily_card_le_N_of_sharedFreshTripleFree (dom : Fin N ↪ F)
    (hfree : SharedFreshTripleFree dom)
    (u₀ u₁ : Fin N → F) (J : Finset (Fin N))
    (hJcard : predecessorThreshold ≤ J.card)
    (hJ : pairJointAgreesOn (predecessorCode dom : Set (Fin N → F)) J u₀ u₁)
    (G : Finset F)
    (hG : ∀ γ ∈ G, mcaEvent (predecessorCode dom : Set (Fin N → F))
      predecessorDelta u₀ u₁ γ) :
    G.card ≤ N := by
  by_contra hover
  rw [not_le] at hover
  obtain ⟨q₀, hq₀, q₁, hq₁, hJagree⟩ := hJ
  have hpack : ∀ γ : { γ // γ ∈ G }, ∃ S : Finset (Fin N), ∃ i : Fin N,
      i ∈ S ∧ i ∉ J ∧ predecessorThreshold ≤ S.card ∧
      (∃ w ∈ (predecessorCode dom : Set (Fin N → F)),
        ∀ e ∈ S, w e = u₀ e + (γ : F) • u₁ e) ∧
      ¬ pairJointAgreesOn (predecessorCode dom : Set (Fin N → F)) S u₀ u₁ := by
    intro γ
    obtain ⟨S, hScard, hw, hno⟩ := hG γ.1 γ.2
    obtain ⟨i, hiS, hiJ⟩ :=
      exists_fresh_of_not_pairJointAgreesOn
        (predecessorCode dom : Set (Fin N → F)) hq₀ hq₁ hJagree hno
    refine ⟨S, i, hiS, hiJ, ?_, hw, hno⟩
    rw [Fintype.card_fin, agreement_mass_eq_predecessorThreshold] at hScard
    exact_mod_cast hScard
  choose Sf idx hmem hnotJ hcard hline hnojoint using hpack
  have hbig : 2 * (Fintype.card (Fin N) - J.card) < G.card := by
    rw [Fintype.card_fin]
    have hT := predecessorThreshold_eq
    have hN : N = 1073741824 := by norm_num [N]
    omega
  obtain ⟨i, hiMem, hcount⟩ :=
    exists_coordinate_with_three_charges idx hnotJ hbig
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hcount
  have hia : idx a = i := (Finset.mem_filter.mp ha).2
  have hib : idx b = i := (Finset.mem_filter.mp hb).2
  have hic : idx c = i := (Finset.mem_filter.mp hc).2
  have hiJ : i ∉ J := (Finset.mem_sdiff.mp hiMem).2
  apply hfree u₀ u₁ J hJcard ⟨q₀, hq₀, q₁, hq₁, hJagree⟩ i hiJ
  refine ⟨a.1, b.1, c.1,
    fun h ↦ hab (Subtype.ext h), fun h ↦ hac (Subtype.ext h),
    fun h ↦ hbc (Subtype.ext h), ?_, ?_, ?_⟩
  · exact ⟨Sf a, hia ▸ hmem a, hcard a, hline a, hnojoint a⟩
  · exact ⟨Sf b, hib ▸ hmem b, hcard b, hline b, hnojoint b⟩
  · exact ⟨Sf c, hic ▸ hmem c, hcard c, hline c, hnojoint c⟩

end ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate

/-! ## Realizability: the shared-fresh triple exists in Reed--Solomon codes

The exact `RS[8,2]/F_11` certificate produced by
`scripts/probes/probe_rate_quarter_p1_shared_fresh_coordinate.py`.  It refutes any hoped-for
code-generic impossibility of the non-absorbed shared-fresh triple. -/

namespace ArkLib.ProximityGap.Frontier.SharedFreshRealizabilityF11

open ProximityGap.SharedFreshPencil

abbrev F11 := ZMod 11

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- The eight-point evaluation domain `0,…,7` in `F_11`. -/
def domainValues : Fin 8 → F11 := ![0, 1, 2, 3, 4, 5, 6, 7]

def dom : Fin 8 ↪ F11 := ⟨domainValues, by decide⟩

/-- First received row. -/
def u0 : Fin 8 → F11 := ![1, 3, 5, 7, 1, 10, 2, 3]

/-- Second received row. -/
def u1 : Fin 8 → F11 := ![3, 4, 5, 6, 1, 8, 10, 7]

def u : WordStack F11 (Fin 2) (Fin 8) := ![u0, u1]

@[simp] theorem u_zero : u 0 = u0 := rfl
@[simp] theorem u_one : u 1 = u1 := rfl

/-- The known joint pair: `q₀ = 1 + 2X`, `q₁ = 3 + X`. -/
noncomputable def q0poly : F11[X] := C 1 + C 2 * X
noncomputable def q1poly : F11[X] := C 3 + C 1 * X

/-- The three witness codewords `4 + 5X`, `10 + X`, `3 + 3X`. -/
noncomputable def linePoly : Fin 3 → F11[X] := ![
  C 4 + C 5 * X, C 10 + C 1 * X, C 3 + C 3 * X]

/-- The three bad scalars. -/
def gamma : Fin 3 → F11 := ![1, 2, 3]

/-- The three witness sets, all containing the shared fresh coordinate `4`. -/
def witness : Fin 3 → Finset (Fin 8) := ![
  {0, 4, 5, 6}, {1, 4, 5, 7}, {2, 4, 6, 7}]

/-- The known joint set. -/
def J : Finset (Fin 8) := {0, 1, 2, 3}

/-- Row-certificate interpolants for the non-jointness proofs (constants of `C c₀ + C c₁·X`):
`1`, `3X`, `9 + 9X`, plus `q₀` itself for the non-absorption certificate. -/
noncomputable def rowCert : Fin 3 → F11[X] := ![
  C 1 + C 0 * X, C 0 + C 3 * X, C 9 + C 9 * X]

/-- The interpolation core of each row certificate. -/
def rowCore : Fin 3 → Finset (Fin 8) := ![{0, 4}, {1, 4}, {2, 4}]

/-- The mismatch coordinate of each row certificate. -/
def rowMismatch : Fin 3 → Fin 8 := ![5, 5, 6]

/-! ### Degree bounds -/

theorem affine_natDegree_le_one (c0 c1 : F11) :
    (C c0 + C c1 * X).natDegree ≤ 1 := by
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_C c0).le.trans (by omega)
  · exact natDegree_mul_le.trans (by simp)

theorem degree_lt_two_of_natDegree_le_one {p : F11[X]}
    (hp : p.natDegree ≤ 1) : p.degree < (2 : ℕ) := by
  by_cases hzero : p = 0
  · rw [hzero]
    exact WithBot.bot_lt_coe 2
  · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mp (by omega)

theorem affine_degree_lt_two (c0 c1 : F11) :
    (C c0 + C c1 * X).degree < ((2 : ℕ) : WithBot ℕ) :=
  degree_lt_two_of_natDegree_le_one (affine_natDegree_le_one c0 c1)

theorem linePoly_degree_lt_two (j : Fin 3) : (linePoly j).degree < (2 : ℕ) := by
  fin_cases j <;> exact affine_degree_lt_two _ _

theorem rowCert_degree_lt_two (j : Fin 3) : (rowCert j).degree < (2 : ℕ) := by
  fin_cases j <;> exact affine_degree_lt_two _ _

theorem q0poly_degree_lt_two : q0poly.degree < (2 : ℕ) := affine_degree_lt_two 1 2
theorem q1poly_degree_lt_two : q1poly.degree < (2 : ℕ) := affine_degree_lt_two 3 1

/-! ### Closed finite-field certificate checks -/

set_option linter.flexible false in
/-- The joint pair explains the stack on `J`. -/
theorem joint_pair_agreement (e : Fin 8) (he : e ∈ J) :
    q0poly.eval (dom e) = u0 e ∧ q1poly.eval (dom e) = u1 e := by
  fin_cases e <;> simp [J] at he ⊢ <;>
    simp [q0poly, q1poly, dom, domainValues, u0, u1] <;> decide

set_option linter.flexible false in
/-- Each witness codeword agrees with its line on its witness set. -/
theorem witness_agreement (j : Fin 3) (e : Fin 8) (he : e ∈ witness j) :
    (linePoly j).eval (dom e) = u0 e + gamma j * u1 e := by
  fin_cases j <;> fin_cases e <;> simp [witness] at he ⊢ <;>
    simp [linePoly, gamma, dom, domainValues, u0, u1] <;> decide

set_option linter.flexible false in
/-- Each row certificate matches `u0` on its core. -/
theorem rowCert_core_agreement (j : Fin 3) (e : Fin 8) (he : e ∈ rowCore j) :
    (rowCert j).eval (dom e) = u0 e := by
  fin_cases j <;> fin_cases e <;> simp [rowCore] at he ⊢ <;>
    simp [rowCert, dom, domainValues, u0] <;> decide

set_option linter.flexible false in
/-- Each row certificate mismatches `u0` at its mismatch coordinate. -/
theorem rowCert_mismatch (j : Fin 3) :
    (rowCert j).eval (dom (rowMismatch j)) ≠ u0 (rowMismatch j) := by
  fin_cases j <;>
    simp [rowCert, rowMismatch, dom, domainValues, u0] <;> decide

/-! ### Non-jointness from the first-row certificates -/

/-- A single unexplainable row on `S` forbids a joint explanation on `S`. -/
theorem not_pairJointAgreesOn_of_firstRow
    (S D : Finset (Fin 8)) (hDS : D ⊆ S) (e : Fin 8) (heS : e ∈ S)
    (L : F11[X]) (hL : L.degree < (2 : ℕ)) (hDcard : 2 ≤ D.card)
    (hcore : ∀ i ∈ D, L.eval (dom i) = u0 i)
    (hmis : L.eval (dom e) ≠ u0 e) :
    ¬ _root_.ProximityGap.pairJointAgreesOn
      ((ReedSolomon.code dom 2 : Submodule F11 (Fin 8 → F11)) :
        Set (Fin 8 → F11)) S u0 u1 := by
  rintro ⟨v0, hv0, v1, hv1, hagree⟩
  change v0 ∈ ReedSolomon.code dom 2 at hv0
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hv0
  obtain ⟨p0, hp0deg, hv0⟩ := hv0
  have hp0eq : p0 = L := by
    apply sub_eq_zero.mp
    apply eq_zero_of_degree_lt_of_vanishes_on
      (lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hp0deg hL))
      D hDcard
    intro i hi
    have hreceived := (hagree i (hDS hi)).1
    have hpoly : p0.eval (dom i) = u0 i := by
      rw [hv0] at hreceived
      simpa only [ReedSolomon.evalOnPoints, LinearMap.coe_mk,
        AddHom.coe_mk, Function.comp_apply] using hreceived
    rw [eval_sub, hpoly, hcore i hi, sub_self]
  apply hmis
  have hfresh := (hagree e heS).1
  rw [hv0, hp0eq] at hfresh
  simpa only [ReedSolomon.evalOnPoints, LinearMap.coe_mk,
    AddHom.coe_mk, Function.comp_apply] using hfresh

theorem rowCore_subset_witness (j : Fin 3) : rowCore j ⊆ witness j := by
  fin_cases j <;> decide

theorem rowMismatch_mem_witness (j : Fin 3) : rowMismatch j ∈ witness j := by
  fin_cases j <;> decide

theorem rowCore_card (j : Fin 3) : 2 ≤ (rowCore j).card := by
  fin_cases j <;> decide

/-- No joint pair explains the stack on any of the three witness sets. -/
theorem witness_not_joint (j : Fin 3) :
    ¬ _root_.ProximityGap.pairJointAgreesOn
      ((ReedSolomon.code dom 2 : Submodule F11 (Fin 8 → F11)) :
        Set (Fin 8 → F11)) (witness j) u0 u1 :=
  not_pairJointAgreesOn_of_firstRow (witness j) (rowCore j)
    (rowCore_subset_witness j) (rowMismatch j) (rowMismatch_mem_witness j)
    (rowCert j) (rowCert_degree_lt_two j) (rowCore_card j)
    (rowCert_core_agreement j) (rowCert_mismatch j)

/-! ### Literal MCA events at radius `1/2` -/

theorem half_mass_eight :
    ((1 : ℝ≥0) - (1 / 2 : ℝ≥0)) * (Fintype.card (Fin 8) : ℝ≥0) = 4 := by
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_sub (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)]
  push_cast [Fintype.card_fin]
  norm_num

theorem witness_card (j : Fin 3) : (witness j).card = 4 := by
  fin_cases j <;> decide

/-- The explicit decode certificate for the `j`-th scalar. -/
noncomputable def decode (j : Fin 3) :
    CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.McaDecode
      dom 2 (1 / 2) u (gamma j) where
  S := witness j
  P := linePoly j
  hdeg := linePoly_degree_lt_two j
  hcard := by
    rw [witness_card, half_mass_eight]
    norm_num
  hagree := by
    intro e he
    simpa only [u_zero, u_one, smul_eq_mul] using witness_agreement j e he
  hnjp := by
    simpa only [u_zero, u_one] using witness_not_joint j

theorem mcaEvent_index (j : Fin 3) :
    _root_.ProximityGap.mcaEvent
      ((ReedSolomon.code dom 2 : Submodule F11 (Fin 8 → F11)) :
        Set (Fin 8 → F11)) (1 / 2) u0 u1 (gamma j) := by
  have := (decode j).mcaEvent
  simpa only [u_zero, u_one] using this

/-! ### The joint set, the shared fresh coordinate, and non-absorption -/

theorem joint_on_J :
    _root_.ProximityGap.pairJointAgreesOn
      ((ReedSolomon.code dom 2 : Submodule F11 (Fin 8 → F11)) :
        Set (Fin 8 → F11)) J u0 u1 := by
  refine ⟨fun e ↦ q0poly.eval (dom e),
    ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval q0poly
      q0poly_degree_lt_two (fun i ↦ rfl),
    fun e ↦ q1poly.eval (dom e),
    ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval q1poly
      q1poly_degree_lt_two (fun i ↦ rfl), ?_⟩
  intro e he
  exact joint_pair_agreement e he

theorem J_card : J.card = 4 := by decide

theorem shared_mem_witness (j : Fin 3) : (4 : Fin 8) ∈ witness j := by
  fin_cases j <;> decide

theorem shared_not_mem_J : (4 : Fin 8) ∉ J := by decide

theorem J_subset_insert : J ⊆ insert (4 : Fin 8) J :=
  Finset.subset_insert _ _

set_option linter.flexible false in
theorem q0poly_core_agreement : ∀ i ∈ ({0, 1} : Finset (Fin 8)),
    q0poly.eval (dom i) = u0 i := by
  intro i hi
  fin_cases i <;> simp at hi ⊢ <;>
    simp [q0poly, dom, domainValues, u0]
  all_goals decide

theorem q0poly_mismatch_at_shared :
    q0poly.eval (dom (4 : Fin 8)) ≠ u0 (4 : Fin 8) := by
  simp [q0poly, dom, domainValues, u0]
  decide

/-- **Non-absorption.**  No joint pair explains the stack on `J ∪ {4}`: the shared fresh
coordinate lies outside the maximal joint-agreement set of every explaining pair. -/
theorem not_joint_on_insert_shared :
    ¬ _root_.ProximityGap.pairJointAgreesOn
      ((ReedSolomon.code dom 2 : Submodule F11 (Fin 8 → F11)) :
        Set (Fin 8 → F11)) (insert (4 : Fin 8) J) u0 u1 :=
  not_pairJointAgreesOn_of_firstRow (insert (4 : Fin 8) J) {0, 1}
    (by decide) (4 : Fin 8) (Finset.mem_insert_self _ _)
    q0poly q0poly_degree_lt_two (by decide)
    q0poly_core_agreement q0poly_mismatch_at_shared

theorem gammas_distinct :
    gamma 0 ≠ gamma 1 ∧ gamma 0 ≠ gamma 2 ∧ gamma 1 ≠ gamma 2 := by decide

/-- **Realizability of the non-absorbed shared-fresh triple.**  The exact analogue (at
generic small parameters) of the configuration the `SharedFreshTripleFree` residual forbids
at P1 exists in a Reed--Solomon code: three distinct bad scalars, one shared fresh coordinate
outside a threshold joint set, threshold-size witnesses, and no absorption.  Any proof of the
P1 residual must therefore use the P1-specific counting, not only the clauses and linearity. -/
theorem sharedFreshTriple_realizable :
    ∃ (i : Fin 8) (J' : Finset (Fin 8)) (γ₁ γ₂ γ₃ : F11),
      i ∉ J' ∧ 4 ≤ J'.card ∧
      _root_.ProximityGap.pairJointAgreesOn
        ((ReedSolomon.code dom 2 : Submodule F11 (Fin 8 → F11)) :
          Set (Fin 8 → F11)) J' u0 u1 ∧
      ¬ _root_.ProximityGap.pairJointAgreesOn
        ((ReedSolomon.code dom 2 : Submodule F11 (Fin 8 → F11)) :
          Set (Fin 8 → F11)) (insert i J') u0 u1 ∧
      γ₁ ≠ γ₂ ∧ γ₁ ≠ γ₃ ∧ γ₂ ≠ γ₃ ∧
      (∀ γ, γ = γ₁ ∨ γ = γ₂ ∨ γ = γ₃ →
        _root_.ProximityGap.mcaEvent
          ((ReedSolomon.code dom 2 : Submodule F11 (Fin 8 → F11)) :
            Set (Fin 8 → F11)) (1 / 2) u0 u1 γ) ∧
      (∀ jdx : Fin 3, ∃ S : Finset (Fin 8), i ∈ S ∧ 4 ≤ S.card ∧
        (∃ w ∈ ((ReedSolomon.code dom 2 : Submodule F11 (Fin 8 → F11)) :
          Set (Fin 8 → F11)), ∀ e ∈ S, w e = u0 e + gamma jdx * u1 e) ∧
        ¬ _root_.ProximityGap.pairJointAgreesOn
          ((ReedSolomon.code dom 2 : Submodule F11 (Fin 8 → F11)) :
            Set (Fin 8 → F11)) S u0 u1) := by
  refine ⟨4, J, gamma 0, gamma 1, gamma 2,
    shared_not_mem_J, le_of_eq J_card.symm, joint_on_J, not_joint_on_insert_shared,
    gammas_distinct.1, gammas_distinct.2.1, gammas_distinct.2.2, ?_, ?_⟩
  · rintro γ (rfl | rfl | rfl)
    · exact mcaEvent_index 0
    · exact mcaEvent_index 1
    · exact mcaEvent_index 2
  · intro jdx
    refine ⟨witness jdx, shared_mem_witness jdx, le_of_eq (witness_card jdx).symm,
      ⟨fun e ↦ (linePoly jdx).eval (dom e),
        ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval (linePoly jdx)
          (linePoly_degree_lt_two jdx) (fun i ↦ rfl),
        fun e he ↦ witness_agreement jdx e he⟩,
      witness_not_joint jdx⟩

end ArkLib.ProximityGap.Frontier.SharedFreshRealizabilityF11

/-! ## Axiom audit -/

open ProximityGap.SharedFreshPencil
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.SharedFreshRealizabilityF11

#print axioms pencil_reproduces_second
#print axioms pairJointAgreesOn_inter
#print axioms witness_not_subset
#print axioms shared_values_distinct
#print axioms pencil_absorption
#print axioms card_three_le_card_add_two_mul_pairCover
#print axioms collinear_agrees_on_pairCover
#print axioms predecessor_sep
#print axioms pairwise_inter_floor
#print axioms absorption_not_forced
#print axioms collinear_cover_floor
#print axioms collinear_triple_forces_high_joint_agreement
#print axioms badFamily_card_le_N_of_sharedFreshTripleFree
#print axioms mcaEvent_index
#print axioms joint_on_J
#print axioms not_joint_on_insert_shared
#print axioms sharedFreshTriple_realizable
