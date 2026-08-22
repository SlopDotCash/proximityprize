/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSharedFreshCoordinate
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCanonicalCodeBridge

/-!
# `SharedFreshTripleFree` is FALSE at the literal P1 predecessor

Successor of `_P1RateQuarterSharedFreshCoordinate.lean` and
`_P1RateQuarterNonCollinearTriple.lean`.  Those files reduced the fixed-witness branch of the
P1 predecessor pin to the residual `SharedFreshTripleFree` (no fresh coordinate outside a
threshold joint set carries three distinct bad scalars) and showed the shared-fresh triple is
realizable at the P1 inequality shape.  This file kernel-checks the predicted lift: on the
literal smooth domain `μ_{2^30} ⊂ F_P` the residual is **false**.

The certificate is purely generator-symbolic.  With `ω = g^(2^26)` of order `16`
(`y = x^(2^26)` folds `μ_{2^30}` onto `μ_16`) and residue classes `t = e mod 16` of the power
enumeration `e ↦ g^e`:

* `J` = the nine cosets `{0,1,2,3,4,8,9,10,11}`, `|J| = 9·2^26 = 603979776 ≥ T = 592794966`;
* `u₀(e) = (g^e)^(2^27)`, `u₁(e) = 1` on the seven fresh cosets `{5,6,7,12,13,14,15}`, and
  `u₀ = u₁ = 0` on `J` — so the pair `(0,0)` jointly explains `J`;
* bad scalars `γ_j = -ω^(2j)` for `j = 0,1,2` (distinct since `ω` has order `16`);
* witness codewords `p_j = X^(2^27) + C γ_j` (degree `2^27 < k = 2^28`), agreeing with the
  line on `S_j` = the seven fresh cosets plus the two cosets `{j, j+8}` (nine cosets `≥ T`):
  on the fresh cosets by construction, on `{j, j+8}` because `ω^(2t) = -γ_j` exactly there;
* non-jointness: any degree-`< k` explanation of the `u₁` row agrees with the constant-`1`
  codeword on the `7·2^26 ≥ k` fresh-part points, hence equals it, but `u₁ = 0` on the
  `J`-part anchor of `S_j`;
* the fresh coordinate `i = 5` (residue `5`) lies in every `S_j` and outside `J`.

**Consequence (honest):** the fixed-witness charge branch is dead at the canonical P1 domain.
`badFamily_card_le_N_of_sharedFreshTripleFree` can never be instantiated there: three bad
scalars *can* share one fresh coordinate outside a threshold joint set.  The lane successor is
counting arguments that tolerate shared triples — e.g. bounding the number of fresh
coordinates that can carry triples, or a global pencil count at pairwise agreement `2T - N` —
not per-coordinate escape charges.

The refutation does **not** produce more than `N` bad scalars and does not touch the
predecessor count itself: the constructed stack exhibits exactly three bad scalars, and the
operational bracket `3/8 ≤ mcaDeltaStar ≤ 43/96 + 1/(3·2^30) < 1/2` is unchanged.

Executable certificate: `scripts/probes/probe_rate_quarter_p1_shared_fresh_triple_refuted.py`
(full enumeration at the mid-scale image `μ_256 = F_257^*`, plus every coset-level identity
at the literal `P`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshTripleP1Refuted

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleConstruction
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open _root_.ProximityGap.KKH26RegimeSplit

local instance localInstance_P1RateQuarterSharedFreshTripleP1Refuted_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterSharedFreshTripleP1Refuted_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## Residue-class cosets of the power enumeration and their cardinalities -/

/-- The union of the residue-`I` cosets of the index enumeration. -/
def residueSet (I : Finset ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun e => (e : ℕ) % 16 ∈ I)

theorem mem_residueSet_iff (I : Finset ℕ) (e : Fin N) :
    e ∈ residueSet I ↔ (e : ℕ) % 16 ∈ I := by
  rw [residueSet, Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩

theorem residueSet_mono {I I' : Finset ℕ} (h : I ⊆ I') :
    residueSet I ⊆ residueSet I' := by
  intro e he
  rw [mem_residueSet_iff] at he ⊢
  exact h he

theorem fin_N_lt (e : Fin N) : (e : ℕ) < 1073741824 := by
  have := e.isLt
  have hN : N = 1073741824 := by norm_num [N]
  omega

/-- Each single residue class has exactly `2^26` coordinates. -/
theorem card_singleResidue (r : ℕ) (hr : r < 16) :
    (Finset.univ.filter (fun e : Fin N => (e : ℕ) % 16 = r)).card = 2 ^ 26 := by
  have hcard : (Finset.univ : Finset (Fin (2 ^ 26))).card = 2 ^ 26 := by
    simp
  rw [← hcard]
  apply Finset.card_nbij'
    (fun e : Fin N => (⟨(e : ℕ) / 16, by
      have := fin_N_lt e
      omega⟩ : Fin (2 ^ 26)))
    (fun s : Fin (2 ^ 26) => (⟨16 * (s : ℕ) + r, by
      have := s.isLt
      have h26 : (2 : ℕ) ^ 26 = 67108864 := by norm_num
      have hN : N = 1073741824 := by norm_num [N]
      omega⟩ : Fin N))
  · intro e he
    simp
  · intro s hs
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    omega
  · intro e he
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at he
    apply Fin.ext
    simp only
    omega
  · intro s hs
    apply Fin.ext
    simp only
    omega

/-- **Coset counting.**  A union of residue classes below `16` has cardinality
`(number of classes) · 2^26`. -/
theorem residueSet_card (I : Finset ℕ) (hI : ∀ r ∈ I, r < 16) :
    (residueSet I).card = I.card * 2 ^ 26 := by
  classical
  have hsplit : residueSet I =
      I.biUnion (fun r => Finset.univ.filter (fun e : Fin N => (e : ℕ) % 16 = r)) := by
    ext e
    rw [mem_residueSet_iff, Finset.mem_biUnion]
    constructor
    · intro h
      exact ⟨(e : ℕ) % 16, h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    · rintro ⟨r, hr, he⟩
      rw [Finset.mem_filter] at he
      rw [he.2]
      exact hr
  rw [hsplit, Finset.card_biUnion]
  · have hsum : ∑ r ∈ I,
        (Finset.univ.filter (fun e : Fin N => (e : ℕ) % 16 = r)).card
          = ∑ _r ∈ I, 2 ^ 26 :=
      Finset.sum_congr rfl (fun r hr => card_singleResidue r (hI r hr))
    rw [hsum, Finset.sum_const, smul_eq_mul]
  · intro r hr r' hr' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e he he'
    rw [Finset.mem_filter] at he he'
    exact hne (he.2.symm.trans he'.2)

/-! ## The symbolic construction -/

/-- The order-`16` fold generator `ω = g^(2^26)`. -/
noncomputable def w (g : F) : F := g ^ ((2 : ℕ) ^ 26)

theorem w_pow_sixteen (g : F) (hg : orderOf g = 2 ^ 30) : w g ^ (16 : ℕ) = 1 := by
  rw [w, ← pow_mul]
  have h1 : (2 : ℕ) ^ 26 * 16 = 2 ^ 30 := by norm_num
  rw [h1, ← hg]
  exact pow_orderOf_eq_one g

theorem w_pow_ne_one (g : F) (hg : orderOf g = 2 ^ 30)
    {s : ℕ} (hs : 0 < s) (hs' : s < 16) : w g ^ s ≠ 1 := by
  intro h
  rw [w, ← pow_mul] at h
  have hdvd := orderOf_dvd_of_pow_eq_one h
  rw [hg] at hdvd
  have hle := Nat.le_of_dvd (by positivity) hdvd
  have h30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
  have h26 : (2 : ℕ) ^ 26 = 67108864 := by norm_num
  omega

theorem w_ne_zero (g : F) (hg0 : g ≠ 0) : w g ≠ 0 := pow_ne_zero _ hg0

/-- The exponent fold: `(g^e)^(2^27) = ω^(2·(e mod 16))`. -/
theorem pow_fold (g : F) (hg : orderOf g = 2 ^ 30) (e : ℕ) :
    (g ^ e) ^ ((2 : ℕ) ^ 27) = w g ^ (2 * (e % 16)) := by
  have h1 : g ^ ((2 : ℕ) ^ 30) = 1 := by
    rw [← hg]
    exact pow_orderOf_eq_one g
  have hdecomp : e * 2 ^ 27 = 2 ^ 30 * (2 * (e / 16)) + 2 ^ 26 * (2 * (e % 16)) := by
    have h30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
    have h27 : (2 : ℕ) ^ 27 = 134217728 := by norm_num
    have h26 : (2 : ℕ) ^ 26 = 67108864 := by norm_num
    omega
  calc
    (g ^ e) ^ ((2 : ℕ) ^ 27) = g ^ (e * 2 ^ 27) := by rw [← pow_mul]
    _ = (g ^ ((2 : ℕ) ^ 30)) ^ (2 * (e / 16)) *
          (g ^ ((2 : ℕ) ^ 26)) ^ (2 * (e % 16)) := by
        rw [← pow_mul, ← pow_mul, ← pow_add, hdecomp]
    _ = w g ^ (2 * (e % 16)) := by rw [h1, one_pow, one_mul, w]

/-- The joint residue classes. -/
def JIdx : Finset ℕ := {0, 1, 2, 3, 4, 8, 9, 10, 11}

/-- The fresh residue classes. -/
def OIdx : Finset ℕ := {5, 6, 7, 12, 13, 14, 15}

/-- The witness residue classes for the three bad scalars. -/
def SIdx : Fin 3 → Finset ℕ := ![
  {0, 5, 6, 7, 8, 12, 13, 14, 15},
  {1, 5, 6, 7, 9, 12, 13, 14, 15},
  {2, 5, 6, 7, 10, 12, 13, 14, 15}]

/-- The three bad scalars `γ_j = -ω^(2j)`. -/
noncomputable def gam (g : F) (j : Fin 3) : F := -(w g ^ (2 * (j : ℕ)))

/-- First received row: `x^(2^27)` on the fresh cosets, `0` on the joint cosets. -/
noncomputable def u0 (g : F) : Fin N → F :=
  fun e => if (e : ℕ) % 16 ∈ OIdx then (g ^ (e : ℕ)) ^ ((2 : ℕ) ^ 27) else 0

/-- Second received row: `1` on the fresh cosets, `0` on the joint cosets. -/
noncomputable def u1 : Fin N → F :=
  fun e => if (e : ℕ) % 16 ∈ OIdx then 1 else 0

/-- The witness codewords as functions. -/
noncomputable def pfun (g : F) (j : Fin 3) : Fin N → F :=
  fun e => (g ^ (e : ℕ)) ^ ((2 : ℕ) ^ 27) + gam g j

def Jset : Finset (Fin N) := residueSet JIdx

def Sset (j : Fin 3) : Finset (Fin N) := residueSet (SIdx j)

/-- The shared fresh coordinate: index `5`, residue `5 ∈ OIdx`. -/
def ifresh : Fin N := ⟨5, by norm_num [N]⟩

/-! ### Scalars are pairwise distinct -/

theorem w_sq_ne_w_four (g : F) (hg : orderOf g = 2 ^ 30) (hg0 : g ≠ 0) :
    w g ^ 2 ≠ w g ^ 4 := by
  intro heq
  have hz : w g ^ 2 * (w g ^ 2 - 1) = 0 := by
    have hmul : w g ^ 2 * w g ^ 2 = w g ^ 4 := by ring
    rw [mul_sub, mul_one, hmul, ← heq, sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · exact pow_ne_zero 2 (w_ne_zero g hg0) h
  · exact w_pow_ne_one g hg (by norm_num) (by norm_num) (sub_eq_zero.mp h)

theorem gam_distinct (g : F) (hg : orderOf g = 2 ^ 30) (hg0 : g ≠ 0) :
    gam g 0 ≠ gam g 1 ∧ gam g 0 ≠ gam g 2 ∧ gam g 1 ≠ gam g 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [gam]
  · intro h
    apply w_pow_ne_one g hg (s := 2) (by norm_num) (by norm_num)
    simpa using h.symm
  · intro h
    apply w_pow_ne_one g hg (s := 4) (by norm_num) (by norm_num)
    simpa using h.symm
  · intro h
    apply w_sq_ne_w_four g hg hg0
    simpa using h

/-! ### Cardinalities -/

theorem JIdx_card : JIdx.card = 9 := by decide

theorem Jset_card_ge : predecessorThreshold ≤ Jset.card := by
  rw [Jset, residueSet_card JIdx (by decide), JIdx_card, predecessorThreshold_eq]
  norm_num

theorem SIdx_card (j : Fin 3) : (SIdx j).card = 9 := by
  fin_cases j <;> decide

theorem SIdx_bound (j : Fin 3) : ∀ r ∈ SIdx j, r < 16 := by
  fin_cases j <;> decide

theorem Sset_card_ge (j : Fin 3) : predecessorThreshold ≤ (Sset j).card := by
  rw [Sset, residueSet_card (SIdx j) (SIdx_bound j), SIdx_card, predecessorThreshold_eq]
  norm_num

/-! ### The joint pair `(0,0)` on `J` -/

theorem JIdx_not_OIdx : ∀ r ∈ JIdx, r ∉ OIdx := by decide

theorem joint_on_Jset (g : F) (dom : Fin N ↪ F) :
    pairJointAgreesOn
      (predecessorCode dom : Set (Fin N → F)) Jset (u0 g) u1 := by
  refine ⟨0, ?_, 0, ?_, ?_⟩
  · exact Submodule.zero_mem _
  · exact Submodule.zero_mem _
  · intro e he
    have hres := (mem_residueSet_iff JIdx e).mp he
    have hO : (e : ℕ) % 16 ∉ OIdx := JIdx_not_OIdx _ hres
    constructor
    · simp [u0, hO]
    · simp [u1, hO]

/-! ### Line agreement of the witness codewords -/

theorem OIdx_subset_SIdx (j : Fin 3) : OIdx ⊆ SIdx j := by
  fin_cases j <;> decide

/-- On a non-fresh witness residue `t`, the fold value kills the scalar:
`ω^(2t) + γ_j = 0`. -/
theorem line_identity (g : F) (hg : orderOf g = 2 ^ 30) (j : Fin 3) (t : ℕ)
    (ht : t < 16) (hmem : t ∈ SIdx j) (hO : t ∉ OIdx) :
    w g ^ (2 * t) + gam g j = 0 := by
  have h16 := w_pow_sixteen g hg
  have hshift : ∀ s : ℕ, w g ^ (16 + s) = w g ^ s := by
    intro s
    rw [pow_add, h16, one_mul]
  fin_cases j <;>
    interval_cases t <;>
      first
        | exact absurd hmem (by decide)
        | exact absurd (by decide) hO
        | (rw [show (2 * 8 : ℕ) = 16 + 2 * 0 by norm_num, hshift]; simp [gam])
        | (rw [show (2 * 9 : ℕ) = 16 + 2 * 1 by norm_num, hshift]; simp [gam])
        | (rw [show (2 * 10 : ℕ) = 16 + 2 * 2 by norm_num, hshift]; simp [gam])
        | (simp [gam])

theorem agreement (g : F) (hg : orderOf g = 2 ^ 30) (j : Fin 3) :
    ∀ e ∈ Sset j, pfun g j e = u0 g e + gam g j • u1 e := by
  intro e he
  have hres := (mem_residueSet_iff (SIdx j) e).mp he
  by_cases hO : (e : ℕ) % 16 ∈ OIdx
  · simp [pfun, u0, u1, hO, smul_eq_mul, mul_one]
  · have hz := line_identity g hg j ((e : ℕ) % 16)
      (Nat.mod_lt _ (by norm_num)) hres hO
    simp only [pfun, u0, u1, hO, if_false, smul_eq_mul, mul_zero, add_zero]
    rw [pow_fold g hg]
    exact hz

/-! ### Codeword membership -/

theorem pfun_mem (g : F) (hg : orderOf g = 2 ^ 30) (hg0 : g ≠ 0) (j : Fin 3) :
    pfun g j ∈ predecessorCode (powDomain g hg hg0) := by
  refine ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval
    ((Polynomial.X : F[X]) ^ ((2 : ℕ) ^ 27) + Polynomial.C (gam g j)) ?_ ?_
  · rw [Polynomial.degree_X_pow_add_C (by norm_num : 0 < (2 : ℕ) ^ 27) (gam g j)]
    exact_mod_cast (by norm_num [k] : (2 : ℕ) ^ 27 < k)
  · intro i
    show (g ^ ((i : Fin N) : ℕ)) ^ ((2 : ℕ) ^ 27) + gam g j = _
    rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C]
    rfl

theorem onefun_mem (dom : Fin N ↪ F) :
    (fun _ : Fin N => (1 : F)) ∈ predecessorCode dom := by
  apply ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval (Polynomial.C 1)
  · calc (C (1 : F)).degree ≤ 0 := Polynomial.degree_C_le
      _ < (k : WithBot ℕ) := by exact_mod_cast (by norm_num [k] : (0 : ℕ) < k)
  · intro i
    simp

/-! ### Non-jointness via the pinned second row -/

/-- The `J`-part anchor of each witness set: index `j`, residue `j ∉ OIdx`. -/
def anchor (j : Fin 3) : Fin N :=
  ⟨(j : ℕ), lt_of_lt_of_le j.isLt (by norm_num [N])⟩

theorem anchor_mem_Sset (j : Fin 3) : anchor j ∈ Sset j := by
  rw [Sset, mem_residueSet_iff]
  fin_cases j <;> decide

theorem anchor_not_OIdx (j : Fin 3) : ((anchor j : Fin N) : ℕ) % 16 ∉ OIdx := by
  fin_cases j <;> decide

theorem Opart_card_ge : k ≤ (residueSet OIdx).card := by
  rw [residueSet_card OIdx (by decide)]
  have : OIdx.card = 7 := by decide
  rw [this]
  norm_num [k]

theorem not_joint_on_Sset (g : F) (hg : orderOf g = 2 ^ 30) (hg0 : g ≠ 0) (j : Fin 3) :
    ¬ pairJointAgreesOn
      (predecessorCode (powDomain g hg hg0) : Set (Fin N → F)) (Sset j) (u0 g) u1 := by
  rintro ⟨v0, hv0, v1, hv1, hagree⟩
  have hOsub : residueSet OIdx ⊆ Sset j :=
    residueSet_mono (OIdx_subset_SIdx j)
  have hv1eq : v1 = fun _ : Fin N => (1 : F) := by
    apply predecessor_sep (powDomain g hg hg0) v1 hv1 _
      (onefun_mem (powDomain g hg hg0)) (residueSet OIdx) Opart_card_ge
    intro x hx
    have hxO := (mem_residueSet_iff OIdx x).mp hx
    have hx1 := (hagree x (hOsub hx)).2
    rw [hx1]
    simp [u1, hxO]
  have hanchor := (hagree (anchor j) (anchor_mem_Sset j)).2
  have h1 : u1 (anchor j) = 0 := by
    simp [u1, anchor_not_OIdx j]
  have h2 : v1 (anchor j) = 1 := by rw [hv1eq]
  exact one_ne_zero (h2.symm.trans (hanchor.trans h1))

/-! ### The fresh coordinate -/

theorem ifresh_mem_Sset (j : Fin 3) : ifresh ∈ Sset j := by
  rw [Sset, mem_residueSet_iff]
  fin_cases j <;> decide

theorem ifresh_not_mem_Jset : ifresh ∉ Jset := by
  rw [Jset, mem_residueSet_iff]
  decide

/-! ### The refutation -/

/-- **`SharedFreshTripleFree` is false on every order-`2^30` power domain of `F_P`.** -/
theorem sharedFreshTripleFree_refuted (g : F) (hg : orderOf g = 2 ^ 30) (hg0 : g ≠ 0) :
    ¬ SharedFreshTripleFree (powDomain g hg hg0) := by
  intro hfree
  apply hfree (u0 g) u1 Jset Jset_card_ge (joint_on_Jset g _)
    ifresh ifresh_not_mem_Jset
  obtain ⟨h01, h02, h12⟩ := gam_distinct g hg hg0
  have hwitness : ∀ j : Fin 3,
      SharedWitnessAt (powDomain g hg hg0) (u0 g) u1 ifresh (gam g j) := by
    intro j
    exact ⟨Sset j, ifresh_mem_Sset j, Sset_card_ge j,
      ⟨pfun g j, pfun_mem g hg hg0 j, agreement g hg j⟩,
      not_joint_on_Sset g hg hg0 j⟩
  exact ⟨gam g 0, gam g 1, gam g 2, h01, h02, h12,
    hwitness 0, hwitness 1, hwitness 2⟩

/-! ## Literal instantiation at the canonical P1 domain -/

/-- **The residual is false at the canonical P1 predecessor domain.**  The fixed-witness
charge branch (`badFamily_card_le_N_of_sharedFreshTripleFree`) is therefore dead at the
canonical domain: its hypothesis can never be discharged. -/
theorem sharedFreshTripleFree_canonicalDomain_refuted :
    ¬ SharedFreshTripleFree
      ArkLib.ProximityGap.Frontier.P1RateQuarterCanonicalCodeBridge.canonicalDomain :=
  sharedFreshTripleFree_refuted g orderOf_g g_ne_zero

/-- Existence form: some (indeed the canonical) P1 evaluation domain refutes the residual. -/
theorem exists_domain_refuting_sharedFreshTripleFree :
    ∃ dom : Fin N ↪ F, ¬ SharedFreshTripleFree dom :=
  ⟨_, sharedFreshTripleFree_canonicalDomain_refuted⟩

end ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshTripleP1Refuted

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshTripleP1Refuted

#print axioms residueSet_card
#print axioms pow_fold
#print axioms gam_distinct
#print axioms joint_on_Jset
#print axioms line_identity
#print axioms agreement
#print axioms pfun_mem
#print axioms not_joint_on_Sset
#print axioms sharedFreshTripleFree_refuted
#print axioms sharedFreshTripleFree_canonicalDomain_refuted
#print axioms exists_domain_refuting_sharedFreshTripleFree
