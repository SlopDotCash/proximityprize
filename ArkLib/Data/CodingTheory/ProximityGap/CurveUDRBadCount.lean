/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CurveUDRCoefficients
import ArkLib.Data.CodingTheory.ProximityGap.MCACurveEvent

/-!
# Curve-UDR stage 2: the curve bad-scalar count (issues #302/#301/#304)

The combinatorial core of the curve unique-decoding-regime MCA bound (plan: issue #302
comment `4668760311`), generalizing `badCount_udr_le` (the pair case) to degree-`<L` curves:

* `curveBadCount_udr_le` — for a code of agreement-form minimum distance `d` and an `L`-row
  data stack `u`, the scalars `γ` whose curve point `∑ₖ γᵏ·uₖ` agrees with a codeword on a
  `t`-large set without joint stack agreement number at most `(L−1)·L·(n−t)`, in the curve
  unique-decoding regime `(L+1)·(n−t) < d`.

Proof: pick `L` distinct good scalars (else the count is `< L`, trivially within budget); the
stage-1 interpolating codeword-curve through them (`exists_curve_coeffs`) agrees with the data
rows on the `L`-fold agreement intersection `T` (inclusion–exclusion: `|T| ≥ n − L(n−t)`);
unique decoding collapses **every** good scalar's codeword onto the curve (disagreement fits in
`(T ∩ S γ)ᶜ`, of size `< d` in the regime); hence each good scalar is a root of a nonzero
degree-`<L` coordinate polynomial supported off `T`, and per-coordinate root counting gives the
bound. Stage 3 wires this through the `epsMCACurve` event and the proven seam
`hasMutualCorrAgreement_genRSC_of_epsMCACurve_le` into Cor 4.11 at every arity. Axiom-clean.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.CurveUDR

variable {F : Type} [Field F] [DecidableEq F]
variable {ι : Type} [Fintype ι]

/-- The coordinate polynomial of a degree-`<L` error stack. Its roots are exactly the scalars
where the curve error vanishes at coordinate `i`. -/
noncomputable def coordinatePoly {L : ℕ} (e : Fin L → ι → F) (i : ι) : F[X] :=
  ∑ k : Fin L, Polynomial.C (e k i) * Polynomial.X ^ (k : ℕ)

omit [DecidableEq F] [Fintype ι] in
theorem coordinatePoly_eval {L : ℕ} (e : Fin L → ι → F) (i : ι) (γ : F) :
    (coordinatePoly e i).eval γ = ∑ k : Fin L, γ ^ (k : ℕ) * e k i := by
  rw [coordinatePoly, Polynomial.eval_finset_sum]
  exact Finset.sum_congr rfl (fun k _ => by
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring)

attribute [simp] coordinatePoly_eval

omit [DecidableEq F] [Fintype ι] in
theorem coordinatePoly_ne_zero_of_exists {L : ℕ} (e : Fin L → ι → F) (i : ι)
    (hi : ∃ k : Fin L, e k i ≠ 0) :
    coordinatePoly e i ≠ 0 := by
  obtain ⟨k, hk⟩ := hi
  intro hzero
  apply hk
  have hcoeff := congrArg (fun p : F[X] => Polynomial.coeff p (k : ℕ)) hzero
  simp only [coordinatePoly, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single k] at hcoeff
  · simpa using hcoeff
  · intro b _ hbk
    rw [if_neg (fun h => hbk ((Fin.ext h).symm)), mul_zero]
  · intro hkmem
    exact absurd (Finset.mem_univ k) hkmem

omit [DecidableEq F] [Fintype ι] in
theorem coordinatePoly_natDegree_le {L : ℕ} (e : Fin L → ι → F) (i : ι) :
    (coordinatePoly e i).natDegree ≤ L - 1 := by
  rw [coordinatePoly]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun k _ => ?_)
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  rw [Polynomial.natDegree_X_pow]
  omega

/-- A finite-set root count for curve-error coordinates. The pair bad-gamma bound is the
degree-one shadow of this statement; here each bad scalar is charged to a coordinate whose
error polynomial is nonzero, and each such coordinate contributes at most `L - 1` roots. -/
theorem curveBadGammaOn_le (G : Finset F) {L : ℕ} (e : Fin L → ι → F) :
    (G.filter (fun γ : F => ∃ i, (∃ k : Fin L, e k i ≠ 0) ∧
      ∑ k : Fin L, γ ^ (k : ℕ) * e k i = 0)).card
      ≤ (L - 1) * (univ.filter (fun i => ∃ k : Fin L, e k i ≠ 0)).card := by
  classical
  set supp : Finset ι := univ.filter (fun i => ∃ k : Fin L, e k i ≠ 0) with hsupp
  have hsub :
      G.filter (fun γ : F => ∃ i, (∃ k : Fin L, e k i ≠ 0) ∧
        ∑ k : Fin L, γ ^ (k : ℕ) * e k i = 0)
        ⊆ supp.biUnion (fun i => (coordinatePoly e i).roots.toFinset) := by
    intro γ hγ
    simp only [mem_filter] at hγ
    rcases hγ with ⟨_hγG, i, hi, hroot⟩
    rw [Finset.mem_biUnion]
    refine ⟨i, ?_, ?_⟩
    · rw [hsupp]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    · rw [Multiset.mem_toFinset, Polynomial.mem_roots']
      refine ⟨coordinatePoly_ne_zero_of_exists e i hi, ?_⟩
      rw [Polynomial.IsRoot, coordinatePoly_eval, hroot]
  calc
    (G.filter (fun γ : F => ∃ i, (∃ k : Fin L, e k i ≠ 0) ∧
      ∑ k : Fin L, γ ^ (k : ℕ) * e k i = 0)).card
        ≤ (supp.biUnion (fun i => (coordinatePoly e i).roots.toFinset)).card :=
          card_le_card hsub
    _ ≤ ∑ i ∈ supp, ((coordinatePoly e i).roots.toFinset).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ supp, (L - 1) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have hisupp : ∃ k : Fin L, e k i ≠ 0 := by
          rw [hsupp] at hi
          exact (Finset.mem_filter.mp hi).2
        calc ((coordinatePoly e i).roots.toFinset).card
            ≤ Multiset.card (coordinatePoly e i).roots := Multiset.toFinset_card_le _
          _ ≤ (coordinatePoly e i).natDegree := Polynomial.card_roots' _
          _ ≤ L - 1 := coordinatePoly_natDegree_le e i
    _ = (L - 1) * (univ.filter (fun i => ∃ k : Fin L, e k i ≠ 0)).card := by
        rw [hsupp, Finset.sum_const, smul_eq_mul, mul_comm]

/-- Local copy of the iterated inclusion–exclusion intersection bound. -/
private theorem card_inf_ge' {κ : Type} [DecidableEq ι] (s : Finset κ) (A : κ → Finset ι) :
    (∑ i ∈ s, (A i).card : ℤ) - (s.card - 1) * (Fintype.card ι : ℤ)
      ≤ ((s.inf A).card : ℤ) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty, Finset.card_empty, Finset.inf_empty]
      have : (Finset.univ : Finset ι).card = Fintype.card ι := Finset.card_univ
      push_cast [this]
      ring_nf
      simp
  | insert a s ha ih =>
      rw [Finset.inf_insert, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have hpair : ((A a ⊓ s.inf A).card : ℤ)
          ≥ (A a).card + (s.inf A).card - (Fintype.card ι : ℤ) := by
        have hu : ((A a ∪ s.inf A).card : ℤ) ≤ (Fintype.card ι : ℤ) := by
          have : (A a ∪ s.inf A).card ≤ Fintype.card ι := by
            rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
          exact_mod_cast this
        have hie : (A a ⊓ s.inf A).card + (A a ∪ s.inf A).card
            = (A a).card + (s.inf A).card := Finset.card_inter_add_card_union _ _
        have : ((A a ⊓ s.inf A).card : ℤ) + ((A a ∪ s.inf A).card : ℤ)
            = (A a).card + (s.inf A).card := by exact_mod_cast hie
        linarith
      push_cast at ih ⊢
      nlinarith [ih, hpair]

set_option maxHeartbeats 2000000 in
-- The interpolation/collapse/root-count proof combines several nonlinear cardinality estimates.
/-- **Curve bad-scalar count in the unique-decoding regime (stage 2).** For a code of minimum
distance `d` (agreement form) and a degree-`<L` data stack `u`, the scalars `γ` whose curve
point `∑ₖ γᵏ·uₖ` agrees with a codeword on a `t`-large set without joint stack agreement number
at most `(L−1)·L·(n−t)`, provided `L ≥ 2`, `(L+1)·(n−t) < d`, and `t ≤ n`. Generalizes
`badCount_udr_le` (the `L = 2` case) via the stage-1 curve-coefficient extraction. -/
theorem curveBadCount_udr_le (C : Submodule F (ι → F)) (L : ℕ) (hL : 2 ≤ L)
    (u : Fin L → ι → F) (d t : ℕ)
    (htn : t < Fintype.card ι)
    (hmd : ∀ a ∈ C, ∀ b ∈ C, (univ.filter (fun i => a i ≠ b i)).card < d → a = b)
    (hreg : (L + 1) * (Fintype.card ι - t) < d)
    (G : Finset F) (S : F → Finset ι) (w : F → ι → F)
    (hSt : ∀ γ ∈ G, t ≤ (S γ).card)
    (hwC : ∀ γ ∈ G, w γ ∈ C)
    (hwS : ∀ γ ∈ G, ∀ i ∈ S γ, w γ i = ∑ k : Fin L, γ ^ (k : ℕ) * u k i)
    (hno : ∀ γ ∈ G, ¬ ProximityGap.stackJointAgreesOn (C : Set (ι → F)) (S γ) u) :
    G.card ≤ (L - 1) * (L * (Fintype.card ι - t)) := by
  classical
  set n := Fintype.card ι with hn
  by_cases hG : L ≤ G.card
  · -- pick L distinct good scalars
    obtain ⟨nodes, hsub, hnodes⟩ := Finset.exists_subset_card_eq hG
    -- the L-fold agreement intersection
    set T : Finset ι := nodes.inf S with hT
    have hTcard : (n : ℤ) - L * (n - t) ≤ (T.card : ℤ) := by
      have h := card_inf_ge' nodes S
      have hsum : (L * t : ℤ) ≤ ∑ γ ∈ nodes, ((S γ).card : ℤ) := by
        calc (L * t : ℤ) = ∑ _γ ∈ nodes, (t : ℤ) := by
              rw [Finset.sum_const, hnodes]; ring
          _ ≤ ∑ γ ∈ nodes, ((S γ).card : ℤ) := by
              refine Finset.sum_le_sum (fun γ hγ => ?_)
              exact_mod_cast hSt γ (hsub hγ)
      have hsum' : (∑ γ ∈ nodes, ((S γ).card : ℤ)) = (∑ γ ∈ nodes, (S γ).card : ℕ) := by
        push_cast; rfl
      rw [hnodes] at h
      have htn' : (t : ℤ) ≤ n := by exact_mod_cast (le_of_lt htn)
      nlinarith [h, hsum]
    -- the interpolating codeword-curve through the nodes
    obtain ⟨c, hcC, hcAgree⟩ := exists_curve_coeffs C L nodes hnodes w
      (fun γ hγ => hwC γ (hsub hγ))
    -- on T the coefficients agree with the data rows
    have hcT : ∀ i ∈ T, ∀ k : Fin L, c k i = u k i := by
      intro i hi k
      refine hcAgree i (fun k => u k i) (fun γ hγ => ?_) k
      have hiS : i ∈ S γ := by
        have := Finset.inf_le (f := S) hγ
        exact this hi
      exact hwS γ (hsub hγ) i hiS
    -- unique-decoding collapse: every good scalar's codeword is on the curve
    have hcollapse : ∀ γ ∈ G, w γ = fun i => ∑ k : Fin L, γ ^ (k : ℕ) * c k i := by
      intro γ hγ
      have hcurveC : (fun i => ∑ k : Fin L, γ ^ (k : ℕ) * c k i) ∈ C := by
        have : (fun i => ∑ k : Fin L, γ ^ (k : ℕ) * c k i)
            = ∑ k : Fin L, γ ^ (k : ℕ) • c k := by
          funext i; rw [Finset.sum_apply]; rfl
        rw [this]
        exact Submodule.sum_mem C (fun k _ => Submodule.smul_mem C _ (hcC k))
      apply hmd _ (hwC γ hγ) _ hcurveC
      have hsub2 : (univ.filter (fun i => w γ i ≠ ∑ k : Fin L, γ ^ (k : ℕ) * c k i))
          ⊆ (T ∩ S γ)ᶜ := by
        intro i hi
        simp only [mem_filter, mem_univ, true_and] at hi
        simp only [mem_compl, mem_inter, not_and]
        intro hiT hiS
        apply hi
        rw [hwS γ hγ i hiS]
        exact Finset.sum_congr rfl (fun k _ => by rw [hcT i hiT k])
      refine lt_of_le_of_lt (card_le_card hsub2) ?_
      rw [card_compl]
      have hint : (T.card : ℤ) + (S γ).card - n ≤ ((T ∩ S γ).card : ℤ) := by
        have huN : (T ∪ S γ).card ≤ n := by
          rw [hn, ← Finset.card_univ]
          exact Finset.card_le_card (Finset.subset_univ _)
        have hu : ((T ∪ S γ).card : ℤ) ≤ (n : ℤ) := by exact_mod_cast huN
        have hie : (T ∩ S γ).card + (T ∪ S γ).card = T.card + (S γ).card :=
          Finset.card_inter_add_card_union _ _
        have : ((T ∩ S γ).card : ℤ) + ((T ∪ S γ).card : ℤ) = T.card + (S γ).card := by
          exact_mod_cast hie
        linarith
      have hSγ : (t : ℤ) ≤ (S γ).card := by exact_mod_cast hSt γ hγ
      have hd : ((L + 1) * (n - t) : ℤ) < d := by
        have hcast : (((L + 1) * (n - t) : ℕ) : ℤ) = ((L : ℤ) + 1) * ((n : ℤ) - t) := by
          rw [Nat.cast_mul, Nat.cast_sub (le_of_lt htn)]
          push_cast
          ring
        calc ((L : ℤ) + 1) * ((n : ℤ) - t) = (((L + 1) * (n - t) : ℕ) : ℤ) := hcast.symm
          _ < d := by exact_mod_cast hreg
      have hgoal : ((n : ℤ) - (T ∩ S γ).card) < d := by
        have hT' := hTcard
        nlinarith [hint, hSγ, hd, hT']
      have hfin : (n - (T ∩ S γ).card : ℕ) < d := by
        by_cases hle : (T ∩ S γ).card ≤ n
        · have : ((n - (T ∩ S γ).card : ℕ) : ℤ) = (n : ℤ) - (T ∩ S γ).card := by
            push_cast [Nat.cast_sub hle]; ring
          exact_mod_cast this ▸ hgoal
        · push Not at hle
          have : (n - (T ∩ S γ).card : ℕ) = 0 := Nat.sub_eq_zero_of_le (le_of_lt hle)
          rw [this]
          have : 0 < d := by
            rcases Nat.eq_zero_or_pos d with h0 | h; · omega
            exact h
          omega
      exact hfin
    -- every good scalar is a root of a nonzero degree-<L polynomial at a bad coordinate
    set e : Fin L → ι → F := fun k => u k - c k with he
    have hGsub : G ⊆ G.filter
        (fun γ : F => ∃ i, (∃ k : Fin L, e k i ≠ 0) ∧
          ∑ k : Fin L, γ ^ (k : ℕ) * e k i = 0) := by
      intro γ hγ
      simp only [mem_filter, hγ, true_and]
      have hnj := hno γ hγ
      have hexi : ∃ i ∈ S γ, ∃ k : Fin L, c k i ≠ u k i := by
        by_contra hcon
        push Not at hcon
        exact hnj ⟨c, hcC, fun i hi k => hcon i hi k⟩
      obtain ⟨i, hiS, k₀, hk₀⟩ := hexi
      refine ⟨i, ⟨k₀, ?_⟩, ?_⟩
      · simp only [he, Pi.sub_apply]
        intro h0
        exact hk₀ ((sub_eq_zero.mp h0).symm)
      · have h1 := hwS γ hγ i hiS
        have h2 := congrFun (hcollapse γ hγ) i
        simp only [he, Pi.sub_apply]
        have : ∑ k : Fin L, γ ^ (k : ℕ) * (u k i - c k i)
            = (∑ k : Fin L, γ ^ (k : ℕ) * u k i) - ∑ k : Fin L, γ ^ (k : ℕ) * c k i := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun k _ => by ring)
        rw [this, ← h1, ← h2, sub_self]
    -- root counting: each bad coordinate contributes at most L−1 roots
    have hbadSupp : (univ.filter (fun i => ∃ k : Fin L, e k i ≠ 0)) ⊆ Tᶜ := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi
      obtain ⟨k, hk⟩ := hi
      simp only [mem_compl]
      intro hiT
      apply hk
      simp only [he, Pi.sub_apply, hcT i hiT k, sub_self]
    have hsuppCard : (univ.filter (fun i => ∃ k : Fin L, e k i ≠ 0)).card
        ≤ L * (n - t) := by
      calc (univ.filter (fun i => ∃ k : Fin L, e k i ≠ 0)).card
          ≤ Tᶜ.card := card_le_card hbadSupp
        _ = n - T.card := by rw [card_compl, hn]
        _ ≤ L * (n - t) := by
            have := hTcard
            have hTn : T.card ≤ n := by
              rw [hn, ← Finset.card_univ]
              exact Finset.card_le_card (Finset.subset_univ _)
            have h1 : (T.card : ℤ) ≤ n := by exact_mod_cast hTn
            have h2 : ((n - T.card : ℕ) : ℤ) = (n : ℤ) - T.card := by
              rw [Nat.cast_sub hTn]
            have h3 : ((L * (n - t) : ℕ) : ℤ) = (L : ℤ) * ((n : ℤ) - t) := by
              rw [Nat.cast_mul, Nat.cast_sub (le_of_lt htn)]
            have : ((n - T.card : ℕ) : ℤ) ≤ ((L * (n - t) : ℕ) : ℤ) := by
              rw [h2, h3]; linarith [hTcard]
            exact_mod_cast this
    -- the union of per-coordinate root sets
    have hcount : G.card ≤ (L - 1) * (univ.filter (fun i => ∃ k : Fin L, e k i ≠ 0)).card := by
      calc
        G.card
            ≤ (G.filter (fun γ : F => ∃ i, (∃ k : Fin L, e k i ≠ 0) ∧
                ∑ k : Fin L, γ ^ (k : ℕ) * e k i = 0)).card :=
              card_le_card hGsub
        _ ≤ (L - 1) * (univ.filter (fun i => ∃ k : Fin L, e k i ≠ 0)).card :=
              curveBadGammaOn_le G e
    calc G.card ≤ (L - 1) * (univ.filter (fun i => ∃ k : Fin L, e k i ≠ 0)).card := hcount
      _ ≤ (L - 1) * (L * (n - t)) := Nat.mul_le_mul_left _ hsuppCard
  · -- fewer than L scalars: trivial bound
    push Not at hG
    have h1 : G.card ≤ L - 1 := by omega
    have hnt : 1 ≤ n - t := by omega
    have h2 : 1 ≤ L * (n - t) := by
      have hL1 : 1 ≤ L := by omega
      calc 1 = 1 * 1 := (one_mul 1).symm
        _ ≤ L * (n - t) := Nat.mul_le_mul hL1 hnt
    calc G.card ≤ L - 1 := h1
      _ = (L - 1) * 1 := (mul_one _).symm
      _ ≤ (L - 1) * (L * (n - t)) := Nat.mul_le_mul_left _ h2

end ArkLib.ProximityGap.CurveUDR

#print axioms ArkLib.ProximityGap.CurveUDR.curveBadCount_udr_le
