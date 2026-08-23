/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BandAttainment
import Mathlib.LinearAlgebra.Lagrange

/-!
# Chained band attainment (#371): the overlap construction

A factor-`k` improvement of the band lower bound: instead of DISJOINT witness
blocks (`band_attainment`, `r ≈ n/(k+m+1)`), use blocks of `k+m+1` consecutive
indices stepping by only `m+1` — adjacent blocks overlap in exactly `k`
points, the maximum the packing law allows.  The explaining codewords are
glued across overlaps by Lagrange interpolation: with

  `P₀ := 0`, `P_{j+1} := P_j + (γ_{j+1} − γ_j)·W_j`,

`W_j` the degree-`< k` interpolant of `x^k` on the `k` overlap points, the
patch formulas `P_j − γ_j·x^k` agree on every overlap (the interpolant matches
`x^k` there), hence telescope coherently; `u₀` is defined by the patch of the
block index `⌊val/(m+1)⌋` (capped).  Each block witnesses its own scalar:

  **`#badSet(u₀, x^k) ≥ r` whenever `r·(m+1) + k ≤ n` and `r ≤ q`** —

so `r = ⌊(n−k)/(m+1)⌋` is realizable at the band `(1−δ)n ≤ k+m+1`, against the
packing ceiling `C(n,k+1)/C(k+m+1,k+1)`.  The witness-core family of this
construction has pairwise overlaps exactly `k` — it is extremal for the
packing constraint among interval families.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

/-- The chained construction's floor lower bound dominates the older disjoint-block floor
whenever the degree parameter fits in the domain. -/
theorem disjoint_band_floor_le_chained_floor {n k m : ℕ} (hkn : k ≤ n) :
    n / (k + m + 1) ≤ (n - k) / (m + 1) := by
  by_cases hq : n / (k + m + 1) = 0
  · rw [hq]
    exact Nat.zero_le _
  · have hqpos : 0 < n / (k + m + 1) := Nat.pos_of_ne_zero hq
    rw [Nat.le_div_iff_mul_le (by omega : 0 < m + 1)]
    have hmul : n / (k + m + 1) * (k + m + 1) ≤ n := Nat.div_mul_le_self _ _
    have hkq : k ≤ n / (k + m + 1) * k :=
      Nat.le_mul_of_pos_left k hqpos
    have hsplit : n / (k + m + 1) * (m + 1) + k
        ≤ n / (k + m + 1) * (k + m + 1) := by
      calc n / (k + m + 1) * (m + 1) + k
          ≤ n / (k + m + 1) * (m + 1) + n / (k + m + 1) * k :=
            Nat.add_le_add_left hkq _
        _ = n / (k + m + 1) * (k + m + 1) := by ring
    omega

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The chained patch polynomial: `P₀ = 0`,
`P_{l+1} = P_l + (γ_{l+1} − γ_l)·W_l`. -/
noncomputable def chainPoly (W : ℕ → F[X]) (g : ℕ → F) : ℕ → F[X] :=
  fun j => Nat.rec 0 (fun l Pl => Pl + C (g (l + 1) - g l) * W l) j

omit [Fintype F] [DecidableEq F] in
theorem chainPoly_zero (W : ℕ → F[X]) (g : ℕ → F) : chainPoly W g 0 = 0 := rfl

omit [Fintype F] [DecidableEq F] in
theorem chainPoly_succ (W : ℕ → F[X]) (g : ℕ → F) (l : ℕ) :
    chainPoly W g (l + 1)
      = chainPoly W g l + C (g (l + 1) - g l) * W l := rfl

set_option maxHeartbeats 1600000 in
-- The chained gluing proof has long interpolation and arithmetic subgoals after refinement.
omit [DecidableEq F] in
open Classical in
/-- **THE CHAINED BAND ATTAINMENT**: overlapping blocks stepping by `m+1`,
glued by interpolants, realize `r` bad scalars whenever `r·(m+1) + k ≤ n` and
`r ≤ q`. -/
theorem band_attainment_chained (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    {r : ℕ} (hr : r * (m + 1) + k ≤ n) (hrF : r ≤ Fintype.card F) :
    ∃ u₀ : Fin n → F,
      r ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
          u₀ (fun i => (dom i) ^ k) γ)).card := by
  rcases Nat.eq_zero_or_pos r with hr0 | hr1
  · exact ⟨0, by rw [hr0]; exact Nat.zero_le _⟩
  -- r distinct scalars, extended to ℕ
  obtain ⟨G, -, hGcard⟩ := Finset.exists_subset_card_eq
    (show r ≤ (Finset.univ : Finset F).card by
      rw [Finset.card_univ]; exact hrF)
  set ι : Fin r → F :=
    fun j => (G.equivFin.symm (Fin.cast hGcard.symm j) : F) with hι
  have hιinj : Function.Injective ι := by
    intro a b hab
    have h1 : (G.equivFin.symm (Fin.cast hGcard.symm a))
        = G.equivFin.symm (Fin.cast hGcard.symm b) := Subtype.ext hab
    exact Fin.cast_injective _ (G.equivFin.symm.injective h1)
  set γn : ℕ → F := fun j => if h : j < r then ι ⟨j, h⟩ else 0 with hγn
  -- the overlap windows and their interpolants
  set O : ℕ → Finset (Fin n) := fun l => Finset.univ.filter
    (fun i : Fin n => (l + 1) * (m + 1) ≤ (i : ℕ)
      ∧ (i : ℕ) < l * (m + 1) + (k + m + 1)) with hO
  have hOcard : ∀ l, (O l).card ≤ k := by
    intro l
    have hinj : ∀ i ∈ O l, ∀ j ∈ O l, (i : ℕ) = (j : ℕ) → i = j :=
      fun i _ j _ h => Fin.ext h
    calc (O l).card
        ≤ (Finset.Ico ((l + 1) * (m + 1)) (l * (m + 1) + (k + m + 1))).card := by
          refine Finset.card_le_card_of_injOn (fun i => (i : ℕ)) ?_
            (fun i hi j hj h => Fin.ext h)
          intro i hi
          have h := (Finset.mem_filter.mp hi).2
          exact Finset.mem_Ico.mpr h
      _ ≤ k := by
          rw [Nat.card_Ico]
          have hexp : (l + 1) * (m + 1) = l * (m + 1) + (m + 1) := by ring
          omega
  obtain ⟨W, hWdeg, hWeval⟩ : ∃ W : ℕ → F[X],
      (∀ l, (W l).degree < (k : ℕ))
        ∧ ∀ l, ∀ i ∈ O l, (W l).eval (dom i) = (dom i) ^ k := by
    refine ⟨fun l => Lagrange.interpolate (O l) (⇑dom)
      (fun i => (dom i) ^ k), fun l => ?_, fun l i hi => ?_⟩
    · have hvs : Set.InjOn dom (O l) := fun a _ b _ h => dom.injective h
      calc (Lagrange.interpolate (O l) (⇑dom)
            (fun i => (dom i) ^ k)).degree
          < ((O l).card : ℕ) := Lagrange.degree_interpolate_lt _ hvs
        _ ≤ (k : ℕ) := by exact_mod_cast hOcard l
    · have hvs : Set.InjOn dom (O l) := fun a _ b _ h => dom.injective h
      exact Lagrange.eval_interpolate_at_node _ hvs hi
  -- the chained patch polynomials (opaque, equation-specified)
  obtain ⟨P, hP0, hPsucc⟩ : ∃ P : ℕ → F[X], P 0 = 0
      ∧ ∀ l, P (l + 1) = P l + C (γn (l + 1) - γn l) * W l :=
    ⟨chainPoly W γn, rfl, fun l => rfl⟩
  have hPdeg : ∀ j, (P j).degree < (k : ℕ) := by
    intro j
    induction j with
    | zero =>
        rw [hP0, degree_zero]
        exact WithBot.bot_lt_coe k
    | succ l ih =>
        rw [hPsucc]
        refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ih ?_)
        have h1 : (C (γn (l + 1) - γn l) * W l).degree ≤ (W l).degree := by
          refine le_trans (degree_mul_le _ _) ?_
          calc (C (γn (l + 1) - γn l)).degree + (W l).degree
              ≤ 0 + (W l).degree := add_le_add_left degree_C_le _
            _ = (W l).degree := zero_add _
        exact lt_of_le_of_lt h1 (hWdeg l)
  -- the telescope: patches agree along chains of overlaps
  have htele : ∀ j l : ℕ, j ≤ l → ∀ i : Fin n,
      l * (m + 1) ≤ (i : ℕ) → (i : ℕ) < j * (m + 1) + (k + m + 1) →
      (P l).eval (dom i) - γn l * (dom i) ^ k
        = (P j).eval (dom i) - γn j * (dom i) ^ k := by
    intro j l hjl
    induction l, hjl using Nat.le_induction with
    | base => intro i _ _; rfl
    | succ l hjl ih =>
        intro i hi1 hi2
        have hexp : (l + 1) * (m + 1) = l * (m + 1) + (m + 1) := by ring
        have hjle : j * (m + 1) ≤ l * (m + 1) :=
          Nat.mul_le_mul_right _ hjl
        have hiO : i ∈ O l := by
          rw [hO, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hi1, by omega⟩
        have hstep : (P (l + 1)).eval (dom i)
            = (P l).eval (dom i) + (γn (l + 1) - γn l) * (dom i) ^ k := by
          rw [hPsucc, eval_add, eval_mul, eval_C, hWeval l i hiO]
        have hIH := ih i (by omega) hi2
        rw [hstep]
        linear_combination hIH
  -- the glued word
  set b : Fin n → ℕ := fun i => min ((i : ℕ) / (m + 1)) (r - 1) with hb
  set u₀ : Fin n → F :=
    fun i => (P (b i)).eval (dom i) - γn (b i) * (dom i) ^ k with hu₀
  refine ⟨u₀, ?_⟩
  -- strong farness of the direction (free)
  have hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c (fun i => (dom i) ^ k)).card ≤ k := by
    have h := agreeSet_card_le_of_natDegree_eq dom hk
      (Q := X ^ k) (natDegree_X_pow k)
    simpa using h
  -- each scalar is bad, witnessed by its block
  have hbadj : ∀ j : Fin r, mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      u₀ (fun i => (dom i) ^ k) (ι j) := by
    intro j
    have hjr : (j : ℕ) ≤ r - 1 := by have := j.2; omega
    have hblockfit : (j : ℕ) * (m + 1) + (k + m + 1) ≤ n := by
      have h1 : (j : ℕ) * (m + 1) ≤ (r - 1) * (m + 1) :=
        Nat.mul_le_mul_right _ hjr
      have h2 : (r - 1) * (m + 1) + (m + 1) = r * (m + 1) := by
        have : r - 1 + 1 = r := by omega
        calc (r - 1) * (m + 1) + (m + 1) = (r - 1 + 1) * (m + 1) := by ring
          _ = r * (m + 1) := by rw [this]
      omega
    have hbound : ∀ x ∈ Finset.Ico ((j : ℕ) * (m + 1))
        ((j : ℕ) * (m + 1) + (k + m + 1)), x < n := by
      intro x hx
      have := (Finset.mem_Ico.mp hx).2
      omega
    set T : Finset (Fin n) :=
      (Finset.Ico ((j : ℕ) * (m + 1)) ((j : ℕ) * (m + 1) + (k + m + 1))).attachFin
        hbound with hT
    have hTcard : T.card = k + m + 1 := by
      rw [hT, Finset.card_attachFin, Nat.card_Ico]
      omega
    -- block membership facts
    have hTval : ∀ i ∈ T, (j : ℕ) * (m + 1) ≤ (i : ℕ)
        ∧ (i : ℕ) < (j : ℕ) * (m + 1) + (k + m + 1) := by
      intro i hi
      exact Finset.mem_Ico.mp ((Finset.mem_attachFin hbound).mp hi)
    -- the patch agreement on the block
    have hagree : ∀ i ∈ T,
        u₀ i = (P (j : ℕ)).eval (dom i) - γn (j : ℕ) * (dom i) ^ k := by
      intro i hi
      obtain ⟨hi1, hi2⟩ := hTval i hi
      have hjb : (j : ℕ) ≤ b i := by
        rw [hb]
        refine le_min ?_ hjr
        rw [Nat.le_div_iff_mul_le (by omega : 0 < m + 1)]
        exact hi1
      have hbval : (b i) * (m + 1) ≤ (i : ℕ) := by
        rw [hb]
        calc (min ((i : ℕ) / (m + 1)) (r - 1)) * (m + 1)
            ≤ ((i : ℕ) / (m + 1)) * (m + 1) :=
              Nat.mul_le_mul_right _ (min_le_left _ _)
          _ ≤ (i : ℕ) := Nat.div_mul_le_self _ _
      rw [hu₀]
      exact htele (j : ℕ) (b i) hjb i hbval hi2
    refine ⟨T, ?_, ⟨fun i => (P (j : ℕ)).eval (dom i),
      ⟨P (j : ℕ), hPdeg _, rfl⟩, fun i hi => ?_⟩, ?_⟩
    · rw [hTcard]
      exact_mod_cast hhi
    · -- the line agreement
      have h := hagree i hi
      have hγj : γn (j : ℕ) = ι j := by
        rw [hγn]
        simp only [j.2, dif_pos]
      change (P (j : ℕ)).eval (dom i) = u₀ i + ι j • (dom i) ^ k
      rw [h, ← hγj, smul_eq_mul]
      ring
    · -- no joint pair: the direction is strongly far
      rintro ⟨v₀, -, v₁, hv₁, hagj⟩
      have hsub : T ⊆ agreeSet v₁ (fun i => (dom i) ^ k) := by
        intro i hi
        rw [agreeSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (hagj i hi).2⟩
      have hcard : k + m + 1 ≤ (agreeSet v₁ (fun i => (dom i) ^ k)).card := by
        calc k + m + 1 = T.card := hTcard.symm
          _ ≤ _ := Finset.card_le_card hsub
      have := hμ v₁ hv₁
      omega
  -- collect
  calc r = ((Finset.univ : Finset (Fin r)).image ι).card := by
        rw [Finset.card_image_of_injective _ hιinj, Finset.card_univ,
          Fintype.card_fin]
    _ ≤ _ := by
        refine Finset.card_le_card fun γ hγ => ?_
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hγ
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbadj j⟩

omit [DecidableEq F] in
open Classical in
/-- **THE IMPROVED BAND BRACKET**: at the band radius
`k+m < (1−δ)n ≤ k+m+1`, the sup over stacks with direction `x^k` satisfies

  `⌊(n−k)/(m+1)⌋ ≤ sup #badSet ≤ C(n,k+1)/C(k+m+1,k+1)` —

a factor-`(k+m+1)/(m+1)` tighter lower side than the disjoint bracket. -/
theorem band_bracket_chained (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hlo : ((k + m : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    (hkn : k ≤ n) (hrF : (n - k) / (m + 1) ≤ Fintype.card F) :
    (∃ u₀ : Fin n → F,
      (n - k) / (m + 1) ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
          u₀ (fun i => (dom i) ^ k) γ)).card)
    ∧ ∀ u₀ : Fin n → F,
      (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
          u₀ (fun i => (dom i) ^ k) γ)).card * (k + m + 1).choose (k + 1)
        ≤ n.choose (k + 1) := by
  constructor
  · refine band_attainment_chained dom hk hhi ?_ hrF
    calc (n - k) / (m + 1) * (m + 1) + k ≤ (n - k) + k :=
          Nat.add_le_add_right (Nat.div_mul_le_self _ _) k
      _ = n := by omega
  · intro u₀
    refine band_packing_law dom hk hlo ?_
    have h := agreeSet_card_le_of_natDegree_eq dom hk
      (Q := X ^ k) (natDegree_X_pow k)
    simpa using h

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.disjoint_band_floor_le_chained_floor
#print axioms ProximityGap.Ownership.band_attainment_chained
#print axioms ProximityGap.Ownership.band_bracket_chained
