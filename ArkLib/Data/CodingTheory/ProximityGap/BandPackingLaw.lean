/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.UniversalBoundaryBound

/-!
# The band packing law and the ladder cliff (#371): the radius dependence

The structure of `ε_mca` BELOW the boundary band (witnesses of `≥ k+2` points):

* `ladder_badSet_empty_below_boundary` — **THE LADDER CLIFF**: the ladder stack
  has NO bad scalars at any radius with `k+1 < (1−δ)n`.  A witness of `k+2`
  points contains two `(k+1)`-tuples differing in one node; both pin `γ` to the
  negated node sum (Schur), forcing the two swapped nodes to be equal —
  absurd.  Combined with rounds 68–70 the ladder curve is COMPLETE:
  `0` below the boundary band, the spectrum mass exactly in it.

* `band_packing_law` — **THE BAND PACKING LAW**: for strongly far directions at
  the band `k+m < (1−δ)n`, witnesses of distinct bad scalars share at most `k`
  points (a shared `(k+1)`-subset would pin both scalars to its ratio), so the
  `(k+1)`-subsets of chosen `(k+m+1)`-point witness cores are disjoint across
  scalars:

    **`#badSet · C(k+m+1, k+1) ≤ C(n, k+1)`.**

  At `m = 0` this recovers the boundary ceiling `C(n,k+1)`; for `m ≥ 1` it
  decays — the upper envelope of the `δ*(ε*)` curve through every band, with
  the boundary band value attained (`boundary_allStacks_solution`).
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **THE LADDER CLIFF**: below the boundary band, the ladder stack has no bad
scalars at all. -/
theorem ladder_badSet_empty_below_boundary (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : ((k + 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) :
    Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => (dom i) ^ (k + 1)) (fun i => (dom i) ^ k) γ) = ∅ := by
  -- tuple-level farness of x^k is free
  have hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c (fun i => (dom i) ^ k)).card ≤ k := by
    have h := agreeSet_card_le_of_natDegree_eq dom hk
      (Q := X ^ k) (natDegree_X_pow k)
    simpa using h
  have hallres : ∀ t : Fin (k + 1) → Fin n, Function.Injective t →
      residual dom k t (fun i => (dom i) ^ k) ≠ 0 := by
    intro t htinj hres
    obtain ⟨c, hcC, hcag⟩ := extension_of_residual_eq_zero dom t htinj hres
    have hsub : Finset.univ.image t ⊆ agreeSet c (fun i => (dom i) ^ k) := by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hcag a⟩
    have hcard : k + 1 ≤ (agreeSet c (fun i => (dom i) ^ k)).card := by
      calc k + 1 = (Finset.univ.image t).card := by
            rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
              Fintype.card_fin]
        _ ≤ _ := Finset.card_le_card hsub
    have := hμ c hcC
    omega
  rw [Finset.eq_empty_iff_forall_notMem]
  intro γ hγ
  obtain ⟨S, hsz, ⟨c, hcC, hag⟩, -⟩ := (Finset.mem_filter.mp hγ).2
  have hScard : k + 2 ≤ S.card := by
    have h1 : (((k + 1 : ℕ)) : ℝ≥0) < (S.card : ℝ≥0) := lt_of_lt_of_le hlo hsz
    have h2 : k + 1 < S.card := by exact_mod_cast h1
    omega
  -- enumerate a (k+2)-point core
  obtain ⟨S'', hS''sub, hS''card⟩ := Finset.exists_subset_card_eq hScard
  set τ : Fin (k + 2) → Fin n :=
    fun a => (S''.equivFin.symm (Fin.cast hS''card.symm a) : Fin n) with hτ
  have hτinj : Function.Injective τ := by
    intro a b hab
    have h1 : (S''.equivFin.symm (Fin.cast hS''card.symm a))
        = S''.equivFin.symm (Fin.cast hS''card.symm b) := Subtype.ext hab
    exact Fin.cast_injective _ (S''.equivFin.symm.injective h1)
  have hτmem : ∀ a, τ a ∈ S := fun a =>
    hS''sub (S''.equivFin.symm (Fin.cast hS''card.symm a)).2
  -- the two overlapping (k+1)-tuples
  set t : Fin (k + 1) → Fin n := fun a => τ a.castSucc with ht
  set t' : Fin (k + 1) → Fin n :=
    Function.update t (Fin.last k) (τ (Fin.last (k + 1))) with ht'
  have htinj : Function.Injective t := fun a b hab =>
    Fin.castSucc_injective _ (hτinj hab)
  have htop : ∀ a : Fin (k + 1), t a ≠ τ (Fin.last (k + 1)) := by
    intro a hab
    have := hτinj hab
    have h1 : (a.castSucc : ℕ) = k + 1 := by
      rw [this]
      simp
    have := a.castSucc.2
    have h2 : (a.castSucc : ℕ) < k + 1 := by
      rw [Fin.val_castSucc]
      exact a.2
    omega
  have ht'inj : Function.Injective t' := by
    intro a b hab
    rw [ht'] at hab
    by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k
    · rw [ha, hb]
    · subst ha
      rw [Function.update_self, Function.update_of_ne hb] at hab
      exact absurd hab.symm (htop b)
    · subst hb
      rw [Function.update_self, Function.update_of_ne ha] at hab
      exact absurd hab (htop a)
    · rw [Function.update_of_ne ha, Function.update_of_ne hb] at hab
      exact htinj hab
  have htmem : ∀ a, t a ∈ S := fun a => hτmem a.castSucc
  have ht'mem : ∀ a, t' a ∈ S := by
    intro a
    rw [ht']
    by_cases ha : a = Fin.last k
    · subst ha
      rw [Function.update_self]
      exact hτmem _
    · rw [Function.update_of_ne ha]
      exact htmem a
  -- both tuples pin γ to their negated node sums
  obtain ⟨P, hPdeg, rfl⟩ := hcC
  have hPdeg' : P.natDegree < k := by
    by_cases hP0 : P = 0
    · subst hP0
      simpa using hk
    · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
  have hpin : ∀ s : Fin (k + 1) → Fin n, Function.Injective s →
      (∀ a, s a ∈ S) → γ = -∑ a, dom (s a) := by
    intro s hsinj hsmem
    have hlinezero : residual dom k s
        (fun i => (dom i) ^ (k + 1) + γ * (dom i) ^ k) = 0 := by
      refine residual_eq_zero_of_extends dom k s hPdeg' fun a => ?_
      have := hag (s a) (hsmem a)
      simpa [smul_eq_mul] using this.symm
    rw [residual_line] at hlinezero
    rw [gamma_eq_of_owned dom k s (hallres s hsinj) hlinezero,
      ladder_ratio_eq dom hk s (hallres s hsinj)]
  have h1 := hpin t htinj htmem
  have h2 := hpin t' ht'inj ht'mem
  -- the sums differ exactly in the swapped node
  have hsum : ∑ a, dom (t a) = ∑ a, dom (t' a) := by
    have h12 := h1.symm.trans h2
    exact neg_injective h12
  rw [Fin.sum_univ_castSucc (f := fun a => dom (t a)),
    Fin.sum_univ_castSucc (f := fun a => dom (t' a))] at hsum
  have hshare : ∀ b : Fin k, t b.castSucc = t' b.castSucc := by
    intro b
    rw [ht', Function.update_of_ne (by
      intro h
      have h1 : ((b.castSucc : Fin (k + 1)) : ℕ)
          = ((Fin.last k : Fin (k + 1)) : ℕ) := by rw [h]
      rw [Fin.val_castSucc, Fin.val_last] at h1
      have := b.2
      omega)]
  rw [Finset.sum_congr rfl fun b _ => congrArg dom (hshare b)] at hsum
  have hlast : dom (t (Fin.last k)) = dom (t' (Fin.last k)) :=
    add_left_cancel hsum
  have h3 : t (Fin.last k) = t' (Fin.last k) := dom.injective hlast
  rw [ht', Function.update_self, ht] at h3
  have h4 := hτinj h3
  have h5 : ((Fin.last k).castSucc : ℕ) = ((Fin.last (k + 1)) : ℕ) := by
    rw [h4]
  rw [Fin.val_castSucc, Fin.val_last, Fin.val_last] at h5
  omega

open Classical in
/-- **THE BAND PACKING LAW**: for strongly far directions at the band
`k+m < (1−δ)n`, the bad-scalar count obeys
`#badSet · C(k+m+1, k+1) ≤ C(n, k+1)` — witnesses of distinct bad scalars
share at most `k` points, so their `(k+1)`-subset families are disjoint. -/
theorem band_packing_law (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hlo : ((k + m : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    {u₀ u₁ : Fin n → F}
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ k) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        u₀ u₁ γ)).card * (k + m + 1).choose (k + 1) ≤ n.choose (k + 1) := by
  have hallres : ∀ t : Fin (k + 1) → Fin n, Function.Injective t →
      residual dom k t u₁ ≠ 0 := by
    intro t htinj hres
    obtain ⟨c, hcC, hcag⟩ := extension_of_residual_eq_zero dom t htinj hres
    have hsub : Finset.univ.image t ⊆ agreeSet c u₁ := by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hcag a⟩
    have hcard : k + 1 ≤ (agreeSet c u₁).card := by
      calc k + 1 = (Finset.univ.image t).card := by
            rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
              Fintype.card_fin]
        _ ≤ _ := Finset.card_le_card hsub
    have := hμ c hcC
    omega
  -- the canonical set-level ratio function
  set Ψ : Finset (Fin n) → F := fun s =>
    if h : s.card = k + 1 then
      -(residual dom k
          (fun a => (s.equivFin.symm (Fin.cast h.symm a) : Fin n)) u₀)
        / residual dom k
          (fun a => (s.equivFin.symm (Fin.cast h.symm a) : Fin n)) u₁
    else 0 with hΨ
  set bad := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      u₀ u₁ γ) with hbad
  -- each bad scalar owns a (k+m+1)-point core all of whose (k+1)-subsets pin it
  have hkey : ∀ γ ∈ bad, ∃ T : Finset (Fin n), T.card = k + m + 1 ∧
      ∀ s ⊆ T, s.card = k + 1 → γ = Ψ s := by
    intro γ hγ
    obtain ⟨S, hsz, ⟨c, hcC, hag⟩, -⟩ := (Finset.mem_filter.mp hγ).2
    have hScard : k + m + 1 ≤ S.card := by
      have h1 : (((k + m : ℕ)) : ℝ≥0) < (S.card : ℝ≥0) :=
        lt_of_lt_of_le hlo hsz
      have h2 : k + m < S.card := by exact_mod_cast h1
      omega
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hScard
    refine ⟨T, hTcard, fun s hsT hscard => ?_⟩
    set ts : Fin (k + 1) → Fin n :=
      fun a => (s.equivFin.symm (Fin.cast hscard.symm a) : Fin n) with hts
    have htsinj : Function.Injective ts := by
      intro a b hab
      have h1 : (s.equivFin.symm (Fin.cast hscard.symm a))
          = s.equivFin.symm (Fin.cast hscard.symm b) := Subtype.ext hab
      exact Fin.cast_injective _ (s.equivFin.symm.injective h1)
    have htsmem : ∀ a, ts a ∈ S := fun a =>
      hTsub (hsT (s.equivFin.symm (Fin.cast hscard.symm a)).2)
    obtain ⟨P, hPdeg, rfl⟩ := hcC
    have hPdeg' : P.natDegree < k := by
      by_cases hP0 : P = 0
      · subst hP0
        simpa using hk
      · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
    have hlinezero : residual dom k ts (fun i => u₀ i + γ * u₁ i) = 0 := by
      refine residual_eq_zero_of_extends dom k ts hPdeg' fun a => ?_
      have := hag (ts a) (htsmem a)
      simpa [smul_eq_mul] using this.symm
    rw [residual_line] at hlinezero
    rw [gamma_eq_of_owned dom k ts (hallres ts htsinj) hlinezero, hΨ]
    simp only [hscard, dif_pos]
    rfl
  choose! T hTcard hTpin using hkey
  -- the (k+1)-subset families are pairwise disjoint
  have hdisj : ∀ γ ∈ bad, ∀ γ' ∈ bad, γ ≠ γ' →
      Disjoint ((T γ).powersetCard (k + 1)) ((T γ').powersetCard (k + 1)) := by
    intro γ hγ γ' hγ' hne
    rw [Finset.disjoint_left]
    intro s hs hs'
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hs
    obtain ⟨hsub', -⟩ := Finset.mem_powersetCard.mp hs'
    exact hne ((hTpin γ hγ s hsub hcard).trans
      (hTpin γ' hγ' s hsub' hcard).symm)
  -- count
  calc bad.card * (k + m + 1).choose (k + 1)
      = ∑ γ ∈ bad, ((T γ).powersetCard (k + 1)).card := by
        rw [Finset.sum_congr rfl fun γ hγ => by
          rw [Finset.card_powersetCard, hTcard γ hγ]]
        rw [Finset.sum_const, smul_eq_mul]
    _ = (bad.biUnion (fun γ => (T γ).powersetCard (k + 1))).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ.powersetCard (k + 1)).card := by
        refine Finset.card_le_card fun s hs => ?_
        obtain ⟨γ, -, hsγ⟩ := Finset.mem_biUnion.mp hs
        obtain ⟨-, hcard⟩ := Finset.mem_powersetCard.mp hsγ
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
    _ = n.choose (k + 1) := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.ladder_badSet_empty_below_boundary
#print axioms ProximityGap.Ownership.band_packing_law
