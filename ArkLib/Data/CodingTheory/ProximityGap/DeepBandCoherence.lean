/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ProductionBoundaryFailure

/-!
# Deep-band coherence (#371): the witness-mass law at every band

The production-regime averaging engine extended below the boundary band.  A
`(k+m+1)`-point core `T` is **coherent** for `u₀ = Q∘dom` when the
`T`-interpolant of `Q` has vanishing coefficients in degrees `k+1, …, k+m`;
then `γ_T := −coeff_k` of the interpolant absorbs the last obstruction and the
line `Q∘dom + γ_T·x^k` is explained on ALL of `T` by a degree-`< k` codeword —
`T` is a full band-`m` witness and `γ_T` is bad (`mcaEvent_of_coherent`).

Coherence is `m` subtraction-linear conditions on the coefficient space, so by
the multi-kernel bound (`card_multiKernel_ge`: `m` linear conditions cut the
space by at most `q^m`) and first-moment averaging:

  **`∃ Q₀ : C(n, k+m+1) ≤ #(coherent cores of Q₀) · q^m`** —

the witness-core family of some stack has density `≥ q^{−m}` among ALL
`(k+m+1)`-cores, at every band radius, with no parameter restrictions
(`deep_band_witness_mass`).  In production (`C(n,k+m+1) ≫ q^m` for every band
reachable by the parameters), the certified witness mass is astronomical: the
band-`m` failure events are everywhere dense in the core geometry.  The
remaining slack against `#badSet` itself is exactly the per-scalar
multiplicity of cores — the design question, now isolated with the mass side
proven.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The core interpolant of a polynomial's values. -/
noncomputable def coreInterp (dom : Fin n ↪ F) (T : Finset (Fin n))
    (Q : F[X]) : F[X] :=
  Lagrange.interpolate T (⇑dom) (fun i => Q.eval (dom i))

/-- **Coherence**: the core interpolant has no coefficients in degrees
`k+1, …, k+m`. -/
def IsCoherent (dom : Fin n ↪ F) (k m : ℕ) (T : Finset (Fin n))
    (Q : F[X]) : Prop :=
  ∀ j : Fin m, (coreInterp dom T Q).coeff (k + 1 + j) = 0

open Classical in
/-- **The multi-kernel bound**: `m` subtraction-linear conditions on `F^M` cut
the space by at most a factor `q^m`. -/
theorem card_multiKernel_ge {M m : ℕ} (φ : Fin m → (Fin M → F) → F)
    (hsub : ∀ j x y, φ j (x - y) = φ j x - φ j y) :
    (Fintype.card F) ^ M
      ≤ (Finset.univ.filter
          (fun c : Fin M → F => ∀ j, φ j c = 0)).card
        * (Fintype.card F) ^ m := by
  induction m with
  | zero =>
      rw [Finset.filter_true_of_mem (fun c _ => fun j => Fin.elim0 j),
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, pow_zero,
        mul_one]
  | succ m ih =>
      set S := Finset.univ.filter
        (fun c : Fin M → F => ∀ j : Fin m, φ j.castSucc c = 0) with hS
      set S' := Finset.univ.filter
        (fun c : Fin M → F => ∀ j : Fin (m + 1), φ j c = 0) with hS'
      -- the fibers of the last condition inject into the zero fiber
      have hfib : ∀ v : F, (S.filter
          (fun c => φ (Fin.last m) c = v)).card
          ≤ (S.filter (fun c => φ (Fin.last m) c = 0)).card := by
        intro v
        rcases Finset.eq_empty_or_nonempty
          (S.filter (fun c => φ (Fin.last m) c = v)) with hempty | ⟨δv, hδv⟩
        · rw [hempty]
          exact Nat.zero_le _
        · obtain ⟨hδS, hδval⟩ := Finset.mem_filter.mp hδv
          refine Finset.card_le_card_of_injOn (fun c => c - δv) ?_ ?_
          · intro c hc
            obtain ⟨hcS, hcval⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hc)
            rw [Finset.mem_coe, Finset.mem_filter]
            refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩, ?_⟩
            · have h1 := (Finset.mem_filter.mp hcS).2 j
              have h2 := (Finset.mem_filter.mp hδS).2 j
              rw [hsub, h1, h2, sub_zero]
            · rw [hsub, hcval, hδval, sub_self]
          · intro a _ b _ hab
            have := congrArg (· + δv) hab
            simpa using this
      -- S splits into at most q fibers, each at most the zero fiber
      have hsplit : S.card ≤ Fintype.card F
          * (S.filter (fun c => φ (Fin.last m) c = 0)).card := by
        calc S.card
            = ∑ v ∈ Finset.univ, (S.filter
                (fun c => φ (Fin.last m) c = v)).card :=
              Finset.card_eq_sum_card_fiberwise fun c _ =>
                Finset.mem_univ _
          _ ≤ ∑ v ∈ (Finset.univ : Finset F), (S.filter
                (fun c => φ (Fin.last m) c = 0)).card :=
              Finset.sum_le_sum fun v _ => hfib v
          _ = Fintype.card F * (S.filter
                (fun c => φ (Fin.last m) c = 0)).card := by
              rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      -- the zero fiber of S is S'
      have hSS' : S.filter (fun c => φ (Fin.last m) c = 0) = S' := by
        ext c
        simp only [hS, hS', Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hcast, hlast⟩ j
          rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
          · exact hcast j'
          · exact hlast
        · intro hall
          exact ⟨fun j => hall j.castSucc, hall (Fin.last m)⟩
      -- assemble
      have hihS := ih (fun j => φ j.castSucc) (fun j x y => hsub j.castSucc x y)
      calc (Fintype.card F) ^ M
          ≤ S.card * (Fintype.card F) ^ m := hihS
        _ ≤ (Fintype.card F * S'.card) * (Fintype.card F) ^ m := by
            refine Nat.mul_le_mul_right _ ?_
            rw [← hSS']
            exact hsplit
        _ = S'.card * (Fintype.card F) ^ (m + 1) := by ring

open Classical in
/-- **Coherent cores certify bad scalars**: a coherent `(k+m+1)`-core is a
full band-`m` witness for the scalar `−coeff_k` of its interpolant. -/
theorem mcaEvent_of_coherent (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    {T : Finset (Fin n)} (hT : T.card = k + m + 1) {Q : F[X]}
    (hcoh : IsCoherent dom k m T Q) :
    mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => Q.eval (dom i)) (fun i => (dom i) ^ k)
      (-(coreInterp dom T Q).coeff k) := by
  have hvs : Set.InjOn dom T := fun a _ b _ h => dom.injective h
  set γ : F := -(coreInterp dom T Q).coeff k with hγ
  set R : F[X] := coreInterp dom T Q + C γ * X ^ k with hR
  -- the shifted interpolant has degree < k
  have hIdeg : (coreInterp dom T Q).degree < ((k + m + 1 : ℕ) : WithBot ℕ) := by
    rw [coreInterp, ← hT]
    exact Lagrange.degree_interpolate_lt _ hvs
  have hRdeg : R.degree < (k : ℕ) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro b hb
    have hbk : k ≤ b := by exact_mod_cast hb
    rw [hR, coeff_add, coeff_C_mul, coeff_X_pow]
    rcases Nat.lt_or_ge b (k + 1) with h | h
    · have hbk' : b = k := by omega
      subst hbk'
      rw [if_pos rfl, hγ]
      ring
    · -- k + 1 ≤ b: split below/above the interpolant degree
      rcases Nat.lt_or_ge b (k + m + 1) with h2 | h2
      · have hj : b - (k + 1) < m := by omega
        have hcoeff := hcoh ⟨b - (k + 1), hj⟩
        have hb' : k + 1 + (b - (k + 1)) = b := by omega
        rw [hb'] at hcoeff
        rw [hcoeff, if_neg (by omega)]
        ring
      · have hzero : (coreInterp dom T Q).coeff b = 0 := by
          refine Polynomial.coeff_eq_zero_of_degree_lt ?_
          exact lt_of_lt_of_le hIdeg (by exact_mod_cast h2)
        rw [hzero, if_neg (by omega)]
        ring
  -- the line agrees with R on T
  have hag : ∀ i ∈ T, R.eval (dom i)
      = Q.eval (dom i) + γ * (dom i) ^ k := by
    intro i hi
    rw [hR, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    congr 1
    rw [coreInterp]
    exact Lagrange.eval_interpolate_at_node _ hvs hi
  -- strong farness of the direction (free)
  have hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c (fun i => (dom i) ^ k)).card ≤ k := by
    have h := agreeSet_card_le_of_natDegree_eq dom hk
      (Q := X ^ k) (natDegree_X_pow k)
    simpa using h
  refine ⟨T, ?_, ⟨fun i => R.eval (dom i), ⟨R, hRdeg, rfl⟩,
    fun i hi => ?_⟩, ?_⟩
  · rw [hT]
    exact_mod_cast hhi
  · show R.eval (dom i) = Q.eval (dom i)
        + (-(coreInterp dom T Q).coeff k) • (dom i) ^ k
    rw [hag i hi, hγ, smul_eq_mul]
  · rintro ⟨v₀, -, v₁, hv₁, hagj⟩
    have hsub : T ⊆ agreeSet v₁ (fun i => (dom i) ^ k) := by
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (hagj i hi).2⟩
    have hcard : k + m + 1 ≤ (agreeSet v₁ (fun i => (dom i) ^ k)).card := by
      calc k + m + 1 = T.card := hT.symm
        _ ≤ _ := Finset.card_le_card hsub
    have := hμ v₁ hv₁
    omega

open Classical in
/-- **THE DEEP-BAND WITNESS-MASS LAW**: at every band radius, some stack's
coherent-core family has density `≥ q^{−m}` among all `(k+m+1)`-cores — and
every coherent core certifies its pinned scalar bad.  Unconditional. -/
theorem deep_band_witness_mass (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0)) :
    ∃ Q₀ : F[X],
      n.choose (k + m + 1)
        ≤ (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
            (fun T => IsCoherent dom k m T Q₀)).card * (Fintype.card F) ^ m
      ∧ ∀ T ∈ ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
            (fun T => IsCoherent dom k m T Q₀),
          mcaEvent (F := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
            (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k)
            (-(coreInterp dom T Q₀).coeff k) := by
  set q := Fintype.card F with hq
  set M := 2 * k + m + 2 with hM
  set Pm : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powersetCard (k + m + 1) with hPm
  set Qc : (Fin M → F) → F[X] :=
    fun c => ∑ j : Fin M, C (c j) * X ^ (j : ℕ) with hQc
  -- coherence is m subtraction-linear conditions
  have hsubQc : ∀ x y : Fin M → F, Qc (x - y) = Qc x - Qc y := by
    intro x y
    rw [hQc, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    show C (x j - y j) * X ^ (j : ℕ) = _
    rw [C_sub]
    ring
  have hsubI : ∀ (T : Finset (Fin n)) (x y : Fin M → F),
      coreInterp dom T (Qc (x - y))
        = coreInterp dom T (Qc x) - coreInterp dom T (Qc y) := by
    intro T x y
    rw [coreInterp, coreInterp, coreInterp, hsubQc]
    have hvals : (fun i => (Qc x - Qc y).eval (dom i))
        = (fun i => (Qc x).eval (dom i)) - (fun i => (Qc y).eval (dom i)) := by
      funext i
      simp [eval_sub]
    rw [hvals, map_sub]
  -- per-core averaging
  have hpercore : ∀ T ∈ Pm,
      q ^ M ≤ (Finset.univ.filter
        (fun c : Fin M → F => IsCoherent dom k m T (Qc c))).card * q ^ m := by
    intro T _
    have h := card_multiKernel_ge
      (φ := fun (j : Fin m) (c : Fin M → F) =>
        (coreInterp dom T (Qc c)).coeff (k + 1 + j))
      (fun j x y => by
        show (coreInterp dom T (Qc (x - y))).coeff (k + 1 + (j : ℕ))
            = (coreInterp dom T (Qc x)).coeff (k + 1 + (j : ℕ))
              - (coreInterp dom T (Qc y)).coeff (k + 1 + (j : ℕ))
        rw [hsubI T x y, coeff_sub])
    have hfeq : (Finset.univ.filter
          (fun c : Fin M → F => IsCoherent dom k m T (Qc c)))
        = (Finset.univ.filter (fun c : Fin M → F => ∀ j : Fin m,
            (fun (j : Fin m) (c : Fin M → F) =>
              (coreInterp dom T (Qc c)).coeff (k + 1 + j)) j c = 0)) :=
      Finset.filter_congr fun c _ => Iff.rfl
    rw [hq, hfeq]
    exact h
  -- double counting + pigeonhole
  have hsum : Pm.card * q ^ M
      ≤ ∑ c : Fin M → F, (Pm.filter
        (fun T => IsCoherent dom k m T (Qc c))).card * q ^ m := by
    have hswap : ∑ c : Fin M → F, (Pm.filter
          (fun T => IsCoherent dom k m T (Qc c))).card
        = ∑ T ∈ Pm, (Finset.univ.filter
          (fun c : Fin M → F => IsCoherent dom k m T (Qc c))).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    calc Pm.card * q ^ M = ∑ T ∈ Pm, q ^ M := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ T ∈ Pm, (Finset.univ.filter
            (fun c : Fin M → F => IsCoherent dom k m T (Qc c))).card * q ^ m :=
          Finset.sum_le_sum hpercore
      _ = (∑ T ∈ Pm, (Finset.univ.filter
            (fun c : Fin M → F => IsCoherent dom k m T (Qc c))).card)
              * q ^ m := by
          rw [Finset.sum_mul]
      _ = _ := by rw [← hswap, Finset.sum_mul]
  have hpigeon : ∃ c : Fin M → F, Pm.card
      ≤ (Pm.filter (fun T => IsCoherent dom k m T (Qc c))).card * q ^ m := by
    by_contra hall
    push Not at hall
    have hlt : ∑ c : Fin M → F, (Pm.filter
          (fun T => IsCoherent dom k m T (Qc c))).card * q ^ m
        < ∑ c : Fin M → F, Pm.card :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun c _ => hall c
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, smul_eq_mul] at hlt
    have := lt_of_le_of_lt hsum hlt
    rw [mul_comm (q ^ M) Pm.card] at this
    exact lt_irrefl _ (this.trans_le (le_refl _))
  obtain ⟨c, hc⟩ := hpigeon
  refine ⟨Qc c, ?_, fun T hT => ?_⟩
  · have hNm : Pm.card = n.choose (k + m + 1) := by
      rw [hPm, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rw [← hNm]
    exact hc
  · obtain ⟨hTmem, hTcoh⟩ := Finset.mem_filter.mp hT
    have hTcard : T.card = k + m + 1 :=
      (Finset.mem_powersetCard.mp hTmem).2
    exact mcaEvent_of_coherent dom hk hhi hTcard hTcoh

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.card_multiKernel_ge
#print axioms ProximityGap.Ownership.mcaEvent_of_coherent
#print axioms ProximityGap.Ownership.deep_band_witness_mass
