/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EsymmFiber

/-!
# The monomial word has unconditionally polynomial supply (#389)

The whole #389 supply wall is about the worst-case ARBITRARY word.  This file proves the
**monomial** word `x ↦ (dom x)^{k+m+1}` is NOT part of the wall: its explainable-core count
is unconditionally polynomial in `n`, on **any** domain, with no Garcia–Voloch/Stepanov
input.

Mechanism (polynomial division).  A `(k+m+1)`-subset `T` is explainable for the monomial
word iff its vanishing polynomial `V_T = ∏_{i∈T}(X − dom i)` satisfies `(V_T − X^{k+m+1})`
has degree `< k` (the first `m+1` elementary symmetric functions vanish).  Then for **any**
`k`-subset `S ⊆ T`, writing `V_S = ∏_{i∈S}(X − dom i)` (monic, degree `k`):
`V_S ∣ V_T`, so `V_T = V_S · (V_T /ₘ V_S)`, and the quotient is forced — if `T, T'` are both
explainable and share `S`, then `V_S·(Q − Q') = V_T − V_{T'}` has degree `< k = deg V_S`,
hence `Q = Q'` and `V_T = V_{T'}`, so `T = T'` (the roots, hence `dom(T)`, coincide).

So each `k`-subset is contained in **at most one** explainable core, and double-counting the
incidences `(T, S)` gives:

* `monomial_supply_choose_le` — **`#cores · C(k+m+1, k) ≤ C(n, k)`**, i.e.
  `#cores ≤ C(n,k)/C(k+m+1,k)`, unconditional, any domain, every band.

This generalizes `CubicSupplyExact`/`QuarticPowerSumFiber` to all bands and removes the
GV-conditionality for the monomial family — sharply isolating the supply wall to genuinely
NON-monomial (arbitrary `u₀`) words.
-/

open Finset Polynomial

namespace ProximityGap.EsymmFiber

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

omit [Fintype F] [DecidableEq F] [NeZero n] in
/-- `coreVanish dom S` divides `coreVanish dom T` when `S ⊆ T`. -/
theorem coreVanish_dvd_of_subset (dom : Fin n ↪ F) {S T : Finset (Fin n)} (hST : S ⊆ T) :
    coreVanish dom S ∣ coreVanish dom T :=
  Finset.prod_dvd_prod_of_subset _ _ _ hST

/-- `coreVanish` is injective on finsets (every index of one is a root, hence an index of
the other). -/
theorem coreVanish_injOn (dom : Fin n ↪ F) {T T' : Finset (Fin n)}
    (h : coreVanish dom T = coreVanish dom T') : T = T' := by
  classical
  have hsub : ∀ {A B : Finset (Fin n)}, coreVanish dom A = coreVanish dom B → A ⊆ B := by
    intro A B hAB i hi
    have h0 : (coreVanish dom B).eval (dom i) = 0 := by
      rw [← hAB]; exact coreVanish_eval_zero dom hi
    rw [coreVanish, eval_prod] at h0
    obtain ⟨j, hj, hj0⟩ := Finset.prod_eq_zero_iff.mp h0
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hj0
    rwa [dom.injective hj0]
  exact Finset.Subset.antisymm (hsub h) (hsub h.symm)

/-- **The determinacy core, in its sharpest form**: if the vanishing polynomials of two
cores differ in degree `< k`, then any common `k`-subset forces them equal.  (The whole
content of the monomial/polynomial-word supply bound.) -/
theorem coreVanish_eq_of_ksubset (dom : Fin n ↪ F) {k : ℕ}
    {T T' S : Finset (Fin n)}
    (hdiff : (coreVanish dom T - coreVanish dom T').degree < (k : WithBot ℕ))
    (hScard : S.card = k) (hST : S ⊆ T) (hST' : S ⊆ T') :
    T = T' := by
  classical
  set VS := coreVanish dom S with hVS
  set VT := coreVanish dom T with hVT
  set VT' := coreVanish dom T' with hVT'
  have hVSmonic : VS.Monic := coreVanish_monic dom S
  have hVSdeg : VS.degree = (k : WithBot ℕ) := by rw [hVS, coreVanish_degree, hScard]
  have hdvdT : VS ∣ VT := coreVanish_dvd_of_subset dom hST
  have hdvdT' : VS ∣ VT' := coreVanish_dvd_of_subset dom hST'
  have hfac : VS * (VT /ₘ VS) = VT := by
    have hmod : VT %ₘ VS = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hVSmonic).mpr hdvdT
    have := Polynomial.modByMonic_add_div VT VS
    rw [hmod, zero_add] at this; exact this
  have hfac' : VS * (VT' /ₘ VS) = VT' := by
    have hmod : VT' %ₘ VS = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hVSmonic).mpr hdvdT'
    have := Polynomial.modByMonic_add_div VT' VS
    rw [hmod, zero_add] at this; exact this
  set Q := VT /ₘ VS
  set Q' := VT' /ₘ VS
  have hQ : Q = Q' := by
    by_contra hne
    have hQQ : Q - Q' ≠ 0 := sub_ne_zero.mpr hne
    have hprod : VS * (Q - Q') = VT - VT' := by rw [mul_sub, hfac, hfac']
    have hdeglow : (VS * (Q - Q')).degree < (k : WithBot ℕ) := by rw [hprod]; exact hdiff
    rw [Polynomial.degree_mul, hVSdeg] at hdeglow
    have hQdeg : (0 : WithBot ℕ) ≤ (Q - Q').degree :=
      Polynomial.zero_le_degree_iff.mpr hQQ
    have hle : (k : WithBot ℕ) ≤ (k : WithBot ℕ) + (Q - Q').degree :=
      le_add_of_nonneg_right hQdeg
    exact absurd (lt_of_le_of_lt hle hdeglow) (lt_irrefl _)
  have hVeq : VT = VT' := by rw [← hfac, ← hfac', hQ]
  exact coreVanish_injOn dom hVeq

/-- **The determinacy core**: two explainable monomial cores sharing a `k`-subset coincide.
The shared `k`-subset's vanishing polynomial divides both, and the quotients agree by a
degree argument, so the full vanishing polynomials — hence the cores — coincide. -/
theorem monomial_core_determined_by_ksubset (dom : Fin n ↪ F) {k m : ℕ}
    {T T' S : Finset (Fin n)}
    (hexpT : (coreVanish dom T - X ^ (k + m + 1)).degree < (k : WithBot ℕ))
    (hexpT' : (coreVanish dom T' - X ^ (k + m + 1)).degree < (k : WithBot ℕ))
    (hScard : S.card = k) (hST : S ⊆ T) (hST' : S ⊆ T') :
    T = T' := by
  classical
  set VS := coreVanish dom S with hVS
  set VT := coreVanish dom T with hVT
  set VT' := coreVanish dom T' with hVT'
  have hVSmonic : VS.Monic := coreVanish_monic dom S
  have hVSdeg : VS.degree = (k : WithBot ℕ) := by rw [hVS, coreVanish_degree, hScard]
  -- VS divides both
  have hdvdT : VS ∣ VT := coreVanish_dvd_of_subset dom hST
  have hdvdT' : VS ∣ VT' := coreVanish_dvd_of_subset dom hST'
  -- VT = VS * (VT /ₘ VS), likewise T'
  have hfac : VS * (VT /ₘ VS) = VT := by
    have hmod : VT %ₘ VS = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hVSmonic).mpr hdvdT
    have := Polynomial.modByMonic_add_div VT VS
    rw [hmod, zero_add] at this; exact this
  have hfac' : VS * (VT' /ₘ VS) = VT' := by
    have hmod : VT' %ₘ VS = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hVSmonic).mpr hdvdT'
    have := Polynomial.modByMonic_add_div VT' VS
    rw [hmod, zero_add] at this; exact this
  -- the two quotients agree: VS*(Q - Q') = VT - VT' has degree < k = deg VS
  set Q := VT /ₘ VS
  set Q' := VT' /ₘ VS
  have hdiffdeg : (VT - VT').degree < (k : WithBot ℕ) := by
    have : VT - VT' = (VT - X ^ (k + m + 1)) - (VT' - X ^ (k + m + 1)) := by ring
    rw [this]
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hexpT hexpT')
  have hQ : Q = Q' := by
    by_contra hne
    have hQQ : Q - Q' ≠ 0 := sub_ne_zero.mpr hne
    have hprod : VS * (Q - Q') = VT - VT' := by rw [mul_sub, hfac, hfac']
    have hdeglow : (VS * (Q - Q')).degree < (k : WithBot ℕ) := by rw [hprod]; exact hdiffdeg
    rw [Polynomial.degree_mul, hVSdeg] at hdeglow
    have hQdeg : (0 : WithBot ℕ) ≤ (Q - Q').degree :=
      Polynomial.zero_le_degree_iff.mpr hQQ
    have hle : (k : WithBot ℕ) ≤ (k : WithBot ℕ) + (Q - Q').degree :=
      le_add_of_nonneg_right hQdeg
    exact absurd (lt_of_le_of_lt hle hdeglow) (lt_irrefl _)
  have hVeq : VT = VT' := by rw [← hfac, ← hfac', hQ]
  exact coreVanish_injOn dom hVeq

open Classical in
/-- **The unconditional monomial supply bound**: `#cores · C(k+m+1, k) ≤ C(n, k)`, where
`#cores` is the number of explainable `(k+m+1)`-cores of the monomial word `x ↦ (dom x)^{k+m+1}`.
Any domain, no Garcia–Voloch/Stepanov input — polynomial supply for the monomial family at
every band. -/
theorem monomial_supply_choose_le (dom : Fin n ↪ F) {k m : ℕ} :
    (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
          ∀ i ∈ T, c i = (dom i) ^ (k + m + 1))).card
      * (k + m + 1).choose k
      ≤ n.choose k := by
  -- the explainability lever (W = X^t)
  have hWdeg : (X ^ (k + m + 1) : Polynomial F).degree = ((k + m + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_X_pow]
  -- rewrite the filter predicate to the vanishing-degree form
  set cores := ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
      (fun T => ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
        ∀ i ∈ T, c i = (dom i) ^ (k + m + 1)) with hcores
  -- the incidence sigma type: (T ∈ cores) × (S ∈ T.powersetCard k)
  set B := cores.sigma (fun T => T.powersetCard k) with hB
  -- |B| = #cores * C(t,k)
  have hBcard : B.card = cores.card * (k + m + 1).choose k := by
    rw [hB, Finset.card_sigma]
    rw [Finset.sum_congr rfl (fun T hT => ?_)]
    · rw [Finset.sum_const, smul_eq_mul]
    · rw [Finset.card_powersetCard]
      have : T.card = k + m + 1 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
      rw [this]
  rw [← hBcard]
  -- inject B into k-subsets of univ, via (T,S) ↦ S
  have hinj : Set.InjOn (fun p : Σ _ : Finset (Fin n), Finset (Fin n) => p.2) (B : Set _) := by
    intro p hp q hq hpq
    simp only [hB, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, hcores,
      Finset.mem_filter, Finset.mem_powersetCard] at hp hq
    obtain ⟨⟨⟨_, hpTcard⟩, cP, hcP, hagreeP⟩, hpSsub, hpScard⟩ := hp
    obtain ⟨⟨⟨_, hqTcard⟩, cQ, hcQ, hagreeQ⟩, hqSsub, hqScard⟩ := hq
    -- explainability in vanishing-degree form for both T's
    have hexpP : (coreVanish dom p.1 - X ^ (k + m + 1)).degree < (k : WithBot ℕ) := by
      have hiff := explainable_iff_forcedPoly_degree dom (X ^ (k + m + 1)) hWdeg hpTcard
      have hword : (∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
          ∀ i ∈ p.1, c i = (X ^ (k + m + 1) : Polynomial F).eval (dom i)) := by
        simpa only [eval_pow, eval_X] using ⟨cP, hcP, hagreeP⟩
      have hfp := hiff.mp hword
      have hfpeq : forcedPoly dom k m (X ^ (k + m + 1)) p.1
          = X ^ (k + m + 1) - coreVanish dom p.1 := by
        rw [forcedPoly, show (X ^ (k + m + 1) : Polynomial F).coeff (k + m + 1) = 1 by
          rw [coeff_X_pow]; simp, map_one, one_mul]
      rw [hfpeq] at hfp
      rw [show coreVanish dom p.1 - X ^ (k + m + 1)
          = -(X ^ (k + m + 1) - coreVanish dom p.1) from by ring, Polynomial.degree_neg]
      exact hfp
    have hexpQ : (coreVanish dom q.1 - X ^ (k + m + 1)).degree < (k : WithBot ℕ) := by
      have hiff := explainable_iff_forcedPoly_degree dom (X ^ (k + m + 1)) hWdeg hqTcard
      have hword : (∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
          ∀ i ∈ q.1, c i = (X ^ (k + m + 1) : Polynomial F).eval (dom i)) := by
        simpa only [eval_pow, eval_X] using ⟨cQ, hcQ, hagreeQ⟩
      have hfp := hiff.mp hword
      have hfpeq : forcedPoly dom k m (X ^ (k + m + 1)) q.1
          = X ^ (k + m + 1) - coreVanish dom q.1 := by
        rw [forcedPoly, show (X ^ (k + m + 1) : Polynomial F).coeff (k + m + 1) = 1 by
          rw [coeff_X_pow]; simp, map_one, one_mul]
      rw [hfpeq] at hfp
      rw [show coreVanish dom q.1 - X ^ (k + m + 1)
          = -(X ^ (k + m + 1) - coreVanish dom q.1) from by ring, Polynomial.degree_neg]
      exact hfp
    have hT : p.1 = q.1 :=
      monomial_core_determined_by_ksubset dom hexpP hexpQ hpScard hpSsub
        (by rw [show p.2 = q.2 from hpq]; exact hqSsub)
    exact Sigma.ext hT (heq_of_eq (show p.2 = q.2 from hpq))
  calc B.card
      ≤ ((Finset.univ : Finset (Fin n)).powersetCard k).card :=
        Finset.card_le_card_of_injOn _ (fun p hp => by
          simp only [Finset.mem_coe, hB, Finset.mem_sigma, hcores, Finset.mem_filter] at hp
          rw [Finset.mem_coe, Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp hp.2).2⟩) hinj
    _ = n.choose k := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

open Classical in
/-- **The general polynomial-word supply bound**: for ANY word that is the evaluation of a
degree-EXACTLY-`(k+m+1)` polynomial `W` — in particular the monomial `X^t`, the ladder word
`X^t + λ·X^{t−2}`, or any single fixed polynomial — the explainable-core count satisfies
`#cores · C(k+m+1, k) ≤ C(n, k)`, UNCONDITIONALLY, any domain, every band.

This subsumes `monomial_supply_choose_le` and, crucially, gives the **ladder words an
unconditional polynomial supply bound** with no resultant/Mann threshold — the forced top
part of `V_T` is fixed by `W`, so any two explainable cores' vanishing polynomials differ in
degree `< k`, and `coreVanish_eq_of_ksubset` applies. -/
theorem polyEval_supply_choose_le (dom : Fin n ↪ F) {k m : ℕ} (W : Polynomial F)
    (hWdeg : W.degree = ((k + m + 1 : ℕ) : WithBot ℕ)) :
    (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
          ∀ i ∈ T, c i = W.eval (dom i))).card
      * (k + m + 1).choose k
      ≤ n.choose k := by
  have hWne : W ≠ 0 := by
    rw [Ne, ← Polynomial.degree_eq_bot, hWdeg]; exact WithBot.coe_ne_bot
  have hWt : W.coeff (k + m + 1) ≠ 0 := by
    rw [← natDegree_eq_of_degree_eq_some hWdeg]; exact leadingCoeff_ne_zero.mpr hWne
  set cores := ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
      (fun T => ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
        ∀ i ∈ T, c i = W.eval (dom i)) with hcores
  set B := cores.sigma (fun T => T.powersetCard k) with hB
  have hBcard : B.card = cores.card * (k + m + 1).choose k := by
    rw [hB, Finset.card_sigma]
    rw [Finset.sum_congr rfl (fun T hT => ?_)]
    · rw [Finset.sum_const, smul_eq_mul]
    · rw [Finset.card_powersetCard,
        (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2]
  rw [← hBcard]
  have hinj : Set.InjOn (fun p : Σ _ : Finset (Fin n), Finset (Fin n) => p.2) (B : Set _) := by
    intro p hp q hq hpq
    simp only [hB, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, hcores,
      Finset.mem_filter, Finset.mem_powersetCard] at hp hq
    obtain ⟨⟨⟨_, hpTcard⟩, hpexp⟩, hpSsub, hpScard⟩ := hp
    obtain ⟨⟨⟨_, hqTcard⟩, hqexp⟩, hqSsub, hqScard⟩ := hq
    -- forced-poly degree form for both cores
    have hfpP := (explainable_iff_forcedPoly_degree dom W hWdeg hpTcard).mp hpexp
    have hfpQ := (explainable_iff_forcedPoly_degree dom W hWdeg hqTcard).mp hqexp
    -- the vanishing polynomials differ in degree < k
    have hdiff : (coreVanish dom p.1 - coreVanish dom q.1).degree < (k : WithBot ℕ) := by
      have hkey : C (W.coeff (k + m + 1)) * (coreVanish dom p.1 - coreVanish dom q.1)
          = forcedPoly dom k m W q.1 - forcedPoly dom k m W p.1 := by
        simp only [forcedPoly]; ring
      have hdegRHS : (forcedPoly dom k m W q.1 - forcedPoly dom k m W p.1).degree
          < (k : WithBot ℕ) :=
        lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hfpQ hfpP)
      have hd : (C (W.coeff (k + m + 1)) * (coreVanish dom p.1 - coreVanish dom q.1)).degree
          < (k : WithBot ℕ) := by rw [hkey]; exact hdegRHS
      rwa [Polynomial.degree_mul, Polynomial.degree_C hWt, zero_add] at hd
    have hT : p.1 = q.1 :=
      coreVanish_eq_of_ksubset dom hdiff hpScard hpSsub (by rw [show p.2 = q.2 from hpq]; exact hqSsub)
    exact Sigma.ext hT (heq_of_eq (show p.2 = q.2 from hpq))
  calc B.card
      ≤ ((Finset.univ : Finset (Fin n)).powersetCard k).card :=
        Finset.card_le_card_of_injOn _ (fun p hp => by
          simp only [Finset.mem_coe, hB, Finset.mem_sigma, hcores, Finset.mem_filter] at hp
          rw [Finset.mem_coe, Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp hp.2).2⟩) hinj
    _ = n.choose k := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

end ProximityGap.EsymmFiber
