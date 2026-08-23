/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CorePartitionLemma
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandMultiplicity
import ArkLib.Data.CodingTheory.ProximityGap.PopularCodewords
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSDimension
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSCoveredFraction
import Mathlib.Data.Nat.Choose.Sum

/-!
# The capped-supply mass identity and the supply floor (#389)

After the mean-degree-law refutation (`MeanDegreeLawRefuted.lean`), the corrected
sub-Johnson target is the supply `Σ_c C(a_c, t)` itself, whose mean over words is the
witness mass.  This file pins that mean EXACTLY and floors the supply residual:

> **`agreeSet_fiber_card`** — for any reference word `c`,
> `#{w : agreeSet c w = S} = (q−1)^{n−|S|}` (prescribed agreements, avoided
> disagreements).

> **`sum_g_agreeSet_card`** — the word-space profile sum: for any `g`,
> `Σ_w g(|agreeSet c w|) = Σ_j C(n,j)·(q−1)^{n−j}·g(j)` — the exact agreement
> profile of the word space against any fixed reference word.

> **`cappedSupply_mass_identity`** — **the first moment, exact**:
> `Σ_w Σ_{c : t ≤ a_c ≤ cap} C(a_c,t) = #code · Σ_{j=t}^{cap} C(n,j)·(q−1)^{n−j}·C(j,t)`.
> At `#code = q^k`, `j = t` dominant: the mean supply is `≈ C(n,t)/q^{t−k}`
> `= C(n,t)/q^{m+1}` — random words sit exactly at the witness mass.

> **`exists_word_cappedSupply_ge`** — pigeonhole: some word's capped-family supply
> is at least the mean.  Because the cap EXCLUDES near-codewords from the family,
> this floor is not the trivial on-code forcing.

> **`cappedSupply_le_explainable_card`** — capped supply ≤ explainable-core count
> (unique explainers partition the cores), so the floor transfers:

> **`explainableCoreSupply_floor`** — any admissible `B` for the named residual
> `ExplainableCoreSupply dom k m B` satisfies
> `(#code · Σ_{j=t}^{n} C(n,j)(q−1)^{n−j}C(j,t)) / qⁿ ≤ B`.

Registered refinement (NOT claimed): the far-word floor — restricting the
pigeonhole to words with global agreement ≤ cap requires bounding the near-word
mass share; open bookkeeping.  Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code ArkLib.CS25

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- The codewords of `rsCode dom k` as a `Finset`. -/
noncomputable def codeFinset (dom : Fin n ↪ F) (k : ℕ) : Finset (Fin n → F) :=
  Finset.univ.filter (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F)))

open Classical in
/-- The capped-family supply of a word: `Σ_{c : t ≤ a_c ≤ cap} C(a_c, t)` — the
number of `t`-cores explained by a capped-agreement codeword. -/
noncomputable def cappedSupply (dom : Fin n ↪ F) (k t cap : ℕ) (w : Fin n → F) : ℕ :=
  ∑ c ∈ codeFinset dom k,
    (if t ≤ (agreeSet c w).card ∧ (agreeSet c w).card ≤ cap
      then (agreeSet c w).card.choose t else 0)

open Classical in
/-- **The agreement-fiber count**: `#{w : agreeSet c w = S} = (q−1)^{n−|S|}`. -/
theorem agreeSet_fiber_card (c : Fin n → F) (S : Finset (Fin n)) :
    ((Finset.univ : Finset (Fin n → F)).filter
        (fun w => agreeSet c w = S)).card
      = (Fintype.card F - 1) ^ (n - S.card) := by
  classical
  have hset : (Finset.univ : Finset (Fin n → F)).filter (fun w => agreeSet c w = S)
      = Fintype.piFinset (fun i =>
          if i ∈ S then ({c i} : Finset F) else Finset.univ.erase (c i)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hag i
      by_cases hi : i ∈ S
      · simp only [hi, if_true, Finset.mem_singleton]
        have : i ∈ agreeSet c w := hag ▸ hi
        have := (Finset.mem_filter.mp this).2
        exact this.symm
      · simp only [hi, if_false, Finset.mem_erase, Finset.mem_univ, and_true]
        intro hwc
        refine hi ?_
        rw [← hag]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwc.symm⟩
    · intro hpi
      ext i
      simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hcw
        by_contra hi
        have := hpi i
        simp only [hi, if_false, Finset.mem_erase] at this
        exact this.1 hcw.symm
      · intro hi
        have := hpi i
        simp only [hi, if_true, Finset.mem_singleton] at this
        exact this.symm
  rw [hset, Fintype.card_piFinset]
  have hprod : ∀ i : Fin n,
      ((if i ∈ S then ({c i} : Finset F) else Finset.univ.erase (c i)).card)
        = if i ∈ S then 1 else Fintype.card F - 1 := by
    intro i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp [hi, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  rw [Finset.prod_congr rfl (fun i _ => hprod i)]
  rw [← Finset.prod_filter_mul_prod_filter_not
    (Finset.univ : Finset (Fin n)) (fun i => i ∈ S)]
  have h1 : ∏ i ∈ Finset.univ.filter (fun i => i ∈ S),
      (if i ∈ S then 1 else Fintype.card F - 1) = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    simp [(Finset.mem_filter.mp hi).2]
  have hcompl : Finset.univ.filter (fun i : Fin n => ¬ i ∈ S) = Sᶜ := by
    ext i
    simp [Finset.mem_compl]
  have h2 : ∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬ i ∈ S),
      (if i ∈ S then 1 else Fintype.card F - 1)
      = (Fintype.card F - 1) ^ (n - S.card) := by
    rw [hcompl]
    rw [Finset.prod_congr rfl (fun i hi => by
      simp [Finset.mem_compl.mp hi] : ∀ i ∈ Sᶜ,
        (if i ∈ S then 1 else Fintype.card F - 1) = Fintype.card F - 1)]
    rw [Finset.prod_const, Finset.card_compl, Fintype.card_fin]
  rw [h1, h2, one_mul]

open Classical in
/-- **The word-space agreement profile**: for any reference word `c` and any
weight `g`, `Σ_w g(|agreeSet c w|) = Σ_{j≤n} C(n,j)·(q−1)^{n−j}·g(j)`. -/
theorem sum_g_agreeSet_card (c : Fin n → F) (g : ℕ → ℕ) :
    ∑ w : Fin n → F, g ((agreeSet c w).card)
      = ∑ j ∈ Finset.range (n + 1),
          n.choose j * (Fintype.card F - 1) ^ (n - j) * g j := by
  classical
  -- fiber the word space over the agreement set
  have hmaps : ∀ w ∈ (Finset.univ : Finset (Fin n → F)),
      agreeSet c w ∈ (Finset.univ : Finset (Fin n)).powerset := by
    intro w _
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun w => g ((agreeSet c w).card))
  rw [← hfiber]
  -- on each fiber the summand is constant `g(|S|)`, and the fiber has known card
  have hinner : ∀ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      (∑ w ∈ (Finset.univ : Finset (Fin n → F)).filter
          (fun w => agreeSet c w = S), g ((agreeSet c w).card))
        = (Fintype.card F - 1) ^ (n - S.card) * g S.card := by
    intro S _
    have hconst : ∀ w ∈ (Finset.univ : Finset (Fin n → F)).filter
        (fun w => agreeSet c w = S), g ((agreeSet c w).card) = g S.card := by
      intro w hw
      rw [(Finset.mem_filter.mp hw).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul,
      agreeSet_fiber_card]
  rw [Finset.sum_congr rfl hinner]
  -- group the powerset by cardinality
  rw [Finset.powerset_card_disjiUnion, Finset.sum_disjiUnion]
  rw [Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcardS : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
      (Fintype.card F - 1) ^ (n - S.card) * g S.card
        = (Fintype.card F - 1) ^ (n - j) * g j := by
    intro S hS
    rw [(Finset.mem_powersetCard.mp hS).2]
  rw [Finset.sum_congr rfl hcardS, Finset.sum_const, smul_eq_mul,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, mul_assoc]

open Classical in
/-- **THE CAPPED-SUPPLY MASS IDENTITY** (the exact first moment): the total capped
supply over the whole word space is

  `#code · Σ_{j ∈ [t, cap]} C(n,j) · (q−1)^{n−j} · C(j,t)`.

At `#code = q^k` and `j = t` dominant this is `≈ qⁿ · C(n,t)/q^{m+1}`: the mean
capped supply IS the witness mass — random words sit exactly at the corrected
target. -/
theorem cappedSupply_mass_identity (dom : Fin n ↪ F) (k t cap : ℕ) :
    ∑ w : Fin n → F, cappedSupply dom k t cap w
      = (codeFinset dom k).card
        * ∑ j ∈ Finset.range (n + 1),
            (if t ≤ j ∧ j ≤ cap
              then n.choose j * (Fintype.card F - 1) ^ (n - j) * j.choose t
              else 0) := by
  classical
  simp only [cappedSupply]
  rw [Finset.sum_comm]
  -- per codeword, the word-space profile sum with g = capped choose
  have hper : ∀ c ∈ codeFinset dom k,
      (∑ w : Fin n → F,
        (if t ≤ (agreeSet c w).card ∧ (agreeSet c w).card ≤ cap
          then (agreeSet c w).card.choose t else 0))
      = ∑ j ∈ Finset.range (n + 1),
          (if t ≤ j ∧ j ≤ cap
            then n.choose j * (Fintype.card F - 1) ^ (n - j) * j.choose t
            else 0) := by
    intro c _
    rw [sum_g_agreeSet_card c
      (fun a => if t ≤ a ∧ a ≤ cap then a.choose t else 0)]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : t ≤ j ∧ j ≤ cap
    · simp [hj]
    · simp [hj]
  rw [Finset.sum_congr rfl hper, Finset.sum_const, smul_eq_mul]

open Classical in
/-- **The pigeonhole floor**: some word's capped-family supply is at least the
mean.  The cap excludes near-codewords from the family, so this is NOT the
trivial on-code forcing. -/
theorem exists_word_cappedSupply_ge (dom : Fin n ↪ F) (k t cap : ℕ) :
    ∃ w : Fin n → F,
      ((codeFinset dom k).card
          * ∑ j ∈ Finset.range (n + 1),
              (if t ≤ j ∧ j ≤ cap
                then n.choose j * (Fintype.card F - 1) ^ (n - j) * j.choose t
                else 0))
        / (Fintype.card F) ^ n
      ≤ cappedSupply dom k t cap w := by
  classical
  set T : ℕ := (codeFinset dom k).card
    * ∑ j ∈ Finset.range (n + 1),
        (if t ≤ j ∧ j ≤ cap
          then n.choose j * (Fintype.card F - 1) ^ (n - j) * j.choose t
          else 0) with hT
  have htotal : ∑ w : Fin n → F, cappedSupply dom k t cap w = T :=
    cappedSupply_mass_identity dom k t cap
  have hconst : ∑ _w : Fin n → F, T / (Fintype.card F) ^ n
      ≤ ∑ w : Fin n → F, cappedSupply dom k t cap w := by
    rw [htotal, Finset.sum_const, smul_eq_mul, Finset.card_univ,
      Fintype.card_pi_const, mul_comm]
    exact Nat.div_mul_le_self T _
  obtain ⟨w, _, hw⟩ := Finset.exists_le_of_sum_le
    (Finset.univ_nonempty (α := Fin n → F)) hconst
  exact ⟨w, hw⟩

open Classical in
/-- **The Markov tail bound**: large-supply (adversarial) words are rare.  For any
threshold `λ`, the number of words whose capped supply reaches `λ`, times `λ`, is at
most the total mass `Σ_w S(w)`.

  `#{w : λ ≤ S(w)} · λ ≤ #code · Σ_j C(n,j)(q−1)^{n−j}C(j,t)`.

With `λ = M · (witness mass)` this says at most a `1/M` fraction of words carry supply
`M×` the mean — the **average-case** statement.  The sub-Johnson wall is precisely that
the *worst case* (`∃ w` with large supply) is not controlled by this: a vanishing
fraction can still be nonempty.  This lemma isolates that gap formally. -/
theorem cappedSupply_tail_card_mul_le (dom : Fin n ↪ F) (k t cap lam : ℕ) :
    (Finset.univ.filter
        (fun w : Fin n → F => lam ≤ cappedSupply dom k t cap w)).card * lam
      ≤ (codeFinset dom k).card
        * ∑ j ∈ Finset.range (n + 1),
            (if t ≤ j ∧ j ≤ cap
              then n.choose j * (Fintype.card F - 1) ^ (n - j) * j.choose t
              else 0) := by
  classical
  rw [← cappedSupply_mass_identity dom k t cap]
  set S : (Fin n → F) → ℕ := cappedSupply dom k t cap with hS
  calc (Finset.univ.filter (fun w => lam ≤ S w)).card * lam
      = ∑ _w ∈ Finset.univ.filter (fun w => lam ≤ S w), lam := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ w ∈ Finset.univ.filter (fun w => lam ≤ S w), S w :=
        Finset.sum_le_sum fun w hw => (Finset.mem_filter.mp hw).2
    _ ≤ ∑ w : Fin n → F, S w :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

open Classical in
/-- **Capped supply is dominated by the explainable-core count**: unique explainers
(`k ≤ t`) make the per-codeword core families disjoint, and every core of a family
member is explainable. -/
theorem cappedSupply_le_explainable_card (dom : Fin n ↪ F) {k t : ℕ} (cap : ℕ)
    (hkt : k ≤ t) (w : Fin n → F) :
    cappedSupply dom k t cap w
      ≤ (((Finset.univ : Finset (Fin n)).powersetCard t).filter
          (fun T => ExplainableOn dom k w T)).card := by
  classical
  -- the per-codeword core family
  set fam : (Fin n → F) → Finset (Finset (Fin n)) := fun c =>
    ((Finset.univ : Finset (Fin n)).powersetCard t).filter
      (fun T => ∀ i ∈ T, c i = w i) with hfam
  -- per-codeword: the capped summand is at most the family size
  have hper : ∀ c ∈ codeFinset dom k,
      (if t ≤ (agreeSet c w).card ∧ (agreeSet c w).card ≤ cap
        then (agreeSet c w).card.choose t else 0) ≤ (fam c).card := by
    intro c _
    by_cases hc : t ≤ (agreeSet c w).card ∧ (agreeSet c w).card ≤ cap
    · simp only [hc, if_true]
      -- C(a_c, t) counts the t-subsets of the agreement set, all in the family
      have hsub : ((agreeSet c w).powersetCard t) ⊆ fam c := by
        intro T hT
        obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
        refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ _, hTcard⟩, fun i hi => ?_⟩
        have := hTsub hi
        simp only [agreeSet, Finset.mem_filter] at this
        exact this.2
      calc (agreeSet c w).card.choose t
          = ((agreeSet c w).powersetCard t).card := by
            rw [Finset.card_powersetCard]
        _ ≤ (fam c).card := Finset.card_le_card hsub
    · simp [hc]
  -- the families of distinct codewords are disjoint (unique explainers)
  have hdisj : ∀ c ∈ codeFinset dom k, ∀ c' ∈ codeFinset dom k, c ≠ c' →
      Disjoint (fam c) (fam c') := by
    intro c hc c' hc' hne
    rw [Finset.disjoint_left]
    intro T hT hT'
    obtain ⟨hTmem, h1⟩ := Finset.mem_filter.mp hT
    obtain ⟨-, h2⟩ := Finset.mem_filter.mp hT'
    obtain ⟨-, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
    exact hne (explainable_core_explainer_unique dom
      (by omega : k ≤ T.card)
      ((Finset.mem_filter.mp hc).2) ((Finset.mem_filter.mp hc').2) h1 h2)
  -- assemble: Σ capped ≤ Σ |fam| = |⊔ fam| ≤ |explainable|
  calc cappedSupply dom k t cap w
      ≤ ∑ c ∈ codeFinset dom k, (fam c).card := Finset.sum_le_sum hper
    _ = ((codeFinset dom k).biUnion fam).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (((Finset.univ : Finset (Fin n)).powersetCard t).filter
          (fun T => ExplainableOn dom k w T)).card := by
        refine Finset.card_le_card ?_
        intro T hT
        obtain ⟨c, hc, hTc⟩ := Finset.mem_biUnion.mp hT
        obtain ⟨hTmem, hagr⟩ := Finset.mem_filter.mp hTc
        exact Finset.mem_filter.mpr
          ⟨hTmem, ⟨c, (Finset.mem_filter.mp hc).2, hagr⟩⟩

open Classical in
/-- **THE SUPPLY FLOOR**: any admissible `B` for the named residual
`ExplainableCoreSupply dom k m B` dominates the mean capped supply:

  `(#code · Σ_{j=k+m+1}^{n} C(n,j)(q−1)^{n−j}·C(j,k+m+1)) / qⁿ ≤ B`. -/
theorem explainableCoreSupply_floor (dom : Fin n ↪ F) {k m B : ℕ}
    (hB : ExplainableCoreSupply dom k m B) :
    ((codeFinset dom k).card
        * ∑ j ∈ Finset.range (n + 1),
            (if k + m + 1 ≤ j ∧ j ≤ n
              then n.choose j * (Fintype.card F - 1) ^ (n - j)
                * j.choose (k + m + 1)
              else 0))
      / (Fintype.card F) ^ n ≤ B := by
  classical
  obtain ⟨w, hw⟩ := exists_word_cappedSupply_ge dom k (k + m + 1) n
  exact le_trans hw (le_trans
    (cappedSupply_le_explainable_card dom n (by omega) w) (hB w))

/-! ## The exact witness-mass floor

The mass sum collapses by Vandermonde absorption + the binomial theorem:
`Σ_{j=t}^{n} C(n,j)(q−1)^{n−j}C(j,t) = C(n,t)·q^{n−t}`.  With `#code = q^k`
(RS dimension, `k ≤ n`) the floor becomes exactly the witness mass
`C(n,k+m+1)/q^{m+1}`. -/

/-- **Vandermonde absorption + binomial theorem in ℕ**:
`Σ_{j=t}^{n} C(n,j)(q−1)^{n−j}C(j,t) = C(n,t)·q^{n−t}`. -/
theorem absorb_choose_sum (q n' t : ℕ) (hq : 1 ≤ q) (htn : t ≤ n') :
    ∑ j ∈ Finset.range (n' + 1),
        (if t ≤ j then n'.choose j * (q - 1) ^ (n' - j) * j.choose t else 0)
      = n'.choose t * q ^ (n' - t) := by
  rw [← Finset.sum_filter]
  have hbij : ∑ j ∈ (Finset.range (n' + 1)).filter (fun j => t ≤ j),
        n'.choose j * (q - 1) ^ (n' - j) * j.choose t
      = ∑ i ∈ Finset.range (n' - t + 1),
          n'.choose (t + i) * (q - 1) ^ (n' - t - i) * (t + i).choose t := by
    refine Finset.sum_nbij' (fun j => j - t) (fun i => t + i) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      simp only [Finset.mem_range]; omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Finset.mem_filter, Finset.mem_range]; omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      simp only []; omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      simp only []; omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      simp only []
      have hjt : t + (j - t) = j := by omega
      have hexp : n' - t - (j - t) = n' - j := by omega
      rw [hjt, hexp]
  rw [hbij]
  have habs : ∀ i ∈ Finset.range (n' - t + 1),
      n'.choose (t + i) * (q - 1) ^ (n' - t - i) * (t + i).choose t
      = n'.choose t * ((n' - t).choose i * (q - 1) ^ (n' - t - i)) := by
    intro i _
    have hmul : n'.choose (t + i) * (t + i).choose t
        = n'.choose t * (n' - t).choose (t + i - t) :=
      Nat.choose_mul (Nat.le_add_right t i)
    have ht' : t + i - t = i := by omega
    rw [ht'] at hmul
    calc n'.choose (t + i) * (q - 1) ^ (n' - t - i) * (t + i).choose t
        = (n'.choose (t + i) * (t + i).choose t) * (q - 1) ^ (n' - t - i) := by ring
      _ = (n'.choose t * (n' - t).choose i) * (q - 1) ^ (n' - t - i) := by rw [hmul]
      _ = n'.choose t * ((n' - t).choose i * (q - 1) ^ (n' - t - i)) := by ring
  rw [Finset.sum_congr rfl habs, ← Finset.mul_sum]
  congr 1
  have hbinom := add_pow (1 : ℕ) (q - 1) (n' - t)
  rw [show (1 : ℕ) + (q - 1) = q from by omega] at hbinom
  rw [hbinom]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_pow, one_mul, Nat.cast_id]
  ring

/-- `rsCode` (the `SpikeFloor` Reed–Solomon submodule) coincides with the Mathlib
`ReedSolomon.code` as a membership predicate. -/
theorem rsCode_mem_iff_code (dom : Fin n ↪ F) (k : ℕ) (c : Fin n → F) :
    c ∈ (rsCode dom k : Submodule F (Fin n → F)) ↔ c ∈ ReedSolomon.code dom k := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, Polynomial.mem_degreeLT.mpr hP, rfl⟩
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, Polynomial.mem_degreeLT.mp hP, rfl⟩

open Classical in
/-- **RS dimension for `codeFinset`**: `#code = q^k` for `1 ≤ k ≤ n`.  Bridges
`codeFinset` to `rsCodeFinset` and applies `rsCodeFinset_card`. -/
theorem codeFinset_card (dom : Fin n ↪ F) {k : ℕ} [NeZero k] (hk : k ≤ n) :
    (codeFinset dom k).card = Fintype.card F ^ k := by
  classical
  have hdeg : Fintype (Polynomial.degreeLT F k) :=
    Fintype.ofEquiv (Fin k → F) (Polynomial.degreeLTEquiv F k).toEquiv.symm
  have hset : codeFinset dom k = rsCodeFinset dom k := by
    ext c
    simp only [codeFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_rsCodeFinset]
    exact rsCode_mem_iff_code dom k c
  rw [hset]
  have hnk : k ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hk
  exact rsCodeFinset_card dom k hnk

open Classical in
/-- **THE EXACT WITNESS-MASS FLOOR**: with the RS dimension `#code = q^k` (true for
`k ≤ n`, discharged by `rsCodeFinset_card`), the supply floor is exactly the witness
mass:

  `C(n, k+m+1) / q^{m+1} ≤ B`

for any admissible `B` of `ExplainableCoreSupply dom k m B`.  Every evaluation domain,
unconditionally: the named residual's `B` cannot beat the witness mass. -/
theorem explainableCoreSupply_witness_floor (dom : Fin n ↪ F) {k m B : ℕ}
    (hkn : k + m + 1 ≤ n)
    (hcard : (codeFinset dom k).card = Fintype.card F ^ k)
    (hB : ExplainableCoreSupply dom k m B) :
    n.choose (k + m + 1) / (Fintype.card F) ^ (m + 1) ≤ B := by
  classical
  set q : ℕ := Fintype.card F with hq
  have hq1 : 1 ≤ q := Fintype.card_pos
  set t : ℕ := k + m + 1 with ht
  have hfloor := explainableCoreSupply_floor dom hB
  -- rewrite the inner sum: the `j ≤ n` condition is automatic on `range (n+1)`
  have hsum : ∑ j ∈ Finset.range (n + 1),
      (if t ≤ j ∧ j ≤ n
        then n.choose j * (q - 1) ^ (n - j) * j.choose t else 0)
      = ∑ j ∈ Finset.range (n + 1),
          (if t ≤ j then n.choose j * (q - 1) ^ (n - j) * j.choose t else 0) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := by simp only [Finset.mem_range] at hj; omega
    by_cases h : t ≤ j
    · simp [h, hjn]
    · simp [h]
  rw [hsum, absorb_choose_sum q n t hq1 hkn] at hfloor
  rw [hcard] at hfloor
  -- q^k · (C(n,t)·q^{n−t}) / q^n = C(n,t)/q^{m+1}
  have hsplit : q ^ k * (n.choose t * q ^ (n - t)) / q ^ n
      = n.choose t / q ^ (m + 1) := by
    have hpow : q ^ k * (n.choose t * q ^ (n - t))
        = (n.choose t) * q ^ (n - (m + 1)) := by
      rw [show n - (m + 1) = k + (n - t) from by omega, pow_add]
      ring
    have hqn : q ^ n = q ^ (m + 1) * q ^ (n - (m + 1)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow, hqn]
    rw [Nat.mul_div_mul_right _ _ (pow_pos hq1 (n - (m + 1)))]
  rw [hsplit] at hfloor
  exact hfloor

open Classical in
/-- **THE WITNESS-MASS FLOOR, unconditional** (`1 ≤ k`, `k+m+1 ≤ n`): every
admissible `B` for the named residual `ExplainableCoreSupply dom k m B` dominates the
witness mass `C(n, k+m+1) / q^{m+1}`, for every evaluation domain.  The RS dimension
hypothesis is discharged by `codeFinset_card`. -/
theorem explainableCoreSupply_witness_floor' (dom : Fin n ↪ F) {k m B : ℕ}
    (hk : 1 ≤ k) (hkn : k + m + 1 ≤ n)
    (hB : ExplainableCoreSupply dom k m B) :
    n.choose (k + m + 1) / (Fintype.card F) ^ (m + 1) ≤ B := by
  have : NeZero k := ⟨by omega⟩
  exact explainableCoreSupply_witness_floor dom hkn
    (codeFinset_card dom (by omega)) hB

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.absorb_choose_sum
#print axioms ProximityGap.PairRank.codeFinset_card
#print axioms ProximityGap.PairRank.explainableCoreSupply_witness_floor
#print axioms ProximityGap.PairRank.explainableCoreSupply_witness_floor'
#print axioms ProximityGap.PairRank.agreeSet_fiber_card
#print axioms ProximityGap.PairRank.sum_g_agreeSet_card
#print axioms ProximityGap.PairRank.cappedSupply_mass_identity
#print axioms ProximityGap.PairRank.exists_word_cappedSupply_ge
#print axioms ProximityGap.PairRank.cappedSupply_tail_card_mul_le
#print axioms ProximityGap.PairRank.cappedSupply_le_explainable_card
#print axioms ProximityGap.PairRank.explainableCoreSupply_floor
