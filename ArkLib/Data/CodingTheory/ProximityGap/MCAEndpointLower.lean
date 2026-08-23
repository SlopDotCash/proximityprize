/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# New lower bounds on `ε_mca` via the `t`-spike construction (ABF26 §1)

This file proves **new quantitative lower bounds** on the mutual-correlated-agreement error
`ε_mca(RS[F, L, k], δ)` (ABF26 Definition 4.3) for Reed-Solomon codes, by exhibiting an
explicit family of adversarial *spike* words.

## The `t`-spike construction

Fix an injection `e : Fin t ↪ ι` selecting `t` distinct *spike positions*
`T := image e ⊆ ι`, and an injection `g : Fin t ↪ F` selecting `t` distinct field values
`γ_0, …, γ_{t-1}` (zero allowed). Define the two line words
```
  u₁ i := if i ∈ T then 1 else 0           -- the indicator of the spike set
  u₀ i := if i = e j then -(g j) else 0    -- minus the chosen value at each spike
```
At the scalar `γ = g j`, the line `u₀ + (g j) • u₁` vanishes *everywhere*:
off `T` both rows are `0`, and at the spike `i = e j'` it is `-(g j') + (g j)·1`, which is
`0` exactly when `j' = j` — but at a *different* spike `j' ≠ j` it need not vanish, so the
witness set is `S_j := (ι \ T) ∪ {e j}`, of size `n - t + 1`.

On `S_j` the line equals the zero codeword `0 ∈ C`. Yet **no** joint pair `(v₀, v₁)` of
codewords can agree with `(u₀, u₁)` on `S_j`: such a `v₁` would agree with `u₁ = 0` on the
`n - t ≥ k` positions of `ι \ T`, forcing the underlying degree-`< k` polynomial to vanish
on `≥ k` distinct domain points, hence `v₁ = 0`; but `v₁ (e j) = u₁ (e j) = 1 ≠ 0`. This is
precisely the `mcaEvent`.

Counting the `t` scalars `g 0, …, g (t-1)` that trigger the event gives, for the worst-case
word `u = ![u₀, u₁]`,
```
  Pr_{γ ← $ᵖ F}[mcaEvent C δ u₀ u₁ γ] ≥ t / q,            q := |F|,
```
and therefore (taking the supremum over line words)
```
  ε_mca(RS[F, L, k], δ) ≥ t / q                            whenever
      t + k ≤ n,  t ≤ q,  and  (1 - δ)·n ≤ n - t + 1.
```

## Consequences

* **Universal `1/q` floor** (`epsMCA_ge_inv_card`): the special case `t = 1` gives
  `1/q ≤ ε_mca(RS, δ)` at *every* radius `δ ∈ [0, 1]` for every non-full RS code
  (`1 + k ≤ n`) — a sanity anchor with no `δ` hypothesis at all.

* **Endpoint floor** (`epsMCA_one_ge`): at `δ = 1` the size hypothesis is free, so for
  `t := min (n - k) q` we obtain `min (n - k, q) / q ≤ ε_mca(RS, 1)`.

* **Refutation of the formalized MCA prize for small fields**
  (`epsStar_lt_epsMCA_one_of_field_small`): if `q < 2^128 · (n - k)` then
  `ε* = 2^(-128) < ε_mca(RS, 1)`. Combined with the endpoint-collapse finding
  (`GrandChallengeCollapse.lean`, proved concurrently — *not* imported here) this refutes
  the formalized §1 Grand MCA prize in that small-field regime: there is no admissible
  `δ* ≤ 1` with `ε_mca ≤ ε*`.

See `[ABF26]` §1 *Grand Challenges* (Grand MCA Challenge) and Definition 4.3.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code ReedSolomon
open scoped ProbabilityTheory BigOperators ENNReal

namespace SpikeLower

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The two spike words -/

/-- The set of `t` spike positions `T := image e ⊆ ι`. -/
def spikeSet {t : ℕ} (e : Fin t ↪ ι) : Finset ι := Finset.univ.image e

/-- The second row `u₁` of the spike line: the indicator of the spike set `T`. -/
noncomputable def spikeWord₁ {t : ℕ} (e : Fin t ↪ ι) : ι → F :=
  fun i => if i ∈ spikeSet e then (1 : F) else 0

open Classical in
/-- The first row `u₀` of the spike line: at spike position `e j` it is `-(g j)`, elsewhere
`0`. Encoded via the chosen preimage of the existential `∃ j, e j = i` (well-defined on the
range of `e` by injectivity; avoids the `Nonempty (Fin t)` requirement of `Function.invFun`). -/
noncomputable def spikeWord₀ {t : ℕ} (e : Fin t ↪ ι) (g : Fin t ↪ F) : ι → F :=
  fun i => if h : ∃ j, e j = i then -(g h.choose) else 0

variable {t : ℕ} (e : Fin t ↪ ι) (g : Fin t ↪ F)

@[simp] lemma mem_spikeSet {i : ι} : i ∈ spikeSet e ↔ ∃ j, e j = i := by
  simp [spikeSet, eq_comm]

lemma ej_mem_spikeSet (j : Fin t) : e j ∈ spikeSet e := by
  simp [spikeSet]

/-- The chosen preimage of `e j` under `e` is `j` itself, by injectivity. -/
lemma choose_e (j : Fin t) (hex : ∃ j', e j' = e j) : hex.choose = j :=
  e.injective hex.choose_spec

@[simp] lemma spikeWord₁_apply_mem {i : ι} (hi : i ∈ spikeSet e) :
    spikeWord₁ (F := F) e i = 1 := by simp [spikeWord₁, hi]

@[simp] lemma spikeWord₁_apply_not_mem {i : ι} (hi : i ∉ spikeSet e) :
    spikeWord₁ (F := F) e i = 0 := by simp [spikeWord₁, hi]

lemma spikeWord₁_ej (j : Fin t) : spikeWord₁ (F := F) e (e j) = 1 := by
  simp

lemma spikeWord₀_apply_not_mem {i : ι} (hi : i ∉ spikeSet e) :
    spikeWord₀ e g i = 0 := by
  have hnex : ¬ ∃ j, e j = i := by rwa [mem_spikeSet] at hi
  simp only [spikeWord₀, dif_neg hnex]

lemma spikeWord₀_ej (j : Fin t) : spikeWord₀ e g (e j) = -(g j) := by
  have hex : ∃ j', e j' = e j := ⟨j, rfl⟩
  simp only [spikeWord₀, dif_pos hex, choose_e e j hex]

/-! ## The witness set `S_j := (ι \ T) ∪ {e j}` -/

/-- The witness set `S_j := (ι \ T) ∪ {e j}`. -/
def spikeWitness (j : Fin t) : Finset ι :=
  (Finset.univ \ spikeSet e) ∪ {e j}

lemma card_spikeSet : (spikeSet e).card = t := by
  rw [spikeSet, Finset.card_image_of_injective _ e.injective, Finset.card_univ,
    Fintype.card_fin]

/-- `|S_j| = n - t + 1`. -/
lemma card_spikeWitness (j : Fin t) :
    (spikeWitness e j).card = Fintype.card ι - t + 1 := by
  classical
  have hcompl : (Finset.univ \ spikeSet e).card = Fintype.card ι - t := by
    rw [Finset.card_univ_diff, card_spikeSet e]
  have hdisj : Disjoint (Finset.univ \ spikeSet e) ({e j} : Finset ι) := by
    rw [Finset.disjoint_singleton_right]
    simp [ej_mem_spikeSet e j]
  rw [spikeWitness, Finset.card_union_of_disjoint hdisj, hcompl, Finset.card_singleton]

/-! ## The line vanishes on `S_j` -/

/-- The line `u₀ + (g j) • u₁` is `0` on every position of `S_j`. -/
lemma line_zero_on_spikeWitness (j : Fin t) :
    ∀ i ∈ spikeWitness e j,
      (spikeWord₀ e g + (g j) • spikeWord₁ (F := F) e) i = 0 := by
  intro i hi
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [spikeWitness, Finset.mem_union] at hi
  rcases hi with hi | hi
  · -- `i ∉ T`: both rows vanish.
    rw [Finset.mem_sdiff] at hi
    have hi' : i ∉ spikeSet e := hi.2
    rw [spikeWord₀_apply_not_mem e g hi', spikeWord₁_apply_not_mem e hi', mul_zero, add_zero]
  · -- `i = e j`: `-(g j) + (g j)·1 = 0`.
    rw [Finset.mem_singleton] at hi
    subst hi
    rw [spikeWord₀_ej e g j, spikeWord₁_ej e j, mul_one, neg_add_cancel]

/-! ## No joint codeword pair agrees with `(u₀, u₁)` on `S_j`

The crux: any `v₁ ∈ RS[F, domain, k]` agreeing with `u₁` on `S_j` must agree with `u₁ = 0`
on the `n - t ≥ k` positions of `ι \ T ⊆ S_j`, hence the underlying degree-`< k` polynomial
vanishes at `≥ k` distinct domain points and is `0`; but `v₁ (e j) = u₁ (e j) = 1 ≠ 0`. -/

/-- An RS codeword vanishing on `≥ k` distinct domain positions is the zero word. -/
lemma rs_eq_zero_of_vanishes_on
    (domain : ι ↪ F) (k : ℕ) {v : ι → F}
    (hv : v ∈ ReedSolomon.code domain k) {Z : Finset ι}
    (hZcard : k ≤ Z.card) (hZvanish : ∀ i ∈ Z, v i = 0) : v = 0 := by
  classical
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hv
  obtain ⟨p, hpdeg, hpeval⟩ := hv
  -- `p` vanishes on the (distinct) domain images of `Z`.
  set Zd : Finset F := Z.image domain with hZd
  have hZd_card : Zd.card = Z.card :=
    Finset.card_image_of_injective _ domain.injective
  have hpeval_zero : ∀ x ∈ Zd, p.eval x = 0 := by
    intro x hx
    rw [hZd, Finset.mem_image] at hx
    obtain ⟨i, hiZ, rfl⟩ := hx
    have : v i = p.eval (domain i) := by
      rw [hpeval]; rfl
    rw [← this]; exact hZvanish i hiZ
  -- degree `< k ≤ |Z| = |Zd|`, so `p = 0`.
  have hp0 : p = 0 := by
    by_cases hp : p = 0
    · exact hp
    · have hdeg_nat : p.natDegree < k := by
        have := (Polynomial.natDegree_lt_iff_degree_lt hp).mpr hpdeg
        exact this
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p Zd hpeval_zero
      rw [hZd_card]; omega
  rw [hpeval, hp0]
  ext i; simp [ReedSolomon.evalOnPoints]

/-- **Core: no joint agreement.** Under `t + k ≤ n`, no joint pair of codewords of
`RS[F, domain, k]` agrees with the spike line `(u₀, u₁)` on `S_j`. -/
lemma not_pairJointAgreesOn_spike
    (domain : ι ↪ F) (k : ℕ) (ht_n : t + k ≤ Fintype.card ι) (j : Fin t) :
    ¬ pairJointAgreesOn (ReedSolomon.code domain k : Set (ι → F)) (spikeWitness e j)
        (spikeWord₀ e g) (spikeWord₁ (F := F) e) := by
  classical
  rintro ⟨v₀, hv₀, v₁, hv₁, hagree⟩
  -- `v₁` agrees with `u₁` on `S_j`, and `u₁ = 0` on `ι \ T ⊆ S_j`.
  have hZ : Finset.univ \ spikeSet e ⊆ spikeWitness e j := by
    intro i hi; rw [spikeWitness, Finset.mem_union]; exact Or.inl hi
  have hv₁_vanish : ∀ i ∈ Finset.univ \ spikeSet e, v₁ i = 0 := by
    intro i hi
    have hi' : i ∉ spikeSet e := (Finset.mem_sdiff.mp hi).2
    have := (hagree i (hZ hi)).2
    rw [this, spikeWord₁_apply_not_mem e hi']
  -- `|ι \ T| = n - t ≥ k`.
  have hcompl_card : (Finset.univ \ spikeSet e).card = Fintype.card ι - t := by
    rw [Finset.card_univ_diff, card_spikeSet e]
  have hk_le : k ≤ (Finset.univ \ spikeSet e).card := by rw [hcompl_card]; omega
  -- Hence `v₁ = 0`.
  have hv₁_zero : v₁ = 0 :=
    rs_eq_zero_of_vanishes_on domain k hv₁ hk_le hv₁_vanish
  -- But `v₁ (e j) = u₁ (e j) = 1 ≠ 0`.
  have hej_mem : e j ∈ spikeWitness e j := by
    rw [spikeWitness, Finset.mem_union]; exact Or.inr (Finset.mem_singleton_self _)
  have hv₁_ej : v₁ (e j) = 1 := by
    rw [(hagree (e j) hej_mem).2, spikeWord₁_ej e j]
  rw [hv₁_zero] at hv₁_ej
  simp at hv₁_ej

/-! ## The spike `mcaEvent` -/

/-- **Core spike lemma.** For each `j`, `mcaEvent C δ u₀ u₁ (g j)` holds, provided
`t + k ≤ n` and `(1 - δ)·n ≤ n - t + 1`. -/
lemma mcaEvent_spike
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (ht_n : t + k ≤ Fintype.card ι)
    (hδ : ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ (Fintype.card ι - t + 1 : ℕ))
    (j : Fin t) :
    mcaEvent (ReedSolomon.code domain k : Set (ι → F)) δ
      (spikeWord₀ e g) (spikeWord₁ (F := F) e) (g j) := by
  refine ⟨spikeWitness e j, ?_, ?_, ?_⟩
  · -- size: `(1 - δ)·n ≤ |S_j| = n - t + 1`.
    rw [card_spikeWitness e j]
    exact hδ
  · -- the line equals the zero codeword on `S_j`.
    refine ⟨0, (ReedSolomon.code domain k).zero_mem, ?_⟩
    intro i hi
    have := line_zero_on_spikeWitness e g j i hi
    simp only [Pi.zero_apply]
    exact this.symm
  · -- no joint agreement.
    exact not_pairJointAgreesOn_spike e g domain k ht_n j

end SpikeLower

/-! ## Probability lower bound and the main theorem -/

open SpikeLower
open scoped ProbabilityTheory ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Probability lower bound.** For the spike line `(u₀, u₁)`, the bad-event probability is
at least `t / q`. -/
lemma pr_mcaEvent_spike_ge
    {t : ℕ} (e : Fin t ↪ ι) (g : Fin t ↪ F)
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (ht_n : t + k ≤ Fintype.card ι)
    (hδ : ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ (Fintype.card ι - t + 1 : ℕ)) :
    (t : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      Pr_{let γ ← $ᵖ F}[mcaEvent (ReedSolomon.code domain k : Set (ι → F)) δ
        (spikeWord₀ e g) (spikeWord₁ (F := F) e) γ] := by
  classical
  -- Unfold the probability as a tsum of indicators.
  rw [ProbabilityTheory.Pr_eq_tsum_indicator (P := fun γ =>
    mcaEvent (ReedSolomon.code domain k : Set (ι → F)) δ
      (spikeWord₀ e g) (spikeWord₁ (F := F) e) γ)]
  -- Each scalar value `g j` contributes `q⁻¹`.
  set imG : Finset F := Finset.univ.image g with himG
  have himG_card : imG.card = t := by
    rw [himG, Finset.card_image_of_injective _ g.injective, Finset.card_univ, Fintype.card_fin]
  -- Lower bound the tsum by the finite sum over `imG`.
  have hsum_le :
      (∑ γ ∈ imG, ($ᵖ F) γ *
          (if mcaEvent (ReedSolomon.code domain k : Set (ι → F)) δ
              (spikeWord₀ e g) (spikeWord₁ (F := F) e) γ then (1 : ℝ≥0∞) else 0)) ≤
        ∑' γ, ($ᵖ F) γ *
          (if mcaEvent (ReedSolomon.code domain k : Set (ι → F)) δ
              (spikeWord₀ e g) (spikeWord₁ (F := F) e) γ then (1 : ℝ≥0∞) else 0) :=
    ENNReal.sum_le_tsum imG
  -- Compute the finite sum: each term is `q⁻¹ * 1`.
  have hsum_eq :
      (∑ γ ∈ imG, ($ᵖ F) γ *
          (if mcaEvent (ReedSolomon.code domain k : Set (ι → F)) δ
              (spikeWord₀ e g) (spikeWord₁ (F := F) e) γ then (1 : ℝ≥0∞) else 0)) =
        (t : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
    have hterm : ∀ γ ∈ imG, ($ᵖ F) γ *
        (if mcaEvent (ReedSolomon.code domain k : Set (ι → F)) δ
            (spikeWord₀ e g) (spikeWord₁ (F := F) e) γ then (1 : ℝ≥0∞) else 0)
          = (Fintype.card F : ℝ≥0∞)⁻¹ := by
      intro γ hγ
      rw [himG, Finset.mem_image] at hγ
      obtain ⟨j, -, rfl⟩ := hγ
      have hevent := mcaEvent_spike e g domain k δ ht_n hδ j
      rw [if_pos hevent, mul_one, PMF.uniformOfFintype_apply]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, himG_card, nsmul_eq_mul]
  -- Conclude.
  calc (t : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      = (t : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞)⁻¹ := by rw [ENNReal.div_eq_inv_mul, mul_comm]
    _ = _ := hsum_eq.symm
    _ ≤ _ := hsum_le

/-- **Main theorem: the `t`-spike floor for `ε_mca`.**

For `RS[F, domain, k]` over an `n`-point domain with `q := |F|`: whenever `t + k ≤ n`,
`t ≤ q`, and `(1 - δ)·n ≤ n - t + 1`, the explicit `t`-spike words force
`t / q ≤ ε_mca(RS[F, domain, k], δ)`.

This is genuinely new quantitative content (ABF26 §1, lower-bound direction). -/
theorem epsMCA_ge_spike (domain : ι ↪ F) (k t : ℕ) (δ : ℝ≥0)
    (ht_n : t + k ≤ Fintype.card ι) (ht_q : t ≤ Fintype.card F)
    (hδ : ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ (Fintype.card ι - t + 1 : ℕ)) :
    (t : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ := by
  classical
  -- Build the two injections from the cardinality hypotheses.
  obtain ⟨e⟩ : Nonempty (Fin t ↪ ι) :=
    Function.Embedding.nonempty_of_card_le (by simp only [Fintype.card_fin]; omega)
  obtain ⟨g⟩ : Nonempty (Fin t ↪ F) :=
    Function.Embedding.nonempty_of_card_le (by simp only [Fintype.card_fin]; exact ht_q)
  -- The per-`u` probability is below the supremum `ε_mca`.
  refine le_trans (pr_mcaEvent_spike_ge e g domain k δ ht_n hδ) ?_
  unfold epsMCA
  exact le_iSup (fun u : WordStack F (Fin 2) ι =>
    Pr_{let γ ← $ᵖ F}[mcaEvent (ReedSolomon.code domain k : Set (ι → F)) δ (u 0) (u 1) γ])
    (Code.finMapTwoWords (spikeWord₀ e g) (spikeWord₁ (F := F) e))

/-! ## Corollaries -/

/-- **Universal `1/q` floor (sanity anchor, `t = 1`).** For every non-full RS code
(`1 + k ≤ n`) and *every* radius `δ`, `1/q ≤ ε_mca(RS[F, domain, k], δ)`. There is no
hypothesis on `δ`: `(1 - δ)·n ≤ n` always holds in `ℝ≥0`. -/
theorem epsMCA_ge_inv_card (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (hk : 1 + k ≤ Fintype.card ι) :
    (Fintype.card F : ℝ≥0∞)⁻¹ ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ := by
  have ht_q : 1 ≤ Fintype.card F := Fintype.card_pos
  have hδ : ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ (Fintype.card ι - 1 + 1 : ℕ) := by
    have h1 : (1 - δ : ℝ≥0) ≤ 1 := tsub_le_self
    have hmul : ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := by
      calc ((1 - δ) * Fintype.card ι : ℝ≥0)
          ≤ 1 * (Fintype.card ι : ℝ≥0) := by
            exact mul_le_mul_of_nonneg_right h1 (zero_le _)
        _ = (Fintype.card ι : ℝ≥0) := one_mul _
    refine le_trans hmul ?_
    have : Fintype.card ι ≤ Fintype.card ι - 1 + 1 := by omega
    exact_mod_cast this
  have := epsMCA_ge_spike domain k 1 δ (by omega) ht_q hδ
  rwa [Nat.cast_one, one_div] at this

/-- **Endpoint floor at `δ = 1`.** At the maximal radius `δ = 1` the size hypothesis is
free, so for `t := min (n - k) q` we get `min (n - k, q) / q ≤ ε_mca(RS, 1)`. -/
theorem epsMCA_one_ge (domain : ι ↪ F) (k : ℕ) (hk : k ≤ Fintype.card ι) :
    ((min (Fintype.card ι - k) (Fintype.card F) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) 1 := by
  set t : ℕ := min (Fintype.card ι - k) (Fintype.card F) with ht_def
  have ht_n : t + k ≤ Fintype.card ι := by
    have : t ≤ Fintype.card ι - k := min_le_left _ _
    omega
  have ht_q : t ≤ Fintype.card F := min_le_right _ _
  have hδ : ((1 - (1 : ℝ≥0)) * Fintype.card ι : ℝ≥0) ≤ (Fintype.card ι - t + 1 : ℕ) := by
    rw [tsub_self, zero_mul]; exact zero_le _
  exact epsMCA_ge_spike domain k t 1 ht_n ht_q hδ

/-- **Refutation of the formalized §1 MCA prize for small fields.** If `q < 2^128·(n - k)`
(with `k ≥ 1`, `n ≥ k + 1`), then `ε* = 2^(-128) < ε_mca(RS[F, domain, k], 1)`. Together with
the endpoint-collapse finding this rules out any admissible prize threshold `δ* ≤ 1`. -/
theorem epsStar_lt_epsMCA_one_of_field_small (domain : ι ↪ F) (k : ℕ)
    (_hk : 1 ≤ k) (hn : k + 1 ≤ Fintype.card ι)
    (hsmall : Fintype.card F < 2 ^ (128 : ℕ) * (Fintype.card ι - k)) :
    (ProximityGap.epsStar : ℝ≥0∞) <
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) 1 := by
  classical
  set n := Fintype.card ι with hn_def
  set q := Fintype.card F with hq_def
  have hnk_pos : 0 < n - k := by omega
  have hq_pos : 0 < q := Fintype.card_pos
  -- `epsStar = 2^(-128)` cast to `ℝ≥0∞`.
  have hepsStar : (ProximityGap.epsStar : ℝ≥0∞) = (2 ^ (128 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [ProximityGap.epsStar]
    push_cast
    rw [one_div]
  rw [hepsStar]
  by_cases hcase : q ≤ n - k
  · -- Case `q ≤ n - k`: the floor is `≥ q/q = 1 > 2^(-128)`.
    have hmin : min (n - k) q = q := by rw [min_eq_right hcase]
    have hfloor := epsMCA_one_ge (F := F) domain k (by omega)
    rw [hmin] at hfloor
    have hqne : (q : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]; omega
    have hqtop : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top q
    have hself : (q : ℝ≥0∞) / (q : ℝ≥0∞) = 1 := ENNReal.div_self hqne hqtop
    rw [hself] at hfloor
    refine lt_of_lt_of_le ?_ hfloor
    rw [ENNReal.inv_lt_one]
    exact one_lt_pow₀ ENNReal.one_lt_two (by norm_num)
  · -- Case `q > n - k`: take `t := n - k`; floor `(n-k)/q > 2^(-128) ⟺ q < 2^128·(n-k)`.
    push Not at hcase
    have hmin : min (n - k) q = n - k := by rw [min_eq_left (le_of_lt hcase)]
    have hfloor := epsMCA_one_ge (F := F) domain k (by omega)
    rw [hmin] at hfloor
    refine lt_of_lt_of_le ?_ hfloor
    -- `2^(-128) < (n-k)/q ⟺ 2^(-128)·q < (n-k) ⟺ q < 2^128·(n-k)`.
    have hqne : (q : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]; omega
    have hqtop : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top q
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hqne) (Or.inl hqtop)]
    -- goal: `(2^128)⁻¹ * q < (n - k)`
    have hpow_pos : (0 : ℝ≥0∞) < 2 ^ (128 : ℕ) := by positivity
    have hpow_ne_zero : (2 ^ (128 : ℕ) : ℝ≥0∞) ≠ 0 := hpow_pos.ne'
    have hpow_ne_top : (2 ^ (128 : ℕ) : ℝ≥0∞) ≠ ⊤ := by finiteness
    have hq_lt : (q : ℝ≥0∞) < (2 ^ (128 : ℕ) : ℝ≥0∞) * ((n - k : ℕ) : ℝ≥0∞) := by
      have hcast : (q : ℝ≥0∞) < ((2 ^ (128 : ℕ) * (n - k) : ℕ) : ℝ≥0∞) := by
        exact_mod_cast hsmall
      calc (q : ℝ≥0∞) < ((2 ^ (128 : ℕ) * (n - k) : ℕ) : ℝ≥0∞) := hcast
        _ = (2 ^ (128 : ℕ) : ℝ≥0∞) * ((n - k : ℕ) : ℝ≥0∞) := by push_cast; ring
    rw [← ENNReal.div_eq_inv_mul,
      ENNReal.div_lt_iff (Or.inl hpow_ne_zero) (Or.inl hpow_ne_top)]
    calc (q : ℝ≥0∞) < (2 ^ (128 : ℕ) : ℝ≥0∞) * ((n - k : ℕ) : ℝ≥0∞) := hq_lt
      _ = ((n - k : ℕ) : ℝ≥0∞) * (2 ^ (128 : ℕ) : ℝ≥0∞) := mul_comm _ _

end ProximityGap
