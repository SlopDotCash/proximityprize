/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# Collapse analysis of the §1 Grand-Challenge encodings (Finding F6)

The `Prop`-valued encodings `grandMCAChallenge` / `grandListDecodingChallenge` in
`GrandChallenges.lean` ask for a **maximal real threshold** `δ* ∈ [0,1]`: the bound holds
at `δ*` and fails **strictly above** it. This file proves that, over a finite field and a
finite index set, both encodings **collapse**:

* `epsMCA C δ` and `Lambda (C^⋈ m) δ` are *right-continuous step functions* of `δ` — they
  depend on `δ` only through `⌊δ · |ι|⌋` (`epsMCA_eq_of_floor_eq`, `Lambda_eq_of_floor_eq`;
  the level-set structure of ABF26 Remark 4.2, here pushed through `mcaEvent` and
  `closeCodewordsRel`).
* Consequently no `δ* < 1` can satisfy the strict-failure clause: points immediately above
  `δ*` in the same `1/n`-level set have the *same* error value
  (`exists_gt_le_one_floor_eq`). Any witness is forced to `δ* = 1`, where the maximality
  clause is **vacuous** (there is no `δ` with `1 < δ ≤ 1`).
* Therefore (`grandMCAChallenge_iff_epsMCA_one`, `grandListDecodingChallenge_iff_Lambda_one`):

  `grandMCAChallenge C ε* ↔ ε_mca(C, 1) ≤ ε*`
  `grandListDecodingChallenge C m ε* ↔ Λ(C^⋈m, 1) ≤ ε* · |F|`

  — i.e. the encodings are equivalent to *radius-one* statements that do not mention any
  threshold structure at all.
* At radius one, `Λ(C^⋈m, 1)` is the **whole code** (`Lambda_one_eq_ncard`: every word is
  within relative distance `1` of everything), so the right-hand side fails whenever the
  code has at least `|F| > ε*·|F|` elements. The interleaving of any Reed-Solomon code with
  `0 < k` contains all constants, hence `grandListDecodingChallengeRS` is **provably
  false** in the prize regime, and the formal `listDecodingPrize` predicate is **refuted**
  (`not_listDecodingPrize`) for every domain with at least two points.

## What this means (honest scope)

This is a *statement-defect* finding about the Lean encodings (the same bug class as the
campaign findings F1–F5: the off-lattice C3.8, the over-strong `htele`, …), **not** a
resolution of the ABF26 prize. The paper's Grand Challenges ask to **determine** the value
of the largest *lattice* threshold `δ*_C` (relative distances live on `{0, 1/n, …, 1}`);
an existence-form encoding over real `δ` with a strict-failure clause cannot capture that:
on the `1/n`-lattice the maximal threshold *trivially exists* (a finite, downward-closed,
nonempty set has a maximum), and over the reals the supremum is generically not attained,
forcing the collapse proved here. The mathematical content of the prize — locating `δ*_C`
between the Johnson radius and capacity — is untouched and remains open; see
`CapacityBounds.lean` and the witness framework in `GrandChallenges.lean`, which are the
faithful encodings of prize *progress*.

## Main results

* `mcaEvent_iff_of_floor_eq`, `epsMCA_eq_of_floor_eq` — `ε_mca` is a step function.
* `closeCodewordsRel_eq_of_floor_eq`, `Lambda_eq_of_floor_eq` — `Λ` is a step function.
* `grandMCAChallenge_iff_epsMCA_one` — the MCA challenge collapses to radius one.
* `mcaPrize_iff_forall_epsMCA_one` — the formal MCA prize is a radius-one statement.
* `Lambda_one_eq_ncard`, `grandListDecodingChallenge_iff_Lambda_one` — the list-decoding
  challenge collapses to radius one.
* `not_grandListDecodingChallengeRS_of_pos` — the RS list-decoding challenge is false
  whenever `0 < k`, `0 < m`, `ε* < 1`.
* `not_listDecodingPrize` — the formal §1 list-decoding prize predicate is **false** for
  every evaluation domain with `2 ≤ |ι|` and every `0 < m`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

section StepStructure

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Level-set structure of `mcaEvent` (ABF26 Remark 4.2 for `ε_mca`).** The radius `δ`
enters `mcaEvent` only through the witness-size clause `|S| ≥ (1-δ)·n`, which for natural
`|S|` is determined by `⌊δ·n⌋` (`relDist_floor_bound_iff_complement_bound`). -/
theorem mcaEvent_iff_of_floor_eq (C : Set (ι → A)) {δ δ' : ℝ≥0} (u₀ u₁ : ι → A) (γ : F)
    (h : Nat.floor (δ * Fintype.card ι) = Nat.floor (δ' * Fintype.card ι)) :
    mcaEvent C δ u₀ u₁ γ ↔ mcaEvent C δ' u₀ u₁ γ := by
  unfold mcaEvent
  refine exists_congr fun S => ?_
  have hsize : ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι) ↔
      ((S.card : ℝ≥0) ≥ (1 - δ') * Fintype.card ι) := by
    rw [ge_iff_le, ← relDist_floor_bound_iff_complement_bound, h,
      relDist_floor_bound_iff_complement_bound, ← ge_iff_le]
  exact and_congr_left fun _ => hsize

/-- **`ε_mca` is a step function of the radius**: it depends on `δ` only through
`⌊δ · |ι|⌋`. This is the `ε_mca` analogue of `epsCA_eq_of_floor_eq`. -/
theorem epsMCA_eq_of_floor_eq (C : Set (ι → A)) {δ δ' : ℝ≥0}
    (h : Nat.floor (δ * Fintype.card ι) = Nat.floor (δ' * Fintype.card ι)) :
    epsMCA (F := F) C δ = epsMCA (F := F) C δ' := by
  unfold epsMCA
  refine iSup_congr fun u => ?_
  exact Pr_congr fun γ => mcaEvent_iff_of_floor_eq C (u 0) (u 1) γ h

/-- Strictly above any `δ < 1` there is a radius in the *same* `1/n`-level set. This is
the witness that defeats the strict-failure clause of the Grand-Challenge encodings. -/
lemma exists_gt_le_one_floor_eq (n : ℕ) {δ : ℝ≥0} (hδ : δ < 1) :
    ∃ δ' : ℝ≥0, δ < δ' ∧ δ' ≤ 1 ∧
      Nat.floor (δ' * n) = Nat.floor (δ * n) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact ⟨1, hδ, le_refl 1, by simp [hn]⟩
  · -- Work inside the level set `[⌊δn⌋/n, (⌊δn⌋+1)/n)`.
    set j : ℕ := Nat.floor (δ * n) with hj
    have hnne : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
    -- `δ < (j+1)/n` since `δ·n < j+1`.
    have hδn_lt : δ * n < ((j : ℝ≥0) + 1) := by
      exact_mod_cast Nat.lt_floor_add_one (δ * (n : ℝ≥0))
    have hδ_lt_step : δ < ((j : ℝ≥0) + 1) / n := by
      rw [lt_div_iff₀ (by positivity)]
      exact hδn_lt
    set b : ℝ≥0 := min (((j : ℝ≥0) + 1) / n) 1 with hb
    have hδ_lt_b : δ < b := lt_min hδ_lt_step hδ
    have hmid_gt : δ < (δ + b) / 2 := by
      rw [lt_div_iff₀ two_pos, mul_two]
      gcongr
    have hmid_lt_b : (δ + b) / 2 < b := by
      rw [div_lt_iff₀ two_pos, mul_two]
      gcongr
    refine ⟨(δ + b) / 2, hmid_gt, ?_, ?_⟩
    · -- `(δ + b)/2 ≤ 1`
      exact le_of_lt (lt_of_lt_of_le hmid_lt_b (min_le_right _ _))
    · -- same floor
      -- upper: `((δ+b)/2)·n < (j+1)` so the floor is `≤ j`.
      have hup : ((δ + b) / 2) * n < (j : ℝ≥0) + 1 := by
        have hb_le : b ≤ ((j : ℝ≥0) + 1) / n := min_le_left _ _
        have hstep : ((δ + b) / 2) * n < b * n := by
          exact mul_lt_mul_of_pos_right hmid_lt_b (by positivity)
        refine lt_of_lt_of_le hstep ?_
        calc b * n ≤ (((j : ℝ≥0) + 1) / n) * n := by gcongr
          _ = (j : ℝ≥0) + 1 := by rw [div_mul_cancel₀ _ hnne]
      have hfloor_le : Nat.floor (((δ + b) / 2) * (n : ℝ≥0)) ≤ j := by
        have hup' : ((δ + b) / 2) * (n : ℝ≥0) < ((j + 1 : ℕ) : ℝ≥0) := by
          push_cast
          exact hup
        have := (Nat.floor_lt (zero_le _)).mpr hup'
        omega
      -- lower: floor is monotone.
      have hfloor_ge : j ≤ Nat.floor (((δ + b) / 2) * (n : ℝ≥0)) := by
        refine Nat.floor_le_floor ?_
        exact mul_le_mul_of_nonneg_right hmid_gt.le (zero_le _)
      omega

/-- **Collapse of the Grand MCA Challenge encoding (Finding F6a).** Over a finite field
and finite index set, the existence-of-a-maximal-real-threshold encoding is equivalent to
the radius-one bound `ε_mca(C, 1) ≤ ε*`: the step structure of `ε_mca` forbids any
maximal witness `δ* < 1`, and at `δ* = 1` the strict-failure clause is vacuous. -/
theorem grandMCAChallenge_iff_epsMCA_one (C : LinearCode ι F) (ε_star : ℝ≥0) :
    grandMCAChallenge C ε_star ↔
      epsMCA (F := F) (A := F) ((C : Set (ι → F))) 1 ≤ (ε_star : ENNReal) := by
  constructor
  · rintro ⟨δs, hle1, hbound, hmax⟩
    rcases eq_or_lt_of_le hle1 with heq | hlt
    · rwa [heq] at hbound
    · exfalso
      obtain ⟨δ', hgt, hle1', hfloor⟩ := exists_gt_le_one_floor_eq (Fintype.card ι) hlt
      have hfail := hmax δ' hgt hle1'
      rw [epsMCA_eq_of_floor_eq (F := F) ((C : Set (ι → F))) hfloor] at hfail
      exact absurd hbound (not_le.mpr hfail)
  · intro h
    exact ⟨1, le_refl 1, h, fun δ h1 h2 => absurd (lt_of_lt_of_le h1 h2) (lt_irrefl 1)⟩

/-- The formal §1 MCA prize predicate is equivalent to four radius-one bounds. The
threshold structure the paper asks about ("determine the largest `δ*`") is absent from
the formal statement: only `ε_mca(·, 1)` matters. -/
theorem mcaPrize_iff_forall_epsMCA_one (domain : ι ↪ F) :
    GrandChallenges.mcaPrize domain ↔
      ∀ j : Fin 4,
        epsMCA (F := F) (A := F)
          ((ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ :
            Set (ι → F))) 1 ≤ (epsStar : ENNReal) := by
  unfold GrandChallenges.mcaPrize GrandChallenges.grandMCAChallengeRSrate
    GrandChallenges.grandMCAChallengeRS
  exact forall_congr' fun j => grandMCAChallenge_iff_epsMCA_one _ _

end StepStructure

section LambdaStep

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open ListDecodable in
/-- **Level-set structure of `closeCodewordsRel`** for radii coming from `ℝ≥0`: membership
depends on the radius only through `⌊δ · |ι|⌋`, because relative Hamming distance takes
values in `{0, 1/n, …, 1}`. -/
theorem closeCodewordsRel_eq_of_floor_eq {α : Type}
    (C : Set (ι → α)) (f : ι → α) {δ δ' : ℝ≥0}
    (h : Nat.floor (δ * Fintype.card ι) = Nat.floor (δ' * Fintype.card ι)) :
    closeCodewordsRel C f (δ : ℝ) = closeCodewordsRel C f (δ' : ℝ) := by
  classical
  unfold closeCodewordsRel relHammingBall
  ext c
  have key : ∀ ρ : ℝ≥0, ((relHammingDist f c : ℚ≥0) : ℝ) ≤ (ρ : ℝ) ↔
      hammingDist f c ≤ Nat.floor (ρ * Fintype.card ι) := by
    intro ρ
    have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
      exact_mod_cast Fintype.card_pos
    rw [Nat.le_floor_iff (zero_le _)]
    unfold relHammingDist
    push_cast
    rw [div_le_iff₀ hcard]
    constructor
    · intro hle
      exact_mod_cast hle
    · intro hle
      exact_mod_cast hle
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hc, hd⟩
    exact ⟨hc, (key δ').mpr (h ▸ (key δ).mp hd)⟩
  · rintro ⟨hc, hd⟩
    exact ⟨hc, (key δ).mpr (h.symm ▸ (key δ').mp hd)⟩

open ListDecodable in
/-- **`Λ` is a step function of the radius** (for radii from `ℝ≥0`). -/
theorem Lambda_eq_of_floor_eq {α : Type}
    (C : Set (ι → α)) {δ δ' : ℝ≥0}
    (h : Nat.floor (δ * Fintype.card ι) = Nat.floor (δ' * Fintype.card ι)) :
    Lambda C (δ : ℝ) = Lambda C (δ' : ℝ) := by
  unfold Lambda
  exact iSup_congr fun f => by rw [closeCodewordsRel_eq_of_floor_eq C f h]

open ListDecodable in
/-- At radius one every codeword is close: `Λ(C, 1)` is the full code size. -/
theorem Lambda_one_eq_ncard {α : Type} [Nonempty α]
    (C : Set (ι → α)) :
    Lambda C (1 : ℝ) = (C.ncard : ℕ∞) := by
  classical
  unfold Lambda
  have hball : ∀ f : ι → α, closeCodewordsRel C f (1 : ℝ) = C := by
    intro f
    unfold closeCodewordsRel relHammingBall
    ext c
    simp only [Set.mem_setOf_eq]
    refine ⟨fun hc => hc.1, fun hc => ⟨hc, ?_⟩⟩
    exact_mod_cast (relHammingDist_le_one (u := f) (v := c))
  refine le_antisymm (iSup_le fun f => by rw [hball f]) ?_
  obtain ⟨a⟩ := (inferInstance : Nonempty α)
  exact le_iSup_of_le (fun _ => a) (by rw [hball (fun _ => a)])

open ListDecodable in
/-- **Collapse of the Grand List Decoding Challenge encoding (Finding F6b).** -/
theorem grandListDecodingChallenge_iff_Lambda_one
    (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) :
    grandListDecodingChallenge C m ε_star ↔
      (Lambda (C^⋈ (Fin m)) ((1 : ℝ≥0) : ℝ) : ENNReal) ≤
        ((ε_star : ENNReal) * (Fintype.card F : ENNReal)) := by
  constructor
  · rintro ⟨δs, hle1, hbound, hmax⟩
    rcases eq_or_lt_of_le hle1 with heq | hlt
    · rwa [heq] at hbound
    · exfalso
      obtain ⟨δ', hgt, hle1', hfloor⟩ := exists_gt_le_one_floor_eq (Fintype.card ι) hlt
      have hfail := hmax δ' hgt hle1'
      have hstep : Lambda (C^⋈ (Fin m)) ((δ' : ℝ≥0) : ℝ) =
          Lambda (C^⋈ (Fin m)) ((δs : ℝ≥0) : ℝ) :=
        Lambda_eq_of_floor_eq (C^⋈ (Fin m)) hfloor
      rw [hstep] at hfail
      exact absurd hbound (not_le.mpr hfail)
  · intro h
    exact ⟨1, le_refl 1, h, fun δ h1 h2 => absurd (lt_of_lt_of_le h1 h2) (lt_irrefl 1)⟩

end LambdaStep

section Refutation

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Constant words are Reed-Solomon codewords as soon as `0 < deg`. -/
lemma const_mem_reedSolomonCode (domain : ι ↪ F) {deg : ℕ} (hdeg : 0 < deg) (a : F) :
    (fun _ : ι => a) ∈ (ReedSolomon.code domain deg : Set (ι → F)) := by
  have hmem : Polynomial.C a ∈ Polynomial.degreeLT F deg := by
    rw [Polynomial.mem_degreeLT]
    calc (Polynomial.C a).degree ≤ 0 := Polynomial.degree_C_le
      _ < (deg : WithBot ℕ) := by exact_mod_cast hdeg
  have : (fun _ : ι => a) ∈ ReedSolomon.code domain deg := by
    rw [ReedSolomon.code, Submodule.mem_map]
    refine ⟨Polynomial.C a, hmem, ?_⟩
    funext i
    simp [ReedSolomon.evalOnPoints]
  exact this

/-- The `m`-fold interleaving of a code containing all constants has at least `|F|`
elements (the constant matrices). -/
lemma card_le_ncard_interleavedCodeSet
    (C : Set (ι → F)) {m : ℕ} (hm : 0 < m)
    (hconst : ∀ a : F, (fun _ : ι => a) ∈ C) :
    (Fintype.card F : ℕ∞) ≤ ((C^⋈ (Fin m)) : Set (Matrix ι (Fin m) F)).ncard := by
  classical
  have hinj : Set.InjOn (fun a : F => (Matrix.of fun _ _ => a : Matrix ι (Fin m) F))
      Set.univ := by
    intro a _ b _ hab
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    have := congrFun (congrFun hab i) ⟨0, hm⟩
    simpa using this
  have hsub : (fun a : F => (Matrix.of fun _ _ => a : Matrix ι (Fin m) F)) '' Set.univ ⊆
      ((C^⋈ (Fin m)) : Set (Matrix ι (Fin m) F)) := by
    rintro _ ⟨a, -, rfl⟩
    intro k
    exact hconst a
  have h1 : (Set.univ : Set F).ncard ≤
      ((C^⋈ (Fin m)) : Set (Matrix ι (Fin m) F)).ncard := by
    rw [← Set.InjOn.ncard_image hinj]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at h1
  exact_mod_cast h1

open ListDecodable in
/-- **The RS Grand List Decoding Challenge encoding is FALSE** whenever `0 < k`, `0 < m`,
`ε* < 1`: the collapse forces the radius-one bound, where `Λ` is the whole interleaved
code, which already contains `|F|` constants — more than `ε* · |F|`. -/
theorem not_grandListDecodingChallengeRS_of_pos
    (domain : ι ↪ F) {k m : ℕ} (hk : 0 < k) (hm : 0 < m) {ε_star : ℝ≥0}
    (hε : ε_star < 1) :
    ¬ GrandChallenges.grandListDecodingChallengeRS domain k m ε_star := by
  unfold GrandChallenges.grandListDecodingChallengeRS
  rw [grandListDecodingChallenge_iff_Lambda_one]
  intro hbound
  -- At radius one, `Λ` is the whole interleaved code …
  rw [show ((1 : ℝ≥0) : ℝ) = (1 : ℝ) by norm_num,
    Lambda_one_eq_ncard (α := Fin m → F)] at hbound
  -- … which contains at least `|F|` elements.
  have hbig := card_le_ncard_interleavedCodeSet
    (ReedSolomon.code domain k : Set (ι → F)) hm
    (const_mem_reedSolomonCode domain hk)
  -- So `|F| ≤ ε* · |F| < |F|`, a contradiction.
  have hq_le : (Fintype.card F : ENNReal) ≤
      (ε_star : ENNReal) * (Fintype.card F : ENNReal) := by
    refine le_trans ?_ hbound
    exact_mod_cast hbig
  have hq_pos : (0 : ENNReal) < (Fintype.card F : ENNReal) := by
    exact_mod_cast Fintype.card_pos
  have hq_ne_top : (Fintype.card F : ENNReal) ≠ ⊤ := by
    exact ENNReal.natCast_ne_top _
  have hε' : (ε_star : ENNReal) < 1 := by exact_mod_cast hε
  have hlt : (ε_star : ENNReal) * (Fintype.card F : ENNReal) <
      (Fintype.card F : ENNReal) := by
    calc (ε_star : ENNReal) * (Fintype.card F : ENNReal)
        = (Fintype.card F : ENNReal) * (ε_star : ENNReal) := mul_comm _ _
      _ < (Fintype.card F : ENNReal) * 1 :=
          ENNReal.mul_lt_mul_right hq_pos.ne' hq_ne_top hε'
      _ = (Fintype.card F : ENNReal) := mul_one _
  exact absurd (lt_of_le_of_lt hq_le hlt) (lt_irrefl _)

/-- **The formal §1 list-decoding prize predicate is FALSE** for every evaluation domain
with at least two points and every positive interleaving parameter: instantiating at the
rate `ρ = 1/2` gives `k = ⌊|ι|/2⌋ ≥ 1`, and `not_grandListDecodingChallengeRS_of_pos`
applies (with `ε* = 2⁻¹²⁸ < 1`).

This refutes the *encoding*, not the prize: the paper's challenge asks to **determine** a
lattice threshold, which the existence-form real-threshold statement cannot express. -/
theorem not_listDecodingPrize (domain : ι ↪ F) {m : ℕ} (hm : 0 < m)
    (hι : 2 ≤ Fintype.card ι) :
    ¬ GrandChallenges.listDecodingPrize domain m := by
  intro hprize
  have h0 := hprize 0
  have hrate : prizeRates 0 = 1 / 2 := by
    unfold prizeRates
    norm_num
  have hk : 0 < ⌊prizeRates 0 * (Fintype.card ι : ℝ≥0)⌋₊ := by
    rw [hrate]
    have h2 : ((1 : ℕ) : ℝ≥0) ≤ (1 / 2) * (Fintype.card ι : ℝ≥0) := by
      push_cast
      calc (1 : ℝ≥0) = (1 / 2) * 2 := by norm_num
        _ ≤ (1 / 2) * (Fintype.card ι : ℝ≥0) := by
            gcongr
            exact_mod_cast hι
    exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_floor h2)
  have hε : epsStar < 1 := by
    unfold epsStar
    rw [div_lt_one (by positivity)]
    exact one_lt_pow₀ one_lt_two (by norm_num)
  exact not_grandListDecodingChallengeRS_of_pos domain hk hm hε h0

end Refutation

end ProximityGap

