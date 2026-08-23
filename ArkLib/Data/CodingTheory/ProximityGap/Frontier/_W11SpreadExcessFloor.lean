/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SpreadExcessLaw

/-!
# The agreement-planting floor and the growth obstruction to `SpreadExcessLaw` (#466 lane W11)

Companion to `Frontier/_SpreadExcessLaw.lean` (the bounded spread-excess law, live constant
`C = 3` after the referee kill of `C = 2`, kb `deltastar-466b-p5-referee-2026-07-01.md`).

## What is PROVEN here (axiom-clean)

* `mem_lineBadScalars_of_certificate` — the certificate lemma: an explicit codeword agreeing
  with the offset line word on `≥ a` points puts the scalar in the bad set.  This is the Lean
  form of the probe's per-γ certificates (`scripts/probes/probe_w11_c3_kill.py`).
* `plantWord` + `card_lineBadScalars_plant_ge` — the **agreement-planting construction**
  (the P5-referee constructive floor, generalized to blocks): given a codeword `h` agreeing
  with the direction `u₁` on `A = agreeSet h u₁` and `m` pairwise-disjoint blocks `T b` of
  size `≥ a − |A|` off `A`, the explicitly constructed offset `u₀ = plantWord …` has `≥ m`
  bad scalars — one per block, at ANY `m` distinct scalar values.
* `worstBad_ge_agreement_floor` — **the floor**: for every codeword `h` with
  `s := |agreeSet h u₁| < a`, `worstBad dom k a u₁ ≥ (n − s) / (a − s)`.
  For an *elevated* direction (`s = a − 1`) this is `n − a + 1`: LINEAR in `n`.
* `farDirection_spread64` — the growth family `u₁ = x⁶ + c·x⁴` (`spread2Dir dom 6 4 c`) is
  provably `a`-far for every `a ≥ 7`, every finite field, every injective domain, every
  `k ≤ 6`: `u₁ − codeword` is the evaluation of a monic sextic, so no codeword agrees on
  `≥ 7` points.
* `spread64_agreeSet_card_eq_six` — whenever the domain contains six points
  `±r₁, ±r₂, ±r₃`, the explicit degree-2 codeword
  `h = r₁²r₂²r₃² − (r₁²r₂² + r₁²r₃² + r₂²r₃²)·x²` agrees with
  `u₁ = x⁶ − (r₁²+r₂²+r₃²)·x⁴` on EXACTLY 6 points (elevated: `s = 6 = a − 1` at `a = 7`).
* `spreadExcessLaw_forces_monoBaseline_growth` — **the growth obstruction**: for every
  constant `C`, `SpreadExcessLaw C` forces `n − 6 ≤ C · monoBaseline dom 4 7` on every
  instance of the family (any finite field, any `n` with `49 ≤ 4n` whose domain has the six
  square-root points).  The monomial baseline is thus forced to grow LINEARLY in `n` at
  fixed `k = 4, a = 7`.
* `concrete_growth_instance` — instantiability certificate (honesty rule): the hypotheses of
  the growth obstruction are satisfiable (explicit 13-point domain over `ZMod 97`), so the
  obstruction is not vacuous.

## What is NOT proven here

No Lean claim that `SpreadExcessLaw C` is false: refuting it needs an UPPER bound on
`monoBaseline` (a sup over `q^n` offsets), which is search-evidence only
(`scripts/probes/_out_w11_c3_kill_*.txt`: certified spread counts follow the floor, the
monomial plateau does not).  The floor side here is complete and unconditional.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Finset

namespace ProximityGap.Frontier.W11SpreadExcessFloor

open ProximityGap.SpikeFloor ProximityGap.Ownership ProximityGap.Frontier.SpreadExcess

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## The certificate lemma -/

/-- A scalar with an explicit agreeing codeword is bad.  (The Lean form of the probe's
per-γ certificates.) -/
theorem mem_lineBadScalars_of_certificate (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ c : Fin n → F) (γ : F) (hc : c ∈ rsCode dom k)
    (hcert : a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card) :
    γ ∈ lineBadScalars dom k a u₀ u₁ := by
  classical
  unfold lineBadScalars
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ γ, c, hc, hcert⟩

/-! ## The agreement-planting construction -/

/-- The planted offset word: `0` on the agreement set (and off all blocks);
`−γ_b·(u₁ − h)` on block `T b`. -/
def plantWord (h u₁ : Fin n → F) {m : ℕ} (γ : Fin m → F)
    (T : Fin m → Finset (Fin n)) : Fin n → F :=
  fun l => ∑ b : Fin m, if l ∈ T b then -(γ b * (u₁ l - h l)) else 0

/-- On the agreement set of `h` with `u₁` (disjoint from every block), the planted word
vanishes. -/
theorem plantWord_eq_zero_of_mem_agree (h u₁ : Fin n → F) {m : ℕ} (γ : Fin m → F)
    (T : Fin m → Finset (Fin n)) (hA : ∀ b, Disjoint (T b) (agreeSet h u₁))
    {l : Fin n} (hl : l ∈ agreeSet h u₁) :
    plantWord h u₁ γ T l = 0 := by
  unfold plantWord
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [if_neg (fun hmem => (Finset.disjoint_left.mp (hA b)) hmem hl)]

/-- On block `T b` (blocks pairwise disjoint), the planted word is `−γ_b·(u₁ − h)`. -/
theorem plantWord_eq_of_mem_block (h u₁ : Fin n → F) {m : ℕ} (γ : Fin m → F)
    (T : Fin m → Finset (Fin n))
    (hdisj : ∀ b b' : Fin m, b ≠ b' → Disjoint (T b) (T b'))
    {b : Fin m} {l : Fin n} (hl : l ∈ T b) :
    plantWord h u₁ γ T l = -(γ b * (u₁ l - h l)) := by
  unfold plantWord
  rw [Finset.sum_eq_single b]
  · rw [if_pos hl]
  · intro b' _ hb'
    rw [if_neg (fun hmem => (Finset.disjoint_left.mp (hdisj b' b hb')) hmem hl)]
  · intro habs
    exact absurd (Finset.mem_univ b) habs

/-- The planted agreement: for each block `b`, the codeword `γ_b • h` agrees with the line
word `plantWord + γ_b • u₁` on all of `agreeSet h u₁ ∪ T b`. -/
theorem plant_agree_superset (h u₁ : Fin n → F) {m : ℕ} (γ : Fin m → F)
    (T : Fin m → Finset (Fin n))
    (hdisj : ∀ b b' : Fin m, b ≠ b' → Disjoint (T b) (T b'))
    (hA : ∀ b, Disjoint (T b) (agreeSet h u₁)) (b : Fin m) :
    agreeSet h u₁ ∪ T b ⊆
      agreeSet (fun i => γ b • h i)
        (fun i => plantWord h u₁ γ T i + γ b • u₁ i) := by
  intro l hl
  simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Finset.mem_union.mp hl with hmem | hmem
  · have hz := plantWord_eq_zero_of_mem_agree h u₁ γ T hA hmem
    have hagree : h l = u₁ l := by
      have := hmem
      simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    rw [hz, hagree, zero_add]
  · have hv := plantWord_eq_of_mem_block h u₁ γ T hdisj hmem
    rw [hv, smul_eq_mul, smul_eq_mul]
    ring

/-- **The planting lower bound.**  `m` pairwise-disjoint blocks off the agreement set, each
completing the agreement to `≥ a`, put `m` distinct scalars in the bad set of the planted
offset. -/
theorem card_lineBadScalars_plant_ge (dom : Fin n ↪ F) (k a : ℕ)
    (h u₁ : Fin n → F) (hh : h ∈ rsCode dom k)
    {m : ℕ} (γ : Fin m ↪ F) (T : Fin m → Finset (Fin n))
    (hdisj : ∀ b b' : Fin m, b ≠ b' → Disjoint (T b) (T b'))
    (hA : ∀ b, Disjoint (T b) (agreeSet h u₁))
    (hcard : ∀ b, a ≤ (agreeSet h u₁).card + (T b).card) :
    m ≤ (lineBadScalars dom k a (plantWord h u₁ γ T) u₁).card := by
  classical
  have hmem : ∀ b : Fin m,
      γ b ∈ lineBadScalars dom k a (plantWord h u₁ γ T) u₁ := by
    intro b
    refine mem_lineBadScalars_of_certificate dom k a _ u₁
      (fun i => γ b • h i) (γ b) (Submodule.smul_mem _ (γ b) hh) ?_
    have hsub := plant_agree_superset h u₁ γ T hdisj hA b
    have hunion : (agreeSet h u₁ ∪ T b).card
        = (agreeSet h u₁).card + (T b).card :=
      Finset.card_union_of_disjoint (hA b).symm
    calc a ≤ (agreeSet h u₁).card + (T b).card := hcard b
      _ = (agreeSet h u₁ ∪ T b).card := hunion.symm
      _ ≤ _ := Finset.card_le_card hsub
  calc m = (Finset.univ : Finset (Fin m)).card := by
        rw [Finset.card_univ, Fintype.card_fin]
    _ ≤ (lineBadScalars dom k a (plantWord h u₁ γ T) u₁).card := by
        refine Finset.card_le_card_of_injOn γ (fun b _ => hmem b) ?_
        exact Function.Injective.injOn γ.injective

/-! ## Disjoint blocks exist -/

/-- Greedy block extraction: a set of size `≥ m·w` contains `m` pairwise-disjoint
`w`-subsets. -/
theorem exists_disjoint_blocks {α : Type} [DecidableEq α] :
    ∀ (m : ℕ) (R : Finset α) (w : ℕ), m * w ≤ R.card →
      ∃ T : Fin m → Finset α, (∀ b, T b ⊆ R) ∧ (∀ b, (T b).card = w) ∧
        (∀ b b' : Fin m, b ≠ b' → Disjoint (T b) (T b'))
  | 0, _R, _w, _ => ⟨fun _ => ∅, fun b => b.elim0, fun b => b.elim0,
      fun b => b.elim0⟩
  | m + 1, R, w, hle => by
    have hsm : (m + 1) * w = m * w + w := by ring
    have hw : w ≤ R.card := le_trans (by rw [hsm]; exact Nat.le_add_left w (m * w)) hle
    obtain ⟨T₀, hT₀R, hT₀c⟩ := exists_subset_card_eq hw
    have h2 : m * w ≤ (R \ T₀).card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hT₀R, hT₀c]
      have : m * w + w ≤ R.card := by rw [← hsm]; exact hle
      omega
    obtain ⟨T', hsub, hcards, hdisj⟩ := exists_disjoint_blocks m (R \ T₀) w h2
    refine ⟨Fin.cases T₀ T', ?_, ?_, ?_⟩
    · intro b
      induction b using Fin.cases with
      | zero => simpa using hT₀R
      | succ i => simpa using fun x hx => Finset.sdiff_subset (hsub i hx)
    · intro b
      induction b using Fin.cases with
      | zero => simpa using hT₀c
      | succ i => simpa using hcards i
    · intro b b' hne
      induction b using Fin.cases with
      | zero =>
        induction b' using Fin.cases with
        | zero => exact absurd rfl hne
        | succ j =>
          simp only [Fin.cases_zero, Fin.cases_succ]
          exact Finset.disjoint_sdiff.mono_right (hsub j)
      | succ i =>
        induction b' using Fin.cases with
        | zero =>
          simp only [Fin.cases_zero, Fin.cases_succ]
          exact (Finset.disjoint_sdiff.mono_right (hsub i)).symm
        | succ j =>
          simp only [Fin.cases_succ]
          exact hdisj i j (fun hij => hne (by rw [hij]))

/-! ## The floor -/

/-- **The agreement floor.**  Any codeword `h` agreeing with the direction `u₁` on
`s < a` points forces `worstBad ≥ (n − s) / (a − s)`.  For an elevated direction
(`s = a − 1`) this is `n − a + 1`: LINEAR in `n`. -/
theorem worstBad_ge_agreement_floor (dom : Fin n ↪ F) (k a : ℕ)
    (h u₁ : Fin n → F) (hh : h ∈ rsCode dom k)
    (hfar : (agreeSet h u₁).card < a) :
    (n - (agreeSet h u₁).card) / (a - (agreeSet h u₁).card)
      ≤ worstBad dom k a u₁ := by
  classical
  set s : ℕ := (agreeSet h u₁).card with hs
  set w : ℕ := a - s with hw
  set m : ℕ := (n - s) / w with hm
  have hcompl : ((agreeSet h u₁)ᶜ : Finset (Fin n)).card = n - s := by
    rw [Finset.card_compl, ← hs, Fintype.card_fin]
  have hmw : m * w ≤ ((agreeSet h u₁)ᶜ : Finset (Fin n)).card := by
    rw [hcompl, hm]
    exact Nat.div_mul_le_self _ _
  obtain ⟨T, hTsub, hTcard, hTdisj⟩ :=
    exists_disjoint_blocks m ((agreeSet h u₁)ᶜ : Finset (Fin n)) w hmw
  have hmF : m ≤ Fintype.card F := by
    have h1 : m ≤ n - s := by rw [hm]; exact Nat.div_le_self _ _
    have h2 : n ≤ Fintype.card F := by
      calc n = Fintype.card (Fin n) := (Fintype.card_fin n).symm
        _ ≤ Fintype.card F := Fintype.card_le_of_embedding dom
    omega
  let γ : Fin m ↪ F :=
    (Fin.castLEEmb hmF).trans (Fintype.equivFin F).symm.toEmbedding
  have hA : ∀ b, Disjoint (T b) (agreeSet h u₁) := by
    intro b
    exact Finset.disjoint_left.mpr fun {x} hx hx' =>
      (Finset.mem_compl.mp (hTsub b hx)) hx'
  have hcard : ∀ b, a ≤ (agreeSet h u₁).card + (T b).card := by
    intro b
    rw [hTcard b, ← hs, hw]
    omega
  have hplant := card_lineBadScalars_plant_ge dom k a h u₁ hh γ T hTdisj hA hcard
  calc (n - s) / w = m := hm.symm
    _ ≤ (lineBadScalars dom k a (plantWord h u₁ γ T) u₁).card := hplant
    _ ≤ worstBad dom k a u₁ := by
        unfold worstBad
        exact Finset.le_sup
          (f := fun u₀ => (lineBadScalars dom k a u₀ u₁).card)
          (Finset.mem_univ (plantWord h u₁ γ T))

/-! ## The growth family `u₁ = x⁶ + c·x⁴` -/

/-- Agreement of two words is bounded by the degree of any nonzero polynomial vanishing on
the agreement points (through the injective domain). -/
theorem agreeSet_card_le_natDegree (dom : Fin n ↪ F) (u v : Fin n → F)
    (P : Polynomial F) (hP : P ≠ 0)
    (hpt : ∀ i, u i = v i → P.eval (dom i) = 0) :
    (agreeSet u v).card ≤ P.natDegree := by
  classical
  have himg : (agreeSet u v).image dom ⊆ P.roots.toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hagr : u i = v i := by
      have := hi
      simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact hpt i hagr
  calc (agreeSet u v).card = ((agreeSet u v).image dom).card :=
        (Finset.card_image_of_injective _ dom.injective).symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card himg
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P

/-- The direction-minus-codeword polynomial of the growth family is (essentially) monic of
degree 6. -/
theorem spread64_poly_facts (c : F) (Q : Polynomial F) (hQ : Q.degree < 6) :
    (Polynomial.X ^ 6 + Polynomial.C c * Polynomial.X ^ 4 - Q).natDegree = 6 ∧
      (Polynomial.X ^ 6 + Polynomial.C c * Polynomial.X ^ 4 - Q) ≠ 0 := by
  have hlow : (Polynomial.C c * Polynomial.X ^ 4 - Q).degree < 6 := by
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ hQ)
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le 4 c) (by norm_num)
  have hdeg : (Polynomial.X ^ 6 + Polynomial.C c * Polynomial.X ^ 4 - Q).degree = 6 := by
    rw [add_sub_assoc]
    rw [Polynomial.degree_add_eq_left_of_degree_lt
      (by rw [Polynomial.degree_X_pow]; exact hlow)]
    exact Polynomial.degree_X_pow 6
  refine ⟨Polynomial.natDegree_eq_of_degree_eq_some hdeg, ?_⟩
  intro h0
  rw [h0, Polynomial.degree_zero] at hdeg
  exact absurd hdeg (by simp)

/-- **Farness of the growth family** — unconditional: `x⁶ + c·x⁴` agrees with NO codeword
of `rsCode dom k` (`k ≤ 6`) on more than 6 points, over every finite field and every
injective domain. -/
theorem spread64_agreement_le_six (dom : Fin n ↪ F) {k : ℕ} (hk : k ≤ 6) (c : F)
    (cw : Fin n → F) (hcw : cw ∈ rsCode dom k) :
    (agreeSet cw (spread2Dir dom 6 4 c)).card ≤ 6 := by
  obtain ⟨Q, hQdeg, rfl⟩ := hcw
  have hQ6 : Q.degree < 6 :=
    lt_of_lt_of_le hQdeg (by exact_mod_cast hk)
  obtain ⟨hdeg, hne⟩ := spread64_poly_facts c Q hQ6
  have hcard := agreeSet_card_le_natDegree dom
    (fun i => Q.eval (dom i)) (spread2Dir dom 6 4 c)
    (Polynomial.X ^ 6 + Polynomial.C c * Polynomial.X ^ 4 - Q) hne ?_
  · omega
  · intro i hagree
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, hagree, spread2Dir]
    ring

/-- The growth family is `a`-far for every `a ≥ 7` (in `FarDirection` form). -/
theorem farDirection_spread64 (dom : Fin n ↪ F) {k a : ℕ} (hk : k ≤ 6)
    (ha : 7 ≤ a) (c : F) :
    FarDirection dom k a (spread2Dir dom 6 4 c) := by
  intro cw hcw
  have := spread64_agreement_le_six dom hk c cw hcw
  omega

/-- The elevated codeword of the growth family. -/
def elevatedCodeword (dom : Fin n ↪ F) (r₁ r₂ r₃ : F) : Fin n → F :=
  fun i => r₁ ^ 2 * r₂ ^ 2 * r₃ ^ 2
    - (r₁ ^ 2 * r₂ ^ 2 + r₁ ^ 2 * r₃ ^ 2 + r₂ ^ 2 * r₃ ^ 2) * dom i ^ 2

theorem elevatedCodeword_mem (dom : Fin n ↪ F) {k : ℕ} (hk : 3 ≤ k)
    (r₁ r₂ r₃ : F) : elevatedCodeword dom r₁ r₂ r₃ ∈ rsCode dom k := by
  refine ⟨Polynomial.C (r₁ ^ 2 * r₂ ^ 2 * r₃ ^ 2)
    - Polynomial.C (r₁ ^ 2 * r₂ ^ 2 + r₁ ^ 2 * r₃ ^ 2 + r₂ ^ 2 * r₃ ^ 2)
      * Polynomial.X ^ 2, ?_, ?_⟩
  · refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast (show 0 < k by omega))
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le 2 _) (by exact_mod_cast hk)
  · funext i
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    rfl

/-- The key pointwise factorization: direction minus elevated codeword is the sextic
`(x² − r₁²)(x² − r₂²)(x² − r₃²)` evaluated on the domain. -/
theorem spread64_sub_elevated (dom : Fin n ↪ F) (r₁ r₂ r₃ : F) (i : Fin n) :
    spread2Dir dom 6 4 (-(r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2)) i
      - elevatedCodeword dom r₁ r₂ r₃ i
    = (dom i ^ 2 - r₁ ^ 2) * (dom i ^ 2 - r₂ ^ 2) * (dom i ^ 2 - r₃ ^ 2) := by
  simp only [elevatedCodeword, spread2Dir]
  ring

/-- **Elevated agreement, exactly six points.**  If the domain contains
`±r₁, ±r₂, ±r₃` (six index points), the elevated codeword agrees with the growth direction
`spread2Dir dom 6 4 (−(r₁²+r₂²+r₃²))` on EXACTLY six points. -/
theorem spread64_agreeSet_card_eq_six (dom : Fin n ↪ F) (r₁ r₂ r₃ : F)
    (e : Fin 6 ↪ Fin n)
    (h0 : dom (e 0) = r₁) (h1 : dom (e 1) = -r₁)
    (h2 : dom (e 2) = r₂) (h3 : dom (e 3) = -r₂)
    (h4 : dom (e 4) = r₃) (h5 : dom (e 5) = -r₃) :
    (agreeSet (elevatedCodeword dom r₁ r₂ r₃)
      (spread2Dir dom 6 4 (-(r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2)))).card = 6 := by
  classical
  have hle : (agreeSet (elevatedCodeword dom r₁ r₂ r₃)
      (spread2Dir dom 6 4 (-(r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2)))).card ≤ 6 :=
    spread64_agreement_le_six dom (le_refl 6) _ _
      (elevatedCodeword_mem dom (by norm_num) r₁ r₂ r₃)
  have hagree : ∀ j : Fin 6, e j ∈ agreeSet (elevatedCodeword dom r₁ r₂ r₃)
      (spread2Dir dom 6 4 (-(r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2))) := by
    intro j
    simp only [agreeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hz : spread2Dir dom 6 4 (-(r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2)) (e j)
        - elevatedCodeword dom r₁ r₂ r₃ (e j) = 0 := by
      rw [spread64_sub_elevated]
      fin_cases j
      · change (dom (e 0) ^ 2 - r₁ ^ 2) * (dom (e 0) ^ 2 - r₂ ^ 2) *
          (dom (e 0) ^ 2 - r₃ ^ 2) = 0
        rw [h0]
        ring
      · change (dom (e 1) ^ 2 - r₁ ^ 2) * (dom (e 1) ^ 2 - r₂ ^ 2) *
          (dom (e 1) ^ 2 - r₃ ^ 2) = 0
        rw [h1]
        ring
      · change (dom (e 2) ^ 2 - r₁ ^ 2) * (dom (e 2) ^ 2 - r₂ ^ 2) *
          (dom (e 2) ^ 2 - r₃ ^ 2) = 0
        rw [h2]
        ring
      · change (dom (e 3) ^ 2 - r₁ ^ 2) * (dom (e 3) ^ 2 - r₂ ^ 2) *
          (dom (e 3) ^ 2 - r₃ ^ 2) = 0
        rw [h3]
        ring
      · change (dom (e 4) ^ 2 - r₁ ^ 2) * (dom (e 4) ^ 2 - r₂ ^ 2) *
          (dom (e 4) ^ 2 - r₃ ^ 2) = 0
        rw [h4]
        ring
      · change (dom (e 5) ^ 2 - r₁ ^ 2) * (dom (e 5) ^ 2 - r₂ ^ 2) *
          (dom (e 5) ^ 2 - r₃ ^ 2) = 0
        rw [h5]
        ring
    exact (sub_eq_zero.mp hz).symm
  have hge : 6 ≤ (agreeSet (elevatedCodeword dom r₁ r₂ r₃)
      (spread2Dir dom 6 4 (-(r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2)))).card := by
    have hsub : (Finset.univ : Finset (Fin 6)).image (fun j => e j)
        ⊆ agreeSet (elevatedCodeword dom r₁ r₂ r₃)
            (spread2Dir dom 6 4 (-(r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2))) := by
      intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact hagree j
    calc (6 : ℕ)
        = ((Finset.univ : Finset (Fin 6)).image (fun j => e j)).card := by
          rw [Finset.card_image_of_injective _ e.injective, Finset.card_univ,
            Fintype.card_fin]
      _ ≤ _ := Finset.card_le_card hsub
  omega

/-! ## The growth obstruction -/

/-- **`SpreadExcessLaw C` forces the monomial baseline to grow linearly in `n`.**
On every instance of the growth family (any finite field, any injective domain containing
six points `±r₁, ±r₂, ±r₃`, any `n` with `49 ≤ 4n`), the law at constant `C` forces
`n − 6 ≤ C · monoBaseline dom 4 7`.

The floor side is unconditional (`worstBad ≥ n − 6` for the elevated direction, which is
provably 7-far); only the baseline upper bound is open.  Hence `SpreadExcessLaw C` at ANY
constant `C` stands or falls with the measurable question "does the monomial worst-offset
count at `(k, a) = (4, 7)` grow linearly in `n`?" — probe data
(`scripts/probes/_out_w11_c3_kill_*.txt`) says it plateaus while the certified spread count
follows the floor. -/
theorem spreadExcessLaw_forces_monoBaseline_growth {C : ℕ}
    (hlaw : SpreadExcessLaw C)
    (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) [NeZero n] (dom : Fin n ↪ F)
    (r₁ r₂ r₃ : F) (e : Fin 6 ↪ Fin n)
    (h0 : dom (e 0) = r₁) (h1 : dom (e 1) = -r₁)
    (h2 : dom (e 2) = r₂) (h3 : dom (e 3) = -r₂)
    (h4 : dom (e 4) = r₃) (h5 : dom (e 5) = -r₃)
    (hwin : 7 * 7 ≤ n * 4) :
    n - 6 ≤ C * monoBaseline dom 4 7 := by
  classical
  have hfar : FarDirection dom 4 7
      (spread2Dir dom 6 4 (-(r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2))) :=
    farDirection_spread64 dom (by norm_num) (le_refl 7) _
  have hlaw' : worstBad dom 4 7 (spread2Dir dom 6 4 (-(r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2)))
      ≤ C * monoBaseline dom 4 7 :=
    hlaw F n dom 4 7 6 4 (-(r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2)) (by norm_num) hwin hfar
  have hcard := spread64_agreeSet_card_eq_six dom r₁ r₂ r₃ e h0 h1 h2 h3 h4 h5
  have hfloor := worstBad_ge_agreement_floor dom 4 7
    (elevatedCodeword dom r₁ r₂ r₃)
    (spread2Dir dom 6 4 (-(r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2)))
    (elevatedCodeword_mem dom (by norm_num) r₁ r₂ r₃) (by rw [hcard]; norm_num)
  rw [hcard] at hfloor
  norm_num at hfloor
  have hdir : -(r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2) = -r₃ ^ 2 + (-r₂ ^ 2 + -r₁ ^ 2) := by
    ring
  rw [← hdir] at hfloor
  have hfloor' : n - 6 ≤
      worstBad dom 4 7 (spread2Dir dom 6 4 (-(r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2))) := by
    omega
  exact le_trans hfloor' hlaw'

/-! ## Instantiability certificate (non-vacuity)

An explicit 13-point domain over `ZMod 97` containing `±2, ±5, ±3`, so the
growth-obstruction hypotheses are satisfiable and the theorem has content. -/

/-- 13 distinct points of `ZMod 97`: `2, −2, 5, −5, 3, −3` then seven fillers. -/
def dom97 : Fin 13 → ZMod 97 :=
  ![2, 95, 5, 92, 3, 94, 0, 1, 4, 6, 7, 8, 9]

theorem dom97_injective : Function.Injective dom97 := by decide

local instance fact97 : Fact (Nat.Prime 97) := ⟨by decide⟩

/-- The growth obstruction is NON-VACUOUS: a concrete instance over `ZMod 97`
(`n = 13` is the smallest window scale `49 ≤ 4n`). -/
theorem concrete_growth_instance {C : ℕ} (hlaw : SpreadExcessLaw C) :
    7 ≤ C * monoBaseline (⟨dom97, dom97_injective⟩ : Fin 13 ↪ ZMod 97) 4 7 := by
  have hgrow := spreadExcessLaw_forces_monoBaseline_growth hlaw (ZMod 97) 13
    (⟨dom97, dom97_injective⟩ : Fin 13 ↪ ZMod 97) 2 5 3
    (Fin.castLEEmb (by norm_num : (6 : ℕ) ≤ 13))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by norm_num)
  simpa using hgrow

/-! ## Source audit -/

#print axioms mem_lineBadScalars_of_certificate
#print axioms card_lineBadScalars_plant_ge
#print axioms exists_disjoint_blocks
#print axioms worstBad_ge_agreement_floor
#print axioms spread64_agreement_le_six
#print axioms farDirection_spread64
#print axioms spread64_agreeSet_card_eq_six
#print axioms spreadExcessLaw_forces_monoBaseline_growth
#print axioms concrete_growth_instance

end ProximityGap.Frontier.W11SpreadExcessFloor
