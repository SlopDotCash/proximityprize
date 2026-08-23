/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.UniversalBelowUDR

/-!
# The UDR-invariant puncture descent: gapless below-UDR at every rate, generic domain (#371)

The universal below-UDR dichotomy (`UniversalBelowUDR.lean`) covers `2w + 2k ≤ n`; its
edge band `n ∈ [2w+k+1, 2w+2k)` was closed on smooth domains by the radius-free
subset-ownership law (`UDREdgeClosure.lean`).  This file closes the band for **every**
injective evaluation domain by a new mechanism — the **γ-preserving puncture descent**:

For a direction `u₁` vanishing at a domain point `x₀ = dom i₀`, every line `u₀ + γ·u₁`
equals `u₀` at `x₀`, so every explainer passes through `(x₀, u₀ x₀)` regardless of `γ`.
Conditioning on `i₀ ∈ S` and dividing the entire instance by `(X − x₀)` — the words by
divided differences, the explainer by polynomial division — maps

  `(n, k, w)  →  (n − 1, k − 1, w)`   at the SAME `γ`,

with `mcaEvent → mcaEvent`: the explainer divides exactly (`punctureWord_mem`), and the
¬joint clause lifts back (`exists_lift_mem`: a child joint pair re-multiplies to a parent
joint pair on `S`, using `u₁ x₀ = 0` for the second row).  Crucially `n − k` — hence the
distance `n − k + 1`, hence the unique-decoding slack `σ = n − 2w − k` — is **invariant**,
so below-UDR instances descend to below-UDR instances.  Induction on `k` bottoms at the
in-tree `k = 1` universal law (whose edge band is empty).  The assembly dichotomy at each
level: far (`∀ c : agree ≤ w`) feeds the general-`k` multiplicity engine at `μ = w`;
near (`∃ c : agree ≥ w+1`) translates (`mcaEvent_translate`) and punctures (the witness
meets the direction's zero set: `|S ∩ Z| ≥ (n−w) + (w+1) − n ≥ 1`).

  **`#bad · (n − 2w − k) ≤ n^{k+1}` for every `2w + k + 1 ≤ n`, every rate, every stack,
  every injective evaluation domain** — one statement for the whole below-UDR range,
  no smoothness, no dichotomy residue.

Honest scope: on smooth domains in the band the subset budget `C(n,k+1)/((k+1)·p)` is
sharper, and on `2w + 2k ≤ n` the dichotomy budget `(n−2w−2k+1)^{−k}` is sharper; what
this adds is the first generic-domain band coverage, the single-statement form, and the
descent lemma itself as reusable technology (it is radius-agnostic — it also descends
above-UDR bad scalars whose witness meets the direction's zero set).

Probe: `scripts/probes/probe_edgeband_puncture.py` (exit 0) — faithful mcaEvent
semantics; band instances `(p,n,k,w) = (17,7,2,2), (13,9,2,3), (17,8,3,2), (17,9,3,2)`;
the descent preserved badness in 633/633 checked `(γ, x₀)` pairs.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## §1 The puncture dictionary -/

/-- The punctured evaluation domain: drop the point `i₀`. -/
def punctureDom {m : ℕ} (dom : Fin (m + 1) ↪ F) (i₀ : Fin (m + 1)) : Fin m ↪ F :=
  ⟨fun j => dom (i₀.succAbove j),
   fun _ _ h => Fin.succAbove_right_injective (dom.injective h)⟩

/-- The divided-difference puncture of a word at `i₀`. -/
def punctureWord {m : ℕ} (dom : Fin (m + 1) ↪ F) (i₀ : Fin (m + 1))
    (u : Fin (m + 1) → F) : Fin m → F :=
  fun j => (u (i₀.succAbove j) - u i₀) * (dom (i₀.succAbove j) - dom i₀)⁻¹

@[simp] theorem punctureDom_apply {m : ℕ} (dom : Fin (m + 1) ↪ F) (i₀ : Fin (m + 1))
    (j : Fin m) : punctureDom dom i₀ j = dom (i₀.succAbove j) := rfl

theorem punctureDom_sub_ne_zero {m : ℕ} (dom : Fin (m + 1) ↪ F) (i₀ : Fin (m + 1))
    (j : Fin m) : dom (i₀.succAbove j) - dom i₀ ≠ 0 :=
  sub_ne_zero.mpr fun h => Fin.succAbove_ne i₀ j (dom.injective h)

/-- Helper: degree of `(X − C x₀) * Q` is `< k + 1` when `degree Q < k`. -/
theorem degree_linear_mul_lt {k : ℕ} (x₀ : F) {Q : F[X]} (hQ : Q.degree < (k : ℕ)) :
    ((X - C x₀) * Q).degree < ((k + 1 : ℕ) : WithBot ℕ) := by
  by_cases hQ0 : Q = 0
  · subst hQ0
    rw [mul_zero, degree_zero]
    exact WithBot.bot_lt_coe _
  · rw [degree_mul, degree_X_sub_C]
    have hd : Q.degree = (Q.natDegree : WithBot ℕ) := degree_eq_natDegree hQ0
    rw [hd] at hQ ⊢
    have hnd : Q.natDegree < k := by exact_mod_cast hQ
    have : (1 : WithBot ℕ) + (Q.natDegree : WithBot ℕ) = ((1 + Q.natDegree : ℕ) : WithBot ℕ) := by
      push_cast; ring
    rw [this]
    exact_mod_cast by omega

/-- **The divided difference**: a polynomial of degree `< k + 1` splits as
`P = C (P.eval x₀) + (X − C x₀) * Q` with `degree Q < k`. -/
theorem exists_divided_difference (P : F[X]) {k : ℕ}
    (hdeg : P.degree < ((k + 1 : ℕ) : WithBot ℕ)) (x₀ : F) :
    ∃ Q : F[X], Q.degree < (k : ℕ) ∧ P = C (P.eval x₀) + (X - C x₀) * Q := by
  have hroot : (P - C (P.eval x₀)).IsRoot x₀ := by
    simp [Polynomial.IsRoot]
  obtain ⟨Q, hQ⟩ := (Polynomial.dvd_iff_isRoot).mpr hroot
  refine ⟨Q, ?_, ?_⟩
  · by_cases hQ0 : Q = 0
    · subst hQ0
      rw [degree_zero]
      exact WithBot.bot_lt_coe _
    · have hdegsub : (P - C (P.eval x₀)).degree < ((k + 1 : ℕ) : WithBot ℕ) :=
        lt_of_le_of_lt (degree_sub_le _ _)
          (max_lt hdeg (lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.succ_pos k)))
      rw [hQ, degree_mul, degree_X_sub_C] at hdegsub
      have hd : Q.degree = (Q.natDegree : WithBot ℕ) := degree_eq_natDegree hQ0
      rw [hd] at hdegsub ⊢
      have : (1 : WithBot ℕ) + (Q.natDegree : WithBot ℕ)
          = ((1 + Q.natDegree : ℕ) : WithBot ℕ) := by push_cast; ring
      rw [this] at hdegsub
      have hnd : 1 + Q.natDegree < k + 1 := by exact_mod_cast hdegsub
      exact_mod_cast by omega
  · exact sub_eq_iff_eq_add'.mp hQ

/-- The divided difference of a codeword is a codeword of one lower degree —
membership descends through the puncture. -/
theorem punctureWord_mem {m k : ℕ} (dom : Fin (m + 1) ↪ F) (i₀ : Fin (m + 1))
    {wd : Fin (m + 1) → F}
    (hwd : wd ∈ (rsCode dom (k + 1) : Submodule F (Fin (m + 1) → F))) :
    punctureWord dom i₀ wd
      ∈ (rsCode (punctureDom dom i₀) k : Submodule F (Fin m → F)) := by
  obtain ⟨P, hdeg, rfl⟩ := hwd
  obtain ⟨Q, hQdeg, hPQ⟩ := exists_divided_difference P hdeg (dom i₀)
  refine ⟨Q, hQdeg, ?_⟩
  funext j
  have hne := punctureDom_sub_ne_zero dom i₀ j
  have heval : P.eval (dom (i₀.succAbove j))
      = P.eval (dom i₀) + (dom (i₀.succAbove j) - dom i₀) * Q.eval (dom (i₀.succAbove j)) := by
    conv_lhs => rw [hPQ]
    simp [eval_add, eval_mul, eval_sub]
  show (P.eval (dom (i₀.succAbove j)) - P.eval (dom i₀))
      * (dom (i₀.succAbove j) - dom i₀)⁻¹ = Q.eval ((punctureDom dom i₀) j)
  rw [heval, punctureDom_apply]
  field_simp
  ring

/-- **The lift**: a child codeword re-multiplies to a parent codeword through any
prescribed value `a` at the punctured point. -/
theorem exists_lift_mem {m k : ℕ} (dom : Fin (m + 1) ↪ F) (i₀ : Fin (m + 1)) (a : F)
    {v : Fin m → F}
    (hv : v ∈ (rsCode (punctureDom dom i₀) k : Submodule F (Fin m → F))) :
    ∃ lw ∈ (rsCode dom (k + 1) : Submodule F (Fin (m + 1) → F)),
      lw i₀ = a ∧ ∀ j : Fin m,
        lw (i₀.succAbove j) = a + (dom (i₀.succAbove j) - dom i₀) * v j := by
  obtain ⟨Q, hQdeg, rfl⟩ := hv
  refine ⟨fun i => (C a + (X - C (dom i₀)) * Q).eval (dom i),
    ⟨C a + (X - C (dom i₀)) * Q,
      lt_of_le_of_lt (degree_add_le _ _)
        (max_lt (lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.succ_pos k))
          (degree_linear_mul_lt _ hQdeg)), rfl⟩, ?_, ?_⟩
  · simp [eval_add, eval_mul, eval_sub]
  · intro j
    simp [eval_add, eval_mul, eval_sub, punctureDom_apply]

/-- Witness bookkeeping: the punctured witness loses exactly the point `i₀`. -/
theorem card_filter_succAbove_mem {m : ℕ} (i₀ : Fin (m + 1)) (S : Finset (Fin (m + 1)))
    (hi₀ : i₀ ∈ S) :
    S.card = (Finset.univ.filter (fun j => i₀.succAbove j ∈ S)).card + 1 := by
  have himg : (Finset.univ.filter (fun j => i₀.succAbove j ∈ S)).image i₀.succAbove
      = S.erase i₀ := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Fin.succAbove_ne i₀ j, hj⟩
    · rintro ⟨hne, hmem⟩
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hne
      exact ⟨j, hmem, rfl⟩
  have h1 : (S.erase i₀).card
      = (Finset.univ.filter (fun j => i₀.succAbove j ∈ S)).card := by
    rw [← himg]
    exact Finset.card_image_of_injective _ (Fin.succAbove_right_injective (p := i₀))
  have h2 : (S.erase i₀).card = S.card - 1 := Finset.card_erase_of_mem hi₀
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i₀, hi₀⟩
  omega

/-! ## §2 The descent -/

open Classical in
/-- **THE γ-PRESERVING PUNCTURE DESCENT.**  If `γ` is MCA-bad for `(u₀, u₁)` at
dimension `k + 1` via a witness `S` containing a zero `i₀` of the direction, then `γ`
is MCA-bad for the punctured instance at dimension `k` on `m` points at the same
integer radius `w` — the explainer divides exactly, and a child joint pair would lift
to a parent joint pair on `S`. -/
theorem mcaEvent_puncture {m k w : ℕ} (hm : 0 < m) (hw : w ≤ m)
    (dom : Fin (m + 1) ↪ F) (i₀ : Fin (m + 1))
    {u₀ u₁ : Fin (m + 1) → F} (hz : u₁ i₀ = 0) {γ : F} {S : Finset (Fin (m + 1))}
    (hcardS : m + 1 - w ≤ S.card) (hi₀S : i₀ ∈ S)
    (hexp : ∃ wd ∈ (rsCode dom (k + 1) : Submodule F (Fin (m + 1) → F)),
      ∀ i ∈ S, wd i = u₀ i + γ • u₁ i)
    (hnj : ¬ pairJointAgreesOn
      ((rsCode dom (k + 1) : Submodule F (Fin (m + 1) → F)) : Set (Fin (m + 1) → F))
      S u₀ u₁) :
    mcaEvent (F := F)
      ((rsCode (punctureDom dom i₀) k : Submodule F (Fin m → F)) : Set (Fin m → F))
      ((w : ℝ≥0) / (m : ℝ≥0))
      (punctureWord dom i₀ u₀) (punctureWord dom i₀ u₁) γ := by
  obtain ⟨wd, hwdC, hag⟩ := hexp
  have hwd0 : wd i₀ = u₀ i₀ := by
    have h := hag i₀ hi₀S
    rw [hz] at h
    simpa using h
  refine ⟨Finset.univ.filter (fun j => i₀.succAbove j ∈ S), ?_, ?_, ?_⟩
  · -- card threshold
    have hcards := card_filter_succAbove_mem i₀ S hi₀S
    have hS'card : m - w ≤ (Finset.univ.filter (fun j => i₀.succAbove j ∈ S)).card := by
      omega
    rw [Fintype.card_fin]
    have hm0 : (m : ℝ≥0) ≠ 0 := by exact_mod_cast hm.ne'
    have h1 : ((1 : ℝ≥0) - (w : ℝ≥0) / (m : ℝ≥0)) * (m : ℝ≥0)
        = (m : ℝ≥0) - (w : ℝ≥0) := by
      rw [tsub_mul, one_mul, div_mul_cancel₀ _ hm0]
    rw [h1]
    have hcast : ((m - w : ℕ) : ℝ≥0) = (m : ℝ≥0) - (w : ℝ≥0) := Nat.cast_tsub m w
    rw [← hcast]
    exact_mod_cast hS'card
  · -- the explainer divides
    refine ⟨punctureWord dom i₀ wd, punctureWord_mem dom i₀ hwdC, ?_⟩
    intro j hj
    have hjS : i₀.succAbove j ∈ S := (Finset.mem_filter.mp hj).2
    have hagj := hag _ hjS
    show (wd (i₀.succAbove j) - wd i₀) * (dom (i₀.succAbove j) - dom i₀)⁻¹
        = (u₀ (i₀.succAbove j) - u₀ i₀) * (dom (i₀.succAbove j) - dom i₀)⁻¹
          + γ • ((u₁ (i₀.succAbove j) - u₁ i₀) * (dom (i₀.succAbove j) - dom i₀)⁻¹)
    rw [hagj, hwd0, hz, smul_eq_mul]
    ring
  · -- a child joint pair lifts to a parent joint pair on S
    rintro ⟨v₀, hv₀, v₁, hv₁, hagj⟩
    obtain ⟨lw₀, hlw₀C, hlw₀i₀, hlw₀⟩ := exists_lift_mem dom i₀ (u₀ i₀) hv₀
    obtain ⟨lw₁, hlw₁C, hlw₁i₀, hlw₁⟩ := exists_lift_mem dom i₀ 0 hv₁
    refine hnj ⟨lw₀, hlw₀C, lw₁, hlw₁C, fun i hiS => ?_⟩
    by_cases hii : i = i₀
    · subst hii
      exact ⟨by rw [hlw₀i₀], by rw [hlw₁i₀, hz]⟩
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hii
      have hjS' : j ∈ Finset.univ.filter (fun j => i₀.succAbove j ∈ S) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiS⟩
      obtain ⟨h0, h1⟩ := hagj j hjS'
      have hne := punctureDom_sub_ne_zero dom i₀ j
      constructor
      · rw [hlw₀ j, h0]
        show u₀ i₀ + (dom (i₀.succAbove j) - dom i₀)
            * ((u₀ (i₀.succAbove j) - u₀ i₀) * (dom (i₀.succAbove j) - dom i₀)⁻¹)
            = u₀ (i₀.succAbove j)
        field_simp
        ring
      · rw [hlw₁ j, h1]
        show (0 : F) + (dom (i₀.succAbove j) - dom i₀)
            * ((u₁ (i₀.succAbove j) - u₁ i₀) * (dom (i₀.succAbove j) - dom i₀)⁻¹)
            = u₁ (i₀.succAbove j)
        rw [hz]
        field_simp
        ring

/-! ## §3 The induction: gapless below-UDR at every rate, generic domain -/

open Classical in
/-- **THE FULL BELOW-UDR LAW (generic domain, one statement)**: for every `1 ≤ k`,
every stack, every injective evaluation domain, and every radius `δ ≤ w/n` with
`2w + k + 1 ≤ n` (the whole range strictly below unique decoding):

  `#bad · (n − 2w − k) ≤ n^{k+1}`.

Induction on `k` through the γ-preserving puncture descent; the in-tree `k = 1`
universal law is the base, the general-`k` multiplicity engine the far branch. -/
theorem belowUDR_badScalars_card_mul_le :
    ∀ (k : ℕ), 1 ≤ k → ∀ (n : ℕ), NeZero n → ∀ (dom : Fin n ↪ F) (w : ℕ)
      (δ : ℝ≥0) (u₀ u₁ : Fin n → F),
      δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w → 2 * w + k + 1 ≤ n →
      (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        * (n - 2 * w - k) ≤ n ^ (k + 1) := by
  intro k
  induction k with
  | zero => exact fun h => absurd h (by omega)
  | succ k ih =>
    intro _ n hnz dom w δ u₀ u₁ hδn hband
    haveI : NeZero n := hnz
    by_cases hk0 : k = 0
    · -- base: dimension 1, the in-tree universal law (its edge band is empty)
      subst hk0
      have h := generalK_badScalars_card_mul_le_universal dom (k := 1) le_rfl
        (by omega) hδn u₀ u₁
      have harith : n - 2 * w - 2 * 1 + 1 = n - 2 * w - 1 := by omega
      rw [harith, pow_one] at h
      exact h
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      by_cases hfar : ∀ c ∈ (rsCode dom (k + 1) : Submodule F (Fin n → F)),
          (agreeSet c u₁).card ≤ w
      · -- far branch: the general-k multiplicity engine at μ = w
        have hmult := badScalars_card_mul_le_of_agreement dom (k := k + 1)
          (by omega) hδn (u₀ := u₀) (u₁ := u₁) (μ := w) hfar
        have hcardfun : Fintype.card (Fin (k + 1 + 1) → Fin n) = n ^ (k + 2) := by
          rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
        rw [hcardfun] at hmult
        have hdesc : 0 < (n - w).descFactorial (k + 1) :=
          Nat.descFactorial_pos.mpr (by omega)
        have harith : n - w - (k + 1) - w = n - 2 * w - (k + 1) := by omega
        calc (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
                ((rsCode dom (k + 1) : Submodule F (Fin n → F)) : Set (Fin n → F))
                δ u₀ u₁ γ)).card * (n - 2 * w - (k + 1))
            ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
                ((rsCode dom (k + 1) : Submodule F (Fin n → F)) : Set (Fin n → F))
                δ u₀ u₁ γ)).card
              * ((n - w).descFactorial (k + 1) * (n - w - (k + 1) - w)) := by
              refine Nat.mul_le_mul_left _ ?_
              rw [harith]
              exact Nat.le_mul_of_pos_left _ hdesc
          _ ≤ n ^ (k + 2) := hmult
      · -- near branch: translate, then puncture at a zero of the direction
        push Not at hfar
        obtain ⟨c, hcC, hagc⟩ := hfar
        -- translate u₁ to ε := u₁ − c
        set ε : Fin n → F := u₁ - c with hε
        have hfilter : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom (k + 1) : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ))
            = (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom (k + 1) : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ ε γ)) := by
          refine Finset.filter_congr fun γ _ => ?_
          have h := ProximityGap.MCAEquivariance.mcaEvent_translate
            (rsCode dom (k + 1) : Submodule F (Fin n → F)) (δ := δ)
            (u₀ := u₀) (u₁ := ε) (c₀ := 0) (c₁ := c)
            ((rsCode dom (k + 1) : Submodule F (Fin n → F)).zero_mem) hcC γ
          have he0 : u₀ + 0 = u₀ := by funext i; simp
          have he1 : ε + c = u₁ := by funext i; simp [hε]
          rw [he0, he1] at h
          exact h
        rw [hfilter]
        -- destructure n = m + 1
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        haveI : NeZero m := ⟨by omega⟩
        -- the zero set of the direction
        set Z : Finset (Fin (m + 1)) := Finset.univ.filter (fun i => ε i = 0) with hZ
        have hZcard : w + 1 ≤ Z.card := by
          have hsub : agreeSet c u₁ ⊆ Z := by
            intro i hi
            have : c i = u₁ i := by
              have := (Finset.mem_filter.mp hi).2
              exact this
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            simp [hε, sub_eq_zero, this.symm]
          calc w + 1 ≤ (agreeSet c u₁).card := hagc
            _ ≤ Z.card := Finset.card_le_card hsub
        -- the cover: every bad scalar descends through some i₀ ∈ Z
        have hσeq : m + 1 - 2 * w - (k + 1) = m - 2 * w - k := by omega
        have hcover : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom (k + 1) : Submodule F (Fin (m + 1) → F)) : Set (Fin (m + 1) → F))
            δ u₀ ε γ)) ⊆
            Z.biUnion (fun i₀ => Finset.univ.filter (fun γ : F => mcaEvent (F := F)
              ((rsCode (punctureDom dom i₀) k : Submodule F (Fin m → F)) : Set (Fin m → F))
              ((w : ℝ≥0) / (m : ℝ≥0))
              (punctureWord dom i₀ u₀) (punctureWord dom i₀ ε) γ)) := by
          intro γ hγ
          obtain ⟨S, hScard, hexp, hnj⟩ := (Finset.mem_filter.mp hγ).2
          -- integer witness size
          have hδ1 : δ * ((m + 1 : ℕ) : ℝ≥0) ≤ w := by
            rw [Fintype.card_fin] at hδn
            exact_mod_cast hδn
          have hScardN : m + 1 - w ≤ S.card := by
            rw [Fintype.card_fin] at hScard
            have hub : ((m + 1 : ℕ) : ℝ≥0) - (w : ℝ≥0)
                ≤ ((1 : ℝ≥0) - δ) * ((m + 1 : ℕ) : ℝ≥0) := by
              rw [tsub_mul, one_mul]
              exact tsub_le_tsub_left hδ1 _
            have hcast : ((m + 1 - w : ℕ) : ℝ≥0) = ((m + 1 : ℕ) : ℝ≥0) - (w : ℝ≥0) :=
              Nat.cast_tsub (m + 1) w
            have : ((m + 1 - w : ℕ) : ℝ≥0) ≤ (S.card : ℝ≥0) := by
              rw [hcast]
              calc ((m + 1 : ℕ) : ℝ≥0) - (w : ℝ≥0)
                  ≤ ((1 : ℝ≥0) - δ) * ((m + 1 : ℕ) : ℝ≥0) := hub
                _ ≤ (S.card : ℝ≥0) := by exact_mod_cast hScard
            exact_mod_cast this
          -- the witness meets the zero set
          have hSZ : 0 < (S ∩ Z).card := by
            have h1 := Finset.card_union_add_card_inter S Z
            have h2 : (S ∪ Z).card ≤ m + 1 := by
              calc (S ∪ Z).card ≤ (Finset.univ : Finset (Fin (m + 1))).card :=
                    Finset.card_le_card (Finset.subset_univ _)
                _ = m + 1 := by rw [Finset.card_univ, Fintype.card_fin]
            omega
          obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp hSZ
          have hi₀S : i₀ ∈ S := (Finset.mem_inter.mp hi₀).1
          have hi₀Z : ε i₀ = 0 :=
            (Finset.mem_filter.mp (Finset.mem_inter.mp hi₀).2).2
          refine Finset.mem_biUnion.mpr ⟨i₀, (Finset.mem_inter.mp hi₀).2,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
          exact mcaEvent_puncture (by omega) (by omega) dom i₀ hi₀Z hScardN hi₀S hexp hnj
        -- count
        calc (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
                ((rsCode dom (k + 1) : Submodule F (Fin (m + 1) → F)) : Set (Fin (m + 1) → F))
                δ u₀ ε γ)).card * (m + 1 - 2 * w - (k + 1))
            ≤ (Z.biUnion (fun i₀ => Finset.univ.filter (fun γ : F => mcaEvent (F := F)
                ((rsCode (punctureDom dom i₀) k : Submodule F (Fin m → F)) : Set (Fin m → F))
                ((w : ℝ≥0) / (m : ℝ≥0))
                (punctureWord dom i₀ u₀) (punctureWord dom i₀ ε) γ))).card
              * (m + 1 - 2 * w - (k + 1)) :=
              Nat.mul_le_mul_right _ (Finset.card_le_card hcover)
          _ ≤ (∑ i₀ ∈ Z, (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
                ((rsCode (punctureDom dom i₀) k : Submodule F (Fin m → F)) : Set (Fin m → F))
                ((w : ℝ≥0) / (m : ℝ≥0))
                (punctureWord dom i₀ u₀) (punctureWord dom i₀ ε) γ)).card)
              * (m + 1 - 2 * w - (k + 1)) :=
              Nat.mul_le_mul_right _ Finset.card_biUnion_le
          _ = ∑ i₀ ∈ Z, ((Finset.univ.filter (fun γ : F => mcaEvent (F := F)
                ((rsCode (punctureDom dom i₀) k : Submodule F (Fin m → F)) : Set (Fin m → F))
                ((w : ℝ≥0) / (m : ℝ≥0))
                (punctureWord dom i₀ u₀) (punctureWord dom i₀ ε) γ)).card
                * (m + 1 - 2 * w - (k + 1))) := by rw [Finset.sum_mul]
          _ ≤ ∑ _i₀ ∈ Z, m ^ (k + 1) := by
              refine Finset.sum_le_sum fun i₀ _ => ?_
              rw [hσeq]
              have hδm : ((w : ℝ≥0) / (m : ℝ≥0)) * (Fintype.card (Fin m) : ℝ≥0) ≤ w := by
                rw [Fintype.card_fin]
                rw [div_mul_cancel₀]
                exact_mod_cast (NeZero.ne m)
              exact ih hk1 m ⟨NeZero.ne m⟩ (punctureDom dom i₀) w
                ((w : ℝ≥0) / (m : ℝ≥0)) (punctureWord dom i₀ u₀) (punctureWord dom i₀ ε)
                hδm (by omega)
          _ = Z.card * m ^ (k + 1) := by
              rw [Finset.sum_const, smul_eq_mul]
          _ ≤ (m + 1) * m ^ (k + 1) := by
              refine Nat.mul_le_mul_right _ ?_
              calc Z.card ≤ (Finset.univ : Finset (Fin (m + 1))).card :=
                    Finset.card_le_card (Finset.subset_univ _)
                _ = m + 1 := by rw [Finset.card_univ, Fintype.card_fin]
          _ ≤ (m + 1) ^ (k + 2) := by
              have : m ^ (k + 1) ≤ (m + 1) ^ (k + 1) :=
                Nat.pow_le_pow_left (by omega) _
              calc (m + 1) * m ^ (k + 1) ≤ (m + 1) * (m + 1) ^ (k + 1) :=
                    Nat.mul_le_mul_left _ this
                _ = (m + 1) ^ (k + 2) := by ring

/-! ## §4 Probability and threshold forms -/

open Classical in
/-- **The probability form**: `ε_mca(RS_k, δ) ≤ n^{k+1}/((n−2w−k)·q)` for every
`δ ≤ w/n` with `2w + k + 1 ≤ n` — the whole below-UDR range, generic domain. -/
theorem belowUDR_epsMCA_le {n : ℕ} [NeZero n] (dom : Fin n ↪ F)
    {k w : ℕ} (hk : 1 ≤ k) (hn : 2 * w + k + 1 ≤ n)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ ((n ^ (k + 1) / (n - 2 * w - k) : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) := by
  rw [epsMCA]
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  have h := belowUDR_badScalars_card_mul_le k hk n ‹NeZero n› dom w δ (u 0) (u 1)
    hδn hn
  have hpos : 0 < n - 2 * w - k := by omega
  have hdiv : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ (u 0) (u 1)
      γ)).card ≤ n ^ (k + 1) / (n - 2 * w - k) :=
    Nat.le_div_iff_mul_le hpos |>.mpr h
  exact_mod_cast hdiv

open Classical in
/-- **The threshold form**: `δ* ≥ δ` for every `δ ≤ w/n` with `2w + k + 1 ≤ n` whenever
the polynomial mass fits the budget — below-UDR radius coverage is gapless at every
rate on EVERY injective evaluation domain (no smoothness). -/
theorem le_mcaDeltaStar_belowUDR {n : ℕ} [NeZero n] (dom : Fin n ↪ F)
    {k w : ℕ} (hk : 1 ≤ k) (hn : 2 * w + k + 1 ≤ n)
    {δ : ℝ≥0} (hδ1 : δ ≤ 1) (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {εstar : ℝ≥0∞}
    (hbudget : ((n ^ (k + 1) / (n - 2 * w - k) : ℕ) : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans (belowUDR_epsMCA_le dom hk hn hδn) hbudget)

open Classical in
/-- **The generic-domain edge-band instance**: on the fifth no-go's band
`2w + k + 1 ≤ n < 2w + 2k` the threshold moves for every injective evaluation domain
at the puncture budget — the band needed neither smoothness nor the subset law. -/
theorem udrEdgeBand_closure_generic {n : ℕ} [NeZero n] (dom : Fin n ↪ F)
    {k w : ℕ} (hk : 1 ≤ k)
    (hband_lo : 2 * w + k + 1 ≤ n) (_hband_hi : n < 2 * w + 2 * k)
    {δ : ℝ≥0} (hδ1 : δ ≤ 1) (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {εstar : ℝ≥0∞}
    (hbudget : ((n ^ (k + 1) / (n - 2 * w - k) : ℕ) : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  le_mcaDeltaStar_belowUDR dom hk hband_lo hδ1 hδn hbudget

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.mcaEvent_puncture
#print axioms ProximityGap.Ownership.belowUDR_badScalars_card_mul_le
#print axioms ProximityGap.Ownership.belowUDR_epsMCA_le
#print axioms ProximityGap.Ownership.le_mcaDeltaStar_belowUDR
#print axioms ProximityGap.Ownership.udrEdgeBand_closure_generic
