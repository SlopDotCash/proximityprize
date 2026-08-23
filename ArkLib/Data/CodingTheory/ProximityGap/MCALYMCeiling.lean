/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAAntichainEngine
import Mathlib.Combinatorics.SetFamily.LYM

/-!
# The LYM ceiling (#357 round 3): `ε_mca(C, δ) ≤ C(n,t)/q` for every linear code

The antichain engine proved that witnesses of distinct bad scalars cannot nest. This file
converts that structure into the **universal staircase ceiling** via the
Lubell–Yamamoto–Meshalkin inequality:

* `choose_anti_above_half` — binomials decrease above the middle (`N ≤ 2t ≤ 2r ≤ 2N ⟹
  C(N,r) ≤ C(N,t)`), by symmetry + monotonicity below half;
* `antichain_card_le_choose` — **truncated Sperner**: an antichain whose members all have
  `≥ t ≥ N/2` elements has at most `C(N,t)` members (LYM, summed against the largest
  admissible layer);
* `badScalar_card_le_choose` — the bad scalars of any stack inject into such an
  antichain (chosen witnesses; nesting collapse), so every linear code at every radius
  `δ` with floor `t` satisfying `(t : ℝ≥0) ≤ (1−δ)n` and `n ≤ 2t` has at most `C(n,t)`
  bad scalars per stack;
* **`epsMCA_le_choose_div`** — `ε_mca(C, δ) ≤ C(n,t)/q`, every linear code, every
  `δ ≤ 1/2`-regime radius.

**Probe verdict (the reason this is the right ceiling):** the first window-interior
staircase cell — `(n,k) = (5,2)` at `δ = 2/5`, strictly between Johnson (`≈ 0.368`) and
capacity (`0.6`) — has measured max bad count **exactly `10 = C(5,3)`** at both `F₁₁` and
`F₁₃` (after small-field breakdown at `F₇`): the LYM ceiling is *attained* inside the
window at this cell. The matching 10-scalar lower construction is the registered next
brick; together they would give the first exact window-interior `ε_mca` value.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- Issue #357 (round-3 window-cell probe comment); `MCAAntichainEngine.lean`;
  Mathlib `Combinatorics.SetFamily.LYM`.
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAWitnessSpread ProximityGap.MCAAntichainEngine

namespace ProximityGap.MCALYMCeiling

/-! ## Binomial monotonicity around the middle -/

theorem choose_mono_below_half {N a b : ℕ} (hab : a ≤ b) (hb : b ≤ N / 2) :
    N.choose a ≤ N.choose b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
      have hb' : b ≤ N / 2 := le_trans (Nat.le_succ b) hb
      have hblt : b < N / 2 := lt_of_lt_of_le (Nat.lt_succ_self b) hb
      exact le_trans (ih hb') (Nat.choose_le_succ_of_lt_half_left hblt)

/-- Binomials decrease above the middle: `C(N,r) ≤ C(N,t)` for `N/2 ≤ t ≤ r ≤ N`. -/
theorem choose_anti_above_half {N t r : ℕ} (hN : N ≤ 2 * t) (htr : t ≤ r) (hrN : r ≤ N) :
    N.choose r ≤ N.choose t := by
  rw [← Nat.choose_symm hrN, ← Nat.choose_symm (le_trans htr hrN)]
  apply choose_mono_below_half (by omega)
  omega

/-! ## Truncated Sperner via LYM -/

open Finset in
/-- **Truncated Sperner.** An antichain in `Finset ι` whose members all have at least
`t ≥ N/2` elements has at most `C(N, t)` members. -/
theorem antichain_card_le_choose {ι : Type} [Fintype ι] [DecidableEq ι]
    {𝒜 : Finset (Finset ι)} (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset ι)))
    {t : ℕ} (hsize : ∀ s ∈ 𝒜, t ≤ s.card) (hhalf : Fintype.card ι ≤ 2 * t) :
    𝒜.card ≤ (Fintype.card ι).choose t := by
  classical
  rcases 𝒜.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨s₀, hs₀⟩ := hne
  have hcardle : ∀ s : Finset ι, s.card ≤ Fintype.card ι := fun s => by
    simpa using Finset.card_le_univ s
  have htN : t ≤ Fintype.card ι := le_trans (hsize s₀ hs₀) (hcardle s₀)
  have hpos : (0 : ℚ≥0) < (((Fintype.card ι).choose t : ℕ) : ℚ≥0) := by
    exact_mod_cast Nat.choose_pos htN
  have hsum := Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose
    (𝕜 := ℚ≥0) (𝒜 := 𝒜) h𝒜
  have hterm : ∀ s ∈ 𝒜, (((Fintype.card ι).choose t : ℕ) : ℚ≥0)⁻¹
      ≤ (((Fintype.card ι).choose s.card : ℕ) : ℚ≥0)⁻¹ := by
    intro s hs
    have hle : (Fintype.card ι).choose s.card ≤ (Fintype.card ι).choose t :=
      choose_anti_above_half hhalf (hsize s hs) (hcardle s)
    have hpos' : (0 : ℚ≥0) < (((Fintype.card ι).choose s.card : ℕ) : ℚ≥0) := by
      have h0 : 0 < (Fintype.card ι).choose s.card := Nat.choose_pos (hcardle s)
      exact_mod_cast h0
    rw [inv_le_inv₀ hpos hpos']
    exact_mod_cast hle
  have hchain : (𝒜.card : ℚ≥0) * (((Fintype.card ι).choose t : ℕ) : ℚ≥0)⁻¹ ≤ 1 := by
    calc (𝒜.card : ℚ≥0) * (((Fintype.card ι).choose t : ℕ) : ℚ≥0)⁻¹
        = ∑ _s ∈ 𝒜, (((Fintype.card ι).choose t : ℕ) : ℚ≥0)⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ s ∈ 𝒜, (((Fintype.card ι).choose s.card : ℕ) : ℚ≥0)⁻¹ :=
          Finset.sum_le_sum hterm
      _ ≤ 1 := hsum
  have h := mul_le_mul_of_nonneg_right hchain (le_of_lt hpos)
  rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), mul_one, one_mul] at h
  exact_mod_cast h

/-! ## The universal staircase ceiling -/

section Ceiling

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **The bad-scalar LYM cap.** For every linear code, every stack and every radius `δ`
whose agreement floor `t` satisfies `(t : ℝ≥0) ≤ (1−δ)·n` and `n ≤ 2t`: at most `C(n,t)`
bad scalars. The chosen witnesses form an antichain of `≥ t`-sets. -/
theorem badScalar_card_le_choose (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (u : WordStack A (Fin 2) ι) {t : ℕ}
    (hfloor : (t : ℝ≥0) ≤ (1 - δ) * (Fintype.card ι : ℝ≥0))
    (hhalf : Fintype.card ι ≤ 2 * t) :
    (Finset.univ.filter
        (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ)).card
      ≤ (Fintype.card ι).choose t := by
  classical
  -- the witness choice
  set W : F → Finset ι := fun γ =>
    if h : mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ
    then h.choose else ∅ with hW
  set G := Finset.univ.filter
    (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ) with hG
  -- facts about chosen witnesses
  have hWspec : ∀ γ ∈ G, (t ≤ (W γ).card) ∧
      (∃ w ∈ C, ∀ i ∈ W γ, w i = u 0 i + γ • u 1 i) ∧
      ¬ pairJointAgreesOn (C : Set (ι → A)) (W γ) (u 0) (u 1) := by
    intro γ hγ
    rw [hG, Finset.mem_filter] at hγ
    obtain ⟨-, hev⟩ := hγ
    obtain ⟨hcard, hline, hno⟩ := hev.choose_spec
    rw [hW]
    simp only [dif_pos hev]
    refine ⟨?_, hline, hno⟩
    have : (t : ℝ≥0) ≤ (hev.choose.card : ℝ≥0) := le_trans hfloor hcard
    exact_mod_cast this
  -- distinct bad scalars have non-nesting (hence distinct) witnesses
  have hWinj : Set.InjOn W ↑G := by
    intro γ hγ γ' hγ' heq
    obtain ⟨-, hline, hno⟩ := hWspec γ (Finset.mem_coe.mp hγ)
    obtain ⟨-, hline', -⟩ := hWspec γ' (Finset.mem_coe.mp hγ')
    rw [heq] at hline hno
    exact unique_bad_gamma_common_witness C (W γ') (u 0) (u 1) hno hline hline'
  -- the image is an antichain
  have hanti : IsAntichain (· ⊆ ·) ((G.image W : Finset (Finset ι)) : Set (Finset ι)) := by
    intro S hS S' hS' hne hsub
    rw [Finset.mem_coe, Finset.mem_image] at hS hS'
    obtain ⟨γ, hγ, rfl⟩ := hS
    obtain ⟨γ', hγ', rfl⟩ := hS'
    obtain ⟨-, hline, hno⟩ := hWspec γ hγ
    obtain ⟨-, hline', -⟩ := hWspec γ' hγ'
    have hγγ : γ = γ' :=
      bad_scalar_eq_of_witness_subset C hsub hline hno hline'
    exact hne (by rw [hγγ])
  -- assemble
  calc G.card = (G.image W).card :=
        (Finset.card_image_of_injOn hWinj).symm
    _ ≤ (Fintype.card ι).choose t := by
        apply antichain_card_le_choose hanti _ hhalf
        intro s hs
        rw [Finset.mem_image] at hs
        obtain ⟨γ, hγ, rfl⟩ := hs
        exact (hWspec γ hγ).1

open Classical in
/-- **THE LYM CEILING.** For every linear code over every finite field, at every radius
with agreement floor `t ≥ n/2`:

  `ε_mca(C, δ) ≤ C(n, t) / q`.

The universal staircase upper bound; tight at the granularity floor (`t = n−1`: `C(n,n−1)
= n`, the flat-`n` law) and — per the window-cell probe — attained at the first
window-interior cell (`C(5,3) = 10` measured at `F₁₁`, `F₁₃`). -/
theorem epsMCA_le_choose_div (C : Submodule F (ι → A)) (δ : ℝ≥0) {t : ℕ}
    (hfloor : (t : ℝ≥0) ≤ (1 - δ) * (Fintype.card ι : ℝ≥0))
    (hhalf : Fintype.card ι ≤ 2 * t) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
      ≤ (((Fintype.card ι).choose t : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast badScalar_card_le_choose C δ u hfloor hhalf

end Ceiling

/-! ## Source audit -/

#print axioms choose_anti_above_half
#print axioms antichain_card_le_choose
#print axioms badScalar_card_le_choose
#print axioms epsMCA_le_choose_div

end ProximityGap.MCALYMCeiling
