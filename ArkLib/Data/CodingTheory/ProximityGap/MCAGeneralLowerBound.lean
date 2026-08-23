/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-!
# A general MCA lower bound up to capacity, for every proper linear code

The MCA upper-bound conjecture (ABF26 Grand Challenge 1) asks for `ε_mca(C, δ) ≤ poly(n)/q` up to
the capacity radius `δ < 1 - ρ`; the *upper* direction is open. This file proves the matching
**lower** direction holds *unconditionally* for **every** linear code, up to the same capacity
radius — sharpening exactly what is open:

  **Theorem (`epsMCA_ge_inv_card_of_finrank_lt`).** For a linear code `C ⊆ Fⁿ` (a submodule) of
  dimension `k`, and any radius `δ` with `k < (1 - δ)·n`, one has `1/|F| ≤ ε_mca(C, δ)`.

Equivalently, with rate `ρ = k/n`: for every `δ < 1 - ρ`, the MCA error is at least `1/|F|`.

This generalizes the zero-code bound (`MCALowerBound`, `k = 0`) to *all* codes, and it is the exact
companion of the open prize: the conjecture posits `ε_mca ≤ poly(n)/q`; here we prove
`ε_mca ≥ 1/q` in the same regime — so the open content is precisely whether the `poly(n)`-factor
upper bound holds, never whether `ε_mca` is *positive*.

## Proof

Pick a coordinate set `S` with `|S| = ⌈(1-δ)n⌉`. Since `k < (1-δ)n ≤ |S|`, the code has
`|C| = q^k < q^{|S|} = |F^S|` words, so the restriction map `C → F^S` (`c ↦ c|_S`) is not
surjective: some `y : S → F` is unreachable. Lifting `y` to `u₁ : ι → F` (`y` on `S`, `0` off),
**no** codeword agrees with `u₁` on all of `S`. Hence the stack `(0, u₁)` fires `mcaEvent` at
`γ = 0`: the witness `S` has size `≥ (1-δ)n`, the zero codeword lies on the line `0`, and no joint
pair agrees with `(0, u₁)` on `S` (the second row `u₁` is unmatchable). By
`epsMCA_ge_inv_card_of_mcaEvent`, `ε_mca(C, δ) ≥ 1/|F|`.

## References
- Generalizes `ProximityGap.MCAZeroCode.epsMCA_bot_ge_inv_card`.
- The capacity-radius lower companion to the open Grand Challenge 1 upper bound (#141 / #171).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.MCAGeneralLower

open scoped NNReal ProbabilityTheory ENNReal
open ProximityGap Code

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- **Pigeonhole on the restriction map.** If a code has fewer words than `F^S`, then some word on
`S` is not the restriction of any codeword — i.e. there is `u₁` that no codeword matches on `S`. -/
theorem exists_unmatched_on_S (C : Submodule F (ι → F)) (S : Finset ι)
    (hcard : Fintype.card ↥C < Fintype.card F ^ S.card) :
    ∃ u₁ : ι → F, ∀ c ∈ C, ∃ i ∈ S, (c : ι → F) i ≠ u₁ i := by
  classical
  let ρ : ↥C → (↥S → F) := fun c i => (c : ι → F) (i : ι)
  have hcardSF : Fintype.card (↥S → F) = Fintype.card F ^ S.card := by
    rw [Fintype.card_fun, Fintype.card_coe]
  obtain ⟨y, hy⟩ : ∃ y : ↥S → F, ∀ c : ↥C, ρ c ≠ y := by
    by_contra h
    push_neg at h
    have hsurj : Function.Surjective ρ := fun y => h y
    have hle := Fintype.card_le_of_surjective ρ hsurj
    rw [hcardSF] at hle
    omega
  refine ⟨fun i => if h : i ∈ S then y ⟨i, h⟩ else 0, ?_⟩
  intro c hc
  by_contra hcon
  push_neg at hcon
  apply hy ⟨c, hc⟩
  funext i
  have hci := hcon i.val i.property
  simp only [dif_pos i.property] at hci
  exact hci

/-- The two-row stack `(0, u₁)`. -/
noncomputable def zeroStack (u₁ : ι → F) : WordStack F (Fin 2) ι := fun k => if k = 0 then 0 else u₁

@[simp] theorem zeroStack_zero (u₁ : ι → F) : zeroStack u₁ 0 = (0 : ι → F) := by simp [zeroStack]
@[simp] theorem zeroStack_one (u₁ : ι → F) : zeroStack u₁ 1 = u₁ := by simp [zeroStack]

open Classical in
/-- **General MCA lower bound up to capacity.** For a linear code `C` of dimension `k` and radius
`δ` with `k < (1-δ)·n`, the MCA error is at least `1/|F|`. -/
theorem epsMCA_ge_inv_card_of_finrank_lt (C : Submodule F (ι → F)) (δ : ℝ≥0)
    (hrank : (Module.finrank F ↥C : ℝ) < (1 - (δ : ℝ)) * (Fintype.card ι : ℝ)) :
    (1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ epsMCA (F := F) (A := F) (↑C : Set (ι → F)) δ := by
  set n := Fintype.card ι with hn
  set k := Module.finrank F ↥C with hk
  -- Choose `S` of size `m := ⌈(1-δ)n⌉`, with `k < m ≤ n`.
  set m : ℕ := ⌈(1 - (δ : ℝ)) * (n : ℝ)⌉₊ with hm
  have hδlt1 : (δ : ℝ) < 1 := by
    by_contra h
    push_neg at h
    have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have : (1 - (δ : ℝ)) * (n : ℝ) ≤ 0 := by nlinarith [hnn]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    linarith [hrank]
  have hkm : k < m := by rw [hm]; exact Nat.lt_ceil.mpr hrank
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have hmn : m ≤ n := by
    rw [hm]; apply Nat.ceil_le.mpr
    have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    nlinarith [hnn, hδ0, mul_nonneg hδ0 hnn]
  obtain ⟨S, _hSsub, hScard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι))
    (by simpa using hmn)
  -- `|C| = q^k < q^m = |F^S|`, so some `u₁` is unmatched on `S`.
  have hqge2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hCcard : Fintype.card ↥C = Fintype.card F ^ k := by
    rw [hk]; exact Module.card_eq_pow_finrank
  have hlt : Fintype.card ↥C < Fintype.card F ^ S.card := by
    rw [hCcard, hScard]
    apply Nat.pow_lt_pow_right <;> omega
  obtain ⟨u₁, hunmatch⟩ := exists_unmatched_on_S C S hlt
  -- The stack `(0, u₁)` fires `mcaEvent` at `γ = 0`.
  have hsize : ((1 - δ) * (Fintype.card ι : ℝ≥0)) ≤ (S.card : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub hδlt1.le, NNReal.coe_one,
      NNReal.coe_natCast, NNReal.coe_natCast]
    rw [hScard]
    have := Nat.le_ceil ((1 - (δ : ℝ)) * (n : ℝ))
    rw [← hm] at this
    simpa [hn] using this
  have hev : mcaEvent (F := F) (↑C : Set (ι → F)) δ (zeroStack u₁ 0) (zeroStack u₁ 1) (0 : F) := by
    refine ⟨S, ?_, ⟨0, C.zero_mem, ?_⟩, ?_⟩
    · simpa using hsize
    · intro i _; simp
    · rintro ⟨v₀, _hv₀, v₁, hv₁, hag⟩
      obtain ⟨i, hiS, hne⟩ := hunmatch v₁ hv₁
      exact hne (by simpa using (hag i hiS).2)
  exact epsMCA_ge_inv_card_of_mcaEvent (F := F) (A := F) (↑C : Set (ι → F)) δ (zeroStack u₁) 0 hev

/-- **Why the Proximity Prize requires a large field.** The prize fixes `ε* = 2^-128` and asks for
the largest `δ*` with `ε_mca(C, δ*) ≤ ε*`, *assuming `|F|` is sufficiently large that such a `δ*`
exists*. This corollary makes that assumption sharp: if `|F| < 2^128` then for **every** proper code
`C` and **every** `δ` below capacity (`finrank C < (1-δ)·n`), `ε_mca(C, δ) > ε*`. Hence no admissible
`δ*` exists in the capacity range unless `|F| ≥ 2^128`. -/
theorem epsMCA_gt_epsStar_of_small_field (C : Submodule F (ι → F)) (δ : ℝ≥0)
    (hrank : (Module.finrank F ↥C : ℝ) < (1 - (δ : ℝ)) * (Fintype.card ι : ℝ))
    (hF : (Fintype.card F : ℝ≥0∞) < 2 ^ (128 : ℕ)) :
    (1 : ℝ≥0∞) / (2 ^ (128 : ℕ)) < epsMCA (F := F) (A := F) (↑C : Set (ι → F)) δ := by
  have h1 : (1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F) (↑C : Set (ι → F)) δ :=
    epsMCA_ge_inv_card_of_finrank_lt C δ hrank
  have h2 : (1 : ℝ≥0∞) / (2 ^ (128 : ℕ)) < (1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
    rw [one_div, one_div]
    exact ENNReal.inv_lt_inv.mpr hF
  exact lt_of_lt_of_le h2 h1

#print axioms exists_unmatched_on_S
#print axioms epsMCA_ge_inv_card_of_finrank_lt
#print axioms epsMCA_gt_epsStar_of_small_field

end ProximityGap.MCAGeneralLower
