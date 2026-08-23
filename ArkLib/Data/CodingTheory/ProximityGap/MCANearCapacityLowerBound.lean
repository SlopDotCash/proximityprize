/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-!
# An explicit linear near-capacity MCA lower bound via the witness spread (Proximity Prize, #232)

`MCAWitnessSpread.lean` proved two halves of the Grand MCA Challenge lower-bound shape:
* the **engine** `epsMCA_ge_card_div_of_mcaEvent_set` — a stack carrying a set `G` of bad scalars
  gives `ε_mca ≥ |G|/|F|`;
* the **obstruction** `common_witness_badGamma_set_card_le_one` — a *single, fixed* witness set `S`
  carries at most **one** bad scalar, so the prize's near-capacity lower bound provably requires the
  witness sets `S_γ` to **vary** with `γ` (the list-decoding spread).

This file supplies the missing positive half for an explicit Reed–Solomon code: a construction that
**realizes** a spread of `n-1` *distinct* witness sets, driving `ε_mca` up to `(n-1)/|F|` — a
*linear* lower bound just below capacity, exactly the `≥ n^{Ω(1)}/|F|` *shape* the literature
([BCHKS25], [KK25], [CGHLL26]) establishes near capacity, here made explicit and kernel-checked.

## The construction (consecutive-window interpolation)

Take the **constant** code `C = RS[ZMod p, Fin n, k=1]` (the degree-`<1` codewords). On the stack
`u₀ i = i²`, `u₁ i = i`, the line `u₀ + γ·u₁ = i² + γ·i` is **constant on the window `{j, j+1}`**
exactly when `γ = γ_j := -(2j+1)` (the unique scalar killing the slope across that pair). Each window
`{j, j+1}` is a *distinct* witness set; `u₁` takes the distinct values `j ≠ j+1` on it, so no codeword
*pair* agrees with `(u₀,u₁)` there (`¬ pairJointAgreesOn`) — i.e. `mcaEvent` fires. The `n-1` scalars
`γ_0, …, γ_{n-2}` are distinct (`2j+1` are distinct mod `p` when `2n ≤ p`), so

`ε_mca(C, 1 - 2/n) ≥ (n-1)/p`.

The radius `δ = 1 - 2/n` sits just below the constant code's capacity `1 - 1/n`, and above its Johnson
radius `1 - 1/√n` once `n ≥ 5` — i.e. **strictly inside the open Johnson→capacity gap**.

This is a genuine realization of the witness spread (the obstruction is *tight*: with a common witness
`≤ 1`, with `n-1` distinct windows `≥ n-1`), not a closure of the prize: it pins one `(δ, code)` point,
whereas the Grand Challenge asks for the threshold `δ*` where `ε_mca` crosses `2^{-128}` for the
constant *positive*-rate prize codes. Generalizing the same window construction to `RS` of degree
`<k` (windows of `k+1` consecutive nodes, `u₁ = x^k`, `u₀ = x^{k+1}`, `γ_j = -h₁(window_j)`) gives
`ε_mca ≥ (n-k)/|F|` at `δ = 1-(k+1)/n` for every rate — the degree-`<k` case needs Reed–Solomon
interpolation (the `k`-th divided difference) and is the natural next brick.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232 / #141.
-/

namespace ProximityGap.MCANearCapacity

open scoped NNReal ENNReal BigOperators
open ProximityGap Code

variable {p : ℕ} [Fact p.Prime]

/-- The length-`n` constant (repetition) Reed–Solomon code `RS[ZMod p, ·, 1]`: the degree-`<1`
polynomials, i.e. the constant functions. -/
def constCode (n : ℕ) : Set (Fin n → ZMod p) := {w | ∃ a : ZMod p, w = fun _ => a}

/-- First row `u₀ i = i²`. -/
def urow0 (n : ℕ) : Fin n → ZMod p := fun i => ((i : ℕ) : ZMod p) ^ 2
/-- Second row `u₁ i = i`. -/
def urow1 (n : ℕ) : Fin n → ZMod p := fun i => ((i : ℕ) : ZMod p)

/-- The bad scalar for the window `{j, j+1}`: `γ_j = -(2j+1)`. -/
def badGamma (j : ℕ) : ZMod p := -(2 * (j : ZMod p) + 1)

/-- **Core: `mcaEvent` fires for every consecutive-window scalar.** For the constant code on
`Fin n`, the stack `(i², i)`, and `γ_j = -(2j+1)`, the line `u₀ + γ_j·u₁` is constant on the
window `{j, j+1}` (a codeword), but `u₁` takes the distinct values `j ≠ j+1` there so no codeword
pair agrees with `(u₀,u₁)` on the window — hence `¬ pairJointAgreesOn`. -/
theorem mcaEvent_window (n : ℕ) (hn : 2 ≤ n) (j : ℕ) (hj : j + 1 < n) :
    mcaEvent (constCode (p := p) n) (1 - 2 / (n : ℝ≥0))
      (urow0 (p := p) n) (urow1 (p := p) n) (badGamma (p := p) j) := by
  have hjn : j < n := by omega
  set a : Fin n := ⟨j, hjn⟩ with ha
  set b : Fin n := ⟨j + 1, hj⟩ with hb
  have hab : a ≠ b := by
    rw [ha, hb, Ne, Fin.mk.injEq]; omega
  set c : ZMod p := urow0 (p := p) n a + badGamma (p := p) j • urow1 (p := p) n a with hc
  refine ⟨{a, b}, ?_, ⟨fun _ => c, ⟨c, rfl⟩, ?_⟩, ?_⟩
  · -- card bound: |{a,b}| = 2 ≥ (1 - δ)·n = 2
    rw [Finset.card_pair hab]
    have hnpos : (0 : ℝ≥0) < (n : ℝ≥0) := by
      have : (0 : ℕ) < n := by omega
      exact_mod_cast this
    have h2le : (2 : ℝ≥0) / (n : ℝ≥0) ≤ 1 := by
      rw [div_le_one hnpos]; exact_mod_cast hn
    have hsub : (1 : ℝ≥0) - (1 - 2 / (n : ℝ≥0)) = 2 / (n : ℝ≥0) :=
      tsub_tsub_cancel_of_le h2le
    rw [Fintype.card_fin, hsub, div_mul_cancel₀ _ (ne_of_gt hnpos)]
    norm_num
  · -- the constant `c` agrees with `u₀ + γ_j·u₁` on `{a, b}`
    intro i hi
    rw [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hi | hi
    · subst hi; rfl
    · subst hi
      simp only [hc, urow0, urow1, ha, hb, badGamma, smul_eq_mul]
      push_cast
      ring
  · -- ¬ pairJointAgreesOn: u₁ is non-constant on {a, b}
    rintro ⟨v₀, ⟨d₀, hv₀⟩, v₁, ⟨d₁, hv₁⟩, hag⟩
    have hva : v₁ a = urow1 (p := p) n a := (hag a (by simp)).2
    have hvb : v₁ b = urow1 (p := p) n b := (hag b (by simp)).2
    rw [hv₁] at hva hvb
    rw [ha, urow1] at hva
    rw [hb, urow1] at hvb
    have : ((j : ZMod p)) = ((j : ℕ) + 1 : ℕ) := by rw [← hva, hvb]
    push_cast at this
    simp at this

/-- The bad-scalar set `{ -(2j+1) : 0 ≤ j < n-1 }`. -/
noncomputable def badSet (n : ℕ) : Finset (ZMod p) :=
  (Finset.range (n - 1)).image (fun j => badGamma (p := p) j)

theorem badGamma_injOn (n : ℕ) (hnp : 2 * n ≤ p) :
    Set.InjOn (fun j => badGamma (p := p) j) (Finset.range (n - 1)) := by
  intro x hx y hy hxy
  simp only [Finset.coe_range, Set.mem_Iio] at hx hy
  simp only [badGamma, neg_inj, add_left_inj] at hxy
  have hx2 : (2 * x) < p := by omega
  have hy2 : (2 * y) < p := by omega
  have : ((2 * x : ℕ) : ZMod p) = ((2 * y : ℕ) : ZMod p) := by push_cast; linear_combination hxy
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp this
  rw [Nat.mod_eq_of_lt hx2, Nat.mod_eq_of_lt hy2] at this
  omega

theorem badSet_card (n : ℕ) (hnp : 2 * n ≤ p) :
    (badSet (p := p) n).card = n - 1 := by
  rw [badSet, Finset.card_image_of_injOn (badGamma_injOn n hnp), Finset.card_range]

/-- **Main: an explicit linear near-capacity MCA lower bound for the constant Reed–Solomon code.**
For the length-`n` constant code over `ZMod p` (`2n ≤ p`), at radius `δ = 1 - 2/n` (just below the
capacity `1 - 1/n`),
`ε_mca(C, δ) ≥ (n-1)/p`.
The `n-1` bad scalars `γ_j = -(2j+1)` each have a *distinct* witness set `{j, j+1}`, realizing the
witness spread that `MCAWitnessSpread.common_witness_badGamma_set_card_le_one` proves is *necessary*
— so the obstruction is tight, and `ε_mca` is genuinely linear in `n` near capacity. -/
theorem epsMCA_constCode_ge (n : ℕ) [NeZero n] (hn : 2 ≤ n) (hnp : 2 * n ≤ p) :
    ((n - 1 : ℕ) : ℝ≥0∞) / (Fintype.card (ZMod p) : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (A := ZMod p) (constCode (p := p) n) (1 - 2 / (n : ℝ≥0)) := by
  have hG : ∀ γ ∈ badSet (p := p) n,
      mcaEvent (constCode (p := p) n) (1 - 2 / (n : ℝ≥0))
        ((![urow0 n, urow1 n] : WordStack (ZMod p) (Fin 2) (Fin n)) 0)
        ((![urow0 n, urow1 n] : WordStack (ZMod p) (Fin 2) (Fin n)) 1) γ := by
    intro γ hγ
    rw [badSet, Finset.mem_image] at hγ
    obtain ⟨j, hj, rfl⟩ := hγ
    rw [Finset.mem_range] at hj
    have : mcaEvent (constCode (p := p) n) (1 - 2 / (n : ℝ≥0))
        (urow0 n) (urow1 n) (badGamma j) := mcaEvent_window n hn j (by omega)
    simpa using this
  have hengine := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (constCode (p := p) n) (1 - 2 / (n : ℝ≥0))
    (![urow0 n, urow1 n] : WordStack (ZMod p) (Fin 2) (Fin n)) (badSet (p := p) n) hG
  rw [badSet_card n hnp] at hengine
  exact hengine

#print axioms epsMCA_constCode_ge

end ProximityGap.MCANearCapacity
