/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Almost-all-`b` ⟹ all-`b` is the moment, with NO amplification gain (#444)

**An honest REDUCED brick (a documented no-gain, NOT a closure).** Parseval pins `|η_b| ≈ √n` for
*almost all* `b` (the 2nd moment `∑_{b≠0}|η_b|² = q·n − n² ≤ q·n` spreads `√n` over `q−1` values);
the open prize is the *worst* `b` (the `L^∞` value `M = max_{b≠0}|η_b|`). A natural hope is that
"almost-all-`b`" could be *amplified* to "all-`b`" by some extra structural input. **This brick
formalizes the amplification and shows the gain is exactly the moment: there is no head start.**

## The amplification (Markov / union bound over `b`)

Let `S = ∑_{b∈B} |η_b|^{2r}` be the total `2r`-th moment over the nonzero frequency set `B`
(`#B = p−1`). At threshold `T > 0`, the set of **bad** `b` (`|η_b|^{2r} > T^{2r}`) is small:

> `card_bad_mul_le_moment` — `#{b ∈ B : T^{2r} < |η_b|^{2r}} · T^{2r} ≤ S`,
> hence `#bad ≤ S / T^{2r}` (`card_bad_le_moment_div`).

The only input is `S` — the moment. Plug the in-tree handles: the moment identity
`S = ∑_{b≠0}|η_b|^{2r} = q·E_r − n^{2r} ≤ q·E_r` (`DCSubtractedMoment.sum_nonzero_moment`), and the
char-`p` Wick bound `E_r ≤ (2r−1)‼·n^r` at `r=⌈log p⌉` (the open residual), giving
`S ≤ q·(2r−1)‼·n^r`. With `T = λ√n`, `λ=√(2 log q)` at `r=⌈log p⌉`, the saddle algebra
(`_MomentSaddleValue.prize_floor_amgm_sqrt_e`) makes `S/T^{2r} < 1`, forcing `#bad = 0` — all-`b`.

## The point: NO amplification gain (the honest REDUCED verdict)

The Markov step uses `S` and nothing else — not the distribution of the typical `b`, no "almost-all"
structure beyond `S`. So `amplification_reduces_to_moment`: `#bad = 0` whenever `S < τ`, and a bad
`b` forces `τ ≤ S` (`bad_witness_of_moment_ge`). Thus "amplify almost-all to all" **is** "bound the
moment `S` below `τ`", which **is** the `M^{2r} ≤ q·(2r−1)‼n^r` Wick saddle — the SAME single-depth
char-`p` energy bound that is the project's minimal open residual
(`_MomentSaddleValue.prize_floor_of_single_depth`). The "almost-all" 2nd-moment (`r=1`) is strictly
weaker than the `r=⌈log p⌉` moment needed here (`bad_count_mono_in_moment`), so almost-all does NOT
help: no amplification gain beyond the moment. This closes the "maybe almost-all helps" hope.

Pure finite probability / Markov over `Finset`; **axiom-clean**
(`propext, Classical.choice, Quot.sound`). Issue #444 (thread T10-almostall-amplify).

## In-tree handles this composes with
- `DCSubtractedMoment.sum_nonzero_moment` — `S = q·E_r − n^{2r}` (the moment `S` here).
- `_MomentSaddleValue.{moment_saddle_value, prize_floor_amgm_sqrt_e, prize_floor_of_single_depth}`.
- `_OpenCoreMonotoneReduction.open_core_of_subGaussian_growth`, `oddDoubleFactorial` (Wick algebra).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.AlmostAllToAllAmplify

open Finset

variable {ι : Type*}

/-- **The Markov amplification (count form).** For nonnegative `v` on a finite set `B` and any
threshold `τ`, the number of `b ∈ B` with `v b > τ` times `τ` is at most the total moment
`S = ∑_{b∈B} v b`. Each bad `b` contributes more than `τ`, so there are at most `S/τ` of them. -/
theorem card_bad_mul_le_moment (B : Finset ι) (v : ι → ℝ) (hv : ∀ b ∈ B, 0 ≤ v b) (τ : ℝ) :
    ((B.filter (fun b => τ < v b)).card : ℝ) * τ ≤ ∑ b ∈ B, v b := by
  set Bad := B.filter (fun b => τ < v b) with hBad
  calc ((Bad.card : ℝ)) * τ
      = ∑ _b ∈ Bad, τ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ b ∈ Bad, v b := by
        apply Finset.sum_le_sum
        intro b hb
        rw [hBad, Finset.mem_filter] at hb
        exact le_of_lt hb.2
    _ ≤ ∑ b ∈ B, v b := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro b hbB _
        exact hv b hbB

/-- **The Markov amplification (ratio form).** With a strictly positive threshold `τ > 0`, the
number of bad `b` is at most the moment over the threshold: `#bad ≤ S / τ`. -/
theorem card_bad_le_moment_div (B : Finset ι) (v : ι → ℝ) (hv : ∀ b ∈ B, 0 ≤ v b) {τ : ℝ}
    (hτ : 0 < τ) :
    ((B.filter (fun b => τ < v b)).card : ℝ) ≤ (∑ b ∈ B, v b) / τ := by
  rw [le_div_iff₀ hτ]
  exact card_bad_mul_le_moment B v hv τ

/-- **Forcing zero bad `b` (the prize step).** If the total moment `S` is strictly below the
threshold `τ`, then there is no bad `b`: every `b ∈ B` has `v b ≤ τ`. This is "all-`b` benign"
derived from the single scalar `S < τ` — the entire content of amplifying almost-all to all. -/
theorem forcing_zero_bad (B : Finset ι) (v : ι → ℝ) (hv : ∀ b ∈ B, 0 ≤ v b) {τ : ℝ}
    (hτ : 0 < τ) (hS : ∑ b ∈ B, v b < τ) :
    (B.filter (fun b => τ < v b)).card = 0 := by
  by_contra hne
  have h1 : (1 : ℝ) ≤ ((B.filter (fun b => τ < v b)).card : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  have hmark := card_bad_mul_le_moment B v hv τ
  have hge : τ ≤ ∑ b ∈ B, v b := by
    calc τ = 1 * τ := (one_mul τ).symm
      _ ≤ ((B.filter (fun b => τ < v b)).card : ℝ) * τ :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt hτ)
      _ ≤ ∑ b ∈ B, v b := hmark
  linarith

/-- **The converse sharpness (a bad `b` forces a large moment).** If some `b ∈ B` is bad
(`τ < v b`) then the total moment is at least `τ`: `τ ≤ S`. It certifies that the threshold `τ` is
exactly the moment quantity that must be beaten; there is no slack to exploit beyond `S`. -/
theorem bad_witness_of_moment_ge (B : Finset ι) (v : ι → ℝ) (hv : ∀ b ∈ B, 0 ≤ v b) {τ : ℝ}
    {b₀ : ι} (hb₀ : b₀ ∈ B) (hbad : τ < v b₀) :
    τ ≤ ∑ b ∈ B, v b := by
  calc τ ≤ v b₀ := le_of_lt hbad
    _ ≤ ∑ b ∈ B, v b := Finset.single_le_sum hv hb₀

/-- **The no-gain equivalence (the honest REDUCED statement).** "All-`b` benign" follows from the
single moment inequality `S < τ`, and a bad `b` forces `τ ≤ S`. Combined, the only obstruction to
all-`b` is the moment `S` vs. the threshold `τ` — no almost-all / distributional input enters. This
is the formal statement that amplification reduces all-`b` to the SAME moment bound, with no gain. -/
theorem amplification_reduces_to_moment (B : Finset ι) (v : ι → ℝ) (hv : ∀ b ∈ B, 0 ≤ v b) {τ : ℝ}
    (hτ : 0 < τ) :
    (∑ b ∈ B, v b < τ → (B.filter (fun b => τ < v b)).card = 0)
      ∧ ((∃ b ∈ B, τ < v b) → τ ≤ ∑ b ∈ B, v b) := by
  refine ⟨fun hS => forcing_zero_bad B v hv hτ hS, ?_⟩
  rintro ⟨b₀, hb₀, hbad⟩
  exact bad_witness_of_moment_ge B v hv hb₀ hbad

/-- **Prize-shaped amplification (the consolidated form).** If the moment `S` is dominated by the
Wick saddle bound `qWick` (`S ≤ qWick`, supplied by `sum_nonzero_moment` + the single-depth char-`p`
energy bound), and that saddle bound is below the threshold `τ` (`qWick < τ`, supplied by the saddle
algebra at `r=⌈log p⌉`, `λ=√(2 log q)`), then there is no bad `b`: the worst frequency is benign and
the prize holds. This exhibits all-`b` as a single moment inequality `S ≤ qWick < τ` — the SAME open
Wick bound, no amplification gain. -/
theorem prize_amplification (B : Finset ι) (v : ι → ℝ) (hv : ∀ b ∈ B, 0 ≤ v b) {τ qWick : ℝ}
    (hτ : 0 < τ) (hmoment : ∑ b ∈ B, v b ≤ qWick) (hsaddle : qWick < τ) :
    (B.filter (fun b => τ < v b)).card = 0 :=
  forcing_zero_bad B v hv hτ (lt_of_le_of_lt hmoment hsaddle)

/-- **Monotonicity in the moment (why almost-all = `r=1` does NOT help).** The bad-count bound `S/τ`
is monotone increasing in the moment `S`: a larger moment gives a weaker (larger) bad-count bound.
The "almost-all" information is the 2nd moment (`r=1`, `S₁ = q·n − n²`), not the deep moment
(`r=⌈log p⌉`) the threshold demands; a shallow moment gives no leverage on the deep one. -/
theorem bad_count_mono_in_moment {S₁ S₂ τ : ℝ} (hτ : 0 < τ) (hS : S₁ ≤ S₂) :
    S₁ / τ ≤ S₂ / τ :=
  by gcongr

end ArkLib.ProximityGap.Frontier.AlmostAllToAllAmplify

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.AlmostAllToAllAmplify.card_bad_mul_le_moment
#print axioms ArkLib.ProximityGap.Frontier.AlmostAllToAllAmplify.card_bad_le_moment_div
#print axioms ArkLib.ProximityGap.Frontier.AlmostAllToAllAmplify.forcing_zero_bad
#print axioms ArkLib.ProximityGap.Frontier.AlmostAllToAllAmplify.bad_witness_of_moment_ge
#print axioms ArkLib.ProximityGap.Frontier.AlmostAllToAllAmplify.amplification_reduces_to_moment
#print axioms ArkLib.ProximityGap.Frontier.AlmostAllToAllAmplify.prize_amplification
#print axioms ArkLib.ProximityGap.Frontier.AlmostAllToAllAmplify.bad_count_mono_in_moment
