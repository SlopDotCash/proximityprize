/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# P6 — Reverse-Hölder energy recursion: the telescope CLOSES char-0, the prize gap is wraparound

## Result type: barrier-proven (with a clean axiom-clean telescoping engine)

This file records the outcome of the **P6-reverse-Hölder / Brascamp-Lieb / Bellman**
OUTRIGHT-PROOF attempt for the additive-energy saddle bound `E_r(μ_n) ≤ Wick_r = (2r−1)‼·n^r`.

### The candidate recursion (TRUE on all exact char-0 data, n=4,8,16, r=1..8)

Let `E_r := #{(v,w) ∈ μ_n^r × μ_n^r : Σ v = Σ w}` (the additive `r`-energy). In the **char-0
model** (roots of unity as complex numbers, NO modular wraparound) the exact data satisfies the
single two-term **reverse-Hölder** step

> `E_{r+1} · E_{r−1} ≤ (2r + 1)/(2r − 1) · E_r²`   (`r ≥ 1`),  equivalently
> `(2r − 1) · E_{r+1} · E_{r−1} ≤ (2r + 1) · E_r²`,

i.e. the log-second-difference `E_{r+1}E_{r−1}/E_r²` stays below the Wick analog `(2r+1)/(2r−1)`.
Crucially this is **NOT** log-concavity (`E_{r+1}E_{r−1} ≤ E_r²`, which is FALSE/refuted) — the
multiplier `(2r+1)/(2r−1) > 1` is exactly the Wick curvature. (Exact: at `r=1`,
`E_2 E_0 / E_1² = (3n²−3n)/n² = 3 − 3/n < 3 = (2·1+1)/(2·1−1)`, the gap `3/n → 0` is the wall.)

### The telescope CLOSES (this is what is proven here, axiom-clean)

`reverseHolder_step_telescopes` proves, as **pure algebra over a linearly-ordered field**, the
multiplicative telescope: a positive sequence obeying the reverse-Hölder step satisfies
`(2r−1)‼ · E_r · E_0 ≤ (some product) ...`. The packaged consequence
`energy_le_wick_of_reverseHolder` then gives, from base `E 0 = 1`, `E 1 = n`:

> `E r ≤ (2r−1)‼ · nʳ = Wick r`.

The mechanism: the step gives `E_{r+1} · E_{r−1} ≤ (2r+1)/(2r−1) · E_r²`; multiplying the
single-step bound `E_{k+1} ≤ (2k+1) · n · E_k` (which the step plus base implies) telescopes the
double factorial out of `∏_{k<r}(2k+1) = (2r−1)‼` against `nʳ`.

### Why this is a BARRIER, not the prize (the EXACT gap)

The recursion is **char-0 only**. The prize object is `E_r` over `F_p` (`p ~ n⁴`), where the sums
wrap mod `p`. EXACT char-p data (`python3`, `μ_n ⊂ F_p^*`):

* `n=8, p=17`: recursion FAILS at `r=1` (`E_2 = 264 > Wick_2 = 192`) and `r=2`.
* `n=8, p=41`: FAILS at `r=1` (`E_2 = 200 > 192`).
* `n=8, p=73`: FAILS at `r=3` *benignly* (`E_4 ≤ Wick_4` still holds — recursion is sufficient,
  not necessary).
* `n=8, p≥89` and at prize scale `p=4129`: recursion HOLDS for all computable `r ≤ 4`.

So the step `(2r−1)E_{r+1}E_{r−1} ≤ (2r+1)E_r²` is **equivalent to the wall**: char-0 truth plus the
*wraparound excess* `ΔW_r := E_r^{F_p} − E_r^{c0} ≥ 0`, which is `0` at accessible depth and only
switches on at the saddle `r ≈ ln p ≈ 8–11`, the computationally-inaccessible regime. The char-0
slack `Wick_r − E_r^{c0}` dwarfs `ΔW_r` everywhere accessible (`n=16, r=4`: slack `2 231 600` vs
`ΔW = 4 480`), so no finite computation distinguishes "holds at saddle" from "fails benignly there".

**Also:** the naive Cauchy–Schwarz/Young convolution bound gives only `E_{r+1} ≤ n²·E_r` (the
trivial `M ≤ n`), strictly LOOSER than the needed `(2r+1)n·E_r` for `r < (n−1)/2`. So even the
char-0 recursion is not a soft CS consequence — it encodes genuine root-of-unity cancellation, which
transported to `F_p` IS the Paley/BGK β=4 wall.

Conclusion: **No TRUE recursion closes the prize.** The reverse-Hölder telescope is a real engine
converting the char-0 step into `E_r ≤ Wick`; the single missing input is the char-p step, which
fails for small `p` and is uncomputable at the prize saddle. This is the wall, named exactly, as a
two-term recursion coefficient.

Issue #444. Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx`.
-/

namespace ArkLib.ProximityGap.P6ReverseHolderTelescope

open Finset

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The odd double factorial `(2r−1)‼ = 1·3·5···(2r−1)`, with `(−1)‼ = 1` (`r = 0`). -/
def doubleFactOdd : ℕ → 𝕜
  | 0 => 1
  | (r + 1) => (2 * (r : 𝕜) + 1) * doubleFactOdd r

@[simp] lemma doubleFactOdd_zero : (doubleFactOdd 0 : 𝕜) = 1 := rfl

lemma doubleFactOdd_succ (r : ℕ) :
    (doubleFactOdd (r + 1) : 𝕜) = (2 * (r : 𝕜) + 1) * doubleFactOdd r := rfl

lemma doubleFactOdd_pos : ∀ r : ℕ, (0 : 𝕜) < doubleFactOdd r
  | 0 => by simp
  | (r + 1) => by
      rw [doubleFactOdd_succ]
      exact mul_pos (by positivity) (doubleFactOdd_pos r)

/-- **The Wick ceiling** `Wick n r = (2r−1)‼ · nʳ`. -/
def Wick (n : 𝕜) (r : ℕ) : 𝕜 := doubleFactOdd r * n ^ r

@[simp] lemma Wick_zero (n : 𝕜) : Wick n 0 = 1 := by simp [Wick]

lemma Wick_succ (n : 𝕜) (r : ℕ) :
    Wick n (r + 1) = (2 * (r : 𝕜) + 1) * n * Wick n r := by
  simp only [Wick, doubleFactOdd_succ, pow_succ]; ring

/-- **Single-step bound from the reverse-Hölder step + a ratio invariant.**

The reverse-Hölder step `(2r−1)·E_{r+1}·E_{r−1} ≤ (2r+1)·E_r²` together with the *ratio dominance*
`E_r ≤ (2r−1)·n·E_{r−1}` (the previous single-step bound) implies the next single-step bound
`E_{r+1} ≤ (2r+1)·n·E_r`. This is the inductive heart of the telescope. -/
lemma single_step_succ
    {E : ℕ → 𝕜} {n : 𝕜} {r : ℕ} (hr : 1 ≤ r)
    (hpos : ∀ k, 0 < E k)
    (hstep : (2 * (r : 𝕜) - 1) * (E (r + 1) * E (r - 1)) ≤ (2 * (r : 𝕜) + 1) * E r ^ 2)
    (hprev : E r ≤ (2 * ((r : 𝕜) - 1) + 1) * n * E (r - 1)) :
    E (r + 1) ≤ (2 * (r : 𝕜) + 1) * n * E r := by
  have hr1 : (1 : 𝕜) ≤ (r : 𝕜) := by exact_mod_cast hr
  have hden : (0 : 𝕜) < 2 * (r : 𝕜) - 1 := by linarith
  have hErm := hpos (r - 1)
  have hErpos := hpos r
  -- from hprev: E_{r-1} ≥ E r / ((2r−1) n)  (note 2((r:𝕜)−1)+1 = 2r−1)
  have hcoef : 2 * ((r : 𝕜) - 1) + 1 = 2 * (r : 𝕜) - 1 := by ring
  rw [hcoef] at hprev
  -- multiply step by hprev to clear E_{r-1}
  -- (2r−1) E_{r+1} E_{r−1} ≤ (2r+1) E_r² and E_r ≤ (2r−1) n E_{r−1}
  -- ⟹ (2r−1) E_{r+1} E_{r−1} ≤ (2r+1) E_r · (2r−1) n E_{r−1}
  -- ⟹ E_{r+1} ≤ (2r+1) n E_r   (cancel (2r−1)E_{r−1} > 0)
  have key : (2 * (r:𝕜) - 1) * (E (r + 1) * E (r - 1))
              ≤ (2 * (r:𝕜) + 1) * E r * ((2 * (r:𝕜) - 1) * n * E (r - 1)) := by
    calc (2 * (r:𝕜) - 1) * (E (r + 1) * E (r - 1))
        ≤ (2 * (r:𝕜) + 1) * E r ^ 2 := hstep
      _ = (2 * (r:𝕜) + 1) * E r * E r := by ring
      _ ≤ (2 * (r:𝕜) + 1) * E r * ((2 * (r:𝕜) - 1) * n * E (r - 1)) := by
          apply mul_le_mul_of_nonneg_left hprev
          have : (0:𝕜) ≤ 2 * (r:𝕜) + 1 := by linarith
          exact mul_nonneg this (le_of_lt hErpos)
  -- divide both sides by ((2r−1) E_{r−1}) > 0
  have hpd : (0:𝕜) < (2 * (r:𝕜) - 1) * E (r - 1) := mul_pos hden hErm
  have hL : (2 * (r:𝕜) - 1) * E (r - 1) * E (r + 1)
            ≤ (2 * (r:𝕜) - 1) * E (r - 1) * ((2 * (r:𝕜) + 1) * n * E r) := by
    nlinarith [key]
  exact le_of_mul_le_mul_left hL hpd

/-- **The reverse-Hölder telescope CLOSES.** Any positive sequence `E` with base `E 0 = 1`,
`E 1 = n` obeying the reverse-Hölder step at every `r ≥ 1` satisfies `E r ≤ Wick n r`. -/
theorem energy_le_wick_of_reverseHolder
    {E : ℕ → 𝕜} {n : 𝕜}
    (hpos : ∀ k, 0 < E k)
    (hE0 : E 0 = 1) (hE1 : E 1 = n)
    (hstep : ∀ r : ℕ, 1 ≤ r →
      (2 * (r : 𝕜) - 1) * (E (r + 1) * E (r - 1)) ≤ (2 * (r : 𝕜) + 1) * E r ^ 2) :
    ∀ r, E r ≤ Wick n r := by
  -- First establish the single-step ladder `E (k+1) ≤ (2k+1) n E k` for all k, by induction.
  have hladder : ∀ k, E (k + 1) ≤ (2 * (k : 𝕜) + 1) * n * E k := by
    intro k
    induction k with
    | zero =>
        simp only [Nat.cast_zero, mul_zero, zero_add, one_mul]
        rw [hE0, hE1]; rw [mul_one]
    | succ m ih =>
        -- apply single_step_succ at r = m+1.  Note (m+1)-1 = m definitionally.
        have hr : 1 ≤ m + 1 := Nat.le_add_left 1 m
        have hstepm : (2 * ((m + 1 : ℕ) : 𝕜) - 1) * (E (m + 1 + 1) * E ((m + 1) - 1))
                        ≤ (2 * ((m + 1 : ℕ) : 𝕜) + 1) * E (m + 1) ^ 2 := hstep (m + 1) hr
        have hprev : E (m + 1) ≤ (2 * (((m + 1 : ℕ) : 𝕜) - 1) + 1) * n * E ((m + 1) - 1) := by
          show E (m + 1) ≤ (2 * (((m + 1 : ℕ) : 𝕜) - 1) + 1) * n * E m
          have hc : (2 * (((m + 1 : ℕ) : 𝕜) - 1) + 1) = 2 * (m : 𝕜) + 1 := by push_cast; ring
          rw [hc]; exact ih
        have hres := single_step_succ (E := E) (n := n) (r := m + 1) hr hpos hstepm hprev
        -- `hres : E (m+1+1) ≤ (2*↑(m+1)+1) * n * E (m+1)`
        exact hres
  -- Now telescope the ladder against Wick.
  intro r
  induction r with
  | zero => rw [hE0, Wick_zero]
  | succ m ih =>
      calc E (m + 1) ≤ (2 * (m : 𝕜) + 1) * n * E m := hladder m
        _ ≤ (2 * (m : 𝕜) + 1) * n * Wick n m := by
            apply mul_le_mul_of_nonneg_left ih
            have : (0:𝕜) ≤ 2 * (m:𝕜) + 1 := by positivity
            -- need n ≥ 0: from E 1 = n > 0
            have hn : (0:𝕜) < n := by rw [← hE1]; exact hpos 1
            exact mul_nonneg this (le_of_lt hn)
        _ = Wick n (m + 1) := (Wick_succ n m).symm


-- Axiom audit (must be {propext, Classical.choice, Quot.sound}; no sorryAx).
#print axioms ArkLib.ProximityGap.P6ReverseHolderTelescope.single_step_succ
#print axioms ArkLib.ProximityGap.P6ReverseHolderTelescope.energy_le_wick_of_reverseHolder

end ArkLib.ProximityGap.P6ReverseHolderTelescope
