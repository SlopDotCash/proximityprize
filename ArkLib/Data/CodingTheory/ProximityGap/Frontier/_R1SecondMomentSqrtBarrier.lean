/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The intrinsic √-barrier of every second-moment LD⇒MCA argument (Route R1, ABF26 §5)

**Route R1** of the end-to-end δ* pin asks whether a good *list-decoding* bound implies a good
*mutual-correlated-agreement* (MCA) bound — a hoped-for bypass of the Face-3 Paley/BGK wall.
The two in-tree LD⇒MCA arrows are both **proven** axiom-clean:

* **Route A** — `InterleavedMCACollapse.mcaBad_card_le_interleavedList` (the ABF26 §5 collapse
  through the interleaved code `C^{≡2}`): `#mcaBad(t) ≤ 1 + (n−(2t−n))·Λ₂(2t−n)`, the interleaved
  list taken at the **doubled radius** `2t−n = (1−2δ)n`.  The radius doubling is *necessary* (the
  module records an exhaustive `F₃` counterexample to the same-radius form).
* **Route B** — `CodingTheory.linear_listSize_to_epsMCA_gcxk25` (ABF26 T5.1 = GCXK25 Thm 3):
  list-decoding at `δ_LD` with list `L` gives `ε_mca(C, 1−√(1−δ_LD+η)) ≤ (L²·δ_LD·n + 1/η)/q` — the
  **Johnson lift** `J(δ_LD) = 1−√(1−δ_LD)`.

This file isolates the **algebraic reason** both arrows stop at the *lower edge* of the prize
window `(1−√ρ, 1−ρ)`.  Both go through the GCXK25 second-moment master inequality
(`GCXK25SecondMoment.card_le_of_second_moment`)

  `N · S² ≤ n · (S + (N−1)·B)`,

with member-size lower bound `S = s·n` and pairwise-overlap upper bound `B = b·n`.  The theorem
`secondMoment_card_bound` below shows this inequality bounds the bad count `N` **if and only if**
`s² > b`, with the explicit bound `N ≤ (s − b)/(s² − b)`; and `secondMoment_unbounded_of_le` shows
that when `s² ≤ b ≤ s` the inequality places *no* upper bound on `N` (it holds for arbitrarily large
`N`).  At the Reed–Solomon values `s = 1−δ` (the agreement-domain fraction of a `δ`-close word) and
`b = ρ` (the unique-decoding overlap fraction), the threshold `s² > b` is exactly

  `(1−δ)² > ρ  ⟺  δ < 1 − √ρ  =  the Johnson radius`,

recorded as `rsCritical_iff_below_johnson`.  So:

> **The prize-window interior `(1−√ρ, 1−ρ)` is exactly the set `{δ : s² ≤ b}` on which the
> second-moment count is unbounded.**  No second-moment LD⇒MCA argument — Route A, Route B, or a
> direct second moment on the MCA agreement domains — can certify a finite MCA bad-count in the
> window interior, *even given a perfect list-decoding-to-capacity oracle*: the loss is intrinsic
> to the `(member size)² > overlap` threshold, not to the strength of the input list bound.

**Relation to the Paley wall.** R1's *surviving* open input (a list-decoding bound for explicit
smooth-domain RS) is genuinely **not** the Face-3 character sum `B = max_{b≠0}|Σ_{y∈μ_n} e_p(by)|`:
it is an algebraic root-counting / Guruswami–Sudan list-size question.  So R1 **does** bypass
Paley in *mechanism*.  But to reach the window interior both arrows need RS list-decoding *strictly
beyond capacity* `1−ρ` (Route A doubles the radius past `1−ρ`; Route B's Johnson lift caps the
reachable MCA radius at `1−√ρ`), and RS lists blow up super-polynomially beyond capacity.  The
bypass is therefore **genuine but dead**: it trades the (open) Paley wall for a (refuted) beyond-
capacity list bound.  The numerics are in `scripts`-style probes; this file proves only the
in-kernel real-algebra dichotomy that the probes verify.

All results are `sorry`-free.  Axiom audit at the bottom.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026; §5.
- [GCXK25] Gao, Cai, Xu, Kan. *From List-Decodability to Proximity Gaps*. eprint 2025/870; Lemma 3.
-/

namespace ProximityGap.R1SqrtBarrier

/-- **The second-moment count bound (the `s² > b` side).**  If a nonnegative real `N` satisfies the
GCXK25 master inequality `N · s² ≤ s + (N − 1) · b` (the fraction-normalized form of
`N·S² ≤ n·(S + (N−1)·B)` with `S = s·n`, `B = b·n`) and the **critical gap `b < s²`** holds, then `N`
is bounded by the explicit constant `(s − b)/(s² − b)`.  This is the regime `δ < 1 − √ρ` (below the
Johnson radius), where the second moment certifies a finite MCA bad-count. -/
theorem secondMoment_card_bound (N s b : ℝ)
    (hmaster : N * s ^ 2 ≤ s + (N - 1) * b) (hcrit : b < s ^ 2) :
    N ≤ (s - b) / (s ^ 2 - b) := by
  have hpos : 0 < s ^ 2 - b := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith [hmaster]

/-- **The second-moment count is unbounded (the `s² ≤ b` side).**  If `s² ≤ b ≤ s` (the regime
`δ ≥ 1 − √ρ`, the prize-window interior and beyond), then the master inequality
`N · s² ≤ s + (N − 1)·b` holds for **every** `N ≥ 1`.  Hence the second moment places *no* upper
bound on the bad count `N`: the count can be arbitrarily large while the inequality still holds.
This is the precise sense in which the second-moment LD⇒MCA argument *fails* in the window
interior. -/
theorem secondMoment_unbounded_of_le (N s b : ℝ)
    (hN : 1 ≤ N) (hsb : s ^ 2 ≤ b) (hbs : b ≤ s) :
    N * s ^ 2 ≤ s + (N - 1) * b := by
  -- N·s² ≤ N·b = b + (N−1)·b ≤ s + (N−1)·b, using s² ≤ b and b ≤ s.
  have h1 : N * s ^ 2 ≤ N * b := by
    apply mul_le_mul_of_nonneg_left hsb (le_trans zero_le_one hN)
  nlinarith [h1, hbs]

/-- **The exact threshold, at the Reed–Solomon values.**  With member-size fraction `s = 1 − δ`
(the agreement-domain fraction of a `δ`-close received word) and overlap fraction `b = ρ` (the
unique-decoding / minimum-distance overlap of two distinct close codewords), the critical gap
`b < s²` of `secondMoment_card_bound` is *equivalent* to `δ` lying strictly **below** the Johnson
radius `1 − √ρ`.  For `0 ≤ ρ ≤ 1` and `0 ≤ δ ≤ 1`:

  `ρ < (1 − δ)²  ⟺  δ < 1 − √ρ`.

Therefore the prize-window interior `(1 − √ρ, 1 − ρ)` is exactly `{δ : (1−δ)² ≤ ρ}`, the regime in
which `secondMoment_unbounded_of_le` applies: the second-moment LD⇒MCA arrows are unconditionally
silent there. -/
theorem rsCritical_iff_below_johnson (ρ δ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hδ1 : δ ≤ 1) :
    ρ < (1 - δ) ^ 2 ↔ δ < 1 - Real.sqrt ρ := by
  have hsqrt0 : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
  have hsd : 0 ≤ 1 - δ := by linarith
  constructor
  · intro h
    -- ρ < (1−δ)² and 0 ≤ 1−δ ⟹ √ρ < 1−δ ⟹ δ < 1−√ρ.
    have hlt : Real.sqrt ρ < 1 - δ := by
      have hsq : Real.sqrt ρ ^ 2 < (1 - δ) ^ 2 := by
        rwa [Real.sq_sqrt hρ0]
      exact lt_of_pow_lt_pow_left₀ 2 hsd hsq
    linarith
  · intro h
    -- δ < 1−√ρ ⟹ √ρ < 1−δ ⟹ ρ = (√ρ)² < (1−δ)².
    have hlt : Real.sqrt ρ < 1 - δ := by linarith
    have hsq : Real.sqrt ρ ^ 2 < (1 - δ) ^ 2 := by
      apply pow_lt_pow_left₀ hlt hsqrt0
      norm_num
    rwa [Real.sq_sqrt hρ0] at hsq

/-- **Window-interior silence, packaged.**  For any `δ` in the closed prize window
`[1 − √ρ, 1 − ρ]` (in particular the open interior), the second-moment master inequality holds for
every `N ≥ 1` at the RS values `s = 1 − δ`, `b = ρ`.  Hence the second-moment LD⇒MCA argument
imposes no finite bound on the MCA bad count anywhere in the window — independently of the input
list-decoding bound `L`. -/
theorem window_interior_secondMoment_silent (ρ δ N : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hN : 1 ≤ N)
    (hlo : 1 - Real.sqrt ρ ≤ δ) (hhi : δ ≤ 1 - ρ) :
    N * (1 - δ) ^ 2 ≤ (1 - δ) + (N - 1) * ρ := by
  have hsqrt0 : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
  have hsqrt1 : Real.sqrt ρ ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hρ1
  -- s² ≤ b: from δ ≥ 1−√ρ, i.e. 1−δ ≤ √ρ, square (both nonneg) to (1−δ)² ≤ ρ.
  have hsd : 0 ≤ 1 - δ := by nlinarith [hsqrt0, hsqrt1]
  have hs_le_sqrt : 1 - δ ≤ Real.sqrt ρ := by linarith
  have hsb : (1 - δ) ^ 2 ≤ ρ := by
    have := pow_le_pow_left₀ hsd hs_le_sqrt 2
    rwa [Real.sq_sqrt hρ0] at this
  -- b ≤ s: ρ ≤ 1−δ from δ ≤ 1−ρ.
  have hbs : ρ ≤ 1 - δ := by linarith
  exact secondMoment_unbounded_of_le N (1 - δ) ρ hN hsb hbs

/-- Non-vacuity: the explicit count bound fires below Johnson.  At `ρ = 1/4`, `δ = 9/20` (so
`s = 11/20`, `s² = 121/400 > 100/400 = b = 1/4`), any `N` with `N·s² ≤ s + (N−1)·b` obeys
`N ≤ (s − b)/(s² − b) = (11/20 − 1/4)/(121/400 − 1/4) = (6/20)/(21/400) = 40/7`. -/
example (N : ℝ) (h : N * (11 / 20 : ℝ) ^ 2 ≤ (11 / 20) + (N - 1) * (1 / 4)) :
    N ≤ ((11 / 20 : ℝ) - 1 / 4) / ((11 / 20) ^ 2 - 1 / 4) :=
  secondMoment_card_bound N (11 / 20) (1 / 4) h (by norm_num)

end ProximityGap.R1SqrtBarrier

/-! ## Axiom audit -/
#print axioms ProximityGap.R1SqrtBarrier.secondMoment_card_bound
#print axioms ProximityGap.R1SqrtBarrier.secondMoment_unbounded_of_le
#print axioms ProximityGap.R1SqrtBarrier.rsCritical_iff_below_johnson
#print axioms ProximityGap.R1SqrtBarrier.window_interior_secondMoment_silent
