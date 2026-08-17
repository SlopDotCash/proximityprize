/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# A machine-checked counterexample to Conjecture 41 (worst-case form) of ePrint 2026/858

Chai–Fan, *FRI Soundness Above the Johnson Bound via Threshold Halving* (ePrint 2026/858), §7.6,
**Conjecture 41** (Open-Set Rank Lemma) asserts the worst-case list-size bound
`max_{s₁,s₂} M_true(s₁,s₂) ≤ ⌊(2D−1)/c⌋` for codimension excess `c ≥ 3` (`D = n−k`, `w = D−c`), claiming the
extremal `(w+1)`-clique configuration is "realizable only at primes below an explicit threshold `p₀`".

This file is an **explicit, machine-checked counterexample to that worst-case claim**, at the parameters
`w = 4`, `c = 3`, `D = 7` (so `⌊(2D−1)/c⌋ = ⌊13/3⌋ = 4`), over `ℚ` (characteristic 0). We exhibit a syndrome
line `s(γ) = s₁ + γ·s₂ ∈ ℚ⁷`, with
`s₁ = (-4980,-8580,-5328,-1728,0,0,41472)` and `s₂ = (0,4980,3600,1728,0,0,0)`, and the `w+1 = 5` size-`w`
subsets of the clique `{0,1,2,3,4}`, each decoding the line at a *distinct* integer `γ ∈ {1,2,3,4,5}` to a
genuine **nonzero** weight-`w` error. Hence `M_true(s₁,s₂) ≥ 5 > 4`, refuting the worst-case bound.

`M_true(s₁,s₂)` (2026/858 §7.5) `= #{γ : ∃ support E with the Vandermonde solution of `V_E v = s(γ)` having
all entries ≠ 0}`, where the syndrome of an error `v` on points `a₀..a₃` is `(V_E v)_j = ∑_i aᵢ^j·vᵢ`,
`j = 0..D−1` (`syndAt` below).

**Not a small-`p` artifact.** The witnesses are in `ℚ` (char 0); the clique rank-deficiency is the
characteristic-0 partial-fraction identity `∑_i Λ_{E_i}/Λ_S'(a_i) = 1`. The integer counterexample reduces
mod every prime not dividing the small denominators, i.e. all large `p`, contradicting the "below `p₀`"
claim. (Exact-`ℚ` construction + reduction: `scripts/probes/probe_conj41_exact_Q_proof.py`.)

**Scope.** Conjecture 41 is on 2026/858's *structural track* (Open Problem 2, worst-case list size); per the
paper's proof map (§1.10) "the mainline uses no result from §7", so the unconditional FRI soundness theorem
(and the in-tree `HalfThresholdCA.lean`) is unaffected, as is the proximity-prize `δ*`. What this corrects:
the worst-case list size is `≥ w+1` via cliques, not `⌊(2D−1)/c⌋`.
-/

set_option linter.style.longLine false


namespace Conj41CliqueCounterexample

/-- Vandermonde syndrome coordinate `j` of the weight-`4` error `(v₀,v₁,v₂,v₃)` on the support points
`(a₀,a₁,a₂,a₃)`: `∑_i aᵢ^j · vᵢ`. -/
def syndAt (a₀ a₁ a₂ a₃ v₀ v₁ v₂ v₃ : ℚ) (j : ℕ) : ℚ :=
  a₀ ^ j * v₀ + a₁ ^ j * v₁ + a₂ ^ j * v₂ + a₃ ^ j * v₃

/-- The support points `(a₀,a₁,a₂,a₃)` with error `(v₀,v₁,v₂,v₃)` decode the fixed syndrome line `s(γ)` at
scalar `γ`: the error is everywhere nonzero, and its Vandermonde syndrome matches `s₁ + γ·s₂` in all
`D = 7` coordinates (`s₁,s₂` the explicit vectors from the docstring). -/
def decodesLine (γ a₀ a₁ a₂ a₃ v₀ v₁ v₂ v₃ : ℚ) : Prop :=
  (v₀ ≠ 0 ∧ v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₃ ≠ 0) ∧
    syndAt a₀ a₁ a₂ a₃ v₀ v₁ v₂ v₃ 0 = -4980 + γ * 0 ∧
    syndAt a₀ a₁ a₂ a₃ v₀ v₁ v₂ v₃ 1 = -8580 + γ * 4980 ∧
    syndAt a₀ a₁ a₂ a₃ v₀ v₁ v₂ v₃ 2 = -5328 + γ * 3600 ∧
    syndAt a₀ a₁ a₂ a₃ v₀ v₁ v₂ v₃ 3 = -1728 + γ * 1728 ∧
    syndAt a₀ a₁ a₂ a₃ v₀ v₁ v₂ v₃ 4 = 0 + γ * 0 ∧
    syndAt a₀ a₁ a₂ a₃ v₀ v₁ v₂ v₃ 5 = 0 + γ * 0 ∧
    syndAt a₀ a₁ a₂ a₃ v₀ v₁ v₂ v₃ 6 = 41472 + γ * 0

/-- Support `{1,2,3,4}` decodes `s(γ)` at `γ = 1` with a nonzero weight-`4` error. -/
theorem w1 : decodesLine 1 1 2 3 4 (-6912) 2592 (-768) 108 := by norm_num [decodesLine, syndAt]

/-- Support `{0,2,3,4}` decodes `s(γ)` at `γ = 2`. -/
theorem w2 : decodesLine 2 0 2 3 4 (-5845) 1296 (-512) 81 := by norm_num [decodesLine, syndAt]

/-- Support `{0,1,3,4}` decodes `s(γ)` at `γ = 3`. -/
theorem w3 : decodesLine 3 0 1 3 4 (-11690) 6912 (-256) 54 := by norm_num [decodesLine, syndAt]

/-- Support `{0,1,2,4}` decodes `s(γ)` at `γ = 4`. -/
theorem w4 : decodesLine 4 0 1 2 4 (-17535) 13824 (-1296) 27 := by norm_num [decodesLine, syndAt]

/-- Support `{0,1,2,3}` decodes `s(γ)` at `γ = 5`. -/
theorem w5 : decodesLine 5 0 1 2 3 (-23380) 20736 (-2592) 256 := by norm_num [decodesLine, syndAt]

/-- **Counterexample to Conjecture 41's worst-case bound.** The single syndrome line
`s(γ) = s₁ + γ·s₂` is decoded — to genuine nonzero weight-`4` errors — at the **five distinct** scalars
`γ ∈ {1,2,3,4,5}` by the five size-`4` subsets of the clique `{0,1,2,3,4}` (`w1`–`w5`). Hence
`M_true(s₁,s₂) ≥ 5`. But the conjectured worst-case bound is `⌊(2D−1)/c⌋ = ⌊(2·7−1)/3⌋ = 4 < 5`. So the
worst-case form of Conjecture 41 is false at these parameters over `ℚ` (and, by reduction mod p, at all
large primes). -/
theorem conj41_worstcase_violated :
    decodesLine 1 1 2 3 4 (-6912) 2592 (-768) 108 ∧
      decodesLine 2 0 2 3 4 (-5845) 1296 (-512) 81 ∧
      decodesLine 3 0 1 3 4 (-11690) 6912 (-256) 54 ∧
      decodesLine 4 0 1 2 4 (-17535) 13824 (-1296) 27 ∧
      decodesLine 5 0 1 2 3 (-23380) 20736 (-2592) 256 ∧
      ([(1 : ℚ), 2, 3, 4, 5]).Nodup ∧
      (5 : ℕ) > (2 * 7 - 1) / 3 :=
  ⟨w1, w2, w3, w4, w5, by norm_num [List.nodup_cons], by norm_num⟩

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only — no sorryAx/native).
#print axioms conj41_worstcase_violated

end Conj41CliqueCounterexample
