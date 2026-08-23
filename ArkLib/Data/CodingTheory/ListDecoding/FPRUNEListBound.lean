/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecoding.FirstMomentListBound
import ArkLib.Data.CodingTheory.ListDecoding.FPRUNEPotential

/-!
# The FPRUNE list-decoding bound, assembled (Chen–Zhang 2025 / arXiv 2512.08017)

This file composes the two verified halves of the subspace-design polynomial list-decoding
argument into the named endpoint:

* `FirstMomentListBound.card_le_of_expectation_bounds` — the union-bound shell
  `|L| · β ≤ M ⟹ |L| ≤ M/β`;
* `FPRUNEPotential.fprune_expectation_lower` (Lemma 3.5, on top of the one-step Lemma 3.4
  `fprune_one_step`) — the per-codeword FPRUNE expectation lower bound `E_c ≥ η/(r+η)`.

Instantiating the shell's per-candidate bound `β` with the FPRUNE potential `η/(r+η)` yields the
**polynomial** list-size bound `|L| ≤ M·(r+η)/η`, the form consumed by ABF26 §4 (T4.13) and
CZ25 C3.5. The single hypothesis that remains genuinely open is the *expectation construction*:
exhibiting, for the actual subspace-design code, a probability mass `p` over FPRUNE coordinate
samplings and a per-codeword score `g c` whose expectation is `∑_T p T · g c T`, together with
the design-budget pointwise bound `∑_{c∈L} g c T ≤ M`. The combinatorial content feeding both —
Lemma 3.4 and Lemma 3.5 — is fully proven upstream.

This endpoint makes the assembly explicit and machine-checked: any construction of
`(p, g, β = η/(r+η))` discharging the two hypotheses immediately yields the polynomial bound.
-/

namespace CodingTheory.ListDecoding

open Finset

variable {α Ω : Type*}

/-- **FPRUNE list-size bound, assembled.** Given a probability mass `p` on a finite sample space
`Ω`, a per-codeword score `g`, the **FPRUNE per-codeword expectation lower bound** (Lemma 3.5,
`η/(r+η) ≤ ∑_T p T · g c T` for each `c` in the list `L`) and the **design-budget simultaneous
bound** (`∑_{c∈L} g c T ≤ M` pointwise), the list size is bounded polynomially:
`|L| ≤ M · (r+η)/η`.

This is the named list-decoding endpoint: the `η/(r+η)` potential supplied by `fprune_*`
(Lemmas 3.4/3.5) instantiated into the first-moment union-bound shell. -/
theorem fprune_list_card_le
    [Fintype Ω] (p : Ω → ℝ) (hp_nonneg : ∀ T, 0 ≤ p T) (hp_sum : ∑ T, p T = 1)
    (L : Finset α) (g : α → Ω → ℝ) (η : ℝ) (hη : 0 < η) (r : ℕ) (M : ℝ)
    (hLower : ∀ c ∈ L, η / ((r : ℝ) + η) ≤ ∑ T, p T * g c T)
    (hSimul : ∀ T, (∑ c ∈ L, g c T) ≤ M) :
    (L.card : ℝ) ≤ M * (((r : ℝ) + η) / η) := by
  have hrη : (0 : ℝ) < (r : ℝ) + η := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hη
  have hβ : 0 < η / ((r : ℝ) + η) := div_pos hη hrη
  have hbound :=
    card_le_of_expectation_bounds p hp_nonneg hp_sum L g (η / ((r : ℝ) + η)) M hβ hLower hSimul
  -- `M / (η/(r+η)) = M·(r+η)/η`.
  rwa [div_div_eq_mul_div, mul_div_assoc] at hbound

end CodingTheory.ListDecoding
