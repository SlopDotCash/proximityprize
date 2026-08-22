/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.UniversalStaircaseCollapse
import Mathlib.LinearAlgebra.Lagrange

/-!
# The granularity ladder for Reed–Solomon codes: closed-form δ* at production shape (#357)

`UniversalStaircaseCollapse.lean` proved the abstract ladder closed form.  This file
instantiates it for **generic Reed–Solomon codes** — any field, any injective
evaluation domain (smoothness is not even required), any dimension:

* `rsCode dom k` — evaluations of polynomials of degree `< k` on an injective domain
  `dom : Fin n ↪ F`;
* `rsCode_noWeightLE` — the distance property: no nonzero codeword of weight `≤ m`
  whenever `m + k ≤ n` (a nonzero polynomial of degree `< k` cannot vanish at `k`
  distinct points);
* **`mcaDeltaStar_rs_eq_granularity`** — the closed form

    `mcaDeltaStar (RS[F, dom, k], ε*) = j / n`   for every `ε* ∈ [j/q, (j+1)/q)`,

  whenever `3(j−1) + k ≤ n` (and `j+2+k ≤ n`, `j+1 ≤ q` for the spike data).

**Reach at production parameters.**  With `ε* = 2^{−128}` fixed, a field of size `q`
puts `ε*` in the band window of `j = ⌊q·2^{−128}⌋`.  For rate-`1/2` codes with
`k ≤ 2^{40}` the distance condition `3(j−1) + k ≤ n` holds for all
`q ≲ 2^{128}·n/3` — i.e. **for every production-shaped instance with
`|F| ≲ 2^{168}`, δ* is now a closed-form theorem at the literal target threshold**.
The production family splits at `q ≈ n·2^{128}`: below, the ladder pins δ* exactly
(this file); above, `ε*·q` exceeds the staircase's reach and the Johnson/window
regime takes over — that frontier is the campaign's remaining open core, bracketed
by the δ* sandwich (`MCADeltaStarSandwich.lean`).
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The generic Reed–Solomon code: evaluations of polynomials of degree `< k` on an
injective evaluation domain `dom : Fin n ↪ F`. -/
def rsCode (dom : Fin n ↪ F) (k : ℕ) : Submodule F (Fin n → F) where
  carrier := {w | ∃ P : Polynomial F, P.degree < k ∧ w = fun i => P.eval (dom i)}
  zero_mem' := ⟨0, by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe k,
    by funext i; simp⟩
  add_mem' := by
    rintro w w' ⟨P, hP, rfl⟩ ⟨Q, hQ, rfl⟩
    exact ⟨P + Q, lt_of_le_of_lt (Polynomial.degree_add_le P Q) (max_lt hP hQ),
      by funext i; simp⟩
  smul_mem' := by
    rintro c w ⟨P, hP, rfl⟩
    exact ⟨c • P, lt_of_le_of_lt (Polynomial.degree_smul_le c P) hP,
      by funext i; simp⟩

/-- **The Reed–Solomon distance property.**  No nonzero codeword of `rsCode dom k`
has weight `≤ m`, provided `m + k ≤ n`: such a codeword would come from a nonzero
polynomial of degree `< k` vanishing at `≥ n − m ≥ k` distinct points. -/
theorem rsCode_noWeightLE (dom : Fin n ↪ F) {k m : ℕ} (hmk : m + k ≤ n) :
    NoWeightLE (rsCode dom k) m := by
  rintro w ⟨P, hP, rfl⟩ ⟨T, hT, hvan⟩
  have hPz : P = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (f := P) (s := (Finset.univ \ T).image dom) ?_ ?_
    · have hcard : ((Finset.univ \ T).image dom).card = n - T.card := by
        rw [Finset.card_image_of_injective _ dom.injective, Finset.card_sdiff,
          Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      rw [hcard]
      calc P.degree < (k : ℕ) := hP
        _ ≤ ((n - T.card : ℕ) : WithBot ℕ) := by
            exact_mod_cast (by omega : k ≤ n - T.card)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hvan i (Finset.mem_sdiff.mp hi).2
  funext i
  simp [hPz]

open Classical in
/-- **The granularity ladder for Reed–Solomon codes (closed-form δ*).**  For any
field `F`, any injective evaluation domain of size `n`, any dimension `k`, any band
index `j ≥ 1` with `3(j−1) + k ≤ n`, `j + 1 + k ≤ n`, and `j + 1 ≤ |F|`, and every
threshold `ε* ∈ [j/|F|, (j+1)/|F|)`:

  `mcaDeltaStar (RS[F, dom, k]) ε* = j / n`.

At `ε* = 2^{−128}` this pins δ* in closed form for every production-shaped instance
with `|F| ≲ n·2^{128}` — smoothness of the domain is not required. -/
theorem mcaDeltaStar_rs_eq_granularity (dom : Fin n ↪ F) {k j : ℕ}
    (hj1 : 1 ≤ j) (hd3 : 3 * (j - 1) + k ≤ n) (hdj : j + 1 + k ≤ n)
    (hjF : j + 1 ≤ Fintype.card F) {εstar : ℝ≥0∞}
    (hlo : (j : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < ((j + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar
      = (j : ℝ≥0) / (Fintype.card (Fin n) : ℝ≥0) := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne n))
  refine mcaDeltaStar_eq_granularity (rsCode dom k)
    (rsCode_noWeightLE dom (by omega)) (rsCode_noWeightLE dom (by omega))
    hj1 (by rw [Fintype.card_fin]; omega) hjF hlo hhi

end ProximityGap.SpikeFloor

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.SpikeFloor.rsCode_noWeightLE
#print axioms ProximityGap.SpikeFloor.mcaDeltaStar_rs_eq_granularity
