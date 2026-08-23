/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineHeavySetBound

/-!
# Issue #232: the per-line first-moment bound (round 14d)

The per-line decode chain needs the first moment `M := ∑_γ |Λ(γ,a)|` bounded uniformly (the
round-14 numeric probe found it field-size independent, `≈ poly(n)`). This file proves the exact
combinatorial bound by the **one-vote-per-coordinate** primitive (the single-codeword form of the
round-14 double counting, = Hab25 Lemma 1 / `[AHIV17]`):

**Single-codeword vote count.** On a line `{f + γ·g}` with nowhere-zero direction (`g i ≠ 0`),
each coordinate `i` agrees with a fixed codeword `c` at *exactly one* line parameter
`γᵢ(c) = (cᵢ − fᵢ)/gᵢ`. Hence summing the per-point agreement over the whole line counts each
coordinate once:
    `∑_γ |agree(f+γg, c)| = n`   (`sum_agree_single_eq`).
So a codeword can be in the agreement-`≥a` list at most `⌊n/a⌋` line points:
    `#{γ : c ∈ Λ(γ,a)} · a ≤ n`   (`single_decode_card_mul_le`).

**Per-line first moment.** Summing over the code `C` (first-moment = sum of per-codeword counts):
    `(∑_γ |Λ(γ,a)|) · a ≤ |C| · n`   (`line_first_moment_bound`).

This closes the per-line chain to three self-contained moments: first (this file, `M·a ≤ |C|·n`),
second (`line_second_moment_bound`, off-diagonal a distance-uniform per-pair constant), and the
heavy-set tail (`heavyLineSet_card_bound`, `#{|Λ|≥L}·L² ≤` second moment). Together: on every line
in the `2a > n` window, the heavy-decode set is `≤ (|C|·n/a + (|C|²−|C|)·2(n−d)/(2a−d))/L²` — a
fully explicit per-line "few bad points", the object the per-code threshold `δ*` is read from.

Axiom-clean: `propext, Classical.choice, Quot.sound`.
-/

open Finset

namespace LinePairCooccurrence

variable {n : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **One vote per coordinate (single codeword).** For a nowhere-zero direction, each coordinate `i`
agrees with `c` at exactly one line parameter: `{γ : f i + γ·g i = c i}` is a singleton. -/
theorem single_vote_card (f g c : Fin n → F) (hg : ∀ i, g i ≠ 0) (i : Fin n) :
    (Finset.univ.filter (fun γ : F => linePt f g γ i = c i)).card = 1 := by
  classical
  rw [Finset.card_eq_one]
  refine ⟨(c i - f i) / g i, ?_⟩
  ext γ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, linePt]
  rw [eq_div_iff (hg i)]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- **Single-codeword agreement sum.** Summing the per-point agreement of a fixed codeword over the
whole line counts each coordinate exactly once: `∑_γ |agree(f+γg, c)| = n`. -/
theorem sum_agree_single_eq (f g c : Fin n → F) (hg : ∀ i, g i ≠ 0) :
    ∑ γ : F, (agreeSet (linePt f g γ) c).card = n := by
  classical
  -- expand each agreement count as a sum of indicators, swap the order, count one vote per coord
  have hexp : ∀ γ : F, (agreeSet (linePt f g γ) c).card
      = ∑ i : Fin n, (if linePt f g γ i = c i then 1 else 0) := by
    intro γ
    rw [agreeSet, Finset.card_filter]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have : ∀ i : Fin n, ∑ γ : F, (if linePt f g γ i = c i then 1 else 0)
      = (Finset.univ.filter (fun γ : F => linePt f g γ i = c i)).card := by
    intro i; rw [Finset.card_filter]
  simp_rw [this, single_vote_card f g c hg]
  simp

/-- **Single-codeword decode count.** A fixed codeword is in the agreement-`≥a` list at most
`⌊n/a⌋` line points: `#{γ : a ≤ |agree(f+γg, c)|} · a ≤ n`. (Markov on the per-point agreement,
whose total over the line is `n`.) -/
theorem single_decode_card_mul_le (f g c : Fin n → F) (a : ℕ) (hg : ∀ i, g i ≠ 0) :
    (Finset.univ.filter (fun γ : F => a ≤ (agreeSet (linePt f g γ) c).card)).card * a ≤ n := by
  classical
  set S := Finset.univ.filter (fun γ : F => a ≤ (agreeSet (linePt f g γ) c).card) with hS
  calc S.card * a
      = ∑ _γ ∈ S, a := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ S, (agreeSet (linePt f g γ) c).card :=
        Finset.sum_le_sum (fun γ hγ => (Finset.mem_filter.mp hγ).2)
    _ ≤ ∑ γ : F, (agreeSet (linePt f g γ) c).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = n := sum_agree_single_eq f g c hg

/-- **The per-line first-moment bound.** On a line with nowhere-zero direction, the per-line list
mass `M = ∑_γ |Λ(γ,a)|` obeys `M · a ≤ |C| · n` — field-size independent, exactly the round-14
numeric probe's `M ≈ poly(n)`. Proof: the first moment reindexes (Fubini over the code) to the sum
of single-codeword decode counts, each `≤ n/a`. -/
theorem line_first_moment_bound (C : Finset (Fin n → F)) (f g : Fin n → F) (a : ℕ)
    (hg : ∀ i, g i ≠ 0) :
    (∑ γ : F, (lineList C f g a γ).card) * a ≤ C.card * n := by
  classical
  -- Fubini: ∑_γ |Λ(γ)| = ∑_γ #{c ∈ C : a ≤ agree} = ∑_{c ∈ C} #{γ : a ≤ agree}
  have hfubini : ∑ γ : F, (lineList C f g a γ).card
      = ∑ c ∈ C, (Finset.univ.filter
          (fun γ : F => a ≤ (agreeSet (linePt f g γ) c).card)).card := by
    simp_rw [lineList, Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hfubini, Finset.sum_mul]
  calc ∑ c ∈ C, (Finset.univ.filter
          (fun γ : F => a ≤ (agreeSet (linePt f g γ) c).card)).card * a
      ≤ ∑ _c ∈ C, n :=
        Finset.sum_le_sum (fun c _ => single_decode_card_mul_le f g c a hg)
    _ = C.card * n := by rw [Finset.sum_const, smul_eq_mul]

/-- **Fully explicit per-line heavy-decode bound (the three-moment capstone).** Combining the
first-moment bound (`M·a ≤ |C|·n`, this file) with the second-moment bound and the heavy-set tail,
on every line with nowhere-zero direction in the `2a > n` window, with `0 < a`:
    `#{γ : |Λ(γ,a)| ≥ L} · L² · a · (2a−d) ≤ |C|·n·(2a−d) + a·(|C|²−|C|)·2(n−d)`.
Every quantity on the right is an explicit `(n, d, a, |C|)` polynomial with NO `∑_γ` left — the
per-line decode heaviness is bounded by code parameters alone, field-size-independent (the
round-14 numeric probe's `M ≈ poly(n)`). This is the per-line "few bad points" the per-code
threshold `δ*` is read from. -/
theorem heavyLineSet_card_explicit_bound (C : Finset (Fin n → F)) (f g : Fin n → F)
    (a d L : ℕ) (hg : ∀ i, g i ≠ 0) (hn : n < 2 * a)
    (hd : ∀ p ∈ C.offDiag, d ≤ (supp p.1 p.2).card) :
    (heavyLineSet C f g a L).card * L ^ 2 * a * (2 * a - d)
      ≤ C.card * n * (2 * a - d) + a * ((C.card * C.card - C.card) * (2 * (n - d))) := by
  -- heavy-set ≤ second moment (×(2a−d)); then bound the first-moment term ∑|Λ| via M·a ≤ |C|·n.
  have hHeavy := heavyLineSet_card_bound C f g a d L hg hn hd
  have hFirst := line_first_moment_bound C f g a hg
  -- multiply the heavy-set bound by `a` and substitute the first-moment bound
  calc (heavyLineSet C f g a L).card * L ^ 2 * a * (2 * a - d)
      = ((heavyLineSet C f g a L).card * L ^ 2 * (2 * a - d)) * a := by ring
    _ ≤ ((∑ γ : F, (lineList C f g a γ).card) * (2 * a - d)
          + (C.card * C.card - C.card) * (2 * (n - d))) * a :=
        Nat.mul_le_mul_right _ hHeavy
    _ = ((∑ γ : F, (lineList C f g a γ).card) * a) * (2 * a - d)
          + a * ((C.card * C.card - C.card) * (2 * (n - d))) := by ring
    _ ≤ (C.card * n) * (2 * a - d) + a * ((C.card * C.card - C.card) * (2 * (n - d))) := by
        have := Nat.mul_le_mul_right (2 * a - d) hFirst
        omega

end LinePairCooccurrence
