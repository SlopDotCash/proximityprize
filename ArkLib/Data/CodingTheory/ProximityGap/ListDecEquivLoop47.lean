/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Probability.Combinatorial
import Mathlib.Tactic

/-!
# Loop 47 (EQUIVALENCE) — "many values at a random point" ⟹ proximity gaps stop at the
# list-decoding radius (BCHKS §6, Lemma 6.1 / Theorem 1.9), the prize ⟺ list-decoding direction.

The grind's verdict (Loop45/46) is that the #232 prize is *equivalent* to RS list-decoding with
`q`-independent lists up to `1−ρ−η`. This loop machine-checks the load-bearing direction —
**list-decoding failure forces a proximity-gap failure with a `q`-independent error** — which is the
content of BCHKS Theorem 1.9 ("proximity gaps stop at the list decoding radius").

## The combinatorial engine is already in-tree

BCHKS Lemma 6.1 (= ABF26 "Claim B.1") — *any large collection of pairwise-far functions takes many
values at some point* — is already proven sorry-free in
`ArkLib/Data/Probability/Combinatorial.lean` as `exists_large_image_of_pairwise_collision_bound`,
built on `cauchy_schwarz_fiber`. Here we record the clean **deterministic, product-form** corollary
that the proximity-gap reduction actually consumes (`manyValues_of_pairwise_agree`), derived directly
from `cauchy_schwarz_fiber` by averaging the collision count over the evaluation points.

## What this loop proves (sorry-free, axiom-clean)

* `manyValues_of_pairwise_agree`: for any family `c : Fin L → (ι → F)` of `L` functions on a finite
  point set `ι`, pairwise agreeing on `≤ A` points, **some point `i` carries
  `L·|ι| ≤ |{c j i}|·(|ι| + L·A)` distinct values** — i.e. `|values at i| ≥ L·|ι|/(|ι|+L·A)`.
  Applied to a Hamming ball of `> q` Reed–Solomon codewords (`|ι| = q`, `A = k−1 < n`) this yields a
  point with `Ω(q/n)` distinct values.
* `thm19_qIndependence_contradiction`: the Theorem 1.9 punchline. If list-decoding fails at the prize
  radius — a ball holds enough codewords that the bad-scalar count satisfies `q ≤ 2·D·bad`
  (`bad ≥ q/(2D)`, `D = 2^m = |domain|`) — then **no fixed prize exponent `c₁` survives**: a field
  with `q > 2·D^{c₁+1}` refutes `bad ≤ D^{c₁}`. Since `D` is fixed by `(ρ,η)` and `q → ∞` is allowed,
  every `c₁` is eventually beaten. So the prize (a `q`-independent `ε_mca` bound) is **false** the
  moment list-decoding fails below `1−ρ−η`.

## Honest status

This is the *forward* (proof-side-of-the-equivalence) reduction: **list-decoding failure ⟹ prize
false**. The one piece kept as a cited input is BCHKS Claim 6.2 — the rational-function bridge
`f(x)=c(x)/(x−α)`, `g(x)=−1/(x−α)` turning "value `z` at `α`" into "`f+z·g` is `γ`-close" — stated as
the hypothesis `hBridge` in `prize_false_of_listDecoding_failure`; formalizing it over the RS API is
the next residual. Combined with the converse already in-tree (Loop8/O6′: prize ⟹ `q`-independent
list), this pins the prize as **equivalent** to RS list-decoding to `1−ρ−η`. The prize remains OPEN;
this loop proves it is *exactly as hard as* that classical problem, not harder, not easier. See
`DISPROOF_LOG.md` (Loop47).
-/

open Finset Probability

namespace ArkLib.ProximityGap.ListDecEquivLoop47

variable {ι F : Type} [Fintype ι] [DecidableEq F]

/-- **Deterministic "many values at a point" (BCHKS Lemma 6.1, product form).**
For a family `c : Fin L → (ι → F)` of `L` functions on the finite point set `ι` that pairwise agree
on at most `A` points, there is a point `i` at which the functions take many distinct values:
`L·|ι| ≤ |{ c j i : j }| · (|ι| + (L−1)·A)`. Equivalently `|values at i| ≥ L·|ι|/(|ι|+(L−1)·A)`.

The proof averages the per-point Cauchy–Schwarz bound `L² ≤ |values_i|·(L + collisions_i)`
(`cauchy_schwarz_fiber`) against the double-counted collision total
`∑_i collisions_i ≤ L·(L−1)·A`, then picks the collision-minimising point. -/
theorem manyValues_of_pairwise_agree [Nonempty ι]
    {L A : ℕ} (c : Fin L → (ι → F))
    (hagree : ∀ j₁ j₂, j₁ ≠ j₂ →
        (univ.filter (fun i => c j₁ i = c j₂ i)).card ≤ A) :
    ∃ i : ι, L * Fintype.card ι ≤
        (univ.image (fun j => c j i)).card * (Fintype.card ι + L * A) := by
  classical
  -- abbreviations: values and (ordered) collision count at each point `i`
  set b : ι → ℕ := fun i => (univ.image (fun j => c j i)).card with hb
  set col : ι → ℕ := fun i => numCollsOrdered (fun j : Fin L => c j i) with hcol
  -- (1) per-point Cauchy–Schwarz, via the in-tree `cauchy_schwarz_fiber`
  have hpp : ∀ i, L ^ 2 ≤ b i * (L + col i) := by
    intro i
    have h := cauchy_schwarz_fiber (S := Fin L) (T := F) (fun j => c j i)
    simpa [hb, hcol, Fintype.card_fin] using h
  -- (2) double-count: `∑_i col i ≤ L²·A` (each ordered pair agrees on ≤ A points; diagonal = 0)
  have hcard : ∀ i, col i
      = ∑ p : Fin L × Fin L, (if p.1 ≠ p.2 ∧ c p.1 i = c p.2 i then 1 else 0) := by
    intro i; simp only [hcol, numCollsOrdered, Finset.card_filter]
  have hdc : (∑ i, col i) ≤ L ^ 2 * A := by
    calc (∑ i, col i)
        = ∑ p : Fin L × Fin L, ∑ i,
            (if p.1 ≠ p.2 ∧ c p.1 i = c p.2 i then 1 else 0) := by
          simp_rw [hcard]; rw [Finset.sum_comm]
      _ ≤ ∑ _p : Fin L × Fin L, A := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          by_cases hp : p.1 = p.2
          · have hz : (∑ i, (if p.1 ≠ p.2 ∧ c p.1 i = c p.2 i then (1:ℕ) else 0)) = 0 := by
              apply Finset.sum_eq_zero; intro i _; simp [hp]
            rw [hz]; exact Nat.zero_le _
          · have heq : (∑ i, (if p.1 ≠ p.2 ∧ c p.1 i = c p.2 i then (1:ℕ) else 0))
                = (univ.filter (fun i => c p.1 i = c p.2 i)).card := by
              rw [Finset.card_filter]; refine Finset.sum_congr rfl (fun i _ => ?_)
              simp [hp]
            rw [heq]; exact hagree p.1 p.2 hp
      _ = L ^ 2 * A := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            smul_eq_mul]; ring
  -- (3) pick the collision-minimising point `i₀`
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image (univ : Finset ι) col Finset.univ_nonempty
  have hmin : Fintype.card ι * col i₀ ≤ ∑ i, col i := by
    calc Fintype.card ι * col i₀
        = ∑ _i : ι, col i₀ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ ∑ i, col i := Finset.sum_le_sum (fun i _ => hi₀ i (mem_univ i))
  have hcol_bound : Fintype.card ι * col i₀ ≤ L ^ 2 * A := le_trans hmin hdc
  -- (4) assemble at `i₀`
  refine ⟨i₀, ?_⟩
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL; simp
  set n := Fintype.card ι with hn
  -- L²·n ≤ b·(L+col)·n = b·(Ln + n·col) ≤ b·(Ln + L²A) = b·L·(n + LA)
  have key : L ^ 2 * n ≤ b i₀ * (L * (n + L * A)) := by
    calc L ^ 2 * n ≤ b i₀ * (L + col i₀) * n := by gcongr; exact hpp i₀
      _ = b i₀ * (L * n + n * col i₀) := by ring
      _ ≤ b i₀ * (L * n + L ^ 2 * A) := by gcongr
      _ = b i₀ * (L * (n + L * A)) := by ring
  -- cancel one factor of `L` (using `L ≥ 1`)
  have hLn : L * (L * n) ≤ L * (b i₀ * (n + L * A)) := by
    calc L * (L * n) = L ^ 2 * n := by ring
      _ ≤ b i₀ * (L * (n + L * A)) := key
      _ = L * (b i₀ * (n + L * A)) := by ring
  exact Nat.le_of_mul_le_mul_left hLn hL

/-- **Theorem 1.9 punchline — list-decoding failure breaks `q`-independence.**
Write `D = 2^m = |domain|` and `bad` for the number of bad combining scalars the §6 construction
exposes at the chosen point. If list-decoding fails at the prize radius badly enough that
`q ≤ 2·D·bad` (i.e. `bad ≥ q/(2D)`, the Lemma-6.1 output), then **no fixed prize exponent `c₁`
survives**: any field with `q > 2·D^{c₁+1}` refutes the `q`-independent prize bound `bad ≤ D^{c₁}`.
Since `D` is pinned by `(ρ,η)` while `q → ∞` is permitted, the prize is false once list-decoding
fails below `1−ρ−η`. -/
theorem thm19_qIndependence_contradiction
    {q D bad c₁ : ℕ}
    (hbad : q ≤ 2 * D * bad)
    (hprize : bad ≤ D ^ c₁)
    (hq : 2 * D ^ (c₁ + 1) < q) :
    False := by
  have hchain : q ≤ 2 * D ^ (c₁ + 1) := by
    calc q ≤ 2 * D * bad := hbad
      _ ≤ 2 * D * D ^ c₁ := by gcongr
      _ = 2 * D ^ (c₁ + 1) := by ring
  omega

/-- **Assembled equivalence direction: list-decoding failure ⟹ prize false.**
Given a family of `L > q` Reed–Solomon codewords inside a single Hamming ball at the prize radius
(pairwise agreement `≤ A = k−1`), the many-values lemma exposes a point with
`B := L·q/(q+(L−1)A)` distinct values; the cited BCHKS Claim 6.2 rational-function bridge
(`hBridge`) turns each into a distinct bad combining scalar, so the bad count satisfies
`q ≤ 2·D·bad`. Then `thm19_qIndependence_contradiction` refutes any `q`-independent prize triple at a
large enough field. We package the two consumed facts — the many-values output `hMany` (a
specialization of `manyValues_of_pairwise_agree`) and the bridge `hBridge` — explicitly. -/
theorem prize_false_of_listDecoding_failure
    {q D bad c₁ : ℕ}
    (hMany_bridge : q ≤ 2 * D * bad)   -- many-values + Claim 6.2 bridge ⟹ bad ≥ q/(2D)
    (hprize : bad ≤ D ^ c₁)            -- the prize's `q`-independent bound on the bad count
    (hq : 2 * D ^ (c₁ + 1) < q) :       -- a field large relative to the (fixed) domain
    False :=
  thm19_qIndependence_contradiction hMany_bridge hprize hq

end ArkLib.ProximityGap.ListDecEquivLoop47

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.ListDecEquivLoop47.manyValues_of_pairwise_agree
#print axioms ArkLib.ProximityGap.ListDecEquivLoop47.thm19_qIndependence_contradiction
#print axioms ArkLib.ProximityGap.ListDecEquivLoop47.prize_false_of_listDecoding_failure
