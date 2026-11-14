/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Extensions.Data.Probability.Combinatorial
import Mathlib.Tactic

/-!
# Loop 47 (EQUIVALENCE) — "many values at a random point" ⟹ proximity gaps stop at the
# list-decoding radius (BCHKS §6, Lemma 6.1 / Theorem 1.9), the prize ⟺ list-decoding direction.

The grind's (unformalized) verdict (Loop45/46) is that the #232 prize is *equivalent* to RS
list-decoding with `q`-independent lists up to `1−ρ−η`. BCHKS Theorem 1.9 ("proximity gaps stop at
the list decoding radius") asserts the direction **list-decoding failure forces a proximity-gap
failure**. This loop does **not** machine-check that direction: it machine-checks (a) the generic
many-values lemma and (b) the final *natural-number arithmetic* step of the argument, with the
source-to-count translation (received word, RS code, list, bad-event definition, and the
Claim 6.2 bridge producing the bad count) left as an explicit, unproved hypothesis.

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
  Applied to a Hamming ball of `> q` Reed–Solomon codewords (`|ι| = q`, `A = k−1 < n`) this would
  yield a point with `Ω(q/n)` distinct values (that application is not formalized here).
* `thm19_qIndependence_contradiction`: a pure natural-number lemma — for `q, D, bad, c₁ : ℕ`,
  `q ≤ 2·D·bad`, `bad ≤ D^{c₁}` and `q > 2·D^{c₁+1}` are jointly contradictory. It is the arithmetic
  punchline of Theorem 1.9 *once* a list-decoding failure has been translated into the count
  inequality `q ≤ 2·D·bad` (`D = 2^m = |domain|`); that translation is not proved here.
* `prize_false_of_listDecoding_failure`: the same arithmetic lemma restated with the count
  inequality named `hMany_bridge`; it contains no received word, RS code, list, or bad-event
  definition.

## Honest status

The **unproved source-to-count obligation** is: from an actual list-decoding failure (a Hamming ball
at the prize radius containing `> q` RS codewords), construct a fixed received pair `(f, g)` and a
bad-event count `bad` (bad combining scalars for an MCA/proximity-gap event) satisfying
`q ≤ 2·D·bad`. This requires applying `manyValues_of_pairwise_agree` to the ball and BCHKS Claim 6.2
— the rational-function bridge `f(x)=c(x)/(x−α)`, `g(x)=−1/(x−α)` turning "value `z` at `α`" into
"`f+z·g` is `γ`-close", together with the far/no-joint property. In this file the whole obligation
is **assumed** as the hypothesis `hMany_bridge` of `prize_false_of_listDecoding_failure`; there is
no separate bridge hypothesis `hBridge` and no definition from which `bad` is computed. (See
`BridgeClaim62Loop48.lean` for a partial bridge; it too still assumes the bad-set geometry.)

Consequently this file does **not** machine-check "list-decoding failure ⟹ prize false", and does
not establish the claimed equivalence of the prize with RS list-decoding to `1−ρ−η` (the converse
direction, Loop8/O6′, is likewise a separate claim). This is not an assertion that the cited
paper's reduction is false — only that its translation is not formalized here. The prize remains
OPEN. See `docs/research/proximity-gap/DISPROOF_LOG.md` (Loop47).
-/

open Finset Probability

namespace ArkLib.ProximityGap.ListDecEquivLoop47

variable {ι F : Type} [Fintype ι] [DecidableEq F]

/-- **Deterministic "many values at a point" (BCHKS Lemma 6.1, product form).**
For a family `c : Fin L → (ι → F)` of `L` functions on the finite point set `ι` that pairwise agree
on at most `A` points, there is a point `i` at which the functions take many distinct values:
`L·|ι| ≤ |{ c j i : j }| · (|ι| + L·A)`. Equivalently `|values at i| ≥ L·|ι|/(|ι|+L·A)`.
(The proof's collision bound is `∑ collisions ≤ L²·A`, which gives the `L·A` form stated.)

The proof averages the per-point Cauchy–Schwarz bound `L² ≤ |values_i|·(L + collisions_i)`
(`cauchy_schwarz_fiber`) against the double-counted collision total
`∑_i collisions_i ≤ L²·A` (crudely bounding the `L·(L−1)` off-diagonal pairs by `L²`), then picks
the collision-minimising point. -/
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

/-- **Theorem 1.9 arithmetic punchline (natural numbers only).**
For natural numbers `q, D, bad, c₁`: `q ≤ 2·D·bad`, `bad ≤ D^{c₁}` and `2·D^{c₁+1} < q` are jointly
contradictory. Intended reading: `D = 2^m = |domain|` and `bad` the number of bad combining scalars
that the §6 construction would expose; *if* a list-decoding failure at the prize radius were
translated into `q ≤ 2·D·bad` (the unproved source-to-count obligation described in the module
docstring), then no fixed prize exponent `c₁` would survive at fields with `q > 2·D^{c₁+1}`. This
lemma proves only the arithmetic; it does not prove that the translation holds. -/
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

/-- **Arithmetic step with the source-to-count obligation assumed (not a reduction).**
This is `thm19_qIndependence_contradiction` restated verbatim, with the count inequality named
`hMany_bridge`. The intended (unformalized) argument: given `L > q` Reed–Solomon codewords inside
a single Hamming ball at the prize radius (pairwise agreement `≤ A = k−1`), the many-values lemma
would expose a point with about `L·q/(q+L·A)` distinct values, and the BCHKS Claim 6.2
rational-function bridge would turn each into a distinct bad combining scalar, giving
`q ≤ 2·D·bad`. **None of that is formalized here**: there is no received word, RS code, list or
bad-event definition, and no separate bridge hypothesis — the entire translation is the single
assumed hypothesis `hMany_bridge`. So this theorem is not a machine-checked
"list-decoding failure ⟹ prize false" reduction; it is the final arithmetic step only. -/
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
