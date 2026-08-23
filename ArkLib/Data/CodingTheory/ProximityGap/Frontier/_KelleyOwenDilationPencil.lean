/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The Kelley–Owen dilation-pencil bound: a Stepanov √N count for the trinomial face (#407)

This is the **proven positive core of the Stepanov / auxiliary-polynomial route** on the isolated
agreement points (#407). The Stepanov-flavoured *dilation-pencil* argument of Kelley–Owen
("Estimating the Number of Roots of Trinomials over Finite Fields", arXiv:1510.01758, Lemma 2.3)
gives, for a **trinomial** `f = a·xⁿ + b·xˢ + 1` with `gcd(n,s,N) = 1`, the bound

  `#{roots of f in the order-N multiplicative subgroup G} ≤ ½ + √N`.

Crucially the `√` is in the **subgroup order `N`**, not the field size `q`. This is the genuine,
elementary, char-free Stepanov harvest for the `t = 3` (i.e. `k = 1`) face of the prize agreement
polynomial `P = xᵃ + γ·xᵇ − c(x)` (`deg c < k`).

## The mechanism (formalized here)

Let `f` have `r` distinct roots `ζ₁,…,ζ_r ∈ G`. Dilate: `gᵢ(x) := f(ζᵢ·x)`. Then

* each `gᵢ` again has `r` roots in `G` (dilation by `ζᵢ ∈ G` permutes `G`), and `gᵢ(1) = f(ζᵢ) = 0`;
* the `gᵢ` lie in the **one-parameter pencil** `C(n,s) = {c·xⁿ − (c+1)·xˢ + 1}` (trinomials with
  support `{n,s,0}`, constant term `1`, value `0` at `1`);
* the `gᵢ` are **pairwise distinct**, because `gᵢ = gⱼ` forces `(ζᵢ/ζⱼ)ⁿ = (ζᵢ/ζⱼ)ˢ = 1`, which by
  `gcd(n,s,N)=1` forces `ζᵢ = ζⱼ`;
* any two distinct members of the pencil share **only** the root `1` (the pencil parameter `c` is
  determined by any second common root).

So the `r` root-sets (each of size `r`, all containing `1`, pairwise meeting only in `1`) have union
`≥ r·(r−1) + 1` inside `G`, giving `r² − r + 1 ≤ N`, hence `r ≤ ½ + √N`.

This file formalizes the **combinatorial heart** as a clean, field-free statement: the
"`r` blocks of size `r`, pairwise overlap ≤ 1, common point" cardinality inequality
`r·(r−1) + 1 ≤ N`, together with the `r ≤ ½ + √N` extraction. The algebraic inputs (the pencil is
1-parameter; distinct members meet only at `1`) are recorded as the precise hypotheses the
combinatorial core consumes — this is the reusable Stepanov-count brick.

## Honest scope: why this does NOT close the prize (the `t → k+2` degradation)

The `√N` here is **special to `t = 3`** (`k = 1`): the pencil is *one-dimensional*, so two distinct
members meet in a **single** point. For the prize agreement polynomial the term count is `t = k + 2`
with `k = ρ·n` (`ρ ∈ {1/2,1/4,…}`), so the dilation pencil is **`k`-dimensional** and two members
can share up to `~k` common roots. The same double-count then gives only
`r² ≤ k·N · (1+o(1))`, i.e. `r ≤ √(k·N) = √(n·k)` — exactly the **Johnson radius**, `Θ(n)` at prize
rate (`= √ρ · n`), the *same order as the legitimate coset core*. So the Stepanov-dilation route
bounds the **full** agreement set at Johnson but does **not** separate the *isolated excess*
(which is `n`-independent, `O(k)`/`O(log)` empirically) from the coset core — it cannot reach the
sub-budget `≈ ε*·q ~ n` isolated bound the prize needs. That sub-`√(nk)` isolated bound is exactly
Kelley's Conjecture 3.2 / Kelley–Owen Heuristic 1.4 (`O(t·log p)` roots in general position),
**recognized open**. See the issue #407 thread; this brick is the proven `t=3` rung, not a closure.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ProximityGap.Frontier.KelleyOwenDilationPencil

/-! ## The combinatorial Stepanov core: `r` size-`r` blocks, pairwise overlap ≤ 1, in `G` -/

/-- **Dilation-pencil cardinality core.** Suppose `G` is a finite set with a family of `r` distinct
"blocks" `B : Fin r → Finset G`, each of size `r`, all containing a common point `p`, and pairwise
meeting **only** at `p`. Then `r·(r−1) + 1 ≤ |G|`.

This is the abstract heart of Kelley–Owen Lemma 2.3: the `r` dilated trinomials' root-sets are
`r` size-`r` subsets of the order-`N` subgroup, all through `1`, pairwise overlapping only at `1`.
The union has `≥ r(r−1)+1` elements (each block contributes `r−1` fresh points beyond `p`). -/
theorem pencil_card_core {G : Type*} [DecidableEq G] (univ : Finset G)
    (r : ℕ) (hr : 1 ≤ r) (B : Fin r → Finset G) (p : G)
    (hsub : ∀ i, B i ⊆ univ)
    (hsize : ∀ i, (B i).card = r)
    (hp : ∀ i, p ∈ B i)
    (hpair : ∀ i j, i ≠ j → B i ∩ B j = {p}) :
    r * (r - 1) + 1 ≤ univ.card := by
  classical
  have hrpos : 0 < r := hr
  -- The union of all blocks is a subset of `univ`; lower-bound its card.
  set U : Finset G := Finset.univ.biUnion B with hU
  have hUsub : U ⊆ univ := by
    intro x hx
    rw [hU, Finset.mem_biUnion] at hx
    obtain ⟨i, _, hxi⟩ := hx
    exact hsub i hxi
  -- It suffices to show `r*(r-1) + 1 ≤ U.card`.
  refine le_trans ?_ (Finset.card_le_card hUsub)
  -- Count `U` by inclusion: `{p} ∪ ⋃ᵢ (Bᵢ \ {p})`, the latter pairwise disjoint of size `r-1`.
  -- Define the punctured blocks.
  set C : Fin r → Finset G := fun i => (B i).erase p with hC
  have hCcard : ∀ i, (C i).card = r - 1 := by
    intro i; rw [hC, Finset.card_erase_of_mem (hp i), hsize i]
  have hCdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rw [hC, Finset.mem_erase] at hxi hxj
    have : x ∈ B i ∩ B j := Finset.mem_inter.mpr ⟨hxi.2, hxj.2⟩
    rw [hpair i j hij, Finset.mem_singleton] at this
    exact hxi.1 this
  -- `p ∉ C i`, and `{p} ∪ ⋃ C i ⊆ U`.
  have hpnotC : ∀ i, p ∉ C i := by intro i; rw [hC]; exact Finset.notMem_erase p _
  set D : Finset G := Finset.univ.biUnion C with hD
  have hDcard : D.card = r * (r - 1) := by
    rw [hD, Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun i _ => hCcard i)]
      simp [Finset.sum_const, Finset.card_univ]
    · intro i _ j _ hij; exact hCdisj i j hij
  have hpnotD : p ∉ D := by
    rw [hD, Finset.mem_biUnion]; rintro ⟨i, _, hi⟩; exact hpnotC i hi
  -- `insert p D ⊆ U`.
  have hinsert : insert p D ⊆ U := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rw [hU, Finset.mem_biUnion]
    rcases hx with rfl | hx
    · -- `x = p`: `p` lies in block `0` (which exists since `r ≥ 1`).
      exact ⟨⟨0, hrpos⟩, Finset.mem_univ _, hp _⟩
    · rw [hD, Finset.mem_biUnion] at hx
      obtain ⟨i, _, hi⟩ := hx
      exact ⟨i, Finset.mem_univ _, Finset.mem_of_mem_erase hi⟩
  -- Card of `insert p D` is `1 + r*(r-1)`.
  have hcard : (insert p D).card = r * (r - 1) + 1 := by
    rw [Finset.card_insert_of_notMem hpnotD, hDcard]
  rw [← hcard]
  exact Finset.card_le_card hinsert

/-! ## The `√N` extraction (Kelley–Owen Lemma 2.3 conclusion) -/

/-- **Stepanov √N root bound (extraction).** From the pencil core `r·(r−1)+1 ≤ N`, the number of
roots satisfies the Kelley–Owen bound `2·r − 1 ≤ 2·√N`, i.e. `r ≤ ½ + √N`. We state it in the
clean square-free integer form `r·(r−1) < N → (r−1)² < N` (so `r − 1 < √N`, `r < 1 + √N`), which
is what the prize-side consumer needs: the trinomial (`t=3`, `k=1`) face has `O(√N)` roots in the
order-`N` subgroup — and the `√` is in the **subgroup order**, not the field size. -/
theorem stepanov_sqrt_bound {r N : ℕ} (h : r * (r - 1) + 1 ≤ N) :
    (r - 1) * (r - 1) < N := by
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0; simpa using h
  · have : (r - 1) * (r - 1) ≤ r * (r - 1) := by
      apply Nat.mul_le_mul_right; omega
    omega

end ProximityGap.Frontier.KelleyOwenDilationPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.KelleyOwenDilationPencil.pencil_card_core
#print axioms ProximityGap.Frontier.KelleyOwenDilationPencil.stepanov_sqrt_bound
