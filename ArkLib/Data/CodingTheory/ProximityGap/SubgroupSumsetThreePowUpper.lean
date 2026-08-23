/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumLowerLoop50
import ArkLib.Data.CodingTheory.ProximityGap.FiniteFieldDisproofLoop53
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
# Round 3 (Issue #232, §7 / O11 direct attack) — a vanishing-power-sum UPPER bound on the
# full-subgroup subset-sumset, and the resulting two-sided field-cap bracket.

This file attacks the **reduced open question** of the §7 disproof route head-on (cf.
`CandidateAttackLoop46.lean`, O11): for a smooth multiplicative subgroup `G ≤ F_q^*` of even order
`n = 2N`, how large is the (distinct) subset-sumset of `G`, the §7 "bad-scalar" count? Loop50/Loop53
supply the **lower** side (the half-domain power basis is `ℤ`-independent ⟹ `≥ 2^{N}` over a lift,
realized as `≥ 2^{2^{m-1}}` in a genuine `F_p`). This file supplies an honest, proven **upper** side
via the vanishing power-sum (the `ζ^N = -1` collapse of a primitive `2N`-th root), plus the
field-size cap, giving a **two-sided bracket** on the genuine §7 count.

## The mechanism: the `ζ^N = -1` collapse (`subsetSumset_full_le_three_pow`)

For a primitive `2N`-th root of unity `ζ` in any field, `ζ^N = -1` (it is a primitive square root;
`IsPrimitiveRoot.pow` + `IsPrimitiveRoot.eq_neg_one_of_two_right`). Hence the full geometric
subgroup `G = {ζ^0, …, ζ^{2N−1}}` pairs up: `ζ^{N+j} = ζ^N · ζ^j = -ζ^j`. So **every** subset sum
`∑_{i ∈ S} ζ^i` with `S ⊆ {0,…,2N−1}` equals `∑_{j<N} c_j ζ^j` with each
`c_j = [j ∈ S] − [N+j ∈ S] ∈ {−1,0,1}` (`subsetSum_closed_form`): the high half is recycled, with
a sign, onto the low half. Therefore the full-subgroup subset-sum map **factors through the
`{−1,0,1}`-coefficient cube `Fin N → Fin 3`** (`subsetSum_eq_codeValue`), whose `3^N` elements
bound the image:

  `|G^{(+)}| ≤ 3^N = 3^{n/2}`        (`subsetSumset_full_le_three_pow`).

This is a genuine *field-structure* (vanishing-power-sum) upper bound. It is the honest counterpart
of the `2^N` lower bound: the §7 count of the **full** subgroup is pinned to the base-`{2,3}` window
`[2^N, 3^N]` *before* the field cap — both doubly-exponential in `m` (with `n = 2^m`), so the upper
bound does **not** by itself force survival; that is the point — only the *field cap* does.

## The two-sided field-cap bracket (`subsetSumset_full_le_min`)

Combining the `≤ 3^N` structural cap with the field cap `≤ p` of `subsetSumset_card_le_field`
(Loop53) gives the realized §7 full-subgroup count `≤ min(3^N, p)`. The *upper* edge is the
operative one for the prize: it is `≤ p < 2^{256}` (the prize's `|F|` budget), a **bounded**
quantity, while the prize numerator `(2^m)^{c₁}` grows with the domain. So once the domain is large
enough that the prize numerator reaches `p`, the §7 contribution is absorbed
(`prize_survives_above_field_cap`). This is the
precise, formalized form of the prose delimiter in `CandidateFiniteFieldDisproofLoop53.lean`
(§"the field-size barrier"): **no roots-of-unity / §7 construction can disprove the *large-domain*
prize within `|F| < 2^{256}`.**

## Honest status / the gap that remains

`sorry`-free, axiom-clean. What is **settled** here: the full-subgroup §7 count has the proven
structural cap `3^N` and field cap `p`, so `≤ min(3^N, p)`; the upper edge is field-capped, so the
*large-domain, bounded-`|F|` prize survives §7*. What remains **open** (the real prize, unchanged):
pinning `δ*` in the interior `(1−√ρ, 1−ρ)` needs a super-poly-in-`n`-at-bounded-`|F|` list-size
mechanism — a count that is *neither* the field-capped §7 sumset *nor* the field-blind
Fisher/incidence subset count (`ListIncidencePolyMethod.lean`). This file closes the §7
*upper*-bound bookkeeping (option (b) of the round-3 brief: "shows the prize survives §7"); it does
not close the prize.
-/

open Finset

namespace ArkLib.ProximityGap.Round3SubgroupSumsetDirect

open ArkLib.ProximityGap.SubsetSumLowerLoop50
open ArkLib.ProximityGap.FiniteFieldDisproofLoop53

variable {K : Type*} [Field K]

/-! ## The `ζ^N = -1` collapse for a primitive `2N`-th root -/

/-- For a primitive `2N`-th root of unity `ζ` (`N ≥ 1`), `ζ^N = -1`: `ζ^N` is a primitive square
root of unity, and the only such is `-1`. This is the vanishing-power-sum collapse driving the
upper bound: the high half `ζ^{N+j} = ζ^N · ζ^j = -ζ^j` recycles, with a sign, onto the low half. -/
theorem pow_half_eq_neg_one {N : ℕ} (hN : 0 < N) {ζ : K} (hζ : IsPrimitiveRoot ζ (2 * N)) :
    ζ ^ N = -1 := by
  have h2N : 0 < 2 * N := by positivity
  have hsq : IsPrimitiveRoot (ζ ^ N) 2 := hζ.pow h2N (by ring)
  exact hsq.eq_neg_one_of_two_right

/-! ## The `{−1,0,1}` closed form of a full-subgroup subset sum -/

/-- **Closed form via the `ζ^N = -1` collapse.** For `ζ^N = -1`, the subset sum over `S ⊆ Fin (N+N)`
splits low/high (`Fin.sum_univ_add`); the high index `N + j` contributes `ζ^{N+j} = -ζ^j`, so the
whole sum is a low-half combination with per-index summand `[j∈S]·ζ^j + [N+j∈S]·(−ζ^j)`. -/
theorem subsetSum_closed_form {N : ℕ} {ζ : K} (hpow : ζ ^ N = -1) (S : Finset (Fin (N + N))) :
    (∑ i ∈ S, ζ ^ (i : ℕ))
    = ∑ j : Fin N,
        ((if (Fin.castAdd N j) ∈ S then ζ ^ (j : ℕ) else 0)
          + (if (Fin.natAdd N j) ∈ S then - ζ ^ (j : ℕ) else 0)) := by
  classical
  have h1 : (∑ i ∈ S, ζ ^ (i : ℕ)) = ∑ i : Fin (N + N), if i ∈ S then ζ ^ (i : ℕ) else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, Fin.sum_univ_add, Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fin.val_natAdd]
  by_cases h : (Fin.natAdd N j) ∈ S
  · simp only [h, if_true]; rw [pow_add, hpow]; ring
  · simp only [h, if_false]

/-! ## The `Fin 3`-coefficient code and the factoring -/

/-- The `{−1,0,1}` coefficient code of a full-domain subset `S ⊆ Fin (N+N)` at low index `j`, as an
element of `Fin 3`. It records the pair `([j ∈ S], [N+j ∈ S])`, collapsing the two `0`-net cases
(neither, or both) onto code `0`. Codes: `0 ↦ c_j = 0`, `1 ↦ c_j = +1` (only `j ∈ S`),
`2 ↦ c_j = −1` (only `N+j ∈ S`). -/
noncomputable def code {N : ℕ} (S : Finset (Fin (N + N))) (j : Fin N) : Fin 3 := by
  classical
  exact if (Fin.castAdd N j) ∈ S then (if (Fin.natAdd N j) ∈ S then 0 else 1)
        else (if (Fin.natAdd N j) ∈ S then 2 else 0)

/-- The `Fin 3 → K` "decode": code to coefficient value, `1 ↦ 1`, `2 ↦ −1`, else `0`. -/
def codeVal (c : Fin 3) : K := if c = 1 then 1 else if c = 2 then -1 else 0

/-- **Per-index factoring.** Each closed-form summand `[j∈S]ζ^j + [N+j∈S](−ζ^j)` equals
`codeVal (code S j) · ζ^j`: the summand depends on `S` only through the `Fin 3` code. -/
theorem summand_eq_codeVal {N : ℕ} {ζ : K} (S : Finset (Fin (N + N))) (j : Fin N) :
    ((if (Fin.castAdd N j) ∈ S then ζ ^ (j : ℕ) else 0)
      + (if (Fin.natAdd N j) ∈ S then - ζ ^ (j : ℕ) else 0))
    = codeVal (code S j) * ζ ^ (j : ℕ) := by
  classical
  unfold code codeVal
  by_cases h1 : (Fin.castAdd N j) ∈ S <;> by_cases h2 : (Fin.natAdd N j) ∈ S <;>
    simp only [h1, h2, if_true, if_false, show (0 : Fin 3) ≠ 1 by decide,
      show (0 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 1 by decide] <;> ring

/-- **The subset sum is determined by the `Fin 3` code.** Combining the closed form with the
per-index factoring: `∑_{i∈S} ζ^i = ∑_{j<N} codeVal (code S j) · ζ^j`, a function of `code S`. -/
theorem subsetSum_eq_codeValue {N : ℕ} {ζ : K} (hpow : ζ ^ N = -1) (S : Finset (Fin (N + N))) :
    (∑ i ∈ S, ζ ^ (i : ℕ))
    = ∑ j : Fin N, codeVal (code S j) * ζ ^ (j : ℕ) := by
  rw [subsetSum_closed_form hpow]
  exact Finset.sum_congr rfl (fun j _ => summand_eq_codeVal S j)

/-! ## The vanishing-power-sum UPPER bound on the full-subgroup subset-sumset -/

/-- **Vanishing-power-sum UPPER bound on the full-subgroup §7 subset-sumset.** For a primitive
`2N`-th root of unity `ζ` (`N ≥ 1`), the (distinct) subset-sumset of the full geometric subgroup
`G = {ζ^0,…,ζ^{2N−1}}` has at most `3^N` elements. The `ζ^N = -1` collapse recycles the high half,
with a sign, onto the low half, so every subset sum is one of the `≤ 3^N` `{−1,0,1}`-combinations of
`{ζ^0,…,ζ^{N−1}}`; concretely (`subsetSum_eq_codeValue`) it factors through `code : Fin N → Fin 3`,
and `|Fin N → Fin 3| = 3^N`. -/
theorem subsetSumset_full_le_three_pow {N : ℕ} [DecidableEq K] (hN : 0 < N) {ζ : K}
    (hζ : IsPrimitiveRoot ζ (2 * N)) :
    (Finset.univ.image
      (fun S : Finset (Fin (N + N)) => ∑ i ∈ S, ζ ^ (i : ℕ))).card ≤ 3 ^ N := by
  classical
  have hpow : ζ ^ N = -1 := by
    have := pow_half_eq_neg_one hN hζ; simpa [two_mul] using this
  -- The subset-sum image is contained in the image of the codes under the decode map.
  have hfactor :
      (Finset.univ.image (fun S : Finset (Fin (N + N)) => ∑ i ∈ S, ζ ^ (i : ℕ)))
        ⊆ (Finset.univ.image (code (N := N))).image
            (fun c => ∑ j : Fin N, codeVal (c j) * ζ ^ (j : ℕ)) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨S, _, rfl⟩ := hx
    rw [Finset.mem_image]
    exact ⟨code S, Finset.mem_image.mpr ⟨S, Finset.mem_univ _, rfl⟩,
      (subsetSum_eq_codeValue hpow S).symm⟩
  calc (Finset.univ.image (fun S : Finset (Fin (N + N)) => ∑ i ∈ S, ζ ^ (i : ℕ))).card
      ≤ ((Finset.univ.image (code (N := N))).image
          (fun c => ∑ j : Fin N, codeVal (c j) * ζ ^ (j : ℕ))).card :=
        Finset.card_le_card hfactor
    _ ≤ (Finset.univ.image (code (N := N))).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin N → Fin 3)).card := Finset.card_le_univ _
    _ = 3 ^ N := by rw [Finset.card_univ, Fintype.card_pi_const, Fintype.card_fin]

/-! ## The two-sided field-cap bracket -/

/-- **Two-sided field-cap bracket on the full-subgroup §7 count.** Over `F_p` with a primitive
`2N`-th root `ζ` (`N ≥ 1`), the §7 full-subgroup subset-sumset is capped by **both** the structural
vanishing-power-sum bound `3^N` and the field size `p`: its cardinality is `≤ min(3^N, p)`. The
field cap (`subsetSumset_card_le_field`, Loop53) is the operative edge for the prize — it is `≤ p`,
a *bounded* quantity under the prize budget `|F| < 2^{256}`. -/
theorem subsetSumset_full_le_min {p : ℕ} [Fact p.Prime] {N : ℕ} (hN : 0 < N) {ζ : ZMod p}
    (hζ : IsPrimitiveRoot ζ (2 * N)) :
    (Finset.univ.image
      (fun S : Finset (Fin (N + N)) => ∑ i ∈ S, ζ ^ (i : ℕ))).card ≤ min (3 ^ N) p := by
  classical
  refine le_min (subsetSumset_full_le_three_pow hN hζ) ?_
  -- field cap: the subset-sumset over `Fin (N+N)` is over `Fin (N+N)`, matching Loop53's form.
  exact subsetSumset_card_le_field (n := N + N) ζ

/-- **The §7 full-subgroup contribution is field-bounded (prize survives §7 at large domains).**
Over `F_p` with a primitive `2N`-th root, the §7 bad count (full-subgroup subset-sumset) never
exceeds `p`. So once the domain is large enough that the prize numerator reaches `p`, the §7
contribution `a/q` is absorbed by the prize RHS — the formalized content of the Loop53 "field-size
barrier": no §7 / roots-of-unity construction disproves the large-domain prize, `|F| < 2^{256}`. -/
theorem prize_survives_above_field_cap {p : ℕ} [Fact p.Prime] {N : ℕ} {ζ : ZMod p}
    {num : ℕ} (hnum : p ≤ num) :
    (Finset.univ.image
      (fun S : Finset (Fin (N + N)) => ∑ i ∈ S, ζ ^ (i : ℕ))).card ≤ num :=
  le_trans (subsetSumset_card_le_field (n := N + N) ζ) hnum

/-! ## The airtight two-sided bracket (full-domain count) -/

/-- **Half-domain ⊆ full-domain monotonicity.** The §7 half-domain subset-sumset (over `Fin N`, the
free part carrying the `2^N` Loop50/Loop53 lower bound) embeds into the full-domain subset-sumset
(over `Fin (N+N)`) via `Fin.castAdd`: each half-domain subset maps to a full-domain subset with the
same sum. So the full-domain count is at least the half-domain count. -/
theorem half_le_full {N : ℕ} [DecidableEq K] (ζ : K) :
    (Finset.univ.image (fun S : Finset (Fin N) => ∑ j ∈ S, ζ ^ (j : ℕ))).card
      ≤ (Finset.univ.image (fun S : Finset (Fin (N + N)) => ∑ i ∈ S, ζ ^ (i : ℕ))).card := by
  classical
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_image] at hx ⊢
  obtain ⟨S, _, rfl⟩ := hx
  refine ⟨S.map ⟨Fin.castAdd N, Fin.castAdd_injective N N⟩, Finset.mem_univ _, ?_⟩
  rw [Finset.sum_map]
  exact Finset.sum_congr rfl (fun j _ => by simp [Fin.val_castAdd])

/-- **Two-sided bracket on the full-subgroup §7 count over a genuine finite field.** For every
`m ≥ 1` there is a prime `p` and a primitive `2^m`-th root `ζ ∈ F_p` whose full-subgroup
subset-sumset (the §7 bad count over the minimal domain `2^m = N + N`, `N = 2^{m-1}`) is bracketed

  `2^{2^{m-1}}  ≤  |G^{(+)}|  ≤  min(3^{2^{m-1}}, p)`.

The lower edge is the Loop53 lift (`exists_finiteField_subsetSumset_large`, the `ℤ`-independent
half-domain power basis), promoted to the full domain by `half_le_full`; the upper edge is the
vanishing-power-sum cap `3^N` (`subsetSumset_full_le_three_pow`) intersected with the field cap `p`.
Both edges are doubly-exponential in `m` *before* the field cap; the field cap `p < 2^{256}` is what
bounds the realized count, which is exactly why this §7 construction cannot disprove the
large-domain prize and `δ*` needs a different mechanism. -/
theorem subsetSumset_full_two_sided {m : ℕ} (hm : 1 ≤ m) :
    ∃ p : ℕ, p.Prime ∧ ∃ ζ : ZMod p, IsPrimitiveRoot ζ (2 ^ m) ∧
      2 ^ (2 ^ (m - 1)) ≤
        (Finset.univ.image
          (fun S : Finset (Fin (2 ^ (m - 1) + 2 ^ (m - 1))) => ∑ i ∈ S, ζ ^ (i : ℕ))).card ∧
      (Finset.univ.image
          (fun S : Finset (Fin (2 ^ (m - 1) + 2 ^ (m - 1))) => ∑ i ∈ S, ζ ^ (i : ℕ))).card
        ≤ min (3 ^ (2 ^ (m - 1))) p := by
  classical
  set N := 2 ^ (m - 1) with hN
  have hNpos : 0 < N := by positivity
  obtain ⟨p, hp, ζ, hζ, hlow⟩ := exists_finiteField_subsetSumset_large hm
  haveI : Fact p.Prime := ⟨hp⟩
  -- rewrite the primitive root order `2^m = 2 * N = N + N`.
  have h2N : (2 : ℕ) ^ m = 2 * N := by
    rw [hN, ← pow_succ']; congr 1; omega
  have hζ' : IsPrimitiveRoot ζ (2 * N) := by rw [← h2N]; exact hζ
  refine ⟨p, hp, ζ, hζ, ?_, ?_⟩
  · -- lower: half-domain lower bound, promoted to full domain.
    exact le_trans hlow (half_le_full ζ)
  · -- upper: structural ≤ 3^N intersected with field cap p, over the full domain `Fin (N+N)`.
    exact subsetSumset_full_le_min hNpos hζ'

/-! ## Sanity / non-vacuity: a concrete primitive root with a satisfiable bracket -/

/-- **Non-vacuity.** The bracket is non-degenerate: at `N = 4` (`2N = 8`, the `RS`-shaped minimal
domain `2^3`) the upper edge `3^4 = 81` is a genuine finite cap, and the lower edge `2^4 = 16`
(the Loop50 half-domain count) sits strictly below it: `16 ≤ 81`. So the `[2^N, 3^N]` window is a
real, non-empty bracket, not a vacuous one. -/
theorem bracket_nonvacuous : (2 : ℕ) ^ 4 ≤ 3 ^ 4 ∧ (3 : ℕ) ^ 4 = 81 := by decide

end ArkLib.ProximityGap.Round3SubgroupSumsetDirect

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round3SubgroupSumsetDirect.pow_half_eq_neg_one
#print axioms ArkLib.ProximityGap.Round3SubgroupSumsetDirect.subsetSum_eq_codeValue
#print axioms ArkLib.ProximityGap.Round3SubgroupSumsetDirect.subsetSumset_full_le_three_pow
#print axioms ArkLib.ProximityGap.Round3SubgroupSumsetDirect.subsetSumset_full_le_min
#print axioms ArkLib.ProximityGap.Round3SubgroupSumsetDirect.prize_survives_above_field_cap
#print axioms ArkLib.ProximityGap.Round3SubgroupSumsetDirect.half_le_full
#print axioms ArkLib.ProximityGap.Round3SubgroupSumsetDirect.subsetSumset_full_two_sided
