/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CumulantDyadicDescent

/-!
# The EXACT dyadic split of the additive-relation count `N₀` (#407)

`CumulantDyadicDescent` delivers the **one-sided floor** `2·N₀(μ_{n/2}, r) ≤ N₀(μ_n, r)`
(the diagonal/endpoint mass of the dyadic split). This file upgrades that to the **exact
equality**: the full coset-pattern partition of the sum-zero tuples of `G = H ⊔ K` (`K = ζ·H`,
the squares/non-squares split of `μ_n`). The point of the upgrade is *honest localization* — it
turns the open obstruction (the cross terms `0 < |T| < r`) from a vague "rest" into a **named,
exactly-counted** object: the cross-resonance cells.

## The exact split (character-sum-free, unconditional)

For a sum-zero `G`-tuple `v ∈ Gʳ`, its **K-pattern** is the set of coordinates landing in `K`:
`T(v) = {i : v i ∈ K} ⊆ Fin r`. Partitioning the sum-zero tuples by `T(v)` is a disjoint
fiberwise decomposition (`G = H ⊔ K`, so each coordinate is in exactly one part):

> **`N0_dyadic_split_exact` :  `N₀(G, r) = ∑_{T : Finset (Fin r)} crossCell H K r T`**,

where `crossCell H K r T = #{ v ∈ Gʳ : ∑ vᵢ = 0, (∀ i ∈ T, vᵢ ∈ K), (∀ i ∉ T, vᵢ ∈ H) }`
is the number of sum-zero tuples with K-pattern *exactly* `T`. This is a pure partition
identity — no character sums, no regime hypotheses — exploiting only the disjoint-coset
structure `G = H ⊔ K`.

## How this localizes the obstruction (the named cross cells)

The two **endpoint** cells are the diagonal floor of `CumulantDyadicDescent`:
* `crossCell_empty` : `crossCell H K r ∅ = N₀(H, r)`        (all coordinates in `H`);
* `crossCell_univ`  : `crossCell H (ζ·H) r univ = N₀(H, r)` (all in `ζ·H`, via `w ↦ ζw`).

So `N₀(G,r) = 2·N₀(H,r) + ∑_{∅ ⊊ T ⊊ univ} crossCell H K r T` exactly
(`N0_dyadic_split_diag_plus_cross`). The sum over the **proper** patterns is the
**off-diagonal cross-resonance count** — the recognized open core (BCHKS Conj 1.12: each
proper cell counts `#{∑u + ζ·∑w = 0}` between two half-size subset-sum distributions, whose
generic size `≈ N₀(H,|Tᶜ|)·N₀(H,|T|)/n` is the distinct-subgroup-subset-sum statement that no
character-sum-free argument is known to bound at the prize point). The descent **is** exact;
what stays open is the *size* of the named cross cells, not their definition.

## Why this is the right "next" object

`CumulantDyadicDescent.N0_dyadic_descent_ge` proves only `≥` (the floor). The reverse — an
*upper* bound `N₀(μ_n,r) ≤ 2·N₀(μ_{n/2},r) + (small)` — is what the prize needs (the cumulant
`M`-ceiling). This file shows the *exact* surplus over the floor is `∑_{proper T} crossCell`,
i.e. the prize ceiling is **equivalent** to bounding the named cross cells. The dyadic
recursion does not collapse this term using only the 2-power structure; it is the same wall,
now an exact equation rather than an inequality with an unnamed gap.

## Main results (axiom-clean: `propext, Classical.choice, Quot.sound`)

* `crossCell` — the K-pattern cell count (sum-zero tuples with K-pattern exactly `T`).
* `N0_dyadic_split_exact` — **the headline**: `N₀(G,r) = ∑_T crossCell H K r T`.
* `crossCell_empty` / `crossCell_univ` — the two endpoint cells each equal `N₀(H,r)`.
* `N0_dyadic_split_diag_plus_cross` — `N₀(G,r) = 2·N₀(H,r) + (cross surplus)` (the exact form
  of the descent: the floor is `2·N₀(H,r)`, the surplus is the named cross-resonance sum).
* `cross_surplus_eq` — the surplus equals `N₀(G,r) − 2·N₀(H,r)` exactly (no inequality).

## References
- [BCHKS25] Ben-Sasson–Carmon–Haböck–Kopparty–Saraf. *On Proximity Gaps for Reed–Solomon Codes*.
  ECCC TR25-169 / ePrint 2025/2055. (Conjecture 1.12: distinct subgroup subset-sum lower bound —
  exactly the size of the proper cross cells of this exact split.)
- [ABF26] Arnon–Boneh–Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumRawMoment
open ArkLib.ProximityGap.CumulantDyadicDescent

namespace ArkLib.ProximityGap.CumulantDyadicSplitExact

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The K-pattern cell count. -/

/-- **The K-pattern cross cell.** For a disjoint coset union `G = H ⊔ K`, `crossCell H K r T`
counts the sum-zero `G`-tuples whose set of `K`-coordinates is *exactly* `T`: every `i ∈ T` has
`vᵢ ∈ K` and every `i ∉ T` has `vᵢ ∈ H`. (The tuple ranges over `(H ∪ K)ʳ`, equivalently over
`Gʳ` for `G = H ∪ K`.) -/
noncomputable def crossCell (H K : Finset F) (r : ℕ) (T : Finset (Fin r)) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin r => H ∪ K)).filter
    (fun v => (∑ i, v i = 0) ∧ (∀ i ∈ T, v i ∈ K) ∧ (∀ i ∉ T, v i ∈ H))).card

/-! ## 2. The exact split: partition the sum-zero tuples by their K-pattern. -/

/-- **The exact dyadic split (#407, the headline).** For a disjoint coset union `G = H ⊔ K`
(the squares/non-squares split `μ_n = μ_{n/2} ⊔ ζ·μ_{n/2}`), the additive-relation count
partitions *exactly* over the K-patterns:

> `N₀(G, r) = ∑_{T : Finset (Fin r)} crossCell H K r T`.

This is a pure, unconditional partition identity (no character sums, no regime hypothesis),
exploiting only the disjoint-coset structure. It is the exact upgrade of
`CumulantDyadicDescent.N0_dyadic_descent_ge` (which keeps only the two endpoint cells). -/
theorem N0_dyadic_split_exact {H K : Finset F} (hdisj : Disjoint H K) (r : ℕ) :
    N0 (H ∪ K) r = ∑ T : Finset (Fin r), crossCell H K r T := by
  classical
  rw [N0_card_eq]
  -- the K-pattern of a tuple: T(v) = {i : v i ∈ K}
  set S := (Fintype.piFinset (fun _ : Fin r => H ∪ K)).filter (fun v => ∑ i, v i = 0) with hS
  -- card S = ∑_T card (fiber over T)  (fiberwise card over the K-pattern map)
  rw [Finset.card_eq_sum_card_fiberwise
        (f := fun v => (Finset.univ.filter (fun i => v i ∈ K)))
        (t := (Finset.univ : Finset (Finset (Fin r))))
        (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro T _
  -- the fiber over T = crossCell H K r T
  unfold crossCell
  congr 1
  ext v
  simp only [Finset.mem_filter, Fintype.mem_piFinset, hS]
  constructor
  · rintro ⟨⟨hmem, hsum⟩, hfib⟩
    -- hfib : (univ.filter (v · ∈ K)) = T
    refine ⟨hmem, hsum, ?_, ?_⟩
    · intro i hiT
      have : i ∈ Finset.univ.filter (fun i => v i ∈ K) := by rw [hfib]; exact hiT
      exact (Finset.mem_filter.mp this).2
    · intro i hiT
      -- i ∉ T ⟹ v i ∉ K ⟹ v i ∈ H (since v i ∈ H ∪ K)
      have hnotK : v i ∉ K := by
        intro hK
        have : i ∈ Finset.univ.filter (fun i => v i ∈ K) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hK⟩
        rw [hfib] at this; exact hiT this
      rcases Finset.mem_union.mp (hmem i) with hH | hK
      · exact hH
      · exact absurd hK hnotK
  · rintro ⟨hmem, hsum, hTK, hTcH⟩
    refine ⟨⟨hmem, hsum⟩, ?_⟩
    -- the K-pattern equals T
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hK
      by_contra hiT
      -- i ∉ T ⟹ v i ∈ H, disjoint from K
      exact absurd (Finset.disjoint_left.mp hdisj (hTcH i hiT) hK) (by simp)
    · intro hiT; exact hTK i hiT

/-! ## 3. The two endpoint cells are each `N₀(H, r)` (recovering the diagonal floor). -/

/-- **The all-`H` endpoint cell.** The cell `T = ∅` (no coordinate in `K`) consists of the
sum-zero all-`H` tuples, so `crossCell H K r ∅ = N₀(H, r)`. -/
theorem crossCell_empty {H K : Finset F} (hdisj : Disjoint H K) (r : ℕ) :
    crossCell H K r ∅ = N0 H r := by
  classical
  unfold crossCell
  rw [N0_card_eq]
  congr 1
  ext v
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.notMem_empty, false_implies,
    implies_true, and_true, true_and, IsEmpty.forall_iff]
  constructor
  · rintro ⟨hmem, hsum, hH⟩
    exact ⟨fun i => hH i (by simp), hsum⟩
  · rintro ⟨hH, hsum⟩
    exact ⟨fun i => Finset.mem_union_left _ (hH i), hsum, fun i _ => hH i⟩

/-- **The all-`K` endpoint cell (`K = ζ·H`).** The cell `T = univ` (every coordinate in `K`)
consists of the sum-zero all-`K` tuples; via the bijection `w ↦ ζ·w` (`N0_smul_eq`) this is
again `N₀(H, r)`. -/
theorem crossCell_univ {H : Finset F} {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => ζ * y))) (r : ℕ) :
    crossCell H (H.image (fun y => ζ * y)) r Finset.univ = N0 H r := by
  classical
  set K := H.image (fun y => ζ * y) with hK
  unfold crossCell
  -- the cell is exactly the sum-zero all-K tuples = N0 K r = N0 H r
  have hcell : ((Fintype.piFinset (fun _ : Fin r => H ∪ K)).filter
      (fun v => (∑ i, v i = 0) ∧ (∀ i ∈ (Finset.univ : Finset (Fin r)), v i ∈ K)
        ∧ (∀ i ∉ (Finset.univ : Finset (Fin r)), v i ∈ H))).card
      = N0 K r := by
    rw [N0_card_eq]
    congr 1
    ext v
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_univ, forall_true_left,
      not_true_eq_false, false_implies, implies_true, and_true]
    constructor
    · rintro ⟨_, hsum, hKall⟩
      exact ⟨fun i => hKall i, hsum⟩
    · rintro ⟨hKall, hsum⟩
      exact ⟨fun i => Finset.mem_union_right _ (hKall i), hsum, fun i => hKall i⟩
  rw [hcell, hK, N0_smul_eq hζ r]

/-! ## 4. The exact descent: `N₀(G,r) = 2·N₀(H,r) + (named cross surplus)`. -/

/-- **The descent surplus is exactly `N₀(G,r) − 2·N₀(H,r)`.** Splitting off the two endpoint
cells (`∅` and `univ`, each `N₀(H,r)`), the remaining sum over the *proper* K-patterns
`∅ ⊊ T ⊊ univ` is the off-diagonal cross-resonance count, and it equals the surplus over the
diagonal floor *exactly*:

> `∑_{T : proper} crossCell H K r T = N₀(G,r) − 2·N₀(H,r)`.

This is the named open core: the prize ceiling (`N₀(μ_n,r) ≤ 2·N₀(μ_{n/2},r) + small`) is
*equivalent* to bounding this proper-pattern sum (BCHKS Conj 1.12). -/
theorem cross_surplus_eq {H : Finset F} {ζ : F} (hζ : ζ ≠ 0) (r : ℕ)
    (hr : 1 ≤ r)
    (hdisj : Disjoint H (H.image (fun y => ζ * y))) :
    (∑ T ∈ (Finset.univ.filter
        (fun T : Finset (Fin r) => T ≠ ∅ ∧ T ≠ Finset.univ)),
        crossCell H (H.image (fun y => ζ * y)) r T)
      = N0 (H ∪ H.image (fun y => ζ * y)) r - 2 * N0 H r := by
  classical
  set K := H.image (fun y => ζ * y) with hK
  -- ∅ ≠ univ since r ≥ 1
  have huniv_ne : (Finset.univ : Finset (Fin r)) ≠ ∅ := by
    obtain ⟨i₀⟩ : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    exact Finset.nonempty_iff_ne_empty.mp ⟨i₀, Finset.mem_univ _⟩
  -- total split
  have htot : N0 (H ∪ K) r = ∑ T : Finset (Fin r), crossCell H K r T :=
    N0_dyadic_split_exact (hK ▸ hdisj) r
  -- peel off the T = ∅ term, then the T = univ term, from the full sum
  have hpeel_empty : (∑ T : Finset (Fin r), crossCell H K r T)
      = crossCell H K r ∅
        + ∑ T ∈ (Finset.univ.filter (fun T : Finset (Fin r) => T ≠ ∅)),
            crossCell H K r T := by
    rw [Finset.sum_eq_sum_diff_singleton_add (i := (∅ : Finset (Fin r)))
          (Finset.mem_univ _)]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_singleton]
  -- now peel off T = univ from the (T ≠ ∅) sum
  have hpeel_univ : (∑ T ∈ (Finset.univ.filter (fun T : Finset (Fin r) => T ≠ ∅)),
        crossCell H K r T)
      = crossCell H K r Finset.univ
        + ∑ T ∈ (Finset.univ.filter (fun T : Finset (Fin r) => T ≠ ∅ ∧ T ≠ Finset.univ)),
            crossCell H K r T := by
    have hmem : (Finset.univ : Finset (Fin r))
        ∈ (Finset.univ.filter (fun T : Finset (Fin r) => T ≠ ∅)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, huniv_ne⟩
    rw [Finset.sum_eq_sum_diff_singleton_add hmem]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_singleton, and_assoc]
  have hsplit : (∑ T : Finset (Fin r), crossCell H K r T)
      = crossCell H K r ∅ + crossCell H K r Finset.univ
        + ∑ T ∈ (Finset.univ.filter (fun T : Finset (Fin r) => T ≠ ∅ ∧ T ≠ Finset.univ)),
            crossCell H K r T := by
    rw [hpeel_empty, hpeel_univ]; ring
  rw [crossCell_empty (hK ▸ hdisj) r, crossCell_univ hζ hdisj r] at hsplit
  -- N0 (H∪K) r = N0 H r + N0 H r + surplus ⟹ surplus = N0(G,r) - 2 N0 H r
  rw [htot, hsplit]
  omega

/-- **The exact descent (`N₀(G,r) = 2·N₀(H,r) + cross surplus`).** Restating `cross_surplus_eq`
as the additive decomposition: the additive-relation count is the diagonal floor `2·N₀(μ_{n/2},r)`
*plus* the named off-diagonal cross-resonance sum, exactly. The descent therefore neither loses
nor invents mass — the entire prize-relevant excess over the half-size floor is the proper-pattern
cross sum. -/
theorem N0_dyadic_split_diag_plus_cross {H : Finset F} {ζ : F} (hζ : ζ ≠ 0) (r : ℕ)
    (hr : 1 ≤ r)
    (hdisj : Disjoint H (H.image (fun y => ζ * y))) :
    N0 (H ∪ H.image (fun y => ζ * y)) r
      = 2 * N0 H r
        + (∑ T ∈ (Finset.univ.filter
            (fun T : Finset (Fin r) => T ≠ ∅ ∧ T ≠ Finset.univ)),
            crossCell H (H.image (fun y => ζ * y)) r T) := by
  have hfloor : 2 * N0 H r ≤ N0 (H ∪ H.image (fun y => ζ * y)) r :=
    N0_dyadic_descent_ge hζ hdisj hr
  rw [cross_surplus_eq hζ r hr hdisj]
  omega

end ArkLib.ProximityGap.CumulantDyadicSplitExact

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.CumulantDyadicSplitExact.N0_dyadic_split_exact
#print axioms ArkLib.ProximityGap.CumulantDyadicSplitExact.crossCell_empty
#print axioms ArkLib.ProximityGap.CumulantDyadicSplitExact.crossCell_univ
#print axioms ArkLib.ProximityGap.CumulantDyadicSplitExact.cross_surplus_eq
#print axioms ArkLib.ProximityGap.CumulantDyadicSplitExact.N0_dyadic_split_diag_plus_cross
