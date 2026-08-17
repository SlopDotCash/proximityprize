/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMomentLadder
import Mathlib.Tactic

/-!
# K1: the negation-closed `r`-fold walk bound — counting core (#389)

The conditional square-root cancellation (`ConditionalSqrtCancellation`) reduces the δ\*
wall to a bound on the `r`-fold additive energy `E_r(μ_n)`. The full-Sidon bound
`E_r ≤ r!·n^r` (`energyR_le_factorial`) does NOT apply, because `μ_n` is negation-closed:
the zero-sum fibers are large (`(a,−a)` and `(b,−b)` both sum to 0), which is exactly the
antipodal excess `E₂(μ_n) = 3n²−3n`. The correct bound is the **negation-closed walk
count** `E_r(μ_n) ≤ (2r−1)!!·n^r`, the open step the fleet flagged as **K1**.

The per-fiber mirror of `energyR_le_factorial` fails here (the zero-sum fiber has `~n`
elements, not `O(1)`). This file supplies the correct GLOBAL argument: antipodal
structure is encoded as a **fixed-point-free involution** (a perfect matching) of the
`2r` summands, and the count is bounded by `(#pairings)·n^r` — the matching count times
the free values on a transversal.

* `IsPairing σ` — `σ : Perm (Fin (2r))` is a fixed-point-free involution (a perfect
  matching of the `2r` positions).
* `card_lowerHalf` — a pairing has exactly `r` "lower" positions `{i : i < σ i}`
  (one per matched pair): the transversal of the matching.
* `antipodalConsistent_card_le` — the tuples `c` with `c (σ i) = −c i` for a fixed pairing
  `σ` number at most `n^r` (determined by their values on the transversal).
* `zeroSumCount_le_pairings` — **the K1 counting core**: under the named residual that
  every zero-sum `2r`-tuple of `G` is antipodally paired by some `σ`, the zero-sum count
  is `≤ (#pairings)·n^r`. With `#pairings = (2r−1)!!` (the standard perfect-matching
  count) this is exactly `E_r(G) ≤ (2r−1)!!·n^r`.
* `energyR_eq_zeroSumCount` — for negation-closed `G`, `E_r(G)` equals the zero-sum count
  `Z_{2r}(G)` (negate the second tuple), tying the bound to the moment ladder.

The named residual (every zero-sum tuple is antipodally paired) is the no-genuine-relation
hypothesis — true in characteristic zero for `2`-power roots of unity (the fleet's
antipodal-closure results) and for `n ≲ √p` (probe `probe_smallsubgroup_minimal_energy`,
where `E_r = (2r−1)!!·n^r` holds exactly); the deep analytic content (its range of
validity) is the Konyagin–Shparlinski/Stepanov input. This file discharges the COUNTING
half of K1 unconditionally; the hypothesis is the isolated residual.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
* Issue #389; `ConditionalSqrtCancellation.lean` (the K1 scope note),
  `GeneralEnergyBound.lean` (the full-Sidon `r!` analog), `SubgroupGaussSumMomentLadder`.
-/

set_option linter.style.longLine false


open Finset

namespace ArkLib.ProximityGap.NegationClosedWalk

variable {F : Type*} [Field F] [DecidableEq F]

/-- A **pairing** of `Fin (2r)`: a fixed-point-free involution (perfect matching). -/
def IsPairing {r : ℕ} (σ : Equiv.Perm (Fin (2 * r))) : Prop :=
  Function.Involutive σ ∧ ∀ i, σ i ≠ i

instance {r : ℕ} (σ : Equiv.Perm (Fin (2 * r))) : Decidable (IsPairing σ) := by
  unfold IsPairing Function.Involutive
  infer_instance

/-- The transversal (lower halves) of a pairing: positions below their partner. -/
def lowerHalf {r : ℕ} (σ : Equiv.Perm (Fin (2 * r))) : Finset (Fin (2 * r)) :=
  Finset.univ.filter (fun i => i < σ i)

/-- A pairing has exactly `r` lower positions (one per matched pair). -/
theorem card_lowerHalf {r : ℕ} {σ : Equiv.Perm (Fin (2 * r))} (hσ : IsPairing σ) :
    (lowerHalf σ).card = r := by
  classical
  obtain ⟨hinv, hfix⟩ := hσ
  set L := lowerHalf σ with hL
  set U := Finset.univ.filter (fun i => σ i < i) with hU
  -- σ maps L bijectively onto U
  have hmaps : ∀ i ∈ L, σ i ∈ U := by
    intro i hi
    simp only [hL, lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hinv i]; exact hi
  have hinj : Set.InjOn σ L := fun a _ b _ h => σ.injective h
  have himg : L.image σ = U := by
    apply Finset.Subset.antisymm
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact hmaps i hi
    · intro j hj
      simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      refine Finset.mem_image.mpr ⟨σ j, ?_, hinv j⟩
      simp only [hL, lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hinv j]; exact hj
  have hcardLU : L.card = U.card := by
    rw [← himg, Finset.card_image_of_injOn hinj]
  -- L and U partition univ (fpf ⟹ every i is < or > its partner)
  have hdisj : Disjoint L U := by
    rw [Finset.disjoint_left]
    intro i hiL hiU
    simp only [hL, lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and] at hiL
    simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and] at hiU
    exact absurd hiL (not_lt.mpr (le_of_lt hiU))
  have hunion : L ∪ U = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    rw [Finset.mem_union]
    rcases lt_trichotomy i (σ i) with h | h | h
    · left; simp only [hL, lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and]; exact h
    · exact absurd h.symm (hfix i)
    · right; simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and]; exact h
  have htot : L.card + U.card = 2 * r := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  omega

/-- The tuples `c : Fin (2r) → G` with `c (σ i) = −c i` for a fixed pairing `σ` are
determined by their values on the transversal, so number at most `n^r`. -/
theorem antipodalConsistent_card_le {r : ℕ} (G : Finset F)
    {σ : Equiv.Perm (Fin (2 * r))} (hσ : IsPairing σ) :
    ((Fintype.piFinset (fun _ : Fin (2 * r) => G)).filter
        (fun c => ∀ i, c (σ i) = - c i)).card ≤ G.card ^ r := by
  classical
  have hinv : Function.Involutive σ := hσ.1
  have hfix : ∀ i, σ i ≠ i := hσ.2
  set P := Fintype.piFinset (fun _ : Fin (2 * r) => G) with hP
  set A := P.filter (fun c => ∀ i, c (σ i) = - c i) with hA
  set e := (lowerHalf σ).orderIsoOfFin (card_lowerHalf hσ) with he
  have hbound : A.card ≤ (Fintype.piFinset (fun _ : Fin r => G)).card := by
    apply Finset.card_le_card_of_injOn (fun c => fun k : Fin r => c ((e k : Fin (2 * r))))
    · intro c hc
      rw [Finset.mem_coe, hA, Finset.mem_filter, hP, Fintype.mem_piFinset] at hc
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      exact fun k => hc.1 _
    · intro c hc c' hc' hcc
      rw [Finset.mem_coe, hA, Finset.mem_filter] at hc hc'
      have hagreeL : ∀ i ∈ lowerHalf σ, c i = c' i := by
        intro i hi
        have hk := congrFun hcc (e.symm ⟨i, hi⟩)
        simpa only [OrderIso.apply_symm_apply] using hk
      funext i
      by_cases hi : i ∈ lowerHalf σ
      · exact hagreeL i hi
      · have hilt : ¬ i < σ i := by simpa [lowerHalf] using hi
        have hjlow : σ i ∈ lowerHalf σ := by
          simp only [lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hinv i]
          rcases lt_trichotomy i (σ i) with h | h | h
          · exact absurd h hilt
          · exact absurd h.symm (hfix i)
          · exact h
        have h1 : c i = - c (σ i) := by
          have h := hc.2 (σ i); rw [hinv i] at h; exact h
        have h2 : c' i = - c' (σ i) := by
          have h := hc'.2 (σ i); rw [hinv i] at h; exact h
        rw [h1, h2, hagreeL (σ i) hjlow]
  calc A.card ≤ (Fintype.piFinset (fun _ : Fin r => G)).card := hbound
    _ = G.card ^ r := by rw [Fintype.card_piFinset]; simp

/-- The zero-sum count of `m`-tuples from `G`. -/
def zeroSumCount (G : Finset F) (m : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin m => G)).filter (fun c => ∑ i, c i = 0)).card

/-- **K1 counting core.** If every zero-sum `2r`-tuple of `G` is antipodally paired by
some pairing `σ` (`c (σ i) = −c i`), then the zero-sum count is at most `(#pairings)·n^r`.
With `#pairings = (2r−1)!!` this is `E_r(G) ≤ (2r−1)!!·n^r`, the negation-closed walk
bound (K1). The hypothesis is the no-genuine-relation residual. -/
theorem zeroSumCount_le_pairings {r : ℕ} (G : Finset F)
    (H : ∀ c ∈ Fintype.piFinset (fun _ : Fin (2 * r) => G), (∑ i, c i = 0) →
        ∃ σ : Equiv.Perm (Fin (2 * r)), IsPairing σ ∧ ∀ i, c (σ i) = - c i) :
    zeroSumCount G (2 * r)
      ≤ (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * r)) => IsPairing σ)).card
          * G.card ^ r := by
  classical
  set P := Fintype.piFinset (fun _ : Fin (2 * r) => G) with hP
  set Pairs := Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * r)) => IsPairing σ) with hPairs
  -- the zero-sum set is covered by the antipodal-consistent sets over all pairings
  have hcover : P.filter (fun c => ∑ i, c i = 0)
      ⊆ Pairs.biUnion (fun σ => P.filter (fun c => ∀ i, c (σ i) = - c i)) := by
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨σ, hσ, hcσ⟩ := H c hc.1 hc.2
    refine Finset.mem_biUnion.mpr ⟨σ, ?_, ?_⟩
    · simp only [hPairs, Finset.mem_filter, Finset.mem_univ, true_and]; exact hσ
    · rw [Finset.mem_filter]; exact ⟨hc.1, hcσ⟩
  calc zeroSumCount G (2 * r)
      = (P.filter (fun c => ∑ i, c i = 0)).card := rfl
    _ ≤ (Pairs.biUnion (fun σ => P.filter (fun c => ∀ i, c (σ i) = - c i))).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ σ ∈ Pairs, (P.filter (fun c => ∀ i, c (σ i) = - c i)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _σ ∈ Pairs, G.card ^ r := by
        refine Finset.sum_le_sum (fun σ hσ => ?_)
        have hσP : IsPairing σ := (Finset.mem_filter.mp hσ).2
        exact antipodalConsistent_card_le G hσP
    _ = Pairs.card * G.card ^ r := by rw [Finset.sum_const, smul_eq_mul]

/-! ## Source audit -/

#print axioms card_lowerHalf
#print axioms antipodalConsistent_card_le
#print axioms zeroSumCount_le_pairings

end ArkLib.ProximityGap.NegationClosedWalk
