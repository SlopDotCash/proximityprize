/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R392RelationCountCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R372ShadowRelationRotationEquivariance

/-!
# LANE B2 (#466 G59): THE FREE-ORBIT DELIMITER — substituting `K = n·orbitRepCount` into
  R392 is an EXACT relabeling, not a gain; the prize needs a weighted-representative hypothesis

The r371/r372 rotation action `rotZ` (the `z ↦ ζ·z` shadow twist, `ζ` a primitive `2m`-th
root, hence of order `n = 2m`) acts on the R388 realized-relation set, `NR`-mass-invariantly
(`NR_rotZ`), vanishing-stably (`rotZ_eval_zero_iff`), height-preservingly (`rotZ_height_le`).
So the total relation count `K = ∑_s #sectorRelations s` that R392 needs is `rotZ`-orbit
structured.  The tempting "quotient gain" is: bound `K` by `n · (#orbits)` and hope the orbit
count is small.  THIS FILE PROVES THAT MOVE CANNOT HELP, and isolates exactly what would.

The mathematics, stated abstractly over a finite type acted on by a fixed-point-free
order-`n` bijection (the `rotZ` regime):

* **`freeOrbit_card`** :  a FREE `C_n` action on a finite `S` (`σ^n = id`, and no nonzero
  power `< n` fixes any point) has `S.card = n · orbitRepCount`, where `orbitRepCount` is the
  number of orbits.  This is an EXACT IDENTITY, not a bound — it pins the orbit size at `n` and
  PERMANENTLY PREVENTS orbit-size churn.

* **`mass_eq_n_mul_repMass`** :  if a weight `w : α → ℕ` is `σ`-invariant, the total mass is
  `∑_{x∈S} w x = n · ∑_{o∈reps} w o` — the EXACT free-orbit MASS decomposition.

* **`relCountBound_of_free_orbit`** :  taking `K := n · orbitRepCount`, the R392 input
  `RealizedRelationCountBound` holds with EQUALITY when the relation-set action is free.

* **`energy_eq_relabel_no_gain`** (THE NO-GO):  substituting `K = n · orbitRepCount` into the
  R392 consumer gives `E ≤ (1 + n·orbitRepCount)·shadowE`, which is LITERALLY the R392 bound at
  the exact `K`.  No shrinkage: `NR_rotZ` makes every orbit member carry identical mass.

* **`no_gain_without_representative_hypothesis`** (the delimiter):  a strict improvement
  `K' < S.card` is EQUIVALENT to `K' < n·orbitRepCount`, i.e. it must beat the raw orbit count.
  Since the free-orbit identity pins `S.card = n·orbitRepCount` with NO slack, such a `K'`
  requires a NEW input: a representative-COUNT bound or a representative-MASS predicate.  The
  quotient supplies neither.  This exposes the single prize-facing WEIGHTED-REPRESENTATIVE object.

Net: the `rotZ` quotient reorganizes `K` into `n · orbitRepCount` exactly and cannot lower it;
orbit-size churn is closed; the open input is precisely a weighted-representative bound.
Issue #466, G59, LANE B2.  Axiom-clean, real locked build.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.G59FreeOrbitDelimiterNoGo

/-! ## Part 1 — abstract free `C_n` orbit combinatorics (self-contained) -/

variable {α : Type*} [DecidableEq α]

/-- The forward orbit of `x` under the first `n` powers of `σ`. -/
def orbitOf (σ : α → α) (n : ℕ) (x : α) : Finset α :=
  (Finset.range n).image (fun k => σ^[k] x)

/-- A predicate packaging a FREE order-`n` action of `σ` on a finite carrier `S`:
`σ` maps `S` to itself, `σ^n = id` on `S`, and no power `1 ≤ k < n` fixes any point of `S`
(fixed-point-free at every nontrivial power — the "free" / no-orbit-collapse condition). -/
structure FreeAction (σ : α → α) (n : ℕ) (S : Finset α) : Prop where
  pos : 0 < n
  maps : ∀ x ∈ S, σ x ∈ S
  period : ∀ x ∈ S, σ^[n] x = x
  free : ∀ x ∈ S, ∀ k, 0 < k → k < n → σ^[k] x ≠ x

/-- Iterates stay in `S`. -/
theorem iterate_mem {σ : α → α} {n : ℕ} {S : Finset α} (hA : FreeAction σ n S)
    {x : α} (hx : x ∈ S) (k : ℕ) : σ^[k] x ∈ S := by
  induction k with
  | zero => simpa using hx
  | succ j ih => rw [Function.iterate_succ_apply']; exact hA.maps _ ih

/-- Under a free action, the forward orbit of a point has exactly `n` elements. -/
theorem orbitOf_card {σ : α → α} {n : ℕ} {S : Finset α} (hA : FreeAction σ n S)
    {x : α} (hx : x ∈ S) : (orbitOf σ n x).card = n := by
  classical
  unfold orbitOf
  rw [Finset.card_image_of_injOn]
  · rw [Finset.card_range]
  · -- `k ↦ σ^[k] x` is injective on `range n`, from freeness
    have key : ∀ a b, a < n → b < n → a < b → σ^[a] x ≠ σ^[b] x := by
      intro a b _ hbn hab heq
      -- `σ^[b] x = σ^[a] x` with `a < b < n` ⇒ `σ^[b-a] (σ^[a] x) = σ^[a] x`, contradiction
      have hcancel : σ^[b - a] (σ^[a] x) = σ^[a] x := by
        rw [← Function.iterate_add_apply, show b - a + a = b from by omega]
        exact heq.symm
      exact hA.free _ (iterate_mem hA hx a) (b - a) (by omega) (by omega) hcancel
    intro a ha b hb hab
    rw [Finset.coe_range, Set.mem_Iio] at ha hb
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (key a b ha hb h)
    · exact h
    · exact absurd hab.symm (key b a hb ha h)

/-- The orbit-representative data: `reps ⊆ S` and every point of `S` lies in exactly one
representative's forward orbit. -/
def IsRepSet (σ : α → α) (n : ℕ) (S reps : Finset α) : Prop :=
  reps ⊆ S ∧ (∀ x ∈ S, ∃! o, o ∈ reps ∧ x ∈ orbitOf σ n o)

/-- `S` is the union of the representative orbits. -/
theorem cover_of_repSet {σ : α → α} {n : ℕ} {S reps : Finset α}
    (hA : FreeAction σ n S) (hrep : IsRepSet σ n S reps) :
    S = reps.biUnion (fun o => orbitOf σ n o) := by
  classical
  obtain ⟨hsub, huniq⟩ := hrep
  ext x
  simp only [Finset.mem_biUnion]
  constructor
  · intro hx; obtain ⟨o, ⟨ho, hxo⟩, _⟩ := huniq x hx; exact ⟨o, ho, hxo⟩
  · rintro ⟨o, ho, hxo⟩
    unfold orbitOf at hxo
    rw [Finset.mem_image] at hxo
    obtain ⟨k, _, rfl⟩ := hxo
    exact iterate_mem hA (hsub ho) k

/-- The representative orbits are pairwise disjoint. -/
theorem disjoint_of_repSet {σ : α → α} {n : ℕ} {S reps : Finset α}
    (hA : FreeAction σ n S) (hrep : IsRepSet σ n S reps) :
    (reps : Set α).PairwiseDisjoint (fun o => orbitOf σ n o) := by
  classical
  obtain ⟨hsub, huniq⟩ := hrep
  intro a ha b hb hab
  rw [Finset.mem_coe] at ha hb
  rw [Function.onFun, Finset.disjoint_left]
  intro x hxa hxb
  have hxS : x ∈ S := by
    unfold orbitOf at hxa
    rw [Finset.mem_image] at hxa
    obtain ⟨k, _, rfl⟩ := hxa
    exact iterate_mem hA (hsub ha) k
  obtain ⟨o, _, ho2⟩ := huniq x hxS
  exact hab (by rw [ho2 a ⟨ha, hxa⟩, ho2 b ⟨hb, hxb⟩])

/-- **The free-orbit cardinality identity**: `S.card = n · reps.card`.  Exact — pins orbit
size at `n`, no churn. -/
theorem freeOrbit_card {σ : α → α} {n : ℕ} {S reps : Finset α}
    (hA : FreeAction σ n S) (hrep : IsRepSet σ n S reps) :
    S.card = n * reps.card := by
  classical
  have hcover := cover_of_repSet hA hrep
  have hdisj := disjoint_of_repSet hA hrep
  rw [hcover, Finset.card_biUnion (fun a ha b hb hab => hdisj ha hb hab)]
  rw [Finset.sum_congr rfl (fun o ho => orbitOf_card hA (hrep.1 ho))]
  rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **The free-orbit MASS decomposition**: a `σ`-invariant weight has total mass
`n · (sum over representatives)`. -/
theorem mass_eq_n_mul_repMass {σ : α → α} {n : ℕ} {S reps : Finset α}
    (hA : FreeAction σ n S) (hrep : IsRepSet σ n S reps)
    (w : α → ℕ) (hw : ∀ x ∈ S, w (σ x) = w x) :
    ∑ x ∈ S, w x = n * ∑ o ∈ reps, w o := by
  classical
  have hsub := hrep.1
  -- `w` is constant on each forward orbit
  have hconst : ∀ o ∈ reps, ∀ x ∈ orbitOf σ n o, w x = w o := by
    intro o ho x hx
    unfold orbitOf at hx
    rw [Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hoS : o ∈ S := hsub ho
    clear hk ho
    induction k with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', hw _ (iterate_mem hA hoS j), ih]
  have hcover := cover_of_repSet hA hrep
  have hdisj := disjoint_of_repSet hA hrep
  calc ∑ x ∈ S, w x
      = ∑ o ∈ reps, ∑ x ∈ orbitOf σ n o, w x := by
        rw [hcover]
        exact Finset.sum_biUnion (fun a ha b hb hab => hdisj ha hb hab)
    _ = ∑ o ∈ reps, ∑ _x ∈ orbitOf σ n o, w o := by
        exact Finset.sum_congr rfl
          (fun o ho => Finset.sum_congr rfl (fun x hx => hconst o ho x hx))
    _ = ∑ o ∈ reps, (orbitOf σ n o).card * w o := by
        exact Finset.sum_congr rfl
          (fun o _ => by rw [Finset.sum_const, smul_eq_mul])
    _ = ∑ o ∈ reps, n * w o := by
        exact Finset.sum_congr rfl (fun o ho => by rw [orbitOf_card hA (hsub ho)])
    _ = n * ∑ o ∈ reps, w o := by rw [Finset.mul_sum]

/-! ## Part 2 — the no-go: `K = n·orbitRepCount` is an exact relabeling of R392, no gain -/

/-- `orbitRepCount` — the number of `rotZ`-orbits of the relation set, i.e. `reps.card`. -/
def orbitRepCount (reps : Finset α) : ℕ := reps.card

/-- **Free-orbit substitution into R392 holds with EQUALITY.**  With `K := n·orbitRepCount reps`,
the exact total relation count `S.card` equals `K`, so the R392 input `S.card ≤ K` holds — and
exactly, giving no headroom to shrink. -/
theorem relCountBound_of_free_orbit {σ : α → α} {n : ℕ} {S reps : Finset α}
    (hA : FreeAction σ n S) (hrep : IsRepSet σ n S reps) :
    S.card = n * orbitRepCount reps ∧ S.card ≤ n * orbitRepCount reps := by
  have h := freeOrbit_card hA hrep
  unfold orbitRepCount
  exact ⟨h, le_of_eq h⟩

/-- **THE NO-GO (energy layer).**  Take `K := n·orbitRepCount reps`.  In the free regime `K`
equals the exact total relation count `S.card`, so the R392 consumer bound
`E ≤ (1 + K)·shadowE` at this `K` is LITERALLY the bound at the exact count `S.card`. -/
theorem energy_eq_relabel_no_gain {σ : α → α} {n : ℕ} {S reps : Finset α}
    (hA : FreeAction σ n S) (hrep : IsRepSet σ n S reps)
    (E shadowE : ℕ)
    (hbound : E ≤ (1 + S.card) * shadowE) :
    E ≤ (1 + n * orbitRepCount reps) * shadowE ∧
      (1 + n * orbitRepCount reps) * shadowE = (1 + S.card) * shadowE := by
  have h : S.card = n * orbitRepCount reps := (relCountBound_of_free_orbit hA hrep).1
  exact ⟨by rw [← h]; exact hbound, by rw [h]⟩

/-- **THE DELIMITER (permanent no-churn + prize-facing hypothesis isolation).**
Any strict improvement over the exact free-orbit count — a `K' < S.card` — is EQUIVALENT to
`K' < n·orbitRepCount reps`.  The free-orbit identity pins `S.card = n·orbitRepCount` with NO
slack, so such a `K'` requires a NEW input on the representatives (a count bound or a mass
predicate); the quotient alone cannot supply it.  Orbit SIZE is fixed at `n` — no churn. -/
theorem no_gain_without_representative_hypothesis
    {σ : α → α} {n : ℕ} {S reps : Finset α}
    (hA : FreeAction σ n S) (hrep : IsRepSet σ n S reps) (K' : ℕ) :
    (K' < S.card ↔ K' < n * orbitRepCount reps) := by
  rw [(relCountBound_of_free_orbit hA hrep).1]

/-- **Mass form of the delimiter.**  The `σ`-invariant relation MASS decomposes exactly as
`n · (representative mass)`.  So a sub-Wick mass certificate is EQUIVALENT to a bound on the
representative mass `∑_{o∈reps} w o` — the weighted-representative hypothesis; the factor `n`
and the per-orbit multiplicity are fixed and cannot be manipulated. -/
theorem mass_no_gain_without_weighted_representative
    {σ : α → α} {n : ℕ} {S reps : Finset α}
    (hA : FreeAction σ n S) (hrep : IsRepSet σ n S reps)
    (w : α → ℕ) (hw : ∀ x ∈ S, w (σ x) = w x) (M : ℕ) :
    ((∑ x ∈ S, w x) ≤ M ↔ n * (∑ o ∈ reps, w o) ≤ M) := by
  rw [mass_eq_n_mul_repMass hA hrep w hw]

end ArkLib.ProximityGap.Frontier.G59FreeOrbitDelimiterNoGo

/-! ## Part 3 — keying to the real `rotZ` action on R388 relations (bridge lemma) -/

namespace ArkLib.ProximityGap.Frontier.G59FreeOrbitDelimiterNoGo

open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R371ShadowKernelRotationAction
open ArkLib.ProximityGap.Frontier.R372ShadowRelationRotationEquivariance

/-- The `rotZ` weight `NR n m r` is `rotZ`-invariant on ALL of `Fin m → ℤ` (from `NR_rotZ`),
hence on any relation set — the mass-invariance hypothesis of
`mass_no_gain_without_weighted_representative` is DISCHARGED by r372 for the real action. -/
theorem NR_rotZ_invariant (n m r : ℕ) (hm : 0 < m) (hn : n = 2 * m)
    (S : Finset (Fin m → ℤ)) :
    ∀ x ∈ S, NR n m r (rotZ m hm x) = NR n m r x :=
  fun x _ => NR_rotZ n m r hm hn x

end ArkLib.ProximityGap.Frontier.G59FreeOrbitDelimiterNoGo

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.G59FreeOrbitDelimiterNoGo in
#print axioms orbitOf_card
open ArkLib.ProximityGap.Frontier.G59FreeOrbitDelimiterNoGo in
#print axioms freeOrbit_card
open ArkLib.ProximityGap.Frontier.G59FreeOrbitDelimiterNoGo in
#print axioms mass_eq_n_mul_repMass
open ArkLib.ProximityGap.Frontier.G59FreeOrbitDelimiterNoGo in
#print axioms relCountBound_of_free_orbit
open ArkLib.ProximityGap.Frontier.G59FreeOrbitDelimiterNoGo in
#print axioms energy_eq_relabel_no_gain
open ArkLib.ProximityGap.Frontier.G59FreeOrbitDelimiterNoGo in
#print axioms no_gain_without_representative_hypothesis
open ArkLib.ProximityGap.Frontier.G59FreeOrbitDelimiterNoGo in
#print axioms mass_no_gain_without_weighted_representative
open ArkLib.ProximityGap.Frontier.G59FreeOrbitDelimiterNoGo in
#print axioms NR_rotZ_invariant
