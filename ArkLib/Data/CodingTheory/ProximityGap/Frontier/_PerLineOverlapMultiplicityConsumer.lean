/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PerLineUnionCountBarrier

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Per-line union bounds with overlap multiplicity

`_PerLineUnionCountBarrier` records the obstruction: per-line bounds give only the union estimate

`#(union over lines) <= (#lines) * S`.

This file records the positive consumer that would make an overlap/collapse theorem useful.  If
every scalar in the union is hit by at least `M` active lines, then the line-count union bound
deflates by `M`:

`#union * M <= sum_i #(lineBad i)`.

Consequently, if every active line has size at most `S`, then

`#union <= (#lines * S) / M`.

Thus the missing #464 input is exactly a lower bound on per-scalar overlap multiplicity.  The
automatic case is only `M = 1`; any saving over the raw union bound must be earned by a genuine
overlap/collapse theorem.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.PerLineOverlapMultiplicityConsumer

open ArkLib.ProximityGap.Frontier.PerLineUnionCountBarrier

variable {ι γ : Type} [DecidableEq γ]

/-- The number of active lines whose bad set contains a scalar `x`. -/
def lineHitMultiplicity (I : Finset ι) (lineBad : ι -> Finset γ) (x : γ) : ℕ :=
  (I.filter fun i => x ∈ lineBad i).card

/-- The incidence-pair finset: a line together with one of its bad scalars. -/
def lineIncidencePairs (I : Finset ι) (lineBad : ι -> Finset γ) : Finset (Σ _ : ι, γ) :=
  I.sigma lineBad

/-- Second projection from an incidence pair. -/
def sigmaSnd : (Σ _ : ι, γ) -> γ := fun p => p.2

/-- Projecting incidence pairs to scalars gives exactly the bad-scalar union. -/
theorem image_sigmaSnd_eq_lineBadUnion
    (I : Finset ι) (lineBad : ι -> Finset γ) :
    (lineIncidencePairs I lineBad).image sigmaSnd = lineBadUnion I lineBad := by
  classical
  ext x
  simp [lineIncidencePairs, sigmaSnd, lineBadUnion]

/-- The fiber over a scalar under the incidence projection has cardinality equal to the number of
active lines containing that scalar. -/
theorem fiber_card_eq_lineHitMultiplicity
    (I : Finset ι) (lineBad : ι -> Finset γ) (x : γ) :
    ((lineIncidencePairs I lineBad).filter (fun p => sigmaSnd p = x)).card =
      lineHitMultiplicity I lineBad x := by
  classical
  unfold lineHitMultiplicity lineIncidencePairs sigmaSnd
  refine Finset.card_bij (fun p _hp => p.1) ?hmem ?hinj ?hsurj
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    rcases hp with ⟨hpSigma, hsnd⟩
    rw [Finset.mem_sigma] at hpSigma
    rcases hpSigma with ⟨hpI, hpLine⟩
    exact ⟨hpI, by simpa [hsnd.symm] using hpLine⟩
  · intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    rcases ha with ⟨_haSigma, haSnd⟩
    rcases hb with ⟨_hbSigma, hbSnd⟩
    cases a with
    | mk ai ax =>
      cases b with
      | mk bi bx =>
        dsimp at hab haSnd hbSnd
        subst bi
        congr
        exact haSnd.trans hbSnd.symm
  · intro i hi
    rw [Finset.mem_filter] at hi
    rcases hi with ⟨hiI, hix⟩
    refine ⟨⟨i, x⟩, ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_sigma]
    exact ⟨⟨hiI, hix⟩, rfl⟩

/-- Double-counting incidence pairs by line or by scalar gives the same total. -/
theorem sum_lineHitMultiplicity_eq_sum_card
    (I : Finset ι) (lineBad : ι -> Finset γ) :
    (∑ x ∈ lineBadUnion I lineBad, lineHitMultiplicity I lineBad x) =
      ∑ i ∈ I, (lineBad i).card := by
  classical
  have himage := image_sigmaSnd_eq_lineBadUnion I lineBad
  calc
    (∑ x ∈ lineBadUnion I lineBad, lineHitMultiplicity I lineBad x)
        = ∑ x ∈ (lineIncidencePairs I lineBad).image sigmaSnd,
            ((lineIncidencePairs I lineBad).filter (fun p => sigmaSnd p = x)).card := by
          rw [himage]
          exact Finset.sum_congr rfl (by intro x _hx; rw [fiber_card_eq_lineHitMultiplicity])
    _ = (lineIncidencePairs I lineBad).card := by
          exact (Finset.card_eq_sum_card_image sigmaSnd (lineIncidencePairs I lineBad)).symm
    _ = ∑ i ∈ I, (lineBad i).card := by
          simp [lineIncidencePairs]

/-- Every scalar in the union is automatically hit by at least one active line.  This recovers the
raw union bound and shows that any better saving needs a real `M > 1` theorem. -/
theorem one_le_lineHitMultiplicity_of_mem_lineBadUnion
    (I : Finset ι) (lineBad : ι -> Finset γ) {x : γ}
    (hx : x ∈ lineBadUnion I lineBad) :
    1 <= lineHitMultiplicity I lineBad x := by
  classical
  rw [lineBadUnion] at hx
  rcases Finset.mem_biUnion.mp hx with ⟨i, hiI, hix⟩
  unfold lineHitMultiplicity
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hiI, hix⟩⟩

/-- If every scalar in the union is hit by at least `M` active lines, then the union cardinality
times `M` is bounded by the total line-incidence count. -/
theorem card_mul_le_sum_card_of_each_union_point_hit_many
    (I : Finset ι) (lineBad : ι -> Finset γ) {M : ℕ}
    (hM : ∀ x ∈ lineBadUnion I lineBad, M <= lineHitMultiplicity I lineBad x) :
    (lineBadUnion I lineBad).card * M <= ∑ i ∈ I, (lineBad i).card := by
  classical
  calc
    (lineBadUnion I lineBad).card * M = ∑ _x ∈ lineBadUnion I lineBad, M := by
      simp [Finset.sum_const, mul_comm]
    _ <= ∑ x ∈ lineBadUnion I lineBad, lineHitMultiplicity I lineBad x :=
      Finset.sum_le_sum hM
    _ = ∑ i ∈ I, (lineBad i).card := by
      rw [sum_lineHitMultiplicity_eq_sum_card]

/-- Quotient form of the overlap consumer. -/
theorem card_le_sum_card_div_of_each_union_point_hit_many
    (I : Finset ι) (lineBad : ι -> Finset γ) {M : ℕ}
    (hMpos : 1 <= M)
    (hM : ∀ x ∈ lineBadUnion I lineBad, M <= lineHitMultiplicity I lineBad x) :
    (lineBadUnion I lineBad).card <= (∑ i ∈ I, (lineBad i).card) / M := by
  rw [Nat.le_div_iff_mul_le hMpos]
  exact card_mul_le_sum_card_of_each_union_point_hit_many I lineBad hM

/-- If every line has at most `S` bad scalars and every union scalar is hit by at least `M` lines,
then the union bound loses only the factor `#lines / M`. -/
theorem card_lineBadUnion_le_card_mul_div_of_each_le_and_overlap
    (I : Finset ι) (lineBad : ι -> Finset γ) {S M : ℕ}
    (hMpos : 1 <= M)
    (hline : ∀ i ∈ I, (lineBad i).card <= S)
    (hM : ∀ x ∈ lineBadUnion I lineBad, M <= lineHitMultiplicity I lineBad x) :
    (lineBadUnion I lineBad).card <= (I.card * S) / M := by
  have hmul := card_mul_le_sum_card_of_each_union_point_hit_many I lineBad hM
  rw [Nat.le_div_iff_mul_le hMpos]
  exact le_trans hmul (Finset.sum_le_card_nsmul I (fun i => (lineBad i).card) S hline)

/-! ## Axiom audit -/
#print axioms lineHitMultiplicity
#print axioms lineIncidencePairs
#print axioms sigmaSnd
#print axioms image_sigmaSnd_eq_lineBadUnion
#print axioms fiber_card_eq_lineHitMultiplicity
#print axioms sum_lineHitMultiplicity_eq_sum_card
#print axioms one_le_lineHitMultiplicity_of_mem_lineBadUnion
#print axioms card_mul_le_sum_card_of_each_union_point_hit_many
#print axioms card_le_sum_card_div_of_each_union_point_hit_many
#print axioms card_lineBadUnion_le_card_mul_div_of_each_le_and_overlap

end ArkLib.ProximityGap.Frontier.PerLineOverlapMultiplicityConsumer
