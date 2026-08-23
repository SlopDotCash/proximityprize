/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GWKernelReduction
import ArkLib.Data.CodingTheory.ProximityGap.GWDirectionScopedWiring
import Mathlib.Algebra.Field.ZMod

/-!
# GW BRICK-L (`GWAffineFiberCharge`) refuted-and-repaired: the affine-flat per-coordinate charge

This file completes the rigour audit of the Guruswami–Wang kernel reduction R2 chain
(`GWKernelReduction.lean` / `GWDirectionScopedWiring.lean`).  The scoped wiring already caught
that **BRICK-W** (`GWDirectionFinrankLe`) is false for genuine codes and replaced it.  The
*last live leaf* of that chain was **BRICK-L** (`GWAffineFiberCharge`), the per-coordinate
affine-flat charge.  Here we:

1. **Refute `GWAffineFiberCharge` as literally stated** (machine-checked, with a concrete
   satisfiable countermodel).  Its second conjunct demands `finrank A ≤ |Lset| − 1` *as reals*.
   On the **empty close list** (`|Lset| = 0`, genuinely reachable in the non-degenerate regime
   `δ ≥ 0` — just take an `f` far from every codeword) this forces `(finrank A : ℝ) ≤ −1`, which
   is impossible since `finrank ≥ 0`.  Hence `GWAffineFiberCharge` is **unsatisfiable** for any
   design admitting an empty close list — i.e. the scoped headline
   `cz25CoordFiberCap_of_interp_and_multiplicity_scoped` consumes a hypothesis `hL` that is false
   for some `f`.  The target `CZ25CoordFiberCap` is by contrast satisfiable on the empty list
   (its cap reads `0 ≤ (1 − τ(r₀))·n`, true once `τ(r₀) ≤ 1`); the bug is the *factoring through
   `finrank A`*, not the cap.

2. **Repair: reduce the genuine target `CZ25CoordFiberCap` to ONE named per-coordinate
   affine-flat charge** `GWFiberCardCharge`, reusing the **proven-in-tree** design budget
   (`IsSubspaceDesign` on the recentred span) and the new dimension bound
   `finrank_recentred_span_le` (`dim span{c − c₀ : c ∈ Lset} ≤ |Lset| − 1`).  The named
   hypothesis is exactly the **`q^{dim}` vs `dim + 1` obstruction** documented at
   `CZ25SpanDimension.lean:326–333`: the per-coordinate fiber `{c ∈ Lset : c i = f i}`, recentred
   at a base `c₀ ∈ Lset`, is an *affine flat* whose direction lies in
   `A ⊓ ker eval_i = span{c − c₀} ⊓ ker eval_i`, and the charge asserts its *cardinality* is
   `≤ 1 + dim(A ⊓ ker eval_i)` (one base point + the independent directions).  This is **true
   below Johnson** (fibers are singletons/empty, `GWFiberCardCharge_holds_of_singleton`) and is
   the documented **open content past Johnson** (affine flats have `q^{dim} ≫ dim + 1` members).

3. **Verify non-vacuity.**  `GWFiberCardCharge` holds on the sub-Johnson / unique-decoding slice
   (every close list a singleton or empty), so the reduction is *not* vacuous.

So the R2 chain's last leaf is now a **satisfiable, correctly-stated** named obligation whose
remaining content is precisely the one algebraic gap (affine-flat cardinality charge), and the
old `GWAffineFiberCharge` leaf is documented-refuted.

## Honesty note

This file does **not** close the GW kernel.  `GWFiberCardCharge` implies `CZ25CoordFiberCap`,
which (via `cz25SpanBound'_of_coordFiberCap` and the `CZ25SpanBound' ⟺ CZ25DimensionCount`
equivalence) implies the **full capacity list-decoding bound** `|L| ≤ (1 − τ(r₀))/η`.  So
`GWFiberCardCharge` is as deep as the GW capacity theorem itself; it is *not* a tractable
sub-lemma but the irreducible algebraic kernel, here stated correctly (unlike the refuted
`GWAffineFiberCharge`) and reduced to a single per-coordinate inequality.  Outcome: one
leg-statement **refuted** (with countermodel), and the genuine target **re-reduced** to a
satisfiable named obligation.

## References

- [GW13] Guruswami–Wang. *Linear-algebraic list decoding of folded Reed–Solomon codes.*
- [CZ25] Thm B.5 (subspace-design route to capacity list decoding).
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace CodingTheory

open scoped NNReal
open ListDecodable
open Module

section FiberChargeRepair

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ### Refutation: `GWAffineFiberCharge` is false on the empty close list -/

/-- **The empty close list refutes `GWAffineFiberCharge`.** If some received word `f₀` in the
non-degenerate regime `δ := 1 − τ(r₀) − η ≥ 0` has an *empty* close list, then
`GWAffineFiberCharge` fails: its second conjunct `(finrank A : ℝ) ≤ |Lset| − 1` becomes
`(finrank A : ℝ) ≤ −1`, contradicting `finrank A ≥ 0`.  The empty close list is genuinely
reachable (`f₀` far from every codeword), so this is not a degenerate edge but a real
unsatisfiability: the scoped headline consuming `hL : GWAffineFiberCharge` consumes a hypothesis
false for some `f`.  Axiom-clean. -/
theorem gwAffineFiberCharge_false_of_empty_close_list
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (f₀ : ι → Fin s → F)
    (hδ : 0 ≤ 1 - τ (Nat.floor (1 / η)) - η)
    (hempty : closeCodewordsRel ((C : Set (ι → Fin s → F))) f₀
        (1 - τ (Nat.floor (1 / η)) - η) = ∅) :
    ¬ GWAffineFiberCharge s τ C h η hη := by
  intro hCharge
  obtain ⟨A, _hcap, hdim⟩ := hCharge f₀ hδ
  have hcard0 : (closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f₀
      (1 - τ (Nat.floor (1 / η)) - η)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro c hc
    rw [mem_closeCodewordsRelFinset, hempty] at hc
    exact absurd hc (by simp)
  rw [hcard0] at hdim
  have hnonneg : (0 : ℝ) ≤ (Module.finrank F A : ℝ) := Nat.cast_nonneg _
  simp only [Nat.cast_zero] at hdim
  linarith

/-! ### The recentred-span dimension bound (`dim A ≤ |Lset| − 1`) -/

/-- **Recentred span dimension is below `|Lset| − 1`.** For any base `c₀ ∈ Lset`, the recentred
span `A := span{c − c₀ : c ∈ Lset}` has `finrank A + 1 ≤ |Lset|` (so `finrank A ≤ |Lset| − 1`).
The image `(· − c₀) '' Lset` has at most `|Lset|` members, one of which is `0 = c₀ − c₀`, and
`span (s \ {0}) = span s`, so the span is generated by at most `|Lset| − 1` vectors.  This is the
`dim A ≤ |Lset| − 1` charge the assembly needs (in `ℕ` form so it is correct even when the list
is empty/singleton).  Axiom-clean. -/
theorem finrank_recentred_span_le
    (s : ℕ) (c₀ : ι → Fin s → F) (Lset : Finset (ι → Fin s → F))
    (hc₀ : c₀ ∈ Lset) :
    Module.finrank F
        (Submodule.span F ((fun c => c - c₀) '' (Lset : Set (ι → Fin s → F)))) + 1
      ≤ Lset.card := by
  classical
  set img : Finset (ι → Fin s → F) := Lset.image (fun c => c - c₀) with himg
  have hspan_eq : Submodule.span F ((fun c => c - c₀) '' (Lset : Set (ι → Fin s → F)))
      = Submodule.span F (img : Set (ι → Fin s → F)) := by
    rw [himg, Finset.coe_image]
  have hzero : (0 : ι → Fin s → F) ∈ img := by
    rw [himg, Finset.mem_image]; exact ⟨c₀, hc₀, sub_self c₀⟩
  have herase : Submodule.span F ((img.erase 0 : Finset (ι → Fin s → F)) :
        Set (ι → Fin s → F))
      = Submodule.span F (img : Set (ι → Fin s → F)) := by
    have hco : ((img.erase 0 : Finset (ι → Fin s → F)) : Set (ι → Fin s → F))
        = (img : Set (ι → Fin s → F)) \ {0} := by rw [Finset.coe_erase]
    rw [hco, Submodule.span_sdiff_singleton_zero]
  have hfin : Module.finrank F
      (Submodule.span F ((img.erase 0 : Finset (ι → Fin s → F)) :
        Set (ι → Fin s → F)))
      ≤ (img.erase 0).card := by
    have hh := finrank_span_finset_le_card (R := F) (img.erase 0)
    rwa [Set.finrank] at hh
  have himg_pos : 1 ≤ img.card := Finset.card_pos.mpr ⟨0, hzero⟩
  have hcard_erase : (img.erase 0).card + 1 ≤ img.card := by
    rw [Finset.card_erase_of_mem hzero]; omega
  have himg_le : img.card ≤ Lset.card := by rw [himg]; exact Finset.card_image_le
  calc Module.finrank F
        (Submodule.span F ((fun c => c - c₀) '' (Lset : Set (ι → Fin s → F)))) + 1
      = Module.finrank F
          (Submodule.span F ((img.erase 0 : Finset (ι → Fin s → F)) :
            Set (ι → Fin s → F))) + 1 := by rw [hspan_eq, ← herase]
    _ ≤ (img.erase 0).card + 1 := Nat.add_le_add_right hfin 1
    _ ≤ img.card := hcard_erase
    _ ≤ Lset.card := himg_le

/-! ### The genuine per-coordinate affine-flat charge (the corrected BRICK-L leaf) -/

/-- **BRICK-L, correctly stated: the per-coordinate affine-flat cardinality charge.**

For each received word `f` in the non-degenerate regime, EITHER the close list is empty, OR there
is a *base* close codeword `c₀ ∈ closeCodewordsRel C f δ` such that for **every** coordinate `i`,
the agreement fiber `{c ∈ Lset : c i = f i}` has cardinality at most `1 + dim(A ⊓ ker eval_i)`,
where `A := span{c − c₀ : c ∈ Lset}` is the recentred span and `Lset` is the canonical close
finset.

The `+1` is the affine base point; `dim(A ⊓ ker eval_i)` is the direction space of the fiber's
affine flat.  This is the **exact** content that the in-tree obstruction
(`CZ25SpanDimension.lean:326–333`) flags as having no shortcut: past Johnson the fiber is a full
affine flat of size `q^{dim}`, so the cardinality charge `#fiber ≤ 1 + dim` is the genuine deep
inequality (true below Johnson, where fibers collapse to base points).  Unlike the refuted
`GWAffineFiberCharge`, it handles the empty list cleanly (left disjunct) and never asserts the
spurious `finrank ≤ |Lset| − 1` as a real inequality. -/
def GWFiberCardCharge
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C) (η : ℝ) (_hη : 0 < η) : Prop :=
  ∀ f : ι → Fin s → F,
    0 ≤ 1 - τ (Nat.floor (1 / η)) - η →
    closeCodewordsRel ((C : Set (ι → Fin s → F))) f
        (1 - τ (Nat.floor (1 / η)) - η) = ∅ ∨
    ∃ c₀ ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f
        (1 - τ (Nat.floor (1 / η)) - η),
      -- BRICK-W dimension bound on the recentred span (the GW solution-flat dimension):
      Module.finrank F
          (Submodule.span F ((fun c => c - c₀) ''
            ((closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f
              (1 - τ (Nat.floor (1 / η)) - η)) : Set (ι → Fin s → F)))) ≤
        Nat.floor (1 / η) ∧
      ∀ i : ι,
        ((closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f
            (1 - τ (Nat.floor (1 / η)) - η)).filter (fun c => c i = f i)).card ≤
          1 + Module.finrank F
            (↥((Submodule.span F ((fun c => c - c₀) ''
                  ((closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f
                    (1 - τ (Nat.floor (1 / η)) - η)) : Set (ι → Fin s → F)))) ⊓
              (LinearMap.ker
                (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
              Submodule F (ι → Fin s → F)))

/-! ### The reduction: `GWFiberCardCharge` ⟹ `CZ25CoordFiberCap` -/

/-- **Repaired reduction: the genuine per-coordinate affine-flat charge implies the cap.**

`GWFiberCardCharge` (correctly stated, satisfiable) plus the design profile bounds
`0 ≤ τ(r₀) ≤ 1` yields the in-tree target `CZ25CoordFiberCap`.  The composition:

* **Empty close list** → `coordAgreeSum = 0 ≤ (1 − τ(r₀))·n = ((0 − 1)·τ(r₀) + 1)·n` (uses
  `τ(r₀) ≤ 1`), with the witness finset realised directly.
* **Nonempty** → recentre at the base `c₀ ∈ Lset`, set `A := span{c − c₀ : c ∈ Lset}`.  Each
  per-coordinate fiber charge gives `#fiber_i ≤ 1 + dim(A ⊓ ker eval_i)`; summing,
  `coordAgreeSum ≤ n + ∑_i dim(A ⊓ ker eval_i)`.  The **proven** subspace-design budget
  (`IsSubspaceDesign` on `A`, at `r₀`, using the BRICK-W bound `finrank A ≤ r₀`) caps
  `∑_i dim(A ⊓ ker eval_i) ≤ finrank A · τ(r₀) · n`, and the dimension bound
  `finrank_recentred_span_le` gives `finrank A ≤ |Lset| − 1`.  Monotonicity in the `finrank A`
  slot (`τ(r₀) ≥ 0`) collapses to `((|Lset| − 1)·τ(r₀) + 1)·n = CZ25CoordFiberCap`.

Reuses only the proven design half and the new dimension bound; no `sorry`, no new axioms.  The
sole non-bookkeeping input is the named affine-flat charge `GWFiberCardCharge` — the documented
`q^{dim}` vs `dim + 1` obstruction. -/
theorem cz25CoordFiberCap_of_fiberCardCharge
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hτ0 : 0 ≤ τ (Nat.floor (1 / η))) (hτ1 : τ (Nat.floor (1 / η)) ≤ 1)
    (hCharge : GWFiberCardCharge s τ C h η hη) :
    CZ25CoordFiberCap s τ C h η hη := by
  classical
  intro f hδ
  set r₀ : ℕ := Nat.floor (1 / η) with hr₀
  set δ : ℝ := 1 - τ r₀ - η with hδdef
  set Lset : Finset (ι → Fin s → F) :=
    closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f δ with hLset
  refine ⟨Lset, fun c => mem_closeCodewordsRelFinset, ?_⟩
  have hn_nonneg : (0 : ℝ) ≤ Fintype.card ι := by positivity
  have hn_natR : ((Fintype.card ι : ℕ) : ℝ) = (Fintype.card ι : ℝ) := by norm_num
  rcases hCharge f hδ with hempty | ⟨c₀, hc₀, hrank, hfiber⟩
  · -- Empty close list: `coordAgreeSum = 0`, cap reduces to `0 ≤ (1 − τ(r₀))·n`.
    have hLempty : Lset = ∅ := by
      rw [hLset, Finset.eq_empty_iff_forall_notMem]
      intro c hc
      rw [mem_closeCodewordsRelFinset, hempty] at hc
      exact absurd hc (by simp)
    have hsum0 : coordAgreeSum s f Lset = 0 := by
      rw [coordAgreeSum, hLempty]; simp
    rw [hsum0]
    have hcard0 : (Lset.card : ℝ) = 0 := by rw [hLempty]; simp
    rw [hcard0]
    -- RHS = ((0 − 1)·τ(r₀) + 1)·n = (1 − τ(r₀))·n ≥ 0.
    have : (((0 : ℝ) - 1) * τ r₀ + 1) * Fintype.card ι = (1 - τ r₀) * Fintype.card ι := by ring
    rw [this]
    apply mul_nonneg _ hn_nonneg
    linarith
  · -- Nonempty: the affine-flat charge + design budget + dimension bound.
    set A : Submodule F (ι → Fin s → F) :=
      Submodule.span F ((fun c => c - c₀) '' (Lset : Set (ι → Fin s → F))) with hA
    -- `c₀ ∈ Lset` and `A ≤ C`.
    have hc₀L : c₀ ∈ Lset := by rw [hLset, mem_closeCodewordsRelFinset]; exact hc₀
    have hL_close : ∀ c ∈ Lset, c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ := by
      intro c hc; rw [hLset, mem_closeCodewordsRelFinset] at hc; exact hc
    -- The design budget on `A` at `r₀` (BRICK-W bound `finrank A ≤ r₀`).
    have hA_le : A ≤ C :=
      span_diffs_le_of_subset_closeCodewordsRel s C f c₀ Lset hc₀ hL_close
    have hrankR : Module.finrank F A ≤ r₀ := by rw [hA]; exact hrank
    have hdesign := h r₀ A hA_le hrankR
    have hn_posR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    rw [div_le_iff₀ hn_posR] at hdesign
    -- `∑_i dim(A ⊓ ker_i) ≤ finrank A · τ(r₀) · n`.
    have hbudget :
        (∑ i : ι,
          (Module.finrank F (↥(A ⊓
            (LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
            Submodule F (ι → Fin s → F))) : ℝ)) ≤
          (Module.finrank F A : ℝ) * τ r₀ * Fintype.card ι := hdesign
    -- Per-coordinate fiber charge, summed: `coordAgreeSum ≤ ∑_i (1 + dim(A ⊓ ker_i))`.
    have hfiberR : ∀ i : ι,
        ((Lset.filter (fun c => c i = f i)).card : ℝ) ≤
          1 + (Module.finrank F (↥(A ⊓
            (LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
            Submodule F (ι → Fin s → F))) : ℝ) := by
      intro i
      have hnat := hfiber i
      have hcast : (((Lset.filter (fun c => c i = f i)).card : ℕ) : ℝ) ≤
          ((1 + Module.finrank F (↥(A ⊓
            (LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
            Submodule F (ι → Fin s → F))) : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast at hcast
      exact hcast
    have hsum_charge : coordAgreeSum s f Lset ≤
        ∑ i : ι, (1 + (Module.finrank F (↥(A ⊓
          (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F))) : ℝ)) := by
      rw [coordAgreeSum]
      exact Finset.sum_le_sum (fun i _ => hfiberR i)
    -- `∑_i (1 + dim) = n + ∑_i dim`.
    have hsplit :
        (∑ i : ι, (1 + (Module.finrank F (↥(A ⊓
          (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F))) : ℝ))) =
        (Fintype.card ι : ℝ) +
          ∑ i : ι, (Module.finrank F (↥(A ⊓
            (LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
            Submodule F (ι → Fin s → F))) : ℝ) := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_const, Finset.card_univ]
      simp
    -- `finrank A ≤ |Lset| − 1`.
    have hdim_le : (Module.finrank F A : ℝ) ≤ (Lset.card : ℝ) - 1 := by
      have hnat := finrank_recentred_span_le s c₀ Lset hc₀L
      rw [← hA] at hnat
      have : (Module.finrank F A : ℝ) + 1 ≤ (Lset.card : ℝ) := by exact_mod_cast hnat
      linarith
    -- Chain the inequalities.
    have hchain : coordAgreeSum s f Lset ≤
        (Fintype.card ι : ℝ) + (Module.finrank F A : ℝ) * τ r₀ * Fintype.card ι := by
      have hstep1 : coordAgreeSum s f Lset ≤
          (Fintype.card ι : ℝ) +
            ∑ i : ι, (Module.finrank F (↥(A ⊓
              (LinearMap.ker
                (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
              Submodule F (ι → Fin s → F))) : ℝ) := by
        rw [← hsplit]; exact hsum_charge
      linarith [hstep1, hbudget]
    -- Final monotonicity collapse to `((|Lset| − 1)·τ(r₀) + 1)·n`.
    have hfinal : (Fintype.card ι : ℝ) +
        (Module.finrank F A : ℝ) * τ r₀ * Fintype.card ι ≤
        (((Lset.card : ℝ) - 1) * τ r₀ + 1) * Fintype.card ι := by
      have hmono : (Module.finrank F A : ℝ) * τ r₀ ≤ ((Lset.card : ℝ) - 1) * τ r₀ :=
        mul_le_mul_of_nonneg_right hdim_le hτ0
      nlinarith [hmono, hn_nonneg]
    exact le_trans hchain hfinal

/-! ### Non-vacuity: `GWFiberCardCharge` holds on the sub-Johnson / unique-decoding slice -/

/-- **`GWFiberCardCharge` is satisfiable (sub-Johnson slice).** If for every received word the
close list at the capacity radius is a singleton or empty (the unique-decoding / sub-Johnson
regime), then `GWFiberCardCharge` holds: take the singleton base `c₀`, whose recentred span is
`⊥` (the only member maps to `0`), and each fiber `{c ∈ {c₀} : c i = f i}` has cardinality `≤ 1 ≤
1 + dim(⊥ ⊓ ker eval_i)`.  This certifies the reduction `cz25CoordFiberCap_of_fiberCardCharge` is
**not vacuous** — its hypothesis is genuinely inhabited (and is exactly where the GW kernel is
unconditional), the deep content living only past Johnson.  Axiom-clean. -/
theorem gwFiberCardCharge_holds_of_close_list_subsingleton
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hsub : ∀ f : ι → Fin s → F,
      (closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η)).Subsingleton) :
    GWFiberCardCharge s τ C h η hη := by
  classical
  intro f hδ
  set δ : ℝ := 1 - τ (Nat.floor (1 / η)) - η with hδdef
  by_cases hne : (closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ) = ∅
  · exact Or.inl hne
  · -- Nonempty + subsingleton ⟹ a unique base codeword `c₀`.
    obtain ⟨c₀, hc₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
    refine Or.inr ⟨c₀, hc₀, ?_, ?_⟩
    · -- The close finset is `{c₀}`, recentred span `⊥`, finrank `0 ≤ r₀`.
      exact Nat.zero_le _ |>.trans' (by
        have : Module.finrank F
            (Submodule.span F ((fun c => c - c₀) ''
              ((closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f δ) :
                Set (ι → Fin s → F)))) = 0 := by
          have hsingle : ∀ c ∈ closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f δ,
              c = c₀ := by
            intro c hc
            rw [mem_closeCodewordsRelFinset] at hc
            exact hsub f hc hc₀
          have himg0 : ((fun c => c - c₀) ''
              ((closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f δ) :
                Set (ι → Fin s → F))) ⊆ {0} := by
            rintro x ⟨c, hc, rfl⟩
            rw [Finset.mem_coe] at hc
            simp only [Set.mem_singleton_iff]
            rw [hsingle c hc, sub_self]
          have : Submodule.span F ((fun c => c - c₀) ''
              ((closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f δ) :
                Set (ι → Fin s → F))) ≤ Submodule.span F ({0} : Set (ι → Fin s → F)) :=
            Submodule.span_mono himg0
          rw [Submodule.span_singleton_eq_bot.mpr rfl] at this
          rw [le_bot_iff.mp this, finrank_bot]
        omega)
    · intro i
      -- The fiber `{c ∈ {c₀} : c i = f i}` has card ≤ 1.
      have hcard_le_one :
          (closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f δ).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        rw [mem_closeCodewordsRelFinset] at ha hb
        exact hsub f ha hb
      have hfilter_le :
          ((closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f δ).filter
            (fun c => c i = f i)).card ≤
            (closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f δ).card :=
        Finset.card_filter_le _ _
      omega

end FiberChargeRepair

/-! ### Concrete satisfiable countermodel: `GWAffineFiberCharge` is genuinely refuted

To certify the empty-list refutation is **not vacuous**, we exhibit a real instance — the trivial
code `⊥` over `ZMod 2`, block length `n = 1`, profile `τ ≡ 0`, `η = 1` (so the regime guard
`δ = 1 − τ(r₀) − η = 0 ≥ 0` holds) — and a received word `f₀ = 1 ≠ 0` whose close list is empty
(the only codeword of `⊥` is `0`, at relative distance `1 > 0 = δ`).  By
`gwAffineFiberCharge_false_of_empty_close_list`, `GWAffineFiberCharge` is **false** on this fully
concrete satisfiable instance. -/

section Countermodel

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- **`⊥` is a subspace design for any profile.** Every submodule of `⊥` is `⊥` (finrank `0`), so
the design budget `0 ≤ 0` holds trivially. -/
private theorem isSubspaceDesign_bot (s : ℕ) (τ : ℕ → ℝ) :
    IsSubspaceDesign (ι := Fin 1) (F := ZMod 2) s τ ⊥ := by
  intro r A hA hrank
  have hAbot : A = ⊥ := le_bot_iff.mp hA
  subst hAbot
  simp

/-- **`GWAffineFiberCharge` is REFUTED on a concrete satisfiable instance.** The trivial code `⊥`
over `ZMod 2`, `n = s = 1`, `τ ≡ 0`, `η = 1`: the regime guard holds (`δ = 0 ≥ 0`), yet the
received word `f₀ = 1` has an empty close list, so the affine-flat charge's `finrank ≤ |Lset| − 1`
conjunct is unsatisfiable.  Hence `GWAffineFiberCharge` fails for this genuine subspace design —
the refutation `gwAffineFiberCharge_false_of_empty_close_list` is not vacuous. Axiom-clean. -/
theorem gwAffineFiberCharge_refuted_concrete :
    ¬ GWAffineFiberCharge (ι := Fin 1) (F := ZMod 2) 1 (fun _ => 0) ⊥
        (isSubspaceDesign_bot 1 (fun _ => 0)) 1 one_pos := by
  classical
  -- The received word `f₀ = 1` (all-ones), distinct from the unique codeword `0`.
  set f₀ : Fin 1 → Fin 1 → ZMod 2 := fun _ _ => 1 with hf₀
  -- The regime guard `δ = 1 − τ(⌊1/1⌋) − 1 = 0 ≥ 0`.
  have hδ : (0 : ℝ) ≤ 1 - (fun _ : ℕ => (0:ℝ)) (Nat.floor (1 / (1:ℝ))) - 1 := by norm_num
  -- The close list of `⊥` around `f₀` at radius `0` is empty.
  have hempty : closeCodewordsRel
      ((⊥ : Submodule (ZMod 2) (Fin 1 → Fin 1 → ZMod 2)) :
        Set (Fin 1 → Fin 1 → ZMod 2)) f₀
      (1 - (fun _ : ℕ => (0:ℝ)) (Nat.floor (1 / (1:ℝ))) - 1) = ∅ := by
    have hrw : (1 - (fun _ : ℕ => (0:ℝ)) (Nat.floor (1 / (1:ℝ))) - 1) = (0 : ℝ) := by norm_num
    rw [hrw]
    rw [Set.eq_empty_iff_forall_notMem]
    intro c hc
    rw [mem_closeCodewordsRel_iff_real] at hc
    obtain ⟨hcmem, hdist⟩ := hc
    have hc0 : c = 0 := by simpa using hcmem
    subst hc0
    have hne : f₀ ≠ (0 : Fin 1 → Fin 1 → ZMod 2) := by
      intro hcontra
      have := congrFun (congrFun hcontra 0) 0
      simp [hf₀] at this
    have hpos : (0 : ℝ) < ((Code.relHammingDist f₀ (0 : Fin 1 → Fin 1 → ZMod 2) : ℚ≥0) : ℝ) := by
      rw [Code.relHammingDist]
      have hcardpos : 0 < Fintype.card (Fin 1) := Fintype.card_pos
      have hhd : hammingDist f₀ (0 : Fin 1 → Fin 1 → ZMod 2) ≠ 0 := by
        rw [hammingDist_ne_zero]; exact hne
      have hhdpos : 0 < hammingDist f₀ (0 : Fin 1 → Fin 1 → ZMod 2) := Nat.pos_of_ne_zero hhd
      positivity
    linarith
  exact gwAffineFiberCharge_false_of_empty_close_list
    1 (fun _ => 0) ⊥ (isSubspaceDesign_bot 1 (fun _ => 0)) 1 one_pos f₀ hδ hempty

end Countermodel

end CodingTheory

#print axioms CodingTheory.gwAffineFiberCharge_refuted_concrete
#print axioms CodingTheory.gwAffineFiberCharge_false_of_empty_close_list
#print axioms CodingTheory.finrank_recentred_span_le
#print axioms CodingTheory.cz25CoordFiberCap_of_fiberCardCharge
#print axioms CodingTheory.gwFiberCardCharge_holds_of_close_list_subsingleton
