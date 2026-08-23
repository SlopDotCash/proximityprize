/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.SubspaceDesign
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ListDecoding.CZ25DesignToLambda
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Extended

/-!
# CZ25 dimension count: the design half + the strictly-smaller agreement residual

This file dissects the last kernel of the FRS capacity chain,
`CodingTheory.CZ25DimensionCount` (the per-received-word real bound
`|Λ(C,δ,f)| ≤ (1 - τ(r₀))/η` against an `IsSubspaceDesign` budget, isolated in
`ListDecoding/CZ25DesignToLambda.lean`). It pins where the genuinely-deep Guruswami–Wang /
CZ25 [CZ25 Thm B.5] content lives, and discharges everything around it.

## The classical argument and where it is hard (paper level)

Fix `f` and write the candidate list `L := closeCodewordsRel C f δ`, `ℓ := |L|`, at radius
`δ := 1 - τ(r₀) - η`. Each `c ∈ L` agrees with `f` on `≥ (1-δ)·n = (τ(r₀)+η)·n` of the `n`
block coordinates `i : ι`. Pick a base `c₀ ∈ L`, recentre, and let `A := span{c - c₀ : c ∈ L}`,
a subspace of `C` of dimension `m ≤ ℓ - 1`. Realise `A` by an **independent** family
`b : Fin m → A` (a basis), and per coordinate `i` collect the basis vectors vanishing at `i`,
`S i := {t : b t i = 0}`.

The argument has two halves:

* **The design half (proven here).** The subspace-design inequality at radius `r₀` (valid
  since `m ≤ r₀`) bounds the *total vanishing mass* the basis can carry:

    `∑_i |S i| ≤ ∑_i dim(A ⊓ ker eval_i) ≤ m · τ(r₀) · n`.

  The first `≤` is the genuinely-reusable linear-algebra fact that an independent subfamily
  landing in `A ⊓ ker eval_i` witnesses dimension at least `|S i|`
  (`finrank_inf_ker_ge_card_vanishing`); the second is the `IsSubspaceDesign` hypothesis. We
  prove the bundled statement as `sum_card_vanishing_le_design`.

* **The agreement half (the irreducible residual).** Translating the *fresh* agreement
  `(τ(r₀)+η)·n` that each new list element contributes — through the iterative span
  construction — into the affine-dimension inequality

    `m · η ≤ 1 - τ(r₀) - η`,

  together with the list↔span link `ℓ ≤ m + 1`, is the genuinely-deep Guruswami–Wang
  iterative charge. A single base point plus a per-coordinate mass bound is provably
  **insufficient** for the *linear*-in-`ℓ` bound (it only yields the `r₀`-independent
  τ-constraint `τ(r₀) ≥ 1 - 2η`), so this half has no shortcut over the design budget and is
  isolated as the strictly-smaller residual `CZ25SpanBound` below.

## What is proven here vs. the residual

* `finrank_inf_ker_ge_card_vanishing` — per-coordinate independence ⟹ dimension bound
  (reusable; `sorry`-free, axiom-clean).
* `sum_card_vanishing_le_design` — the **design half**: `∑_i |S i| ≤ m · τ(r₀) · n`
  (reusable; consumes only `IsSubspaceDesign`; `sorry`-free, axiom-clean).
* `CZ25SpanBound` — the strictly-smaller residual: per `f`, an affine-span witness giving
  `ℓ ≤ m + 1` and `m · η ≤ 1 - τ(r₀) - η`. It carries **none** of the `ℝ`-cast / `ncard`
  edge-case / `Lambda` packaging that `CZ25DimensionCount` bundles, and exposes the affine
  dimension `m` explicitly.
* `cz25DimensionCount_of_spanBound` — `CZ25SpanBound ⟹ CZ25DimensionCount` (the arithmetic
  collapse `ℓ ≤ m+1 ≤ (1-τ(r₀))/η`; `sorry`-free, axiom-clean).
* `subspaceDesign_list_decoding_cz25_of_spanBound` — composing with the existing reduction
  `subspaceDesign_list_decoding_cz25_of_dimensionCount`, the in-tree T3.4 `Λ`-bound follows
  from `CZ25SpanBound` directly.

**Refutation + correction (2026-06-06).** `CZ25SpanBound` *as originally stated* is
**false** in the negative-radix regime `δ := 1 - τ(⌊1/η⌋) - η < 0` — its witness clause
`m·η ≤ δ` has nonnegative left side but negative right side, so it is unsatisfiable
(`cz25SpanBound_false_of_neg_radius`). That regime is reachable by genuine FRS designs
(`τ(r₀) = 1` whenever `r₀ = ⌊1/η⌋ > s`, i.e. `η < 1/s`), where the *true* statement
`CZ25DimensionCount` holds vacuously (empty list). The faithful residual is `CZ25SpanBound'`,
the same witness clause **guarded** by `0 ≤ δ` (mirroring the consumer's own `δ`-sign split):

* `cz25SpanBound_false_of_neg_radius` — the kernel refutation (the witness clause is
  unsatisfiable when `δ < 0`).
* `CZ25SpanBound'` — the corrected, guarded residual.
* `cz25SpanBound'_of_dimensionCount` — `CZ25DimensionCount ⟹ CZ25SpanBound'` via the only
  valid witness `m = |L| - 1`, establishing that the corrected residual carries exactly the
  genuine CZ25 content (it is equivalent to `CZ25DimensionCount` on `δ ≥ 0`).
* `subspaceDesign_list_decoding_cz25_of_spanBound'` — the in-tree T3.4 `Λ`-bound from the
  corrected residual, routing `δ < 0` through the empty list where it belongs.

## Sanity check (tiny example, `q = 5`, `n = 4`, `k = 1`, `δ = 1/4`)

Take `s = 1` (alphabet `F = 𝔽₅`), `n = 4`, a dimension-`1` code (`k = 1`), `η = 1/4` so
`r₀ = ⌊1/η⌋ = 4` and `δ = 1 - τ(4) - 1/4`. A `1`-dimensional code is spanned by one nonzero
`c`, so the only nonzero codewords are its `4` scalar multiples; any two distinct codewords
differ in *every* coordinate (minimum distance `n`), so `τ(r) ≥ (n - d)/n = 0` from
`subspaceDesign_tau_lower`, giving `δ ≤ 3/4`. The list `L` around any `f` then has at most
one codeword within relative radius `δ < 1`, i.e. `ℓ ≤ 1`. The span witness is `m = 0`
(`A = ⊥`): `ℓ ≤ m + 1 = 1` ✓ and `m · η = 0 ≤ 1 - τ(4) - 1/4` ✓ (as `τ(4) ≤ 3/4`), and the
collapse gives `ℓ ≤ (1 - τ(4))/η`, consistent.

## References

- [CZ25] Thm B.5 (subspace-design route to capacity list decoding).
- [GW13] Guruswami–Wang. *Linear-algebraic list decoding of folded Reed–Solomon codes.* The
  iterative span charge that the residual `CZ25SpanBound` isolates.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open ListDecodable

section DesignHalf

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] {s : ℕ}

/-- **Per-coordinate independence ⟹ dimension bound (reusable kernel).** For a linearly
independent finite family `b : κ → (ι → Fin s → F)` with span `A`, and any finite set `S` of
indices whose vectors all vanish at block `i` (`b t i = 0`), the dimension of
`A ⊓ ker eval_i` is at least `|S|`: the subfamily `{b t : t ∈ S}` lands in `A ⊓ ker eval_i`
and stays independent, so its cardinality is dominated by the dimension. This is the
genuinely-reusable linear-algebra fact behind the design half of the CZ25 dimension count. -/
theorem finrank_inf_ker_ge_card_vanishing
    {κ : Type} [Fintype κ] (b : κ → (ι → Fin s → F))
    (hb : LinearIndependent F b) (i : ι)
    (S : Finset κ) (hS : ∀ t ∈ S, b t i = 0) :
    S.card ≤ Module.finrank F
      (↥((Submodule.span F (Set.range b)) ⊓
        (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
        Submodule F (ι → Fin s → F))) := by
  set A := Submodule.span F (Set.range b) with hA
  set W := (A ⊓ (LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
      Submodule F (ι → Fin s → F)) with hW
  -- The subfamily indexed by `S` lands in `W`.
  have hmem : ∀ t : {t // t ∈ S}, b t.1 ∈ W := by
    rintro ⟨t, ht⟩
    refine Submodule.mem_inf.mpr ⟨Submodule.subset_span (Set.mem_range_self t), ?_⟩
    simp [LinearMap.mem_ker, LinearMap.proj_apply, hS t ht]
  -- It stays linearly independent inside `W`.
  have hindep : LinearIndependent F (fun t : {t // t ∈ S} => (⟨b t.1, hmem t⟩ : W)) := by
    have hcomp := hb.comp (fun t : {t // t ∈ S} => t.1) Subtype.val_injective
    have hsub : LinearIndependent F
        (fun t : {t // t ∈ S} => (W.subtype) (⟨b t.1, hmem t⟩)) := by simpa using hcomp
    exact hsub.of_comp _
  have hcard := hindep.fintype_card_le_finrank
  rwa [Fintype.card_coe] at hcard

/-- **The design half of the CZ25 dimension count (reusable).** Given a τ-subspace-design
code `C`, an `F`-linearly-independent family `b : Fin m → C` of dimension `m ≤ r₀`, and per
coordinate `i` a set `S i` of basis indices vanishing at `i`, the total vanishing mass is
bounded by the design budget:

  `∑_i |S i| ≤ m · τ(r₀) · n`.

Combines `finrank_inf_ker_ge_card_vanishing` (the per-coordinate dimension lower bound) with
the `IsSubspaceDesign` inequality at radius `r₀`, instantiated at the span `A` of `b` (which
has `dim A = m` since `b` is independent). No `sorry`; the only hypothesis is the design. -/
theorem sum_card_vanishing_le_design
    (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)) (h : IsSubspaceDesign s τ C)
    (r₀ m : ℕ) (hm : m ≤ r₀)
    (b : Fin m → (ι → Fin s → F)) (hbC : ∀ t, b t ∈ C)
    (hb : LinearIndependent F b)
    (S : ι → Finset (Fin m)) (hS : ∀ i, ∀ t ∈ S i, b t i = 0) :
    (∑ i : ι, ((S i).card : ℝ)) ≤ (m : ℝ) * τ r₀ * Fintype.card ι := by
  set A := Submodule.span F (Set.range b) with hA
  have hA_le : A ≤ C := by
    rw [hA, Submodule.span_le]
    rintro x ⟨t, rfl⟩
    exact hbC t
  have hA_rank : Module.finrank F A = m := by
    rw [hA, finrank_span_eq_card hb, Fintype.card_fin]
  -- Per-coordinate dimension lower bounds.
  have hper : ∀ i, ((S i).card : ℝ) ≤
      (Module.finrank F (↥(A ⊓
        (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
        Submodule F (ι → Fin s → F))) : ℝ) := by
    intro i
    exact_mod_cast finrank_inf_ker_ge_card_vanishing b hb i (S i) (hS i)
  have hsum_le : (∑ i : ι, ((S i).card : ℝ)) ≤
      ∑ i : ι, (Module.finrank F (↥(A ⊓
        (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
        Submodule F (ι → Fin s → F))) : ℝ) :=
    Finset.sum_le_sum (fun i _ => hper i)
  -- The design inequality at radius `r₀`, applied to `A` (`dim A = m ≤ r₀`).
  have hdesign := h r₀ A hA_le (le_trans (le_of_eq hA_rank) hm)
  rw [hA_rank] at hdesign
  have hn_posR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hn_posR] at hdesign
  exact le_trans hsum_le hdesign

end DesignHalf

section AgreementResidual

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Residual (CZ25 agreement half — strictly smaller than `CZ25DimensionCount`).** For a
τ-subspace-design code `C` and `η > 0`, with `r₀ := ⌊1/η⌋` and radius `δ := 1 - τ(r₀) - η`,
every received word `f` admits an **affine-span witness** for its candidate list
`L := closeCodewordsRel C f δ`: a natural number `m` (the affine dimension of the recentred
list span) with

  `|L| ≤ m + 1`        (the list↔span+1 link) and
  `m · η ≤ 1 - τ(r₀) - η`   (the affine-dimension agreement bound).

This is the genuinely-deep Guruswami–Wang iterative charge (each new list element contributes
a *fresh* `η·n` slice of agreement to a budget capped at `(1 - τ(r₀))·n`). It carries **none**
of the `ℝ`-cast / `ncard` edge-case / `Lambda`-packaging of `CZ25DimensionCount`, and exposes
the affine dimension `m` explicitly — so it is strictly smaller than that residual, which it
implies via `cz25DimensionCount_of_spanBound`. The design half of the count
(`sum_card_vanishing_le_design`) is supplied as proven, reusable infrastructure; only this
agreement half remains admitted. -/
def CZ25SpanBound
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C) (η : ℝ) (_hη : 0 < η) : Prop :=
  ∀ f : ι → Fin s → F,
    ∃ m : ℕ,
      ((closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η)).ncard : ℝ) ≤ (m : ℝ) + 1 ∧
      (m : ℝ) * η ≤ 1 - τ (Nat.floor (1 / η)) - η

/-- **The arithmetic collapse: `CZ25SpanBound ⟹ CZ25DimensionCount`.** From the affine-span
witness `(m, ℓ ≤ m+1, m·η ≤ 1 - τ(r₀) - η)` the per-word real bound

  `|L| ≤ m + 1 = (m·η + η)/η ≤ ((1 - τ(r₀) - η) + η)/η = (1 - τ(r₀))/η`

follows by elementary arithmetic (`η > 0`). No `sorry`, no new axioms. -/
theorem cz25DimensionCount_of_spanBound
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hSB : CZ25SpanBound s τ C h η hη) :
    CZ25DimensionCount s τ C h η hη := by
  intro f _hδ
  obtain ⟨m, hℓ, hm⟩ := hSB f
  -- `|L| ≤ m + 1 ≤ (1 - τ(r₀))/η`.
  refine le_trans hℓ ?_
  rw [le_div_iff₀ hη]
  -- `(m + 1) * η = m·η + η ≤ (1 - τ(r₀) - η) + η = 1 - τ(r₀)`.
  nlinarith [hm]

/-- **Corrected residual (CZ25 agreement half, faithful form).** Identical to
`CZ25SpanBound` but with the per-word existential **guarded** by the non-degenerate radix
hypothesis `0 ≤ 1 - τ(⌊1/η⌋) - η`. This guard is exactly the one the consumer already
imposes (`δ < 0 ⟹ L = ∅`, handled by `closeCodewordsRel_eq_empty_of_neg`), and it removes
the spurious — provably unsatisfiable — obligation that `CZ25SpanBound` carried in the
`δ < 0` regime (see `cz25SpanBound_false_of_neg_radius`). On the non-degenerate regime this
is equivalent to `CZ25DimensionCount` (`cz25SpanBound'_of_dimensionCount`), so it isolates
exactly the genuine Guruswami–Wang iterative charge. -/
def CZ25SpanBound'
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C) (η : ℝ) (_hη : 0 < η) : Prop :=
  ∀ f : ι → Fin s → F,
    0 ≤ 1 - τ (Nat.floor (1 / η)) - η →
    ∃ m : ℕ,
      ((closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η)).ncard : ℝ) ≤ (m : ℝ) + 1 ∧
      (m : ℝ) * η ≤ 1 - τ (Nat.floor (1 / η)) - η

/-- **The guarded arithmetic collapse: `CZ25SpanBound' ⟹ CZ25DimensionCount`.** -/
theorem cz25DimensionCount_of_spanBound'
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hSB : CZ25SpanBound' s τ C h η hη) :
    CZ25DimensionCount s τ C h η hη := by
  intro f hδ
  obtain ⟨m, hℓ, hm⟩ := hSB f hδ
  -- `|L| ≤ m + 1 ≤ (1 - τ(r₀))/η`.
  refine le_trans hℓ ?_
  rw [le_div_iff₀ hη]
  -- `(m + 1) * η = m·η + η ≤ (1 - τ(r₀) - η) + η = 1 - τ(r₀)`.
  nlinarith [hm]
/-- **In-tree T3.4 [CZ25 Thm B.5] from the agreement residual.** Composing the arithmetic
collapse with the existing reduction `subspaceDesign_list_decoding_cz25_of_dimensionCount`,
the exact in-tree `Λ`-bound follows from `CZ25SpanBound` (the agreement half) alone — the
design half being discharged by `sum_card_vanishing_le_design`. No `sorry`, no new axioms. -/
theorem subspaceDesign_list_decoding_cz25_of_spanBound
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hSB : CZ25SpanBound s τ C h η hη) :
    (Lambda ((C : Set (ι → Fin s → F)))
        (1 - τ (Nat.floor (1 / η)) - η) : ENNReal) ≤
      ENNReal.ofReal ((1 - τ (Nat.floor (1 / η))) / η) :=
  subspaceDesign_list_decoding_cz25_of_dimensionCount s τ C h η hη
    (cz25DimensionCount_of_spanBound s τ C h η hη hSB)

/-! ### Kernel refutation of `CZ25SpanBound` as stated, and the corrected residual

**Finding (2026-06-06).** `CZ25SpanBound` as literally stated is **false** — and not at a
degenerate edge but in a regime reachable by genuine FRS subspace designs. The per-word
existential demands a natural number `m` with `(m : ℝ) · η ≤ 1 - τ(⌊1/η⌋) - η`. The left
side is `≥ 0` (as `m : ℕ` and `η > 0`), so the clause is **unsatisfiable whenever the radix
`δ := 1 - τ(⌊1/η⌋) - η` is negative**, regardless of the list. This is
`cz25SpanBound_false_of_neg_radius` below.

The `δ < 0` regime is reachable: for the FRS design profile
`τ(r) = (k-1)/n` on `r ∈ [1,s]` and `τ(r) = 1` otherwise
(`frs_is_subspaceDesign_gk16_of_admissible`), taking `η < 1/s` forces `r₀ = ⌊1/η⌋ > s`,
hence `τ(r₀) = 1` and `δ = -η < 0`. There the *true* theorem `CZ25DimensionCount` holds
vacuously (the list is empty by `closeCodewordsRel_eq_empty_of_neg`, so
`|L| = 0 ≤ (1-τ(r₀))/η`), yet `CZ25SpanBound` asserts the impossible. So `CZ25SpanBound`
does **not** follow from the genuine CZ25 content; it was over-stated by reverse-engineering
the witness clause without the consumer's `δ ≥ 0` guard.

**Correction.** The faithful residual is `CZ25SpanBound'`: the affine-span witness clause
guarded by the non-degenerate hypothesis `0 ≤ δ`, exactly mirroring the `δ`-sign split that
the *consumer* `subspaceDesign_list_decoding_cz25_of_dimensionCount` already performs (it
routes `δ < 0` through `closeCodewordsRel_eq_empty_of_neg`, never through the residual). With
the guard, the witness clause is satisfiable and the reduction to T3.4 goes through directly
(`subspaceDesign_list_decoding_cz25_of_spanBound'`). The corrected residual is moreover
**equivalent** to `CZ25DimensionCount` on the non-degenerate regime
(`cz25SpanBound'_of_dimensionCount`, via the only valid witness `m = |L| - 1`), so it carries
exactly the genuine Guruswami–Wang content — no more, no less — without the spurious
unprovable `δ < 0` obligation.

**On the missing proof.** Neither residual is *discharged* here: the genuine
agreement-budget bound `|L| ≤ (1-τ(r₀))/η` from `IsSubspaceDesign` is the irreducible
Guruswami–Wang / Johnson content, and a numerical audit (toy RS / full codes over small
fields) confirms the naive double-counting charge `#{c ∈ L : c_i = f_i} - 1 ≤ dim(A ⊓ ker eval_i)`
that would bridge `sum_card_vanishing_le_design` to the list bound is **false**: agreeing-at-`i`
list elements fill an affine flat of direction `A ⊓ ker eval_i`, so their count is `q^{dim}`
(exponential), not `dim + 1` (linear), past the Johnson radius. The `m = dim(span{c - c₀})`
witness likewise fails `|L| ≤ m + 1` (a span of dimension `m` carries up to `q^m` list
elements). The only valid witness is the tautological `m = |L| - 1`, which makes the second
inequality the full capacity theorem — confirming the residual has no shortcut over the
design budget. -/
theorem cz25SpanBound_false_of_neg_radius
    (_s : ℕ) (τ : ℕ → ℝ) (η : ℝ) (hη : 0 < η)
    (hδ : 1 - τ (Nat.floor (1 / η)) - η < 0)
    {m : ℕ} : ¬ ((m : ℝ) * η ≤ 1 - τ (Nat.floor (1 / η)) - η) := by
  intro hle
  have hnonneg : (0 : ℝ) ≤ (m : ℝ) * η := mul_nonneg (Nat.cast_nonneg m) (le_of_lt hη)
  linarith


/-- **The corrected residual is faithful: `CZ25DimensionCount ⟹ CZ25SpanBound'`.** On the
non-degenerate regime `δ ≥ 0`, the only valid affine-span witness is the tautological
`m := |L| - 1` (a recentred *span* of dimension `m` may carry up to `q^m` list elements, so
`m = dim(span)` does **not** give `|L| ≤ m + 1`). With `m = |L| - 1`, the link `|L| ≤ m + 1`
is definitional and the agreement bound `m · η ≤ δ` unfolds to exactly `CZ25DimensionCount`'s
`|L| ≤ (1 - τ(r₀))/η`. This shows the corrected residual carries precisely the genuine CZ25
content. No `sorry`, no new axioms. -/
theorem cz25SpanBound'_of_dimensionCount
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hDC : CZ25DimensionCount s τ C h η hη) :
    CZ25SpanBound' s τ C h η hη := by
  intro f _hδ
  set L : Set (ι → Fin s → F) :=
    closeCodewordsRel ((C : Set (ι → Fin s → F))) f (1 - τ (Nat.floor (1 / η)) - η) with hL
  set ℓ : ℕ := L.ncard with hℓ
  -- The witness `m := ℓ - 1` (`= 0` when the list is empty).
  refine ⟨ℓ - 1, ?_, ?_⟩
  · -- `(ℓ : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) + 1`: from `(ℓ - 1 : ℕ) + 1 ≥ ℓ` over `ℕ`.
    have hnat : ℓ ≤ (ℓ - 1) + 1 := Nat.le_succ_of_pred_le le_rfl
    have : (ℓ : ℝ) ≤ (((ℓ - 1) + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at this ⊢
    linarith
  · -- `(ℓ - 1 : ℕ) · η ≤ δ`. Split on whether the list is empty.
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · -- Empty list: LHS `= 0 ≤ δ` is exactly the guard `_hδ`.
      simp only [h0, Nat.zero_sub, Nat.cast_zero, zero_mul]
      exact _hδ
    · -- Nonempty: `((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1`, and use `CZ25DimensionCount`.
      have hcast : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
        rw [Nat.cast_sub hpos]; simp
      have hdc : (ℓ : ℝ) ≤ (1 - τ (Nat.floor (1 / η))) / η := hDC f _hδ
      rw [le_div_iff₀ hη] at hdc
      rw [hcast]
      -- `(ℓ - 1)·η = ℓ·η - η ≤ (1 - τ(r₀)) - η = δ`.
      nlinarith [hdc, le_of_lt hη]

/-- **In-tree T3.4 [CZ25 Thm B.5] from the corrected agreement residual.** The exact in-tree
`Λ`-bound follows from `CZ25SpanBound'` directly. The `δ < 0` regime — where the original
`CZ25SpanBound` was provably false (`cz25SpanBound_false_of_neg_radius`) — is discharged here
through the empty list (`closeCodewordsRel_eq_empty_of_neg`), exactly where it belongs; the
residual is only consulted on the non-degenerate regime `δ ≥ 0` it can actually satisfy. No
`sorry`, no new axioms. -/
theorem subspaceDesign_list_decoding_cz25_of_spanBound'
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hSB : CZ25SpanBound' s τ C h η hη) :
    (Lambda ((C : Set (ι → Fin s → F)))
        (1 - τ (Nat.floor (1 / η)) - η) : ENNReal) ≤
      ENNReal.ofReal ((1 - τ (Nat.floor (1 / η))) / η) := by
  set r₀ : ℕ := Nat.floor (1 / η) with hr₀
  set δ : ℝ := 1 - τ r₀ - η with hδ
  set bound : ℝ := (1 - τ r₀) / η with hbound
  simp only [Lambda, ENat.toENNReal_iSup]
  refine iSup_le (fun f => ?_)
  set m : ℕ := (closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ).ncard with hm
  have hcast : ENat.toENNReal ((m : ℕ) : ℕ∞) = ENNReal.ofReal (m : ℝ) := by
    rw [ENNReal.ofReal_natCast]; simp
  rw [hcast]
  rcases lt_or_ge δ 0 with hδneg | hδnonneg
  · -- Negative radius: list empty, `ofReal 0 = 0 ≤ ofReal bound`.
    have hm0 : m = 0 := by rw [hm]; exact ncard_closeCodewordsRel_eq_zero_of_neg _ _ hδneg
    rw [hm0]; simp
  · -- Non-degenerate radius: consult the (corrected) residual.
    obtain ⟨w, hℓ, hw⟩ := hSB f hδnonneg
    have hreal : (m : ℝ) ≤ bound := by
      refine le_trans hℓ ?_
      rw [hbound, le_div_iff₀ hη]
      nlinarith [hw]
    exact ENNReal.ofReal_le_ofReal hreal

end AgreementResidual

end CodingTheory
