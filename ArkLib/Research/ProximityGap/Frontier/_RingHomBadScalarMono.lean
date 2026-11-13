/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Ring-homomorphism merge-only monotonicity plus the saturation escape hatch (#407)

This Frontier file records the **characteristic-free** half of the window
characteristic-faithfulness lever for the Ethereum Proximity Prize (issue #407):
the finite-scalar merge-only direction, plus the exact place where it does **not**
control total incidence.

## The mathematical content

At the boundary band the deployed object is, per genuine direction `(a,b)`, the
set of **bad scalars**
`γ_T = − h_{a−k}(ζ^T) / h_{b−k}(ζ^T)`,
a ratio of complete-homogeneous (Schur) values living in `Frac(ℤ[ζ_n])`, indexed
by the `T`'s ranging over a fixed finite index set `ι`.

Reducing `ℤ[ζ_n] → 𝔽_q` is a **ring homomorphism** `φ` (it sends `0 ↦ 0`). The
char-`p` bad-scalar value at a `T` is `φ(num T) · φ(den T)⁻¹`, and it is only
*eligible* as a finite scalar where `φ(den T) ≠ 0`.
Hence the **finite-scalar** char-`p` set is the image of a subset of the char-0
data: on that finite branch, reduction can only

* **merge** distinct `T`'s onto the same char-`p` scalar (a collision), or
* **drop out of the finite-scalar branch** when a denominator vanishes mod `q`,

and it can **never create a new finite scalar**. Cardinality of an image is at
most the cardinality of the (eligible subset of the) source, so

> **finite scalar count** `≤ N(char-0)` — characteristic-free, scale-independent.

This does **not** imply the total incidence count is monotone.  In the Schur-ratio
consumer, a vanished denominator can mean the corresponding line is bad for every
scalar (saturation), contributing the whole field rather than deleting one finite
ratio.  The reusable split is therefore:

* finite branch: image of eligible ratios, merge-only;
* saturation branch: if any saturating index exists, the realized bad-scalar set is
  `univ`.

No theorem in this file claims that char-`p` never promotes a good band.

## What this file proves (axiom-clean)

1. `card_image_le_index` — the bare Finset core: any per-index value map's image
   has card ≤ the index count.
2. `card_eligible_image_le_card_eligible` / `..._le_index` — with an eligibility
   predicate (denominator-nonvanishing), the char-`p` distinct-scalar count is at
   most the number of eligible indices, hence at most the total index count.
3. `ringHom_badScalar_card_le` — the **ring-hom specialization**: with `num den :
   ι → R`, `φ : R →+* S`, eligibility `φ (den t) ≠ 0`, the distinct char-`p`
   bad-scalar count `#{ φ(num t)·φ(den t)⁻¹ }` is at most `#ι`.
4. `badScalar_charP_card_le_charZero` — **finite-scalar merge-only monotonicity**:
   when the char-`p` value *factors through* the char-0 value (a `red : K → S`
   with `charP t = red (charZero t)` on eligible `t` — i.e. *no SPLIT*: equal
   char-0 values force equal char-`p` values), the char-`p` distinct-scalar count
   on the eligible finite branch is `≤` the char-0 distinct-scalar count.
5. `saturatedBadScalarSet_eq_univ_of_saturation` — the missing escape hatch:
   once a saturating denominator index exists, the total bad-scalar set is the
   entire field.

Tier 4 is the reusable brick the synthesis calls for; tiers 1–3 are the bare
mechanism it is assembled from. The wiring to the concrete `h_j` Schur ratios on
`μ_n` is described in `wiringNote` below; it must supply both the finite-ratio
factorization and a separate saturation predicate.
-/

namespace ProximityGap.Frontier.RingHomBadScalarMono

open Finset

/-! ## Tier 1 — the bare Finset image core (merge-only) -/

/--
**Merge-only core.** The set of char-`p` scalar values realized over an index
finset `T` is the image of `T` under the value map `v`, so its cardinality is at
most `#T`. Distinct indices that collide onto the same scalar are *merged*; the
count can only drop.
-/
theorem card_image_le_index {ι S : Type*} [DecidableEq S]
    (T : Finset ι) (v : ι → S) :
    (T.image v).card ≤ T.card :=
  Finset.card_image_le

/-! ## Tier 2 — eligibility filter (delete-only) on top of merge-only -/

/--
**Finite-branch drop + merge.** With an eligibility predicate `elig` (think:
`φ(denominator) ≠ 0`), the realized char-`p` scalar set is the image of the
*eligible* indices, so its cardinality is at most the number of eligible indices.
-/
theorem card_eligible_image_le_card_eligible {ι S : Type*} [DecidableEq S]
    (T : Finset ι) (elig : ι → Prop) [DecidablePred elig] (v : ι → S) :
    ((T.filter elig).image v).card ≤ (T.filter elig).card :=
  Finset.card_image_le

/--
**Finite-branch drop + merge, against the full index count.** Dropping ineligible
indices from the finite-scalar branch and merging collisions, the finite
char-`p` scalar count is at most the *total* index count.
-/
theorem card_eligible_image_le_index {ι S : Type*} [DecidableEq S]
    (T : Finset ι) (elig : ι → Prop) [DecidablePred elig] (v : ι → S) :
    ((T.filter elig).image v).card ≤ T.card :=
  le_trans Finset.card_image_le (Finset.card_le_card (Finset.filter_subset _ _))

/-! ## Tier 3 — the ring-homomorphism specialization -/

/--
**Ring-hom finite bad-scalar count bound.** Let `num den : ι → R` be the
(numerator, denominator) ratio data, `φ : R →+* S` the reduction ring
homomorphism, and call `t` *eligible* when `φ (den t) ≠ 0`. The distinct
finite char-`p` bad-scalar count

`#{ φ(num t) · φ(den t)⁻¹ : t eligible }`

is at most the total index count `#T`. (Reduction is `0 ↦ 0`; vanishing
denominators leave this finite-ratio branch, while collisions merge. Saturation,
when the consumer interprets `φ(den t)=0` as "bad for every scalar", is handled
separately below.)
-/
theorem ringHom_badScalar_card_le {ι R S : Type*} [CommRing R] [Field S] [DecidableEq S]
    (T : Finset ι) (num den : ι → R) (φ : R →+* S) :
    ((T.filter (fun t => φ (den t) ≠ 0)).image
        (fun t => φ (num t) * (φ (den t))⁻¹)).card ≤ T.card :=
  card_eligible_image_le_index T (fun t => φ (den t) ≠ 0)
    (fun t => φ (num t) * (φ (den t))⁻¹)

/-! ## Tier 4 — finite-scalar merge-only monotonicity -/

/--
**Finite-scalar merge-only monotonicity.**

Setup. `charZero : ι → K` assigns to each index its char-0 bad scalar (e.g.
`γ_T ∈ Frac(ℤ[ζ_n])`); `charP : ι → S` assigns its char-`p` bad scalar (e.g. the
reduction `γ̄_T ∈ 𝔽_q`); `elig : ι → Prop` is char-`p` eligibility (denominator
nonvanishing mod `q`).

`red : K → S` is the reduction map on the fraction field. The hypothesis
`hfactor` says the char-`p` value *factors through* the char-0 value on eligible
indices: `charP t = red (charZero t)`. This is precisely the **no-SPLIT** content
verified in the probes — a single char-0 scalar maps to a single char-`p` scalar,
so reduction can only *merge* char-0 scalars, never split one into several.

Conclusion. The finite char-`p` distinct-scalar count over the eligible indices is at
most the char-0 distinct-scalar count over *all* indices:

`#{ charP t : t eligible } ≤ #{ charZero t : t }`.

This is deliberately **not** a statement about total incidence when denominator
vanishing saturates a line.
-/
theorem badScalar_charP_card_le_charZero {ι K S : Type*} [DecidableEq K] [DecidableEq S]
    (T : Finset ι) (elig : ι → Prop) [DecidablePred elig]
    (charZero : ι → K) (charP : ι → S) (red : K → S)
    (hfactor : ∀ t ∈ T, elig t → charP t = red (charZero t)) :
    ((T.filter elig).image charP).card ≤ (T.image charZero).card := by
  -- On the eligible indices, `charP = red ∘ charZero`, so the realized char-`p`
  -- set equals `red` applied to the char-0 image of the eligible indices.
  have hEqOn : Set.EqOn charP (red ∘ charZero) (↑(T.filter elig)) := by
    intro t ht
    rw [Finset.coe_filter, Set.mem_setOf_eq] at ht
    simpa using hfactor t ht.1 ht.2
  have hrewrite :
      (T.filter elig).image charP
        = ((T.filter elig).image charZero).image red := by
    rw [Finset.image_congr hEqOn, Finset.image_image]
  calc
    ((T.filter elig).image charP).card
        = (((T.filter elig).image charZero).image red).card := by rw [hrewrite]
    _ ≤ ((T.filter elig).image charZero).card := Finset.card_image_le
    _ ≤ (T.image charZero).card :=
          Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))

/--
**Finite budget-consumer form.** If the char-0 distinct-scalar count is at most
the Kambiré budget `B`, then so is the eligible finite char-`p` count.
-/
theorem badScalar_charP_card_le_budget {ι K S : Type*} [DecidableEq K] [DecidableEq S]
    (T : Finset ι) (elig : ι → Prop) [DecidablePred elig]
    (charZero : ι → K) (charP : ι → S) (red : K → S) {B : ℕ}
    (hfactor : ∀ t ∈ T, elig t → charP t = red (charZero t))
    (hbudget : (T.image charZero).card ≤ B) :
    ((T.filter elig).image charP).card ≤ B :=
  le_trans
    (badScalar_charP_card_le_charZero T elig charZero charP red hfactor) hbudget

/-! ## Tier 5 — saturation split for total incidence -/

/--
The total bad-scalar set obtained by combining the eligible finite-ratio branch
with a saturation branch.  If any index satisfies `sat`, the consumer interprets
that denominator-vanishing witness as "bad for every scalar", so the second
summand is `univ`; otherwise it is empty.
-/
noncomputable def saturatedBadScalarSet {ι S : Type*} [Fintype S] [DecidableEq S]
    (T : Finset ι) (elig sat : ι → Prop) [DecidablePred elig] [DecidablePred sat]
    (v : ι → S) : Finset S := by
  classical
  exact ((T.filter elig).image v) ∪
    (if (T.filter sat).Nonempty then Finset.univ else ∅)

/-- If a saturation index exists, the total bad-scalar set is the whole field. -/
theorem saturatedBadScalarSet_eq_univ_of_saturation {ι S : Type*}
    [Fintype S] [DecidableEq S]
    (T : Finset ι) (elig sat : ι → Prop) [DecidablePred elig] [DecidablePred sat]
    (v : ι → S) (hsat : (T.filter sat).Nonempty) :
    saturatedBadScalarSet T elig sat v = Finset.univ := by
  classical
  unfold saturatedBadScalarSet
  simp [hsat]

/-- If no saturation index exists, the total set is just the finite-ratio branch. -/
theorem saturatedBadScalarSet_eq_finite_of_no_saturation {ι S : Type*}
    [Fintype S] [DecidableEq S]
    (T : Finset ι) (elig sat : ι → Prop) [DecidablePred elig] [DecidablePred sat]
    (v : ι → S) (hno : ¬ (T.filter sat).Nonempty) :
    saturatedBadScalarSet T elig sat v = (T.filter elig).image v := by
  classical
  unfold saturatedBadScalarSet
  simp [hno]

/--
Saturation-aware cardinality envelope.  The finite-ratio branch is bounded by
merge-only image cardinality, but one saturating denominator can add the whole
field.  This is the corrected consumer shape for #407.
-/
theorem card_saturatedBadScalarSet_le_finite_plus_univ {ι S : Type*}
    [Fintype S] [DecidableEq S]
    (T : Finset ι) (elig sat : ι → Prop) [DecidablePred elig] [DecidablePred sat]
    (v : ι → S) :
    (saturatedBadScalarSet T elig sat v).card
      ≤ ((T.filter elig).image v).card
        + if (T.filter sat).Nonempty then Fintype.card S else 0 := by
  classical
  by_cases hsat : (T.filter sat).Nonempty
  · rw [saturatedBadScalarSet_eq_univ_of_saturation T elig sat v hsat]
    simp [hsat]
  · rw [saturatedBadScalarSet_eq_finite_of_no_saturation T elig sat v hsat]
    simp [hsat]

/--
The old monotonicity is recovered for total incidence only under an explicit
no-saturation hypothesis.  This is the safe form downstream consumers should use
when they really have proved denominator-vanishing cannot saturate.
-/
theorem saturatedBadScalarSet_card_le_charZero_of_no_saturation
    {ι K S : Type*} [Fintype S] [DecidableEq K] [DecidableEq S]
    (T : Finset ι) (elig sat : ι → Prop) [DecidablePred elig] [DecidablePred sat]
    (charZero : ι → K) (charP : ι → S) (red : K → S)
    (hno : ¬ (T.filter sat).Nonempty)
    (hfactor : ∀ t ∈ T, elig t → charP t = red (charZero t)) :
    (saturatedBadScalarSet T elig sat charP).card ≤ (T.image charZero).card := by
  classical
  rw [saturatedBadScalarSet_eq_finite_of_no_saturation T elig sat charP hno]
  exact badScalar_charP_card_le_charZero T elig charZero charP red hfactor

/--
Ring-hom specialization of the saturation hook: if some denominator reduces to
zero and the consumer marks such indices as saturating, the resulting total
bad-scalar set is all of `S`.
-/
theorem ringHom_saturatedBadScalarSet_eq_univ_of_zero_den
    {ι R S : Type*} [CommRing R] [Field S] [Fintype S] [DecidableEq S]
    (T : Finset ι) (num den : ι → R) (φ : R →+* S)
    {t : ι} (ht : t ∈ T) (hden : φ (den t) = 0) :
    saturatedBadScalarSet T (fun t => φ (den t) ≠ 0) (fun t => φ (den t) = 0)
      (fun t => φ (num t) * (φ (den t))⁻¹) = Finset.univ := by
  classical
  refine saturatedBadScalarSet_eq_univ_of_saturation T
    (fun t => φ (den t) ≠ 0) (fun t => φ (den t) = 0)
    (fun t => φ (num t) * (φ (den t))⁻¹) ?_
  exact ⟨t, by simp [ht, hden]⟩

/-!
## Wiring to the concrete `h_j` Schur-ratio bad-scalar map

To deploy the finite branch on the prize object one instantiates:

* `ι := ` the finite index set of admissible boundary-band subsets `T` for a fixed
  genuine direction `(a,b)`;
* `K := Frac(ℤ[ζ_n])` (or its image field), `charZero t := γ_T =
  − h_{a−k}(ζ^T) / h_{b−k}(ζ^T)` (the char-0 bad scalar);
* `S := 𝔽_q`, `charP t :=` the reduction of `γ_T`;
* `elig t := φ(h_{b−k}(ζ^T)) ≠ 0` (denominator nonvanishing mod `q`);
* `red :=` the field map induced by the reduction ring homomorphism
  `φ : ℤ[ζ_n] → 𝔽_q` on the fraction field (defined on the eligible locus).

The only nontrivial hypothesis is `hfactor : charP t = red (charZero t)` on
eligible `t`, which holds because `φ` is a **ring homomorphism**: it commutes with
the numerator/denominator arithmetic defining `γ_T`, so reducing the ratio equals
the ratio of reductions wherever the denominator survives. (`ringHom_badScalar_card_le`
above is the same statement with the ratio written out explicitly via `φ`, `num`,
`den`, and `⁻¹` in a field `S`, requiring no separate `red`.) The conclusion is
the eligible finite-ratio count is bounded by the char-0 image per direction.

The total bad-scalar count needs one more input: a proof that the saturation
predicate is empty, or a separate budget for `saturatedBadScalarSet`'s `univ`
branch.  A denominator-vanishing index is not deletion in consumers where it
means "bad for every scalar"; it is exactly the whole-field case
`ringHom_saturatedBadScalarSet_eq_univ_of_zero_den`.

This file proves the characteristic-free finite-branch monotonicity and the
saturation split only. It does NOT prove the companion char-0 statement
`N(char-0) = budget`, nor does it prove that saturation is absent in the prize
regime.
-/

/-- Documentation anchor for the wiring note above. -/
def wiringNote : Unit := ()

end ProximityGap.Frontier.RingHomBadScalarMono

#print axioms ProximityGap.Frontier.RingHomBadScalarMono.card_image_le_index
#print axioms
  ProximityGap.Frontier.RingHomBadScalarMono.card_eligible_image_le_card_eligible
#print axioms ProximityGap.Frontier.RingHomBadScalarMono.card_eligible_image_le_index
#print axioms ProximityGap.Frontier.RingHomBadScalarMono.ringHom_badScalar_card_le
#print axioms ProximityGap.Frontier.RingHomBadScalarMono.badScalar_charP_card_le_charZero
#print axioms ProximityGap.Frontier.RingHomBadScalarMono.badScalar_charP_card_le_budget
#print axioms
  ProximityGap.Frontier.RingHomBadScalarMono.saturatedBadScalarSet_eq_univ_of_saturation
#print axioms
  ProximityGap.Frontier.RingHomBadScalarMono.saturatedBadScalarSet_card_le_charZero_of_no_saturation
#print axioms
  ProximityGap.Frontier.RingHomBadScalarMono.ringHom_saturatedBadScalarSet_eq_univ_of_zero_den
