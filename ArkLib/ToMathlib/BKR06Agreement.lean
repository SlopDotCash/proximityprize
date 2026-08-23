/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.ListDecoding.BKR06SubspacePoly
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# BKR06 Lemma 3.5: the agreement-count bridge

Ben-Sasson–Kopparty–Radhakrishnan, *Subspace polynomials and list decoding of
Reed–Solomon codes* (FOCS 2006), build their list-decoding lower bound by exhibiting,
for each subspace `W ⊆ K` in the pigeonhole family, a codeword that agrees with the
received word on *many* evaluation points.  Concretely: the evaluation vectors of a
pivot polynomial `pivot` and of `pivot − s_W` (where `s_W = subspacePoly (subFinset W)`
is the subspace polynomial of `W`) agree at an evaluation point `x` **iff** `s_W`
vanishes there, i.e. iff `domain x ∈ W`.

This file proves that bridge as a clean, parameter-free counting fact:

* `evalOnPoints_agreement_eq_filter` — the agreement set is *exactly*
  `{x | domain x ∈ W}` (pointwise characterization, from `subspacePoly_isRoot_iff`).
* `evalOnPoints_agreement_card` — when `domain` is **surjective**, the map `x ↦ domain x`
  is a bijection from the agreement set onto `subFinset W`, so the agreement count
  equals `Fintype.card W` exactly.
* `evalOnPoints_agreement_card_ge` — the `≥ Fintype.card W` corollary, which is exactly
  the agreement-count hypothesis `a ≤ #{i | w i = c i}` that
  `BKR06Close.mem_closeCodewordsRel_of_agreement` consumes to discharge the `hclose`
  residual of `rs_lambda_superpoly_extension_bkr06_of_family`.

The mathematics is BKR06's: the subspace polynomial of `W` has the `|W|` points of `W`
as its roots (`subspacePoly_roots`), so subtracting it off `pivot` changes the value at
exactly the `|K| − |W|` non-`W` points and leaves the `|W|` points of `W` untouched —
hence agreement `= |W|`.  **No real-exponent / dimension-threshold arithmetic is used:**
this is the geometric root-count half of `hclose`, kept separate from the parameter
inequality `q^(β−1) ≤ a/N` (the honest dimension-condition residual handled in
`BKR06Close`).

All declarations compile `sorry`/`axiom`-free and are axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

open Polynomial BigOperators Finset

namespace BKR06

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Module F K]

/-- **Pointwise agreement characterization.**  The evaluation vectors of `pivot` and of
`pivot − s_W` agree at the point `x` iff the subspace polynomial `s_W` vanishes at
`domain x`, i.e. iff `domain x ∈ W`. -/
lemma evalOnPoints_agreement_iff
    (domain : K ↪ K) (pivot : K[X]) (W : Submodule F K) [Fintype W] (x : K) :
    (ReedSolomon.evalOnPoints domain pivot) x
        = (ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset W))) x
      ↔ domain x ∈ W := by
  have he : ∀ p : K[X], (ReedSolomon.evalOnPoints domain p) x = p.eval (domain x) :=
    fun p => rfl
  rw [he, he, eval_sub]
  constructor
  · intro h
    have hz : (subspacePoly (subFinset W)).eval (domain x) = 0 := by linear_combination h
    exact mem_subFinset.mp ((subspacePoly_isRoot_iff (subFinset W) (domain x)).mp hz)
  · intro hW
    have hz : (subspacePoly (subFinset W)).eval (domain x) = 0 :=
      (subspacePoly_isRoot_iff (subFinset W) (domain x)).mpr (mem_subFinset.mpr hW)
    rw [hz, sub_zero]

/-- **BKR06 Lemma 3.5 agreement count (exact).**  When `domain` is surjective, the
evaluation vectors of `pivot` and `pivot − s_W` agree on **exactly** `Fintype.card W`
of the `|K|` evaluation points — the bijective image (under `domain`) of the `|W|` roots
of `s_W`.  The agreement `Finset` carries the default `DecidableEq K` instance, so this
lemma plugs directly into `BKR06Close.mem_closeCodewordsRel_of_agreement`. -/
lemma evalOnPoints_agreement_card
    (domain : K ↪ K) (hsurj : Function.Surjective domain)
    (pivot : K[X]) (W : Submodule F K) [Fintype W] :
    (Finset.univ.filter (fun x =>
        (ReedSolomon.evalOnPoints domain pivot) x
          = (ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset W))) x)).card
      = Fintype.card W := by
  classical
  -- `x ↦ domain x` is a bijection from the agreement set onto `subFinset W`
  -- (membership characterized by `evalOnPoints_agreement_iff`).
  have hbij :
      (Finset.univ.filter (fun x =>
          (ReedSolomon.evalOnPoints domain pivot) x
            = (ReedSolomon.evalOnPoints domain
                (pivot - subspacePoly (subFinset W))) x)).card
        = (subFinset W).card := by
    apply Finset.card_bij (fun x _ => domain x)
    · intro a ha
      rw [Finset.mem_filter] at ha
      exact mem_subFinset.mpr ((evalOnPoints_agreement_iff domain pivot W a).mp ha.2)
    · intro a _ b _ hab
      exact domain.injective hab
    · intro b hb
      obtain ⟨a, ha⟩ := hsurj b
      refine ⟨a, ?_, ha⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ a, (evalOnPoints_agreement_iff domain pivot W a).mpr ?_⟩
      rw [ha]
      exact mem_subFinset.mp hb
  rw [hbij, subFinset]
  simp [Set.toFinset_card]

/-- **BKR06 Lemma 3.5 agreement count (lower bound).**  The agreement count is at least
`Fintype.card W`.  This is exactly the agreement hypothesis
`a ≤ #{i | w i = c i}` (with `a = |W|`) consumed by
`BKR06Close.mem_closeCodewordsRel_of_agreement` to discharge the `hclose` residual of
`rs_lambda_superpoly_extension_bkr06_of_family`. -/
lemma evalOnPoints_agreement_card_ge
    (domain : K ↪ K) (hsurj : Function.Surjective domain)
    (pivot : K[X]) (W : Submodule F K) [Fintype W] :
    Fintype.card W ≤
      (Finset.univ.filter (fun x =>
        (ReedSolomon.evalOnPoints domain pivot) x
          = (ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset W))) x)).card :=
  (evalOnPoints_agreement_card domain hsurj pivot W).ge

end BKR06
