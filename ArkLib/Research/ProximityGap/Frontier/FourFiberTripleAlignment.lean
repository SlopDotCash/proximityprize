/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSMinDistance
import Mathlib.Data.Fin.Rev

/-! # A four-fiber obstruction for prescribed triple agreements

A rational function classifying the exceptional head on too many triple-agreement
sites forces the same agreements on its full fibers. This excludes the
near-partition by four quotient fibers at the half-rate quarter successor.
-/

set_option autoImplicit false
open Finset Polynomial
namespace ProximityGap.FourFiberTripleAlignment

variable {I F : Type} [Fintype I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

/-- A degree-bounded four-fiber map can classify at most deg(map) + d sites on which
all three other heads agree with the received value. Only the two fibers opposite
the distinguished distinct heads need to be large enough to determine their difference. -/
theorem alignment_cap (dom : I ↪ F) (g b : F[X]) (hb : ∀ x, b.eval (dom x) ≠ 0) (a : Fin 4 ↪ F) (label : I → Fin 4)
    (hfiber : ∀ x, g.eval (dom x) = a (label x) * b.eval (dom x)) (f : Fin 4 → F[X]) (d : ℕ)
    (hdeg : ∀ i, (f i).natDegree ≤ d) (hne : f 0 ≠ f 1)
    (hopp : d < (univ.filter (fun x => label x = 2 ∨ label x = 3)).card)
    (y : I → F) (S : Finset I)
    (hs : ∀ x ∈ S, ∀ i, i ≠ label x → (f i).eval (dom x) = y x) :
    S.card ≤ max g.natDegree b.natDegree + d := by
  classical
  by_contra! hmany
  let entry (i : Fin 4) := (g - C (a i) * b) * f i
  let test (r : Fin 4) := C (a 1 - a r) * entry 0 +
    C (a r - a 0) * entry 1 + C (a 0 - a 1) * entry r
  have de (i : Fin 4) : (entry i).natDegree ≤ max g.natDegree b.natDegree + d := by
    apply (natDegree_mul_le ..).trans (Nat.add_le_add _ (hdeg i))
    exact (natDegree_sub_le ..).trans (max_le_max_left _ (natDegree_C_mul_le ..))
  have dt (r : Fin 4) : (test r).natDegree ≤ max g.natDegree b.natDegree + d := by
    apply (natDegree_add_le ..).trans (max_le _ ((natDegree_C_mul_le ..).trans (de r)))
    exact (natDegree_add_le ..).trans (max_le ((natDegree_C_mul_le ..).trans (de 0))
      ((natDegree_C_mul_le ..).trans (de 1)))
  have vanishes (r : Fin 4) : test r = 0 := by
    by_contra hnonzero
    have sub : S ⊆ univ.filter (fun x => (test r).eval (dom x) = 0) := by
      intro x hx
      apply mem_filter.mpr ⟨mem_univ _, ?_⟩
      have he (i : Fin 4) : (entry i).eval (dom x) = ((a (label x) - a i) * b.eval (dom x)) * y x := by
        simp only [entry, eval_mul, eval_sub, eval_C, hfiber]
        by_cases h : i = label x
        · simp [h]
        · rw [hs x hx i h]
          ring
      simp only [test, eval_add, eval_mul, eval_C, he]
      ring
    exact (not_lt_of_ge ((card_le_card sub).trans
      ((ArkLib.CS25.card_domain_roots_le dom (test r) hnonzero).trans (dt r)))) hmany
  have eq_on {x : I} (h0 : label x ≠ 0) (h1 : label x ≠ 1) :
      (f 0).eval (dom x) = (f 1).eval (dom x) := by
    have hv := congrArg (fun p : F[X] => p.eval (dom x)) (vanishes (label x))
    simp only [test, entry, eval_add, eval_mul, eval_sub, eval_C, hfiber, sub_self,
      zero_mul, mul_zero, add_zero, eval_zero] at hv
    have hz : b.eval (dom x) * ((a (label x) - a 0) * (a (label x) - a 1) *
        ((f 0).eval (dom x) - (f 1).eval (dom x))) = 0 := by linear_combination -hv
    have hprod := (mul_eq_zero.mp hz).resolve_left (hb x)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left
      (mul_ne_zero (sub_ne_zero.mpr (a.injective.ne h0)) (sub_ne_zero.mpr (a.injective.ne h1))))
  have sub : univ.filter (fun x => label x = 2 ∨ label x = 3) ⊆
      univ.filter (fun x => (f 0 - f 1).eval (dom x) = 0) := by
    intro x hx
    apply mem_filter.mpr ⟨mem_univ _, ?_⟩
    rcases (mem_filter.mp hx).2 with h | h <;>
      simpa only [eval_sub, sub_eq_zero] using (eq_on (x := x) (by omega) (by omega))
  exact (not_lt_of_ge ((card_le_card sub).trans
    ((ArkLib.CS25.card_domain_roots_le dom _ (sub_ne_zero.mpr hne)).trans
      ((natDegree_sub_le ..).trans (max_le (hdeg 0) (hdeg 1)))))) hopp

/-- At length greater than twice the head degree, the fiber-size condition is
automatic after relabeling. The four fibers may have unequal cardinalities. -/
theorem four_value_cap (dom : I ↪ F) (g b : F[X]) (hb : ∀ x, b.eval (dom x) ≠ 0)
    (a : Fin 4 ↪ F) (label : I → Fin 4)
    (hfiber : ∀ x, g.eval (dom x) = a (label x) * b.eval (dom x))
    (f : Fin 4 → F[X]) (d : ℕ) (hd : 2*d < Fintype.card I)
    (hdeg : ∀ i, (f i).natDegree ≤ d) (hinj : Function.Injective f)
    (y : I → F) (S : Finset I)
    (hs : ∀ x ∈ S, ∀ i, i ≠ label x → (f i).eval (dom x) = y x) :
    S.card ≤ max g.natDegree b.natDegree + d := by
  classical
  by_cases h23 : d < (univ.filter fun x => label x = 2 ∨ label x = 3).card
  · exact alignment_cap dom g b hb a label hfiber f d hdeg (hinj.ne (by decide)) h23 y S hs
  let a' := (Fin.revPerm (n := 4)).toEmbedding.trans a
  let lb (x : I) := (label x).rev
  let f' (i : Fin 4) := f i.rev
  have hpartition : (univ.filter (fun x => lb x = 2 ∨ lb x = 3)) =
      univ.filter (fun x => ¬(label x = 2 ∨ label x = 3)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, lb]
    generalize label x = v
    fin_cases v <;> decide
  have hop : d < (univ.filter (fun x => lb x = 2 ∨ lb x = 3)).card := by
    rw [hpartition]
    have he := Finset.card_filter_add_card_filter_not (s := (univ : Finset I))
      (fun x => label x = 2 ∨ label x = 3)
    rw [card_univ] at he
    omega
  apply alignment_cap dom g b hb a' lb (fun x => by simpa [a', lb] using hfiber x) f' d
    (fun i => hdeg i.rev) (hinj.ne (by decide)) hop y S
  intro x hx i hi
  apply hs x hx i.rev
  exact fun he => hi (by simpa [lb] using congrArg Fin.rev he)

/-- If the four scalar heads from a successor violation have at least n - 8 triple
sites, any degree-h four-value rational map
must misclassify at least h - 6 of them. -/
theorem production_mismatches (dom : I ↪ F) (hn : Fintype.card I = 1073741824) (g b : F[X])
    (hg : max g.natDegree b.natDegree ≤ 268435456) (hb : ∀ x, b.eval (dom x) ≠ 0)
    (a : Fin 4 ↪ F) (label : I → Fin 4) (hfiber : ∀ x, g.eval (dom x) = a (label x) * b.eval (dom x))
    (f : Fin 4 → F[X]) (hdeg : ∀ i, (f i).natDegree ≤ 536870910) (hinj : Function.Injective f)
    (y : I → F) (triples aligned : Finset I) (hsub : aligned ⊆ triples)
    (ht : 1073741816 ≤ triples.card)
    (hs : ∀ x ∈ aligned, ∀ i, i ≠ label x → (f i).eval (dom x) = y x) :
    268435450 ≤ (triples \ aligned).card := by
  have bound := four_value_cap dom g b hb a label hfiber f _ (by omega) hdeg hinj y aligned hs
  rw [card_sdiff_of_subset hsub]
  omega

#print axioms alignment_cap
#print axioms four_value_cap
#print axioms production_mismatches

end ProximityGap.FourFiberTripleAlignment
