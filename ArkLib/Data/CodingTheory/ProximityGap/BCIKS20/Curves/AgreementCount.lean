/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Curve–codeword agreement counting ([BCIKS20] §6 building block)

A self-contained double-counting bound used in the Johnson-radius analysis of the proximity gap.
For a degree-`k` curve `w z = ∑ t, z^t • u t` through words `u 0 … u k : ι → F` and a target word
`c : ι → F`, it bounds how many curve parameters `z` can agree with `c` on a large set of
coordinates, in terms of the *permanent* agreement set `A = {i : ∀ z, agree at i}`.

`card_curveAgreement_le`:  `|G| · ((|ι| - e) - |A|) ≤ k · |ι|`, where `G` collects the parameters
agreeing on `≥ |ι| - e` coordinates. The mechanism: each non-permanent coordinate yields a
*nonzero* degree-`≤k` polynomial, hence at most `k` agreeing parameters (Schwartz–Zippel over a
finite field), while each `z ∈ G` contributes `≥ (|ι|-e) - |A|` non-permanent agreements.

`permanentAgreement_of_card_curveAgreement_gt`:  the dichotomy consequence — if *more than*
`k · |ι|` parameters agree with `c` on `≥ |ι| - e` coordinates, then `c` *permanently* agrees with
the curve on `≥ |ι| - e` coordinates. (Permanent agreement on a set `S` means the curve is
constant `= c` there, i.e. `u 0 = c` and `u t = 0` for `t ≥ 1` on `S` once `k < |F|` — exactly the
seed of joint agreement.)

This isolates the elementary half of the Johnson-radius counting; the deep remaining content of
the proximity gap is calibrating the threshold (the actual hypothesis is `Pr > k · errorBound`, a
list-size–weighted bound, not the crude `> k · |ι|` here).
-/

open Polynomial Finset BigOperators

namespace ProximityGap

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
         {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Root-set cardinality bound (reproved inline to keep imports light): over a finite field a
nonzero polynomial vanishes at at most `natDegree` points. -/
private lemma card_filter_eval_zero_le (p : F[X]) (hp : p ≠ 0) :
    (Finset.univ.filter (fun x => p.eval x = 0)).card ≤ p.natDegree := by
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  rw [Polynomial.mem_roots hp, Polynomial.IsRoot.def]
  exact hx

/-- The per-coordinate curve polynomial `∑ t, u t i · X^t`. -/
private noncomputable def colPoly {k : ℕ} (u : Fin (k + 1) → ι → F) (i : ι) : F[X] :=
  ∑ t : Fin (k + 1), Polynomial.monomial (t : ℕ) (u t i)

private lemma colPoly_eval {k : ℕ} (u : Fin (k + 1) → ι → F) (i : ι) (z : F) :
    (colPoly u i).eval z = ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i := by
  rw [colPoly, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Polynomial.eval_monomial]; ring

private lemma natDegree_colPoly_le {k : ℕ} (u : Fin (k + 1) → ι → F) (i : ι) :
    (colPoly u i).natDegree ≤ k := by
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  exact ⟨Nat.zero_le _, fun t _ =>
    (Polynomial.natDegree_monomial_le _).trans (by exact_mod_cast Nat.lt_succ_iff.mp t.2)⟩

/-- **Per-codeword curve-agreement count bound** ([BCIKS20] §6 building block).

`|G| · ((|ι| - e) - |A|) ≤ k · |ι|`, where `A` is the permanent agreement set
(`{i : ∀ z, curve agrees with c at i}`) and `G` collects parameters agreeing on `≥ |ι| - e`
coordinates. Double-counts transient agreements: each non-permanent coordinate contributes a
nonzero degree-`≤k` polynomial (`≤ k` roots), each `z ∈ G` contributes `≥ (|ι|-e) - |A|`
transient agreements. -/
theorem card_curveAgreement_le {k : ℕ} (u : Fin (k + 1) → ι → F) (c : ι → F) (e : ℕ) :
    (Finset.univ.filter (fun z : F =>
        Fintype.card ι - e ≤
          (Finset.univ.filter (fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i)).card)).card
      * ((Fintype.card ι - e)
          - (Finset.univ.filter (fun i => ∀ z : F,
              ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i)).card)
      ≤ k * Fintype.card ι := by
  classical
  set agr : F → ι → Prop := fun z i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i with hagr
  set A : Finset ι := Finset.univ.filter (fun i => ∀ z : F, agr z i) with hA
  set G : Finset F :=
    Finset.univ.filter (fun z : F => Fintype.card ι - e ≤ (Finset.univ.filter (agr z)).card)
    with hG
  set m : ℕ := (Fintype.card ι - e) - A.card with hm
  set f : F → ℕ := fun z => (Finset.univ.filter (fun i => agr z i ∧ i ∉ A)).card with hf
  have hAsub : ∀ z : F, A ⊆ Finset.univ.filter (agr z) := by
    intro z i hi
    rw [hA, Finset.mem_filter] at hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.2 z⟩
  have hfdiff : ∀ z : F, f z = (Finset.univ.filter (agr z)).card - A.card := by
    intro z
    have hset : Finset.univ.filter (fun i => agr z i ∧ i ∉ A)
        = (Finset.univ.filter (agr z)) \ A := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    simp only [hf]
    rw [hset, Finset.card_sdiff_of_subset (hAsub z)]
  have hlower : G.card * m ≤ ∑ z ∈ G, f z := by
    have hterm : ∀ z ∈ G, m ≤ f z := by
      intro z hz
      rw [hfdiff z, hm]
      have hzc : Fintype.card ι - e ≤ (Finset.univ.filter (agr z)).card := by
        rw [hG, Finset.mem_filter] at hz; exact hz.2
      exact Nat.sub_le_sub_right hzc A.card
    calc G.card * m = G.card • m := by rw [smul_eq_mul]
      _ ≤ ∑ z ∈ G, f z := G.card_nsmul_le_sum f m hterm
  have hstep1 : ∑ z ∈ G, f z ≤ ∑ z ∈ (Finset.univ : Finset F), f z :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hswap : ∑ z ∈ (Finset.univ : Finset F), f z
      = ∑ i ∈ (Finset.univ : Finset ι),
          (Finset.univ.filter (fun z : F => agr z i ∧ i ∉ A)).card := by
    simp only [hf, Finset.card_filter]
    rw [Finset.sum_comm]
  have hcol : ∀ i : ι, (Finset.univ.filter (fun z : F => agr z i ∧ i ∉ A)).card ≤ k := by
    intro i
    by_cases hiA : i ∈ A
    · have hempty : Finset.univ.filter (fun z : F => agr z i ∧ i ∉ A) = ∅ := by
        apply Finset.filter_false_of_mem
        intro z _ hcon
        exact hcon.2 hiA
      rw [hempty]; simp
    · set q : F[X] := colPoly u i - Polynomial.C (c i) with hq
      have hagr_iff : ∀ z : F, agr z i ↔ q.eval z = 0 := by
        intro z
        rw [hq, Polynomial.eval_sub, Polynomial.eval_C, colPoly_eval, hagr]
        exact sub_eq_zero.symm
      have hqne : q ≠ 0 := by
        rw [hA, Finset.mem_filter] at hiA
        push Not at hiA
        obtain ⟨z, hz⟩ := hiA (Finset.mem_univ i)
        intro hq0
        exact hz (by rw [hagr_iff z, hq0, Polynomial.eval_zero])
      have hqdeg : q.natDegree ≤ k := by
        refine (Polynomial.natDegree_sub_le _ _).trans ?_
        simp only [Polynomial.natDegree_C, Nat.max_eq_left (Nat.zero_le _)]
        exact natDegree_colPoly_le u i
      have hfe : Finset.univ.filter (fun z : F => agr z i ∧ i ∉ A)
          = Finset.univ.filter (fun z : F => q.eval z = 0) := by
        apply Finset.filter_congr
        intro z _
        rw [hagr_iff z]; simp [hiA]
      rw [hfe]
      exact (card_filter_eval_zero_le q hqne).trans hqdeg
  have hupper2 : ∑ i ∈ (Finset.univ : Finset ι),
      (Finset.univ.filter (fun z : F => agr z i ∧ i ∉ A)).card ≤ k * Fintype.card ι := by
    calc ∑ i ∈ (Finset.univ : Finset ι),
            (Finset.univ.filter (fun z : F => agr z i ∧ i ∉ A)).card
        ≤ ∑ _i ∈ (Finset.univ : Finset ι), k := Finset.sum_le_sum (fun i _ => hcol i)
      _ = k * Fintype.card ι := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  calc G.card * m ≤ ∑ z ∈ G, f z := hlower
    _ ≤ ∑ z ∈ (Finset.univ : Finset F), f z := hstep1
    _ = ∑ i ∈ (Finset.univ : Finset ι),
          (Finset.univ.filter (fun z : F => agr z i ∧ i ∉ A)).card := hswap
    _ ≤ k * Fintype.card ι := hupper2

/-- **Agreement dichotomy.** If strictly more than `k · |ι|` curve parameters agree with the
target `c` on `≥ |ι| - e` coordinates, then `c` *permanently* agrees with the curve on `≥ |ι| - e`
coordinates (i.e. the permanent agreement set has size `≥ |ι| - e`). This is the qualitative
"global structure is forced" conclusion of the counting bound. -/
theorem permanentAgreement_of_card_curveAgreement_gt {k : ℕ}
    (u : Fin (k + 1) → ι → F) (c : ι → F) (e : ℕ)
    (hG : k * Fintype.card ι <
      (Finset.univ.filter (fun z : F =>
        Fintype.card ι - e ≤
          (Finset.univ.filter
            (fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i)).card)).card) :
    Fintype.card ι - e ≤
      (Finset.univ.filter (fun i => ∀ z : F,
        ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i)).card := by
  classical
  set g : ℕ := (Finset.univ.filter (fun z : F =>
      Fintype.card ι - e ≤
        (Finset.univ.filter
          (fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i)).card)).card with hgdef
  set a : ℕ := (Finset.univ.filter (fun i => ∀ z : F,
      ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i)).card with hadef
  have hbound : g * ((Fintype.card ι - e) - a) ≤ k * Fintype.card ι :=
    card_curveAgreement_le u c e
  by_contra hlt
  push Not at hlt
  -- hlt : a < |ι| - e, so the truncated difference is ≥ 1
  have hpos : 1 ≤ (Fintype.card ι - e) - a := by omega
  have : g ≤ g * ((Fintype.card ι - e) - a) := Nat.le_mul_of_pos_right g hpos
  omega

end ProximityGap
