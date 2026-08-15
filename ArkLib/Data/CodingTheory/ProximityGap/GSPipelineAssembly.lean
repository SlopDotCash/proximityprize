/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
Round 14 — Angle D: the Guruswami–Sudan ASSEMBLY (ArkLib #232, proximity-prize GS route).

CONTENT (all fully proved, no placeholders):

1. `root_cap` — the GS Y-degree cap: a nonzero bivariate `Q : F[X][Y]` admits at most
   `Q.natDegree` (its `Y`-degree) distinct polynomials `f` with `(Y - C f) ∣ Q`.
   Proof: each such `f` is a root of `Q` over the integral domain `F[X]`, and a nonzero
   polynomial over a domain has at most `natDegree` roots.

2. `gs_list_bound` — the conditional GS assembly: for evaluation points `α : Fin n → F`
   and received word `w : Fin n → F`, IF some nonzero `Q : F[X][Y]` has `Y`-degree ≤ L
   and `(Y - C f) ∣ Q` for every `f` of degree < k agreeing with `w` on ≥ t points
   (the interpolation + root-order front end, packaged as a hypothesis), THEN the list
   `{f : deg f < k, agree(f, w) ≥ t}` is finite of size ≤ L.

3. Full discharge of the hypothesis on a concrete RS instance (Sudan-style, m = 1):
   `F = ZMod 7`, n = 6, k = 2, α = (0,1,2,3,4,5), w = (0,0,0,3,4,5), t = 3,
   `Q(X,Y) = Y·(Y - X)` (so L = 2). `Q` is nonzero, has `Y`-degree exactly 2, vanishes
   at all six points `(αᵢ, wᵢ)` (`Qc_vanishes`), and the divisibility hypothesis is
   genuinely proved (`vanishing_concrete`): any degree-<2 polynomial agreeing with `w`
   on ≥ 3 of the 6 points is `0` or `X` (a kernel-checked classification over all 49
   candidate lines), and both `Y - C 0` and `Y - C X` divide `Q`.

4. End-to-end firing: `gs_concrete` (list ≤ 2) and exactness `theList_eq`/`gs_main`
   (the list is exactly `{0, X}`, of size exactly 2 — the bound is tight, hence
   non-vacuous: the list is nonempty and even has TWO elements).

HONEST SCOPE. The radius here is the genuine LIST-decoding regime but not past Johnson:
t = 3 agreements out of n = 6 with k = 2 is strictly beyond unique decoding
(unique decoding needs t ≥ ⌈(n + k)/2⌉ = 4; indeed the output list has two codewords),
and satisfies the Sudan/GS condition t > √((k-1)n) = √6 ≈ 2.45. The Johnson bound at
these parameters also certifies small lists, so this instance does NOT push past Johnson;
no claim to the contrary is made. What this file contributes is the verified end-to-end
GS pipeline skeleton — conditional assembly + a fully discharged concrete instance —
which is the scaffold any past-Johnson refinement of the interpolation step would plug
into (only the hypothesis `hvan` of `gs_list_bound` would change).
-/
import Mathlib

open Polynomial
open scoped Polynomial.Bivariate

namespace R14GS

universe u

instance primeFact_GSPipelineAssembly_1 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ## Part 1: the generic GS endgame (Y-degree cap) -/

/-- **GS Y-degree cap.** If `Q : F[X][Y]` is nonzero and every member of a set
`S ⊆ F[X]` gives a linear factor `Y - C f` of `Q`, then `S` is finite with at most
`Q.natDegree` (= the `Y`-degree of `Q`) elements. This is the endgame of every
Guruswami–Sudan style list bound. -/
theorem root_cap {F : Type u} [Field F] (Q : F[X][Y]) (hQ : Q ≠ 0)
    {S : Set F[X]} (hS : ∀ f ∈ S, (Y - C f) ∣ Q) :
    S.Finite ∧ S.ncard ≤ Q.natDegree := by
  classical
  have hsub : S ⊆ ↑Q.roots.toFinset := by
    intro f hf
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots']
    exact ⟨hQ, dvd_iff_isRoot.mp (hS f hf)⟩
  refine ⟨(Q.roots.toFinset.finite_toSet).subset hsub, ?_⟩
  calc S.ncard ≤ (↑Q.roots.toFinset : Set F[X]).ncard :=
        Set.ncard_le_ncard hsub (Q.roots.toFinset.finite_toSet)
    _ = Q.roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Multiset.card Q.roots := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := Q.card_roots'

/-! ## Part 2: the conditional GS assembly for Reed–Solomon lists -/

/-- Number of evaluation points where `f` agrees with the received word `w`. -/
def agree {F : Type u} [Field F] [DecidableEq F] {n : ℕ} (α w : Fin n → F)
    (f : F[X]) : ℕ :=
  (Finset.univ.filter fun i => f.eval (α i) = w i).card

/-- The Guruswami–Sudan list: degree-`< k` message polynomials agreeing with the
received word `w` on at least `t` of the `n` evaluation points. -/
def gsList {F : Type u} [Field F] [DecidableEq F] {n : ℕ} (α w : Fin n → F)
    (k t : ℕ) : Set F[X] :=
  {f : F[X] | f.degree < (k : WithBot ℕ) ∧ t ≤ agree α w f}

/-- **Conditional GS list bound (the assembly).** If some nonzero `Q : F[X][Y]` has
`Y`-degree at most `L` and the GS vanishing property — `(Y - C f) ∣ Q` for every
degree-`< k` polynomial `f` agreeing with `w` on at least `t` points (this hypothesis
packages the multiplicity interpolation and the `t·m > wdeg` root-order argument) —
then the GS list is finite of size at most `L`. -/
theorem gs_list_bound {F : Type u} [Field F] [DecidableEq F] {n k t L : ℕ}
    (α w : Fin n → F) (Q : F[X][Y]) (hQ : Q ≠ 0) (hdegY : Q.natDegree ≤ L)
    (hvan : ∀ f : F[X], f.degree < (k : WithBot ℕ) → t ≤ agree α w f → (Y - C f) ∣ Q) :
    (gsList α w k t).Finite ∧ (gsList α w k t).ncard ≤ L := by
  obtain ⟨hfin, hcard⟩ := root_cap Q hQ (S := gsList α w k t)
    (fun f hf => hvan f hf.1 hf.2)
  exact ⟨hfin, hcard.trans hdegY⟩

/-! ## Part 3: full discharge on a concrete RS instance (Sudan m = 1)

`RS[ZMod 7, n = 6, k = 2]`, evaluation points `0,…,5`, received word `(0,0,0,3,4,5)`
(three points on the line `y = 0`, four on the line `y = x`, sharing the point `(0,0)`),
agreement threshold `t = 3`, interpolation polynomial `Q(X,Y) = Y·(Y − X)`. -/

/-- The six evaluation points of the Reed–Solomon code. -/
def αv : Fin 6 → ZMod 7 := ![0, 1, 2, 3, 4, 5]

/-- The received word: agrees with the codeword `0` on `{0,1,2}` and with the
codeword `X` on `{0,3,4,5}`. -/
def wv : Fin 6 → ZMod 7 := ![0, 0, 0, 3, 4, 5]

/-- The explicit Sudan (m = 1) interpolation polynomial `Q(X,Y) = Y·(Y − X)`. -/
noncomputable def Qc : (ZMod 7)[X][Y] := Y * (Y - C X)

/-- `Q` is genuinely an interpolation witness: it vanishes at all six points
`(αᵢ, wᵢ)` of the received word. -/
theorem Qc_vanishes : ∀ i : Fin 6, Qc.evalEval (αv i) (wv i) = 0 := by
  intro i
  fin_cases i <;> simp [Qc, αv, wv, evalEval]

theorem Qc_ne_zero : Qc ≠ 0 :=
  mul_ne_zero X_ne_zero (X_sub_C_ne_zero X)

theorem Qc_natDegree : Qc.natDegree = 2 := by
  rw [Qc, natDegree_mul X_ne_zero (X_sub_C_ne_zero X), natDegree_X, natDegree_X_sub_C]

/-- Kernel-checked classification: among all 49 affine lines `y = b·x + a` over
`ZMod 7`, only `y = 0` (i.e. `b = 0, a = 0`) and `y = x` (i.e. `b = 1, a = 0`)
pass through at least 3 of the six points `(αᵢ, wᵢ)`. -/
theorem classify : ∀ b a : ZMod 7,
    3 ≤ (Finset.univ.filter fun i : Fin 6 => b * αv i + a = wv i).card →
    (b = 0 ∧ a = 0) ∨ (b = 1 ∧ a = 0) := by decide

/-- Discharge of the GS vanishing hypothesis on the concrete instance: every
degree-< 2 polynomial agreeing with `wv` on ≥ 3 points yields a factor `Y - C f`
of `Qc`. -/
theorem vanishing_concrete :
    ∀ f : (ZMod 7)[X], f.degree < ((2 : ℕ) : WithBot ℕ) → 3 ≤ agree αv wv f →
      (Y - C f) ∣ Qc := by
  intro f hdeg hagree
  have h1 : f.degree ≤ 1 := by
    rcases eq_or_ne f 0 with rfl | hf
    · simp
    · have h2 : f.natDegree < 2 := (natDegree_lt_iff_degree_lt hf).mpr hdeg
      calc f.degree ≤ (f.natDegree : WithBot ℕ) := degree_le_natDegree
        _ ≤ (1 : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_iff.mp h2
  have hrepr : f = C (f.coeff 1) * X + C (f.coeff 0) := eq_X_add_C_of_degree_le_one h1
  have heval : ∀ i : Fin 6, f.eval (αv i) = f.coeff 1 * αv i + f.coeff 0 := by
    intro i
    conv_lhs => rw [hrepr]
    simp
  have hcount :
      3 ≤ (Finset.univ.filter fun i : Fin 6 => f.coeff 1 * αv i + f.coeff 0 = wv i).card := by
    have hfilter :
        (Finset.univ.filter fun i : Fin 6 => f.eval (αv i) = wv i)
          = Finset.univ.filter fun i : Fin 6 => f.coeff 1 * αv i + f.coeff 0 = wv i :=
      Finset.filter_congr (fun i _ => by rw [heval i])
    have := hagree
    rw [agree, hfilter] at this
    exact this
  rcases classify (f.coeff 1) (f.coeff 0) hcount with ⟨hb, ha⟩ | ⟨hb, ha⟩
  · -- f = 0, and (Y - C 0) = Y divides Y·(Y - X)
    have hf0 : f = 0 := by rw [hrepr, hb, ha]; simp
    rw [hf0, map_zero, sub_zero]
    exact dvd_mul_right _ _
  · -- f = X, and (Y - C X) divides Y·(Y - X)
    have hfX : f = X := by rw [hrepr, hb, ha]; simp
    rw [hfX]
    exact dvd_mul_left _ _

/-! ## Part 4: the pipeline fires end-to-end -/

/-- **End-to-end GS list bound on a real RS instance.** The list of degree-< 2
polynomials over `ZMod 7` agreeing with `wv` on at least 3 of the 6 points is finite
of size at most 2 — obtained by running the conditional assembly `gs_list_bound`
on the fully verified witness `Qc`. Note t = 3 is strictly BELOW the unique-decoding
threshold ⌈(n+k)/2⌉ = 4, so this is a genuine list-decoding (not unique-decoding) radius. -/
theorem gs_concrete :
    (gsList αv wv 2 3).Finite ∧ (gsList αv wv 2 3).ncard ≤ 2 :=
  gs_list_bound αv wv Qc Qc_ne_zero (by rw [Qc_natDegree]) vanishing_concrete

/-- Exactness / non-vacuity: the GS list at these parameters is exactly `{0, X}`. -/
theorem theList_eq : gsList αv wv 2 3 = {0, X} := by
  ext f
  constructor
  · rintro ⟨hdeg, hagree⟩
    have h1 : f.degree ≤ 1 := by
      rcases eq_or_ne f 0 with rfl | hf
      · simp
      · have h2 : f.natDegree < 2 := (natDegree_lt_iff_degree_lt hf).mpr hdeg
        calc f.degree ≤ (f.natDegree : WithBot ℕ) := degree_le_natDegree
          _ ≤ (1 : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_iff.mp h2
    have hrepr : f = C (f.coeff 1) * X + C (f.coeff 0) := eq_X_add_C_of_degree_le_one h1
    have heval : ∀ i : Fin 6, f.eval (αv i) = f.coeff 1 * αv i + f.coeff 0 := by
      intro i
      conv_lhs => rw [hrepr]
      simp
    have hcount :
        3 ≤ (Finset.univ.filter fun i : Fin 6 => f.coeff 1 * αv i + f.coeff 0 = wv i).card := by
      have hfilter :
          (Finset.univ.filter fun i : Fin 6 => f.eval (αv i) = wv i)
            = Finset.univ.filter fun i : Fin 6 => f.coeff 1 * αv i + f.coeff 0 = wv i :=
        Finset.filter_congr (fun i _ => by rw [heval i])
      have := hagree
      rw [agree, hfilter] at this
      exact this
    rcases classify (f.coeff 1) (f.coeff 0) hcount with ⟨hb, ha⟩ | ⟨hb, ha⟩
    · left; rw [hrepr, hb, ha]; simp
    · right; rw [hrepr, hb, ha]; simp
  · rintro (rfl | rfl)
    · refine ⟨by rw [degree_zero]; exact_mod_cast WithBot.bot_lt_coe (2 : ℕ), ?_⟩
      show 3 ≤ (Finset.univ.filter fun i : Fin 6 => (0 : (ZMod 7)[X]).eval (αv i) = wv i).card
      simp only [eval_zero]
      decide
    · refine ⟨?_, ?_⟩
      · rw [degree_X]
        exact_mod_cast Nat.one_lt_two
      · show 3 ≤ (Finset.univ.filter fun i : Fin 6 => (X : (ZMod 7)[X]).eval (αv i) = wv i).card
        simp only [eval_X]
        decide

/-- **Main theorem (capstone).** The verified end-to-end Guruswami–Sudan pipeline on
`RS[ZMod 7, 6, 2]` at agreement t = 3: the conditional assembly fires on the explicit
witness `Q = Y·(Y−X)`, the resulting list bound 2 holds, and it is TIGHT — the list is
exactly `{0, X}` of size exactly 2 (so nothing here is vacuous, and the radius is
genuinely beyond unique decoding). -/
theorem gs_main :
    (gsList αv wv 2 3).Finite ∧ (gsList αv wv 2 3).ncard ≤ 2 ∧
      gsList αv wv 2 3 = {0, X} ∧ (gsList αv wv 2 3).ncard = 2 := by
  refine ⟨gs_concrete.1, gs_concrete.2, theList_eq, ?_⟩
  rw [theList_eq]
  exact Set.ncard_pair (Ne.symm X_ne_zero)

end R14GS

#print axioms R14GS.root_cap
#print axioms R14GS.gs_list_bound
#print axioms R14GS.gs_concrete
#print axioms R14GS.gs_main
