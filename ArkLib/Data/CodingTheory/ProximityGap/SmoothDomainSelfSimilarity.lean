/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-!
# Round 16 (Issue #232) — SMOOTH-DOMAIN SELF-SIMILARITY: the list-size function is monotone along
# the divisor lattice of the evaluation subgroup, at fixed rate and fixed relative radius

A structural theorem **specific to the smooth (multiplicative-subgroup) domains the prize fixes** —
it uses the subgroup structure essentially and fails for generic evaluation sets.

Let `ζ` be a primitive `(s·e)`-th root of unity in `F`, so the scale-`n` domain (`n = s·e`) is
`μ_n = {ζ^i}` and the scale-`s` domain is `μ_s = {(ζ^e)^j}`. The power map `x ↦ x^e` maps `μ_n`
onto `μ_s` with **uniform fibers of size `e`**, and `Polynomial.expand F e` (`g ↦ g(X^e)`) lifts
degree-`< k'` polynomials to degree-`< k'·e` polynomials with

  `agreement_n(expand g, w ∘ π) = e · agreement_s(g, w)`     (`π` = the index fiber map).

Hence the lift **injects the scale-`s` list into the scale-`n` list at the same rate
`ρ = k'/s = (k'e)/(se)` and the same relative agreement `a/s = (ea)/(es)`**:

  `listSize_s(ρ, δ) ≤ listSize_n(ρ, δ)`   for every `s ∣ n` (headline `selfsimilar_list_le`).

## Consequences for the prize (#232)

* **Monotonicity along the divisor lattice.** For the prize family (`n = 2^m`), the worst-case
  list size at fixed `(ρ, δ)` is monotone non-decreasing in `m`. Every small-scale verified
  interior data point (the in-tree δ*-table: exact interior lists at `n = 8, 16`) lifts to a
  verified lower bound at full prize scale `n = 2^20, …` over any field containing `μ_n`.
* **A constraint on future upper bounds.** Any proof of a beyond-Johnson list cap for scale `n`
  must respect all divisor scales simultaneously — the cap at scale `n` implies the cap at every
  `s ∣ n`. Upper-bound strategies that would "use the size of `n`" against a fixed `(ρ, δ)` are
  structurally constrained by the embedded small scales.
* The reduction is **rate- and radius-preserving**: self-similarity does not move `δ` relative to
  the gap `(1−√ρ, 1−ρ)`, so it transfers data *within* the gap but cannot by itself decide `δ*`
  (honest scope).

Everything is self-contained over Mathlib (`Polynomial.expand`, `IsPrimitiveRoot`).
-/

open Polynomial Finset

namespace Round16SelfSimilar

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. The two domains and the fiber map -/

/-- Scale-`n` domain (`n = s·e`): `i ↦ ζ^i`. -/
def domN (ζ : F) (s e : ℕ) : Fin (s * e) → F := fun i => ζ ^ (i : ℕ)

/-- Scale-`s` domain: `j ↦ (ζ^e)^j` (powers of the primitive `s`-th root `ζ^e`). -/
def domS (ζ : F) (e : ℕ) (s : ℕ) : Fin s → F := fun j => (ζ ^ e) ^ (j : ℕ)

/-- The index fiber map `π : Fin (s·e) → Fin s`, `i ↦ i % s` (the index-level power map). -/
def proj (s e : ℕ) (hs : 0 < s) : Fin (s * e) → Fin s :=
  fun i => ⟨(i : ℕ) % s, Nat.mod_lt _ hs⟩

omit [DecidableEq F] in
/-- **Power-map compatibility:** `(ζ^i)^e = (ζ^e)^{i % s}` on `μ_{s·e}` — the `e`-th power map
sends the scale-`n` domain onto the scale-`s` domain along `π`. -/
theorem domN_pow_e {ζ : F} {s e : ℕ} (hs : 0 < s) (hζ : ζ ^ (s * e) = 1) (i : Fin (s * e)) :
    (domN ζ s e i) ^ e = domS ζ e s (proj s e hs i) := by
  unfold domN domS proj
  simp only
  rw [← pow_mul, ← pow_mul]
  -- ζ^{i·e} = ζ^{e·(i % s)}: write i = s·(i/s) + i%s and kill the s·e block with hζ.
  have key : (i : ℕ) * e = (s * e) * ((i : ℕ) / s) + ((i : ℕ) % s) * e := by
    conv_lhs => rw [← Nat.div_add_mod (i : ℕ) s]
    ring
  calc ζ ^ ((i : ℕ) * e)
      = ζ ^ ((s * e) * ((i : ℕ) / s) + ((i : ℕ) % s) * e) := by rw [key]
    _ = (ζ ^ (s * e)) ^ ((i : ℕ) / s) * ζ ^ (((i : ℕ) % s) * e) := by
        rw [pow_add, pow_mul]
    _ = ζ ^ ((i : ℕ) % s * e) := by rw [hζ, one_pow, one_mul]
    _ = ζ ^ (e * ((i : ℕ) % s)) := by rw [Nat.mul_comm]

/-- **Uniform fibers:** each `j : Fin s` has exactly `e` preimages under `π`. -/
theorem card_fiber_proj {s e : ℕ} (hs : 0 < s) (j : Fin s) :
    ((Finset.univ : Finset (Fin (s * e))).filter (fun i => proj s e hs i = j)).card = e := by
  classical
  have hse : ∀ l : ℕ, l < e → (j : ℕ) + s * l < s * e := by
    intro l hl
    have h1 : s * l + s ≤ s * e := by
      have : l + 1 ≤ e := hl
      calc s * l + s = s * (l + 1) := by ring
        _ ≤ s * e := Nat.mul_le_mul_left _ this
    omega
  have hdiv : ∀ i : Fin (s * e), (i : ℕ) / s < e := fun i => Nat.div_lt_of_lt_mul i.2
  have huniv : (Finset.univ : Finset (Fin e)).card = e := by simp
  refine Eq.trans ?_ huniv
  apply Finset.card_nbij' (fun (i : Fin (s * e)) => (⟨(i : ℕ) / s, hdiv i⟩ : Fin e))
    (fun (l : Fin e) => (⟨(j : ℕ) + s * (l : ℕ), hse (l : ℕ) l.2⟩ : Fin (s * e)))
  · intro i _
    exact Finset.mem_coe.mpr (Finset.mem_univ _)
  · intro l _
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    unfold proj
    ext
    simp only
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt j.2
  · -- left inverse: i ↦ i/s ↦ j + s·(i/s) = i, using i % s = j on the fiber
    intro i hi
    have hi' := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
    have hmod : (i : ℕ) % s = (j : ℕ) := by
      have h2 := hi'.2
      unfold proj at h2
      exact congrArg Fin.val h2
    have hdm := Nat.div_add_mod (i : ℕ) s
    ext
    simp only
    omega
  · -- right inverse: l ↦ j + s·l ↦ (j + s·l)/s = l
    intro l _
    ext
    simp only
    rw [Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt j.2, Nat.zero_add]

/-! ## 2. Agreement multiplies by `e` under `expand` -/

/-- Agreement count of a polynomial `g` with a word `w` over a domain `D`. -/
def agreement {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ι → F) (g : F[X]) (w : ι → F) : ℕ :=
  ((Finset.univ : Finset ι).filter (fun i => g.eval (D i) = w i)).card

/-- **Agreement lifts multiplicatively:** `agreement_n(expand_e g, w∘π) = e · agreement_s(g, w)`.
Each scale-`s` agreement point fans out to its full `e`-point fiber (and non-agreements likewise),
because `(expand F e g).eval(ζ^i) = g.eval((ζ^i)^e) = g.eval(domS (π i))`. -/
theorem agreement_expand {ζ : F} {s e : ℕ} (hs : 0 < s)
    (hζ : ζ ^ (s * e) = 1) (g : F[X]) (w : Fin s → F) :
    agreement (domN ζ s e) (expand F e g) (w ∘ proj s e hs) = e * agreement (domS ζ e s) g w := by
  classical
  unfold agreement
  -- rewrite the scale-n predicate through the fiber map.
  have hpred : ∀ i : Fin (s * e),
      ((expand F e g).eval (domN ζ s e i) = (w ∘ proj s e hs) i)
        ↔ (g.eval (domS ζ e s (proj s e hs i)) = w (proj s e hs i)) := by
    intro i
    rw [Function.comp_apply, expand_eval, domN_pow_e hs hζ i]
  rw [Finset.filter_congr (fun i _ => by rw [hpred i])]
  -- count fiberwise over the scale-s agreement set.
  rw [Finset.card_eq_sum_card_fiberwise
      (f := proj s e hs)
      (t := (Finset.univ : Finset (Fin s)).filter (fun j => g.eval (domS ζ e s j) = w j))
      (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)]
  -- each fiber over an agreement point has size e.
  rw [Finset.sum_congr rfl (fun j hj => ?_), Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  -- the inner filter is exactly the proj-fiber of j (the agreement condition is constant on it).
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  have : (Finset.univ.filter (fun i => g.eval (domS ζ e s (proj s e hs i)) = w (proj s e hs i))).filter
      (fun i => proj s e hs i = j)
      = Finset.univ.filter (fun i => proj s e hs i = j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h2⟩; exact h2
    · intro h2; rw [h2]; exact ⟨hj, rfl⟩
  rw [this, card_fiber_proj hs j]

/-! ## 3. The headline: the scale-`s` list injects into the scale-`n` list -/

/-- The list (as a finset of coefficient tuples): degree-`< k` polynomials, encoded by their
coefficient tuples `c : Fin k → F` via `∑ᵢ c i · Xⁱ`, whose agreement with `w` is `≥ a`. -/
noncomputable def polyOfCoeffs {k : ℕ} (c : Fin k → F) : F[X] :=
  ∑ i : Fin k, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)

omit [DecidableEq F] in
theorem coeff_polyOfCoeffs {k : ℕ} (c : Fin k → F) (m : ℕ) :
    (polyOfCoeffs c).coeff m = if h : m < k then c ⟨m, h⟩ else 0 := by
  classical
  unfold polyOfCoeffs
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases h : m < k
  · rw [dif_pos h, Finset.sum_eq_single (⟨m, h⟩ : Fin k)]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hmb
      exact hb (by ext; simp [hmb])
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro hmi
    exact h (hmi ▸ i.2)

/-- The lifted coefficient tuple: spreads `c` onto indices divisible by `e`. -/
def liftCoef {k' : ℕ} (e : ℕ) (c : Fin k' → F) : Fin (k' * e) → F :=
  fun i => if h : e ∣ (i : ℕ) ∧ (i : ℕ) / e < k' then c ⟨(i : ℕ) / e, h.2⟩ else 0

omit [DecidableEq F] in
/-- `polyOfCoeffs (liftCoef c) = expand F e (polyOfCoeffs c)` — the coefficient encoding commutes
with the expansion. -/
theorem polyOfCoeffs_liftCoef {k' e : ℕ} (he : 0 < e) (c : Fin k' → F) :
    polyOfCoeffs (liftCoef e c) = expand F e (polyOfCoeffs c) := by
  classical
  ext m
  rw [coeff_polyOfCoeffs, Polynomial.coeff_expand he, coeff_polyOfCoeffs]
  by_cases hdvd : e ∣ m
  · rw [if_pos hdvd]
    by_cases hm : m < k' * e
    · rw [dif_pos hm]
      have hdiv : m / e < k' := by
        obtain ⟨c', rfl⟩ := hdvd
        rw [Nat.mul_div_cancel_left _ he]
        rw [Nat.mul_comm] at hm
        exact Nat.lt_of_mul_lt_mul_right hm
      rw [dif_pos hdiv]
      unfold liftCoef
      rw [dif_pos ⟨hdvd, hdiv⟩]
    · rw [dif_neg hm]
      have : ¬ (m / e < k') := by
        intro hdiv
        apply hm
        obtain ⟨c', rfl⟩ := hdvd
        rw [Nat.mul_div_cancel_left _ he] at hdiv
        calc e * c' < e * k' := (Nat.mul_lt_mul_left he).mpr hdiv
          _ = k' * e := Nat.mul_comm _ _
      rw [dif_neg this]
  · rw [if_neg hdvd]
    by_cases hm : m < k' * e
    · rw [dif_pos hm]
      unfold liftCoef
      rw [dif_neg (fun hh => hdvd hh.1)]
    · rw [dif_neg hm]

omit [DecidableEq F] in
/-- `liftCoef` is injective (read back `c j` at index `e·j`). -/
theorem liftCoef_injective {k' e : ℕ} (he : 0 < e) :
    Function.Injective (liftCoef (k' := k') e (F := F)) := by
  intro c c' h
  funext j
  have hj : (j : ℕ) * e < k' * e := (Nat.mul_lt_mul_right he).mpr j.2
  have := congrFun h ⟨(j : ℕ) * e, hj⟩
  unfold liftCoef at this
  have hcond : e ∣ ((j : ℕ) * e) ∧ ((j : ℕ) * e) / e < k' := by
    refine ⟨dvd_mul_left e _, ?_⟩
    rw [Nat.mul_div_cancel _ he]
    exact j.2
  rw [dif_pos hcond, dif_pos hcond] at this
  have hidx : (⟨((j : ℕ) * e) / e, hcond.2⟩ : Fin k') = j := by
    ext; simp [Nat.mul_div_cancel _ he]
  rwa [hidx] at this

/-- The scale-`s` (resp. scale-`n`) list finset: coefficient tuples with agreement `≥ a`. -/
noncomputable def listFinset {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype F]
    (D : ι → F) (w : ι → F) (k a : ℕ) : Finset (Fin k → F) :=
  Finset.univ.filter (fun c => a ≤ agreement D (polyOfCoeffs c) w)

/-- **HEADLINE — smooth-domain self-similarity.** For `ζ` with `ζ^{s·e} = 1` and any scale-`s`
received word `w`, threshold `a`: the scale-`s` list injects into the scale-`n` list (`n = s·e`)
at degree bound `k'·e` and agreement threshold `e·a` — the same rate `k'/s = k'e/(se)` and the
same relative agreement `a/s = ea/(se)`:

  `listSize_s(w, a) ≤ listSize_n(w∘π, e·a)`.

The smooth-domain list-size function is monotone non-decreasing along the divisor lattice of the
evaluation subgroup, at fixed rate and fixed relative radius. -/
theorem selfsimilar_list_le [Fintype F] {ζ : F} {s e k' : ℕ}
    (hs : 0 < s) (he : 0 < e) (hζ : ζ ^ (s * e) = 1) (w : Fin s → F) (a : ℕ) :
    (listFinset (domS ζ e s) w k' a).card
      ≤ (listFinset (domN ζ s e) (w ∘ proj s e hs) (k' * e) (e * a)).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun c => liftCoef e c)
  · intro c hc
    simp only [listFinset, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rw [polyOfCoeffs_liftCoef he c, agreement_expand hs hζ]
    exact Nat.mul_le_mul_left e hc
  · intro c _ c' _ h
    exact liftCoef_injective he h

end Round16SelfSimilar

#print axioms Round16SelfSimilar.domN_pow_e
#print axioms Round16SelfSimilar.card_fiber_proj
#print axioms Round16SelfSimilar.agreement_expand
#print axioms Round16SelfSimilar.polyOfCoeffs_liftCoef
#print axioms Round16SelfSimilar.liftCoef_injective
#print axioms Round16SelfSimilar.selfsimilar_list_le
