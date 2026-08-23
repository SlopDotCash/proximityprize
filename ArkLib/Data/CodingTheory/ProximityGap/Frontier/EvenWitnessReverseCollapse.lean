/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.EvenDirectionDescent

/-!
# Fibre-symmetric reverse even-direction collapse (#407) — `collapse-via-iff`

Attacks the named open `Prop`
`ProximityGap.FarCosetExplosion.EvenDirectionIncidenceCollapse`
(reverse leg of the 2-adic even–odd descent, `I_n ≤ I_{n/2}` for the even direction `x^{2a'}`).

## What the numerics force (honest picture)

The UNCONDITIONAL reverse collapse is **FALSE** (machine-checked countermodel,
`probe_farline_incidence_exact`, `n=16, k=2, code dim 2k=4`, even offset `a=10`, even direction
`b=4`, rung `r=10`): `I_n = 89 > I_{n/2} = 25`, i.e. **64 excess scalars** are bad on `μ_16`
(even-pullback line) but NOT on `μ_8`.  So `EvenDirectionIncidenceCollapse` is refuted as stated;
the odd part genuinely adds incidence.  But the excess is structurally pinned:

* `f : μ_n → μ_{n/2}, x ↦ x²` is exactly 2-to-1, fibres the antipodal pairs `{x, −x}`;
* all 64 excess scalars have ONLY **fibre-asymmetric** witness sets;
* every scalar that DESCENDS has a **fibre-symmetric** (negation-closed) witness set.

Mechanism (`char ≠ 2`-exact): on a fibre-symmetric witness `S = f⁻¹(S')` the line value `r'∘f`
is fibre-constant, so the witnessing codeword `w = eval p` (deg `p < 2k`) satisfies `p(x)=p(−x)`
on `S`; its **even part** `q(x²)` (deg `q < k`) agrees with `r'` on `S' = f(S)`.

## What this brick proves

`explainableScalars_sq_pullback_reverse_of_evenWitness`: a scalar `γ` bad for the even-pullback
line `(u₀'∘f, u₁'∘f)` against `RS[μ_n, 2k]` **with a fibre-symmetric witness** descends — it is
bad for `(u₀', u₁')` against `RS[μ_{n/2}, k]`.  References the REAL in-tree `explainableScalars`,
`ReedSolomon.code`, `evalOnPoints`, and the squaring index map `f` of `EvenDirectionDescent`.

The crux is the even-part factorization `even_eval_eq_evenHalf` (Mathlib lacks it).

Axiom-clean target: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.FarCosetExplosion

variable {ι ι' : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  [Fintype ι'] [Nonempty ι'] [DecidableEq ι']
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Part 1 — the even-part polynomial and the value identity. -/

/-- **Even half of a polynomial.**  `evenHalf k p = ∑_{i<k} p.coeff (2*i) • X^i`, so that evaluating
at `x²` recovers the even-degree part of `p.eval x`. -/
noncomputable def evenHalf (k : ℕ) (p : F[X]) : F[X] :=
  ∑ i ∈ Finset.range k, Polynomial.C (p.coeff (2 * i)) * X ^ i

/-- The even half has degree `< k`. -/
theorem evenHalf_degree_lt (k : ℕ) (p : F[X]) :
    (evenHalf k p).degree < (k : WithBot ℕ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [evenHalf]
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (a := (k : WithBot ℕ)) (bot_lt_iff_ne_bot.mpr (WithBot.coe_ne_bot))]
  intro i hi
  rw [Finset.mem_range] at hi
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le i (p.coeff (2 * i))) ?_
  exact_mod_cast hi

/-- **Even half evaluates to the even part at a square.**  For any `x`,
`(evenHalf k p).eval (x²) = ∑_{i<k} p.coeff (2*i) * x^(2*i)` — the even-degree slice of `p.eval x`. -/
theorem evenHalf_eval_sq (k : ℕ) (p : F[X]) (x : F) :
    (evenHalf k p).eval (x ^ 2) = ∑ i ∈ Finset.range k, p.coeff (2 * i) * x ^ (2 * i) := by
  rw [evenHalf, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    ← pow_mul]

/-- **Pairing a `range (2k)` sum into `k` consecutive pairs.**  `∑_{j<2k} g j = ∑_{i<k} (g(2i)+g(2i+1))`. -/
theorem sum_range_two_mul_pair {M : Type*} [AddCommMonoid M] (g : ℕ → M) (k : ℕ) :
    ∑ j ∈ Finset.range (2 * k), g j = ∑ i ∈ Finset.range k, (g (2 * i) + g (2 * i + 1)) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, show 2 * (n + 1) = (2 * n + 1) + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]

/-- **Even half at a square = the symmetrised average of `p`.**  For a polynomial `p` of degree
`< 2k`, `(evenHalf k p).eval (x²) = (p.eval x + p.eval (−x)) / 2`.  Even-degree terms are their own
symmetrisation; odd-degree terms cancel.  Needs only `2 ≠ 0`. -/
theorem evenHalf_eval_sq_eq_avg [NeZero (2 : F)] {k : ℕ} {p : F[X]} (hp : p.natDegree < 2 * k)
    (x : F) :
    (evenHalf k p).eval (x ^ 2) = (p.eval x + p.eval (-x)) / 2 := by
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  rw [eq_div_iff h2]
  rw [evenHalf_eval_sq, Polynomial.eval_eq_sum_range' hp x, Polynomial.eval_eq_sum_range' hp (-x),
    ← Finset.sum_add_distrib]
  rw [sum_range_two_mul_pair (fun j => p.coeff j * x ^ j + p.coeff j * (-x) ^ j) k,
    Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have heven : (-x) ^ (2 * i) = x ^ (2 * i) := by
    rw [neg_pow, Even.neg_one_pow ⟨i, by ring⟩, one_mul]
  have hodd : (-x) ^ (2 * i + 1) = - x ^ (2 * i + 1) :=
    Odd.neg_pow ⟨i, rfl⟩ x
  simp only [heven, hodd]
  ring

/-- **The KEY value identity.**  If `p` (deg `< 2k`) is *even at `x`* — `p.eval x = p.eval (−x)` —
then its even half recovers it: `(evenHalf k p).eval (x²) = p.eval x`. -/
theorem even_eval_eq_evenHalf [NeZero (2 : F)] {k : ℕ} {p : F[X]} (hp : p.natDegree < 2 * k)
    {x : F} (hx : p.eval x = p.eval (-x)) :
    (evenHalf k p).eval (x ^ 2) = p.eval x := by
  rw [evenHalf_eval_sq_eq_avg hp, ← hx]
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  field_simp
  ring

/-! ## Part 2 — the descended codeword on `RS[μ_{n/2}, k]`. -/

/-- **The even half of a witnessing codeword descends to `RS[μ_{n/2}, k]`.**  If `w = eval p`
(`p ∈ degreeLT (2k)`) is the witnessing `RS[domain, 2k]` codeword and `g : ι' → F` is the function
sending `y` to `(evenHalf k p).eval y`, then `g ∈ RS[domain', k]`.  (Pure even-part of the codeword;
references the REAL `ReedSolomon.code` / `evalOnPoints`.) -/
theorem evenHalf_mem_code (domain' : ι' ↪ F) (k : ℕ) {p : F[X]} (hp : p.degree < (2 * k : ℕ)) :
    (fun y : ι' => (evenHalf k p).eval (domain' y)) ∈ ReedSolomon.code domain' k := by
  rw [ReedSolomon.mem_code_iff_exists_polynomial]
  exact ⟨evenHalf k p, evenHalf_degree_lt k p, rfl⟩

/-! ## Part 3 — the fibre-symmetric reverse collapse on the REAL `explainableScalars`. -/

open Classical in
/-- **Fibre-symmetric reverse even-direction collapse (the real, conditional `I_n ≤ I_{n/2}`).**
Let `f : ι → ι'` realize the squaring map `domain' (f i) = (domain i)²` and let `neg : ι → ι`
realize negation on the domain (`domain (neg i) = − domain i`) compatibly with `f`
(`f (neg i) = f i`, i.e. `neg` permutes fibres of `f`).  Suppose `char F ≠ 2`.

If a scalar `γ` is bad for the even-pullback line `(u₀'∘f, u₁'∘f)` against `RS[domain, 2k]`
**with a fibre-symmetric witness** — a witness set of the form `f⁻¹(S')` (`= {i : f i ∈ S'}`) that
meets the full radius and on which the half-radius is met for `S'` — then `γ` is bad for
`(u₀', u₁')` against `RS[domain', k]`.

This is the proved reverse leg of `EvenDirectionIncidenceCollapse`, conditioned on the witness
being fibre-symmetric (which the numerics show is exactly the descending case; the non-symmetric
witnesses are the genuine odd-part excess that makes the *unconditional* collapse false). -/
theorem explainableScalars_sq_pullback_reverse_of_evenWitness [NeZero (2 : F)]
    (domain : ι ↪ F) (domain' : ι' ↪ F) (k : ℕ) (hk : 0 < k) (f : ι → ι') (neg : ι → ι)
    (hf : ∀ i, domain' (f i) = (domain i) ^ 2)
    (hsurj : ∀ y : ι', ∃ i : ι, f i = y)
    (hneg : ∀ i, domain (neg i) = - domain i)
    (hfneg : ∀ i, f (neg i) = f i)
    (δ δ' : ℝ≥0) (u₀' u₁' : ι' → F)
    {γ : F}
    -- `γ` is bad on `μ_n` for the even-pullback line, witnessed on a fibre-symmetric set `f⁻¹(S')`
    (S' : Finset ι')
    (hsz' : (S'.card : ℝ≥0) ≥ (1 - δ') * Fintype.card ι')
    (w : ι → F) (hwC : w ∈ ReedSolomon.code domain (2 * k))
    (hw : ∀ i ∈ (Finset.univ.filter (fun i : ι => f i ∈ S')), w i = (u₀' ∘ f) i + γ • (u₁' ∘ f) i) :
    γ ∈ explainableScalars (F := F) (ReedSolomon.code domain' k : Set (ι' → F)) δ' u₀' u₁' := by
  classical
  -- extract the witnessing polynomial of the full codeword
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hwC
  obtain ⟨p, hpdeg, hpeval⟩ := hwC
  -- `natDegree` form of the degree bound (needed for the even-part identity)
  have hpnd : p.natDegree < 2 * k := by
    rcases eq_or_ne p 0 with rfl | hp0
    · simpa only [Polynomial.natDegree_zero] using (by omega : 0 < 2 * k)
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hpdeg
  -- the descended codeword: even half of `p`, evaluated on `domain'`
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, S', hsz',
    (fun y : ι' => (evenHalf k p).eval (domain' y)),
    evenHalf_mem_code domain' k (by exact_mod_cast hpdeg), ?_⟩
  intro y hy
  -- pick a fibre representative `i` with `f i = y`; both `i` and `neg i` lie in the witness set.
  obtain ⟨i, hi⟩ := hsurj y
  -- both i and neg i are in the witness filter (the fibre-symmetric witness)
  have hiS : i ∈ Finset.univ.filter (fun i : ι => f i ∈ S') := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [hi]; exact hy⟩
  have hniS : neg i ∈ Finset.univ.filter (fun i : ι => f i ∈ S') := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [hfneg, hi]; exact hy⟩
  -- the line value on the fibre is constant: `(u₀'∘f + γ • u₁'∘f)` at `i` equals at `neg i`
  have hval_i := hw i hiS
  have hval_ni := hw (neg i) hniS
  have hline_eq : w (neg i) = w i := by
    rw [hval_i, hval_ni]
    simp only [Function.comp_apply, hfneg]
  -- translate to polynomial values: `w i = p.eval (domain i)`, `w (neg i) = p.eval (domain (neg i))`
  have hwi : w i = p.eval (domain i) := by
    rw [hpeval]; rfl
  have hwni : w (neg i) = p.eval (domain (neg i)) := by
    rw [hpeval]; rfl
  have hp_sym : p.eval (domain i) = p.eval (- domain i) := by
    rw [← hwi, ← hline_eq, hwni, hneg]
  -- even-part identity at `x = domain i`, and `domain' y = (domain i)²`
  have hkey : (evenHalf k p).eval ((domain i) ^ 2) = p.eval (domain i) :=
    even_eval_eq_evenHalf hpnd hp_sym
  -- `domain' y = (domain i)²` (since `f i = y`)
  have hdy : domain' y = (domain i) ^ 2 := by rw [← hi]; exact hf i
  -- assemble the agreement of the descended codeword with the half-line on `S'`
  show (evenHalf k p).eval (domain' y) = u₀' y + γ • u₁' y
  rw [hdy, hkey, hwi.symm, hval_i]
  simp only [Function.comp_apply, hi]

end ProximityGap.FarCosetExplosion

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.FarCosetExplosion.evenHalf_degree_lt
#print axioms ProximityGap.FarCosetExplosion.evenHalf_eval_sq
#print axioms ProximityGap.FarCosetExplosion.sum_range_two_mul_pair
#print axioms ProximityGap.FarCosetExplosion.evenHalf_eval_sq_eq_avg
#print axioms ProximityGap.FarCosetExplosion.even_eval_eq_evenHalf
#print axioms ProximityGap.FarCosetExplosion.evenHalf_mem_code
#print axioms ProximityGap.FarCosetExplosion.explainableScalars_sq_pullback_reverse_of_evenWitness
