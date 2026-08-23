/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.Connections.ListDecodingAndCA
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# CS25 "Claim 3" deep-hole construction — the concrete polynomial-algebra bricks

This file formalizes the *concrete, definition-internal* part of the [CS25]
(Crites–Stewart, eprint 2025/2046) Theorem 2 "Claim 3" deep-hole construction — the part
that **is** manufacturable from the in-tree `ReedSolomon.code` / `degreeLT` /
`relHammingDist` definitions. It supplies the algebraic bricks consumed by the
`hDeepHole` residual surfaced in `ArkLib.ToMathlib.CS25Claim3`.

## The construction (informal, CS25 Claim 3)

Fix an evaluation embedding `domain : ι ↪ F` and a "deep hole" point `a : F` outside the
image of `domain`. For a received word `u : ι → F`, set the *deep-hole word* and its scaling

  `u⁰_i = u_i / (xᵢ − a)`,   `u¹_i = −1 / (xᵢ − a)`,   where `xᵢ := domain i`,

and consider, for a field element `z`, the line point `w_z := u⁰ − z • u¹`, i.e.
`w_z i = (u_i + z) / (xᵢ − a)`.

The key remainder-theorem identity: for a polynomial `p` of degree `< k + 1`, writing
`q := p /ₘ (X − C a)` (degree `< k`), Mathlib's `modByMonic_add_div` gives
`p = (X − C a) · q + C (p.eval a)`, hence for every `x`

  `p.eval x − p.eval a = (x − a) · q.eval x`.                                  (★)

Therefore, with combiner `z = −p.eval a`, on every coordinate `i`

  `w_{−p.eval a} i = (u_i − p.eval a) / (xᵢ − a)`,

and `w_{−p.eval a} i = q.eval xᵢ` **exactly when** `u_i = p.eval xᵢ` (using `xᵢ ≠ a`, true
because `a ∉ range domain`). So the disagreement set of the RS[k] line point `w_{−p.eval a}`
against the RS[k] codeword `q` is **identical** to the disagreement set of `u` against the
RS[k+1] codeword `p`. Hence the relative Hamming distance is preserved:

  `δᵣ(w_{−p.eval a}, q-as-codeword) = δᵣ(u, p-as-codeword)`.

(The injective map `p ↦ −p.eval a` preserves the distinct-value count, so distinct values
`p^{(j)}.eval a` still give distinct combiners `z`.)

This is what turns each distinct value `p^{(j)}.eval a` into a distinct `z` with `w_z`
`δ`-close to `RS[k]`, which is the geometric input to the `epsCA` probability bound.

## What is proven here (all `sorry`-free)

- `lineQuotient` — the quotient `p /ₘ (X − C a)`.
- `lineQuotient_mem_degreeLT` — **(brick 2, degree):** `deg p < k+1 ⇒ deg (lineQuotient p a) < k`.
- `eval_sub_eval_eq` — identity (★): `p.eval x − p.eval a = (x − a) · (lineQuotient p a).eval x`.
- `lineQuotient_eval_eq_div` — **(brick 2):** for `x ≠ a`,
  `(lineQuotient p a).eval x = (p.eval x − p.eval a) / (x − a)`.
- `deepHoleLine` — the line point `w_z i = (u i + z) / (domain i − a)`.
- `deepHoleLine_eval_eq_iff` — **(brick 3, coordinate):** at `z = −p.eval a`,
  `w_z i = (lineQuotient p a).eval (domain i) ↔ u i = p.eval (domain i)`.
- `deepHoleLine_agree_set_eq` — **(brick 3):** the agreement (hence disagreement) sets coincide.
- `relHammingDist_deepHoleLine_eq` — **(brick 3, distance):** the relative Hamming distances
  coincide, so RS[k+1]-closeness of `u` to `p` transfers to RS[k]-closeness of `w_{−p.eval a}`.
- `lineQuotient_mem_RScode` — `lineQuotient p a` evaluates into `RS[k]` when `deg p < k+1`.

## What is *not* here

The remaining step — turning "each distinct `p^{(j)}.eval a` gives an RS[k]-close line point"
into the probability bound `numDistinct ≤ ε·q` via `epsCA`'s PMF semantics and the
minimum-distance joint-far side condition — is the genuinely external probabilistic content
and stays surfaced as the `hDeepHole` hypothesis in `CS25Claim3.lean`.

## References

- [CS25] Crites, Stewart. *On Reed–Solomon Proximity Gaps Conjectures*. eprint 2025/2046,
  Theorem 2, Claim 3.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CodingTheory.CS25.DeepHole

open Polynomial

variable {F : Type} [Field F] [DecidableEq F]

/-! ### Brick 2 — the remainder-theorem line quotient -/

/-- The **line quotient** `p /ₘ (X − C a)`. By the remainder theorem this is the degree-`< k`
polynomial `q` with `p = (X − C a)·q + C (p.eval a)`; its evaluation at `x ≠ a` is the
"slope" `(p.eval x − p.eval a)/(x − a)`. -/
noncomputable def lineQuotient (p : F[X]) (a : F) : F[X] := p /ₘ (X - C a)

/-- **(★) Remainder identity.** `p.eval x − p.eval a = (x − a) · (lineQuotient p a).eval x`. -/
theorem eval_sub_eval_eq (p : F[X]) (a x : F) :
    p.eval x - p.eval a = (x - a) * (lineQuotient p a).eval x := by
  unfold lineQuotient
  -- p = (X - C a) * (p /ₘ (X - C a)) + C (p.eval a)   (remainder theorem at a monic linear)
  have hpe : p = (X - C a) * (p /ₘ (X - C a)) + C (p.eval a) := by
    conv_lhs => rw [← modByMonic_add_div p (X - C a)]
    rw [modByMonic_X_sub_C_eq_C_eval]; ring
  -- evaluate both sides at x
  have hcg := congrArg (fun q => Polynomial.eval x q) hpe
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C] at hcg
  -- hcg : p.eval x = (x - a) * (p /ₘ (X - C a)).eval x + p.eval a
  rw [hcg]; ring

/-- **Brick 2 (slope form).** For `x ≠ a`,
`(lineQuotient p a).eval x = (p.eval x − p.eval a) / (x − a)`. -/
theorem lineQuotient_eval_eq_div (p : F[X]) {a x : F} (hxa : x ≠ a) :
    (lineQuotient p a).eval x = (p.eval x - p.eval a) / (x - a) := by
  have hne : x - a ≠ 0 := sub_ne_zero.mpr hxa
  rw [eval_sub_eval_eq p a x]
  field_simp

/-- **Brick 2 (degree).** The line quotient drops the degree by one: if `deg p < k + 1`
then `deg (lineQuotient p a) < k`. -/
theorem lineQuotient_mem_degreeLT {p : F[X]} {a : F} {k : ℕ}
    (hp : p ∈ Polynomial.degreeLT F (k + 1)) :
    lineQuotient p a ∈ Polynomial.degreeLT F k := by
  classical
  unfold lineQuotient
  by_cases hp0 : p = 0
  · simp only [hp0, zero_divByMonic]
    exact Submodule.zero_mem _
  -- natDegree of quotient is natDegree p - 1 < k.
  rw [Polynomial.mem_degreeLT] at hp ⊢
  -- p ≠ 0, so its degree is its natDegree.
  have hpdeg : (p.natDegree : ℕ) < k + 1 := by
    rw [Polynomial.degree_eq_natDegree hp0] at hp
    exact_mod_cast hp
  rcases eq_or_ne (p /ₘ (X - C a)) 0 with hq | hq
  · rw [hq, Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (by simp)
  · rw [Polynomial.degree_eq_natDegree hq]
    have hnd : (p /ₘ (X - C a)).natDegree = p.natDegree - 1 := by
      rw [Polynomial.natDegree_divByMonic p (monic_X_sub_C a), Polynomial.natDegree_X_sub_C]
    -- nonzero quotient forces `1 ≤ natDegree p` (else `degree p < degree (X−C a)`).
    have h1 : 1 ≤ p.natDegree := by
      have hdeg_le : (X - C a).degree ≤ p.degree := by
        by_contra hlt
        rw [not_le] at hlt
        exact hq ((divByMonic_eq_zero_iff (monic_X_sub_C a)).mpr hlt)
      rw [Polynomial.degree_X_sub_C, Polynomial.degree_eq_natDegree hp0] at hdeg_le
      exact_mod_cast hdeg_le
    rw [hnd]
    have : p.natDegree - 1 < k := by omega
    exact_mod_cast this

/-- **Brick 2 (RS membership).** The line quotient of a degree-`< k+1` polynomial evaluates
into `RS[k]`: `evalOnPoints domain (lineQuotient p a) ∈ ReedSolomon.code domain k`. -/
theorem lineQuotient_mem_RScode
    {ι : Type} [Fintype ι] {p : F[X]} {a : F} {k : ℕ}
    (domain : ι ↪ F) (hp : p ∈ Polynomial.degreeLT F (k + 1)) :
    ReedSolomon.evalOnPoints domain (lineQuotient p a)
      ∈ (ReedSolomon.code domain k : Set (ι → F)) := by
  refine ⟨lineQuotient p a, lineQuotient_mem_degreeLT hp, rfl⟩

/-! ### Brick 3 — the deep-hole line point and closeness transfer -/

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-- The **deep-hole line point** `w_z` of a received word `u` at hole `a` with combiner `z`:
`w_z i = (u i + z) / (domain i − a)`.  (This is `u⁰ − z • u¹` for the CS25 deep-hole pair
`u⁰_i = u_i/(xᵢ−a)`, `u¹_i = −1/(xᵢ−a)`.) -/
noncomputable def deepHoleLine (domain : ι ↪ F) (u : ι → F) (a z : F) : ι → F :=
  fun i => (u i + z) / (domain i - a)

/-- **Brick 3 (coordinate identity).**  When the hole `a` is outside the evaluation domain
(so `domain i ≠ a`), the deep-hole line point at combiner `z = −p.eval a` equals the RS[k]
codeword `evalOnPoints domain (lineQuotient p a)` on coordinate `i` **iff** `u` agrees with
`p` there.  (The CS25 combiner is `z = −p.eval a`: with `w_z i = (u_i + z)/(xᵢ−a)` and the
slope `q.eval xᵢ = (p.eval xᵢ − p.eval a)/(xᵢ−a)`, equality at `u_i = p.eval xᵢ` forces
`z = −p.eval a`.)  This is the per-coordinate heart of the disagreement-set preservation. -/
theorem deepHoleLine_eval_eq_iff
    (domain : ι ↪ F) (u : ι → F) (a : F) (p : F[X]) (i : ι)
    (hai : domain i ≠ a) :
    deepHoleLine domain u a (-(p.eval a)) i
        = ReedSolomon.evalOnPoints domain (lineQuotient p a) i
      ↔ u i = p.eval (domain i) := by
  have hne : domain i - a ≠ 0 := sub_ne_zero.mpr hai
  -- RHS coordinate is the slope `(p.eval xᵢ − p.eval a)/(xᵢ − a)`.
  have hrhs : ReedSolomon.evalOnPoints domain (lineQuotient p a) i
      = (p.eval (domain i) - p.eval a) / (domain i - a) := by
    change (lineQuotient p a).eval (domain i) = _
    exact lineQuotient_eval_eq_div p hai
  rw [deepHoleLine, hrhs]
  rw [div_eq_div_iff hne hne]
  constructor
  · intro h
    -- (u i + (−p.eval a))*(xᵢ−a) = (p.eval xᵢ − p.eval a)*(xᵢ−a) ⇒ cancel.
    have hcanc := mul_right_cancel₀ hne h
    linear_combination hcanc
  · intro h
    rw [h]; ring

/-- **Brick 3 (agreement-set equality).**  Off the domain hole `a`, the set of coordinates on
which the deep-hole line point `w_{-p.eval a}` agrees with the RS[k] codeword
`evalOnPoints domain (lineQuotient p a)` equals the set on which `u` agrees with `p`. -/
theorem deepHoleLine_agree_set_eq
    (domain : ι ↪ F) (u : ι → F) (a : F) (p : F[X])
    (hdom : ∀ i, domain i ≠ a) :
    {i | deepHoleLine domain u a (-(p.eval a)) i
          = ReedSolomon.evalOnPoints domain (lineQuotient p a) i}
      = {i | u i = p.eval (domain i)} := by
  ext i
  exact deepHoleLine_eval_eq_iff domain u a p i (hdom i)

/-- **Brick 3 (Hamming distance preserved).**  The Hamming distance from the deep-hole line
point to the RS[k] codeword equals the Hamming distance from `u` to the RS[k+1] codeword
`evalOnPoints domain p`. -/
theorem hammingDist_deepHoleLine_eq
    (domain : ι ↪ F) (u : ι → F) (a : F) (p : F[X])
    (hdom : ∀ i, domain i ≠ a) :
    hammingDist (deepHoleLine domain u a (-(p.eval a)))
        (ReedSolomon.evalOnPoints domain (lineQuotient p a))
      = hammingDist u (ReedSolomon.evalOnPoints domain p) := by
  classical
  unfold hammingDist
  apply Finset.card_bij (fun i _ => i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro hcon
    exact hi ((deepHoleLine_eval_eq_iff domain u a p i (hdom i)).mpr hcon)
  · intro i _ j _ h; exact h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨i, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hcon
    exact hi ((deepHoleLine_eval_eq_iff domain u a p i (hdom i)).mp hcon)

/-- **Brick 3 (relative distance preserved).**  Consequently the relative Hamming distances
coincide: `δᵣ(w_{-p.eval a}, lineQuotient-codeword) = δᵣ(u, p-codeword)`.  This is the exact
sense in which RS[k+1]-closeness of `u` to `p` transfers to RS[k]-closeness of the deep-hole
line point — turning each distinct value `p.eval a` into a `z` whose line point is `δ`-close
to `RS[k]`. -/
theorem relHammingDist_deepHoleLine_eq
    (domain : ι ↪ F) (u : ι → F) (a : F) (p : F[X])
    (hdom : ∀ i, domain i ≠ a) :
    Code.relHammingDist (deepHoleLine domain u a (-(p.eval a)))
        (ReedSolomon.evalOnPoints domain (lineQuotient p a))
      = Code.relHammingDist u (ReedSolomon.evalOnPoints domain p) := by
  unfold Code.relHammingDist
  rw [hammingDist_deepHoleLine_eq domain u a p hdom]

end CodingTheory.CS25.DeepHole
