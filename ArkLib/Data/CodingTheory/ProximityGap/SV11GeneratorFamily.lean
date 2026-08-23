/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WronskianNonVanishing

/-!
# The Garcia–Voloch / Shkredov–Vyugin Stepanov generator family has nonzero Wronskian (#389)

The Stepanov bound on `|R ∩ (R+c)|` (Garcia–Voloch / Heath-Brown–Konyagin, Shkredov–Vyugin
arXiv:1102.1172 Prop 3.2) is built from the generator family `g_{a,b}(X) = X^a · (X − c)^{t·b}`. To
run the method one must certify these generators are *linearly independent* — equivalently, that
their classical Wronskian is nonzero.

This file supplies that certificate by routing through the distinct-degree Wronskian non-vanishing
(`wronskianDet_ne_zero_of_distinctDeg`): `g_{a,b}` has `natDegree = a + t·b` (`sv11Gen_natDegree`),
and `(a,b) ↦ a + t·b` is **injective for `a < t`** (`add_mul_lt_injective`, a mod-`t` argument) — so
in the SV11 regime `D·B ≤ t` (where each `a < D ≤ t`) the family has distinct degrees, and the
Wronskian is nonzero (`sv11_wronskianDet_ne_zero`) in characteristic `0` or `> l−1`.

This is the connector between the non-vanishing certificate chain (`BinomialMatrixDet` →
`HasseWronskian{Monomial,Poly}` → `WronskianNonVanishing`) and the concrete Stepanov family. The one
remaining piece for the sharp `O(n^{2/3})` split-case bound is the multiplicity-from-relations
construction: at a rep point `(X−c)^{t·b} = 1`, so `g_{a,b}` collapses to `X^a`, and the `t·b`-weighted
derivatives engineer the high-order vanishing (the sibling `RepCountStepanovOrderTwo` is its base case).

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Matrix Polynomial Finset

namespace ProximityGap.BinomialDet

variable {F : Type*} [Field F]

/-- The SV11 / Garcia–Voloch generator `g_{a,b}(X) = X^a · (X − c)^{t·b}`. -/
noncomputable def sv11Gen (c : F) (t : ℕ) (ab : ℕ × ℕ) : F[X] :=
  X ^ ab.1 * (X - C c) ^ (t * ab.2)

/-- The SV11 generator has `natDegree = a + t·b`. -/
theorem sv11Gen_natDegree (c : F) (t : ℕ) (ab : ℕ × ℕ) :
    (sv11Gen c t ab).natDegree = ab.1 + t * ab.2 := by
  unfold sv11Gen
  rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero)
        (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero c)),
    Polynomial.natDegree_pow, Polynomial.natDegree_X,
    Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one, mul_one]

/-- The SV11 generator is nonzero. -/
theorem sv11Gen_ne_zero (c : F) (t : ℕ) (ab : ℕ × ℕ) : sv11Gen c t ab ≠ 0 := by
  unfold sv11Gen
  exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
    (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero c))

/-- **The key degree-injectivity:** `(a, b) ↦ a + t·b` is injective on `a < t` (mod-`t` argument).
This is why the SV11 family `X^a (X−c)^{t b}` has *distinct degrees* — the engine for applying the
distinct-degree Wronskian non-vanishing certificate to it. -/
theorem add_mul_lt_injective {t a₁ b₁ a₂ b₂ : ℕ} (ha₁ : a₁ < t) (ha₂ : a₂ < t)
    (h : a₁ + t * b₁ = a₂ + t * b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have ht : 0 < t := lt_of_le_of_lt (Nat.zero_le _) ha₁
  have hmod : a₁ = a₂ := by
    have h2 := congrArg (· % t) h
    simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha₁, Nat.mod_eq_of_lt ha₂] using h2
  subst hmod
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left ht (by omega)⟩

/-- **The SV11 family Wronskian is nonzero.** Any indexed subfamily of `sv11Gen` whose degrees
`aᵢ + t·bᵢ` are distinct in `F` (e.g. by `add_mul_lt_injective` with `aᵢ < t` and the degrees below
`char F`) has nonzero classical Wronskian, in characteristic `0` or `> l−1`. This is the concrete
connector between the distinct-degree non-vanishing certificate and the Garcia–Voloch / HBK Stepanov
generator family. -/
theorem sv11_wronskianDet_ne_zero {l : ℕ} (c : F) (t : ℕ) (idx : Fin l → ℕ × ℕ)
    (hchar : ∀ a : Fin l, ((a : ℕ).factorial : F) ≠ 0)
    (hdistinct : Function.Injective
      (fun i => (((idx i).1 + t * (idx i).2 : ℕ) : F))) :
    ArkLib.ProximityGap.Wronskian.wronskianDet (fun i => sv11Gen c t (idx i)) ≠ 0 := by
  apply wronskianDet_ne_zero_of_distinctDeg
  · exact hchar
  · intro j; exact sv11Gen_ne_zero c t (idx j)
  · intro i j hij
    apply hdistinct
    dsimp only at hij ⊢
    rw [sv11Gen_natDegree, sv11Gen_natDegree] at hij
    exact hij


/-- **The b-collapse at a rep point.** If `(y − c)^t = 1` (the subgroup relation defining a rep
point), the SV11 generator `g_{a,b}(X) = X^a (X−c)^{tb}` evaluates to `y^a`, *independent of `b`*.
This is the seed of the Stepanov multiplicity-from-relations mechanism: all `g_{a,b}` sharing an `a`
collapse to the same value `y^a` at rep points, so the value-evaluation map has rank `≤ D` (not
`D·B`) — the rank deficiency the high-order vanishing exploits. -/
theorem sv11Gen_eval_of_pow_eq_one (c y : F) {t : ℕ} (a b : ℕ) (h : (y - c) ^ t = 1) :
    (sv11Gen c t (a, b)).eval y = y ^ a := by
  unfold sv11Gen
  rw [eval_mul, eval_pow, eval_X, eval_pow, eval_sub, eval_X, eval_C, pow_mul, h, one_pow, mul_one]


/-- **Free order-1 vanishing from the b-collapse rank deficiency.** Any combination
`Ψ = ∑_{a<D} ∑_{b<B} coef(a,b) · g_{a,b}` whose *row sums* vanish (`∑_b coef(a,b) = 0` ∀`a`)
evaluates to `0` at every rep point `y` (`(y−c)^t = 1`) — independent of the number of rep points.
So order-1 vanishing at *all* rep points costs only the `D` row-sum conditions (not `D·B` or one per
point): the rank deficiency (value-map rank `≤ D`) the Stepanov high-order vanishing exploits. -/
theorem sv11_combination_vanishes_of_rowsum_zero {D B : ℕ} (c : F) (t : ℕ)
    (coef : ℕ → ℕ → F) (y : F) (h : (y - c) ^ t = 1)
    (hrow : ∀ a, ∑ b ∈ Finset.range B, coef a b = 0) :
    (∑ a ∈ Finset.range D, ∑ b ∈ Finset.range B,
        Polynomial.C (coef a b) * sv11Gen c t (a, b)).eval y = 0 := by
  rw [eval_finset_sum]
  apply Finset.sum_eq_zero
  intro a _
  rw [eval_finset_sum]
  have hb : ∀ b ∈ Finset.range B,
      (Polynomial.C (coef a b) * sv11Gen c t (a, b)).eval y = coef a b * y ^ a := by
    intro b _
    rw [eval_mul, eval_C, sv11Gen_eval_of_pow_eq_one c y a b h]
  rw [Finset.sum_congr rfl hb, ← Finset.sum_mul, hrow a, zero_mul]


/-- **The derivative at a rep point (the tb-weighting).** At a rep point `(y−c)^t = 1`,
`(y − c) · g_{a,b}'(y) = a·y^{a−1}·(y−c) + t·b·y^a`. The `t·b` term is how the `b`-index enters at
the first-derivative level — the weighting that governs the higher-order (multiplicity) vanishing of
the Stepanov auxiliary / Wronskian at rep points (so the value map is `b`-collapsed but the jet map
acquires `b`-rank through these `tb` weights). -/
theorem sv11Gen_deriv_eval_mul (c y : F) {t : ℕ} (a b : ℕ) (h : (y - c) ^ t = 1) :
    (Polynomial.derivative (sv11Gen c t (a, b))).eval y * (y - c)
      = (a : F) * y ^ (a - 1) * (y - c) + (t * b : ℕ) * y ^ a := by
  have hpow : (y - c) ^ (t * b) = 1 := by rw [pow_mul, h, one_pow]
  have hpm : ((t * b : ℕ) : F) * (y - c) ^ (t * b - 1) * (y - c) = ((t * b : ℕ) : F) := by
    rcases Nat.eq_zero_or_pos (t * b) with htb | htb
    · simp [htb]
    · rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel htb, hpow, mul_one]
  unfold sv11Gen
  rw [Polynomial.derivative_mul, Polynomial.derivative_X_pow, Polynomial.derivative_pow,
      Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, mul_one]
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_sub]
  rw [hpow, mul_one, add_mul,
    show y ^ a * (((t * b : ℕ) : F) * (y - c) ^ (t * b - 1)) * (y - c)
        = ((t * b : ℕ) : F) * (y - c) ^ (t * b - 1) * (y - c) * y ^ a by ring,
    hpm]

/-- **Order-1 of the combination: the weighted moments.** If the row sums vanish
(`∑_b coef(a,b) = 0`), then the *first derivative* of `Ψ = ∑ coef·g_{a,b}` at a rep point is governed
by the next moment level — `(y−c)·Ψ'(y) = t·∑_a (∑_b b·coef(a,b))·y^a`. So imposing order-2 vanishing
at the rep points costs only the `D` *weighted* row-sum conditions `∑_b b·coef(a,b) = 0` (on top of the
`D` row-sum conditions): the order-`M` moment ladder, the next rung after `sv11_combination_vanishes_of_rowsum_zero`. -/
theorem sv11_deriv_combination_of_rowsum_zero {D B : ℕ} (c y : F) (t : ℕ) (coef : ℕ → ℕ → F)
    (h : (y - c) ^ t = 1) (hrow : ∀ a, ∑ b ∈ Finset.range B, coef a b = 0) :
    (Polynomial.derivative (∑ a ∈ Finset.range D, ∑ b ∈ Finset.range B,
        Polynomial.C (coef a b) * sv11Gen c t (a, b))).eval y * (y - c)
      = (t : F) * ∑ a ∈ Finset.range D, (∑ b ∈ Finset.range B, (b : F) * coef a b) * y ^ a := by
  rw [derivative_sum, eval_finset_sum, Finset.sum_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [derivative_sum, eval_finset_sum, Finset.sum_mul]
  -- inner: ∑_b (derivative (C (coef a b) * g)).eval y * (y-c) = t * (∑_b b*coef) * y^a   (using row sum 0)
  have hterm : ∀ b ∈ Finset.range B,
      (Polynomial.derivative (Polynomial.C (coef a b) * sv11Gen c t (a, b))).eval y * (y - c)
        = coef a b * ((a : F) * y ^ (a - 1) * (y - c)) + (t : F) * ((b : F) * coef a b) * y ^ a := by
    intro b _
    rw [derivative_C_mul, eval_mul, eval_C, mul_assoc, sv11Gen_deriv_eval_mul c y a b h]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul, hrow a, zero_mul,
    zero_add, ← Finset.sum_mul, ← Finset.mul_sum, mul_assoc]

/-- **Order-2 free vanishing at a rep point.** If the row sums vanish (`∑_b coef(a,b) = 0`, order-0)
and the weighted-moment polynomial vanishes at `y` (`∑_a (∑_b b·coef(a,b))·y^a = 0`, order-1), then
`Ψ = ∑ coef·g_{a,b}` vanishes to order ≥ 2 at the rep point: both `Ψ(y) = 0` and `Ψ'(y) = 0`. Combines
the order-0 (`sv11_combination_vanishes_of_rowsum_zero`) and order-1 (`sv11_deriv_combination_of_rowsum_zero`)
moment-ladder bricks — the order-2 rung of the Stepanov multiplicity. -/
theorem sv11_combination_order_two_vanish {D B : ℕ} (c y : F) (t : ℕ) (coef : ℕ → ℕ → F)
    (h : (y - c) ^ t = 1) (hcy : y ≠ c)
    (hrow : ∀ a, ∑ b ∈ Finset.range B, coef a b = 0)
    (hwm : ∑ a ∈ Finset.range D, (∑ b ∈ Finset.range B, (b : F) * coef a b) * y ^ a = 0) :
    (∑ a ∈ Finset.range D, ∑ b ∈ Finset.range B,
          Polynomial.C (coef a b) * sv11Gen c t (a, b)).eval y = 0
      ∧ (Polynomial.derivative (∑ a ∈ Finset.range D, ∑ b ∈ Finset.range B,
          Polynomial.C (coef a b) * sv11Gen c t (a, b))).eval y = 0 := by
  refine ⟨sv11_combination_vanishes_of_rowsum_zero c t coef y h hrow, ?_⟩
  have h1 := sv11_deriv_combination_of_rowsum_zero (D := D) c y t coef h hrow
  rw [hwm, mul_zero] at h1
  exact (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hcy)

/-- **Degree bound for the imposed combination.** `Ψ = ∑_{a<D} ∑_{b<B} coef(a,b)·g_{a,b}` has
`natDegree ≤ (D−1) + t·(B−1)` — the max generator degree. Combined with the proven counting engine
(`|rep set|·M ≤ deg Ψ` from `sv11_combination_rootMultiplicity_ge`) this gives `r ≤ ((D−1)+t(B−1))/M`,
i.e. `r ≲ tB/M`: since order-`M` vanishing needs `B > M`, this is only the *trivial* `r ≲ t` bound.
Formalizes precisely why the imposed-combination route does **not** reach `O(t^{2/3})` — the `t`-power
degree must be cancelled (the Wronskian-as-auxiliary degree-reduction), into which the structural
theorems feed. -/
theorem sv11_combination_natDegree_le {D B : ℕ} (c : F) (t : ℕ) (coef : ℕ → ℕ → F) :
    (∑ a ∈ Finset.range D, ∑ b ∈ Finset.range B,
        Polynomial.C (coef a b) * sv11Gen c t (a, b)).natDegree ≤ (D - 1) + t * (B - 1) := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a ha
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro b hb
  rw [Finset.mem_range] at ha hb
  calc (Polynomial.C (coef a b) * sv11Gen c t (a, b)).natDegree
      ≤ (sv11Gen c t (a, b)).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ = a + t * b := sv11Gen_natDegree c t (a, b)
    _ ≤ (D - 1) + t * (B - 1) :=
        Nat.add_le_add (by omega) (Nat.mul_le_mul_left t (by omega))

end ProximityGap.BinomialDet


-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.BinomialDet.sv11Gen_eval_of_pow_eq_one
#print axioms ProximityGap.BinomialDet.sv11_combination_vanishes_of_rowsum_zero
#print axioms ProximityGap.BinomialDet.sv11Gen_deriv_eval_mul
#print axioms ProximityGap.BinomialDet.sv11_deriv_combination_of_rowsum_zero
#print axioms ProximityGap.BinomialDet.sv11_combination_order_two_vanish
#print axioms ProximityGap.BinomialDet.sv11_combination_natDegree_le
#print axioms ProximityGap.BinomialDet.add_mul_lt_injective
#print axioms ProximityGap.BinomialDet.sv11_wronskianDet_ne_zero
