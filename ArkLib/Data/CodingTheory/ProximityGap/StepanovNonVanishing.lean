/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Issue #232 — the Stepanov non-vanishing, PROVEN (squarefree / integrally-closed argument).

`StepanovWeilSubstrate.lean` reduced the #232 Weil bound to the Stepanov auxiliary's
**non-vanishing**: that the constructed `R(X) = A₀(X, X^q) + g(X)^((q−1)/2)·A₁(X, X^q)` is not the
zero polynomial. This file pins that down completely:

## The algebraic chain `squarefree ⟹ Y²−g irreducible` (proven)

* `squarefree_not_isSquare` / `squarefree_not_isSquare_ratFunc` — a squarefree `g` of positive degree
  is not a square in `F[X]`, nor in the rational function field `RatFunc F` (integrally-closed route).
* `X_sq_sub_C_irreducible_iff_not_isSquare` — over any field, `X²−C c` is irreducible iff `c` is not a
  square (Kummer `p = 2`).
* `squarefree_quadratic_irreducible_ratFunc` (the chain) — for `g` squarefree of positive degree,
  `Y²−g` is **irreducible** over `RatFunc F` (i.e. the hyperelliptic curve `Y²=g(X)` is geometrically
  the right object). This discharges the *irreducibility precondition* of the genus argument.

## The base-`q` substitution machinery and faithfulness (proven)

* `subq q A := A(X, X^q)` for `A ∈ F[X][Y]`, with `subq_eq_sum`, `subq_add`, `subq_C_mul`,
  `coeff_subq_digit`, and the keystone `subq_eq_zero_iff` — **`Y↦X^q` is injective on
  `deg_X < q` two-variable polynomials** (base-`q` blocks do not overlap).
* `aux_collapses_to_relation` — `R = 0` collapses to the algebraic relation `A₀ + C(g^((q−1)/2))·A₁ = 0`
  **iff** the *combined* X-blocks all have degree `< q`.

## The precise obstruction, and the wall as one named hypothesis (honest)

* `obstruction_combined_digit_fails` — the combined-digit hypothesis **provably fails** in the
  relevant regime (`deg g·(q−1)/2 ≥ q`): the second term's block overflows the digit, so the two
  terms cancel *across* base-`q` blocks. The elementary base-`q` route therefore **cannot** close the
  non-vanishing — this is machine-checked, not asserted.
* `aux_key_claim_under_irreducibility` — the non-vanishing conclusion `A₀ = A₁ = 0`, carried under the
  single **named hypothesis** `hIrred` (the absolute-irreducibility / genus / Riemann–Roch consequence
  that the relation `A₀ = −g^((q−1)/2)·A₁` has only the trivial solution). SUPERSEDED by `obstruction_forces_trivial` (§5), which proves the non-vanishing outright; the
  earlier reading was that ruling out the cross-block cancellation requires counting `F`-points on
  `Y²=g(X)` (Hasse–Weil), which recovers **only the Johnson radius `√ρ`**, never the past-Johnson `δ*`
  prize #232 actually asks for.

Net: the entire Stepanov non-vanishing is now machine-checked (`obstruction_forces_trivial`, §5),
axiom-clean, with NO named genus hypothesis. Honest: even the full Weil bound recovers Johnson,
not the past-Johnson prize. `#232`/`#389` stay the open tracker for the deep-band supply wall.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
- Stepanov; Schmidt, *Equations over Finite Fields*; Kopparty, *The Weil bounds*; Bombieri (1973);
  Kowalski, *Exponential sums over finite fields, an elementary approach*.
-/

set_option linter.style.longLine false


open Polynomial

namespace ArkLib.ProximityGap.StepanovNonVanishing

/-! ## 1. A squarefree polynomial of positive degree is not a square (`F[X]` and `RatFunc F`). -/

section CharNonSquare
variable {F : Type*} [Field F]

/-- A squarefree polynomial that is a square must be a unit. -/
theorem squarefree_isSquare_isUnit (g : F[X]) (hsf : Squarefree g) (hsq : IsSquare g) :
    IsUnit g := by
  obtain ⟨h, rfl⟩ := hsq
  have hh : IsUnit h := hsf h (dvd_refl (h * h))
  exact hh.mul hh

/-- A squarefree polynomial of positive degree is not a square. -/
theorem squarefree_not_isSquare (g : F[X]) (hsf : Squarefree g) (hdeg : 0 < g.natDegree) :
    ¬ IsSquare g := by
  intro hsq
  have hu : IsUnit g := squarefree_isSquare_isUnit g hsf hsq
  have hd0 : g.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
  omega

/-- **Function-field form.** A squarefree `g : F[X]` of positive degree is not a square in
`RatFunc F`. (Integrally-closed route: a square root would be integral over `F[X]`, hence in `F[X]`,
contradicting `squarefree_not_isSquare`.) -/
theorem squarefree_not_isSquare_ratFunc (g : F[X]) (hsf : Squarefree g)
    (hdeg : 0 < g.natDegree) :
    ¬ IsSquare (algebraMap F[X] (RatFunc F) g) := by
  rintro ⟨r, hr⟩
  have hr2 : r ^ 2 = algebraMap F[X] (RatFunc F) g := by rw [sq]; exact hr.symm
  have hint : IsIntegral F[X] r := by
    refine ⟨X ^ 2 - C g, ?_, ?_⟩
    · apply monic_X_pow_sub
      exact lt_of_le_of_lt degree_C_le (by norm_num)
    · rw [eval₂_sub, eval₂_X_pow, eval₂_C, hr2, sub_self]
  obtain ⟨h, hh⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have key : algebraMap F[X] (RatFunc F) g = algebraMap F[X] (RatFunc F) (h ^ 2) := by
    rw [map_pow, hh, ← hr2]
  have hg : g = h ^ 2 := RatFunc.algebraMap_injective F key
  have : IsSquare g := ⟨h, by rw [hg, sq]⟩
  exact squarefree_not_isSquare g hsf hdeg this

end CharNonSquare

/-! ## 2. The quadratic irreducibility criterion. -/

section QuadraticIrreducible
variable {K : Type*} [Field K]

/-- `IsSquare c ↔ ∃ b, b² = c`. -/
lemma isSquare_iff_exists_sq_eq (c : K) : IsSquare c ↔ ∃ b : K, b ^ 2 = c := by
  constructor
  · rintro ⟨r, rfl⟩; exact ⟨r, by ring⟩
  · rintro ⟨b, rfl⟩; exact ⟨b, by ring⟩

/-- Over a field, `X²−C c` is irreducible iff `c` is not a square (Kummer `p = 2`). -/
theorem X_sq_sub_C_irreducible_iff_not_isSquare (c : K) :
    Irreducible (X ^ 2 - C c) ↔ ¬ IsSquare c := by
  rw [X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two, isSquare_iff_exists_sq_eq, not_exists]

end QuadraticIrreducible

/-! ## 3. The chain: squarefree `g` ⟹ `Y²−g` irreducible over `RatFunc F`. -/

section RatFuncIrreducible
variable {F : Type*} [Field F]

/-- `Y²−g` is irreducible over `RatFunc F` iff `g` is not a square there. -/
theorem stepanov_quadratic_irreducible_iff (g : F[X]) :
    Irreducible (X ^ 2 - C (algebraMap F[X] (RatFunc F) g)) ↔
      ¬ IsSquare (algebraMap F[X] (RatFunc F) g) :=
  X_sq_sub_C_irreducible_iff_not_isSquare _

/-- **The chain (discharges the irreducibility precondition).** For `g` squarefree of positive degree,
`Y²−g` is irreducible over `RatFunc F` — the hyperelliptic curve `Y²=g(X)` is geometrically
irreducible, the precondition of the genus / Hasse–Weil argument. -/
theorem squarefree_quadratic_irreducible_ratFunc (g : F[X]) (hsf : Squarefree g)
    (hdeg : 0 < g.natDegree) :
    Irreducible (X ^ 2 - C (algebraMap F[X] (RatFunc F) g)) :=
  (stepanov_quadratic_irreducible_iff g).mpr (squarefree_not_isSquare_ratFunc g hsf hdeg)

end RatFuncIrreducible

/-! ## 4. The base-`q` substitution `Y ↦ X^q`, its faithfulness, and the auxiliary collapse. -/

section BaseQ
variable {F : Type*}

/-- Substitution `Y ↦ X^q` on `A ∈ F[X][Y]`, i.e. the polynomial `A(X, X^q)`. -/
noncomputable def subq [CommRing F] (q : ℕ) (A : Polynomial (Polynomial F)) : Polynomial F :=
  A.eval₂ (RingHom.id (Polynomial F)) (X ^ q)

/-- `A(X, X^q) = ∑_j A_j(X)·X^(q·j)` — the base-`q` block decomposition. -/
theorem subq_eq_sum [CommRing F] (q : ℕ) (A : Polynomial (Polynomial F)) :
    subq q A = ∑ j ∈ Finset.range (A.natDegree + 1), (A.coeff j) * X ^ (q * j) := by
  unfold subq
  rw [eval₂_eq_sum_range]
  simp only [RingHom.id_apply, ← pow_mul]

/-- `subq` is additive. -/
theorem subq_add [CommRing F] (q : ℕ) (A B : Polynomial (Polynomial F)) :
    subq q (A + B) = subq q A + subq q B := by
  unfold subq; rw [Polynomial.eval₂_add]

/-- Pulling a scalar `G ∈ F[X]` out: `(C G · A)(X, X^q) = G · A(X, X^q)`. -/
theorem subq_C_mul [CommRing F] (q : ℕ) (G : Polynomial F) (A : Polynomial (Polynomial F)) :
    subq q (Polynomial.C G * A) = G * subq q A := by
  unfold subq
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, RingHom.id_apply]

/-- **Base-`q` coefficient extraction.** When every X-block has degree `< q`, the coefficient of
`A(X, X^q)` at exponent `q·j₀ + i` (`i < q`) is the `i`-th coefficient of the `j₀`-th block. -/
theorem coeff_subq_digit [CommRing F] (q : ℕ) (A : Polynomial (Polynomial F))
    (hdig : ∀ j, (A.coeff j).natDegree < q) (j0 i : ℕ) (hi : i < q) :
    (subq q A).coeff (q * j0 + i) = (A.coeff j0).coeff i := by
  rw [subq_eq_sum, finset_sum_coeff]
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le i) hi
  have hvanish : ∀ j ∈ Finset.range (A.natDegree + 1), j ≠ j0 →
      ((A.coeff j) * X ^ (q * j)).coeff (q * j0 + i) = 0 := by
    intro j _hj hjne
    rw [coeff_mul_X_pow']
    split_ifs with hcond
    · rcases lt_or_gt_of_ne hjne with hlt | hgt
      · apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hle : q ≤ q * j0 + i - q * j := by
          have heq : q * j + q * (j0 - j) = q * j0 := by rw [← Nat.mul_add]; congr 1; omega
          have h2 : q ≤ q * (j0 - j) := by
            calc q = q * 1 := (Nat.mul_one q).symm
            _ ≤ q * (j0 - j) := Nat.mul_le_mul_left q (by omega)
          omega
        exact lt_of_lt_of_le (hdig j) hle
      · exfalso
        have : q * (j0 + 1) ≤ q * j := Nat.mul_le_mul_left q (by omega)
        rw [Nat.mul_add, Nat.mul_one] at this; omega
    · rfl
  by_cases hj0 : j0 ≤ A.natDegree
  · rw [Finset.sum_eq_single j0]
    · rw [coeff_mul_X_pow', if_pos (Nat.le_add_right _ _)]
      congr 1; omega
    · exact hvanish
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · push Not at hj0
    rw [coeff_eq_zero_of_natDegree_lt hj0, Polynomial.coeff_zero]
    apply Finset.sum_eq_zero
    intro j hj
    exact hvanish j hj (by simp only [Finset.mem_range] at hj; omega)

/-- **Base-`q` faithfulness (keystone).** If every X-block of `A` has degree `< q` and
`A(X, X^q) = 0`, then `A = 0`: the substitution `Y ↦ X^q` is injective on `deg_X < q` polynomials. -/
theorem subq_eq_zero_iff [CommRing F] (q : ℕ) (A : Polynomial (Polynomial F))
    (hdig : ∀ j, (A.coeff j).natDegree < q) :
    subq q A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext j i'
    by_cases hi' : i' < q
    · have := coeff_subq_digit q A hdig j i' hi'
      rw [h, Polynomial.coeff_zero] at this
      rw [Polynomial.coeff_zero, Polynomial.coeff_zero]
      exact this.symm
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdig j) (by omega)),
        Polynomial.coeff_zero, Polynomial.coeff_zero]
  · intro h; rw [h]; unfold subq; simp

/-- First-term corollary: `A₀(X, X^q) = 0` with `deg_X < q` forces `A₀ = 0`. -/
theorem subq_first_term_eq_zero [CommRing F] (q : ℕ) (A0 : Polynomial (Polynomial F))
    (hdig : ∀ j, (A0.coeff j).natDegree < q) (h : subq q A0 = 0) : A0 = 0 :=
  (subq_eq_zero_iff q A0 hdig).mp h

/-- **Degree bound on the substituted term.** `deg A(X, X^q) ≤ q·deg_Y A + (q−1)`. -/
theorem natDegree_subq_le [Field F] (q : ℕ) (A : Polynomial (Polynomial F))
    (hdig : ∀ j, (A.coeff j).natDegree < q) :
    (subq q A).natDegree ≤ q * A.natDegree + (q - 1) := by
  rw [subq_eq_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  apply le_trans (Polynomial.natDegree_mul_le)
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
  simp only [Finset.mem_range] at hj
  have h1 : (A.coeff j).natDegree ≤ q - 1 := by have := hdig j; omega
  have h2 : q * j ≤ q * A.natDegree := Nat.mul_le_mul_left q (by omega)
  omega

/-- **The genuine reduction.** `R = subq q A₀ + G·subq q A₁ = 0` collapses (when the *combined*
X-blocks `A₀ⱼ + G·A₁ⱼ` all have degree `< q`) to the algebraic relation `A₀ + C G·A₁ = 0`. -/
theorem aux_collapses_to_relation [CommRing F] (q : ℕ) (G : Polynomial F)
    (A0 A1 : Polynomial (Polynomial F))
    (hdig : ∀ j, ((A0 + Polynomial.C G * A1).coeff j).natDegree < q)
    (hR : subq q A0 + G * subq q A1 = 0) :
    A0 + Polynomial.C G * A1 = 0 := by
  have hfold : subq q (A0 + Polynomial.C G * A1) = 0 := by
    rw [subq_add, subq_C_mul]; exact hR
  exact (subq_eq_zero_iff q _ hdig).mp hfold

/-- The relation always produces a vanishing auxiliary (the reduction is an equivalence). -/
theorem relation_gives_aux_zero [CommRing F] (q : ℕ) (G : Polynomial F)
    (A0 A1 : Polynomial (Polynomial F)) (hrel : A0 + Polynomial.C G * A1 = 0) :
    subq q A0 + G * subq q A1 = 0 := by
  have : subq q (A0 + Polynomial.C G * A1) = 0 := by rw [hrel]; unfold subq; simp
  rwa [subq_add, subq_C_mul] at this

/-- The `Y`-degree-2 hyperelliptic relation `A₀ + C(g^((q−1)/2))·A₁ = 0`. -/
def ObstructionRelation [CommRing F] (g : Polynomial F) (q : ℕ)
    (A0 A1 : Polynomial (Polynomial F)) : Prop :=
  A0 + Polynomial.C (g ^ ((q - 1) / 2)) * A1 = 0

/-- **The non-vanishing key claim, under the named genus hypothesis.** `hIrred` is the
absolute-irreducibility / genus consequence Mathlib does not yet provide: that the relation
`A₀ = −g^((q−1)/2)·A₁` (with both X-degrees `< q`) has only the trivial solution. Under it, the
auxiliary's blocks vanish. This isolates the wall as one named hypothesis (whose *precondition* —
irreducibility of `Y²−g` — is discharged by `squarefree_quadratic_irreducible_ratFunc`). -/
theorem aux_key_claim_under_irreducibility [CommRing F]
    (g : Polynomial F) (q : ℕ)
    (hIrred : ∀ A0 A1 : Polynomial (Polynomial F),
      (∀ j, (A0.coeff j).natDegree < q) → (∀ j, (A1.coeff j).natDegree < q) →
      ObstructionRelation g q A0 A1 → A0 = 0 ∧ A1 = 0)
    (A0 A1 : Polynomial (Polynomial F))
    (h0 : ∀ j, (A0.coeff j).natDegree < q) (h1 : ∀ j, (A1.coeff j).natDegree < q)
    (hcomb : ∀ j, ((A0 + Polynomial.C (g ^ ((q - 1) / 2)) * A1).coeff j).natDegree < q)
    (hR : subq q A0 + (g ^ ((q - 1) / 2)) * subq q A1 = 0) :
    A0 = 0 ∧ A1 = 0 :=
  hIrred A0 A1 h0 h1 (aux_collapses_to_relation q (g ^ ((q - 1) / 2)) A0 A1 hcomb hR)

/-- **The obstruction, made concrete.** The combined-digit hypothesis of `aux_collapses_to_relation`
genuinely fails in the relevant regime: if `A1 ≠ 0` and `deg g·((q−1)/2) ≥ q`, the second-term block
`g^((q−1)/2)·a` overflows the base-`q` digit. So one cannot apply faithfulness blindly — the elementary
route provably stops, and the cross-block cancellation is excluded only by counting `F`-points on
`Y²=g(X)` (Hasse–Weil), the genus content Mathlib lacks. -/
theorem obstruction_combined_digit_fails [Field F]
    (g : Polynomial F) (q : ℕ)
    (hG : g ^ ((q - 1) / 2) ≠ 0)
    (hbig : q ≤ ((q - 1) / 2) * g.natDegree)
    (a : Polynomial F) (ha : a ≠ 0) :
    ¬ ((g ^ ((q - 1) / 2)) * a).natDegree < q := by
  rw [Polynomial.natDegree_mul hG ha, Polynomial.natDegree_pow]
  omega

/-! ## 5. The genuine non-vanishing, PROVEN: the squarefree / integrally-closed argument.

The `aux_collapses_to_relation` route above is a dead end (`obstruction_combined_digit_fails`:
its combined-digit hypothesis is *false* in the relevant regime). But the non-vanishing does
**not** need that collapse, and it is **not** "genus content Mathlib lacks". The correct argument
(Kopparty, *The Weil bounds*, Lemma 3 = Hanson, *Stepanov's Method for Hyperelliptic Curves*,
Lemma 5) **squares first**: from `R = subq A₀ + g^((q−1)/2)·subq A₁ = 0` one gets
`(subq A₀)² = g^(q−1)·(subq A₁)²`, then multiplies by `g` and uses `g^q = g(X^q) = subq ĝ`
(`pow_card_eq_subq_map_C`) to fold *both* sides through `subq` — now with `X`-blocks of degree
`< q`, so faithfulness (`subq_eq_zero_iff`) applies and yields the genuine `F[X][Y]` identity
`C g · A₀² = ĝ · A₁²` (i.e. `g(X)·A₀² = g(Y)·A₁²`). Squarefree `g` of positive degree then forces
`A₀ = A₁ = 0` by the integrally-closed argument (`genus_squarefree_forces_trivial`), which is the
**same** `IsIntegrallyClosed` route already used here for the one-variable
`squarefree_not_isSquare_ratFunc`. This closes the Stepanov non-vanishing wall outright,
axiom-clean — superseding the named hypothesis `hIrred` of `aux_key_claim_under_irreducibility`.

Honest scope unchanged: the Weil bound recovers the **Johnson** radius `√ρ`, never the
past-Johnson `δ*` prize (#389/#232 stay the open tracker for the deep-band supply wall). -/

/-- `subq` packaged as a ring hom, to transport `*`, `^`. -/
noncomputable def subqHom [CommRing F] (q : ℕ) : Polynomial (Polynomial F) →+* Polynomial F :=
  Polynomial.eval₂RingHom (RingHom.id (Polynomial F)) (X ^ q)

theorem subqHom_apply [CommRing F] (q : ℕ) (A : Polynomial (Polynomial F)) :
    subqHom q A = subq q A := rfl

theorem subq_mul [CommRing F] (q : ℕ) (A B : Polynomial (Polynomial F)) :
    subq q (A * B) = subq q A * subq q B := by
  show subqHom q (A * B) = subqHom q A * subqHom q B; rw [map_mul]

theorem subq_pow [CommRing F] (q : ℕ) (A : Polynomial (Polynomial F)) (k : ℕ) :
    subq q (A ^ k) = (subq q A) ^ k := by
  show subqHom q (A ^ k) = (subqHom q A) ^ k; rw [map_pow]

theorem subq_C [CommRing F] (q : ℕ) (G : Polynomial F) : subq q (Polynomial.C G) = G := by
  show subqHom q (Polynomial.C G) = G; simp [subqHom, Polynomial.eval₂RingHom]

/-- `subq` of the `Y`-lift `g.map C` is `g(X^q)`. -/
theorem subq_map_C [CommRing F] (q : ℕ) (g : Polynomial F) :
    subq q (g.map (Polynomial.C)) = Polynomial.expand F q g := by
  unfold subq
  rw [Polynomial.eval₂_map]
  rw [show (RingHom.id (Polynomial F)).comp Polynomial.C = Polynomial.C from rfl]
  rw [Polynomial.expand_eq_comp_X_pow]; rfl

/-- **Frobenius for polynomials:** over a finite field, `g^q = g(X^q) = subq ĝ`. -/
theorem pow_card_eq_subq_map_C [Field F] [Fintype F] (g : Polynomial F) :
    g ^ (Fintype.card F) = subq (Fintype.card F) (g.map (Polynomial.C)) := by
  rw [subq_map_C, FiniteField.expand_card]

/-- A squarefree polynomial of positive degree over a field `L` is not a square in
`FractionRing L[X]` (the two-variable analogue's integrally-closed core). -/
theorem squarefree_pos_not_isSquare_frac {L : Type*} [Field L] (p : L[X])
    (hsf : Squarefree p) (hdeg : 0 < p.natDegree) :
    ¬ IsSquare (algebraMap L[X] (FractionRing L[X]) p) := by
  rintro ⟨r, hr⟩
  have hr2 : r ^ 2 = algebraMap L[X] (FractionRing L[X]) p := by rw [sq]; exact hr.symm
  have hint : IsIntegral L[X] r := by
    refine ⟨X ^ 2 - C p, ?_, ?_⟩
    · apply monic_X_pow_sub
      exact lt_of_le_of_lt degree_C_le (by norm_num)
    · rw [eval₂_sub, eval₂_X_pow, eval₂_C, hr2, sub_self]
  obtain ⟨h, hh⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have key : algebraMap L[X] (FractionRing L[X]) p
      = algebraMap L[X] (FractionRing L[X]) (h ^ 2) := by
    rw [map_pow, hh, ← hr2]
  have hp : p = h ^ 2 := IsFractionRing.injective L[X] (FractionRing L[X]) key
  have hsq : IsSquare p := ⟨h, by rw [hp, sq]⟩
  obtain ⟨h2, rfl⟩ := hsq
  have hu : IsUnit (h2 * h2) := (hsf h2 (dvd_refl _)).mul (hsf h2 (dvd_refl _))
  have := natDegree_eq_zero_of_isUnit hu
  omega

/-- Over a field `K`, `C γ · s² = gL · t²` with `γ ≠ 0` and `gL` squarefree of positive
degree forces `s = t = 0`. -/
theorem const_times_sq_eq_squarefree_times_sq {K : Type*} [Field K]
    (γ : K) (hγ : γ ≠ 0) (gL : K[X]) (hsf : Squarefree gL) (hdeg : 0 < gL.natDegree)
    (s t : K[X]) (hrel : C γ * s ^ 2 = gL * t ^ 2) : s = 0 ∧ t = 0 := by
  by_cases ht : t = 0
  · subst ht
    rw [zero_pow (two_ne_zero), mul_zero] at hrel
    have hCγ0 : (C γ : K[X]) ≠ 0 := by rwa [ne_eq, C_eq_zero]
    rcases mul_eq_zero.mp hrel with h | h
    · exact absurd h hCγ0
    · exact ⟨(pow_eq_zero_iff (two_ne_zero)).mp h, rfl⟩
  · exfalso
    set A := FractionRing K[X]
    set ν := algebraMap K[X] A with hν
    have hνinj : Function.Injective ν := IsFractionRing.injective K[X] A
    have ht0 : ν t ≠ 0 := by
      simp only [ne_eq, map_eq_zero_iff ν hνinj]; exact ht
    have hCγ : IsUnit (C γ⁻¹ : K[X]) := isUnit_C.mpr (Ne.isUnit (inv_ne_zero hγ))
    have hassoc : Associated (C γ⁻¹ * gL) gL :=
      ⟨(isUnit_C.mpr (Ne.isUnit hγ)).unit, by
        rw [IsUnit.unit_spec]
        rw [mul_comm (C γ⁻¹) gL, mul_assoc, ← C_mul, inv_mul_cancel₀ hγ, C_1, mul_one]⟩
    have hsf2 : Squarefree (C γ⁻¹ * gL) := hassoc.squarefree_iff.mpr hsf
    have hdeg2 : 0 < (C γ⁻¹ * gL).natDegree := by
      rw [natDegree_C_mul (inv_ne_zero hγ)]; exact hdeg
    apply squarefree_pos_not_isSquare_frac (C γ⁻¹ * gL) hsf2 hdeg2
    refine ⟨ν s / ν t, ?_⟩
    have hmap : ν (C γ) * ν s ^ 2 = ν gL * ν t ^ 2 := by
      have := congrArg ν hrel
      rwa [map_mul, map_mul, map_pow, map_pow] at this
    have hCC : ν (C γ⁻¹) * ν (C γ) = 1 := by
      rw [← map_mul, ← C_mul, inv_mul_cancel₀ hγ, C_1, map_one]
    rw [map_mul, div_mul_div_comm, ← sq, ← sq, eq_div_iff (pow_ne_zero 2 ht0)]
    linear_combination (-ν (C γ⁻¹)) * hmap + ν s ^ 2 * hCC

/-- **THE GENUS STATEMENT, PROVEN.** Over a finite field `F`, `C g · A₀² = ĝ · A₁²`
(`g(X)·A₀² = g(Y)·A₁²`) with `g` squarefree of positive degree forces `A₀ = A₁ = 0`. This is
exactly the consequence `hIrred` named as "Mathlib-lacking genus content"; it is the
integrally-closed argument, here discharged. -/
theorem genus_squarefree_forces_trivial [Field F] [Fintype F]
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (A0 A1 : Polynomial (Polynomial F))
    (hrel : Polynomial.C g * A0 ^ 2 = (g.map Polynomial.C) * A1 ^ 2) :
    A0 = 0 ∧ A1 = 0 := by
  set ι : F[X] →+* RatFunc F := algebraMap F[X] (RatFunc F) with hιdef
  have hιinj : Function.Injective ι := IsFractionRing.injective F[X] (RatFunc F)
  set φ : Polynomial (Polynomial F) →+* Polynomial (RatFunc F) := Polynomial.mapRingHom ι with hφ
  have hφinj : Function.Injective φ := Polynomial.map_injective ι hιinj
  have himg : φ (C g * A0 ^ 2) = φ ((g.map C) * A1 ^ 2) := by rw [hrel]
  rw [map_mul, map_mul, map_pow, map_pow] at himg
  have h1 : φ (C g) = C (ι g) := by rw [hφ, coe_mapRingHom, Polynomial.map_C]
  have h2 : φ (g.map (C : F →+* F[X])) = g.map (algebraMap F (RatFunc F)) := by
    rw [hφ, coe_mapRingHom, Polynomial.map_map]; congr 1
  rw [h1, h2] at himg
  have hγ : ι g ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff ι hιinj]; rintro rfl; simp at hdeg
  have hgLsf : Squarefree (g.map (algebraMap F (RatFunc F))) :=
    (PerfectField.separable_iff_squarefree.mpr hg).map.squarefree
  have hgLdeg : 0 < (g.map (algebraMap F (RatFunc F))).natDegree := by
    rw [natDegree_map_eq_of_injective (algebraMap F (RatFunc F)).injective]; exact hdeg
  obtain ⟨ha0, ha1⟩ := const_times_sq_eq_squarefree_times_sq (ι g) hγ
    (g.map (algebraMap F (RatFunc F))) hgLsf hgLdeg (φ A0) (φ A1) himg
  exact ⟨hφinj (by rw [ha0, map_zero]), hφinj (by rw [ha1, map_zero])⟩

/-- **THE STEPANOV NON-VANISHING, PROVEN (no `hIrred`).** Over a finite field `F` with `q = |F|`
odd, for `g` squarefree of positive degree: if the combined square-blocks `C g·A₀² − ĝ·A₁²` have
`X`-degree `< q` and the auxiliary `R = subq A₀ + g^((q−1)/2)·subq A₁` vanishes, then `A₀ = A₁ = 0`.
Squares first (so faithfulness applies), then closes by `genus_squarefree_forces_trivial`. -/
theorem obstruction_forces_trivial [Field F] [Fintype F]
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (hq_odd : Odd (Fintype.card F))
    (A0 A1 : Polynomial (Polynomial F))
    (hblk : ∀ j, ((C g * A0 ^ 2 - (g.map C) * A1 ^ 2).coeff j).natDegree < Fintype.card F)
    (hR : subq (Fintype.card F) A0
      + (g ^ ((Fintype.card F - 1) / 2)) * subq (Fintype.card F) A1 = 0) :
    A0 = 0 ∧ A1 = 0 := by
  set q := Fintype.card F with hq
  have hq1 : 1 ≤ q := Fintype.card_pos
  have heven : Even (q - 1) := Nat.Odd.sub_odd hq_odd odd_one
  have htwo : 2 * ((q - 1) / 2) = q - 1 := Nat.two_mul_div_two_of_even heven
  have hg2 : (g ^ ((q - 1) / 2)) ^ 2 = g ^ (q - 1) := by
    rw [← pow_mul, mul_comm ((q - 1) / 2) 2, htwo]
  have hsq : (subq q A0) ^ 2 = g ^ (q - 1) * (subq q A1) ^ 2 := by
    have h0 : subq q A0 = - (g ^ ((q - 1) / 2)) * subq q A1 := by linear_combination hR
    rw [h0, neg_mul, neg_sq, mul_pow, hg2]
  have hgmul : g * (subq q A0) ^ 2 = g ^ q * (subq q A1) ^ 2 := by
    rw [hsq, ← mul_assoc, ← pow_succ', show q - 1 + 1 = q from by omega]
  have hfold : subq q (C g * A0 ^ 2) = subq q ((g.map C) * A1 ^ 2) := by
    rw [subq_mul, subq_mul, subq_C, subq_pow, subq_pow, hgmul, pow_card_eq_subq_map_C]
  have hdiff : subq q (C g * A0 ^ 2 - (g.map C) * A1 ^ 2) = 0 := by
    have : subqHom q (C g * A0 ^ 2 - (g.map C) * A1 ^ 2) = 0 := by
      rw [map_sub]; show subq q _ - subq q _ = 0; rw [hfold]; ring
    rwa [subqHom_apply] at this
  have hrel0 : C g * A0 ^ 2 - (g.map C) * A1 ^ 2 = 0 :=
    (subq_eq_zero_iff q _ hblk).mp hdiff
  have hrel : C g * A0 ^ 2 = (g.map C) * A1 ^ 2 := by linear_combination hrel0
  exact genus_squarefree_forces_trivial g hg hdeg A0 A1 hrel

end BaseQ

end ArkLib.ProximityGap.StepanovNonVanishing

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StepanovNonVanishing.squarefree_not_isSquare_ratFunc
#print axioms ArkLib.ProximityGap.StepanovNonVanishing.squarefree_quadratic_irreducible_ratFunc
#print axioms ArkLib.ProximityGap.StepanovNonVanishing.subq_eq_zero_iff
#print axioms ArkLib.ProximityGap.StepanovNonVanishing.aux_collapses_to_relation
#print axioms ArkLib.ProximityGap.StepanovNonVanishing.aux_key_claim_under_irreducibility
#print axioms ArkLib.ProximityGap.StepanovNonVanishing.obstruction_combined_digit_fails
#print axioms ArkLib.ProximityGap.StepanovNonVanishing.genus_squarefree_forces_trivial
#print axioms ArkLib.ProximityGap.StepanovNonVanishing.obstruction_forces_trivial
