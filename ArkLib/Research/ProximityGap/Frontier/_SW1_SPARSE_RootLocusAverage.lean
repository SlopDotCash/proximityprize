/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Units.Equiv

/-!
# SW1 / SPARSE: the CORE energy as a root-locus average of sparse polynomials

**Target.**  Reformulate the DC-subtracted energy `E_r` (dossier form B, exponent coordinates)
as an exact average, over signed `2r`-tuples of exponents, of the number of *primitive* `n`-th
roots of unity at which the associated sparse polynomial
`P_t(T) = ∑ T^{a_i} − ∑ T^{b_i}` vanishes, and pin the characteristic-zero (`Φ_n ∣ P_t`)
stratum exactly.

**Objects** (`F` a commutative ring, `n ≠ 0`, `g : F`, exponents in `ZMod n`):

* `evalTuple g u t = P_t(g^u)` — the signed `2r`-term sum at the embedding `g^u`;
* `energyAt g r u = #{t : P_t(g^u) = 0}` — the energy at embedding `g^u`
  (`energyAt g r 1` is `E_r` in exponent coordinates when `g` has exact order `n`);
* `rootLocusCount g t = #{u ∈ (ZMod n)ˣ : P_t(g^u) = 0}` — the primitive-root count `Z(P_t)`.

**Results (all axiom-clean, Mathlib-only).**

* `energyAt_mul_unit` / `energyAt_unit_eq`: Galois dilation `t ↦ c·t` (`c` a unit) is a
  bijection of tuples with `P_{c·t}(g^u) = P_t(g^{uc})`, so the energy is the same at every
  primitive embedding.  (Row form; the coefficient-vector pool version is
  `_OCGaloisEmbeddingEquidistribution.lean`, this file is the tuple/energy-coordinate transpose.)
* `sum_rootLocusCount_eq` — **the root-locus average**:
  `∑_t Z(P_t) = |(ZMod n)ˣ| · E_r`.
* `rootLocusCount_of_cyclotomic_dvd` — **char-0 stratum**: if `Φ_n ∣ P_t` in `ℤ[T]` and `g` is
  a primitive `n`-th root of unity, then `Z(P_t) = |(ZMod n)ˣ|` (every primitive root).
* `spurious_sum_add_charZero` — the split
  `∑_{Φ_n ∤ P_t} Z(P_t) + |(ZMod n)ˣ| · #{Φ_n ∣ P_t} = |(ZMod n)ˣ| · E_r`,
  i.e. the *spurious* root-locus mass is exactly `|(ZMod n)ˣ| · (E_r − E_r⁰)`.
* `union_le_spurious_sum` / `energyAt_le_charZero_add_union` — the **index-blindness window**:
  `E_r − E_r⁰ ≤ #{spurious t : Z(P_t) ≥ 1} ≤ ∑_{spurious} Z(P_t) = |(ZMod n)ˣ|·(E_r − E_r⁰)`.
  Any per-polynomial root bound `Z(P) ≤ B` can only move CORE inside this window (a loss
  factor between `1` and `|(ZMod n)ˣ|`); the residual object is the *number of sparse
  polynomials vanishing somewhere on the primitive locus*, which is not a root-count statement.
* `evalTuple_reflect` / `rootLocusCount_reflect`: exponent reflection `a ↦ s − a` transports the
  vanishing set by `u ↦ −u`; a self-reciprocal signed multiset therefore has a negation-closed
  vanishing set (hence even `Z` for `n ≥ 3`).

**Honest classification (dossier v4 §6).**  Unconditional components (exact identities) plus an
exact obstruction statement.  No bound on `E_r`, no CORE closure; production δ* remains
OPEN / ON-BGK.  Probe: `scripts/probes/sw1_sparse_root_locus.py`
(measured: spurious `Z(P) ∈ {0,1}` on every enumerated cell `n ≤ 64`, `r ≤ 4`).
KB note: `docs/kb/deltastar-sw1-sparse-2026-09-05.md`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.SW1SparseRootLocus

open Finset Polynomial

/-- A signed `2r`-tuple of exponents in `ZMod n`: `r` plus-exponents and `r` minus-exponents. -/
abbrev STuple (n r : ℕ) := (Fin r → ZMod n) × (Fin r → ZMod n)

section Identity

variable {F : Type*} [CommRing F] [DecidableEq F] {n : ℕ} [NeZero n] {r : ℕ}

/-- `P_t(g^u) = ∑ g^{u a_i} − ∑ g^{u b_i}`, the sparse polynomial of `t` evaluated at `g^u`. -/
def evalTuple (g : F) (u : ZMod n) (t : STuple n r) : F :=
  (∑ i, g ^ (u * t.1 i).val) - ∑ i, g ^ (u * t.2 i).val

/-- Galois dilation of the exponents by `c`. -/
def dilate (c : ZMod n) (t : STuple n r) : STuple n r :=
  (fun i => c * t.1 i, fun i => c * t.2 i)

/-- `P_{c·t}(g^u) = P_t(g^{uc})`. -/
theorem evalTuple_dilate (g : F) (u c : ZMod n) (t : STuple n r) :
    evalTuple g u (dilate c t) = evalTuple g (u * c) t := by
  simp [evalTuple, dilate, mul_assoc]

/-- The energy at the embedding `g^u`: the number of signed tuples whose sparse polynomial
vanishes at `g^u`. -/
def energyAt (g : F) (r : ℕ) (u : ZMod n) : ℕ :=
  (univ.filter fun t : STuple n r => evalTuple g u t = 0).card

/-- `Z(P_t)`: the number of unit exponents `u` (primitive embeddings) with `P_t(g^u) = 0`. -/
def rootLocusCount (g : F) (t : STuple n r) : ℕ :=
  (univ.filter fun u : (ZMod n)ˣ => evalTuple g (u : ZMod n) t = 0).card

/-- Dilation by a unit is a permutation of the tuples. -/
def dilateEquiv (c : (ZMod n)ˣ) : STuple n r ≃ STuple n r where
  toFun := dilate (c : ZMod n)
  invFun := dilate ((c⁻¹ : (ZMod n)ˣ) : ZMod n)
  left_inv := fun t => by ext i <;> simp [dilate]
  right_inv := fun t => by ext i <;> simp [dilate]

theorem dilateEquiv_apply (c : (ZMod n)ˣ) (t : STuple n r) :
    dilateEquiv c t = dilate (c : ZMod n) t := rfl

/-- **Galois invariance of the energy.**  `#{t : P_t(g^{uc}) = 0} = #{t : P_t(g^u) = 0}`. -/
theorem energyAt_mul_unit (g : F) (r : ℕ) (u : ZMod n) (c : (ZMod n)ˣ) :
    energyAt g r (u * (c : ZMod n)) = energyAt g r u := by
  unfold energyAt
  refine Finset.card_equiv (dilateEquiv (r := r) c) ?_
  intro t
  simp [dilateEquiv_apply, evalTuple_dilate]

/-- The energy is the same at every primitive embedding `g^u`, `u` a unit. -/
theorem energyAt_unit_eq (g : F) (r : ℕ) (u : (ZMod n)ˣ) :
    energyAt g r (u : ZMod n) = energyAt g r (1 : ZMod n) := by
  simpa using energyAt_mul_unit g r 1 u

/-- Double count: `∑_t Z(P_t) = ∑_{u unit} #{t : P_t(g^u) = 0}`. -/
theorem sum_rootLocusCount (g : F) (r : ℕ) :
    ∑ t : STuple n r, rootLocusCount g t = ∑ u : (ZMod n)ˣ, energyAt g r (u : ZMod n) := by
  unfold rootLocusCount energyAt
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- **The root-locus average.**  `∑_t Z(P_t) = |(ZMod n)ˣ| · E_r`. -/
theorem sum_rootLocusCount_eq (g : F) (r : ℕ) :
    ∑ t : STuple n r, rootLocusCount g t
      = Fintype.card (ZMod n)ˣ * energyAt g r (1 : ZMod n) := by
  rw [sum_rootLocusCount]
  simp [energyAt_unit_eq, Finset.sum_const, Finset.card_univ]

end Identity

section CharZero

variable {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F] {n : ℕ} [NeZero n] {r : ℕ}

/-- The sparse polynomial `P_t = ∑ X^{a_i} − ∑ X^{b_i} ∈ ℤ[X]` of a signed tuple. -/
noncomputable def tuplePoly (t : STuple n r) : ℤ[X] :=
  (∑ i, X ^ (t.1 i).val) - ∑ i, X ^ (t.2 i).val

theorem pow_val_mul {g : F} (hg : g ^ n = 1) (u a : ZMod n) :
    g ^ (u * a).val = (g ^ u.val) ^ a.val := by
  rw [ZMod.val_mul, ← pow_eq_pow_mod _ hg, pow_mul]

/-- `P_t(g^u)` is the evaluation of the integer sparse polynomial at `g^{u.val}`. -/
theorem evalTuple_eq_eval {g : F} (hg : g ^ n = 1) (u : ZMod n) (t : STuple n r) :
    evalTuple g u t = ((tuplePoly t).map (Int.castRingHom F)).eval (g ^ u.val) := by
  simp [evalTuple, tuplePoly, Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.eval_finset_sum, pow_val_mul hg]

/-- **Char-0 stratum.**  If `Φ_n ∣ P_t` in `ℤ[X]` then `P_t` vanishes at every primitive
embedding `g^u`. -/
theorem evalTuple_eq_zero_of_cyclotomic_dvd {g : F} (hg : IsPrimitiveRoot g n)
    (t : STuple n r) (hdvd : cyclotomic n ℤ ∣ tuplePoly t) (u : (ZMod n)ˣ) :
    evalTuple g (u : ZMod n) t = 0 := by
  rw [evalTuple_eq_eval hg.pow_eq_one]
  have hprim : IsPrimitiveRoot (g ^ (u : ZMod n).val) n :=
    hg.pow_of_coprime _ (ZMod.val_coe_unit_coprime u)
  have hroot : (cyclotomic n F).eval (g ^ (u : ZMod n).val) = 0 :=
    hprim.isRoot_cyclotomic (NeZero.pos n)
  have hdvdF : cyclotomic n F ∣ (tuplePoly t).map (Int.castRingHom F) := by
    have := Polynomial.map_dvd (Int.castRingHom F) hdvd
    rwa [Polynomial.map_cyclotomic] at this
  exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvdF hroot

/-- **Char-0 stratum, counted.**  `Φ_n ∣ P_t` forces `Z(P_t) = |(ZMod n)ˣ|`. -/
theorem rootLocusCount_of_cyclotomic_dvd {g : F} (hg : IsPrimitiveRoot g n)
    (t : STuple n r) (hdvd : cyclotomic n ℤ ∣ tuplePoly t) :
    rootLocusCount g t = Fintype.card (ZMod n)ˣ := by
  unfold rootLocusCount
  rw [Finset.filter_true_of_mem (fun u _ => evalTuple_eq_zero_of_cyclotomic_dvd hg t hdvd u),
    Finset.card_univ]

open Classical in
/-- **Spurious split.**  `∑_{Φ_n ∤ P_t} Z(P_t) + |(ZMod n)ˣ| · #{Φ_n ∣ P_t} = |(ZMod n)ˣ| · E_r`:
the spurious root-locus mass is exactly `|(ZMod n)ˣ| · (E_r − E_r⁰)`. -/
theorem spurious_sum_add_charZero {g : F} (hg : IsPrimitiveRoot g n) (r : ℕ) :
    (∑ t ∈ univ.filter (fun t : STuple n r => ¬ cyclotomic n ℤ ∣ tuplePoly t),
        rootLocusCount g t)
      + Fintype.card (ZMod n)ˣ
          * (univ.filter (fun t : STuple n r => cyclotomic n ℤ ∣ tuplePoly t)).card
      = Fintype.card (ZMod n)ˣ * energyAt g r (1 : ZMod n) := by
  rw [← sum_rootLocusCount_eq g r,
    ← Finset.sum_filter_add_sum_filter_not univ (fun t : STuple n r => cyclotomic n ℤ ∣ tuplePoly t)]
  have hC : ∑ t ∈ univ.filter (fun t : STuple n r => cyclotomic n ℤ ∣ tuplePoly t),
      rootLocusCount g t
      = Fintype.card (ZMod n)ˣ
          * (univ.filter (fun t : STuple n r => cyclotomic n ℤ ∣ tuplePoly t)).card := by
    rw [Finset.sum_congr rfl (fun t ht => rootLocusCount_of_cyclotomic_dvd hg t
      (Finset.mem_filter.mp ht).2), Finset.sum_const, smul_eq_mul, mul_comm]
  rw [hC]
  ring

open Classical in
/-- **Index-blindness window, upper half.**  The number of spurious tuples vanishing somewhere on
the primitive locus is at most the spurious root-locus mass. -/
theorem union_le_spurious_sum (g : F) (r : ℕ) :
    (univ.filter (fun t : STuple n r => ¬ cyclotomic n ℤ ∣ tuplePoly t ∧
        1 ≤ rootLocusCount g t)).card
      ≤ ∑ t ∈ univ.filter (fun t : STuple n r => ¬ cyclotomic n ℤ ∣ tuplePoly t),
          rootLocusCount g t := by
  rw [Finset.card_filter, Finset.sum_filter]
  refine Finset.sum_le_sum fun t _ => ?_
  by_cases hp : ¬ cyclotomic n ℤ ∣ tuplePoly t ∧ 1 ≤ rootLocusCount g t
  · rw [if_pos hp, if_pos hp.1]; exact hp.2
  · rw [if_neg hp]; exact Nat.zero_le _

open Classical in
/-- **Index-blindness window, lower half.**  `E_r ≤ #{Φ_n ∣ P_t} + #{spurious t : Z(P_t) ≥ 1}`:
every tuple counted by `E_r` is either a char-0 relation or a spurious tuple vanishing at the
base embedding. -/
theorem energyAt_le_charZero_add_union (g : F) (r : ℕ) :
    energyAt g r (1 : ZMod n)
      ≤ (univ.filter (fun t : STuple n r => cyclotomic n ℤ ∣ tuplePoly t)).card
        + (univ.filter (fun t : STuple n r => ¬ cyclotomic n ℤ ∣ tuplePoly t ∧
            1 ≤ rootLocusCount g t)).card := by
  unfold energyAt
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro t ht
  rw [Finset.mem_filter] at ht
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  by_cases hc : cyclotomic n ℤ ∣ tuplePoly t
  · exact Or.inl ⟨Finset.mem_univ _, hc⟩
  · refine Or.inr ⟨Finset.mem_univ _, hc, ?_⟩
    unfold rootLocusCount
    refine Finset.card_pos.mpr ⟨1, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa using ht.2⟩

end CharZero

section Reflection

variable {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F] {n : ℕ} [NeZero n] {r : ℕ}

/-- Exponent reflection `a ↦ s − a`. -/
def reflect (s : ZMod n) (t : STuple n r) : STuple n r :=
  (fun i => s - t.1 i, fun i => s - t.2 i)

theorem pow_val_add {g : F} (hg : g ^ n = 1) (x y : ZMod n) :
    g ^ (x + y).val = g ^ x.val * g ^ y.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hg, pow_add]

/-- `P_{reflect s t}(g^u) = g^{us} · P_t(g^{−u})`: reflection transports the vanishing set by
`u ↦ −u`. -/
theorem evalTuple_reflect {g : F} (hg : g ^ n = 1) (s u : ZMod n) (t : STuple n r) :
    evalTuple g u (reflect s t) = g ^ (u * s).val * evalTuple g (-u) t := by
  have key : ∀ a : ZMod n, g ^ (u * (s - a)).val = g ^ (u * s).val * g ^ (-u * a).val := by
    intro a
    rw [← pow_val_add hg]
    congr 1
    ring
  simp only [evalTuple, reflect, key]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]

/-- The vanishing set of `reflect s t` is the negation of the vanishing set of `t`; in
particular `Z(P_{reflect s t}) = Z(P_t)`. -/
theorem rootLocusCount_reflect {g : F} (hg : IsPrimitiveRoot g n) (s : ZMod n)
    (t : STuple n r) :
    rootLocusCount g (reflect s t) = rootLocusCount g t := by
  unfold rootLocusCount
  refine Finset.card_equiv (Equiv.neg (ZMod n)ˣ) ?_
  intro u
  have hg0 : g ≠ 0 := hg.ne_zero (NeZero.ne n)
  simp [evalTuple_reflect hg.pow_eq_one, hg0]

/-- A tuple whose evaluation function is reflection-invariant (a self-reciprocal signed multiset)
has a negation-closed vanishing set: `P_t(g^u) = 0 → P_t(g^{−u}) = 0`. -/
theorem vanish_neg_of_reflect_invariant {g : F} (hg : IsPrimitiveRoot g n) (s : ZMod n)
    (t : STuple n r) (hinv : ∀ u : ZMod n, evalTuple g u (reflect s t) = evalTuple g u t)
    (u : ZMod n) (hu : evalTuple g u t = 0) : evalTuple g (-u) t = 0 := by
  have h := evalTuple_reflect hg.pow_eq_one s u t
  rw [hinv, hu] at h
  have hne : g ^ (u * s).val ≠ 0 := pow_ne_zero _ (hg.ne_zero (NeZero.ne n))
  rcases mul_eq_zero.mp h.symm with h0 | h0
  · exact absurd h0 hne
  · exact h0

end Reflection

end ArkLib.ProximityGap.Frontier.SW1SparseRootLocus

#print axioms ArkLib.ProximityGap.Frontier.SW1SparseRootLocus.energyAt_mul_unit
#print axioms ArkLib.ProximityGap.Frontier.SW1SparseRootLocus.energyAt_unit_eq
#print axioms ArkLib.ProximityGap.Frontier.SW1SparseRootLocus.sum_rootLocusCount
#print axioms ArkLib.ProximityGap.Frontier.SW1SparseRootLocus.sum_rootLocusCount_eq
#print axioms ArkLib.ProximityGap.Frontier.SW1SparseRootLocus.evalTuple_eq_zero_of_cyclotomic_dvd
#print axioms ArkLib.ProximityGap.Frontier.SW1SparseRootLocus.rootLocusCount_of_cyclotomic_dvd
#print axioms ArkLib.ProximityGap.Frontier.SW1SparseRootLocus.spurious_sum_add_charZero
#print axioms ArkLib.ProximityGap.Frontier.SW1SparseRootLocus.union_le_spurious_sum
#print axioms ArkLib.ProximityGap.Frontier.SW1SparseRootLocus.energyAt_le_charZero_add_union
#print axioms ArkLib.ProximityGap.Frontier.SW1SparseRootLocus.evalTuple_reflect
#print axioms ArkLib.ProximityGap.Frontier.SW1SparseRootLocus.rootLocusCount_reflect
#print axioms ArkLib.ProximityGap.Frontier.SW1SparseRootLocus.vanish_neg_of_reflect_invariant
