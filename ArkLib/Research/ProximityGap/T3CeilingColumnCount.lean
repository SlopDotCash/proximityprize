/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-!
# Column counts for the `t = 3` ceiling pencil `(X^a, X^(n-1))`

`T3CeilingColumnZeroLaw` decides when the scalar `0` is bad. This file counts **every** bad
scalar of the same column. On a field containing a primitive `n`-th root of unity, a scalar `s`
is bad when `X^a + s · X^(n-1)` is affine on three distinct `n`-th roots of unity. That is the
`t = 3` ceiling event of the monomial pencil at column `b = n - 1`: the second divided
difference of `X^(n-1)` never vanishes on such a triple, so each triple contributes exactly one
scalar, `-h_a / h_(n-1)`.

The count is:

* **T4, endpoints.** For `a ∈ {0, 1, n-1}` there is exactly one bad scalar (`0`, `0`, and `-1`).
* **T4, interior.** For `2 ≤ a ≤ n-2` there are at least `n / gcd(a+1, n) ≥ 2` bad scalars.
  One nonzero scalar dilates along `μ_n` to an orbit of that size, because
  `(c x)^a + (s · c^(a+1)) (c x)^(n-1) = c^a (x^a + s x^(n-1))`.
* **T5.** For `a = 2` and `n ≥ 4` the bad scalars are exactly `{-x y z}` as `{x,y,z}` runs
  over distinct `n`-th roots, and those products cover `μ_n`, so the count is `n`.

## Scope

One column (`b = n - 1`) of one threshold (`t = 3`). Nothing is claimed about the
large-prime converse (the probe's T3), the column maximum, any other column, `t ≥ 4`, or `δ*`.
-/

namespace ProximityPrize.T3CeilingColumnCount

open Polynomial

variable {K : Type*} [Field K]

/-- `f` takes affine values at `x, y, z`: the second divided difference vanishes, written
without division. This is `Collinear3` of `T3CeilingColumnZeroLaw` applied to the values of `f`. -/
def AffineOn (f : K → K) (x y z : K) : Prop :=
  (y - x) * (f z - f x) = (z - x) * (f y - f x)

/-- The same relation as a difference, so linearity is an equation rather than a rewrite of a
proposition. -/
def cross (f : K → K) (x y z : K) : K :=
  (y - x) * (f z - f x) - (z - x) * (f y - f x)

lemma affineOn_iff_cross (f : K → K) (x y z : K) :
    AffineOn f x y z ↔ cross f x y z = 0 := by
  unfold AffineOn cross
  exact sub_eq_zero.symm

lemma cross_add (f g : K → K) (x y z : K) :
    cross (fun t => f t + g t) x y z = cross f x y z + cross g x y z := by
  unfold cross
  ring

lemma cross_smul (c : K) (f : K → K) (x y z : K) :
    cross (fun t => c * f t) x y z = c * cross f x y z := by
  unfold cross
  ring

lemma cross_congr {f g : K → K} {x y z : K}
    (hx : f x = g x) (hy : f y = g y) (hz : f z = g z) :
    cross f x y z = cross g x y z := by
  unfold cross
  rw [hx, hy, hz]

lemma cross_const (c x y z : K) : cross (fun _ => c) x y z = 0 := by
  unfold cross
  ring

lemma cross_id (x y z : K) : cross (fun t => t) x y z = 0 := by
  unfold cross
  ring

lemma cross_sq (x y z : K) :
    cross (fun t => t ^ 2) x y z = (y - x) * (z - x) * (z - y) := by
  unfold cross
  ring

/-- Cross of inversion. The numerator is the same Vandermonde factor as `cross` of `t^2`. -/
lemma cross_inv_eq {x y z : K} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    cross (fun t => t⁻¹) x y z = (y - x) * (z - x) * (z - y) / (x * y * z) := by
  unfold cross
  field_simp
  ring

lemma cross_inv_ne_zero {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    cross (fun t => t⁻¹) x y z ≠ 0 := by
  rw [cross_inv_eq hx hy hz]
  refine div_ne_zero ?_ (mul_ne_zero (mul_ne_zero hx hy) hz)
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hxy.symm) (sub_ne_zero.mpr hxz.symm))
    (sub_ne_zero.mpr hyz.symm)

lemma pow_pred_eq_inv {n : ℕ} {t : K} (hn : 0 < n) (ht : t ^ n = 1) :
    t ^ (n - 1) = t⁻¹ := by
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at ht
    exact zero_ne_one ht
  have hmul : t * t ^ (n - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hn, ht]
  exact eq_inv_of_mul_eq_one_right hmul

lemma cross_pow_pred {n : ℕ} (hn : 0 < n) {x y z : K}
    (hx : x ^ n = 1) (hy : y ^ n = 1) (hz : z ^ n = 1) :
    cross (fun t => t ^ (n - 1)) x y z = cross (fun t => t⁻¹) x y z := by
  refine cross_congr ?_ ?_ ?_
  · exact pow_pred_eq_inv hn hx
  · exact pow_pred_eq_inv hn hy
  · exact pow_pred_eq_inv hn hz

lemma cross_pow_pred_ne_zero {n : ℕ} (hn : 0 < n) {x y z : K}
    (hx : x ^ n = 1) (hy : y ^ n = 1) (hz : z ^ n = 1)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    cross (fun t => t ^ (n - 1)) x y z ≠ 0 := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hx
    exact zero_ne_one hx
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hy
    exact zero_ne_one hy
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hz
    exact zero_ne_one hz
  rw [cross_pow_pred hn hx hy hz]
  exact cross_inv_ne_zero hxy hxz hyz hx0 hy0 hz0

lemma cross_pencil (n a : ℕ) (s x y z : K) :
    cross (fun t => t ^ a + s * t ^ (n - 1)) x y z =
      cross (fun t => t ^ a) x y z + s * cross (fun t => t ^ (n - 1)) x y z := by
  have hfun :
      (fun t : K => t ^ a + s * t ^ (n - 1)) =
        fun t => (fun u => u ^ a) t + s * (fun u => u ^ (n - 1)) t := rfl
  rw [hfun, cross_add, cross_smul]

/-- The unique scalar making `X^a + s X^(n-1)` affine on a triple of distinct `n`-th roots.
`X^(n-1)` contributes a nonzero cross difference, so the linear equation in `s` has one root. -/
noncomputable def ratioOf (n a : ℕ) (x y z : K) : K :=
  -cross (fun t => t ^ a) x y z / cross (fun t => t ^ (n - 1)) x y z

lemma affineOn_pencil_iff_ratio {n a : ℕ} (hn : 0 < n) {x y z s : K}
    (hx : x ^ n = 1) (hy : y ^ n = 1) (hz : z ^ n = 1)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    AffineOn (fun t => t ^ a + s * t ^ (n - 1)) x y z ↔ s = ratioOf n a x y z := by
  set A : K := cross (fun t => t ^ a) x y z
  set B : K := cross (fun t => t ^ (n - 1)) x y z
  have hB : B ≠ 0 := cross_pow_pred_ne_zero hn hx hy hz hxy hxz hyz
  rw [affineOn_iff_cross, cross_pencil]
  change A + s * B = 0 ↔ s = -A / B
  constructor
  · intro h
    have hsB : s * B = -A := by linear_combination h
    rwa [eq_div_iff hB]
  · intro hs
    rw [hs]
    calc
      A + (-A / B) * B = A + -A := by rw [div_mul_cancel₀ _ hB]
      _ = 0 := add_neg_cancel A

/-- `s` is a bad scalar of the pencil `(X^a, X^(n-1))` on the `n`-th roots of unity. -/
def BadScalar (n a : ℕ) (s : K) : Prop :=
  ∃ x y z : K, x ^ n = 1 ∧ y ^ n = 1 ∧ z ^ n = 1 ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    AffineOn (fun t => t ^ a + s * t ^ (n - 1)) x y z

/-- The set of bad scalars. Its `ncard` is the column count. -/
def badScalarSet (n a : ℕ) : Set K :=
  {s | BadScalar n a s}

lemma nthRoots_ne_zero {n : ℕ} (hn : 0 < n) : (X ^ n - C (1 : K)) ≠ 0 := by
  intro h
  have hdeg : (X ^ n - C (1 : K)).natDegree = n := by
    have hlt : (C (1 : K)).natDegree < (X ^ n : K[X]).natDegree := by
      rw [natDegree_C, natDegree_X_pow]
      omega
    rw [natDegree_sub_eq_left_of_natDegree_lt hlt, natDegree_X_pow]
  rw [h, natDegree_zero] at hdeg
  omega

lemma nthRoots_finite {n : ℕ} (hn : 0 < n) : {t : K | t ^ n = 1}.Finite := by
  classical
  let : DecidableEq K := Classical.typeDecidableEq K
  refine ((X ^ n - C (1 : K)).roots.toFinset).finite_toSet.subset ?_
  intro t ht
  rw [Set.mem_ofPred] at ht
  rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots (nthRoots_ne_zero (K := K) hn),
    IsRoot.def]
  simp [ht]

lemma badScalarSet_finite {n : ℕ} (hn : 0 < n) (a : ℕ) :
    (badScalarSet (K := K) n a).Finite := by
  classical
  let : DecidableEq K := Classical.typeDecidableEq K
  have hfin := nthRoots_finite (K := K) hn
  let μ : Finset K := hfin.toFinset
  have hμ : ∀ t : K, t ∈ μ ↔ t ^ n = 1 := by
    intro t
    simp [μ, Set.Finite.mem_toFinset]
  let trips := (μ ×ˢ μ ×ˢ μ).filter fun p =>
    p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2
  refine ((trips.image fun p => ratioOf n a p.1 p.2.1 p.2.2).finite_toSet).subset ?_
  intro s hs
  rw [badScalarSet, Set.mem_ofPred] at hs
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz, haff⟩ := hs
  have hseq : s = ratioOf n a x y z :=
    (affineOn_pencil_iff_ratio hn hx hy hz hxy hxz hyz).1 haff
  rw [hseq]
  refine Finset.mem_coe.2 (Finset.mem_image.2 ?_)
  refine ⟨(x, y, z), ?_, rfl⟩
  refine Finset.mem_filter.2 ?_
  constructor
  · simp [Finset.mem_product, hμ, hx, hy, hz]
  · exact ⟨hxy, hxz, hyz⟩

lemma exists_three_roots {ζ : K} {n : ℕ} (hn : 3 ≤ n) (hζ : IsPrimitiveRoot ζ n) :
    ∃ x y z : K, x ^ n = 1 ∧ y ^ n = 1 ∧ z ^ n = 1 ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  refine ⟨(1 : K), ζ, ζ ^ 2, by simp [one_pow], hζ.pow_eq_one, ?_, ?_, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · exact (hζ.ne_one (by omega)).symm
  · exact (hζ.pow_ne_one_of_pos_of_lt two_ne_zero (by omega)).symm
  · intro h
    have hpow : ζ ^ 1 = ζ ^ 2 := by simpa [pow_one] using h
    have := hζ.pow_inj (by omega) (by omega) hpow
    omega

/-- T4 at the constant and identity rows: the only bad scalar is `0`. -/
theorem badScalarSet_eq_zero {ζ : K} {n a : ℕ} (hn : 3 ≤ n) (hζ : IsPrimitiveRoot ζ n)
    (ha : a = 0 ∨ a = 1) : badScalarSet n a = {(0 : K)} := by
  classical
  ext s
  simp only [badScalarSet, Set.mem_ofPred, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz, haff⟩
    have hB : cross (fun t => t ^ (n - 1)) x y z ≠ 0 :=
      cross_pow_pred_ne_zero (by omega) hx hy hz hxy hxz hyz
    rw [affineOn_iff_cross, cross_pencil] at haff
    rcases ha with rfl | rfl
    · have hA : cross (fun t : K => t ^ 0) x y z = 0 := by
        simpa using cross_const (1 : K) x y z
      rw [hA, zero_add] at haff
      exact (mul_eq_zero.mp haff).resolve_right hB
    · have hA : cross (fun t : K => t ^ 1) x y z = 0 := by
        simpa using cross_id x y z
      rw [hA, zero_add] at haff
      exact (mul_eq_zero.mp haff).resolve_right hB
  · intro hs
    subst hs
    obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := exists_three_roots hn hζ
    refine ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz, ?_⟩
    rw [affineOn_iff_cross, cross_pencil]
    rcases ha with rfl | rfl
    · simp [cross_const]
    · simp [cross_id]

/-- T4 at the column itself: `X^(n-1) + s X^(n-1) = (1+s) X^(n-1)`, so only `s = -1` is bad. -/
theorem badScalarSet_eq_neg_one {ζ : K} {n : ℕ} (hn : 3 ≤ n) (hζ : IsPrimitiveRoot ζ n) :
    badScalarSet n (n - 1) = {(-1 : K)} := by
  classical
  ext s
  simp only [badScalarSet, Set.mem_ofPred, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz, haff⟩
    have hB : cross (fun t => t ^ (n - 1)) x y z ≠ 0 :=
      cross_pow_pred_ne_zero (by omega) hx hy hz hxy hxz hyz
    have hfun : (fun t : K => t ^ (n - 1) + s * t ^ (n - 1)) =
        fun t => (1 + s) * t ^ (n - 1) := by
      funext t
      ring
    rw [affineOn_iff_cross, hfun, cross_smul] at haff
    rcases mul_eq_zero.mp haff with h | h
    · rw [add_comm] at h
      exact eq_neg_of_add_eq_zero_left h
    · exact absurd h hB
  · intro hs
    subst hs
    obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := exists_three_roots hn hζ
    refine ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz, ?_⟩
    rw [affineOn_iff_cross]
    have hfun : (fun t : K => t ^ (n - 1) + (-1 : K) * t ^ (n - 1)) =
        fun t => (0 : K) * t ^ (n - 1) := by
      funext t
      ring
    rw [hfun, cross_smul]
    simp

theorem ncard_badScalar_endpoint {ζ : K} {n a : ℕ} (hn : 3 ≤ n) (hζ : IsPrimitiveRoot ζ n)
    (ha : a = 0 ∨ a = 1 ∨ a = n - 1) : (badScalarSet (K := K) n a).ncard = 1 := by
  rcases ha with ha0 | ha0 | ha0
  · rw [badScalarSet_eq_zero hn hζ (Or.inl ha0), Set.ncard_singleton]
  · rw [badScalarSet_eq_zero hn hζ (Or.inr ha0), Set.ncard_singleton]
  · rw [ha0, badScalarSet_eq_neg_one hn hζ, Set.ncard_singleton]

/-- Two affine functions that agree at two distinct points agree at the third. -/
lemma eq_of_affineOn_agree {f g : K → K} {x y z : K} (hxy : x ≠ y)
    (hf : AffineOn f x y z) (hg : AffineOn g x y z) (hx : f x = g x) (hy : f y = g y) :
    f z = g z := by
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  rw [AffineOn] at hf hg
  have hf' : f z - f x = (z - x) * (f y - f x) / (y - x) := by
    rw [eq_div_iff hyx]
    linear_combination hf
  have hg' : g z - g x = (z - x) * (g y - g x) / (y - x) := by
    rw [eq_div_iff hyx]
    linear_combination hg
  have : f z - f x = g z - g x := by
    rw [hf', hg', hx, hy]
  calc
    f z = (f z - f x) + f x := by ring
    _ = (g z - g x) + g x := by rw [this, hx]
    _ = g z := by ring

/-- `X^a` is not affine on all of `μ_n` when `2 ≤ a ≤ n-2`: a nonzero polynomial of degree `a`
cannot vanish at `n > a` roots. -/
lemma exists_triple_not_affine_pow {ζ : K} {n a : ℕ} (hn : 3 ≤ n) (hζ : IsPrimitiveRoot ζ n)
    (ha1 : 2 ≤ a) (ha2 : a ≤ n - 2) :
    ∃ x y z : K, x ^ n = 1 ∧ y ^ n = 1 ∧ z ^ n = 1 ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      ¬ AffineOn (fun t => t ^ a) x y z := by
  classical
  let : DecidableEq K := Classical.typeDecidableEq K
  by_contra hbad
  push Not at hbad
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  let c : K := (ζ ^ a - 1) / (ζ - 1)
  let L : K → K := fun t => 1 + c * (t - 1)
  have hL1 : L 1 = 1 := by
    simp [L]
  have hLζ : L ζ = ζ ^ a := by
    have hden : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
    simp only [L, c]
    field_simp [hden]
    ring
  have hagree : ∀ t : K, t ^ n = 1 → t ^ a = L t := by
    intro t ht
    by_cases ht1 : t = 1
    · simp [ht1, hL1]
    by_cases htζ : t = ζ
    · simp [htζ, hLζ]
    have h1t : (1 : K) ≠ t := fun h => ht1 h.symm
    have hζt : ζ ≠ t := fun h => htζ h.symm
    have haff := hbad (1 : K) ζ t (by simp [one_pow]) hζ.pow_eq_one ht hζ1.symm h1t hζt
    have hLaff : AffineOn L (1 : K) ζ t := by
      rw [affineOn_iff_cross]
      unfold cross L
      ring
    exact eq_of_affineOn_agree hζ1.symm haff hLaff
      (by rw [hL1]; exact (one_pow a : (1 : K) ^ a = 1)) hLζ.symm
  let p : K[X] := X ^ a - C c * X - C (1 - c)
  have hpform : p = X ^ a - (C c * X + C (1 - c)) := by
    unfold p
    ring
  have hlow : (C c * X + C (1 - c)).natDegree < a := by
    calc
      (C c * X + C (1 - c)).natDegree ≤
          max (C c * X).natDegree (C (1 - c)).natDegree :=
        natDegree_add_le _ _
      _ ≤ 1 := by
        refine max_le ?_ ?_
        · rw [← pow_one X]
          exact natDegree_C_mul_X_pow_le c 1
        · rw [natDegree_C]
          exact Nat.zero_le 1
      _ < a := by omega
  have hdeg : p.natDegree = a := by
    have hlt : (C c * X + C (1 - c)).natDegree < (X ^ a : K[X]).natDegree := by
      rw [natDegree_X_pow]
      exact hlow
    rw [hpform, natDegree_sub_eq_left_of_natDegree_lt hlt, natDegree_X_pow]
  have hp0 : p ≠ 0 := by
    intro h
    have : p.natDegree = 0 := by simp [h]
    omega
  have heval : ∀ t : K, t ^ n = 1 → p.eval t = 0 := by
    intro t ht
    have hL : t ^ a = c * t + (1 - c) := by
      calc
        t ^ a = 1 + c * (t - 1) := hagree t ht
        _ = c * t + (1 - c) := by ring
    simp only [p, eval_sub, eval_mul, eval_pow, eval_X, eval_C, hL]
    ring
  let s : Finset K := (Finset.range n).image fun i => ζ ^ i
  have hscard : s.card = n := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro i hi j hj hij
      exact hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
  have hss : s ⊆ p.roots.toFinset := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    rw [Multiset.mem_toFinset, mem_roots hp0, IsRoot.def]
    apply heval
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hle : n ≤ a := by
    calc
      n = s.card := hscard.symm
      _ ≤ p.roots.toFinset.card := Finset.card_le_card hss
      _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := card_roots' p
      _ = a := hdeg
  have : n ≤ n - 2 := hle.trans ha2
  omega

lemma exists_nonzero_bad {ζ : K} {n a : ℕ} (hn : 3 ≤ n) (hζ : IsPrimitiveRoot ζ n)
    (ha1 : 2 ≤ a) (ha2 : a ≤ n - 2) :
    ∃ x y z s : K, x ^ n = 1 ∧ y ^ n = 1 ∧ z ^ n = 1 ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      s ≠ 0 ∧ s = ratioOf n a x y z ∧ BadScalar n a s := by
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz, hnot⟩ :=
    exists_triple_not_affine_pow hn hζ ha1 ha2
  refine ⟨x, y, z, ratioOf n a x y z, hx, hy, hz, hxy, hxz, hyz, ?_, rfl, ?_⟩
  · intro hs
    apply hnot
    have hzero : cross (fun t => t ^ a) x y z = 0 := by
      set B : K := cross (fun t => t ^ (n - 1)) x y z
      have hB : B ≠ 0 := cross_pow_pred_ne_zero (by omega) hx hy hz hxy hxz hyz
      have hs0 : -cross (fun t => t ^ a) x y z / B = 0 := by
        simpa [ratioOf, B] using hs
      rcases div_eq_zero_iff.mp hs0 with hzero | hzero
      · exact neg_eq_zero.mp hzero
      · exact absurd hzero hB
    rw [affineOn_iff_cross]
    exact hzero
  · refine ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz, ?_⟩
    exact (affineOn_pencil_iff_ratio (by omega) hx hy hz hxy hxz hyz).2 rfl

/-- Dilating the nodes by `c ∈ μ_n` multiplies the bad scalar by `c^(a+1)`. -/
lemma badScalar_dilate {n a : ℕ} (hn : 0 < n) {x y z c s : K}
    (hx : x ^ n = 1) (hy : y ^ n = 1) (hz : z ^ n = 1) (hc : c ^ n = 1)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (haff : AffineOn (fun t => t ^ a + s * t ^ (n - 1)) x y z) :
    BadScalar n a (s * c ^ (a + 1)) := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hc
    exact zero_ne_one hc
  have hscale : ∀ u : K,
      (c * u) ^ a + (s * c ^ (a + 1)) * (c * u) ^ (n - 1) =
        c ^ a * (u ^ a + s * u ^ (n - 1)) := by
    intro u
    have hexp : a + 1 + (n - 1) = a + n := by omega
    calc
      (c * u) ^ a + (s * c ^ (a + 1)) * (c * u) ^ (n - 1)
          = c ^ a * u ^ a + (s * c ^ (a + 1)) * (c ^ (n - 1) * u ^ (n - 1)) := by
            rw [mul_pow, mul_pow]
      _ = c ^ a * u ^ a + s * c ^ (a + 1 + (n - 1)) * u ^ (n - 1) := by ring
      _ = c ^ a * u ^ a + s * c ^ (a + n) * u ^ (n - 1) := by rw [hexp]
      _ = c ^ a * u ^ a + s * (c ^ a * c ^ n) * u ^ (n - 1) := by rw [pow_add]
      _ = c ^ a * (u ^ a + s * u ^ (n - 1)) := by rw [hc]; ring
  have hxy' : c * x ≠ c * y := fun h => hxy (mul_left_cancel₀ hc0 h)
  have hxz' : c * x ≠ c * z := fun h => hxz (mul_left_cancel₀ hc0 h)
  have hyz' : c * y ≠ c * z := fun h => hyz (mul_left_cancel₀ hc0 h)
  refine ⟨c * x, c * y, c * z, ?_, ?_, ?_, hxy', hxz', hyz', ?_⟩
  · rw [mul_pow, hc, hx, one_mul]
  · rw [mul_pow, hc, hy, one_mul]
  · rw [mul_pow, hc, hz, one_mul]
  · rw [AffineOn] at haff ⊢
    set fz : K := z ^ a + s * z ^ (n - 1)
    set fx : K := x ^ a + s * x ^ (n - 1)
    set fy : K := y ^ a + s * y ^ (n - 1)
    have haff' : (y - x) * (fz - fx) = (z - x) * (fy - fx) := by
      simpa [fz, fx, fy] using haff
    have hzv := hscale z
    have hxv := hscale x
    have hyv := hscale y
    simp only [hzv, hxv, hyv]
    calc
      (c * y - c * x) * (c ^ a * fz - c ^ a * fx) =
          (c * (y - x)) * (c ^ a * (fz - fx)) := by ring
      _ = (c * c ^ a) * ((y - x) * (fz - fx)) := by ring
      _ = (c * c ^ a) * ((z - x) * (fy - fx)) := by rw [haff']
      _ = (c * (z - x)) * (c ^ a * (fy - fx)) := by ring
      _ = (c * z - c * x) * (c ^ a * fy - c ^ a * fx) := by ring

lemma card_scaled_pow_image {ζ : K} {n k : ℕ} {s : K} [DecidableEq K] (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (hs : s ≠ 0) :
    ((Finset.range (n / Nat.gcd k n)).image fun i => s * ζ ^ (i * k)).card =
      n / Nat.gcd k n := by
  classical
  rw [Finset.card_image_of_injOn]
  · simp
  intro i hi j hj hij
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn.ne'
  have hpow : ζ ^ (i * k) = ζ ^ (j * k) := mul_left_cancel₀ hs hij
  have hle_or := le_total i j
  rcases hle_or with hijle | hjle
  · have hcancel : ζ ^ ((j - i) * k) = 1 := by
      have hunit : ζ ^ (i * k) ≠ 0 := pow_ne_zero _ hζ0
      apply mul_left_cancel₀ hunit
      calc
        ζ ^ (i * k) * ζ ^ ((j - i) * k) = ζ ^ (i * k + (j - i) * k) := by rw [← pow_add]
        _ = ζ ^ (j * k) := by
          congr 1
          have : i * k + (j - i) * k = j * k := by
            have hsum : i + (j - i) = j := Nat.add_sub_of_le hijle
            calc
              i * k + (j - i) * k = (i + (j - i)) * k := by ring
              _ = j * k := by rw [hsum]
          exact this
        _ = ζ ^ (i * k) * 1 := by rw [hpow, mul_one]
    have hdv : n ∣ (j - i) * k := (hζ.pow_eq_one_iff_dvd ((j - i) * k)).1 hcancel
    set d := Nat.gcd k n
    have hdpos : 0 < d := Nat.gcd_pos_of_pos_right k hn
    have hcop : Nat.Coprime (k / d) (n / d) := Nat.coprime_div_gcd_div_gcd (m := k) (n := n) hdpos
    have hkd : d * (k / d) = k := Nat.mul_div_cancel' (Nat.gcd_dvd_left k n)
    have hnd : d * (n / d) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_right k n)
    obtain ⟨t, ht⟩ := hdv
    have hdiv : n / d ∣ (j - i) * (k / d) := by
      refine ⟨t, ?_⟩
      apply Nat.mul_left_cancel hdpos
      calc
        d * ((j - i) * (k / d)) = (j - i) * (d * (k / d)) := by ring
        _ = (j - i) * k := by rw [hkd]
        _ = n * t := ht
        _ = (d * (n / d)) * t := by rw [hnd]
        _ = d * ((n / d) * t) := Nat.mul_assoc _ _ _
    have hdiv' : n / d ∣ j - i := (hcop.symm).dvd_of_dvd_mul_right hdiv
    have hlt : j - i < n / d := lt_of_le_of_lt (Nat.sub_le _ _) (Finset.mem_range.mp hj)
    have hzero : j - i = 0 := Nat.eq_zero_of_dvd_of_lt hdiv' hlt
    omega
  · have hsym : i = j := by
      -- The same argument with the factors swapped.
      have hcancel : ζ ^ ((i - j) * k) = 1 := by
        have hunit : ζ ^ (j * k) ≠ 0 := pow_ne_zero _ hζ0
        apply mul_left_cancel₀ hunit
        calc
          ζ ^ (j * k) * ζ ^ ((i - j) * k) = ζ ^ (j * k + (i - j) * k) := by rw [← pow_add]
          _ = ζ ^ (i * k) := by
            congr 1
            have : j * k + (i - j) * k = i * k := by
              have hsum : j + (i - j) = i := Nat.add_sub_of_le hjle
              calc
                j * k + (i - j) * k = (j + (i - j)) * k := by ring
                _ = i * k := by rw [hsum]
            exact this
          _ = ζ ^ (j * k) * 1 := by rw [hpow.symm, mul_one]
      have hdv : n ∣ (i - j) * k := (hζ.pow_eq_one_iff_dvd ((i - j) * k)).1 hcancel
      set d := Nat.gcd k n
      have hdpos : 0 < d := Nat.gcd_pos_of_pos_right k hn
      have hcop : Nat.Coprime (k / d) (n / d) :=
        Nat.coprime_div_gcd_div_gcd (m := k) (n := n) hdpos
      have hkd : d * (k / d) = k := Nat.mul_div_cancel' (Nat.gcd_dvd_left k n)
      have hnd : d * (n / d) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_right k n)
      obtain ⟨t, ht⟩ := hdv
      have hdiv : n / d ∣ (i - j) * (k / d) := by
        refine ⟨t, ?_⟩
        apply Nat.mul_left_cancel hdpos
        calc
          d * ((i - j) * (k / d)) = (i - j) * (d * (k / d)) := by ring
          _ = (i - j) * k := by rw [hkd]
          _ = n * t := ht
          _ = (d * (n / d)) * t := by rw [hnd]
          _ = d * ((n / d) * t) := Nat.mul_assoc _ _ _
      have hdiv' : n / d ∣ i - j := (hcop.symm).dvd_of_dvd_mul_right hdiv
      have hlt : i - j < n / d := lt_of_le_of_lt (Nat.sub_le _ _) (Finset.mem_range.mp hi)
      have hzero : i - j = 0 := Nat.eq_zero_of_dvd_of_lt hdiv' hlt
      omega
    exact hsym

/-- A proper divisor of `n` is at most `n/2`, and `gcd(a+1, n)` is proper for `2 ≤ a ≤ n-2`. -/
lemma two_le_div_gcd (n a : ℕ) (ha1 : 2 ≤ a) (ha2 : a ≤ n - 2) :
    2 ≤ n / Nat.gcd (a + 1) n := by
  have hn : 0 < n := by omega
  set d := Nat.gcd (a + 1) n
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_right _ hn
  have hdvd : d ∣ n := Nat.gcd_dvd_right (a + 1) n
  have hdlt : d < n := by
    have hle : Nat.gcd (a + 1) n ≤ a + 1 := Nat.gcd_le_left n (by omega)
    have : a + 1 ≤ n - 1 := by omega
    omega
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · simp at hk
      omega
    · simp at hk
      omega
    · omega
  rw [hk, Nat.mul_div_cancel_left _ hdpos]
  exact hk2

/-- T4, interior: the dilation orbit of one nonzero bad scalar is a lower bound. -/
theorem div_gcd_le_ncard_badScalar {ζ : K} {n a : ℕ} (hn : 3 ≤ n) (hζ : IsPrimitiveRoot ζ n)
    (ha1 : 2 ≤ a) (ha2 : a ≤ n - 2) :
    n / Nat.gcd (a + 1) n ≤ (badScalarSet (K := K) n a).ncard := by
  classical
  let : DecidableEq K := Classical.typeDecidableEq K
  obtain ⟨x, y, z, s, hx, hy, hz, hxy, hxz, hyz, hs0, hratio, _⟩ :=
    exists_nonzero_bad hn hζ ha1 ha2
  have haff : AffineOn (fun t => t ^ a + s * t ^ (n - 1)) x y z :=
    (affineOn_pencil_iff_ratio (by omega) hx hy hz hxy hxz hyz).2 hratio
  let orbit : Finset K :=
    (Finset.range (n / Nat.gcd (a + 1) n)).image fun i => s * ζ ^ (i * (a + 1))
  have hcard : orbit.card = n / Nat.gcd (a + 1) n :=
    card_scaled_pow_image (by omega) hζ hs0
  have hsub : (orbit : Set K) ⊆ badScalarSet n a := by
    intro γ hγ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hγ)
    have hc : (ζ ^ i) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hmem := badScalar_dilate (by omega) hx hy hz hc hxy hxz hyz haff
    have hpow : s * (ζ ^ i) ^ (a + 1) = s * ζ ^ (i * (a + 1)) := by
      rw [pow_mul]
    rw [badScalarSet, Set.mem_ofPred, ← hpow]
    exact hmem
  have hfin : (badScalarSet (K := K) n a).Finite := badScalarSet_finite (by omega) a
  calc
    n / Nat.gcd (a + 1) n = orbit.card := hcard.symm
    _ = (orbit : Set K).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (badScalarSet n a).ncard := Set.ncard_le_ncard hsub hfin

theorem two_le_div_gcd_of_interior (n a : ℕ) (ha1 : 2 ≤ a) (ha2 : a ≤ n - 2) :
    2 ≤ n / Nat.gcd (a + 1) n :=
  two_le_div_gcd n a ha1 ha2

lemma add_n_mod {n r : ℕ} (hr : r < n) : (n + r) % n = r := by
  have hn : 0 < n := by omega
  rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr]

/-- Every residue modulo `n ≥ 4` is a sum of three distinct residues. -/
lemma exists_sum_three {n r : ℕ} (hn : 4 ≤ n) (hr : r < n) :
    ∃ i j k : ℕ, i < n ∧ j < n ∧ k < n ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ (i + j + k) % n = r := by
  by_cases hr1 : r = 1
  · refine ⟨0, 2, n - 1, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
    have hsum : 0 + 2 + (n - 1) = n + 1 := by omega
    rw [hsum, hr1, add_n_mod (by omega)]
  · by_cases hr2 : r = 2
    · by_cases hn4 : n = 4
      · refine ⟨1, 2, 3, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
        rw [hn4, hr2]
      · refine ⟨0, 3, n - 1, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
        have hsum : 0 + 3 + (n - 1) = n + 2 := by omega
        rw [hsum, hr2, add_n_mod (by omega)]
    · by_cases hr0 : r = 0
      · refine ⟨0, 1, n - 1, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
        have hsum : 0 + 1 + (n - 1) = n := by omega
        rw [hsum, hr0, Nat.mod_self]
      · refine ⟨0, 1, r - 1, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
        have hsum : 0 + 1 + (r - 1) = r := by omega
        rw [hsum, Nat.mod_eq_of_lt hr]

lemma pow_sum_mod {ζ : K} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (i j k : ℕ) :
    ζ ^ i * ζ ^ j * ζ ^ k = ζ ^ ((i + j + k) % n) := by
  calc
    ζ ^ i * ζ ^ j * ζ ^ k = ζ ^ (i + j + k) := by rw [← pow_add, ← pow_add]
    _ = ζ ^ ((i + j + k) % n + n * ((i + j + k) / n)) := by
      congr 1
      exact (Nat.mod_add_div _ _).symm
    _ = ζ ^ ((i + j + k) % n) * (ζ ^ n) ^ ((i + j + k) / n) := by rw [pow_add, pow_mul]
    _ = ζ ^ ((i + j + k) % n) * (1 : K) ^ ((i + j + k) / n) := by rw [hζ.pow_eq_one]
    _ = ζ ^ ((i + j + k) % n) := by simp

/-- At `a = 2`, the bad scalar of a triple of `n`-th roots is the negated product. -/
lemma ratioOf_two {n : ℕ} (hn : 0 < n) {x y z : K}
    (hx : x ^ n = 1) (hy : y ^ n = 1) (hz : z ^ n = 1)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ratioOf n 2 x y z = -(x * y * z) := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hx
    exact zero_ne_one hx
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hy
    exact zero_ne_one hy
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hz
    exact zero_ne_one hz
  unfold ratioOf
  rw [cross_sq, cross_pow_pred hn hx hy hz, cross_inv_eq hx0 hy0 hz0]
  have hfac : (y - x) * (z - x) * (z - y) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hxy.symm) (sub_ne_zero.mpr hxz.symm))
      (sub_ne_zero.mpr hyz.symm)
  have hden : x * y * z ≠ 0 := mul_ne_zero (mul_ne_zero hx0 hy0) hz0
  field_simp

/-- T5: for `a = 2` and `n ≥ 4`, the bad scalars are exactly `-μ_n`. -/
theorem badScalarSet_two {ζ : K} {n : ℕ} [DecidableEq K] (hn : 4 ≤ n)
    (hζ : IsPrimitiveRoot ζ n) :
    badScalarSet n 2 = ((Finset.range n).image fun i => -ζ ^ i : Set K) := by
  classical
  let : NeZero n := ⟨by omega⟩
  ext s
  constructor
  · intro hs
    obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz, haff⟩ := hs
    have hseq : s = -(x * y * z) := by
      rw [(affineOn_pencil_iff_ratio (by omega) hx hy hz hxy hxz hyz).1 haff,
        ratioOf_two (by omega) hx hy hz hxy hxz hyz]
    obtain ⟨ix, hix, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    obtain ⟨iy, hiy, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy
    obtain ⟨iz, hiz, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
    rw [hseq, pow_sum_mod hζ]
    refine Finset.mem_coe.2 (Finset.mem_image.2 ?_)
    refine ⟨(ix + iy + iz) % n, Finset.mem_range.2 (Nat.mod_lt _ (by omega)), ?_⟩
    rfl
  · intro hs
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hs)
    obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk, hsum⟩ :=
      exists_sum_three hn (Finset.mem_range.mp hr)
    have hxi : (ζ ^ i) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hyj : (ζ ^ j) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hzk : (ζ ^ k) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hxy : ζ ^ i ≠ ζ ^ j := fun h => hij (hζ.pow_inj hi hj h)
    have hxz : ζ ^ i ≠ ζ ^ k := fun h => hik (hζ.pow_inj hi hk h)
    have hyz : ζ ^ j ≠ ζ ^ k := fun h => hjk (hζ.pow_inj hj hk h)
    have hprod : ζ ^ i * ζ ^ j * ζ ^ k = ζ ^ r := by
      rw [pow_sum_mod hζ, hsum]
    have hratio := ratioOf_two (by omega) hxi hyj hzk hxy hxz hyz
    rw [← hprod, ← hratio]
    exact ⟨ζ ^ i, ζ ^ j, ζ ^ k, hxi, hyj, hzk, hxy, hxz, hyz,
      (affineOn_pencil_iff_ratio (by omega) hxi hyj hzk hxy hxz hyz).2 rfl⟩

lemma card_neg_powers {ζ : K} {n : ℕ} [DecidableEq K] (hζ : IsPrimitiveRoot ζ n) :
    ((Finset.range n).image fun i => -ζ ^ i).card = n := by
  classical
  rw [Finset.card_image_of_injOn]
  · simp
  intro i hi j hj hij
  exact hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (neg_inj.mp hij)

theorem ncard_badScalar_two {ζ : K} {n : ℕ} (hn : 4 ≤ n) (hζ : IsPrimitiveRoot ζ n) :
    (badScalarSet (K := K) n 2).ncard = n := by
  classical
  let : DecidableEq K := Classical.typeDecidableEq K
  rw [badScalarSet_two hn hζ, Set.ncard_coe_finset, card_neg_powers hζ]

#print axioms badScalarSet_eq_zero
#print axioms badScalarSet_eq_neg_one
#print axioms ncard_badScalar_endpoint
#print axioms div_gcd_le_ncard_badScalar
#print axioms ncard_badScalar_two

end ProximityPrize.T3CeilingColumnCount
