/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DivisorListBound
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS
import Mathlib.LinearAlgebra.Lagrange

/-!
# The RS-list divisor bound on a smooth domain (#389, the divisor route made concrete)

`DivisorListBound.lean` proved the injective gcd backbone of the divisor route at the
pure-polynomial level.  This file transfers it **to the actual RS code** on any finite-field
evaluation domain `dom : Fin n ↪ F`, with vanishing polynomial `Z = ∏_i (X − dom i)`
(`= Xⁿ − 1` exactly when `dom` enumerates `μ_n`):

* `agreement_le_gcd_degree` — for the Lagrange interpolant `W` of `w`, each agreement point
  `dom i` is a common root of `W − c` and `Z`, hence a root of their gcd, so
  `#agreement(c, w) ≤ deg gcd(W − c, Z)`.
* `rs_list_card_le_divisors` — consequently the list of degree-`<k` codewords with
  agreement `≥ a ≥ k` injects (via `c ↦ gcd(W − c, Z)`) into the divisors of `Z` of degree
  `≥ a`, so **`|list| ≤ #{monic divisors of Z of degree ≥ a}`**.

**Scope: which field the divisors are counted over.**  The theorems here assume `[Fintype F]`
and count monic divisors of `Z` in `F[X]`, the evaluation field itself.  When `dom` enumerates
`n` distinct roots of `Xⁿ − 1` in `F`, the polynomial `Z = Xⁿ − 1` SPLITS into `n` distinct
linear factors over `F`, so it has exactly `2ⁿ` monic divisors; this is true in any field
containing the `n` evaluation roots, characteristic zero included (e.g. over `ℂ`).  The
cyclotomic count is different: over `ℚ`, `Xⁿ − 1 = ∏_{d ∣ n} Φ_d` has `2^{τ(n)}` monic
divisors (`τ(n)` = number of divisors of `n`), which is `2^{m+1} = O(n)` only for dyadic
`n = 2^m`.  That rational count does NOT apply to the RS bound proved here: `ℚ` does not
contain `μ_n` for `n > 2` (so no `Fin n ↪ ℚ` enumerates `μ_n`), and enlarging the coefficient
field to contain the evaluation points destroys the rational count.  Using a rational count
would require an additional integrality / rational-coefficient constraint on the gcds
`gcd(W − c, Z)`, which is not formalised here.  Over the deployed finite split field the bound
is therefore the vacuous `2ⁿ`.  Issue #389.
-/

open Polynomial EuclideanDomain
namespace ProximityGap.RSBridge

open ProximityGap.SpikeFloor ProximityGap.DivisorList

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The domain vanishing polynomial `Z = ∏_i (X − dom i)`. -/
noncomputable def domZ (dom : Fin n ↪ F) : F[X] := ∏ i, (X - C (dom i))

theorem domZ_ne_zero (dom : Fin n ↪ F) : domZ dom ≠ 0 := by
  rw [domZ]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact X_sub_C_ne_zero (dom i)

theorem domZ_root (dom : Fin n ↪ F) (i : Fin n) : (domZ dom).eval (dom i) = 0 := by
  rw [domZ, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

set_option maxHeartbeats 1000000 in
open Classical in
/-- **Agreement ≤ gcd degree on a smooth domain.**  For the Lagrange interpolant `W` of `w`
and a codeword `C` (any polynomial), the agreement points are common roots of `W − C` and
`Z`, hence roots of their gcd, so `#agreement ≤ deg gcd(W − C, Z)`. -/
theorem agreement_le_gcd_degree (dom : Fin n ↪ F) (w : Fin n → F) (cw : F[X]) :
    let W := Lagrange.interpolate (Finset.univ) (fun i => dom i) w
    ((Finset.univ : Finset (Fin n)).filter (fun i => cw.eval (dom i) = w i)).card
      ≤ (EuclideanDomain.gcd (W - cw) (domZ dom)).natDegree := by
  intro W
  classical
  set S := (Finset.univ : Finset (Fin n)).filter (fun i => cw.eval (dom i) = w i) with hS
  set D := EuclideanDomain.gcd (W - cw) (domZ dom) with hD
  have hDne : D ≠ 0 := by
    rw [hD]; intro h
    rw [EuclideanDomain.gcd_eq_zero_iff] at h
    exact domZ_ne_zero dom h.2
  have hinj : Set.InjOn (fun i : Fin n => dom i)
      (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)) :=
    fun a _ b _ hab => dom.injective hab
  -- each i ∈ S: dom i is a root of D
  have hroot : ∀ i ∈ S, (dom i) ∈ D.roots.toFinset := by
    intro i hi
    obtain ⟨_, hci⟩ := Finset.mem_filter.mp hi
    have hWi : W.eval (dom i) = w i :=
      Lagrange.eval_interpolate_at_node (v := fun a => dom a) (r := w) hinj
        (Finset.mem_univ i)
    have hWC : (W - cw).eval (dom i) = 0 := by rw [eval_sub, hWi, hci, sub_self]
    have h1 : (X - C (dom i)) ∣ (W - cw) := dvd_iff_isRoot.mpr hWC
    have h2 : (X - C (dom i)) ∣ (domZ dom) := dvd_iff_isRoot.mpr (domZ_root dom i)
    have h3 : (X - C (dom i)) ∣ D := dvd_gcd h1 h2
    rw [Multiset.mem_toFinset, mem_roots hDne]
    exact dvd_iff_isRoot.mp h3
  calc S.card = (S.image (fun i => dom i)).card :=
        (Finset.card_image_of_injOn (fun a _ b _ h => dom.injective h)).symm
    _ ≤ D.roots.toFinset.card := by
        refine Finset.card_le_card ?_
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact hroot i hi
    _ ≤ Multiset.card D.roots := Multiset.toFinset_card_le _
    _ ≤ D.natDegree := Polynomial.card_roots' _

set_option maxHeartbeats 1000000 in
open Classical in
/-- **The RS-list divisor bound on a smooth domain.**  The list of degree-`<k` codeword
polynomials whose agreement with `w` reaches `a ≥ k` injects, via `C ↦ gcd(W − C, Z)`
(`W` = Lagrange interpolant of `w`, `Z = ∏(X − dom i)`), into the divisors of `Z`: the
list cardinality equals its gcd-image, every element of which divides `Z` with degree
`≥ a`.  Hence `|list| ≤ #{monic divisors of Z of degree ≥ a}`.

The divisors are counted in `F[X]` for the finite evaluation field `F`.  On `μ_n ⊆ F`
(`Z = Xⁿ − 1`, split into `n` distinct linear factors) that count is `2ⁿ`, so the bound is
vacuous there; the `ℚ`-cyclotomic count `2^{τ(n)}` does not apply to this theorem (see the
module docstring). -/
theorem rs_list_card_le_divisors (dom : Fin n ↪ F) (w : Fin n → F) {k a : ℕ}
    (hka : k ≤ a) (L : Finset F[X])
    (hL : ∀ cw ∈ L, cw.degree < (k : ℕ) ∧
      a ≤ ((Finset.univ : Finset (Fin n)).filter (fun i => cw.eval (dom i) = w i)).card) :
    L.card = (L.image (fun cw =>
        EuclideanDomain.gcd (Lagrange.interpolate Finset.univ (fun i => dom i) w - cw)
          (domZ dom))).card := by
  classical
  set W := Lagrange.interpolate (Finset.univ) (fun i => dom i) w with hW
  refine (list_card_le_gcdImage (domZ dom) W hka L (fun cw hC => ⟨(hL cw hC).1, ?_⟩)).1
  exact le_trans (hL cw hC).2 (agreement_le_gcd_degree dom w cw)

end ProximityGap.RSBridge

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.RSBridge.agreement_le_gcd_degree
#print axioms ProximityGap.RSBridge.rs_list_card_le_divisors
