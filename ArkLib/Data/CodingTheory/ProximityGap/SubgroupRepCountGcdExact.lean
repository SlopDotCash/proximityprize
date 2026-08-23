/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupRepresentationRoots
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.SplittingField.Construction

/-!
# The representation count IS the gcd degree — sharpening the Stepanov frontier (#389)

`SubgroupRepresentationRoots.representationCount_le_gcd_degree` bounds the additive
representation count `r(c) = #{z ∈ G : c − z ∈ G}` of a root-of-unity subgroup
`G = {z : zⁿ = 1}` by `deg gcd(Xⁿ−1, (C c − X)ⁿ − 1)` — the Garcia–Voloch/HBK "Stepanov
frontier" object.  This file upgrades the inequality to an **exact equality** under the
hypotheses that hold for every smooth (NTT) domain:

* `representationSet_eq_gcd_roots` — UNCONDITIONALLY the representation *set* equals the
  gcd root set: a common root `z` of `Xⁿ−1` and `(C c−X)ⁿ−1` has `zⁿ = 1` (so `z ∈ G`) and
  `(c−z)ⁿ = 1` (so `c−z ∈ G`), i.e. it is a representation; the forward inclusion is the
  in-tree `representationSet_subset_gcd_roots`.
* `representationCount_eq_gcd_roots_card` — hence `r(c) = #distinct gcd roots`,
  unconditionally.
* `representationCount_eq_gcd_degree` — under `(n : F) ≠ 0` (separability of `Xⁿ−1`, i.e.
  `char F ∤ n`) and `(Xⁿ−1).Splits` (the domain is a *full* smooth subgroup, automatic
  for `n ∣ |F|−1`): `r(c) = deg gcd(Xⁿ−1, (C c−X)ⁿ−1)` **exactly**.

So the Garcia–Voloch obligation `GVRepBound G M` (`∀ c ≠ 0, r(c) ≤ M`) is, on smooth
domains, **equivalent** to the pure gcd-degree statement
`∀ c ≠ 0, deg gcd(Xⁿ−1, (C c−X)ⁿ−1) ≤ M` — no slack between the combinatorial count and
the resultant/Stepanov target.  Combined with `addEnergy_le_sum_gcd_degree_sq` this makes
`E(G) = Σ_c (deg gcd)²` an exact identity on smooth domains (the `≤` there was only the
toFinset/multiplicity gap, now closed).

Issue #389.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.SubgroupRepresentationRoots

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The representation set EQUALS the gcd root set** (both inclusions, unconditional).
Forward is `representationSet_subset_gcd_roots`; reverse: a root `z` of
`gcd(Xⁿ−1, (C c−X)ⁿ−1)` is a root of both factors, so `zⁿ = 1` (hence `z ∈ G`) and
`(c−z)ⁿ = 1` (hence `c − z ∈ G`). -/
theorem representationSet_eq_gcd_roots (G : Finset F) {n : ℕ} (hn : 0 < n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (c : F) :
    G.filter (fun z => c - z ∈ G)
      = (gcd (X ^ n - 1 : F[X]) (reprPoly c n)).roots.toFinset := by
  classical
  apply Finset.Subset.antisymm (representationSet_subset_gcd_roots G hn hGmem c)
  intro z hz
  have hgne : gcd (X ^ n - 1 : F[X]) (reprPoly c n) ≠ 0 := by
    intro h; rw [_root_.gcd_eq_zero_iff] at h; exact X_pow_sub_one_ne_zero hn h.1
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hgne, Polynomial.IsRoot.def] at hz
  -- `z` is a root of both `Xⁿ−1` and `reprPoly c n` since the gcd divides each
  have hz1 : (X ^ n - 1 : F[X]).eval z = 0 :=
    Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (gcd_dvd_left _ _) hz
  have hz2 : (reprPoly c n).eval z = 0 :=
    Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (gcd_dvd_right _ _) hz
  -- decode the two root conditions into subgroup membership
  have hzn : z ^ n = 1 := by
    have := hz1
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one] at this
    exact sub_eq_zero.mp this
  have hcz : (c - z) ^ n = 1 := by
    have := hz2
    rw [reprPoly] at this
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one] at this
    exact sub_eq_zero.mp this
  exact Finset.mem_filter.mpr ⟨(hGmem z).mpr hzn, (hGmem (c - z)).mpr hcz⟩

/-- **The representation count equals the number of distinct gcd roots** (unconditional). -/
theorem representationCount_eq_gcd_roots_card (G : Finset F) {n : ℕ} (hn : 0 < n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (c : F) :
    (G.filter (fun z => c - z ∈ G)).card
      = (gcd (X ^ n - 1 : F[X]) (reprPoly c n)).roots.toFinset.card := by
  rw [representationSet_eq_gcd_roots G hn hGmem c]

/-- **The representation count IS the gcd degree, on smooth domains.** Under
`(n : F) ≠ 0` (so `Xⁿ−1` is separable, i.e. `char F ∤ n`) and `(Xⁿ−1).Splits` (the
domain is the full order-`n` subgroup, automatic when `n ∣ |F|−1`):
`r(c) = deg gcd(Xⁿ−1, (C c−X)ⁿ−1)` exactly.  Hence `GVRepBound G M` ⟺ the pure
gcd-degree bound `∀ c ≠ 0, deg gcd ≤ M` — the Stepanov target with no slack. -/
theorem representationCount_eq_gcd_degree (G : Finset F) {n : ℕ} (hn : 0 < n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1)
    (hsep : (n : F) ≠ 0) (hsplit : (X ^ n - 1 : F[X]).Splits) (c : F) :
    (G.filter (fun z => c - z ∈ G)).card
      = (gcd (X ^ n - 1 : F[X]) (reprPoly c n)).natDegree := by
  classical
  set d : F[X] := gcd (X ^ n - 1 : F[X]) (reprPoly c n) with hd
  have hXne : (X ^ n - 1 : F[X]) ≠ 0 := X_pow_sub_one_ne_zero hn
  have hdne : d ≠ 0 := by
    rw [hd]; intro h; rw [_root_.gcd_eq_zero_iff] at h; exact hXne h.1
  -- `Xⁿ−1` is separable ⟹ squarefree; the gcd divides it, so the gcd is squarefree
  have hXsep : (X ^ n - 1 : F[X]).Separable := by
    have := separable_X_pow_sub_C (1 : F) hsep one_ne_zero
    simpa using this
  have hdsep : d.Separable := hXsep.of_dvd (hd ▸ gcd_dvd_left _ _)
  -- separable ⟹ roots have no duplicates ⟹ toFinset.card = roots.card
  have hnodup : d.roots.Nodup := Polynomial.nodup_roots hdsep
  -- the gcd splits (divides the split `Xⁿ−1`) ⟹ roots.card = natDegree
  have hdsplit : d.Splits := hsplit.of_dvd hXne (hd ▸ gcd_dvd_left _ _)
  rw [representationCount_eq_gcd_roots_card G hn hGmem c, ← hd,
    Multiset.toFinset_card_of_nodup hnodup,
    Polynomial.splits_iff_card_roots.mp hdsplit]

end ArkLib.ProximityGap.SubgroupRepresentationRoots

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.SubgroupRepresentationRoots.representationCount_eq_gcd_degree
