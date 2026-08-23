/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Issue #232 — the COPRIME packet minimal polynomial: the named gate to three-prime
moduli (O106)

The O105 addendum gated the squarefree-`pqr` ℚ-classification on ONE lemma: the
generalization of `CRTPacketMinpoly.minpoly_adjoin_primitiveRoot_eq_packet` from
prime-power base roots to ARBITRARY coprime bases.  This file lands it:

* `minpoly_adjoin_coprime_eq_cyclotomic` — for `ξ` a primitive `m`-th root and `η`
  a primitive `r`-th root (char 0) with `Coprime m r`:
  `minpoly ℚ⟮ξ⟯ η = cyclotomic r ℚ⟮ξ⟯` — the `r`-th cyclotomic stays irreducible
  over ANY coprime cyclotomic extension, not only prime-power ones;
* `natDegree_minpoly_adjoin_coprime` — the degree extraction from that same
  linear-disjointness brick;
* `minpoly_adjoin_coprime_prime_eq_geom` — at `r` prime, in the geometric-packet
  shape `Σ_{t<r} X^(t·1)` consumed verbatim by
  `CRTDoubleSlice.slice_of_packet_minpoly`.

Proof = the CRTPacketMinpoly totient-tower pinch with the prime-power split
replaced by `Nat.totient_mul hco` (which is exactly why the generalization is
free): `φ(m·r) = φ(m)·φ(r)` bounds `[ℚ⟮ξ⟯⟮η⟯ : ℚ⟮ξ⟯] ≥ φ(r)` through the
ℚ-linear embedding `ℚ⟮ξ·η⟯ ↪ ℚ⟮ξ⟯⟮η⟯`, while `minpoly ∣ Φ_r` gives `≤`; monic +
divides + equal degree closes.

With this gate open, the squarefree-`pqr` classification route of the O105
addendum is pure composition: peel the `r`-direction by the slice engine at this
minpoly (base `m = pq`), reduce to the two-variable ℚ-classification per fiber
difference, and integrate.  Queued as the next brick.
-/

namespace CoprimePacketMinpoly

open Polynomial IntermediateField Module

private lemma isIntegral_of_pow_eq_one {F L : Type*} [Field F] [Field L]
    [Algebra F L] {x : L} {n : ℕ} (hn : 0 < n) (h : x ^ n = 1) :
    IsIntegral F x := by
  refine ⟨X ^ n - 1, monic_X_pow_sub_C 1 hn.ne', ?_⟩
  simp [eval₂_sub, eval₂_pow, h]

/-- **The coprime packet minimal polynomial**: over `K = ℚ⟮ξ⟯` with `ξ` a primitive
`m`-th root of unity, the minimal polynomial of a primitive `r`-th root `η`
(`Coprime m r`, char 0) is the FULL `r`-th cyclotomic — coprime cyclotomic
extensions never split each other's cyclotomics. -/
theorem minpoly_adjoin_coprime_eq_cyclotomic
    {L : Type*} [Field L] [CharZero L] {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r) (hco : Nat.Coprime m r)
    {ξ η : L} (hξ : IsPrimitiveRoot ξ m) (hη : IsPrimitiveRoot η r) :
    minpoly ℚ⟮ξ⟯ η = cyclotomic r ℚ⟮ξ⟯ := by
  classical
  have hn : 0 < m * r := Nat.mul_pos hm hr
  -- integrality of the three roots involved
  have hintξ : IsIntegral ℚ ξ := isIntegral_of_pow_eq_one hm hξ.pow_eq_one
  have hintηK : IsIntegral ℚ⟮ξ⟯ η := isIntegral_of_pow_eq_one hr hη.pow_eq_one
  -- `ξ * η` is a primitive `(m·r)`-th root of unity (coprime orders multiply)
  have h1 : orderOf ξ = m := hξ.eq_orderOf.symm
  have h2 : orderOf η = r := hη.eq_orderOf.symm
  have horder : orderOf (ξ * η) = m * r := by
    rw [(Commute.all ξ η).orderOf_mul_eq_mul_orderOf_of_coprime
      (by rw [h1, h2]; exact hco), h1, h2]
  have hζ : IsPrimitiveRoot (ξ * η) (m * r) :=
    horder ▸ IsPrimitiveRoot.orderOf (ξ * η)
  have hintζ : IsIntegral ℚ (ξ * η) := isIntegral_of_pow_eq_one hn hζ.pow_eq_one
  -- absolute degrees over ℚ via rationals-cyclotomic irreducibility
  have hrkK : finrank ℚ ℚ⟮ξ⟯ = m.totient := by
    rw [IntermediateField.adjoin.finrank hintξ, ← cyclotomic_eq_minpoly_rat hξ hm,
      natDegree_cyclotomic]
  have hrkZ : finrank ℚ ℚ⟮ξ * η⟯ = (m * r).totient := by
    rw [IntermediateField.adjoin.finrank hintζ, ← cyclotomic_eq_minpoly_rat hζ hn,
      natDegree_cyclotomic]
  -- finite dimensionality up the tower
  haveI : FiniteDimensional ℚ ℚ⟮ξ⟯ := IntermediateField.adjoin.finiteDimensional hintξ
  haveI : FiniteDimensional ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯ :=
    IntermediateField.adjoin.finiteDimensional hintηK
  haveI : FiniteDimensional ℚ ℚ⟮ξ⟯⟮η⟯ := Module.Finite.trans ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯
  -- `ξ * η` lives in `ℚ⟮ξ⟯⟮η⟯`
  have hξE : ξ ∈ ℚ⟮ξ⟯⟮η⟯ := by
    have h := ℚ⟮ξ⟯⟮η⟯.algebraMap_mem ⟨ξ, mem_adjoin_simple_self ℚ ξ⟩
    simpa using h
  have hηE : η ∈ ℚ⟮ξ⟯⟮η⟯ := mem_adjoin_simple_self ℚ⟮ξ⟯ η
  have hsub : ∀ {x : L}, x ∈ ℚ⟮ξ * η⟯ → x ∈ ℚ⟮ξ⟯⟮η⟯ := by
    intro x hx
    have hle : ℚ⟮ξ * η⟯ ≤ (ℚ⟮ξ⟯⟮η⟯).restrictScalars ℚ := by
      rw [adjoin_le_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact mul_mem hξE hηE
    exact hle hx
  -- ℚ-linear embedding gives the degree lower bound
  let f : ℚ⟮ξ * η⟯ →ₗ[ℚ] ℚ⟮ξ⟯⟮η⟯ :=
    { toFun := fun x => ⟨x.1, hsub x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective f := fun x y hxy => by
    have h1 := congrArg Subtype.val hxy
    exact Subtype.ext h1
  have hle : finrank ℚ ℚ⟮ξ * η⟯ ≤ finrank ℚ ℚ⟮ξ⟯⟮η⟯ :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have htower : finrank ℚ ℚ⟮ξ⟯ * finrank ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯ = finrank ℚ ℚ⟮ξ⟯⟮η⟯ :=
    Module.finrank_mul_finrank ℚ ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯
  -- the totient tower bound: `φ(r) ≤ natDegree (minpoly ℚ⟮ξ⟯ η)`
  have hdeg_ge : r.totient ≤ (minpoly ℚ⟮ξ⟯ η).natDegree := by
    have hmul : m.totient * r.totient
        ≤ m.totient * finrank ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯ := by
      calc m.totient * r.totient
          = (m * r).totient := (Nat.totient_mul hco).symm
        _ = finrank ℚ ℚ⟮ξ * η⟯ := hrkZ.symm
        _ ≤ finrank ℚ ℚ⟮ξ⟯⟮η⟯ := hle
        _ = finrank ℚ ℚ⟮ξ⟯ * finrank ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯ := htower.symm
        _ = m.totient * finrank ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯ := by rw [hrkK]
    have h2 : r.totient ≤ finrank ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯ :=
      Nat.le_of_mul_le_mul_left hmul (Nat.totient_pos.mpr hm)
    rwa [IntermediateField.adjoin.finrank hintηK] at h2
  -- divisibility: `minpoly ℚ⟮ξ⟯ η ∣ Φ_r` over `ℚ⟮ξ⟯`
  have hdvd : minpoly ℚ⟮ξ⟯ η ∣ cyclotomic r ℚ⟮ξ⟯ := by
    apply minpoly.dvd
    rw [aeval_def, ← eval_map, map_cyclotomic]
    exact hη.isRoot_cyclotomic hr
  -- monic divisor of matching degree
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintηK)
    (cyclotomic.monic _ _) hdvd (by rwa [natDegree_cyclotomic])).symm

/-- **The coprime tower degree**: adjoining a primitive `r`-th root to the
coprime cyclotomic field generated by a primitive `m`-th root has degree `φ(r)`. -/
theorem natDegree_minpoly_adjoin_coprime
    {L : Type*} [Field L] [CharZero L] {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r) (hco : Nat.Coprime m r)
    {ξ η : L} (hξ : IsPrimitiveRoot ξ m) (hη : IsPrimitiveRoot η r) :
    (minpoly ℚ⟮ξ⟯ η).natDegree = r.totient := by
  rw [minpoly_adjoin_coprime_eq_cyclotomic hm hr hco hξ hη, natDegree_cyclotomic]

/-- **The slice-engine shape at a prime outer root**: for `r` PRIME coprime to `m`,
`minpoly ℚ⟮ξ⟯ η = Σ_{t<r} X^(t·1)` — exactly the `hmin` hypothesis of
`CRTDoubleSlice.slice_of_packet_minpoly` at `(p, q) = (r, 1)`. -/
theorem minpoly_adjoin_coprime_prime_eq_geom
    {L : Type*} [Field L] [CharZero L] {m r : ℕ}
    (hm : 0 < m) (hrp : r.Prime) (hco : Nat.Coprime m r)
    {ξ η : L} (hξ : IsPrimitiveRoot ξ m) (hη : IsPrimitiveRoot η r) :
    minpoly ℚ⟮ξ⟯ η = ∑ t ∈ Finset.range r, (X : Polynomial ℚ⟮ξ⟯) ^ (t * 1) := by
  haveI : Fact r.Prime := ⟨hrp⟩
  rw [minpoly_adjoin_coprime_eq_cyclotomic hm hrp.pos hco hξ hη,
    cyclotomic_prime ℚ⟮ξ⟯ r]
  exact Finset.sum_congr rfl fun t _ => by rw [mul_one]

end CoprimePacketMinpoly

#print axioms CoprimePacketMinpoly.minpoly_adjoin_coprime_eq_cyclotomic
#print axioms CoprimePacketMinpoly.natDegree_minpoly_adjoin_coprime
#print axioms CoprimePacketMinpoly.minpoly_adjoin_coprime_prime_eq_geom
