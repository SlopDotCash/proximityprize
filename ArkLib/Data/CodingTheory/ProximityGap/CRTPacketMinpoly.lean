/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CRTDoubleSlice
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

/-!
# Issue #232 — the packet minimal polynomial over the coprime cyclotomic extension

De Bruijn capstone step (1) from `CRTDoubleSlice` ("What remains for full de Bruijn"):
discharge the packet minimal-polynomial hypothesis of
`CRTDoubleSlice.slice_of_packet_minpoly` over `K = ℚ(ζ_{p^a})`.

* `minpoly_adjoin_primitiveRoot_eq_packet` — **the discharge**: for distinct primes
  `p ≠ q`, `b ≥ 1`, and primitive roots `ξ` (of order `p^a`) and `η` (of order `q^b`)
  in any characteristic-zero field `L`, the minimal polynomial of `η` over the
  intermediate field `ℚ⟮ξ⟯` IS the geometric packet `Σ_{t<q} X^(t·q^(b-1))`
  (= `Φ_{q^b}`, which stays irreducible over the coprime cyclotomic extension).
  Engine: `minpoly ℚ⟮ξ⟯ η ∣ Φ_{q^b}` plus the totient tower bound
  `φ(p^a)·φ(q^b) = φ(p^a q^b) = [ℚ(ξη):ℚ] ≤ [ℚ⟮ξ⟯⟮η⟯:ℚ] = φ(p^a)·[ℚ⟮ξ⟯⟮η⟯:ℚ⟮ξ⟯]`
  (`Nat.totient_mul` on coprimality + `Module.finrank_mul_finrank`), then monic
  divisor of matching degree (`eq_of_monic_of_dvd_of_natDegree_le`).
* `crt_fiber_slice_coprimePrimePowers` — **the headline corollary**: the CRT
  double-slice `CRTDoubleSlice.crt_fiber_slice` instantiated at `K = ℚ⟮ξ⟯`, now with
  NO minimal-polynomial hypothesis: any vanishing double sum `Σ_{(j,c)∈I} ξ^j·η^c = 0`
  over the coprime exponent grid `range (p^a) ×ˢ range (q^b)` has μ_q-shift invariant
  fiber sums `Σ_j [(j,c)∈I]·ξ^j`, as an unconditional statement about two primitive
  roots in any characteristic-zero field.

Falsified first: `scripts/probes/probe_crt_packet_minpoly.py` (exact integer/fraction
arithmetic, no floats; exit 0) — packet form of `Φ_{q^b}` (9 prime powers), the tower
equality as full rank of the `φ(n)×φ(n)` CRT power matrix over `ℚ[x]/Φ_n` at 10
coprime prime-power pairs up to `(25,3)`/`(27,4)`, and 5 overlap (non-coprime)
controls all rank-deficient — coprimality is measured load-bearing.  The probe also
documents the honest boundary: `(6,4)` with `gcd = 2` still has full rank
(`φ(6)φ(4) = φ(12)`), so the theorem's prime-power coprimality is sufficient but the
failure mode is totient multiplicativity, not gcd per se.

What remains for full de Bruijn (unchanged, named): (2) the exponent bijection
`μ_{p^a} × μ_{q^b} ≃ μ_n` converting subset sums of `μ_n` into grid double sums;
(3) the positivity/disjointness step — indicator fiber sums force DISJOINT rotated
packets — the genuinely de Bruijn part.
-/

namespace CRTPacketMinpoly

open Polynomial Finset IntermediateField Module

/-- Roots of unity are integral over any base field of the ambient field. -/
private lemma isIntegral_of_pow_eq_one {F L : Type*} [Field F] [Field L] [Algebra F L]
    {x : L} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) : IsIntegral F x :=
  ⟨X ^ m - 1, by simpa using monic_X_pow_sub_C (1 : F) hm.ne', by simp [hx]⟩

/-- **The packet minimal polynomial over the coprime cyclotomic extension** — the
de Bruijn capstone step (1).  For distinct primes `p ≠ q`, `0 < b`, a primitive
`p^a`-th root `ξ` and a primitive `q^b`-th root `η` in a characteristic-zero field
`L`, the minimal polynomial of `η` over `K = ℚ⟮ξ⟯ = ℚ(ζ_{p^a})` is the geometric
packet `Σ_{t<q} X^(t·q^(b-1))` — i.e. `Φ_{q^b}` remains irreducible over the coprime
cyclotomic extension.  This discharges the `hmin` hypothesis of
`CRTDoubleSlice.slice_of_packet_minpoly` / `CRTDoubleSlice.crt_fiber_slice`. -/
theorem minpoly_adjoin_primitiveRoot_eq_packet
    {L : Type*} [Field L] [CharZero L] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hb : 0 < b)
    {ξ η : L} (hξ : IsPrimitiveRoot ξ (p ^ a)) (hη : IsPrimitiveRoot η (q ^ b)) :
    minpoly ℚ⟮ξ⟯ η = ∑ t ∈ Finset.range q, (X : Polynomial ℚ⟮ξ⟯) ^ (t * q ^ (b - 1)) := by
  classical
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  have hqb : 0 < q ^ b := pow_pos hq.pos b
  have hn : 0 < p ^ a * q ^ b := Nat.mul_pos hpa hqb
  have hco : Nat.Coprime (p ^ a) (q ^ b) :=
    Nat.Coprime.pow a b ((Nat.coprime_primes hp hq).mpr hpq)
  -- integrality of the three roots involved
  have hintξ : IsIntegral ℚ ξ := isIntegral_of_pow_eq_one hpa hξ.pow_eq_one
  have hintηK : IsIntegral ℚ⟮ξ⟯ η := isIntegral_of_pow_eq_one hqb hη.pow_eq_one
  -- `ξ * η` is a primitive `(p^a * q^b)`-th root of unity (coprime orders multiply)
  have h1 : orderOf ξ = p ^ a := hξ.eq_orderOf.symm
  have h2 : orderOf η = q ^ b := hη.eq_orderOf.symm
  have horder : orderOf (ξ * η) = p ^ a * q ^ b := by
    rw [(Commute.all ξ η).orderOf_mul_eq_mul_orderOf_of_coprime
      (by rw [h1, h2]; exact hco), h1, h2]
  have hζ : IsPrimitiveRoot (ξ * η) (p ^ a * q ^ b) :=
    horder ▸ IsPrimitiveRoot.orderOf (ξ * η)
  have hintζ : IsIntegral ℚ (ξ * η) := isIntegral_of_pow_eq_one hn hζ.pow_eq_one
  -- absolute degrees over ℚ, via unconditional rationals-cyclotomic irreducibility
  have hrkK : finrank ℚ ℚ⟮ξ⟯ = (p ^ a).totient := by
    rw [IntermediateField.adjoin.finrank hintξ, ← cyclotomic_eq_minpoly_rat hξ hpa,
      natDegree_cyclotomic]
  have hrkZ : finrank ℚ ℚ⟮ξ * η⟯ = (p ^ a * q ^ b).totient := by
    rw [IntermediateField.adjoin.finrank hintζ, ← cyclotomic_eq_minpoly_rat hζ hn,
      natDegree_cyclotomic]
  -- finite dimensionality up the tower
  haveI : FiniteDimensional ℚ ℚ⟮ξ⟯ := IntermediateField.adjoin.finiteDimensional hintξ
  haveI : FiniteDimensional ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯ := IntermediateField.adjoin.finiteDimensional hintηK
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
      -- membership in `restrictScalars` is definitionally membership (`Iff.rfl`)
      exact mul_mem hξE hηE
    exact hle hx
  -- ℚ-linear embedding `ℚ⟮ξ * η⟯ ↪ ℚ⟮ξ⟯⟮η⟯` gives the degree lower bound
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
  -- the totient tower bound: `φ(q^b) ≤ natDegree (minpoly ℚ⟮ξ⟯ η)`
  have hdeg_ge : (q ^ b).totient ≤ (minpoly ℚ⟮ξ⟯ η).natDegree := by
    have hmul : (p ^ a).totient * (q ^ b).totient
        ≤ (p ^ a).totient * finrank ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯ := by
      calc (p ^ a).totient * (q ^ b).totient
          = (p ^ a * q ^ b).totient := (Nat.totient_mul hco).symm
        _ = finrank ℚ ℚ⟮ξ * η⟯ := hrkZ.symm
        _ ≤ finrank ℚ ℚ⟮ξ⟯⟮η⟯ := hle
        _ = finrank ℚ ℚ⟮ξ⟯ * finrank ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯ := htower.symm
        _ = (p ^ a).totient * finrank ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯ := by rw [hrkK]
    have h2 : (q ^ b).totient ≤ finrank ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯ :=
      Nat.le_of_mul_le_mul_left hmul (Nat.totient_pos.mpr hpa)
    rwa [IntermediateField.adjoin.finrank hintηK] at h2
  -- divisibility: `minpoly ℚ⟮ξ⟯ η ∣ Φ_{q^b}` over `ℚ⟮ξ⟯`
  have hdvd : minpoly ℚ⟮ξ⟯ η ∣ cyclotomic (q ^ b) ℚ⟮ξ⟯ := by
    apply minpoly.dvd
    rw [aeval_def, ← eval_map, map_cyclotomic]
    exact hη.isRoot_cyclotomic hqb
  -- monic divisor of matching degree: the minimal polynomial IS the cyclotomic
  have heq : cyclotomic (q ^ b) ℚ⟮ξ⟯ = minpoly ℚ⟮ξ⟯ η :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintηK)
      (cyclotomic.monic _ _) hdvd (by rwa [natDegree_cyclotomic])
  -- and at a prime power the cyclotomic is the geometric packet
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, (Nat.succ_pred_eq_of_pos hb).symm⟩
  rw [← heq, cyclotomic_prime_pow_eq_geom_sum hq]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Nat.add_sub_cancel, mul_comm t (q ^ b'), pow_mul]

/-- **The CRT double-slice for coprime prime powers, unconditionally** — the headline
corollary: `CRTDoubleSlice.crt_fiber_slice` instantiated at `K = ℚ⟮ξ⟯`, with the
packet minimal-polynomial hypothesis discharged by
`minpoly_adjoin_primitiveRoot_eq_packet`.  A vanishing double sum
`Σ_{(j,c)∈I} ξ^j · η^c = 0` over the coprime exponent grid
`range (p^a) ×ˢ range (q^b)` has μ_q-shift invariant fiber sums: for every residue
`s < q^(b-1)`, the value `Σ_{j<p^a} [(j, i·q^(b-1)+s) ∈ I]·ξ^j` is independent of
`i < q`.  No minimal-polynomial, intermediate-field, or cyclotomic hypothesis
remains — only the two primitive roots. -/
theorem crt_fiber_slice_coprimePrimePowers
    {L : Type*} [Field L] [CharZero L] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hb : 0 < b)
    {ξ η : L} (hξ : IsPrimitiveRoot ξ (p ^ a)) (hη : IsPrimitiveRoot η (q ^ b))
    (I : Finset (ℕ × ℕ)) (hI : I ⊆ Finset.range (p ^ a) ×ˢ Finset.range (q ^ b))
    (hsum : ∑ x ∈ I, ξ ^ x.1 * η ^ x.2 = 0)
    {i i' s : ℕ} (hi : i < q) (hi' : i' < q) (hs : s < q ^ (b - 1)) :
    (∑ j ∈ Finset.range (p ^ a), if (j, i * q ^ (b - 1) + s) ∈ I then ξ ^ j else 0)
      = ∑ j ∈ Finset.range (p ^ a), if (j, i' * q ^ (b - 1) + s) ∈ I then ξ ^ j else 0 := by
  classical
  have hb' : b - 1 + 1 = b := Nat.succ_pred_eq_of_pos hb
  have hqq : q * q ^ (b - 1) = q ^ b := by rw [← pow_succ', hb']
  set ξK : ℚ⟮ξ⟯ := ⟨ξ, mem_adjoin_simple_self ℚ ξ⟩ with hξK
  have hcoe : (algebraMap ℚ⟮ξ⟯ L) ξK = ξ := rfl
  have hmin := minpoly_adjoin_primitiveRoot_eq_packet hp hq hpq hb hξ hη
  have hsum' : ∑ x ∈ I, (algebraMap ℚ⟮ξ⟯ L ξK) ^ x.1 * η ^ x.2 = 0 := by
    simp only [hcoe]
    exact hsum
  have h := CRTDoubleSlice.crt_fiber_slice (Pn := p ^ a) (q := q) (Q' := q ^ (b - 1))
    hmin ξK I (by rwa [hqq]) hsum' hi hi' hs
  have h2 := congrArg (algebraMap ℚ⟮ξ⟯ L) h
  simpa [map_sum, apply_ite (algebraMap ℚ⟮ξ⟯ L), hcoe] using h2

/-- The brief's worked special case, now a one-liner: over `ℚ(ζ₄) = ℚ(i)`, the minimal
polynomial of a primitive cube root of unity is the full packet `1 + X + X²` —
`Φ₃` does not split over `ℚ(i)`. -/
example {L : Type*} [Field L] [CharZero L] {ξ η : L}
    (hξ : IsPrimitiveRoot ξ 4) (hη : IsPrimitiveRoot η 3) :
    minpoly ℚ⟮ξ⟯ η = 1 + X + X ^ 2 := by
  have h4 : IsPrimitiveRoot ξ (2 ^ 2) := by norm_num [hξ]
  have h3 : IsPrimitiveRoot η (3 ^ 1) := by norm_num [hη]
  have h := minpoly_adjoin_primitiveRoot_eq_packet (p := 2) (q := 3) (a := 2) (b := 1)
    Nat.prime_two Nat.prime_three (by norm_num) one_pos h4 h3
  rw [h]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  ring

/-- Non-vacuity of the corollary's hypothesis spine in a concrete field: the primitive
roots exist in `ℂ` (so the unconditional fiber-slice statement is genuinely about
satisfiable data; instantiated at the empty exponent set). -/
example :
    (∑ j ∈ Finset.range (2 ^ 2), if (j, 1 * 3 ^ (1 - 1) + 0) ∈ (∅ : Finset (ℕ × ℕ))
        then (Complex.exp (2 * Real.pi * Complex.I / 4)) ^ j else 0)
      = ∑ j ∈ Finset.range (2 ^ 2), if (j, 2 * 3 ^ (1 - 1) + 0) ∈ (∅ : Finset (ℕ × ℕ))
        then (Complex.exp (2 * Real.pi * Complex.I / 4)) ^ j else 0 := by
  have he4 : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 4)) 4 := by
    have h := Complex.isPrimitiveRoot_exp 4 (by norm_num)
    norm_num at h
    exact h
  have he3 : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 3)) 3 := by
    have h := Complex.isPrimitiveRoot_exp 3 (by norm_num)
    norm_num at h
    exact h
  have h4 : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 4)) (2 ^ 2) := by
    norm_num [he4]
  have h3 : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 3)) (3 ^ 1) := by
    norm_num [he3]
  exact crt_fiber_slice_coprimePrimePowers Nat.prime_two Nat.prime_three (by norm_num)
    one_pos h4 h3 ∅ (Finset.empty_subset _) (by simp) (by norm_num) (by norm_num)
    (by norm_num)

end CRTPacketMinpoly

#print axioms CRTPacketMinpoly.minpoly_adjoin_primitiveRoot_eq_packet
#print axioms CRTPacketMinpoly.crt_fiber_slice_coprimePrimePowers
