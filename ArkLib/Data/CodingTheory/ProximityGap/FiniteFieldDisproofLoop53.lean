/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ResultantLiftLoop52
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Loop 53 (O16, CLOSE) — the finite-field lifting, assembled: a finite field with a super-exponential
# §7 subset-sumset, **no remaining hypothesis**.

Assembles the seven resultant/Dirichlet/cyclotomic pillars of Loop52 into the existence the
finite-field §7 disproof needs, with **no abstract hypothesis left**:

> `exists_finiteField_subsetSumset_large`: for every `m ≥ 1` there is a prime `p` and a primitive
> `2^m`-th root of unity `ζ ∈ F_p` whose subset-sumset over `Fin (2^{m-1})` has `≥ 2^{2^{m-1}}`
> elements — **super-exponential in the domain `2^m`**.

With `thm71_no_fixed_exponent` (Loop46) this **disproves the §7 minimal-domain prize over a genuine
finite field**. See `DISPROOF_LOG.md` (O16/Loop53).
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.FiniteFieldDisproofLoop53

open ArkLib.ProximityGap.ResultantLiftLoop52

variable {N : ℕ}

/-- The integer polynomial `f_S = ∑_{j ∈ S} X^j`. -/
noncomputable def fpoly (S : Finset (Fin N)) : Polynomial ℤ := ∑ j ∈ S, X ^ (j : ℕ)

/-- `f_S.coeff k = 1` if `k = (j:ℕ)` for some `j ∈ S`, else `0`. -/
theorem fpoly_coeff (S : Finset (Fin N)) (k : ℕ) :
    (fpoly S).coeff k = if k ∈ S.image (fun j : Fin N => (j : ℕ)) then 1 else 0 := by
  classical
  rw [fpoly, finset_sum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_boole]
  by_cases hk : k ∈ S.image (fun j : Fin N => (j : ℕ))
  · rw [if_pos hk]
    obtain ⟨j, hjS, hjk⟩ := Finset.mem_image.mp hk
    have : S.filter (fun j' : Fin N => k = (j' : ℕ)) = {j} := by
      ext j'
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hj'⟩; exact Fin.ext (hjk ▸ hj'.symm)
      · rintro rfl; exact ⟨hjS, hjk.symm⟩
    rw [this]; simp
  · rw [if_neg hk]
    rw [Finset.filter_eq_empty_iff.mpr, Finset.card_empty, Nat.cast_zero]
    intro j hjS hj'
    exact hk (Finset.mem_image.mpr ⟨j, hjS, hj'.symm⟩)

/-- Every coefficient of `f_S − f_T` lies in `{-1, 0, 1}`. -/
theorem fpoly_sub_coeff_cases (S T : Finset (Fin N)) (k : ℕ) :
    (fpoly S - fpoly T).coeff k = -1 ∨ (fpoly S - fpoly T).coeff k = 0
      ∨ (fpoly S - fpoly T).coeff k = 1 := by
  rw [coeff_sub, fpoly_coeff, fpoly_coeff]
  by_cases h1 : k ∈ S.image (fun j : Fin N => (j : ℕ)) <;>
    by_cases h2 : k ∈ T.image (fun j : Fin N => (j : ℕ)) <;> simp [h1, h2]

/-- `f_S = f_T ↔ S = T` — distinct subsets give distinct polynomials. -/
theorem fpoly_injective : Function.Injective (fpoly (N := N)) := by
  classical
  intro S T h
  ext j
  have hc := congrArg (fun q => Polynomial.coeff q (j : ℕ)) h
  simp only [fpoly_coeff] at hc
  have hS : ((j : ℕ) ∈ S.image (fun j : Fin N => (j : ℕ))) ↔ j ∈ S := by
    simp [Finset.mem_image, Fin.val_inj]
  have hT : ((j : ℕ) ∈ T.image (fun j : Fin N => (j : ℕ))) ↔ j ∈ T := by
    simp [Finset.mem_image, Fin.val_inj]
  by_cases hjS : j ∈ S <;> by_cases hjT : j ∈ T <;> simp_all

/-- `deg (f_S) < N` (each monomial `X^j` has `j < N`). -/
theorem fpoly_natDegree_lt (hN : 0 < N) (S : Finset (Fin N)) : (fpoly S).natDegree < N := by
  classical
  have hdeg : (fpoly S).degree < (N : WithBot ℕ) := by
    rw [fpoly]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe N)).mpr fun j _ => ?_
    exact lt_of_le_of_lt (degree_X_pow_le _) (WithBot.coe_lt_coe.mpr j.isLt)
  by_cases h0 : fpoly S = 0
  · rw [h0]; simpa using hN
  · rwa [natDegree_lt_iff_degree_lt h0]

/-- `(f_S mod φ)(ζ) = ∑_{j ∈ S} ζ^j` — the subset sum is the evaluation of `f_S`. -/
theorem fpoly_map_eval {R : Type*} [CommRing R] (φ : ℤ →+* R) (ζ : R) (S : Finset (Fin N)) :
    ((fpoly S).map φ).eval ζ = ∑ j ∈ S, ζ ^ (j : ℕ) := by
  rw [fpoly, Polynomial.map_sum, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_pow, map_X, Polynomial.eval_pow, eval_X]

/-- The leading coefficient of `f_S − f_T` (for `S ≠ T`) is `±1`, hence nonzero mod any prime `p`. -/
theorem fpoly_sub_leadingCoeff_cast_ne {p : ℕ} [Fact p.Prime] {S T : Finset (Fin N)}
    (hST : S ≠ T) : (((fpoly S - fpoly T).leadingCoeff : ℤ) : ZMod p) ≠ 0 := by
  have hne : fpoly S - fpoly T ≠ 0 := sub_ne_zero.mpr fun h => hST (fpoly_injective h)
  have hlc0 : (fpoly S - fpoly T).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hne
  have : (fpoly S - fpoly T).leadingCoeff = -1 ∨ (fpoly S - fpoly T).leadingCoeff = 1 := by
    rcases fpoly_sub_coeff_cases S T (fpoly S - fpoly T).natDegree with h | h | h
    · exact Or.inl h
    · exact absurd h hlc0
    · exact Or.inr h
  rcases this with h | h <;> rw [h] <;> simp

/-- **The finite-field §7 disproof core (Loop53 capstone), no remaining hypothesis.** For every
`m ≥ 1` there is a prime `p` and a primitive `2^m`-th root of unity `ζ ∈ F_p` whose subset-sumset over
`Fin (2^{m-1})` has `≥ 2^{2^{m-1}}` elements — **super-exponential in the domain `2^m`**. With
`thm71_no_fixed_exponent` (Loop46) this disproves the §7 minimal-domain prize over a genuine finite
field. -/
theorem exists_finiteField_subsetSumset_large {m : ℕ} (hm : 1 ≤ m) :
    ∃ p : ℕ, p.Prime ∧ ∃ ζ : ZMod p, IsPrimitiveRoot ζ (2 ^ m) ∧
      2 ^ (2 ^ (m - 1)) ≤
        (Finset.univ.image
          (fun S : Finset (Fin (2 ^ (m - 1))) => ∑ j ∈ S, ζ ^ (j : ℕ))).card := by
  classical
  set N := 2 ^ (m - 1) with hNdef
  have hNpos : 0 < N := by positivity
  -- family of differences over ordered pairs (constant `1` on the diagonal)
  set gs : Finset (Fin N) × Finset (Fin N) → Polynomial ℤ :=
    fun ST => if ST.1 = ST.2 then 1 else fpoly ST.1 - fpoly ST.2 with hgs
  have hcop : ∀ ST, IsCoprime ((gs ST).map (Int.castRingHom ℚ))
      ((cyclotomic (2 ^ m) ℤ).map (Int.castRingHom ℚ)) := by
    rintro ⟨S, T⟩
    by_cases hST : S = T
    · simp only [hgs, if_pos hST, Polynomial.map_one]; exact isCoprime_one_left
    · simp only [hgs, if_neg hST]
      refine diff_coprime_cyclotomic_rat hm _ ?_ (sub_ne_zero.mpr fun h => hST (fpoly_injective h))
      calc (fpoly S - fpoly T).natDegree
          ≤ max (fpoly S).natDegree (fpoly T).natDegree := natDegree_sub_le _ _
        _ < N := by
            rw [max_lt_iff]; exact ⟨fpoly_natDegree_lt hNpos S, fpoly_natDegree_lt hNpos T⟩
  -- a Dirichlet prime `p ≡ 1 (mod 2^m)` with no common resultant
  have hq2 : 2 ≤ 2 ^ m := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm
  obtain ⟨p, hpp, hpmod, hpndvd⟩ :=
    exists_good_prime_no_common_resultant (q := 2 ^ m) hq2 (cyclotomic (2 ^ m) ℤ) gs hcop
  haveI : Fact p.Prime := ⟨hpp⟩
  -- `2^m ∣ p − 1`, so a primitive root exists
  have hdvd : 2 ^ m ∣ p - 1 := by
    have h1 : (p : ZMod (2 ^ m)) = ((1 : ℕ) : ZMod (2 ^ m)) := by push_cast; exact hpmod
    exact (Nat.modEq_iff_dvd' hpp.one_lt.le).mp
      ((ZMod.natCast_eq_natCast_iff _ _ _).mp h1).symm
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_zmod hm hdvd
  -- `ζ` is a root of `Φ mod p`
  have hζroot : ((cyclotomic (2 ^ m) ℤ).map (Int.castRingHom (ZMod p))).IsRoot ζ := by
    rw [map_cyclotomic_int]; exact hζ.isRoot_cyclotomic (by positivity)
  refine ⟨p, hpp, ζ, hζ, ?_⟩
  -- injectivity of the subset-sum map ⟹ image of full cardinality
  have hinj : Function.Injective
      (fun S : Finset (Fin N) => ∑ j ∈ S, ζ ^ (j : ℕ)) := by
    intro S T heq
    by_contra hST
    -- collision ⟹ `ζ` is a common root of `f_S − f_T` and `Φ` mod `p`
    have hroot : ((fpoly S - fpoly T).map (Int.castRingHom (ZMod p))).IsRoot ζ := by
      rw [IsRoot.def, Polynomial.map_sub, Polynomial.eval_sub, fpoly_map_eval, fpoly_map_eval]
      exact sub_eq_zero.mpr heq
    have hΦmonic : ((cyclotomic (2 ^ m) ℤ).leadingCoeff : ZMod p) ≠ 0 := by
      rw [(cyclotomic.monic (2 ^ m) ℤ).leadingCoeff]; simp
    have hdvdRes := prime_dvd_resultant_of_common_root (fpoly S - fpoly T) (cyclotomic (2 ^ m) ℤ)
      (fpoly_sub_leadingCoeff_cast_ne hST) hΦmonic hroot hζroot
    refine hpndvd (S, T) ?_
    have hgseq : gs (S, T) = fpoly S - fpoly T := by simp only [hgs, if_neg hST]
    rw [hgseq]; exact hdvdRes
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_finset,
    Fintype.card_fin]

/-- **Super-exponential beats any fixed power**: for every `c`, some `m ≥ 1` has `m·c < 2^{m-1}`.
Witness `m = 2^{c+1} + 1`: `(B+1)·c < B·(c+1) ≤ 2^{c+1}·2^c = 2^{2c+1} ≤ 2^{2^{c+1}}` with `B = 2^{c+1}`. -/
theorem exists_m_gap (c : ℕ) : ∃ m, 1 ≤ m ∧ m * c < 2 ^ (m - 1) := by
  refine ⟨2 ^ (c + 1) + 1, Nat.le_add_left 1 _, ?_⟩
  rw [Nat.add_sub_cancel]
  set B := 2 ^ (c + 1) with hB
  have hc1 : c + 1 ≤ 2 ^ c := Nat.lt_two_pow_self
  have hcB : c < B := by
    have h2 : (2 : ℕ) ^ c ≤ 2 ^ (c + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ c)
    omega
  calc (B + 1) * c < B * (c + 1) := by rw [add_one_mul, Nat.mul_succ]; omega
    _ ≤ 2 ^ (c + 1) * 2 ^ c := by rw [hB]; gcongr
    _ = 2 ^ (2 * c + 1) := by rw [← pow_add]; congr 1; ring
    _ ≤ 2 ^ B := by
        rw [hB]
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have h2 : 2 * (c + 1) ≤ 2 ^ (c + 1) := by
          calc 2 * (c + 1) ≤ 2 * 2 ^ c := by omega
            _ = 2 ^ (c + 1) := by rw [pow_succ]; ring
        omega

/-- **End-to-end disproof: the §7 bad count exceeds any fixed prize bound `(domain)^{c₁}` over a
genuine finite field.** For every fixed prize exponent `c₁` there is a prime `p`, a primitive `2^m`-th
root `ζ ∈ F_p`, with the subset-sumset (the §7 bad-scalar count) over the minimal domain `D = 2^m`
satisfying `D^{c₁} < bad`. Since `c₁` is arbitrary and `D` is the (fixed-by-gap) domain, **no fixed
`q`-independent prize exponent survives**: the §7 minimal-domain prize-as-stated is refuted over a real
finite field. This wires `exists_finiteField_subsetSumset_large` into the `no_fixed_exponent` form. -/
theorem prize_exponent_refuted_finiteField (c₁ : ℕ) :
    ∃ (m p : ℕ), 1 ≤ m ∧ p.Prime ∧ ∃ ζ : ZMod p, IsPrimitiveRoot ζ (2 ^ m) ∧
      (2 ^ m) ^ c₁ <
        (Finset.univ.image
          (fun S : Finset (Fin (2 ^ (m - 1))) => ∑ j ∈ S, ζ ^ (j : ℕ))).card := by
  obtain ⟨m, hm1, hgap⟩ := exists_m_gap c₁
  obtain ⟨p, hpp, ζ, hζ, hcard⟩ := exists_finiteField_subsetSumset_large hm1
  refine ⟨m, p, hm1, hpp, ζ, hζ, lt_of_lt_of_le ?_ hcard⟩
  -- `(2^m)^c₁ = 2^(m·c₁) < 2^(2^(m-1))`
  rw [← pow_mul]
  exact Nat.pow_lt_pow_right (by norm_num) hgap

/-- A linear-in-`m` budget is eventually beaten by `2^{m-1}`: `∃ m ≥ 1, m·a + (m-1)·b + k < 2^{m-1}`.
Bounds `m·a + (m-1)·b + k ≤ m·(a+b+k)` (for `m ≥ 1`) and applies `exists_m_gap`. -/
theorem exists_numerator_gap (a b k : ℕ) :
    ∃ m, 1 ≤ m ∧ m * a + (m - 1) * b + k < 2 ^ (m - 1) := by
  obtain ⟨m, hm1, hgap⟩ := exists_m_gap (a + b + k)
  refine ⟨m, hm1, lt_of_le_of_lt ?_ hgap⟩
  have hk : k ≤ m * k := Nat.le_mul_of_pos_left k hm1
  have hb : (m - 1) * b ≤ m * b := Nat.mul_le_mul_right b (Nat.sub_le m 1)
  calc m * a + (m - 1) * b + k ≤ m * a + m * b + m * k := by omega
    _ = m * (a + b + k) := by ring

/-- **O11 CLOSED: the §7 minimal-domain bad count provably exceeds the prize numerator over a finite
field.** Loop46's `thm71_refutes_prize` left open *"whether `a > num` is realizable at a smooth
subgroup (O11)."* It is. At the minimal domain (`ρ = 2^{-r}`, `η = 2^{1-m}`, domain `2^m`) the prize
numerator `(2^m)^{c₁}/(ρ^{c₂} η^{c₃})` equals `2^{m·c₁} · 2^{r·c₂} · 2^{(m-1)·c₃}`, which is `2^{O(m)}`,
while the realized §7 bad count (the subset-sumset of `2^m`-th roots of unity in `F_p`, Loop53) is
`≥ 2^{2^{m-1}}` — doubly-exponential. So for every fixed prize triple `(c₁,c₂,c₃)` and prize rate
`ρ = 2^{-r}`, a genuine finite field realizes `num < a`, and (via `thm71_refutes_prize`) the §7 MCA
contribution `a/q` strictly exceeds the prize RHS `(1/q)·num`. The §7 minimal-domain prize is refuted
in terms of the actual `ε_mca` quantity, no realizability gap. -/
theorem badCount_exceeds_prize_numerator (c₁ c₂ c₃ r : ℕ) :
    ∃ (m p : ℕ), 1 ≤ m ∧ p.Prime ∧ ∃ ζ : ZMod p, IsPrimitiveRoot ζ (2 ^ m) ∧
      2 ^ (m * c₁) * 2 ^ (r * c₂) * 2 ^ ((m - 1) * c₃) <
        (Finset.univ.image
          (fun S : Finset (Fin (2 ^ (m - 1))) => ∑ j ∈ S, ζ ^ (j : ℕ))).card := by
  obtain ⟨m, hm1, hgap⟩ := exists_numerator_gap c₁ c₃ (r * c₂)
  obtain ⟨p, hpp, ζ, hζ, hcard⟩ := exists_finiteField_subsetSumset_large hm1
  refine ⟨m, p, hm1, hpp, ζ, hζ, lt_of_lt_of_le ?_ hcard⟩
  rw [← pow_add, ← pow_add]
  refine Nat.pow_lt_pow_right (by norm_num) ?_
  -- `m·c₁ + r·c₂ + (m-1)·c₃ = m·c₁ + (m-1)·c₃ + r·c₂ < 2^{m-1}`
  omega

/-! ## The field-size barrier — why this disproof is *minimal-domain only* (an honest delimiter)

The prize fixes `|F| < 2^256`. The bad count realized above is a *subset-sumset*, whose elements live
in `F_p`, so it is **capped by `p = |F_p|`**. The doubly-exponential `2^{2^{N-1}}` lower bound only
*bites* while it is below the field size; once the domain is large enough that `2^{2^{N-1}} ≥ p`
(`N = 2^{k-1}` for a domain of size `2^k`, so already `k ≥ 9` under `|F| < 2^256`), the realized bad
count is pinned at `≤ p`, a *bounded* quantity — and the prize numerator, growing with the domain,
absorbs it. This is the concrete, field-size form of `thm71_within_prize`: it is **structurally why no
roots-of-unity / §7 construction can disprove the *large-domain* prize**, and hence why pinning `δ*`
needs a genuinely different (super-poly-in-`n`-at-bounded-`|F|`) mechanism that is open. -/

/-- **Field-size cap on the realized bad count.** The subset-sumset over `F_p` has at most `p`
elements (its values are field elements). So the doubly-exponential `2^{2^{N-1}}` lower bound is only
meaningful when `p` is at least that large; at large domains under `|F| < 2^256` the bad count is
capped at `p` and the prize is not refuted by this construction. -/
theorem subsetSumset_card_le_field {p : ℕ} [Fact p.Prime] {n : ℕ} (ζ : ZMod p) :
    (Finset.univ.image
      (fun S : Finset (Fin n) => ∑ j ∈ S, ζ ^ (j : ℕ))).card ≤ p := by
  classical
  calc (Finset.univ.image (fun S : Finset (Fin n) => ∑ j ∈ S, ζ ^ (j : ℕ))).card
      ≤ Fintype.card (ZMod p) := Finset.card_le_univ _
    _ = p := ZMod.card p

end ArkLib.ProximityGap.FiniteFieldDisproofLoop53

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.FiniteFieldDisproofLoop53.exists_finiteField_subsetSumset_large
#print axioms ArkLib.ProximityGap.FiniteFieldDisproofLoop53.prize_exponent_refuted_finiteField
#print axioms ArkLib.ProximityGap.FiniteFieldDisproofLoop53.badCount_exceeds_prize_numerator
#print axioms ArkLib.ProximityGap.FiniteFieldDisproofLoop53.subsetSumset_card_le_field
