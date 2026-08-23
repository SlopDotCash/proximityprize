/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FarLineIncidenceEquivariance
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# The monomial-line bridge: MCA threshold of `RS[k]` ⟺ list-decoding of `RS[k+1]` (issue #389)

The cyclic lever (`FarLineIncidenceEquivariance`) shows the far-line incidence `I(δ)` is invariant
under the `Z/n` dilation group of `μ_n`, so the **extremal far directions are the dilation-fixed
ones — the monomials `X^a`**. This file pins down what the incidence *is* for the basic monomial
direction `u₁ = X^k` (degree exactly `k`, the first direction outside `RS[k]`), and the answer is a
pure **list-decoding** quantity of the **one-dimension-larger** code `RS[k+1]`:

> **`badScalars_monomial_eq_degreeLTSucc`** — `γ` is a bad scalar of the line `(u₀, X^k)` for `RS[k]`
> at radius `δ` **iff** there is a polynomial `q` of degree `< k+1` whose `X^k`-coefficient is `−γ`
> and whose evaluation `(1−δ)n`-agrees with `u₀`.

The mechanism is the **`+1`-degree lift**: `u₀ + γ·X^k` agrees with `c = eval(p)` (`deg p < k`) on a
witness set `iff` `u₀` agrees with `eval(p − γ·X^k)` there, and `p − γ·X^k ∈ RS[k+1]` has
`X^k`-coefficient `−γ`. So bad scalars of `RS[k]` are exactly the **leading coefficients** of the
`RS[k+1]`-codewords that `(1−δ)n`-agree with `u₀`.

**Why this is the unification of the two grand challenges.** Reading the equivalence as a count,

  `#{bad γ} = #{distinct X^k-coefficients in the (1−δ)n-agreement list of RS[k+1] around u₀}`
            `≤ |list-decoding list of RS[k+1] at radius δn|`.

Through the governing law `δ* = sup{δ : max-far-line I(δ) ≤ q·ε*}` (and the cyclic lever making
monomials extremal), the **grand MCA challenge** (pin `δ*` for `RS[k]`) is therefore controlled by
the **grand list-decoding challenge** (the list size of `RS[k+1]` beyond Johnson) — the very pair the
companion paper poses together. The `+1` in the dimension is the extra frequency the far monomial
direction injects; it is the concrete, computable form of the BGM higher-order-MDS ⟺ list-decoding
correspondence, specialised to the prize domain. The residual `(R) = κ_d` ("worst ≤ average") becomes
exactly "the `RS[k+1]` list concentrates to its first moment", i.e. the list-decoding prize itself.

This file proves the exact equivalence (the bridge); the cardinality bound and the `δ*` bracket are
its immediate corollaries. Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Finset Polynomial
open scoped NNReal

namespace ProximityGap.FarCosetExplosion

open ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The monomial-line bridge (exact form).** For the basic far monomial direction `u₁ = X^k`, a
scalar `γ` is bad for the line `(u₀, X^k)` over `RS[k] = code domain k` at radius `δ` **iff** there is
a polynomial `q` of degree `< k+1` with `X^k`-coefficient `−γ` whose Reed–Solomon evaluation agrees
with `u₀` on a witness-sized (`≥ (1−δ)n`) set. The bad scalars of `RS[k]` are precisely the leading
coefficients of the `RS[k+1]`-codewords that `(1−δ)n`-agree with `u₀` — the `+1`-degree lift linking
the MCA threshold to list decoding. -/
theorem badScalars_monomial_eq_degreeLTSucc (domain : ι ↪ F) (δ : ℝ≥0) (u₀ : ι → F) (k : ℕ)
    (γ : F) :
    γ ∈ explainableScalars (F := F) (↑(ReedSolomon.code domain k) : Set (ι → F)) δ u₀
          (ReedSolomon.evalOnPoints domain (X ^ k))
      ↔ ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
          ∃ q : F[X], q ∈ Polynomial.degreeLT F (k + 1) ∧ q.coeff k = -γ ∧
            ∀ i ∈ S, ReedSolomon.evalOnPoints domain q i = u₀ i := by
  classical
  simp only [explainableScalars, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨S, hsz, w, hwC, hw⟩
    -- `w = eval p`, `deg p < k`; take `q = p − γ • X^k ∈ RS[k+1]`, leading coeff `−γ`.
    rw [SetLike.mem_coe, ReedSolomon.code, Submodule.mem_map] at hwC
    obtain ⟨p, hpdeg, hpw⟩ := hwC
    rw [Polynomial.mem_degreeLT] at hpdeg
    refine ⟨S, hsz, p - γ • X ^ k, ?_, ?_, ?_⟩
    · rw [Polynomial.mem_degreeLT]
      refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_trans hpdeg (by exact_mod_cast Nat.lt_succ_self k)
      · calc (γ • X ^ k).degree ≤ (X ^ k : F[X]).degree := Polynomial.degree_smul_le γ _
          _ = (k : WithBot ℕ) := Polynomial.degree_X_pow k
          _ < ((k + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self k
    · rw [Polynomial.coeff_sub, Polynomial.coeff_smul, Polynomial.coeff_eq_zero_of_degree_lt hpdeg,
        Polynomial.coeff_X_pow, if_pos rfl, smul_eq_mul, mul_one, zero_sub]
    · intro i hiS
      have hev : ReedSolomon.evalOnPoints domain (p - γ • X ^ k) i
          = ReedSolomon.evalOnPoints domain p i
            - γ • ReedSolomon.evalOnPoints domain (X ^ k) i := by
        simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply]
      rw [hev, hpw, hw i hiS, add_sub_cancel_right]
  · rintro ⟨S, hsz, q, hqdeg, hqcoeff, hq⟩
    -- `p = q + γ • X^k` has degree `< k` (the `X^k` term cancels); `w = eval p ∈ RS[k]`.
    rw [Polynomial.mem_degreeLT] at hqdeg
    refine ⟨S, hsz, ReedSolomon.evalOnPoints domain (q + γ • X ^ k), ?_, ?_⟩
    · rw [SetLike.mem_coe, ReedSolomon.code, Submodule.mem_map]
      refine ⟨q + γ • X ^ k, ?_, rfl⟩
      rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      rw [Polynomial.coeff_add, Polynomial.coeff_smul, Polynomial.coeff_X_pow, smul_eq_mul]
      rcases eq_or_lt_of_le hm with hmk | hlt
      · rw [← hmk, hqcoeff, if_pos rfl, mul_one, neg_add_cancel]
      · rw [Polynomial.coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le hqdeg (by exact_mod_cast Nat.succ_le_of_lt hlt)),
          if_neg (by omega), mul_zero, add_zero]
    · intro i hiS
      have hev : ReedSolomon.evalOnPoints domain (q + γ • X ^ k) i
          = ReedSolomon.evalOnPoints domain q i
            + γ • ReedSolomon.evalOnPoints domain (X ^ k) i := by
        simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply]
      rw [hev, hq i hiS]

/-- **Evaluation is injective on low-degree polynomials.** Over `≥ d` distinct points, the only
degree-`<d` polynomial that evaluates to a fixed word is unique — a degree-`<d` difference vanishing
at `d` points is `0`. (`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`.) -/
private theorem evalOnPoints_inj_of_degree_lt {d : ℕ} (domain : ι ↪ F)
    (hd : d ≤ Fintype.card ι) {q q' : F[X]}
    (hq : q.degree < (d : WithBot ℕ)) (hq' : q'.degree < (d : WithBot ℕ))
    (h : ReedSolomon.evalOnPoints domain q = ReedSolomon.evalOnPoints domain q') : q = q' := by
  rw [← sub_eq_zero]
  have hdeg : (q - q').degree < (d : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hq hq')
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (q - q') (Finset.univ.map domain)
  · intro x hx
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    have hi := congrFun h i
    simp only [ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk] at hi
    rw [Polynomial.eval_sub, hi, sub_self]
  · rw [Finset.card_map, Finset.card_univ]
    by_cases hz : q - q' = 0
    · simp only [hz, Polynomial.natDegree_zero]; exact Fintype.card_pos
    · calc (q - q').natDegree < d := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hdeg
        _ ≤ Fintype.card ι := hd

/-- **The MCA bad-count is bounded by the list-decoding list size of `RS[k+1]` (the literal
inequality).** When `k+1 ≤ n` (so evaluation pins down the lifted polynomial), the number of bad
scalars of the monomial line `(u₀, X^k)` for `RS[k]` at radius `δ` is at most the number of
`RS[k+1]`-codewords that `(1−δ)n`-agree with `u₀` — i.e. the size of the radius-`δn` list of the
`+1`-lifted code. The injection sends each bad `γ` to the lifted codeword, distinct because their
`X^k`-coefficients `−γ` differ and evaluation is injective in degree `< k+1`. This is the operative
form for the prize: any list lower bound on `RS[μ_n, k+1]` becomes a `δ*` upper bracket via
`epsMCA_ge_far_incidence`, and any list upper bound becomes a `δ*` lower bracket. -/
theorem badScalars_monomial_card_le_listSize (domain : ι ↪ F) (δ : ℝ≥0) (u₀ : ι → F) (k : ℕ)
    (hk : k + 1 ≤ Fintype.card ι) :
    let liftedList : Finset (ι → F) := by
      classical
      exact Finset.univ.filter (fun e : ι → F => e ∈ ReedSolomon.code domain (k + 1) ∧
        ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
          ∀ i ∈ S, e i = u₀ i)
    (explainableScalars (F := F) (↑(ReedSolomon.code domain k) : Set (ι → F)) δ u₀
        (ReedSolomon.evalOnPoints domain (X ^ k))).card
      ≤ liftedList.card := by
  classical
  dsimp only
  have key : ∀ γ ∈ explainableScalars (F := F) (↑(ReedSolomon.code domain k) : Set (ι → F)) δ u₀
        (ReedSolomon.evalOnPoints domain (X ^ k)),
      ∃ q : F[X], q ∈ Polynomial.degreeLT F (k + 1) ∧ q.coeff k = -γ ∧
        ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
          ∀ i ∈ S, ReedSolomon.evalOnPoints domain q i = u₀ i := by
    intro γ hγ
    obtain ⟨S, hS, q, hq, hc, ha⟩ := (badScalars_monomial_eq_degreeLTSucc domain δ u₀ k γ).mp hγ
    exact ⟨q, hq, hc, S, hS, ha⟩
  choose! qf hqmem hqcoeff Sf hScard hagree using key
  refine Finset.card_le_card_of_injOn (fun γ => ReedSolomon.evalOnPoints domain (qf γ)) ?_ ?_
  · intro γ hγ
    rw [Finset.mem_coe]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rw [ReedSolomon.code, Submodule.mem_map]
      exact ⟨qf γ, hqmem γ hγ, rfl⟩
    · exact ⟨Sf γ, hScard γ hγ, hagree γ hγ⟩
  · intro γ hγ γ' hγ' heq
    rw [Finset.mem_coe] at hγ hγ'
    have hqq : qf γ = qf γ' :=
      evalOnPoints_inj_of_degree_lt domain hk
        (Polynomial.mem_degreeLT.mp (hqmem γ hγ)) (Polynomial.mem_degreeLT.mp (hqmem γ' hγ')) heq
    have : -γ = -γ' := by rw [← hqcoeff γ hγ, ← hqcoeff γ' hγ', hqq]
    simpa using this

end ProximityGap.FarCosetExplosion

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.FarCosetExplosion.badScalars_monomial_eq_degreeLTSucc
#print axioms ProximityGap.FarCosetExplosion.badScalars_monomial_card_le_listSize
