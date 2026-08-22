/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# R347: Stickelberger carry vectors — exact telescoping + Rank Lemma certificates

Session 2026-07-09 (#466), route `kummer-hecke-alignment`; companion to
`_R341CAZACCosetEquivalence.lean` (the exact Mellin ⟺ Gaussian-period-coset identity and
the named `MellinCAZACBound` / `SubgroupCosetSqrtCancellation` Props — untouched here).

## Where this sits in the route

This session's pen-and-paper Theorem A (classical; NOT formalized here) shows that for every
odd prime `m`, `limsup_{p ≡ 1 (m)} M_p = m − 1`, where `M_p = max_{τ∈μ_m} |Σ_{j=1}^{m-1} u_j τ^{-j}|`
is the r341 Mellin maximum of the normalized Gauss phases `u_j = g(χ^j)/√p` — so the literal
CAZAC `√(m log m)` bound fails unconditionally (modulo the classical inputs listed below).
The proof pipeline is: Kummer-shift invariance (`M_p` depends only on the Jacobi-sum angles
`β_k = arg(J(χ,χ^k)/√p)`, `k = 1..K`, `K = (m-1)/2` — the metaplectic/Kummer coordinate
cancels) → JOINT equidistribution of `(β_1..β_K)` on `T^K` → an alignment ball hits
infinitely often → `M_p ≥ (m-1)cos(2δ)`.

The joint-equidistribution step is Weil 1952 + PNT for Hecke L-functions + **one genuinely
NEW ingredient, the Rank Lemma**, whose combinatorial core this file machine-checks:

> **Rank Lemma** (session 2026-07-09; pen-and-paper for all odd primes `m`, via telescoping
> to Stickelberger elements `(a − σ_a)θ`, `ψ`-component factorization `(a − ψ(a))B_{1,ψ̄}`,
> and Dirichlet's `B_{1,ψ} ≠ 0` for odd `ψ`): for `m` an odd prime, the signed Stickelberger
> vectors `w_k = 2·v_k − 1 : ((ℤ/m)ˣ → ℚ)`, `k = 1..K`, are `ℚ`-linearly independent.

Here `v_k(t) = ⟨t/m⟩ + ⟨kt/m⟩ − ⟨(k+1)t/m⟩ ∈ {0,1}` is the Stickelberger fractional-weight
= the infinity-type of the Jacobi Hecke Grossencharacter `p̄ ↦ J(χ_p̄, χ_p̄^k)` of `ℚ(ζ_m)`
mod `m²` (Weil 1952, "Jacobi sums as Grössencharaktere", Trans. AMS 73; verified against
Watkins, Publ. Math. Besançon 2018, §2.1/§2.3.2/§4.3). The Rank Lemma forces every
nontrivial Weyl monomial `∏ ξ_k^{n_k}` of the unitarized Jacobi characters to have nonzero
infinity-type `Σ n_k (v_k − ½·1) ≠ 0`, hence infinite order, hence PNT-cancellation — which
is exactly what upgrades Weil's single-angle equidistribution to the JOINT statement the
alignment argument consumes (and it excludes self-dual characters, so no Landau–Siegel
issue arises in the family).

## Dictionary (session ↔ this file)

* `stickCarry m k t` = `v_k(t)` as a **carry indicator**: `v_k(t) = 1` iff
  `(t % m) + (k·t % m) ≥ m`.  That this equals the fractional-part expression is
  `stickCarry_mul_eq` (integer form, ALL `m k t`, no hypotheses — Lean `x % 0 = x`
  conventions included) and `stickCarry_fract` (genuine `Int.fract` form over `ℚ`, `0 < m`).
* `stickCarry_telescope` = the Stickelberger-element telescoping
  `Σ_{k=1}^{a} v_k = (a+1)⟨t/m⟩ − ⟨(a+1)t/m⟩`, i.e. the coefficient form of
  `Σ_{k<a} V_k = (a − σ_a)θ`.  The session had verified this exactly for all `m ≤ 200`
  (stick_rank.py); here it is a **general theorem** for all `m, t, a`.
* `signedStick m K` = the family `w_k = 2·v_k − 1` (twice the unitarized infinity-type
  `v_k − ½·1`), indexed `k : Fin K ↦ k+1`, `t : Fin (m-1) ↦ t+1` (for `m` prime the units
  of `ℤ/m` are exactly `1..m-1`).
* `stickRank_m3/m5/m7/m11/m13` = the Rank Lemma as machine-checked instances
  (`LinearIndependent ℚ`), tied directly to the `stickCarry` definition — no transcribed
  literal matrices in the statements.
* `stick_m8_relation` + `stickRank_m8_degenerate` = **primality is necessary**: at `m = 8`
  the Stickelberger kernel relation `w_3 = w_1` holds exactly on the units `{1,3,5,7}`
  (by `decide`), so the `K = 3` family is NOT linearly independent.  This finite-order
  relation (`ξ_3 ξ_1^{-1}` of finite order) is precisely what the session's numerics saw as
  the sharp `β_3 − β_1 ∈ {0, π}` atom at `m = 8` (jacobi_joint.py: four atoms of mass ≈ ¼,
  all other histogram bins 0.000) — a positive test of the Grossencharacter formalism, and
  the reason the refuter family is stated for odd prime `m` only.

Probe (exact integer/fraction arithmetic, run before formalizing; values match):
`scripts/probes/probe_r347_stickelberger_rank.py` — identity + telescoping sweeps
(`m ≤ 40` resp. `m ≤ 30`, incl. `m = 0` Lean conventions), full rank `K = (m-1)/2` for ALL
odd primes `m ≤ 200`, first-`K`-columns minors nonsingular for `m ∈ {3,5,7,11,13}`
(dets `-1, -2, 4, -16, -32`), and the `m = 8` kernel `w_3 = w_1` with rank `2 < 3`.

## PROVEN here (machine-checked, axiom-clean)

* `stickCarry_eq_zero_or_one` — the weight is a 0/1 indicator.
* `stickCarry_mul_eq` — `m·v_k(t) = (t % m) + (kt % m) − ((k+1)t % m)` for ALL `m, k, t`.
* `stickCarry_fract` — `v_k(t) = ⟨t/m⟩ + ⟨kt/m⟩ − ⟨(k+1)t/m⟩` with real `Int.fract` (`0 < m`).
* `stickCarry_telescope` — `m·Σ_{k=1}^{a} v_k(t) = (a+1)(t % m) − ((a+1)t % m)`, ALL `m, t, a`.
* `stickRank_m3`, `stickRank_m5`, `stickRank_m7`, `stickRank_m11`, `stickRank_m13` —
  `LinearIndependent ℚ (signedStick m K)` for `(m,K) ∈ {(3,1),(5,2),(7,3),(11,5),(13,6)}`.
* `stick_m8_relation`, `stickRank_m8_degenerate` — the `m = 8` kernel relation and the
  resulting failure of linear independence.

## NAMED OPEN / NOT DONE HERE (do not discharge)

* **General-`m` Rank Lemma**: needs Dirichlet `B_{1,ψ} ≠ 0` for odd `ψ` (equivalently
  `L(1,ψ) ≠ 0` through the functional equation) — beyond the current substrate; the per-`m`
  certificates above are the decide-style instances (any further fixed odd prime `m ≤ 200`
  can be added by the same script/pattern).
* **Joint equidistribution of Jacobi angles**: honest label (verifier-corrected):
  *derived — classical inputs (Weil 1952 Grossencharacter + Hecke-L PNT + Dirichlet
  `B_{1,ψ} ≠ 0`) + the new pen-and-paper Rank Lemma (machine-checked `m ≤ 200`) — not
  formalized*.  The JOINT statement is folklore-at-best in the literature; it is NOT stated
  as a Prop in this file (this brick is pure combinatorics; the route's consumer brick owns
  that named Prop).
* The r341 `MellinCAZACBound` is **neither discharged nor refuted in Lean** by this file;
  Theorem A / Corollary B remain pen-and-paper-grade with a machine-checked combinatorial
  core (this file).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R347StickelbergerRank

/-- The Stickelberger fractional weight `v_k(t) = ⟨t/m⟩ + ⟨kt/m⟩ − ⟨(k+1)t/m⟩ ∈ {0,1}` of
the Jacobi Hecke character `J(χ, χ^k)` at the embedding `t`, realized as the **carry
indicator** of the addition `(t % m) + (k·t % m)`.  (`stickCarry_mul_eq` /
`stickCarry_fract` prove the equality with the fractional-part expression.) -/
def stickCarry (m k t : ℕ) : ℤ := if t % m + k * t % m < m then 0 else 1

theorem stickCarry_eq_zero_or_one (m k t : ℕ) :
    stickCarry m k t = 0 ∨ stickCarry m k t = 1 := by
  unfold stickCarry
  split <;> simp

/-- Exact integer form of the Stickelberger weight, for ALL `m, k, t` (including the
degenerate `m = 0` under Lean's `x % 0 = x`): `m·v_k(t) = (t%m) + (kt%m) − ((k+1)t%m)`.
Dividing by `m` this is `v_k(t) = ⟨t/m⟩ + ⟨kt/m⟩ − ⟨(k+1)t/m⟩`. -/
theorem stickCarry_mul_eq (m k t : ℕ) :
    (m : ℤ) * stickCarry m k t
      = ((t % m : ℕ) : ℤ) + ((k * t % m : ℕ) : ℤ) - (((k + 1) * t % m : ℕ) : ℤ) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    unfold stickCarry
    simp only [Nat.mod_zero]
    rw [if_neg (by omega : ¬ (t + k * t < 0))]
    push_cast
    ring
  · have key : (k + 1) * t % m = (t % m + k * t % m) % m := by
      conv_lhs => rw [show (k + 1) * t = t + k * t by ring]
      rw [Nat.add_mod]
    by_cases h : t % m + k * t % m < m
    · rw [Nat.mod_eq_of_lt h] at key
      unfold stickCarry
      rw [if_pos h, key]
      push_cast
      ring
    · have ht : t % m < m := Nat.mod_lt _ hm
      have hkt : k * t % m < m := Nat.mod_lt _ hm
      have key2 : (k + 1) * t % m = t % m + k * t % m - m := by
        conv_lhs => rw [key, show t % m + k * t % m = m + (t % m + k * t % m - m) by omega]
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      unfold stickCarry
      rw [if_neg h, key2]
      have hcast : ((t % m + k * t % m - m : ℕ) : ℤ)
          = ((t % m : ℕ) : ℤ) + ((k * t % m : ℕ) : ℤ) - (m : ℤ) := by omega
      rw [hcast]
      ring

/-- The Stickelberger-element telescoping `Σ_{k=1}^{a} v_k(t) = (a+1)⟨t/m⟩ − ⟨(a+1)t/m⟩`
(coefficient form of `Σ_{k<a} V_k = (a − σ_a)θ`), as an exact integer identity for ALL
`m, t, a`.  This upgrades the session's exact verification for all `m ≤ 200`
(stick_rank.py) to a general theorem. -/
theorem stickCarry_telescope (m t : ℕ) :
    ∀ a : ℕ, (m : ℤ) * (∑ k ∈ Finset.range a, stickCarry m (k + 1) t)
      = ((a : ℤ) + 1) * ((t % m : ℕ) : ℤ) - (((a + 1) * t % m : ℕ) : ℤ)
  | 0 => by simp
  | a + 1 => by
    rw [Finset.sum_range_succ, mul_add, stickCarry_telescope m t a, stickCarry_mul_eq]
    push_cast
    ring

/-- The carry indicator IS the fractional-part expression
`v_k(t) = ⟨t/m⟩ + ⟨kt/m⟩ − ⟨(k+1)t/m⟩`, with genuine `Int.fract` over `ℚ` (`0 < m`). -/
theorem stickCarry_fract (m k t : ℕ) (hm : 0 < m) :
    (stickCarry m k t : ℚ)
      = Int.fract ((t : ℚ) / (m : ℚ)) + Int.fract (((k * t : ℕ) : ℚ) / (m : ℚ))
        - Int.fract ((((k + 1) * t : ℕ) : ℚ) / (m : ℚ)) := by
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [Int.fract_div_natCast_eq_div_natCast_mod, Int.fract_div_natCast_eq_div_natCast_mod,
    Int.fract_div_natCast_eq_div_natCast_mod]
  have hq : (m : ℚ) * (stickCarry m k t : ℚ)
      = ((t % m : ℕ) : ℚ) + ((k * t % m : ℕ) : ℚ) - (((k + 1) * t % m : ℕ) : ℚ) := by
    exact_mod_cast stickCarry_mul_eq m k t
  field_simp
  linear_combination hq

/-- The signed Stickelberger family `w_k = 2·v_k − 1` (twice the unitarized infinity-type
`v_k − ½·1`) as `ℚ`-vectors on the units of `ℤ/m` for `m` prime: index `k : Fin K` is the
Jacobi index `k+1`, coordinate `t : Fin (m-1)` is the unit `t+1`. -/
def signedStick (m K : ℕ) : Fin K → Fin (m - 1) → ℚ :=
  fun k t => ((2 * stickCarry m (k.1 + 1) (t.1 + 1) - 1 : ℤ) : ℚ)

/-- Rank Lemma instance `m = 3` (`K = 1`): `w_1 = (-1, 1)` is nonzero, hence independent. -/
theorem stickRank_m3 : LinearIndependent ℚ (signedStick 3 1) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun hg ⟨0, by norm_num⟩
  norm_num [signedStick, stickCarry, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_one] at h0
  have hg0 : g 0 = 0 := by linarith
  intro k
  fin_cases k
  · exact hg0

/-- Rank Lemma instance `m = 5` (`K = 2`): `w_1 = (-1,-1,1,1)`, `w_2 = (-1,1,-1,1)`;
the units-`{1,2}` minor has determinant `-2 ≠ 0`. -/
theorem stickRank_m5 : LinearIndependent ℚ (signedStick 5 2) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun hg ⟨0, by norm_num⟩
  have h1 := congrFun hg ⟨1, by norm_num⟩
  norm_num [signedStick, stickCarry, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_two] at h0 h1
  have hg0 : g 0 = 0 := by linarith
  have hg1 : g 1 = 0 := by linarith
  intro k
  fin_cases k
  · exact hg0
  · exact hg1

/-- Rank Lemma instance `m = 7` (`K = 3`): the units-`{1,2,3}` minor has det `4 ≠ 0`. -/
theorem stickRank_m7 : LinearIndependent ℚ (signedStick 7 3) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun hg ⟨0, by norm_num⟩
  have h1 := congrFun hg ⟨1, by norm_num⟩
  have h2 := congrFun hg ⟨2, by norm_num⟩
  norm_num [signedStick, stickCarry, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_three] at h0 h1 h2
  have hg0 : g 0 = 0 := by linarith
  have hg1 : g 1 = 0 := by linarith
  have hg2 : g 2 = 0 := by linarith
  intro k
  fin_cases k
  · exact hg0
  · exact hg1
  · exact hg2

/-- Rank Lemma instance `m = 11` (`K = 5`): the units-`{1,…,5}` minor has det `-16 ≠ 0`. -/
theorem stickRank_m11 : LinearIndependent ℚ (signedStick 11 5) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun hg ⟨0, by norm_num⟩
  have h1 := congrFun hg ⟨1, by norm_num⟩
  have h2 := congrFun hg ⟨2, by norm_num⟩
  have h3 := congrFun hg ⟨3, by norm_num⟩
  have h4 := congrFun hg ⟨4, by norm_num⟩
  norm_num [signedStick, stickCarry, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_five] at h0 h1 h2 h3 h4
  have hg0 : g 0 = 0 := by linarith
  have hg1 : g 1 = 0 := by linarith
  have hg2 : g 2 = 0 := by linarith
  have hg3 : g 3 = 0 := by linarith
  have hg4 : g 4 = 0 := by linarith
  intro k
  fin_cases k
  · exact hg0
  · exact hg1
  · exact hg2
  · exact hg3
  · exact hg4

/-- Rank Lemma instance `m = 13` (`K = 6`): the units-`{1,…,6}` minor has det `-32 ≠ 0`. -/
theorem stickRank_m13 : LinearIndependent ℚ (signedStick 13 6) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun hg ⟨0, by norm_num⟩
  have h1 := congrFun hg ⟨1, by norm_num⟩
  have h2 := congrFun hg ⟨2, by norm_num⟩
  have h3 := congrFun hg ⟨3, by norm_num⟩
  have h4 := congrFun hg ⟨4, by norm_num⟩
  have h5 := congrFun hg ⟨5, by norm_num⟩
  norm_num [signedStick, stickCarry, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_six] at h0 h1 h2 h3 h4 h5
  have hg0 : g 0 = 0 := by linarith
  have hg1 : g 1 = 0 := by linarith
  have hg2 : g 2 = 0 := by linarith
  have hg3 : g 3 = 0 := by linarith
  have hg4 : g 4 = 0 := by linarith
  have hg5 : g 5 = 0 := by linarith
  intro k
  fin_cases k
  · exact hg0
  · exact hg1
  · exact hg2
  · exact hg3
  · exact hg4
  · exact hg5

/-- `m = 8` Stickelberger kernel relation: on the units `{1, 3, 5, 7}` of `ℤ/8` (coordinate
`t ↦ 2t+1`), `v_3 = v_1` exactly.  This is the finite-order Hecke relation behind the
observed exact `β_3 − β_1 ∈ {0, π}` atom in the session numerics. -/
theorem stick_m8_relation :
    ∀ t : Fin 4, stickCarry 8 3 (2 * t.1 + 1) = stickCarry 8 1 (2 * t.1 + 1) := by
  decide

/-- `m = 8` degeneracy: the signed family `{w_1, w_2, w_3}` on the units of `ℤ/8` is NOT
`ℚ`-linearly independent (`w_3 = w_1`, so the family is not even injective).  Primality of
`m` in the Rank Lemma is necessary; joint equidistribution on the full torus fails for
composite `m`, exactly as the session's Stickelberger-kernel computations predicted. -/
theorem stickRank_m8_degenerate :
    ¬ LinearIndependent ℚ (fun (k : Fin 3) (t : Fin 4) =>
        ((2 * stickCarry 8 (k.1 + 1) (2 * t.1 + 1) - 1 : ℤ) : ℚ)) := by
  intro h
  have h02 : (fun (k : Fin 3) (t : Fin 4) =>
        ((2 * stickCarry 8 (k.1 + 1) (2 * t.1 + 1) - 1 : ℤ) : ℚ)) 0
      = (fun (k : Fin 3) (t : Fin 4) =>
        ((2 * stickCarry 8 (k.1 + 1) (2 * t.1 + 1) - 1 : ℤ) : ℚ)) 2 := by
    funext t
    fin_cases t <;> norm_num [stickCarry]
  exact absurd (h.injective h02) (by decide)

end ArkLib.ProximityGap.Frontier.R347StickelbergerRank

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/

#print axioms ArkLib.ProximityGap.Frontier.R347StickelbergerRank.stickCarry_eq_zero_or_one
#print axioms ArkLib.ProximityGap.Frontier.R347StickelbergerRank.stickCarry_mul_eq
#print axioms ArkLib.ProximityGap.Frontier.R347StickelbergerRank.stickCarry_telescope
#print axioms ArkLib.ProximityGap.Frontier.R347StickelbergerRank.stickCarry_fract
#print axioms ArkLib.ProximityGap.Frontier.R347StickelbergerRank.stickRank_m3
#print axioms ArkLib.ProximityGap.Frontier.R347StickelbergerRank.stickRank_m5
#print axioms ArkLib.ProximityGap.Frontier.R347StickelbergerRank.stickRank_m7
#print axioms ArkLib.ProximityGap.Frontier.R347StickelbergerRank.stickRank_m11
#print axioms ArkLib.ProximityGap.Frontier.R347StickelbergerRank.stickRank_m13
#print axioms ArkLib.ProximityGap.Frontier.R347StickelbergerRank.stick_m8_relation
#print axioms ArkLib.ProximityGap.Frontier.R347StickelbergerRank.stickRank_m8_degenerate
