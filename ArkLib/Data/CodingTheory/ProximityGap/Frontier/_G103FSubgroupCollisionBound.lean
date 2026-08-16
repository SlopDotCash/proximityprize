/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G102FAdditiveLiftAmplification
import ArkLib.Data.CodingTheory.ProximityGap.StepanovGeneratorIndep
import ArkLib.Data.CodingTheory.ProximityGap.StepanovVanisherExistence
import ArkLib.Data.CodingTheory.ProximityGap.HasseMultiplicityBridge
import ArkLib.Data.CodingTheory.ProximityGap.StepanovCountingLemma

/-!
# LANE G103F (#466, 2026-07-10): the classical additive-collision bound for multiplicative
  subgroups — the two-relation Stepanov theorem `#(H ∩ (H+c)) ≤ 4B²` at `2B ≤ t ≤ B³/2`,
  `tB ≤ p` (Heath-Brown–Konyagin / Mit'kin / Vyugin–Shkredov, `≈ 6.4·t^{2/3}`), welded
  unconditionally into G102F's Capstone A (axiom-clean).

## What this file proves

G102F (`_G102FAdditiveLiftAmplification.lean`) made its Capstone A — the first counting
bound on the G80Q terminal object valid across `√p` — PARAMETRIC in the additive-collision
bound `AddCollisionBound H ρ` (`ρ = max_{c≠0} #(H ∩ (H+c))`), and recorded honestly that no
in-tree sub-trivial `ρ` existed. This lane formalizes the classical collision bound and
discharges that named residual:

> **`card_collision_le_four_sq`** — for any `H ⊆ ZMod p` with `x^t = 1` on `H`, any `c ≠ 0`,
> and any parameter `B` with `2 ≤ B`, `2B ≤ t`, `2t ≤ B³`, `tB ≤ p`:
> `#{x ∈ H : x − c ∈ H} ≤ 4B²`.
>
> At the optimal `B ≈ (2t)^{1/3}` this is the classical `#(H ∩ (H+c)) ≲ 4·(2t)^{2/3}
> ≈ 6.35·t^{2/3}`, valid throughout `t ≲ (p/2^{1/3})^{3/4}` — the Heath-Brown–Konyagin
> range shape `|G| < (p−1)/((p−1)^{1/4}+1)` up to constants.

The proof is the genuine two-relation Stepanov method (Mit'kin 1992; García–Voloch 1988;
Heath-Brown–Konyagin, Q. J. Math 51 (2000); the parameterization follows Vyugin–Shkredov,
*On additive shifts of multiplicative subgroups*, arXiv:1102.1172, Lemma 3.1 + Lemma 4.1
specialized to one shift):

1. **Generators** `X^{a+tb}(X−c)^{tb'}` (`a < D`, `b, b' < B`): `D·B²` free coefficients.
2. **Conditions degeneracy** (`key_identity`): on a collision point (`x^t = 1`,
   `(x−c)^t = 1`) the order-`n` Hasse derivative collapses —
   `Xⁿ(X−c)ⁿ·Dⁿ[X^{a+tb}(X−c)^{tb'}] = X^{tb}(X−c)^{tb'}·P_{n,a,b,b'}(X)` with
   `deg P ≤ a + n < 2D` INDEPENDENT of `b, b'`. So order-`D` vanishing at EVERY collision
   point is implied by `D·(2D−1)` polynomial-identity conditions, not `D·#A` point
   conditions. This is exactly the "conditions-degeneracy count" that
   `StepanovGenericInsufficiency` proved the generic engine cannot supply.
3. **Non-vanishing**: the generator family is linearly independent at `DB ≤ t`, `tB ≤ p` —
   the in-tree Shkredov–Vyugin Lemma 3.1 (`stepanov_generators_linearIndependent`, proved
   via the sparse-multiplicity/disjoint-valuation route, no Wronskian converse).
4. **Count**: `D·#A ≤ deg Ψ ≤ (D−1) + 2t(B−1)`; at `D = ⌊t/B⌋`, `2D ≤ B²` this gives
   `#A ≤ 4B²`.

## Why this evades the recorded Stepanov no-gos (C36, I008, `StepanovStructuredVacuous`)

The DISPROOF_LOG Stepanov wall (`stepanov_collapses_to_degree`, C36 "HBK REFUTED-FALSE",
I008 dyadic-tower NO-GAIN) says: `X^n − 1` is separable, so an auxiliary built from the
SINGLE relation `x ∈ μ_n` manufactures NO multiplicity — Stepanov on `μ_n` itself collapses
to the trivial degree bound, and the C36 entry correctly refutes using the HBK
*character-sum* exponents (`n^{5/8}p^{1/8}`) as a SUP-norm bound in the prize band. The
collision bound proved here is a DIFFERENT theorem evading that horn exactly as the log's
own mechanism analysis predicts: the point set is `A = {x : x^t = 1 AND (x−c)^t = 1}` — TWO
independent algebraic relations — and the auxiliary vanishes to order `D ~ t/B` at `A` not
because `X^t − 1` has multiple roots (it does not; separability is untouched) but because
the TWO relations together collapse the `D·#A` Hasse conditions to rank `< 2D²`. Nothing
here contradicts C36: this is a bound on a shifted-intersection COUNT (`≈ t^{2/3}`, useless
as a sup-norm route), not a `√`-cancellation estimate; the BGK wall is untouched.

## The weld into G102F, and honest scope

* `addCollisionBound_of_closure` — the G102F interface `AddCollisionBound H (4B²)`, with
  the subgroup-power input derived from G102F's own closure hypotheses via a Lagrange
  product trick (`pow_card_eq_one_of_mul_closed`).
* **`smallDiffPairs_sq_le_unconditional_stepanov`** — CAPSTONE: G102F's Capstone A with the
  collision input DISCHARGED: for every window `4W < p`,
  `sdp(W)² ≤ n·sdp(W) + 16B²·W·n²` — now an UNCONDITIONAL theorem (closure hypotheses
  only), the first in-tree `√p`-crossing counting bound on the terminal object with no
  collision hypothesis.
* The bound `4B² ≈ 4·(2t)^{2/3}` beats the trivial `ρ = t` from `t = 512` on (`484 < 512`;
  at `t = 4096`: `1764`, see `addCollisionBound_4096`). Probe truth (below) is FAR smaller
  (`ρ ≤ 10`), so the G102F window `ρ < W < n²/(4ρ)` in which the welded Capstone A beats
  the trivial caps is real but much narrower than the truth would give; with the classical
  `ρ ~ t^{2/3}` the amplification window crosses `√p` only for `p ≲ n^{8/3}` — the welded
  capstone is a genuine unconditional `√p`-crossing tool at `β ≤ 8/3`, NOT a prize-band
  certificate. CORE stays OPEN / ON-BGK.

## Probe (scratchpad `probe_g103f_collision_growth.py`, 2026-07-10, exact, exit 0)

`ρ_true = max_{c≠0} #(H∩(H+c))` for `n = 16..1024`, `β ∈ {2,3,4}` (first prime
`p ≡ 1 mod n` above `n^β`): `ρ_true ∈ {2,...,10}`; at `β ≥ 3` it is exactly `2` at every
measured `n ≥ 16` (near-perfect difference-Sidon); at `β = 2` it grows like `n^{0.28}`
(`4, 4, 4, 6, 9, 8, 10`). Truth-vs-classical gap: `ρ_true/n^{2/3}` falls from `0.63` to
`0.02` — the classical `t^{2/3}` is far from optimal on smooth subgroups (consistent with
the conjectured `n^{o(1)}`; Vyugin–Shkredov multi-shift gives `n^{1/2+o(1)}` for a bounded
number of shifts, still far above truth). The formalized `4B²` bound goes sub-trivial from
`n = 512`.

Issue #466. Axiom-clean: no `sorry`, no new axioms, no named hypotheses.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false


open Polynomial Finset

namespace ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound

open ArkLib.ProximityGap.Wronskian
open ArkLib.CodingTheory.StepanovVanisher
open ArkLib.CodingTheory.HasseMultiplicityBridge
open ArkLib.ProximityGap.Stepanov
open ArkLib.ProximityGap.Frontier.G80SDirectionalStripReduction
open ArkLib.ProximityGap.Frontier.G102FAdditiveLiftAmplification

/-! ## Part 0 — Hasse-derivative bricks: `Dᵏ(Xᵘ)` and `Dᵏ((X−c)ᵛ)` in closed form -/

section HasseBricks

variable {R : Type*} [CommRing R]

/-- Hasse derivative of a pure power: `Dᵏ(Xᵘ) = C(u,k)·X^{u−k}` (char-free). -/
theorem hasseDeriv_X_pow (u k : ℕ) :
    hasseDeriv k (X ^ u : R[X]) = C (u.choose k : R) * X ^ (u - k) := by
  rw [X_pow_eq_monomial, hasseDeriv_monomial, mul_one, C_mul_X_pow_eq_monomial]

/-- Hasse derivative of a shifted power: `Dᵏ((X−c)ᵛ) = C(v,k)·(X−c)^{v−k}` (char-free).
Proved by induction on `v` via the Hasse–Leibniz rule and Pascal's identity; this is the
second-relation brick the two-relation Stepanov auxiliary consumes. -/
theorem hasseDeriv_X_sub_C_pow (c : R) (v : ℕ) :
    ∀ k : ℕ, hasseDeriv k ((X - C c) ^ v : R[X])
      = C (v.choose k : R) * (X - C c) ^ (v - k) := by
  induction v with
  | zero =>
    intro k
    cases k with
    | zero => simp
    | succ k =>
      rw [pow_zero, ← C_1, hasseDeriv_C _ _ (Nat.succ_pos k),
        Nat.choose_eq_zero_of_lt (Nat.succ_pos k), Nat.cast_zero, C_0, zero_mul]
  | succ v ih =>
    intro k
    have hD1 : hasseDeriv 1 (X - C c : R[X]) = 1 := by
      rw [hasseDeriv_one', derivative_sub, derivative_X, derivative_C, sub_zero]
    have hDge2 : ∀ j : ℕ, 1 < j → hasseDeriv j (X - C c : R[X]) = 0 := by
      intro j hj
      rw [map_sub, hasseDeriv_X _ hj, hasseDeriv_C _ _ (by omega : 0 < j), sub_zero]
    rw [pow_succ, hasseDeriv_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    cases k with
    | zero => simp [pow_succ]
    | succ k =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hzero : (∑ j ∈ Finset.range k,
          hasseDeriv j ((X - C c) ^ v : R[X]) * hasseDeriv (k + 1 - j) (X - C c)) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [hDge2 (k + 1 - j) (by omega), mul_zero]
      rw [hzero, zero_add, show k + 1 - k = 1 from by omega, hD1, mul_one,
        Nat.sub_self, hasseDeriv_zero', ih k, ih (k + 1)]
      rcases Nat.lt_or_ge v (k + 1) with hkv | hkv
      · -- the `(k+1)`-binomial is dead: `v < k+1`
        rw [Nat.choose_eq_zero_of_lt hkv, Nat.cast_zero, C_0, zero_mul, zero_mul,
          add_zero]
        rcases Nat.lt_or_ge v k with hvk | hvk
        · rw [Nat.choose_eq_zero_of_lt hvk,
            Nat.choose_eq_zero_of_lt (by omega : v + 1 < k + 1)]
          simp
        · have hveq : v = k := by omega
          subst hveq
          rw [Nat.choose_self, Nat.choose_self, Nat.sub_self,
            show v + 1 - (v + 1) = 0 from by omega]
      · -- genuine Pascal case: `k + 1 ≤ v`
        have hexp : v - (k + 1) + 1 = v - k := by omega
        rw [show v + 1 - (k + 1) = v - k from by omega, Nat.choose_succ_succ' v k,
          Nat.cast_add, C_add, add_mul, mul_assoc, ← pow_succ, hexp]

end HasseBricks

/-! ## Part 1 — the two-relation Stepanov data: generators and condition polynomials -/

variable {p : ℕ} [Fact p.Prime] [NeZero p]

/-- The two-relation Stepanov generator family: `X^{a+tb}·(X−c)^{tb'}` for
`(a, b, b') ∈ Fin D × Fin B × Fin B`. `D·B²` free coefficients of degree
`≤ (D−1) + 2t(B−1)`. -/
noncomputable def gen {D B : ℕ} (t : ℕ) (c : ZMod p) (i : Fin D × Fin B × Fin B) :
    (ZMod p)[X] :=
  X ^ ((i.1 : ℕ) + t * (i.2.1 : ℕ)) * (X - C c) ^ (t * (i.2.2 : ℕ))

/-- The condition polynomial `P_{n,a,b,b'}` of the degeneracy identity: on a collision
point the order-`n` Hasse derivative of the generator equals
`X^{tb}(X−c)^{tb'}·P_{n,a,b,b'}` after clearing `Xⁿ(X−c)ⁿ`; crucially `deg P ≤ a + n < 2D`,
INDEPENDENT of `b, b'` — this is the conditions-degeneracy that beats the generic
dimension count. -/
noncomputable def condPoly {D B : ℕ} (t : ℕ) (c : ZMod p) (n : ℕ)
    (i : Fin D × Fin B × Fin B) : (ZMod p)[X] :=
  ∑ kl ∈ Finset.antidiagonal n,
    C ((((i.1 : ℕ) + t * (i.2.1 : ℕ)).choose kl.1 : ZMod p)
        * ((t * (i.2.2 : ℕ)).choose kl.2 : ZMod p))
      * (X ^ ((i.1 : ℕ) + kl.2) * (X - C c) ^ kl.1)

/-- **The conditions-degeneracy identity** (the heart of the two-relation method):
`Xⁿ·(X−c)ⁿ·Dⁿ(gen) = X^{tb}·(X−c)^{tb'}·condPoly` as a POLYNOMIAL identity. Since
`x^{tb} = (x^t)^b = 1` and `(x−c)^{tb'} = 1` at a collision point, the `n`-th Hasse
derivative of any coefficient combination vanishes at every collision point as soon as the
degree-`< 2D` polynomial `∑ λ·condPoly` is identically zero — `2D−1` conditions per
derivative order instead of one condition per point. -/
theorem key_identity {D B : ℕ} (t : ℕ) (c : ZMod p) (i : Fin D × Fin B × Fin B) (n : ℕ) :
    X ^ n * (X - C c) ^ n * hasseDeriv n (gen t c i)
      = X ^ (t * (i.2.1 : ℕ)) * (X - C c) ^ (t * (i.2.2 : ℕ)) * condPoly t c n i := by
  obtain ⟨a, b, b'⟩ := i
  simp only [gen, condPoly]
  rw [hasseDeriv_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  obtain ⟨k, l⟩ := kl
  rw [Finset.mem_antidiagonal] at hkl
  simp only
  rw [hasseDeriv_X_pow, hasseDeriv_X_sub_C_pow]
  set u := (a : ℕ) + t * (b : ℕ) with hu
  set v := t * (b' : ℕ) with hv
  rcases Nat.lt_or_ge u k with hk | hk
  · rw [Nat.choose_eq_zero_of_lt hk]
    simp
  · rcases Nat.lt_or_ge v l with hl | hl
    · rw [Nat.choose_eq_zero_of_lt hl]
      simp
    · have h1 : n + (u - k) = t * (b : ℕ) + ((a : ℕ) + l) := by omega
      have h2 : n + (v - l) = v + k := by omega
      have hL : X ^ n * (X - C c) ^ n
            * (C (u.choose k : ZMod p) * X ^ (u - k)
              * (C (v.choose l : ZMod p) * (X - C c) ^ (v - l)))
          = C (u.choose k : ZMod p) * C (v.choose l : ZMod p)
            * (X ^ (n + (u - k)) * (X - C c) ^ (n + (v - l))) := by
        rw [pow_add, pow_add]; ring
      have hR : X ^ (t * (b : ℕ)) * (X - C c) ^ v
            * (C ((u.choose k : ZMod p) * (v.choose l : ZMod p))
              * (X ^ ((a : ℕ) + l) * (X - C c) ^ k))
          = C (u.choose k : ZMod p) * C (v.choose l : ZMod p)
            * (X ^ (t * (b : ℕ) + ((a : ℕ) + l)) * (X - C c) ^ (v + k)) := by
        rw [C_mul, pow_add, pow_add]; ring
      rw [hL, hR, h1, h2]

/-- Degree control for the condition polynomials: `deg P_{n,a,b,b'} ≤ a + n` —
independent of `b, b'`. -/
theorem condPoly_natDegree_le {D B : ℕ} (t : ℕ) (c : ZMod p) (n : ℕ)
    (i : Fin D × Fin B × Fin B) :
    (condPoly t c n i).natDegree ≤ (i.1 : ℕ) + n := by
  refine natDegree_sum_le_of_forall_le _ _ fun kl hkl => ?_
  rw [Finset.mem_antidiagonal] at hkl
  calc (C ((((i.1 : ℕ) + t * (i.2.1 : ℕ)).choose kl.1 : ZMod p)
          * ((t * (i.2.2 : ℕ)).choose kl.2 : ZMod p))
        * (X ^ ((i.1 : ℕ) + kl.2) * (X - C c) ^ kl.1)).natDegree
      ≤ (C ((((i.1 : ℕ) + t * (i.2.1 : ℕ)).choose kl.1 : ZMod p)
          * ((t * (i.2.2 : ℕ)).choose kl.2 : ZMod p))).natDegree
        + (X ^ ((i.1 : ℕ) + kl.2) * (X - C c) ^ kl.1).natDegree := natDegree_mul_le
    _ ≤ 0 + ((X ^ ((i.1 : ℕ) + kl.2) : (ZMod p)[X]).natDegree
        + ((X - C c) ^ kl.1 : (ZMod p)[X]).natDegree) :=
        Nat.add_le_add (Nat.le_of_eq (natDegree_C _)) natDegree_mul_le
    _ ≤ (i.1 : ℕ) + n := by
        rw [natDegree_X_pow, natDegree_pow, natDegree_X_sub_C, mul_one]
        omega

/-- Degree control for the generators: `deg(gen) ≤ (D−1) + t(B−1) + t(B−1)`. -/
theorem gen_natDegree_le {D B : ℕ} (_hD : 1 ≤ D) (hB : 1 ≤ B) (t : ℕ) (c : ZMod p)
    (i : Fin D × Fin B × Fin B) :
    (gen t c i).natDegree ≤ D - 1 + t * (B - 1) + t * (B - 1) := by
  have h1 : (i.1 : ℕ) ≤ D - 1 := by have := i.1.isLt; omega
  have h2 : t * (i.2.1 : ℕ) ≤ t * (B - 1) :=
    Nat.mul_le_mul_left t (by have := i.2.1.isLt; omega)
  have h3 : t * (i.2.2 : ℕ) ≤ t * (B - 1) :=
    Nat.mul_le_mul_left t (by have := i.2.2.isLt; omega)
  calc (gen t c i).natDegree
      ≤ (X ^ ((i.1 : ℕ) + t * (i.2.1 : ℕ)) : (ZMod p)[X]).natDegree
        + ((X - C c) ^ (t * (i.2.2 : ℕ)) : (ZMod p)[X]).natDegree := natDegree_mul_le
    _ = (i.1 : ℕ) + t * (i.2.1 : ℕ) + t * (i.2.2 : ℕ) := by
        rw [natDegree_X_pow, natDegree_pow, natDegree_X_sub_C, mul_one]
    _ ≤ D - 1 + t * (B - 1) + t * (B - 1) := by omega

/-! ## Part 2 — non-vanishing: the generator family is linearly independent
(Shkredov–Vyugin Lemma 3.1, via the in-tree sparse-multiplicity route) -/

/-- **Linear independence of the two-relation generators** at `DB ≤ t`, `tB ≤ p`:
the `x`-exponents `a + tb` (`a < D ≤ t`, `b < B`) are distinct naturals `< tB ≤ p`, hence
distinct in `ZMod p`; the in-tree Shkredov–Vyugin Lemma 3.1
(`stepanov_generators_linearIndependent`) then gives independence of the full family.
This is the non-vanishing input — the step the single-relation no-gos never needed and the
generic engine cannot see. -/
theorem gen_linearIndependent {D B : ℕ} (t : ℕ) (_hD : 1 ≤ D) (hB : 1 ≤ B)
    (hDB : D * B ≤ t) (hp : t * B ≤ p) {c : ZMod p} (hc : c ≠ 0) :
    LinearIndependent (ZMod p) (gen (p := p) (D := D) (B := B) t c) := by
  classical
  have hDt : D ≤ t := le_trans (Nat.le_mul_of_pos_right D hB) hDB
  -- the exponent enumeration `Fin (D*B) → ℕ`, `k ↦ a + t·b`
  set efun : Fin (D * B) → ℕ := fun k =>
    ((finProdFinEquiv.symm k).1 : ℕ) + t * ((finProdFinEquiv.symm k).2 : ℕ) with hefun
  -- exponent values are `< t*B ≤ p`
  have hlt : ∀ k, efun k < t * B := by
    intro k
    have h0 : ((finProdFinEquiv.symm k).1 : ℕ) < t :=
      lt_of_lt_of_le (finProdFinEquiv.symm k).1.isLt hDt
    have h3 : t * ((finProdFinEquiv.symm k).2 : ℕ) ≤ t * (B - 1) :=
      Nat.mul_le_mul_left t (by have := (finProdFinEquiv.symm k).2.isLt; omega)
    have h4 : t * (B - 1) + t = t * B := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    simp only [hefun]
    omega
  -- nat-level injectivity of `(a, b) ↦ a + t·b` given `a < D ≤ t`
  have hinjNat : Function.Injective efun := by
    intro k k' hkk'
    simp only [hefun] at hkk'
    set a := ((finProdFinEquiv.symm k).1 : ℕ) with ha_def
    set b := ((finProdFinEquiv.symm k).2 : ℕ) with hb_def
    set a' := ((finProdFinEquiv.symm k').1 : ℕ) with ha'_def
    set b' := ((finProdFinEquiv.symm k').2 : ℕ) with hb'_def
    have ha : a < t := lt_of_lt_of_le (finProdFinEquiv.symm k).1.isLt hDt
    have ha' : a' < t := lt_of_lt_of_le (finProdFinEquiv.symm k').1.isLt hDt
    have ht0 : 0 < t := by omega
    have hb : b = b' := by
      have h1 : (a + t * b) / t = b := by
        rw [Nat.add_mul_div_left a b ht0, Nat.div_eq_of_lt ha, zero_add]
      have h2 : (a' + t * b') / t = b' := by
        rw [Nat.add_mul_div_left a' b' ht0, Nat.div_eq_of_lt ha', zero_add]
      rw [← h1, ← h2, hkk']
    have haa : a = a' := by
      rw [hb] at hkk'
      omega
    have hpair : finProdFinEquiv.symm k = finProdFinEquiv.symm k' := by
      apply Prod.ext
      · exact Fin.ext haa
      · exact Fin.ext hb
    exact finProdFinEquiv.symm.injective hpair
  -- distinctness survives the cast to `ZMod p`
  have hvand : (Matrix.vandermonde (fun k => (efun k : ZMod p))).det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    intro k k' hkk'
    apply hinjNat
    have hk : efun k < p := lt_of_lt_of_le (hlt k) hp
    have hk' : efun k' < p := lt_of_lt_of_le (hlt k') hp
    have := congrArg ZMod.val hkk'
    rwa [ZMod.val_natCast_of_lt hk, ZMod.val_natCast_of_lt hk'] at this
  -- the in-tree Shkredov–Vyugin Lemma 3.1
  have hli0 := stepanov_generators_linearIndependent (R := ZMod p) efun c t B hc hvand hDB
  -- reindex `(a, b, b') ↦ (b', (a, b))`
  set ε : Fin D × Fin B × Fin B → Fin B × Fin (D * B) :=
    fun i => (i.2.2, finProdFinEquiv (i.1, i.2.1)) with hε
  have hεinj : Function.Injective ε := by
    intro i j hij
    obtain ⟨ia, ib, ib'⟩ := i
    obtain ⟨ja, jb, jb'⟩ := j
    simp only [hε, Prod.mk.injEq] at hij
    obtain ⟨h1, h2⟩ := hij
    have h3 := finProdFinEquiv.injective h2
    simp only [Prod.mk.injEq] at h3
    simp only [Prod.mk.injEq]
    exact ⟨h3.1, h3.2, h1⟩
  have hEq : gen (p := p) (D := D) (B := B) t c
      = (fun q : Fin B × Fin (D * B) =>
          (X - C c) ^ (t * (q.1 : ℕ)) * X ^ (efun q.2)) ∘ ε := by
    funext i
    obtain ⟨a, b, b'⟩ := i
    simp only [gen, hε, hefun, Function.comp_apply, Equiv.symm_apply_apply]
    ring
  rw [hEq]
  exact hli0.comp ε hεinj

/-! ## Part 3 — the auxiliary polynomial: existence, degree, and order-`D` vanishing -/

/-- **The two-relation Stepanov auxiliary exists.** For parameters `D, B` with `DB ≤ t`,
`2D ≤ B²` (conditions-vs-unknowns), `tB ≤ p` (non-vanishing range) and `c ≠ 0`, there is a
NONZERO `Ψ` of degree `≤ (D−1) + 2t(B−1)` vanishing to order `≥ D` at EVERY point `x` with
`x^t = 1` and `(x−c)^t = 1`. The linear system has `D·(2D−1)` polynomial-identity
conditions against `D·B²` unknowns — the degeneracy count, not the point count. -/
theorem exists_collision_vanisher {t B D : ℕ} (hD : 1 ≤ D) (hB : 1 ≤ B)
    (hDB : D * B ≤ t) (hcond : 2 * D ≤ B ^ 2) (hp : t * B ≤ p)
    {c : ZMod p} (hc : c ≠ 0) :
    ∃ Ψ : (ZMod p)[X], Ψ ≠ 0
      ∧ Ψ.natDegree ≤ D - 1 + t * (B - 1) + t * (B - 1)
      ∧ ∀ x : ZMod p, x ^ t = 1 → (x - c) ^ t = 1 → D ≤ Ψ.rootMultiplicity x := by
  classical
  have hli := gen_linearIndependent (p := p) (D := D) (B := B) t hD hB hDB hp hc
  -- the conditions map: coefficient `m < 2D−1` of the `n`-th condition polynomial, `n < D`
  set Φ : ((Fin D × Fin B × Fin B) → ZMod p)
      →ₗ[ZMod p] ((Fin D × Fin (2 * D - 1)) → ZMod p) :=
    LinearMap.pi fun nm =>
      (lcoeff (ZMod p) (nm.2 : ℕ)).comp
        (Fintype.linearCombination (ZMod p)
          (fun i => condPoly (p := p) (D := D) (B := B) t c (nm.1 : ℕ) i)) with hΦ
  have hcard : Fintype.card (Fin D × Fin (2 * D - 1))
      < Fintype.card (Fin D × Fin B × Fin B) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    have h1 : 2 * D - 1 < B ^ 2 := by omega
    calc D * (2 * D - 1) < D * B ^ 2 := mul_lt_mul_of_pos_left h1 (by omega : 0 < D)
      _ = D * (B * B) := by ring
  obtain ⟨lam, hne, hΦc⟩ := exists_nonzero_vanishing_combination
    (gen (p := p) (D := D) (B := B) t c) hli Φ hcard
  set Ψ : (ZMod p)[X] := ∑ i, lam i • gen (p := p) (D := D) (B := B) t c i with hΨ
  -- each condition-polynomial combination vanishes identically
  have hQzero : ∀ n : ℕ, n < D →
      (∑ i, lam i • condPoly (p := p) (D := D) (B := B) t c n i) = 0 := by
    intro n hn
    set Q : (ZMod p)[X] :=
      ∑ i, lam i • condPoly (p := p) (D := D) (B := B) t c n i with hQ
    have hQdeg : Q.natDegree ≤ D - 1 + (D - 1) := by
      rw [hQ]
      refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
      refine le_trans (natDegree_smul_le _ _) ?_
      refine le_trans (condPoly_natDegree_le t c n i) ?_
      have := i.1.isLt
      omega
    ext m
    rw [coeff_zero]
    rcases Nat.lt_or_ge m (2 * D - 1) with hm | hm
    · have hcomp := congrFun hΦc (⟨n, hn⟩, ⟨m, hm⟩)
      simp only [hΦ, LinearMap.pi_apply, LinearMap.comp_apply,
        Fintype.linearCombination_apply, lcoeff_apply, Pi.zero_apply] at hcomp
      rw [hQ]
      simpa using hcomp
    · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQdeg (by omega))
  refine ⟨Ψ, hne, ?_, ?_⟩
  · rw [hΨ]
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    exact le_trans (natDegree_smul_le _ _) (gen_natDegree_le hD hB t c i)
  · intro x hx hxc
    have ht1 : 1 ≤ t := by
      calc 1 = 1 * 1 := by ring
        _ ≤ D * B := Nat.mul_le_mul hD hB
        _ ≤ t := hDB
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, zero_pow (by omega : t ≠ 0)] at hx
      exact zero_ne_one hx
    have hxc0 : x - c ≠ 0 := by
      intro h
      rw [h, zero_pow (by omega : t ≠ 0)] at hxc
      exact zero_ne_one hxc
    refine rootMultiplicity_ge_of_hasseDeriv_vanish hne x D fun n hn => ?_
    -- the summed degeneracy identity
    have hpoly : X ^ n * (X - C c) ^ n * hasseDeriv n Ψ
        = ∑ i, C (lam i) * (X ^ (t * (i.2.1 : ℕ)) * (X - C c) ^ (t * (i.2.2 : ℕ))
            * condPoly (p := p) (D := D) (B := B) t c n i) := by
      rw [hΨ, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_C_mul]
      calc X ^ n * (X - C c) ^ n
            * (C (lam i) * hasseDeriv n (gen (p := p) (D := D) (B := B) t c i))
          = C (lam i) * (X ^ n * (X - C c) ^ n
              * hasseDeriv n (gen (p := p) (D := D) (B := B) t c i)) := by ring
        _ = C (lam i) * (X ^ (t * (i.2.1 : ℕ)) * (X - C c) ^ (t * (i.2.2 : ℕ))
              * condPoly (p := p) (D := D) (B := B) t c n i) := by
            rw [key_identity]
    have hev := congrArg (Polynomial.eval x) hpoly
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_finset_sum] at hev
    have hRHS : ∀ i : Fin D × Fin B × Fin B,
        (lam i) * (x ^ (t * (i.2.1 : ℕ)) * (x - c) ^ (t * (i.2.2 : ℕ))
            * (condPoly (p := p) (D := D) (B := B) t c n i).eval x)
        = (lam i) * (condPoly (p := p) (D := D) (B := B) t c n i).eval x := by
      intro i
      rw [pow_mul, pow_mul, hx, hxc, one_pow, one_pow, one_mul, one_mul]
    rw [Finset.sum_congr rfl fun i _ => hRHS i] at hev
    have hsum : (∑ i, (lam i)
        * (condPoly (p := p) (D := D) (B := B) t c n i).eval x) = 0 := by
      calc ∑ i, (lam i) * (condPoly (p := p) (D := D) (B := B) t c n i).eval x
          = (∑ i, lam i • condPoly (p := p) (D := D) (B := B) t c n i).eval x := by
            rw [eval_finset_sum]
            exact Finset.sum_congr rfl fun i _ => by
              rw [smul_eq_C_mul, eval_mul, eval_C]
        _ = (0 : (ZMod p)[X]).eval x := by rw [hQzero n hn]
        _ = 0 := eval_zero
    rw [hsum] at hev
    -- cancel the nonzero prefactor `xⁿ(x−c)ⁿ`
    rcases mul_eq_zero.mp hev with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (pow_ne_zero n hx0)
      · exact absurd h' (pow_ne_zero n hxc0)
    · exact h

/-! ## Part 4 — the master counting theorem and the clean `4B²` corollary -/

/-- **The two-relation Stepanov master bound.** For any `H` on which `x^t = 1`, any
`c ≠ 0`, and any parameters `1 ≤ D`, `1 ≤ B` with `DB ≤ t` (non-vanishing), `2D ≤ B²`
(solvability), `tB ≤ p` (range):

`D · #{x ∈ H : x − c ∈ H} ≤ (D−1) + 2t(B−1)`.

Order-`D` vanishing at every collision point against degree `≈ 2tB`. -/
theorem stepanov_collision_bound (H : Finset (ZMod p)) {t B D : ℕ}
    (hD : 1 ≤ D) (hB : 1 ≤ B) (hDB : D * B ≤ t) (hcond : 2 * D ≤ B ^ 2)
    (hp : t * B ≤ p) (hpow : ∀ x ∈ H, x ^ t = 1) {c : ZMod p} (hc : c ≠ 0) :
    D * (H.filter (fun x => x - c ∈ H)).card ≤ D - 1 + t * (B - 1) + t * (B - 1) := by
  classical
  obtain ⟨Ψ, hne, hdeg, hmult⟩ :=
    exists_collision_vanisher (p := p) (t := t) (B := B) (D := D) hD hB hDB hcond hp hc
  refine le_trans (card_le_natDegree_of_vanishing hne fun s hs => ?_) hdeg
  rw [Finset.mem_filter] at hs
  obtain ⟨hsH, hscH⟩ := hs
  have h1 : s ^ t = 1 := hpow s hsH
  have h2 : (s - c) ^ t = 1 := hpow (s - c) hscH
  exact (Polynomial.le_rootMultiplicity_iff hne).mp (hmult s h1 h2)

/-- **THE CLASSICAL ADDITIVE-COLLISION BOUND** (Heath-Brown–Konyagin / Mit'kin /
García–Voloch shape, Vyugin–Shkredov parameterization): for any `H ⊆ ZMod p` with
`x^t = 1` on `H`, any `c ≠ 0`, and ANY `B` with `2 ≤ B`, `2B ≤ t`, `2t ≤ B³`, `tB ≤ p`:

`#(H ∩ (H + c)) = #{x ∈ H : x − c ∈ H} ≤ 4B²`.

At the optimal `B = ⌈(2t)^{1/3}⌉` this is `≤ 4·((2t)^{1/3}+1)² ≈ 6.35·t^{2/3}` — the
classical `O(t^{2/3})`, valid throughout `tB ≤ p` (i.e. up to `t ≈ p^{3/4}/2^{1/4}`,
the Heath-Brown–Konyagin range). Instantiated with `D = ⌊t/B⌋`. -/
theorem card_collision_le_four_sq (H : Finset (ZMod p)) {t B : ℕ}
    (hB : 2 ≤ B) (h2B : 2 * B ≤ t) (hB3 : 2 * t ≤ B ^ 3) (hp : t * B ≤ p)
    (hpow : ∀ x ∈ H, x ^ t = 1) {c : ZMod p} (hc : c ≠ 0) :
    (H.filter (fun x => x - c ∈ H)).card ≤ 4 * B ^ 2 := by
  set D : ℕ := t / B with hD
  have hB0 : 0 < B := by omega
  have hD1 : 1 ≤ D := by
    rw [hD, Nat.le_div_iff_mul_le hB0]
    omega
  have hDB : D * B ≤ t := by rw [hD]; exact Nat.div_mul_le_self t B
  have hcond : 2 * D ≤ B ^ 2 := by
    have h3 : 2 * D * B ≤ B ^ 2 * B := by
      calc 2 * D * B = 2 * (D * B) := by ring
        _ ≤ 2 * t := Nat.mul_le_mul_left 2 hDB
        _ ≤ B ^ 3 := hB3
        _ = B ^ 2 * B := by ring
    exact Nat.le_of_mul_le_mul_right h3 hB0
  have hmaster := stepanov_collision_bound (p := p) H hD1 (by omega : 1 ≤ B) hDB hcond
    hp hpow hc
  -- `t ≤ 2·B·D` from `B·D = B·⌊t/B⌋ > t − B` and `2B ≤ t`
  have hml : t % B < B := Nat.mod_lt t hB0
  have hBD : B * D + t % B = t := by rw [hD]; exact Nat.div_add_mod t B
  have ht2BD : t ≤ 2 * (B * D) := by omega
  -- assemble: `D·card ≤ D − 1 + 2t(B−1) ≤ D − 1 + 4B²·D < D·(4B² + 1)`
  have h1 : t * (B - 1) ≤ t * B := Nat.mul_le_mul_left t (by omega)
  have h2 : 2 * (t * B) ≤ 4 * B ^ 2 * D := by
    calc 2 * (t * B) ≤ 2 * (2 * (B * D) * B) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right B ht2BD)
      _ = 4 * B ^ 2 * D := by ring
  have hchain : D * (H.filter (fun x => x - c ∈ H)).card < D * (4 * B ^ 2 + 1) := by
    calc D * (H.filter (fun x => x - c ∈ H)).card
        ≤ D - 1 + t * (B - 1) + t * (B - 1) := hmaster
      _ ≤ D - 1 + 2 * (t * B) := by omega
      _ ≤ D - 1 + 4 * B ^ 2 * D := by omega
      _ < D + 4 * B ^ 2 * D := by omega
      _ = D * (4 * B ^ 2 + 1) := by ring
  have hfin := Nat.lt_of_mul_lt_mul_left hchain
  omega

/-! ## Part 5 — the Lagrange bridge: G102F's closure hypotheses supply `x^t = 1` -/

/-- **Lagrange product trick** for a multiplicatively closed finite set: if `0 ∉ H` and `H`
is closed under multiplication, every `x ∈ H` satisfies `x^{|H|} = 1` (multiplication by
`x` permutes `H`; compare products). This turns G102F's closure hypotheses into the power
relation the Stepanov bound consumes. -/
theorem pow_card_eq_one_of_mul_closed (H : Finset (ZMod p)) (h0 : (0 : ZMod p) ∉ H)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) : ∀ x ∈ H, x ^ H.card = 1 := by
  classical
  intro x hx
  have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
  have hinj : Function.Injective (fun y : ZMod p => x * y) := mul_right_injective₀ hx0
  have himg : H.image (fun y => x * y) = H := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact hmul x hx y hy
    · rw [Finset.card_image_of_injective _ hinj]
  have hprod : (∏ y ∈ H, y) = ∏ y ∈ H, (x * y) := by
    have h : ∏ z ∈ H.image (fun y => x * y), z = ∏ y ∈ H, x * y :=
      Finset.prod_image (fun y _ y' _ h => hinj h)
    rw [himg] at h
    exact h
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hprod
  have hne : (∏ y ∈ H, y) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun y hy => fun h => h0 (h ▸ hy)
  have hprod' : (1 : ZMod p) * (∏ y ∈ H, y) = x ^ H.card * (∏ y ∈ H, y) := by
    rw [one_mul]; exact hprod
  exact (mul_right_cancel₀ hne hprod').symm

/-- **The G102F interface, discharged**: a multiplicatively closed `H ∌ 0` (any subgroup of
`(ZMod p)ˣ` as a Finset) satisfies `AddCollisionBound H (4B²)` for every admissible `B`.
This is the first in-tree sub-trivial additive-collision bound — the named residual of
G102F's Capstone A. Sub-trivial (`4B² < |H|`) from `|H| = 512` on. -/
theorem addCollisionBound_of_closure (H : Finset (ZMod p)) {B : ℕ}
    (h0 : (0 : ZMod p) ∉ H) (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    (hB : 2 ≤ B) (h2B : 2 * B ≤ H.card) (hB3 : 2 * H.card ≤ B ^ 3)
    (hp : H.card * B ≤ p) :
    AddCollisionBound H (4 * B ^ 2) := by
  intro c hc
  exact card_collision_le_four_sq H hB h2B hB3 hp
    (pow_card_eq_one_of_mul_closed H h0 hmul) hc

/-- Concrete instantiation at the deployed scale `|H| = 4096 = 2^{12}` (any `p ≥ 86016`
with a multiplicatively closed `H` of that order, e.g. `μ_{4096}` at the NTT primes):
`ρ ≤ 1764 < 4096` — strictly sub-trivial, zero hypotheses beyond closure.
(`B = 21`: `2·4096 = 8192 ≤ 9261 = 21³`.) -/
theorem addCollisionBound_4096 (H : Finset (ZMod p))
    (h0 : (0 : ZMod p) ∉ H) (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    (hcard : H.card = 4096) (hp : 86016 ≤ p) :
    AddCollisionBound H 1764 := by
  have h := addCollisionBound_of_closure (p := p) H (B := 21) h0 hmul (by norm_num)
    (by omega) (by rw [hcard]; norm_num) (by rw [hcard]; omega)
  have hval : (4 * 21 ^ 2 : ℕ) = 1764 := by norm_num
  exact hval ▸ h

/-! ## Part 6 — CAPSTONE: G102F's Capstone A, now UNCONDITIONAL -/

/-- **CAPSTONE — the unconditional `√p`-crossing counting bound on the G80Q terminal
object.** G102F's Capstone A with its named collision residual DISCHARGED by the classical
two-relation Stepanov bound: for every prime `p`, multiplicative `H` (`0 ∉ H`, closed under
`·` and `/`), every collision parameter `B` (`2 ≤ B`, `2B ≤ n`, `2n ≤ B³`, `nB ≤ p`), every
dilation `b ≠ 0`, and EVERY window `4W < p`:

`smallDiffPairs(b·H, W)² ≤ n·smallDiffPairs(b·H, W) + 16·B²·W·n²`,

i.e. `sdp ≲ n + 4nB√W` with `B ≈ (2n)^{1/3}` — nontrivial against both trivial caps on
`4B² < W < n²/(16B²)`, a window that crosses `√p` whenever `√p < n²/(16B²) ≈ n^{4/3}/26`.
Honest scope: at prize shape `p ≈ n⁴` the window closes; the unconditional crossing lives
at `β ≲ 8/3`. No prize claim; CORE stays OPEN / ON-BGK. -/
theorem smallDiffPairs_sq_le_unconditional_stepanov (H : Finset (ZMod p))
    (h0 : (0 : ZMod p) ∉ H)
    (hdiv : ∀ x ∈ H, ∀ y ∈ H, x * y⁻¹ ∈ H) (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    {W B : ℕ} (hW : 4 * W < p) (hB : 2 ≤ B) (h2B : 2 * B ≤ H.card)
    (hB3 : 2 * H.card ≤ B ^ 3) (hp : H.card * B ≤ p) (b : ZMod p) (hb : b ≠ 0) :
    (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
        (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card ^ 2
      ≤ H.card * (((H.image (fun y => b * y)) ×ˢ (H.image (fun y => b * y))).filter
          (fun q => q.1 ≠ q.2 ∧ q.1 - q.2 ∈ strip p W)).card
        + 4 * (4 * B ^ 2) * W * H.card ^ 2 :=
  smallDiffPairs_sq_le_of_addCollisionBound H h0 hdiv hmul hW
    (addCollisionBound_of_closure H h0 hmul hB h2B hB3 hp) b hb

end ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound in
#print axioms hasseDeriv_X_pow
open ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound in
#print axioms hasseDeriv_X_sub_C_pow
open ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound in
#print axioms key_identity
open ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound in
#print axioms condPoly_natDegree_le
open ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound in
#print axioms gen_natDegree_le
open ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound in
#print axioms gen_linearIndependent
open ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound in
#print axioms exists_collision_vanisher
open ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound in
#print axioms stepanov_collision_bound
open ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound in
#print axioms card_collision_le_four_sq
open ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound in
#print axioms pow_card_eq_one_of_mul_closed
open ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound in
#print axioms addCollisionBound_of_closure
open ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound in
#print axioms addCollisionBound_4096
open ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound in
#print axioms smallDiffPairs_sq_le_unconditional_stepanov
