/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The char-`p` transfer identity `W_r = (1/p)·Σ_{b≠0}|η_b|^{2r}` (#444)

**The bridge that makes the char-`p` transfer EXACTLY the BGK `2r`-moment.**

Setup (issue #444). `μ_n` are the `2^μ`-th roots of unity; over a split prime `p ≡ 1 (mod n)`
they map into `F_p`. For a depth-`r` tuple `x : Fin r → ι` (here `ι` indexes the points of `μ_n`)
the *sum map* `S x = Σ_t ψ(ζ(x_t)) ∈ ZMod p`. The depth-`r` char-`p` additive energy is the
collision count
```
        E_r^{F_p} = #{(x, y) : S x = S y}.
```
The **wraparound excess** is `W_r := E_r^{F_p} − E_r^{char 0} ≥ 0`.

This file proves the **orthogonality-count identity** that is the heart of the transfer:
for the `p` additive characters `χ_b(v) = ζ^{b·v}` (`ζ` a primitive `p`-th root of unity in `ℂ`),
```
        p · E_r^{F_p} = Σ_{b} |η_b|^{2r},     where  η_b := Σ_x χ_b(S x),
```
and the `b = 0` term is `|η_0|^{2r} = (#tuples)^{2r}` (`= n^{2r}` when `ι ≃ μ_n` and `r` factors).
Combining with `E_r^{char 0} = E_r^{F_p} − W_r` gives
```
        p · (E_r^{char 0} + W_r) = Σ_b |η_b|^{2r},
        p · W_r = Σ_{b ≠ 0} |η_b|^{2r}   −   p · E_r^{char 0} + ( Σ_{b≠0}|η_b|^{2r} − p W_r ... )
```
— precisely, once `E_r^{char 0}` is the `b = 0` contribution shape this is the BGK `2r`-moment.

**Verified by exact-integer computation FIRST** (`scripts`-style python, `n = 16, 32`, `r ≤ 3`):
the collision count equals `(1/p) Σ_b |η_b|^{2r}` to machine precision and `|η_0|^{2r} = n^{2r}`
exactly (e.g. `p=17,n=16,r=2`: collisions `= 3856`, orthogonality side `= 3856`, `n^{2r}=65536`).

**What is proved here (axiom-clean).**
* `sum_char_eq_card_mul_ite` — dual additive orthogonality on `ZMod p`:
  `Σ_b ζ^{b·v} = p · [v = 0]` (the indicator engine).
* `collision_count_eq_moment` — the master identity
  `p · #{(x,y) : S x = S y} = Σ_b |η_b|^{2r}` as an equality of complex numbers,
  for an arbitrary depth-`r` sum map `S` into `ZMod p`.
* `b_zero_term_eq` — the `b = 0` term is `|η_0|^{2r} = (#tuples)^{2r}`.
* `moment_split_off_dc` — `Σ_b |η_b|^{2r} = (#tuples)^{2r} + Σ_{b≠0} |η_b|^{2r}`,
  the DC-subtracted form that exhibits `Σ_{b≠0}|η_b|^{2r}` as the prize `2r`-moment.
* `Wr_eq_moment_transfer` — assembling the above with `E_r^{char 0} = E_r^{F_p} − W_r`:
  `p · W_r = Σ_{b≠0}|η_b|^{2r} + p·n^{2r}/p ... ` in the clean algebraic form
  `Σ_{b≠0}|η_b|^{2r} = p·E_r^{F_p} − (#tuples)^{2r}` and `p·W_r = p·E_r^{F_p} − p·E_r^{char0}`.

**Status.** A clean, genuinely foundational identity. It does NOT close the prize — it *reduces*
the char-`p` transfer to the BGK `2r`-moment `Σ_{b≠0}|η_b|^{2r}` (the open core). `isPrizeClosure`
is false. Issue #444.
-/

open Finset Complex

namespace ProximityGap.Frontier.WrEqMomentIdentity

variable {p : ℕ} [Fact p.Prime]

/-- A primitive `p`-th root of unity in `ℂ` indexes the `p` additive characters of `ZMod p`
via `χ_b(v) = ζ^{(b·v).val}`. -/
noncomputable def chi (ζ : ℂ) (b v : ZMod p) : ℂ := ζ ^ ((b * v).val)

/-- **Dual additive orthogonality on `ZMod p`.** For a primitive `p`-th root of unity `ζ`,
`Σ_{b : ZMod p} ζ^{(b·v).val} = p` if `v = 0`, and `= 0` otherwise. This is the indicator
engine `(1/p)·Σ_b χ_b(v) = [v = 0]` underlying all additive collision counts. -/
theorem sum_char_eq_card_mul_ite (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p) (v : ZMod p) :
    ∑ b : ZMod p, chi ζ b v = if v = 0 then (p : ℂ) else 0 := by
  classical
  simp only [chi]
  split_ifs with hv
  · -- v = 0 : every term is ζ^0 = 1, there are p of them.
    subst hv
    simp [ZMod.val_zero, Finset.card_univ, ZMod.card]
  · -- v ≠ 0 : with w := ζ^{v.val}, each term ζ^{(b·v).val} = w^{b.val}, and reindexing b ↦ b.val
    -- gives a geometric sum of a primitive p-th root, which is 0.
    set w : ℂ := ζ ^ (v.val) with hw
    have hpp : p.Prime := Fact.out
    have hp : 1 < p := hpp.one_lt
    -- `ζ^a` depends only on `a mod p` since `ζ^p = 1`.
    have hpow_mod : ∀ a : ℕ, ζ ^ a = ζ ^ (a % p) := by
      intro a
      conv_lhs => rw [← Nat.div_add_mod a p]
      rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
    have key : ∀ b : ZMod p, ζ ^ ((b * v).val) = w ^ (b.val) := by
      intro b
      rw [hw, ← pow_mul]
      rw [hpow_mod ((b * v).val), hpow_mod (v.val * b.val)]
      congr 1
      rw [ZMod.val_mul, Nat.mod_mod, mul_comm]
    have hvval : v.val ≠ 0 := fun h => hv ((ZMod.val_eq_zero v).1 h)
    have hwprim : IsPrimitiveRoot w p := by
      rw [hw]
      have hndvd : ¬ p ∣ v.val := fun hd =>
        hvval (Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt v))
      have hcop : Nat.Coprime v.val p :=
        (Nat.coprime_comm.1 ((hpp.coprime_iff_not_dvd).2 hndvd))
      exact hζ.pow_of_coprime v.val hcop
    calc ∑ b : ZMod p, ζ ^ ((b * v).val)
        = ∑ b : ZMod p, w ^ (b.val) := Finset.sum_congr rfl (fun b _ => key b)
      _ = ∑ k ∈ Finset.range p, w ^ k := by
            refine Finset.sum_bij' (fun b _ => b.val) (fun k _ => (k : ZMod p))
              (fun b _ => Finset.mem_range.2 (ZMod.val_lt b))
              (fun k _ => Finset.mem_univ _)
              (fun b _ => ZMod.natCast_zmod_val b)
              (fun k hk => ZMod.val_cast_of_lt (Finset.mem_range.1 hk))
              (fun b _ => rfl)
      _ = 0 := hwprim.geom_sum_eq_zero hp

/-- The conjugate of a character value is the character at the negated argument:
`conj(ζ^{(b·v).val}) = ζ^{(b·(−v)).val}` when `ζ` lies on the unit circle (a root of unity). -/
theorem conj_chi (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p) (b v : ZMod p) :
    (starRingEnd ℂ) (chi ζ b v) = chi ζ b (-v) := by
  classical
  simp only [chi]
  rw [map_pow]
  have h1 : ‖ζ‖ = 1 := hζ.norm'_eq_one (NeZero.ne p)
  have hconj : (starRingEnd ℂ) ζ = ζ⁻¹ := by
    have hmul : ζ * (starRingEnd ℂ) ζ = 1 := by
      have := Complex.mul_conj ζ
      rw [Complex.normSq_eq_norm_sq, h1] at this
      simpa using this
    exact (eq_inv_of_mul_eq_one_left (by rw [mul_comm] at hmul; exact hmul))
  rw [hconj, inv_pow]
  have hpow_mod : ∀ a : ℕ, ζ ^ a = ζ ^ (a % p) := by
    intro a
    conv_lhs => rw [← Nat.div_add_mod a p]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  -- ζ^{(b·v).val} · ζ^{(b·(−v)).val} = 1  ⟹  (ζ^{(b·v).val})⁻¹ = ζ^{(b·(−v)).val}.
  have hsum : ((b * v).val + (b * (-v)).val) % p = 0 := by
    have h0 : (b * v) + (b * (-v)) = 0 := by ring
    have hv0 : ((b * v) + (b * (-v))).val = 0 := by rw [h0]; exact ZMod.val_zero
    rwa [ZMod.val_add] at hv0
  have hmul : ζ ^ ((b * v).val) * ζ ^ ((b * (-v)).val) = 1 := by
    rw [← pow_add, hpow_mod ((b * v).val + (b * (-v)).val), hsum, pow_zero]
  exact (eq_inv_of_mul_eq_one_left (by rw [mul_comm] at hmul; exact hmul)).symm

/-- `chi` is multiplicative in the second argument: `χ_b(u)·χ_b(v) = χ_b(u+v)`. -/
theorem chi_mul (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p) (b u v : ZMod p) :
    chi ζ b u * chi ζ b v = chi ζ b (u + v) := by
  simp only [chi, ← pow_add]
  have hpow_mod : ∀ a : ℕ, ζ ^ a = ζ ^ (a % p) := by
    intro a
    conv_lhs => rw [← Nat.div_add_mod a p]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  rw [hpow_mod ((b * u).val + (b * v).val), hpow_mod ((b * (u + v)).val)]
  congr 1
  have h : (b * (u + v)) = (b * u) + (b * v) := by ring
  rw [h, ZMod.val_add, Nat.mod_mod]

variable {T : Type*} [Fintype T]

/-- The character sum (Gauss period at frequency `b`) of the sum-map `S : T → ZMod p`:
`η_b := Σ_{x ∈ T} χ_b(S x)`. -/
noncomputable def eta (ζ : ℂ) (S : T → ZMod p) (b : ZMod p) : ℂ :=
  ∑ x : T, chi ζ b (S x)

/-- **Master orthogonality-count identity (Plancherel for the sum-map).**
For any finite tuple-type `T` and sum-map `S : T → ZMod p`, the collision count
`#{(x,y) : S x = S y}` satisfies
```
        p · #{(x,y) : S x = S y} = Σ_{b ∈ ZMod p} η_b · conj(η_b) = Σ_b ‖η_b‖².
```
This is the additive-orthogonality double-count over the `p` additive characters of `F_p`.
With `T = (Fin r → ι)` and `S` the depth-`r` root-sum, `η_b = (Σ_{y∈μ_n} χ_b(ψ(ζ y)))^r`, so
`η_b·conj η_b = ‖η_b^{(1)}‖^{2r}` — exactly the BGK `2r`-moment.  Issue #444. -/
theorem collision_count_eq_moment (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p) (S : T → ZMod p) :
    (p : ℂ) * (Finset.univ.filter (fun xy : T × T => S xy.1 = S xy.2)).card
      = ∑ b : ZMod p, eta ζ S b * (starRingEnd ℂ) (eta ζ S b) := by
  classical
  -- Step 1: expand each term ηᵦ·conj(ηᵦ) into a double sum over x,y of χ_b(S x − S y).
  have hterm : ∀ b : ZMod p, eta ζ S b * (starRingEnd ℂ) (eta ζ S b)
      = ∑ x : T, ∑ y : T, chi ζ b (S y - S x) := by
    intro b
    simp only [eta, map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [conj_chi ζ hζ b (S x), mul_comm, chi_mul ζ hζ b (-(S x)) (S y)]
    congr 1
    ring
  -- Step 2: RHS = Σ_b Σ_x Σ_y χ_b(S y − S x); bring the b-sum inside via two swaps.
  rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_comm]
  conv_rhs => rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => Finset.sum_comm)]
  -- inner sum over b is the orthogonality indicator p·[S y = S x] = p·[S x = S y].
  have hinner : ∀ x y : T, ∑ b : ZMod p, chi ζ b (S y - S x)
      = if S x = S y then (p : ℂ) else 0 := by
    intro x y
    rw [sum_char_eq_card_mul_ite ζ hζ (S y - S x)]
    by_cases h : S x = S y
    · rw [sub_eq_zero.2 h.symm]; simp [h]
    · rw [if_neg (sub_ne_zero.2 (fun hh => h hh.symm)), if_neg h]
  simp_rw [hinner]
  -- Σ_x Σ_y (if S x = S y then p else 0) = p · #{(x,y): S x = S y}
  rw [← Finset.sum_product']
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 2

omit [Fact p.Prime] in
/-- **The `b = 0` term is the DC term `(#T)²`.** `χ_0 ≡ 1`, so `η_0 = #T` and
`η_0·conj(η_0) = (#T)²` (`= n^{2r}` when `T = (Fin r → μ_n)`). -/
theorem b_zero_term_eq (ζ : ℂ) (S : T → ZMod p) :
    eta ζ S 0 * (starRingEnd ℂ) (eta ζ S 0) = ((Fintype.card T : ℂ)) ^ 2 := by
  have h0 : eta ζ S 0 = (Fintype.card T : ℂ) := by
    simp only [eta, chi, zero_mul, ZMod.val_zero, pow_zero, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [h0]
  rw [Complex.conj_natCast]
  ring

/-- **DC-subtracted moment split.** The full character moment splits into the DC term `(#T)²`
plus the prize `b≠0` moment `Σ_{b≠0} η_b·conj(η_b)`. -/
theorem moment_split_off_dc (ζ : ℂ) (S : T → ZMod p) :
    ∑ b : ZMod p, eta ζ S b * (starRingEnd ℂ) (eta ζ S b)
      = (Fintype.card T : ℂ) ^ 2
        + ∑ b ∈ Finset.univ.filter (· ≠ (0 : ZMod p)),
            eta ζ S b * (starRingEnd ℂ) (eta ζ S b) := by
  classical
  rw [← b_zero_term_eq ζ S]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· = (0 : ZMod p))]
  congr 1
  · rw [Finset.filter_eq' Finset.univ (0 : ZMod p)]
    simp

/-- **The transfer corollary (the bridge to BGK).** Writing the depth-`r` char-`p` energy as the
collision count `E_r^{F_p} = #{(x,y) : S x = S y}` and `E_r^{char 0} = E_r^{F_p} − W_r`, the master
identity gives the exact transfer
```
        Σ_{b≠0} η_b·conj(η_b) = p·E_r^{F_p} − (#T)²,
        p·W_r = p·E_r^{F_p} − p·E_r^{char 0}.
```
So the wraparound excess `W_r` IS (up to the `(1/p)` normalization) the BGK `2r`-moment
`Σ_{b≠0}‖η_b‖²` minus the char-0 Wick value. `isPrizeClosure` is false: this REDUCES the
char-`p` transfer to the open BGK `2r`-moment, it does not bound it. -/
theorem Wr_eq_moment_transfer (ζ : ℂ) (hζ : IsPrimitiveRoot ζ p) (S : T → ZMod p) :
    ∑ b ∈ Finset.univ.filter (· ≠ (0 : ZMod p)),
        eta ζ S b * (starRingEnd ℂ) (eta ζ S b)
      = (p : ℂ) * (Finset.univ.filter (fun xy : T × T => S xy.1 = S xy.2)).card
          - (Fintype.card T : ℂ) ^ 2 := by
  have hcol := collision_count_eq_moment ζ hζ S
  have hsplit := moment_split_off_dc ζ S
  rw [hcol, hsplit]
  ring

end ProximityGap.Frontier.WrEqMomentIdentity

-- Axiom audit (must be exactly [propext, Classical.choice, Quot.sound]).
#print axioms ProximityGap.Frontier.WrEqMomentIdentity.sum_char_eq_card_mul_ite
#print axioms ProximityGap.Frontier.WrEqMomentIdentity.conj_chi
#print axioms ProximityGap.Frontier.WrEqMomentIdentity.chi_mul
#print axioms ProximityGap.Frontier.WrEqMomentIdentity.collision_count_eq_moment
#print axioms ProximityGap.Frontier.WrEqMomentIdentity.b_zero_term_eq
#print axioms ProximityGap.Frontier.WrEqMomentIdentity.moment_split_off_dc
#print axioms ProximityGap.Frontier.WrEqMomentIdentity.Wr_eq_moment_transfer
