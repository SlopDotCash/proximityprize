/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic
import ArkLib.Data.Polynomial.SpecializationAvoidance

/-! # Coincidences of power slopes under multiplicative translations -/
namespace ArkLib.ProximityGap.Frontier.PowerSlopeCoincidences
open Finset Polynomial
set_option autoImplicit false
variable {G F : Type*} [CommGroup G] [Fintype G] [Field F]

/-- Count ordered pairs by their multiplicative displacement. -/
theorem shift_count (S : Finset G) [DecidableEq G] {m : ℕ}
    (localBound : ∀ g : G, g≠1 → (S.filter fun x => g*x ∈ S).card≤m) :
    S.card*S.card ≤ S.card+(Fintype.card G-1)*m := by
  classical
  let f (g : G) := (S.filter fun x => g*x∈S).card
  have total : ∑ g, f g = S.card*S.card := by
    calc
      _ = ∑ g : G, ∑ x ∈ S, if g*x∈S then 1 else 0 := by simp [f]
      _ = ∑ x ∈ S, ∑ g : G, if g*x∈S then 1 else 0 := sum_comm
      _ = ∑ _x ∈ S, S.card := by
        apply sum_congr rfl
        intro x _
        have h := Equiv.sum_comp (Equiv.mulRight x) (fun g : G => if g∈S then 1 else 0)
        exact h.trans (by simp)
      _ = _ := by simp
  have cap := sum_le_sum (s:=univ.erase (1:G)) (g:=fun _ => m)
    (fun z hz => localBound z (mem_erase.mp hz).1)
  have split := sum_erase_add (s:=univ) f (mem_univ (1:G))
  have self : f 1 = S.card := by simp [f]
  change ∑ z ∈ univ.erase (1:G), f z ≤ _ at cap
  simp only [sum_const,card_erase_of_mem (mem_univ (1:G)),card_univ,nsmul_eq_mul] at cap
  change ∑ z ∈ univ.erase (1:G), f z ≤ (Fintype.card G-1)*m at cap
  rw [self,total] at split
  omega

/-- Rational functions evaluating to a character on distinct torus points
have at most twice their degree many coincidences with a translate unless
the two translated rational functions agree identically. -/
theorem rational_bound (x y : G →* Fˣ) (inj : Function.Injective x)
    (p q : F[X]) (b : ℕ) (hp : p.natDegree≤b) (hq : q.natDegree≤b)
    (S : Finset G) (fit : ∀ g ∈ S, (y g : F)*q.eval (x g : F)=p.eval (x g : F))
    (moving : ∀ g : G, g≠1 → C (y g : F)*p*q.comp (C (x g : F)*X) -
      p.comp (C (x g : F)*X)*q ≠ 0) :
    S.card*S.card ≤ S.card+(Fintype.card G-1)*(2*b) := by
  classical
  apply shift_count
  intro g ng
  let u : F := x g
  let v : F := y g
  let B : F[X] := C u*X
  let D := C v*p*q.comp B-p.comp B*q
  have nonzero : D≠0 := moving g ng
  have db : B.natDegree≤1 := by simpa [B] using natDegree_C_mul_X_pow_le u 1
  have comp (A : F[X]) : (A.comp B).natDegree≤A.natDegree :=
    natDegree_comp_le.trans (by simpa using Nat.mul_le_mul_left A.natDegree db)
  have dp := comp p
  have dq := comp q
  have cap : D.natDegree≤2*b := by
    apply (natDegree_sub_le ..).trans (max_le ?_ ?_)
    · have constant := natDegree_C_mul_le v p
      exact (natDegree_mul_le ..).trans (by omega)
    · exact (natDegree_mul_le ..).trans (by omega)
  apply le_trans _ cap
  apply Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero nonzero
    (Units.val_injective.comp inj).injOn
  intro z hz
  obtain ⟨left,right⟩ := mem_filter.mp hz
  have h := fit z left
  have k := fit (g*z) right
  simp only [map_mul,Units.val_mul] at k
  change v*(y z : F)*q.eval (u*(x z : F))=p.eval (u*(x z : F)) at k
  change D.eval (x z : F) = 0
  simp only [D,B,eval_sub,eval_mul,eval_C,eval_comp,eval_X]
  linear_combination q.eval (x z : F)*k-v*q.eval (u*(x z : F))*h

/-- A non-toric fractional-linear graph through points of a finite cyclic
power graph has at most two points in each nonidentity translate. One of the
two coordinates is assumed injective on the group. -/
theorem mobius_bound (x y : G →* Fˣ) (inj : Function.Injective x)
    (a b c d : F) (det : a*d-b*c≠0) (mixed : a*c≠0 ∨ b*d≠0)
    (S : Finset G) (fit : ∀ g ∈ S, (y g : F)*(c*(x g : F)+d)=a*(x g : F)+b) :
    S.card*S.card ≤ S.card+(Fintype.card G-1)*2 := by
  classical
  apply shift_count
  intro g ng
  let u : F := x g
  let v : F := y g
  have nu : u≠0 := Units.ne_zero _
  have u1 : u≠1 := by
    intro eq
    apply ng
    apply inj
    apply Units.ext
    simpa [u] using eq
  let A := a*c*u*(v-1)
  let B := v*(a*d+b*c*u)-(a*d*u+b*c)
  let D := b*d*(v-1)
  let p : F[X] := C A*X^2+C B*X+C D
  have np : p ≠ 0 := by
    intro zero
    have co (i : ℕ) := congrArg (fun f : F[X] => f.coeff i) zero
    have hA : A=0 := by simpa [p] using co 2
    have hB : B=0 := by simpa [p] using co 1
    have hD : D=0 := by simpa [p] using co 0
    by_cases v1 : v=1
    · apply (mul_ne_zero (sub_ne_zero.mpr (Ne.symm u1)) det)
      dsimp [B] at hB
      rw [v1] at hB
      linear_combination hB
    · rcases mixed with h|h
      · exact (mul_ne_zero (mul_ne_zero h nu) (sub_ne_zero.mpr v1)) hA
      · exact (mul_ne_zero h (sub_ne_zero.mpr v1)) hD
  have degree : p.natDegree≤2 := by
    apply (natDegree_add_le ..).trans (max_le ?_ (by simp))
    apply (natDegree_add_le ..).trans (max_le ?_ ?_)
    · exact natDegree_C_mul_X_pow_le _ _
    · simpa using (natDegree_C_mul_X_pow_le B 1).trans (by decide : 1≤2)
  apply le_trans _ degree
  apply Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero np (Units.val_injective.comp inj).injOn
  intro z hz
  obtain ⟨left,right⟩ := mem_filter.mp hz
  have h := fit z left
  have k := fit (g*z) right
  simp only [map_mul,Units.val_mul] at k
  change v * (y z : F) * (c * (u*(x z : F))+d) = a*(u*(x z : F))+b at k
  simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  dsimp [A,B,D]
  linear_combination (c*(x z : F)+d)*k - v*(c*(u*(x z : F))+d)*h

/-- Numerical non-toric cutoff on the named length when the graph is injective in one coordinate. -/
theorem named {s : ℕ} (h : s*s ≤ s+(1073741824-1)*2) : s≤46341 := by
  by_contra! high
  have h₁ : 46342≤s := by omega
  have h₂ := Nat.mul_le_mul h₁ (by omega : 46341≤s-1)
  have sub : s*(s-1)+s=s*s := by
    cases s <;> simp [Nat.mul_succ]
  omega

/-- Both power exponents in a quarter-rate overrun are odd, so their
combined degree satisfies the even refinement of the numerical cutoff. -/
theorem named_even {s : ℕ} (even : s%2=0) (h : s*s≤s+(1073741824-1)*2) : s≤46340 := by
  have bound := named h
  omega

/-- Integer threshold on the larger of two arbitrary companions to a power
slope at the eighth-rate successor. The comparison guaranteed to move has degree
at most B and at least d−B coincidence sites. -/
theorem eighth_companion {B s : ℕ} (sumDegree : 134217727≤s+B)
    (hits : s*s≤s+(1073741824-1)*(2*B)) : 7479698≤B := by
  by_contra! small
  have lower : 126738030≤s := by omega
  have product := Nat.mul_le_mul lower (by omega : 126738029≤s-1)
  have sub : s*(s-1)+s=s*s := by cases s <;> simp [Nat.mul_succ]
  omega

/-- The corresponding lower bound for the larger companion at quarter rate. -/
theorem quarter_companion {B s : ℕ} (sumDegree : 268435455≤s+B)
    (hits : s*s≤s+(1073741824-1)*(2*B)) : 27117488≤B := by
  by_contra! small
  have lower : 241317968≤s := by omega
  have product := Nat.mul_le_mul lower (by omega : 241317967≤s-1)
  have sub : s*(s-1)+s=s*s := by cases s <;> simp [Nat.mul_succ]
  omega

private theorem dyadic_cap {s : ℕ} (lower : 46341<s) (upper : s≤134217727)
    (pow : ∃ k : ℕ, s=2^k) : s≤67108864 ∧ s%2=0 := by
  obtain ⟨k,rfl⟩ := pow
  have kmax : k≤26 := by
    by_contra! high
    have h := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 27≤k)
    norm_num at h
    omega
  have cap := Nat.pow_le_pow_right (by decide : 0<2) kmax
  norm_num at cap
  cases k with
  | zero => norm_num at lower
  | succ k => exact ⟨cap,by simp [pow_succ]⟩

/-- The dyadic alternative from the Möbius graph bound is inconsistent with
three positive power slopes at eighth rate. The largest degree is `a`. -/
theorem eighth_no_three {a b c : ℕ} (sum : a+b+c=134217727)
    (bp : 0<b) (cp : 0<c) (ba : b≤a) (ca : c≤a)
    (ab : a%2=1 ∨ b%2=1 → a+b≤46341 ∨ ∃ k : ℕ, a+b=2^k)
    (ac : a%2=1 ∨ c%2=1 → a+c≤46341 ∨ ∃ k : ℕ, a+c=2^k) : False := by
  have bnd1 (odd : a%2=1 ∨ b%2=1) := dyadic_cap (by omega : 46341<a+b)
    (by omega : a+b≤134217727) ((ab odd).resolve_left (by omega))
  have bnd2 (odd : a%2=1 ∨ c%2=1) := dyadic_cap (by omega : 46341<a+c)
    (by omega : a+c≤134217727) ((ac odd).resolve_left (by omega))
  by_cases odd : a%2=1
  · have b₁ := bnd1 (.inl odd)
    have b₂ := bnd2 (.inl odd)
    omega
  · by_cases ob : b%2=1
    · have b₁ := bnd1 (.inr ob)
      omega
    · have b₂ := bnd2 (.inr (by omega))
      omega

/-- A proper cover of the saturated eighth-rate face map contributes at most
one double-site orbit per geometric fiber. Its degree divides the odd head
degree, whose smallest prime divisor is seven. Include every singleton slot. -/
theorem eighth_cover {q B heads other : ℕ} (large : 7≤q) (doubleSites : q*B≤536870908)
    (slots : heads≤2*B+3*536870916) (rest : other≤20607410) :
    heads≤1764004436 ∧ heads+other≤1784611846 := by
  have bound := Nat.mul_le_mul_right B large
  omega

/-- Lower bound on the number of distinct double-site direction orbits needed
when every off-quartet factor is charged its full eighth-rate allowance. -/
theorem eighth_orbits {B heads other : ℕ} (slots : heads≤2*B+3*536870916)
    (rest : other≤20607410) (failure : 2147483648<heads+other) : 258131746≤B := by omega

#print axioms eighth_cover
#print axioms eighth_orbits
#print axioms eighth_no_three
#print axioms quarter_companion
#print axioms rational_bound
#print axioms eighth_companion
#print axioms shift_count
#print axioms mobius_bound
#print axioms named_even
#print axioms named
end ArkLib.ProximityGap.Frontier.PowerSlopeCoincidences
