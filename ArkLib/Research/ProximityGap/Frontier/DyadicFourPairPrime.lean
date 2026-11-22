/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicFourPairGeometry
import Mathlib.FieldTheory.Finite.Basic

/-! # The height-12 involution criterion at every dyadic order -/

namespace ProximityGap.DyadicFourPairPrime
open DyadicFourPairGeometry DyadicPairMinorTransfer

private theorem modpow {F : Type*} [Field F] {n : ℕ} {t : F} (ht : IsPrimitiveRoot t n) (r : ℕ) : t^(r%n)=t^r := by
    rw [ht.eq_orderOf,pow_mod_orderOf]

private theorem back {K L : Type*} [Field K] [Field L] {n : ℕ} (np : 0<n) {w : K} {z : L}
    (hw : IsPrimitiveRoot w n) (hz : IsPrimitiveRoot z n) {i j : ℕ} (same : w^i=w^j) : z^i=z^j := by
  have ij : i%n=j%n := hw.pow_inj (Nat.mod_lt _ np) (Nat.mod_lt _ np)
    ((modpow hw i).trans (same.trans (modpow hw j).symm))
  rw [←modpow hz i,←modpow hz j,ij]

private theorem recover {K : Type*} [Field K] {u v x y a b c : K}
    (ux : u≠x) (uy : u≠y) (p₀ : c*u*v-a*(u+v)=b) (p₁ : c*x*y-a*(x+y)=b)
    (shape : u*v=x*y ∨ (u+v=0 ∧ x+y=0)) : a=0 ∨ c=0 ∧ b=0 := by
  have different (hp : u*v=x*y) (hs : u+v=x+y) : False :=
    mul_ne_zero (sub_ne_zero.mpr ux) (sub_ne_zero.mpr uy) (by linear_combination u*hs-hp)
  rcases shape with hp|⟨s₀,s₁⟩
  · left
    have z : a*(u+v-(x+y))=0 := by linear_combination p₁-p₀+c*hp
    exact (mul_eq_zero.mp z).resolve_right (sub_ne_zero.mpr (different hp))
  · right
    have hp : u*v≠x*y := fun eq => different eq (s₀.trans s₁.symm)
    have z : c*(u*v-x*y)=0 := by linear_combination p₀-p₁+a*s₀-a*s₁
    have hc := (mul_eq_zero.mp z).resolve_right (sub_ne_zero.mpr hp)
    exact ⟨hc,by simpa [hc,s₀] using p₀.symm⟩

/-- Once the first two marked pairs and each further pair have vanishing
minors in the cyclotomic field, the dyadic seven-site theorem forces a
dihedral shape back in the prime field. -/
theorem of_minors {m p : ℕ} [Fact p.Prime] {z : ZMod p} {w : ℂ} (hz : IsPrimitiveRoot z (2^m))
    (hw : IsPrimitiveRoot w (2^m)) (q : Fin 4 × Fin 2 ↪ Fin (2^m)) (a b c : ZMod p)
    (law : ∀ i, c*z^(q (i,0)).val*z^(q (i,1)).val-a*(z^(q (i,0)).val+z^(q (i,1)).val)=b)
    (rel : ∀ i, minor (w^(q (0,0)).val) (w^(q (0,1)).val) (w^(q (1,0)).val) (w^(q (1,1)).val)
      (w^(q (i,0)).val) (w^(q (i,1)).val)=0) : a=0 ∨ c=0 ∧ b=0 := by
  have np : 0<2^m := by positivity
  let Z (i : Fin 4 × Fin 2) := z^(q i).val
  let W (i : Fin 4 × Fin 2) := w^(q i).val
  have iz : Function.Injective Z := fun i j eq => q.injective (Fin.ext (hz.pow_inj (q i).isLt (q j).isLt eq))
  have shape := pattern hw (DyadicSevenProjectivities.all_orders (m:=m) hw) q rel
  apply recover (u:=Z (0,0)) (v:=Z (0,1)) (x:=Z (1,0)) (y:=Z (1,1))
    (iz.ne (by decide)) (iz.ne (by decide)) (law 0) (law 1)
  rcases shape with h|⟨h₀,h₁⟩
  · left
    dsimp only [Z]
    rw [←pow_add,←pow_add]
    exact back np hw hz (by simpa only [pow_add] using h)
  · right
    have anti (i : Fin 4) (h : W (i,0)+W (i,1)=0) : Z (i,0)+Z (i,1)=0 := by
      have sq : (W (i,0))^2=(W (i,1))^2 := by linear_combination (W (i,0)-W (i,1))*h
      have sq' : (Z (i,0))^2=(Z (i,1))^2 := by
        dsimp only [Z]
        rw [←pow_mul,←pow_mul]
        exact back np hw hz (by simpa only [pow_mul,W] using sq)
      have ne : Z (i,0)≠Z (i,1) := iz.ne (fun eq => (by decide : (0:Fin 2)≠1) (congrArg Prod.snd eq))
      exact eq_neg_iff_add_eq_zero.mp ((sq_eq_sq_iff_eq_or_eq_neg.mp sq').resolve_left ne)
    exact ⟨anti 0 h₀,anti 1 h₁⟩

/-- A non-dihedral involution exchanges at most three disjoint pairs of
order-2^m roots in a prime field as soon as 12^φ(2^m) is smaller than p². -/
theorem dihedral {m p : ℕ} [Fact p.Prime] {z : ZMod p} (hz : IsPrimitiveRoot z (2^m))
    (large : 12^(2^m).totient<p^2) (q : Fin 4 × Fin 2 ↪ Fin (2^m)) (a b c : ZMod p)
    (det : a^2+b*c≠0)
    (law : ∀ i, c*z^(q (i,0)).val*z^(q (i,1)).val-a*(z^(q (i,0)).val+z^(q (i,1)).val)=b) :
    a=0 ∨ c=0 ∧ b=0 := by
  let n := 2^m
  have np : 0<n := by dsimp [n];positivity
  have card := Fintype.card_le_of_injective q q.injective
  simp only [Fintype.card_prod,Fintype.card_fin] at card
  have length : 2<n := by dsimp [n];omega
  have hn : n∣p-1 := hz.dvd_of_pow_eq_one _ (ZMod.pow_card_sub_one_eq_one (hz.ne_zero np.ne'))
  have pp := (Fact.out : p.Prime).one_lt
  have below : n<p := (Nat.le_of_dvd (by omega) hn).trans_lt (by omega)
  let _ : NeZero (n:ZMod p) := ⟨fun e => below.not_ge (Nat.le_of_dvd np ((ZMod.natCast_eq_zero_iff n p).mp e))⟩
  obtain ⟨w,hw⟩ : ∃ w : ℂ, IsPrimitiveRoot w n := ⟨_,Complex.isPrimitiveRoot_exp n np.ne'⟩
  let W (i : Fin 4 × Fin 2) := w^(q i).val
  have rel (i : Fin 4) : minor (W (0,0)) (W (0,1)) (W (1,0)) (W (1,1)) (W (i,0)) (W (i,1))=0 := by
    by_cases zero : i=0
    · subst i;simp only [minor];ring
    have neq (j : Fin 2) : q (i,j)≠q (0,1) := q.injective.ne (fun h => zero (congrArg Prod.fst h))
    exact DyadicPairMinorTransfer.transfer (n:=n) length hz hw _ _ _ _ _ _
      (q.injective.ne (by decide)) (q.injective.ne (by decide)) (q.injective.ne (by decide)) (neq 0) (neq 1)
      (incident det (law 0) (law 1) (law i)) large
  exact of_minors hz hw q a b c law rel

end ProximityGap.DyadicFourPairPrime
#print axioms ProximityGap.DyadicFourPairPrime.dihedral
