/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicChordNorm
import ArkLib.Research.ProximityGap.Frontier.CyclotomicProjectiveTransfer

/-! # Cross ratios cannot occupy all four dyadic parity classes

Opposite-parity chords on a dyadic orbit have absolute rational norm two.
Every nonzero same-parity chord has norm at least four. A cross-ratio
identity for four prescribed matches cannot interchange these two products.
-/
namespace ProximityGap.DyadicCrossRatioParity
open Polynomial Algebra
noncomputable section
variable {L : Type*} [Field L] [Algebra ℚ L]

/-- Absolute rational norm in the chosen cyclotomic field. -/
def size (x : L) : ℚ := |Algebra.norm ℚ x|

@[simp] theorem size_mul (x y : L) : size (x*y)=size x*size y := by simp [size,abs_mul]

@[simp] theorem size_neg (x : L) : size (-x)=size x := by
  have h : Algebra.norm ℚ (-1:L)=(-1:ℚ)^(Module.finrank ℚ L) := by
    simpa only [map_neg,map_one] using Algebra.norm_algebraMap (S:=L) (-1:ℚ)
  rw [← neg_one_mul, size_mul]
  simp [size,h,abs_pow]

private theorem size_sub_comm (x y : L) : size (x-y)=size (y-x) := by
  rw [← neg_sub y x, size_neg]

variable {m : ℕ} [IsCyclotomicExtension {2^(m+1)} ℚ L] {z : L}

private theorem ordered (hm : 0<m) (hz : IsPrimitiveRoot z (2^(m+1))) {i j : ℕ}
    (ord : j ≤ i) (ne : z^i≠z^j) :
    size (z^i-z^j)=(2:ℚ)^((i-j).gcd (2^(m+1))) := by
  have nonzero : ¬2^(m+1) ∣ i-j := by
    intro div
    obtain ⟨t,ht⟩ := div
    apply ne
    calc z^i = z^j*z^(i-j) := by rw [← pow_add]; congr 1; omega
         _ = z^j := by rw [ht,pow_mul,hz.pow_eq_one,one_pow,mul_one]
  have h := DyadicChordNorm.between hm hz j (i-j) nonzero
  rw [show j+(i-j)=i by omega] at h
  simp [size,h,abs_pow]

/-- A chord between opposite exponent classes has absolute rational norm two. -/
theorem opposite (hm : 0<m) (hz : IsPrimitiveRoot z (2^(m+1))) (i j : ℕ)
    (ne : z^i≠z^j) (parity : i%2≠j%2) : size (z^i-z^j)=2 := by
  wlog ord : j ≤ i generalizing i j
  · rw [size_sub_comm]
    exact this j i ne.symm parity.symm (by omega)
  have odd : Odd (i-j) := by rw [Nat.odd_iff]; omega
  rw [ordered hm hz ord ne,(odd.coprime_two_right.pow_right _).gcd_eq_one,pow_one]

/-- A nonzero chord between sites in the same parity class has norm at least four. -/
theorem same (hm : 0<m) (hz : IsPrimitiveRoot z (2^(m+1))) (i j : ℕ)
    (ne : z^i≠z^j) (parity : i%2=j%2) : 4≤size (z^i-z^j) := by
  wlog ord : j ≤ i generalizing i j
  · rw [size_sub_comm]
    exact this j i ne.symm parity.symm (by omega)
  have divides : 2 ∣ (i-j).gcd (2^(m+1)) :=
    Nat.dvd_gcd (by omega) (dvd_pow_self 2 (by omega))
  have pos : 0 < (i-j).gcd (2^(m+1)) := Nat.gcd_pos_of_pos_right _ (by positivity)
  rw [ordered hm hz ord ne]
  exact (show (4:ℚ) = 2^2 by norm_num).trans_le
    (pow_le_pow_right₀ (by norm_num) (Nat.le_of_dvd pos divides))

@[simp] theorem size_root (hm : 0<m) (hz : IsPrimitiveRoot z (2^(m+1))) (i : ℕ) :
    size (z^i)=1 := by simp [size,map_pow,DyadicChordNorm.norm_root hm hz]

private theorem negative_site (hz : IsPrimitiveRoot z (2^(m+1))) (j : ℕ) :
    -z^j=z^(j+2^m) := by
  have h₂ : (z^(2^m))^2=1 := by rw [← pow_mul,← pow_succ,hz.pow_eq_one]
  have hne : z^(2^m)≠1 := hz.pow_ne_one_of_pos_of_lt (by positivity) (Nat.pow_lt_pow_right (by decide : 1<2) (Nat.lt_succ_self m))
  have half : z^(2^m) = -1 := (sq_eq_one_iff.mp h₂).resolve_left hne
  rw [pow_add,half]; ring

/-- A nonzero same-parity endpoint sum has norm at least four. -/
theorem same_sum (hm : 0<m) (hz : IsPrimitiveRoot z (2^(m+1))) (i j : ℕ)
    (ne : z^i+z^j≠0) (parity : i%2=j%2) : 4≤size (z^i+z^j) := by
  have shift := negative_site hz j
  have h₂ : 2 ∣ 2^m := dvd_pow_self 2 (by omega)
  rw [← sub_neg_eq_add,shift]
  apply same hm hz _ _ (fun eq => ne (by rw [← shift] at eq; rw [eq]; ring))
  omega

/-- An opposite-parity endpoint sum has the same norm as its difference. -/
theorem opposite_sum (hm : 0<m) (hz : IsPrimitiveRoot z (2^(m+1))) (i j : ℕ)
    (ne : z^i+z^j≠0) (parity : i%2≠j%2) : size (z^i+z^j)=2 := by
  have shift := negative_site hz j
  have h₂ : 2 ∣ 2^m := dvd_pow_self 2 (by omega)
  rw [← sub_neg_eq_add,shift]
  apply opposite hm hz _ _ (fun eq => ne (by rw [← shift] at eq; rw [eq]; ring))
  omega

/-- Four matches in the classes EE, EO, OE and OO contradict an equality
of cross ratios. Indices are natural exponents in any order, with explicit
distinctness only for the four chords on each side. -/
theorem excludes_quadrants (hm : 0<m) (hz : IsPrimitiveRoot z (2^(m+1)))
    (a b : Fin 4 → ℕ) (ax : Function.Injective (fun i => z^(a i)))
    (bx : Function.Injective (fun i => z^(b i)))
    (s01 : a 0%2=a 1%2) (s23 : a 2%2=a 3%2) (sd : a 0%2≠a 2%2)
    (t02 : b 0%2=b 2%2) (t13 : b 1%2=b 3%2) (td : b 0%2≠b 1%2) :
    (z^(a 0)-z^(a 1))*(z^(a 2)-z^(a 3))*(z^(b 0)-z^(b 2))*(z^(b 1)-z^(b 3)) ≠
      (z^(a 0)-z^(a 2))*(z^(a 1)-z^(a 3))*(z^(b 0)-z^(b 1))*(z^(b 2)-z^(b 3)) := by
  intro eq
  have norms := congrArg size eq
  simp only [size_mul] at norms
  rw [opposite hm hz _ _ (ax.ne (by decide : (0:Fin 4)≠2)) sd,
      opposite hm hz _ _ (ax.ne (by decide : (1:Fin 4)≠3)) (by omega : a 1%2≠a 3%2),
      opposite hm hz _ _ (bx.ne (by decide : (0:Fin 4)≠1)) td,
      opposite hm hz _ _ (bx.ne (by decide : (2:Fin 4)≠3)) (by omega : b 2%2≠b 3%2)] at norms
  have h₁ := same hm hz _ _ (ax.ne (by decide : (0:Fin 4)≠1)) s01
  have h₂ := same hm hz _ _ (ax.ne (by decide : (2:Fin 4)≠3)) s23
  have h₃ := same hm hz _ _ (bx.ne (by decide : (0:Fin 4)≠2)) t02
  have h₄ := same hm hz _ _ (bx.ne (by decide : (1:Fin 4)≠3)) t13
  have bound : (4:ℚ)*4*4*4 ≤ size (z^(a 0)-z^(a 1))*size (z^(a 2)-z^(a 3))*
      size (z^(b 0)-z^(b 2))*size (z^(b 1)-z^(b 3)) := by
    gcongr
  linarith

end
end ProximityGap.DyadicCrossRatioParity
#print axioms ProximityGap.DyadicCrossRatioParity.excludes_quadrants
