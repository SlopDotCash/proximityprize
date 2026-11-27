/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PrimeHDOrder
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

/-!
# Prime-Field Top-Variable Hasse Derivatives & Smoothness-Free Proper Cuts (`PrimeHDTopHasse`)

Generalized formalization of `PortLowBase` (`P0_9_3_2`: `translateTop`, `topHasse`,
`topHasse_order`, `exact_hasse_not_dvd`) and `Final50OrderProof_2` (`topHasse_one_not_dvd`,
`topHasse_bounds`, proper cut extraction) for arbitrary jet order `d : ℕ` (`n = d + 1` variables,
top jet variable `Fin.last d`) over any field `L` of characteristic `0` or prime characteristic
`p > deg_{Y_d}(f)`.

Crucially, `topHasse a P` extracts a polynomial NOT divisible by `f` with guaranteed shift-order
`OrderAt (topHasse a P) S (ord - a)` for **every** codeword `S` — requiring **ZERO smoothness**
of `f = 0` at `S`! When `ord - a ≥ 1`, `atJet_eq_zero_of_orderAt_pos` immediately yields
`(topHasse a P)(X, S, D¹S, ..., D^d S) = 0`, feeding directly into `PrimeHDResultant`!

Clean-room / attributed Apache-2.0 adaptation from `proximity-prize/proximity-prize`
(`PortLowBase.lean`, `Final50Order.lean`), generalized to arbitrary `d` and arbitrary fields.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace ArkLib.ProximityGap.Frontier.PrimeHDTopHasse

open Polynomial PrimeHDOrder
open scoped BigOperators

noncomputable section

/-! ### Part 1: Top-Variable Translation and Hasse Derivatives `topHasse` -/

/-- Translate the top jet variable `Y_d = X (Fin.last d)` by a formal indeterminate `T`:
`Y_d ↦ Y_d + T`, fixing `X` and all lower jet variables `Y_0, ..., Y_{d-1}`. -/
def translateTop {L : Type*} [CommRing L] {d : ℕ} :
    JetRow L (d + 1) →+* Polynomial (JetRow L (d + 1)) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C) fun i =>
    Polynomial.C (MvPolynomial.X i) + if i = Fin.last d then Polynomial.X else 0

/-- The `a`-th Hasse derivative of `P ∈ JetRow L (d + 1)` with respect to the top jet variable
`Y_d = X (Fin.last d)`. -/
def topHasse {L : Type*} [CommRing L] {d : ℕ} (a : ℕ) (P : JetRow L (d + 1)) : JetRow L (d + 1) :=
  (translateTop P).coeff a

theorem erase_last_add {d : ℕ} (u : Fin (d + 1) →₀ ℕ) :
    u.erase (Fin.last d) + Finsupp.single (Fin.last d) (u (Fin.last d)) = u := by
  ext i
  by_cases hi : i = Fin.last d
  · subst hi; simp
  · simp [Finsupp.erase_ne hi, Finsupp.single_eq_of_ne hi]

theorem apply_add_last {d : ℕ} (m : Fin (d + 1) →₀ ℕ) (a : ℕ) :
    (m + Finsupp.single (Fin.last d) a) (Fin.last d) = m (Fin.last d) + a := by
  simp

private theorem translate_independent {L : Type*} [CommRing L] {d : ℕ}
    (m : Fin (d + 1) →₀ ℕ) (c : Polynomial L) (hm : m (Fin.last d) = 0) :
    translateTop (MvPolynomial.monomial m c) = Polynomial.C (MvPolynomial.monomial m c) := by
  rw [translateTop, MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq, map_mul]
  simp only [RingHom.comp_apply]
  congr 1
  unfold Finsupp.prod
  rw [map_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hne : i ≠ Fin.last d := by
    intro he
    subst he
    exact (Finsupp.mem_support_iff.mp hi) hm
  simp [hne]

private theorem translate_top_pow_coeff {L : Type*} [CommRing L] {d : ℕ} (n a : ℕ) :
    ((Polynomial.C (MvPolynomial.X (Fin.last d) : JetRow L (d + 1)) + Polynomial.X) ^ n).coeff a =
      MvPolynomial.C (↑(n.choose a) : Polynomial L) * MvPolynomial.X (Fin.last d) ^ (n - a) := by
  rw [add_comm (Polynomial.C (MvPolynomial.X (Fin.last d) : JetRow L (d + 1))),
    ← Polynomial.taylor_X_pow, Polynomial.taylor_coeff,
    Polynomial.X_pow_eq_monomial, Polynomial.hasseDeriv_monomial]
  simp [Polynomial.eval_monomial]

private theorem topHasse_monomial {L : Type*} [CommRing L] {d : ℕ}
    (a : ℕ) (u : Fin (d + 1) →₀ ℕ) (c : Polynomial L) :
    topHasse a (MvPolynomial.monomial u c) =
      MvPolynomial.monomial (u.erase (Fin.last d) + Finsupp.single (Fin.last d) (u (Fin.last d) - a))
        (↑((u (Fin.last d)).choose a) * c) := by
  have hu : MvPolynomial.monomial u c =
      MvPolynomial.monomial (u.erase (Fin.last d)) c * MvPolynomial.X (Fin.last d) ^ (u (Fin.last d)) := by
    rw [← MvPolynomial.monomial_add_single, erase_last_add]
  have hx : translateTop (MvPolynomial.X (Fin.last d) : JetRow L (d + 1)) =
      Polynomial.C (MvPolynomial.X (Fin.last d)) + Polynomial.X := by
    simp [translateTop]
  unfold topHasse
  rw [hu, map_mul, map_pow, translate_independent _ _ Finsupp.erase_same, hx,
    Polynomial.coeff_C_mul, translate_top_pow_coeff, ← mul_assoc]
  rw [mul_comm (MvPolynomial.monomial (u.erase (Fin.last d)) c), MvPolynomial.C_mul_monomial,
    ← MvPolynomial.monomial_add_single]

/-- Exact coefficient formula for `topHasse a P`. -/
theorem topHasse_coeff {L : Type*} [CommRing L] {d : ℕ}
    (a : ℕ) (P : JetRow L (d + 1)) (m : Fin (d + 1) →₀ ℕ) :
    (topHasse a P).coeff m =
      ↑((m (Fin.last d) + a).choose a) * P.coeff (m + Finsupp.single (Fin.last d) a) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [topHasse_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases ha : a ≤ u (Fin.last d)
    · have hcancel :
          (u.erase (Fin.last d) + Finsupp.single (Fin.last d) (u (Fin.last d) - a)) +
            Finsupp.single (Fin.last d) a = u := by
        rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel ha, erase_last_add]
      have heq : u.erase (Fin.last d) + Finsupp.single (Fin.last d) (u (Fin.last d) - a) = m ↔
          u = m + Finsupp.single (Fin.last d) a := by
        constructor
        · intro h; rw [← h, hcancel]
        · intro h; exact add_right_cancel (hcancel.trans h)
      simp only [heq]
      by_cases h : u = m + Finsupp.single (Fin.last d) a
      · have htop : u (Fin.last d) = m (Fin.last d) + a := by rw [h, apply_add_last]
        simp only [htop, ite_eq_left h]
      · simp [h]
    · have hne : u ≠ m + Finsupp.single (Fin.last d) a := by
        intro h
        have htop : u (Fin.last d) = m (Fin.last d) + a := by rw [h, apply_add_last]
        omega
      rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge ha)]
      simp [hne]
  | add P Q hP hQ =>
    simp only [topHasse, map_add, Polynomial.coeff_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply] at hP hQ ⊢
    rw [hP, hQ, mul_add]

theorem topHasse_zero {L : Type*} [CommRing L] {d : ℕ} (P : JetRow L (d + 1)) :
    topHasse 0 P = P := by
  ext m
  simp [topHasse_coeff]

theorem source_support {L : Type*} [CommRing L] {d a : ℕ} {P : JetRow L (d + 1)}
    {m : Fin (d + 1) →₀ ℕ} (hm : m ∈ (topHasse a P).support) :
    m + Finsupp.single (Fin.last d) a ∈ P.support := by
  rw [MvPolynomial.mem_support_iff, topHasse_coeff] at hm
  exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hm)

theorem sum_add_last {d : ℕ} (w : Fin (d + 1) → ℕ) (m : Fin (d + 1) →₀ ℕ) (a : ℕ) :
    (m + Finsupp.single (Fin.last d) a).sum (fun i k => w i * k) =
      m.sum (fun i k => w i * k) + w (Fin.last d) * a := by
  rw [Finsupp.sum_add_index' (fun i => Nat.mul_zero (w i)) (fun i b c => Nat.mul_add (w i) b c),
    Finsupp.sum_single_index (h := fun i k => w i * k) (Nat.mul_zero _)]

theorem total_add_last {d : ℕ} (m : Fin (d + 1) →₀ ℕ) (a : ℕ) :
    (m + Finsupp.single (Fin.last d) a).sum (fun _ k => k) = m.sum (fun _ k => k) + a := by
  simpa only [one_mul] using sum_add_last (fun _ => 1) m a

/-! ### Part 2: Smoothness-Free Order Drop (`topHasse_order`) and Degree/Weight Bounds -/

private theorem translate_shift {L : Type*} [CommRing L] {d : ℕ} (S : Polynomial L) :
    translateTop.comp (shiftJetHom (n := d + 1) S) =
      (Polynomial.mapRingHom (shiftJetHom (n := d + 1) S)).comp translateTop := by
  apply MvPolynomial.ringHom_ext
  · intro c; simp [translateTop, shiftJetHom]
  · intro i
    simp only [RingHom.comp_apply, shiftJetHom, translateTop, MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval₂Hom_C, map_add, Polynomial.coe_mapRingHom, Polynomial.map_C]
    by_cases hi : i = Fin.last d
    · simp only [hi, ite_true, Polynomial.map_X]
      exact add_right_comm _ _ _
    · simp only [hi, ite_false, Polynomial.map_zero, add_zero]

/-- **Smoothness-Free Order Drop (`PortLowBase.topHasse_order`):**
If `OrderAt P S ord`, then `OrderAt (topHasse a P) S (ord - a)` for **every** polynomial `S`
(even singular solutions on `f = 0`). -/
theorem topHasse_order {L : Type*} [CommRing L] {d : ℕ}
    (a ord : ℕ) (P : JetRow L (d + 1)) (S : Polynomial L)
    (h : OrderAt P S ord) : OrderAt (topHasse a P) S (ord - a) := by
  have he := RingHom.congr_fun (translate_shift (d := d) S) P
  change translateTop (shiftJet P S) = (translateTop P).map (shiftJetHom S) at he
  have hs : topHasse a (shiftJet P S) = shiftJet (topHasse a P) S := by
    change (translateTop (shiftJet P S)).coeff a = shiftJetHom S ((translateTop P).coeff a)
    rw [he, Polynomial.coeff_map]
  intro m hm
  rw [← hs] at hm
  have hd := h _ (source_support hm)
  change ord ≤ (m + Finsupp.single (Fin.last d) a).sum (fun _ k => k) at hd
  rw [total_add_last] at hd
  change ord - a ≤ m.sum (fun _ k => k)
  omega

/-- `topHasse a P` lowers `TrueWeightLE` by `a * (physDeg - d)` (and in particular preserves
`TrueWeightLE physDeg P T`). -/
theorem topHasse_trueWeightLE_sub {L : Type*} [CommRing L] {d : ℕ}
    (physDeg T a : ℕ) (P : JetRow L (d + 1)) (hw : TrueWeightLE physDeg P T) :
    TrueWeightLE physDeg (topHasse a P) (T - a * (physDeg - d)) := by
  intro m hm
  have hp := hw _ (source_support hm)
  rw [sum_add_last (fun i : Fin (d + 1) => physDeg - i.val)] at hp
  simp only [Fin.val_last] at hp
  rw [topHasse_coeff]
  have hc := Polynomial.natDegree_mul_le
    (p := (↑((m (Fin.last d) + a).choose a) : Polynomial L))
    (q := P.coeff (m + Finsupp.single (Fin.last d) a))
  rw [Polynomial.natDegree_natCast, zero_add] at hc
  have hmul : (physDeg - d) * a = a * (physDeg - d) := Nat.mul_comm _ _
  omega

theorem topHasse_trueWeightLE {L : Type*} [CommRing L] {d : ℕ}
    (physDeg T a : ℕ) (P : JetRow L (d + 1)) (hw : TrueWeightLE physDeg P T) :
    TrueWeightLE physDeg (topHasse a P) T := fun m hm =>
  (topHasse_trueWeightLE_sub physDeg T a P hw m hm).trans (Nat.sub_le _ _)

theorem topHasse_totalDegree_le {L : Type*} [CommRing L] {d : ℕ}
    (a : ℕ) (P : JetRow L (d + 1)) :
    (topHasse a P).totalDegree ≤ P.totalDegree - a := by
  apply Finset.sup_le
  intro m hm
  have hp := MvPolynomial.le_totalDegree (source_support hm)
  change (m + Finsupp.single (Fin.last d) a).sum (fun _ k => k) ≤ P.totalDegree at hp
  rw [total_add_last] at hp
  change m.sum (fun _ k => k) ≤ P.totalDegree - a
  omega

theorem topHasse_degreeOf_last_le {L : Type*} [CommRing L] {d : ℕ}
    (a : ℕ) (P : JetRow L (d + 1)) :
    (topHasse a P).degreeOf (Fin.last d) ≤ P.degreeOf (Fin.last d) - a := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro m hm
  have hp := MvPolynomial.le_degreeOf_of_mem_support (Fin.last d) (source_support hm)
  rw [apply_add_last] at hp
  omega

theorem topHasse_degreeOf_le {L : Type*} [CommRing L] {d : ℕ}
    (a : ℕ) (P : JetRow L (d + 1)) (i : Fin (d + 1)) :
    (topHasse a P).degreeOf i ≤ P.degreeOf i := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro m hm
  have hp := MvPolynomial.le_degreeOf_of_mem_support i (source_support hm)
  have hle : m i ≤ (m + Finsupp.single (Fin.last d) a) i := by simp
  exact hle.trans hp

/-! ### Part 3: Exact-Divisibility Non-Divisibility (`exact_hasse_not_dvd` & `topHasse_one_not_dvd`) -/

private theorem coeff_X_mul_pow {R : Type*} [CommSemiring R]
    (V W : Polynomial R) (a : ℕ) :
    ((Polynomial.X * V) ^ a * W).coeff a = (V.coeff 0) ^ a * W.coeff 0 := by
  rw [mul_pow, mul_assoc]
  calc _ = (V ^ a * W).coeff 0 := by
        simpa only [zero_add] using Polynomial.coeff_X_pow_mul (V ^ a * W) a 0
    _ = _ := by
      change Polynomial.constantCoeff (V ^ a * W) =
        Polynomial.constantCoeff V ^ a * Polynomial.constantCoeff W
      rw [map_mul, map_pow]

/-- **Abstract Exact-Divisibility Non-Divisibility (`PortLowBase.exact_hasse_not_dvd`):**
Over ANY commutative ring `R` and any ring homomorphism `T : R →+* Polynomial R` with
`(T G).coeff 0 = G`, if `f` is prime with `¬ f ∣ (T f).coeff 1`, `f^a ∣ P`, and `¬ f^(a+1) ∣ P`,
then `¬ f ∣ (T P).coeff a`. -/
theorem exact_hasse_not_dvd {R : Type*} [CommRing R]
    (T : R →+* Polynomial R) (T0 : ∀ G, (T G).coeff 0 = G)
    (f P : R) (a : ℕ) (hf : Prime f) (hsep : ¬ f ∣ (T f).coeff 1)
    (hdiv : f ^ a ∣ P) (hexact : ¬ f ^ (a + 1) ∣ P) : ¬ f ∣ (T P).coeff a := by
  obtain ⟨U, rfl⟩ := hdiv
  have hu : ¬ f ∣ U := by
    rintro ⟨V, rfl⟩
    exact hexact ⟨V, by rw [pow_succ, mul_assoc]⟩
  let J := Ideal.span ({f} : Set R)
  have : J.IsPrime := Ideal.isPrime_span_singleton_of_prime hf
  let reduce := Ideal.Quotient.mk J
  let tr := (Polynomial.mapRingHom reduce).comp T
  have hzero (G : R) : reduce G = 0 ↔ f ∣ G :=
    Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  have hcoeff (G : R) (n : ℕ) : (tr G).coeff n = reduce ((T G).coeff n) :=
    Polynomial.coeff_map _ _
  have hconstant (G : R) : (tr G).coeff 0 = reduce G := by rw [hcoeff, T0]
  obtain ⟨V, hV⟩ := Polynomial.X_dvd_iff.mpr
    (show (tr f).coeff 0 = 0 by rw [hconstant]; exact (hzero _).mpr dvd_rfl)
  have hfirst : V.coeff 0 = reduce ((T f).coeff 1) := by
    rw [← hcoeff, hV]
    exact (Polynomial.coeff_X_mul V 0).symm
  have hr : reduce ((T (f ^ a * U)).coeff a) = reduce ((T f).coeff 1) ^ a * reduce U := by
    calc _ = (tr (f ^ a * U)).coeff a := (hcoeff _ _).symm
      _ = (V.coeff 0) ^ a * (tr U).coeff 0 := by
        rw [map_mul, map_pow, hV]
        exact coeff_X_mul_pow V (tr U) a
      _ = _ := by rw [hfirst, hconstant]
  intro h
  exact (mul_ne_zero (pow_ne_zero _ ((hzero _).not.mpr hsep))
    ((hzero _).not.mpr hu)) (hr.symm.trans ((hzero _).mpr h))

/-- Over any field `L`, if `f : JetRow L (d + 1)` is irreducible with `0 < deg_{Y_d}(f)` and
either `ringChar L = 0` or `deg_{Y_d}(f) < ringChar L`, then `¬ f ∣ topHasse 1 f`. -/
theorem topHasse_one_not_dvd {L : Type*} [Field L] {d : ℕ}
    (f : JetRow L (d + 1)) (hf : Irreducible f)
    (hpos : 0 < f.degreeOf (Fin.last d))
    (hchar : ringChar L = 0 ∨ f.degreeOf (Fin.last d) < ringChar L) :
    ¬ f ∣ topHasse 1 f := by
  classical
  have hdeg : (topHasse 1 f).degreeOf (Fin.last d) ≤ f.degreeOf (Fin.last d) - 1 :=
    topHasse_degreeOf_last_le 1 f
  have hnz : topHasse 1 f ≠ 0 := by
    have hsup : 0 < f.support.sup (fun m => m (Fin.last d)) := by
      rwa [← MvPolynomial.degreeOf_eq_sup]
    obtain ⟨u, hu, htop⟩ := (Finset.le_sup_iff hsup).mp (le_refl _)
    rw [← MvPolynomial.degreeOf_eq_sup] at htop
    have hupos : 0 < u (Fin.last d) := hpos.trans_le htop
    have hule : u (Fin.last d) ≤ f.degreeOf (Fin.last d) :=
      MvPolynomial.le_degreeOf_of_mem_support (Fin.last d) hu
    let m := u.erase (Fin.last d) + Finsupp.single (Fin.last d) (u (Fin.last d) - 1)
    have hsum : m + Finsupp.single (Fin.last d) 1 = u := by
      dsimp [m]
      rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel hupos, erase_last_add]
    have hm : m (Fin.last d) + 1 = u (Fin.last d) := by
      rw [← apply_add_last, hsum]
    have hc : (↑(u (Fin.last d)) : Polynomial L) ≠ 0 := by
      intro hz
      have hz' : (↑(u (Fin.last d)) : L) = 0 := by
        simpa only [map_natCast, map_zero] using congrArg (Polynomial.evalRingHom (0 : L)) hz
      rcases hchar with h0 | hlt
      · have : CharZero L := (CharP.ringChar_zero_iff_CharZero L).mp h0
        have := Nat.cast_eq_zero.mp hz'
        omega
      · have hdvd : ringChar L ∣ u (Fin.last d) :=
          (ringChar.spec L (u (Fin.last d))).mp hz'
        have := Nat.le_of_dvd hupos hdvd
        omega
    have hcoeff : (topHasse 1 f).coeff m ≠ 0 := by
      rw [topHasse_coeff, hm, hsum, Nat.choose_one_right]
      exact mul_ne_zero hc (MvPolynomial.mem_support_iff.mp hu)
    intro hz
    exact hcoeff (by rw [hz]; rfl)
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := fun h => hnz (by rw [hg, h, mul_zero])
  have h := MvPolynomial.degreeOf_mul_eq (n := Fin.last d) hf.ne_zero hg0
  rw [hg, h] at hdeg
  omega

/-- Prime-characteristic convenience corollary of `topHasse_one_not_dvd`. -/
theorem topHasse_one_not_dvd_of_charP {L : Type*} [Field L] {p d : ℕ} [CharP L p]
    (f : JetRow L (d + 1)) (hf : Irreducible f)
    (hpos : 0 < f.degreeOf (Fin.last d)) (hsmall : f.degreeOf (Fin.last d) < p) :
    ¬ f ∣ topHasse 1 f := by
  apply topHasse_one_not_dvd f hf hpos
  right
  rwa [ringChar.eq L p]

/-- **Smoothness-Free Proper Cut Extraction (`Final50OrderProof_2` generalized):**
Given irreducible `f : JetRow L (d + 1)` with `0 < deg_{Y_d}(f)` and characteristic guard
`ringChar L = 0 ∨ deg_{Y_d}(f) < ringChar L`, and `P : JetRow L (d + 1)` with `TrueWeightLE physDeg P T`,
`OrderAt P S ord` for all `S ∈ Γ`, `f^a ∣ P`, `¬ f^(a+1) ∣ P`, the polynomial `Q := topHasse a P`
satisfies:
1. `¬ f ∣ Q`,
2. `TrueWeightLE physDeg Q (T - a * (physDeg - d))` (hence `≤ T`),
3. `Q.degreeOf (Fin.last d) ≤ P.degreeOf (Fin.last d) - a`,
4. `∀ S ∈ Γ, OrderAt Q S (ord - a)` (and hence `atJet Q S = 0` whenever `a < ord`!). -/
theorem properCut_of_topHasse {L : Type*} [Field L] {d : ℕ}
    (physDeg T ord a : ℕ) (f P : JetRow L (d + 1))
    (hf : Irreducible f)
    (hpos : 0 < f.degreeOf (Fin.last d))
    (hchar : ringChar L = 0 ∨ f.degreeOf (Fin.last d) < ringChar L)
    (hw : TrueWeightLE physDeg P T)
    (hdiv : f ^ a ∣ P) (hexact : ¬ f ^ (a + 1) ∣ P)
    (Γ : Set (Polynomial L)) (hord : ∀ S ∈ Γ, OrderAt P S ord) :
    ∃ Q : JetRow L (d + 1),
      (¬ f ∣ Q) ∧
      TrueWeightLE physDeg Q (T - a * (physDeg - d)) ∧
      Q.degreeOf (Fin.last d) ≤ P.degreeOf (Fin.last d) - a ∧
      (∀ i, Q.degreeOf i ≤ P.degreeOf i) ∧
      (∀ S ∈ Γ, OrderAt Q S (ord - a)) := by
  refine ⟨topHasse a P, ?_, topHasse_trueWeightLE_sub physDeg T a P hw,
    topHasse_degreeOf_last_le a P, topHasse_degreeOf_le a P,
    fun S hS => topHasse_order a ord P S (hord S hS)⟩
  have hp : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hf
  exact exact_hasse_not_dvd translateTop topHasse_zero f P a hp
    (topHasse_one_not_dvd f hf hpos hchar) hdiv hexact

end

#print axioms topHasse_coeff
#print axioms topHasse_order
#print axioms topHasse_trueWeightLE_sub
#print axioms exact_hasse_not_dvd
#print axioms topHasse_one_not_dvd
#print axioms topHasse_one_not_dvd_of_charP
#print axioms properCut_of_topHasse

end ArkLib.ProximityGap.Frontier.PrimeHDTopHasse
