/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubCeilingLadder
import ArkLib.Data.CodingTheory.ProximityGap.MCASecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.SmoothDomainSelfSimilarity
import ArkLib.Data.CodingTheory.ProximityGap.CensusDominationWeld

/-!
# Generic interpolation spread lifted through a smooth-domain quotient

The KKH26 bad line uses one explicit first row and must prove that many subset sums are
distinct.  For MCA the first row is adversarial, so at a sufficiently large field one can
instead choose it by hyperplane avoidance.  At quotient size `s`, every `r`-subset then gives
a different interpolation scalar for the deep-hole direction `Y^(r-1)`.  Pulling the stack
back along `Y = X^m` replaces every base coordinate by a full `m`-point fiber.

For the exact-rate code of dimension `(r-1)m` on the `sm`-point smooth domain this gives

`epsMCA >= choose(s,r) / p`

at radius `1-r/s`, under only `choose(choose(s,r),2) < p`.  Thus a global `O(n)` bound on
the number of interpolation vertices cannot follow from affine-cluster caps: whenever
`choose(s,r) > sm`, this one stack already has more than the block length many bad scalars.
The `n=8, k=2, r=3` example is the `m=1` boundary case; the quotient lift makes the same
geometry live at excess agreement `m`, including `m = n/Theta(log n)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Finset
open scoped NNReal ENNReal ProbabilityTheory BigOperators
open ProximityGap Code

namespace ArkLib.ProximityGap.Frontier.GenericQuotientInterpolationSpread

open ArkLib.ProximityGap.KKH26
open ProximityGap.Ownership

variable {p s m r : Nat} [Fact p.Prime] [NeZero s] [NeZero m]

/-- Arithmetic degree window for the exact dimension-`(r-1)m` endpoint. -/
theorem genericQuotient_degree_window (hm : 1 ≤ m) (hr2 : 2 ≤ r) :
    (r - 2) * m ≤ (r - 1) * m - 1 ∧
      (r - 1) * m - 1 < (r - 1) * m := by
  have hstep : (r - 2) * m < (r - 1) * m :=
    (Nat.mul_lt_mul_right hm).2 (by omega)
  have hpos : 0 < (r - 1) * m := Nat.mul_pos (by omega) hm
  omega

/-- Raising a generator of order `s*m` to the `m`-th power gives order `s`. -/
theorem orderOf_pow_fiber (hm : 1 <= m) {g : ZMod p} (hg : orderOf g = s * m) :
    orderOf (g ^ m) = s := by
  have hone : (g ^ m) ^ s = 1 := by
    rw [<- pow_mul, Nat.mul_comm m s, <- hg]
    exact pow_orderOf_eq_one g
  have hupper : orderOf (g ^ m) ∣ s := orderOf_dvd_of_pow_eq_one hone
  have hone' : g ^ (m * orderOf (g ^ m)) = 1 := by
    rw [pow_mul]
    exact pow_orderOf_eq_one (g ^ m)
  have hdvd : s * m ∣ m * orderOf (g ^ m) :=
    hg ▸ orderOf_dvd_of_pow_eq_one hone'
  rw [Nat.mul_comm s m] at hdvd
  have hlower : s ∣ orderOf (g ^ m) :=
    (Nat.mul_dvd_mul_iff_left (by omega : 0 < m)).mp hdvd
  exact Nat.dvd_antisymm hupper hlower

/-- A subset of the quotient coordinates pulls back to exactly `m` times as many coordinates. -/
theorem card_filter_proj (hs : 1 <= s) (T : Finset (Fin s)) :
    ((Finset.univ : Finset (Fin (s * m))).filter
      (fun i => Round16SelfSimilar.proj s m (by omega) i ∈ T)).card = m * T.card := by
  classical
  let pi : Fin (s * m) -> Fin s := Round16SelfSimilar.proj s m (by omega)
  let U : Finset (Fin (s * m)) := Finset.univ.filter (fun i => pi i ∈ T)
  have hmaps : ∀ i ∈ U, pi i ∈ T := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  calc
    U.card = ∑ j ∈ T, (U.filter (fun i => pi i = j)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ _j ∈ T, m := by
      apply Finset.sum_congr rfl
      intro j hj
      have hfilter : U.filter (fun i => pi i = j) =
          Finset.univ.filter (fun i => pi i = j) := by
        ext i
        simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro h
          exact ⟨by simpa [h] using hj, h⟩
      rw [hfilter]
      simpa [pi] using Round16SelfSimilar.card_fiber_proj (e := m) (by omega) j
    _ = m * T.card := by simp [Nat.mul_comm]

/-- The `m`-power of a smooth-domain point is its quotient-domain point. -/
theorem pow_m_eq_quotient (hs : 1 <= s) {g : ZMod p} (hg : orderOf g = s * m)
    (i : Fin (s * m)) :
    (g ^ (i : Nat)) ^ m =
      (g ^ m) ^ ((Round16SelfSimilar.proj s m (by omega) i : Fin s) : Nat) := by
  have hpow : g ^ (s * m) = 1 := by
    rw [<- hg]
    exact pow_orderOf_eq_one g
  simpa [Round16SelfSimilar.domN, Round16SelfSimilar.domS] using
    (Round16SelfSimilar.domN_pow_e (F := ZMod p) (e := m) (by omega) hpow i)

/-- Per-subset quotient-lift event.  The first row on the quotient is arbitrary; its
`r`-subset interpolation functional chooses the scalar. -/
theorem mcaEvent_of_quotient_subset
    (hs : 1 <= s) (hm : 1 <= m) (hr2 : 2 <= r) (hr : r <= s)
    {g : ZMod p} (hg : orderOf g = s * m)
    (v : Fin s -> ZMod p) (T : Finset (Fin s)) (hT : T.card = r) :
    mcaEvent (KKH26.evalCode g (s * m) ((r - 1) * m - 1))
      (1 - (r : NNReal) / (s : NNReal))
      (fun i => v (Round16SelfSimilar.proj s m (by omega) i))
      (fun i => (g ^ (i : Nat)) ^ ((r - 1) * m))
      (-ProximityGap.cT (smoothDom (g ^ m) s (orderOf_pow_fiber hm hg)) (r - 1) T v) := by
  classical
  have hsm : 1 <= s * m := Nat.mul_pos hs hm
  have hg0 : g ≠ 0 := by
    rintro rfl
    have hzero : (0 : ZMod p) ^ (s * m) = 1 := by
      rw [<- hg]
      exact pow_orderOf_eq_one 0
    rw [zero_pow (by omega : s * m ≠ 0)] at hzero
    exact zero_ne_one hzero
  have hgmord : orderOf (g ^ m) = s := orderOf_pow_fiber hm hg
  let dom : Fin s ↪ ZMod p := smoothDom (g ^ m) s hgmord
  have hTbase : T.card = (r - 1) + 1 := by omega
  let gamma : ZMod p := -ProximityGap.cT dom (r - 1) T v
  obtain ⟨w, hwcode, hwagree⟩ :=
    (ProximityGap.line_extendable_iff dom hTbase v gamma).2 rfl
  obtain ⟨P, hPdegree, hPeval⟩ := hwcode
  let q : Polynomial (ZMod p) := P.comp (X ^ m)
  have hPnat : P.natDegree < r - 1 := by
    by_cases hP0 : P = 0
    · rw [hP0]
      simp
      omega
    · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).2
        (Polynomial.mem_degreeLT.mp hPdegree)
  have hwindow := genericQuotient_degree_window hm hr2
  have hqdegree : q.natDegree <= (r - 1) * m - 1 := by
    calc
      q.natDegree = P.natDegree * m := by
        simp [q, Polynomial.natDegree_comp]
      _ <= (r - 2) * m := Nat.mul_le_mul_right m (by omega)
      _ <= (r - 1) * m - 1 := hwindow.1
  let S : Finset (Fin (s * m)) := Finset.univ.filter
    (fun i => Round16SelfSimilar.proj s m (by omega) i ∈ T)
  have hScard : S.card = m * r := by
    simpa [S, hT] using (card_filter_proj (m := m) hs T)
  have hqmem : (fun i : Fin (s * m) => q.eval (g ^ (i : Nat))) ∈
      KKH26.evalCode g (s * m) ((r - 1) * m - 1) := by
    rw [ProximityGap.Ownership.evalCode_eq_rsCode hg]
    refine ⟨q, ?_, rfl⟩
    by_cases hq0 : q = 0
    · rw [hq0, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · apply (Polynomial.natDegree_lt_iff_degree_lt hq0).mp
      omega
  refine ⟨S, ?_, ⟨fun i => q.eval (g ^ (i : Nat)), hqmem, ?_⟩, ?_⟩
  · have hrs : (r : NNReal) / (s : NNReal) <= 1 := by
      rw [div_le_one (by positivity)]
      exact_mod_cast hr
    have hcardF : (Fintype.card (Fin (s * m)) : NNReal) = ((s * m : Nat) : NNReal) := by
      rw [Fintype.card_fin]
    have h1delta : (1 : NNReal) - (1 - (r : NNReal) / (s : NNReal)) =
        (r : NNReal) / (s : NNReal) := tsub_tsub_cancel_of_le hrs
    rw [hScard, hcardF, h1delta]
    have harith : ((r : NNReal) / (s : NNReal)) * ((s * m : Nat) : NNReal) =
        ((m * r : Nat) : NNReal) := by
      push_cast
      rw [div_mul_eq_mul_div, mul_comm (r : NNReal) _, mul_comm (s : NNReal) _,
        mul_assoc, mul_div_assoc,
        mul_div_cancel_left₀ _ (by positivity : (s : NNReal) ≠ 0)]
    rw [harith]
  · intro i hi
    have hiproj : Round16SelfSimilar.proj s m (by omega) i ∈ T :=
      (Finset.mem_filter.mp hi).2
    have hbase := hwagree (Round16SelfSimilar.proj s m (by omega) i) hiproj
    have hpow := pow_m_eq_quotient hs hg i
    have hqeval : q.eval (g ^ (i : Nat)) =
        P.eval ((g ^ m) ^ ((Round16SelfSimilar.proj s m (by omega) i : Fin s) : Nat)) := by
      simp [q, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X, hpow]
    have hwval : w (Round16SelfSimilar.proj s m (by omega) i) =
        P.eval ((g ^ m) ^ ((Round16SelfSimilar.proj s m (by omega) i : Fin s) : Nat)) := by
      rw [<- hPeval]
      rfl
    change q.eval (g ^ (i : Nat)) =
      v (Round16SelfSimilar.proj s m (by omega) i) +
        gamma • (g ^ (i : Nat)) ^ ((r - 1) * m)
    rw [hqeval, <- hwval, hbase]
    simp only [gamma, ProximityGap.deepHole, smul_eq_mul]
    change v (Round16SelfSimilar.proj s m (by omega) i) +
        (-ProximityGap.cT dom (r - 1) T v) *
          ((g ^ m) ^ ((Round16SelfSimilar.proj s m (by omega) i : Fin s) : Nat)) ^ (r - 1) =
      v (Round16SelfSimilar.proj s m (by omega) i) +
        (-ProximityGap.cT dom (r - 1) T v) * (g ^ (i : Nat)) ^ ((r - 1) * m)
    congr 2
    calc
      ((g ^ m) ^ ((Round16SelfSimilar.proj s m (by omega) i : Fin s) : Nat)) ^ (r - 1) =
          ((g ^ (i : Nat)) ^ m) ^ (r - 1) := by rw [hpow]
      _ = (g ^ (i : Nat)) ^ (m * (r - 1)) := by rw [pow_mul]
      _ = (g ^ (i : Nat)) ^ ((r - 1) * m) :=
        congrArg (fun e : Nat => (g ^ (i : Nat)) ^ e) (Nat.mul_comm m (r - 1))
  · rintro ⟨_v0, _hv0, v1, hv1, hpair⟩
    have hv1rs := hv1
    rw [ProximityGap.Ownership.evalCode_eq_rsCode hg] at hv1rs
    obtain ⟨q1, hq1degree, hq1eval⟩ := hv1rs
    have hq1nat : q1.natDegree <= (r - 1) * m - 1 := by
      by_cases hq10 : q1 = 0
      · rw [hq10]
        simp
      · have hlt : q1.natDegree < ((r - 1) * m - 1) + 1 :=
          (Polynomial.natDegree_lt_iff_degree_lt hq10).2 hq1degree
        omega
    let SH : Finset (ZMod p) := S.image
      (fun i : Fin (s * m) => g ^ (i : Nat))
    have hSHsub : SH <= (Finset.range (s * m)).image (fun i => g ^ i) := by
      intro x hx
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨(i : Nat), Finset.mem_range.mpr i.isLt, rfl⟩
    have hSHcard : r * m <= SH.card := by
      have himage : SH.card = S.card := by
        apply Finset.card_image_of_injOn
        intro i _ j _ hij
        apply (smoothDom g (s * m) hg).injective
        simpa [smoothDom] using hij
      rw [himage, hScard, Nat.mul_comm]
    refine subceiling_ca_failure hm hwindow.2 SH hSHsub hSHcard q1 hq1nat ?_
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have h1 : v1 i = (g ^ (i : Nat)) ^ ((r - 1) * m) := (hpair i hi).2
    have h2 : v1 i = q1.eval (g ^ (i : Nat)) := congrFun hq1eval i
    rw [<- h2, h1]

open Classical in
/-- Any quotient subset family contributes the cardinality of its interpolation-scalar image
to the bad-scalar count upstairs.  This is the count-preserving core used by both the sharp
hyperplane-avoidance theorem and the second-moment theorem below. -/
theorem quotientFamily_epsMCA_lower_bound
    (hs : 1 <= s) (hm : 1 <= m) (hr2 : 2 <= r) (hr : r <= s)
    {g : ZMod p} (hg : orderOf g = s * m)
    (v : Fin s -> ZMod p) (Fam : Finset (Finset (Fin s)))
    (hcard : ∀ T ∈ Fam, T.card = r) :
    (((Fam.image (fun T =>
          -ProximityGap.cT (smoothDom (g ^ m) s (orderOf_pow_fiber hm hg)) (r - 1) T v)).card :
        Nat) : ENNReal) / (p : ENNReal) <=
      epsMCA (F := ZMod p) (KKH26.evalCode g (s * m) ((r - 1) * m - 1))
        (1 - (r : NNReal) / (s : NNReal)) := by
  let dom : Fin s ↪ ZMod p := smoothDom (g ^ m) s (orderOf_pow_fiber hm hg)
  let Lambda : Finset (ZMod p) := Fam.image
    (fun T => -ProximityGap.cT dom (r - 1) T v)
  have hbad : ∀ gamma ∈ Lambda,
      mcaEvent (KKH26.evalCode g (s * m) ((r - 1) * m - 1))
        (1 - (r : NNReal) / (s : NNReal))
        ((![fun i => v (Round16SelfSimilar.proj s m (by omega) i),
            fun i => (g ^ (i : Nat)) ^ ((r - 1) * m)] :
          WordStack (ZMod p) (Fin 2) (Fin (s * m))) 0)
        ((![fun i => v (Round16SelfSimilar.proj s m (by omega) i),
            fun i => (g ^ (i : Nat)) ^ ((r - 1) * m)] :
          WordStack (ZMod p) (Fin 2) (Fin (s * m))) 1) gamma := by
    intro gamma hgamma
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hgamma
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, dom] using
      mcaEvent_of_quotient_subset hs hm hr2 hr hg v T (hcard T hT)
  have hengine := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (F := ZMod p) (KKH26.evalCode g (s * m) ((r - 1) * m - 1))
    (1 - (r : NNReal) / (s : NNReal))
    (![fun i => v (Round16SelfSimilar.proj s m (by omega) i),
        fun i => (g ^ (i : Nat)) ^ ((r - 1) * m)] :
      WordStack (ZMod p) (Fin 2) (Fin (s * m))) Lambda hbad
  rw [ZMod.card] at hengine
  simpa only [Lambda, dom] using hengine

open Classical in
/-- **Generic quotient interpolation spread.**  Hyperplane avoidance on the quotient makes all
`r`-subset interpolation scalars distinct; the smooth quotient lift turns each into an
`rm`-point witness for the exact dimension-`(r-1)m` code. -/
theorem genericQuotient_epsMCA_lower_bound
    (hs : 1 <= s) (hm : 1 <= m) (hr2 : 2 <= r) (hr : r <= s)
    {g : ZMod p} (hg : orderOf g = s * m)
    (hp : (Nat.choose s r).choose 2 < p) :
    ((Nat.choose s r : Nat) : ENNReal) / (p : ENNReal) <=
      epsMCA (F := ZMod p) (KKH26.evalCode g (s * m) ((r - 1) * m - 1))
        (1 - (r : NNReal) / (s : NNReal)) := by
  have hgmord : orderOf (g ^ m) = s := orderOf_pow_fiber hm hg
  let dom : Fin s ↪ ZMod p := smoothDom (g ^ m) s hgmord
  have hbase : (r - 1) + 1 <= Fintype.card (Fin s) := by
    rw [Fintype.card_fin]
    omega
  have hp' : (Nat.choose (Fintype.card (Fin s)) ((r - 1) + 1)).choose 2 <
      Fintype.card (ZMod p) := by
    simpa [Fintype.card_fin, ZMod.card, show (r - 1) + 1 = r by omega] using hp
  obtain ⟨v, hv⟩ := ProximityGap.exists_u0_injOn_cT dom hbase hp'
  let Fam : Finset (Finset (Fin s)) := Finset.univ.powersetCard r
  have hinj : Set.InjOn (fun T => -ProximityGap.cT dom (r - 1) T v) Fam := by
    intro T hT T' hT' heq
    apply hv T (by simpa [Fam, show (r - 1) + 1 = r by omega] using hT)
      T' (by simpa [Fam, show (r - 1) + 1 = r by omega] using hT')
    exact neg_injective heq
  have hcard : ∀ T ∈ Fam, T.card = r := by
    intro T hT
    exact (Finset.mem_powersetCard.mp hT).2
  have hbound := quotientFamily_epsMCA_lower_bound hs hm hr2 hr hg v Fam hcard
  change (((Fam.image (fun T => -ProximityGap.cT dom (r - 1) T v)).card : Nat) : ENNReal) /
      (p : ENNReal) ≤ _ at hbound
  rw [Finset.card_image_of_injOn hinj] at hbound
  have hFamCard : Fam.card = Nat.choose s r := by simp [Fam]
  rw [hFamCard] at hbound
  simpa only [dom] using hbound

open Classical in
/-- **Second-moment generic quotient spread.**  For any
`M <= choose(s,r)`, averaging over all quotient first rows leaves at most `M^2/p`
collisions among `M` chosen interpolation functionals.  Lifting that row through `X^m`
therefore gives the same second-moment numerator at the deep exact-rate radius, with no
field-size hypothesis:

`(M - M^2/p)/p <= epsMCA`.

Compared with `TheoremQAssembly.theoremQ_epsMCA_lower`, the quotient family itself is
classical; the strengthening is that MCA permits the entire quotient first row to vary,
so the collision denominator has no extra code-dimension factor. -/
theorem genericQuotient_epsMCA_lower_bound_secondMoment
    (hs : 1 <= s) (hm : 1 <= m) (hr2 : 2 <= r) (hr : r <= s)
    {g : ZMod p} (hg : orderOf g = s * m) (M : Nat)
    (hM : M <= Nat.choose s r) :
    (((M : ENNReal) - (M * M : ENNReal) / (p : ENNReal)) / (p : ENNReal)) <=
      epsMCA (F := ZMod p) (KKH26.evalCode g (s * m) ((r - 1) * m - 1))
        (1 - (r : NNReal) / (s : NNReal)) := by
  let dom : Fin s ↪ ZMod p := smoothDom (g ^ m) s (orderOf_pow_fiber hm hg)
  let All : Finset (Finset (Fin s)) := Finset.univ.powersetCard r
  have hAllCard : All.card = Nat.choose s r := by
    simp [All]
  have hMAll : M <= All.card := by rwa [hAllCard]
  obtain ⟨Fam, hFamSub, hFamCard⟩ := Finset.exists_subset_card_eq hMAll
  have hFamWindow : ∀ T ∈ Fam, T.card = (r - 1) + 1 := by
    intro T hT
    have hTr : T.card = r := (Finset.mem_powersetCard.mp (hFamSub hT)).2
    omega
  obtain ⟨v, hv⟩ := ProximityGap.exists_u0_small_collisions dom hFamWindow
  set c : Nat := ProximityGap.collCount dom (r - 1) Fam v with hc
  let Lambda : Finset (ZMod p) := Fam.image
    (fun T => -ProximityGap.cT dom (r - 1) T v)
  have hImage : Fam.card - c <=
      (Fam.image (fun T => ProximityGap.cT dom (r - 1) T v)).card := by
    simpa only [c, ProximityGap.collCount] using
      (ProximityGap.card_image_ge_card_sub_offDiag_collisions Fam
        (fun T => ProximityGap.cT dom (r - 1) T v))
  have hNegCard : Lambda.card =
      (Fam.image (fun T => ProximityGap.cT dom (r - 1) T v)).card := by
    change (Fam.image (fun T => -ProximityGap.cT dom (r - 1) T v)).card = _
    rw [show (fun T => -ProximityGap.cT dom (r - 1) T v) =
        (fun x : ZMod p => -x) ∘ (fun T => ProximityGap.cT dom (r - 1) T v) from rfl,
      <- Finset.image_image]
    exact Finset.card_image_of_injective _ neg_injective
  have hMC : M - c <= Lambda.card := by
    rw [hFamCard, <- hNegCard] at hImage
    exact hImage
  have hMle : M <= Lambda.card + c := by omega
  have hOff : Fam.offDiag.card = M * M - M := by
    rw [Finset.offDiag_card, hFamCard]
  have hpc : p * c <= M * M := by
    have hv' : p * c <= Fam.offDiag.card := by
      simpa [ZMod.card] using hv
    rw [hOff] at hv'
    omega
  have hcard : ∀ T ∈ Fam, T.card = r := by
    intro T hT
    have := hFamWindow T hT
    omega
  have hLift := quotientFamily_epsMCA_lower_bound hs hm hr2 hr hg v Fam hcard
  have hLift' : (Lambda.card : ENNReal) / (p : ENNReal) <=
      epsMCA (F := ZMod p) (KKH26.evalCode g (s * m) ((r - 1) * m - 1))
        (1 - (r : NNReal) / (s : NNReal)) := by
    simpa only [Lambda, dom] using hLift
  set q : ENNReal := (p : ENNReal) with hq
  have hpPos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hqne : q ≠ 0 := by simp [hq, hpPos.ne']
  have hqtop : q ≠ ⊤ := by simp [hq]
  have hcDiv : (c : ENNReal) <= (M * M : ENNReal) / q := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hqne) (Or.inl hqtop)]
    calc
      (c : ENNReal) * q = q * (c : ENNReal) := mul_comm _ _
      _ = ((p * c : Nat) : ENNReal) := by rw [hq]; push_cast; ring
      _ <= ((M * M : Nat) : ENNReal) := by exact_mod_cast hpc
      _ = (M * M : ENNReal) := by push_cast; ring
  have hMbound : (M : ENNReal) <=
      (Lambda.card : ENNReal) + (M * M : ENNReal) / q := by
    calc
      (M : ENNReal) <= ((Lambda.card + c : Nat) : ENNReal) := by exact_mod_cast hMle
      _ = (Lambda.card : ENNReal) + (c : ENNReal) := by push_cast; ring
      _ <= (Lambda.card : ENNReal) + (M * M : ENNReal) / q := by gcongr
  have hSub : (M : ENNReal) - (M * M : ENNReal) / q <= (Lambda.card : ENNReal) := by
    rw [tsub_le_iff_right]
    exact hMbound
  calc
    ((M : ENNReal) - (M * M : ENNReal) / (p : ENNReal)) / (p : ENNReal)
        = ((M : ENNReal) - (M * M : ENNReal) / q) / q := by rw [hq]
    _ <= (Lambda.card : ENNReal) / q := ENNReal.div_le_div_right hSub q
    _ = (Lambda.card : ENNReal) / (p : ENNReal) := by rw [hq]
    _ <= _ := hLift'

/-- The lifted evaluation code is exactly the smooth-domain Reed--Solomon code of dimension
`(r-1)m`; the construction does not hide the former KKH degree/dimension mismatch. -/
theorem genericQuotient_evalCode_eq_rsCode
    (hm : 1 <= m) (hr2 : 2 <= r) {g : ZMod p} (hg : orderOf g = s * m) :
    KKH26.evalCode g (s * m) ((r - 1) * m - 1) =
      ((ProximityGap.SpikeFloor.rsCode
          (smoothDom g (s * m) hg) ((r - 1) * m) :
          Submodule (ZMod p) (Fin (s * m) -> ZMod p)) : Set (Fin (s * m) -> ZMod p)) := by
  have hpos : 0 < (r - 1) * m := Nat.mul_pos (by omega) hm
  have hdim : (r - 1) * m - 1 + 1 = (r - 1) * m := by omega
  simpa only [hdim] using
    ProximityGap.Ownership.evalCode_eq_rsCode hg ((r - 1) * m - 1)

/-- Operational `deltaStar` ceiling from the collision-free quotient spread. -/
theorem genericQuotient_mcaDeltaStar_le
    (hs : 1 <= s) (hm : 1 <= m) (hr2 : 2 <= r) (hr : r <= s)
    {g : ZMod p} (hg : orderOf g = s * m)
    (hp : (Nat.choose s r).choose 2 < p) (epsStar : ENNReal)
    (hEps : epsStar < (Nat.choose s r : ENNReal) / (p : ENNReal)) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
        (KKH26.evalCode g (s * m) ((r - 1) * m - 1)) epsStar <=
      1 - (r : NNReal) / (s : NNReal) :=
  ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hEps
      (genericQuotient_epsMCA_lower_bound hs hm hr2 hr hg hp))

/-- Operational ceiling from the stronger second-moment quotient spread. -/
theorem genericQuotient_mcaDeltaStar_le_secondMoment
    (hs : 1 <= s) (hm : 1 <= m) (hr2 : 2 <= r) (hr : r <= s)
    {g : ZMod p} (hg : orderOf g = s * m) (M : Nat)
    (hM : M <= Nat.choose s r) (epsStar : ENNReal)
    (hEps : epsStar <
      ((M : ENNReal) - (M * M : ENNReal) / (p : ENNReal)) / (p : ENNReal)) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
        (KKH26.evalCode g (s * m) ((r - 1) * m - 1)) epsStar <=
      1 - (r : NNReal) / (s : NNReal) :=
  ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hEps
      (genericQuotient_epsMCA_lower_bound_secondMoment hs hm hr2 hr hg M hM))

end ArkLib.ProximityGap.Frontier.GenericQuotientInterpolationSpread

#print axioms ArkLib.ProximityGap.Frontier.GenericQuotientInterpolationSpread.card_filter_proj
#print axioms ArkLib.ProximityGap.Frontier.GenericQuotientInterpolationSpread.mcaEvent_of_quotient_subset
#print axioms ArkLib.ProximityGap.Frontier.GenericQuotientInterpolationSpread.genericQuotient_epsMCA_lower_bound
#print axioms ArkLib.ProximityGap.Frontier.GenericQuotientInterpolationSpread.genericQuotient_epsMCA_lower_bound_secondMoment
#print axioms ArkLib.ProximityGap.Frontier.GenericQuotientInterpolationSpread.genericQuotient_mcaDeltaStar_le_secondMoment
