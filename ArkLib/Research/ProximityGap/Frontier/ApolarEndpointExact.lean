/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarBorderCoordinates
import ArkLib.Research.ProximityGap.Frontier.ApolarBorderDescent
import ArkLib.Research.ProximityGap.Frontier.ApolarCoefficientSpan
import ArkLib.Research.ProximityGap.Frontier.ApolarPowerOptimal

/-! # The sharp scalar count at the divisible unique-decoding endpoint -/

set_option autoImplicit false
open Finset Polynomial Code ProximityGap Classical
open ProximityGap.ApolarDividedLocator ProximityGap.ApolarDividedPolynomial ProximityGap.ApolarParameterTransition
open ProximityGap.ApolarSyndromeInterpolation ProximityGap.ApolarChartDescent ProximityGap.ApolarUnitChartData
open ProximityGap.ApolarInverseCoordinates ProximityGap.ApolarUnitChartSpecialization ProximityGap.ApolarCubicObstruction
open ArkLib.ProximityGap.Frontier.ApolarReciprocalCharts ArkLib.ProximityGap.Frontier.ApolarFixedTarget
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.ApolarEndpointExact

variable {K : Type*} [Field K]

private theorem nodal_congr {J : Type*} (G : Finset J) (a b : J → K[X])
    (h : ∀ t ∈ G, a t = b t) : Lagrange.nodal G a = Lagrange.nodal G b := by
  apply Finset.prod_congr rfl
  intro t ht
  rw [h t ht]

private theorem count_remainders (power : ℕ) [IsAlgClosed K] [DecidableEq K]
    (D G : Finset K) (w : K → K[X]) (f : K[X][X]) (V : K[X]) {l j : ℕ}
    (h0G : 0 ∉ G) (hV : V ≠ 0) (hw : ∀ i ∈ D, (w i).natDegree ≤ 1)
    (hf : ∀ i, (f.coeff i).natDegree ≤ l) (hmov : 0 < (f.coeff j).natDegree)
    (hfree : ∀ t : K, f.map (evalRingHom t) ≠ 0)
    (hc : IsCoprime (f.map (algebraMap K[X] (FractionRing K[X])))
      ((representative D C w f).map (algebraMap K[X] (FractionRing K[X]))))
    (hl : 0 < l) (span : ∀ i ≤ l, ∃ c : Fin (f.natDegree+1) → K,
      ∑ j, C (c j)*f.coeff j.val = Polynomial.X^i)
    (Q Qt B Bt : K[X][X]) (hQt : Qt.natDegree < G.card) (hB : B.natDegree < l) (hBt : Bt.natDegree < l)
    (hb : (Bivariate.swap B).natDegree ≤ f.natDegree)
    (hbt : (Bivariate.swap Bt).natDegree ≤ f.natDegree)
    (hforward : C V * (Bivariate.swap (representative D C w f))^power =
      Bivariate.swap f * Q + Lagrange.nodal G C * B)
    (hback : C V * (Bivariate.swap (representative D C (fun i => reflect 1 (w i))
      (reverseCoeffs l f)))^power =
      Bivariate.swap (reverseCoeffs l f) * Qt +
        Lagrange.nodal (G.image Inv.inv) C * Bt) : G.card ≤ power * (l + 1) + 1 := by
  classical
  by_contra! hmany
  let site (t : K) : K[X]ˣ := Units.map (C : K →+* K[X]).toMonoidHom
    (if h : t = 0 then 1 else Units.mk0 t h)
  have hs (t : K) (ht : t ∈ G) : (site t : K[X]) = C t := by
    have hn : t ≠ 0 := fun he => h0G (he ▸ ht)
    simp [site, hn]
  have hsi (t : K) (ht : t ∈ G) : (↑(site t)⁻¹ : K[X]) = C t⁻¹ := by
    have hn : t ≠ 0 := fun he => h0G (he ▸ ht)
    simp [site, hn]
  have hfwd := hforward
  rw [← nodal_congr G _ _ hs] at hfwd
  rw [nodal_inverse_image, ← nodal_congr G _ _ hsi] at hback
  have hg (i : K) (hi : i ∈ G) : (Bivariate.swap f).eval (site i : K[X]) ≠ 0 := by
    rw [hs i hi, eval_swap]
    exact hfree i
  let a := G.card - power * (l + 1)
  have ha : G.card = power * (l + 1) + a := by dsimp [a]; omega
  have hd := cleared_power_remainders power G site D w f V l (l - 1) a Q Qt B Bt ha hw hf
    (by omega) (by omega) hg hfwd hback
  obtain ⟨hb0, _⟩ := ApolarBorderDescent.vanish_of_cleared f B Bt (∏ i ∈ G, -(site i))⁻¹
    (by dsimp [a]; omega : 2 ≤ a) hb hbt (by omega : B.natDegree ≤ l - 1)
    (by omega : Bt.natDegree ≤ l - 1) (by simpa only [show l-1+1=l by omega] using span) hd
  rw [hb0, mul_zero, add_zero] at hforward
  have he := congrArg Bivariate.swap hforward
  simp only [map_mul, map_pow, Bivariate.swap_C, Bivariate.swap_swap_apply] at he
  exact not_dvd_fixed_mul_pow f (representative D C w f) V hV hfree j hmov hc power ⟨_, he⟩

private theorem count_chart (power : ℕ) (hpower : 0 < power) [IsAlgClosed K] [DecidableEq K] (D G : Finset K)
    (w : K → K[X]) (f : K[X][X]) {r d l : ℕ} (hr : 0 < r) (hrd : r ≤ d) (hl : 0 < l)
    (hdeg : f.natDegree = r) (htop : (f.coeff r).natDegree = l) (hz : f.coeff 0 ≠ 0)
    (hf : ∀ j, (f.coeff j).natDegree ≤ l) (hprim : ∀ t : K, f.map (evalRingHom t) ≠ 0)
    (hw : ∀ i ∈ D, (w i).natDegree ≤ 1) (hD : 0 ∉ D) (hG : 0 ∉ G) (hne : G.Nonempty)
    (span : ∀ i ≤ l, ∃ c : Fin (f.natDegree+1) → K,
      ∑ j, C (c j)*f.coeff j.val = Polynomial.X^i)
    (htwist : D.card ≤ power * (d + 2 - r) + r)
    (ha : ApolarThrough (ApolarRootTransition.measure D C w) f (d - r))
    (hc : IsCoprime (f.map (algebraMap K[X] (FractionRing K[X])))
      ((representative D C w f).map (algebraMap K[X] (FractionRing K[X]))))
    (hsp : ∀ t ∈ G, ∃ E ⊆ D, E.card ≤ d - r + 1 ∧ ∃ v : K → K, ∀ p : K[X],
      p.natDegree ≤ d → weighted D (RingHom.id K) (fun i => (w i).eval t) p =
        weighted E (RingHom.id K) v p) :
    G.card ≤ power * (l + 1) + 1 := by
  classical
  by_contra! hmany
  have htop0 : f.coeff r ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at htop
    omega
  let V := Lagrange.nodal D id
  have hV : V.natDegree ≤ D.card := Lagrange.natDegree_nodal.le
  have htw : D.card ≤ power * (d - r + 2) + r := by rwa [show d-r+2=d+2-r by omega]
  have hrs : r + (d - r) = d := by omega
  have hpdeg := parameter_degree f hf htop htop0
  obtain ⟨Q, B, _, hB, hb, hforward⟩ := ApolarBorderCoordinates.small_interpolation_weak power hpower D G w f V
    hD hne hl hr hdeg hpdeg (dvd_refl V) hV htw hw hf hz hprim (by omega) ha
    (by simpa only [hrs] using hsp)
  let Gt := G.image Inv.inv
  let ft := reverseCoeffs l f
  let wt := fun i => reflect 1 (w i)
  have hgcard : Gt.card = G.card := card_image_of_injective _ inv_injective
  have hft (j : ℕ) : (ft.coeff j).natDegree ≤ l :=
    natDegree_reflect_le.trans (max_le le_rfl (hf j))
  have hwt (i : K) (hi : i ∈ D) : (wt i).natDegree ≤ 1 :=
    natDegree_reflect_le.trans (max_le le_rfl (hw i hi))
  have hf0 : ft.coeff 0 ≠ 0 := by
    intro h
    have hu := congrArg (reflect l) h
    apply hz
    simpa only [ft, coeff_reverseCoeffs, reflect_reflect, reflect_zero] using hu
  have htprim := reverse_fibers_nonzero f l hf ⟨r, htop, htop0⟩ hprim
  have hrev := reciprocal_sparse_family D G w d (d - r + 1) hG hw hsp
  obtain ⟨Qt, Bt, hQt, hBt, hbt, hback⟩ := ApolarBorderCoordinates.small_interpolation_weak power hpower D Gt wt ft V
    hD (hne.image _) hl hr ((reverse_coordinate_degree f l).trans hdeg)
    (reverse_parameter_degree f l hf (hprim 0)) (dvd_refl V) hV htw hwt hft hf0 htprim
    (by omega) (apolar_parameter_reverse D w f l (d - r) hw hf ha)
    (by simpa only [hrs] using hrev)
  rw [hgcard] at hQt
  exact hmany.not_ge (count_remainders power D G w f V hG Lagrange.nodal_ne_zero hw hf
    (htop ▸ hl) hprim hc hl span Q Qt B Bt hQt hB hBt (hdeg.symm ▸ hb) (hdeg.symm ▸ hbt) hforward hback)

private theorem coprime_data {K : Type*} [Field K] [DecidableEq K] {H S : Finset K}
    {e d r l : ℕ} (A : Data H S e d r l) (hr : 0<r) (hd : r≤d) :
    let φ := algebraMap K[X] (FractionRing K[X])
    IsCoprime (A.f.map φ) ((representative A.D C A.w A.f).map φ) := by
  have hr1 : r-1+1=r := by omega
  have ha : A.f.natDegree=r-1+1 := A.degree.trans hr1.symm
  apply ApolarGenericCoprime.generic_coprime A.D (C : K → K[X]) A.w A.f (r-1) (d-r) ha A.apolar
  simpa only [show d-r+1=d-(r-1) by omega] using A.minimal (r-1) (by omega)

/-- Weak coordinate descent and the complete coefficient span give one extra
bad scalar beyond the preceding full-fiber multiple. -/
private theorem family_of_span {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] [DecidableEq (AlgebraicClosure F)]
    {dom : ι ↪ F} {k e n : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}
    (fam : BadScalarRichPointFamily dom k δ u) (hn : Fintype.card ι=n)
    (hshape : n=k+2*e) (hk : 0<k) (he : 0<e) (hdiv : e+1 ∣ n+1)
    (hag : n-e ≤ ⌈(1-δ)*(Fintype.card ι:ℝ≥0)⌉₊)
    (hspan : ∀ {H S : Finset (AlgebraicClosure F)} {r l : ℕ}
      (A : Data H S e (2*e-1) r l), 0<r → 0<l → r≤e →
      ∀ i ≤ l, ∃ c : Fin (r+1) → AlgebraicClosure F,
        ∑ j, C (c j)*A.f.coeff j.val = Polynomial.X^i) :
    fam.G.card ≤ n-e+1 := by
  classical
  obtain ⟨b,hb⟩ := hdiv
  have hbeq : b*(e+1)=n+1 := (Nat.mul_comm ..).trans hb.symm
  have hb₂ : 2≤b := by
    by_contra! hh
    have := Nat.mul_le_mul_right (e+1) (show b≤1 by omega)
    rw [one_mul,hbeq] at this
    omega
  let power := b-1
  have hpower : 0<power := by dsimp [power]; omega
  have hpow : power*(e+1)+e=n := by
    have h : b=power+1 := by dsimp [power]; omega
    rw [h,Nat.add_mul,one_mul] at hbeq
    omega
  by_cases hs : fam.G.card ≤ e+1
  · omega
  let d := 2*e-1
  obtain ⟨r,hre,l,hr,hl,hdeg,⟨A⟩⟩ := of_mca_family (algebraMap F (AlgebraicClosure F))
    (e:=e) (d:=d) fam fam.G Subset.rfl (by omega) (by dsimp [d]; omega) (by dsimp [d]; omega) hk
    (by dsimp [d]; omega) (by simpa only [hn] using hag)
  have hd : r≤d := by dsimp [d]; omega
  have hsites : A.D.card=n := by rw [A.card_sites];simpa using hn
  have hG : A.G.card=fam.G.card := by rw [A.card_parameters];simp
  have hspan' : ∀ i ≤ l, ∃ c : Fin (A.f.natDegree+1) → AlgebraicClosure F,
      ∑ j, C (c j)*A.f.coeff j.val = Polynomial.X^i := by
    rw [A.degree]
    exact hspan A hr hl hre
  have hwidth : d+2-r=(e+1)+(e-r) := by dsimp [d]; omega
  have hmul : e-r ≤ power*(e-r) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (e-r) (show 1≤power from hpower)
  have hcoord : A.D.card≤power*(d+2-r)+r := by rw [hsites,hwidth,Nat.mul_add];omega
  have h := count_chart power hpower A.D A.G A.w A.f hr hd hl A.degree A.top_height A.bottom_nonzero
    A.height A.primitive A.weights_affine A.sites_unit A.parameters_unit
    (Finset.card_pos.mp (by omega)) hspan' hcoord A.apolar (coprime_data A hr hd)
    (interpolation_sparse A (by dsimp [d]; omega))
  have hrl : l≤r := by
    have h1 : 1≤d+2-2*r := by dsimp [d];omega
    exact (show l≤(d+2-2*r)*l by simpa only [one_mul] using Nat.mul_le_mul_right l h1).trans hdeg
  have hle := Nat.mul_le_mul_left power (show l+1≤e+1 by omega)
  rw [hG] at h
  omega

/-- Exact arbitrary-domain extremal numerator at the unique radius. -/
def numerator (n e : ℕ) : ℕ :=
  if e+1 ∣ n+1 then n-e+1 else ((n+1)/(e+1))*(e+1)

/-- Every actual scalar family satisfies the sharp upper bound when the
evaluation length plus one is divisible by the exceptional fiber size. -/
theorem family {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {dom : ι ↪ F} {k e n : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}
    (fam : BadScalarRichPointFamily dom k δ u) (hn : Fintype.card ι=n)
    (hshape : n=k+2*e) (hk : 0<k) (he : 0<e) (hdiv : e+1 ∣ n+1)
    (hag : n-e ≤ ⌈(1-δ)*(Fintype.card ι:ℝ≥0)⌉₊) :
    fam.G.card ≤ n-e+1 := by
  classical
  apply family_of_span fam hn hshape hk he hdiv hag
  intro H S r l A hr hl hre
  exact ApolarCoefficientSpan.monomials A hr hl (by omega)

/-- The sharp numerator bounds every pair on every finite-field domain. -/
theorem pair_bound {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] (dom : ι ↪ F) (u v : ι → F) {k e n : ℕ}
    (hn : Fintype.card ι=n) (hshape : n=k+2*e) (hk : 0<k) (he : 0<e) :
    (univ.filter fun t : F => mcaEvent (ReedSolomon.code dom k : Set (ι → F))
      ((e:ℝ≥0)/n) u v t).card ≤ numerator n e := by
  classical
  by_cases hdiv : e+1 ∣ n+1
  · rw [numerator,ite_eq_left hdiv]
    let w : WordStack F (Fin 2) ι := ![u,v]
    let fam := canonicalBadScalarRichPointFamily dom ((e:ℝ≥0)/n) w hk
    apply family fam hn hshape hk he hdiv
    have h := one_sub_div_mul_cast (ι:=ι) e (by omega)
    rw [hn] at h ⊢
    rw [h,Nat.ceil_natCast]
  · rw [numerator,ite_eq_right hdiv]
    exact ApolarPowerOptimal.pair_bound dom u v hn hshape hk he

/-- On every sufficiently large splitting prime field there is one domain
and pair attaining the absolute bound, and the worst-case error probability
on that same domain is exactly this numerator divided by p. -/
theorem prime (k e p : ℕ) [Fact p.Prime] (hk : 0<k) (he : 0<e)
    (hp : k+2*e<p) (hsplit : e+1 ∣ p-1) :
    let n := k+2*e
    let count := numerator n e
    ∃ D : Finset (ZMod p), D.card=n ∧
      let C := (ReedSolomon.code (Function.Embedding.subtype (·∈D)) k : Set (D → ZMod p))
      (∃ u v : D → ZMod p, (univ.filter fun t : ZMod p => mcaEvent C ((e:ℝ≥0)/D.card) u v t).card=count) ∧
      epsMCA (F:=ZMod p) C ((e:ℝ≥0)/D.card)=(count:ℝ≥0∞)/(p:ℝ≥0∞) := by
  classical
  let n := k+2*e
  let count := numerator n e
  by_cases hdiv : e+1 ∣ k+2*e+1
  · obtain ⟨D,hD,u,v,hu⟩ := PowerFiberEndpoint.prime_partial k e p hk he hdiv hp hsplit
    have hcount : count=n-e+1 := ite_eq_left hdiv
    rw [← hcount] at hu
    have hn : Fintype.card D=n := (Fintype.card_coe D).trans hD
    let _ : Nonempty D := Fintype.card_pos_iff.mp (by rw [hn]; dsimp [n]; omega)
    let dom := Function.Embedding.subtype (·∈D)
    let C := (ReedSolomon.code dom k : Set (D → ZMod p))
    have bound (u v : D → ZMod p) :
        (univ.filter fun t : ZMod p => mcaEvent C ((e:ℝ≥0)/D.card) u v t).card≤count := by
      rw [hD]
      exact pair_bound dom u v hn rfl hk he
    refine ⟨D,hD,⟨u,v,(bound u v).antisymm hu⟩,le_antisymm ?_ ?_⟩
    · apply (epsMCA_le_of_badCount_le C _ count ?_).trans (by rw [ZMod.card])
      intro w
      exact bound (w 0) (w 1)
    · rw [epsMCA_eq_iSup_badCount_div,ZMod.card]
      apply ENNReal.div_le_div_right
      let w : WordStack (ZMod p) (Fin 2) D := ![u,v]
      apply LE.le.trans _ (le_iSup _ w)
      exact_mod_cast hu

  · simpa only [numerator,ite_eq_right hdiv] using ApolarPowerOptimal.prime k e p hk he hdiv hp hsplit

/-- The matching extremizers exist over arbitrarily large prime fields. -/
theorem arbitrarily_large (k e bound : ℕ) (hk : 0<k) (he : 0<e) :
    let n := k+2*e
    let count := numerator n e
    ∃ (p : ℕ) (hp : Nat.Prime p), bound<p ∧
      let _ : Fact p.Prime := ⟨hp⟩
      ∃ D : Finset (ZMod p), D.card=n ∧
        let C := (ReedSolomon.code (Function.Embedding.subtype (·∈D)) k : Set (D → ZMod p))
        (∃ u v : D → ZMod p, (univ.filter fun t : ZMod p => mcaEvent C ((e:ℝ≥0)/D.card) u v t).card=count) ∧
        epsMCA (F:=ZMod p) C ((e:ℝ≥0)/D.card)=(count:ℝ≥0∞)/(p:ℝ≥0∞) := by
  obtain ⟨p,hp,hbig,hcong⟩ := Nat.exists_prime_gt_modEq_one (max bound (k+2*e)) (Nat.succ_ne_zero e)
  let _ : Fact p.Prime := ⟨hp⟩
  refine ⟨p,hp,(le_max_left ..).trans_lt hbig,prime k e p hk he ((le_max_right ..).trans_lt hbig) ?_⟩
  exact hcong.symm.dvd'

set_option pp.fullNames true
#print axioms family
#print axioms pair_bound
#print axioms prime
#print axioms arbitrarily_large
end ArkLib.ProximityGap.Frontier.ApolarEndpointExact
