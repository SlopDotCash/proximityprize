/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FineGridFirstOrderSecurity
import ArkLib.Research.ProximityGap.Frontier.BlsScalarSubgroup
import ArkLib.Research.ProximityGap.Frontier.FourRateListPrime246
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.FiniteLengthMca

/-! # Uniform squarefree first-order MCA bounds at the four sponsor rates

Twelve slot choices give three security levels on every prescribed prime-field
domain whose length is a positive multiple of 4096. The strongest radii cover
the BLS12-381 scalar field at length `2^30`.
-/
set_option autoImplicit false
namespace ProximityGap.ScaledSquarefreeSafety
open ReedSolomon ReedSolomon.HiddenDerivative ReedSolomon.FirstOrder
open CoreDefinitions FineGridFirstOrderSecurity

structure Case where
  k : ℕ
  A : ℕ
  m : ℕ
  M : ℕ
  v : ℕ
  h : ℕ
  bits : ℕ
  deriving DecidableEq, Repr

/-- The tiers occupy successive groups of four rows in sponsor-rate order. -/
def cases : Fin 12 → Case
  | 0 => ⟨2048,2830,251,77,346,31113,36⟩
  | 1 => ⟨1024,1925,251,113,471,43219,37⟩
  | 2 => ⟨512,1311,251,138,642,71065,37⟩
  | 3 => ⟨256,897,235,154,822,80393,37⟩
  | 4 => ⟨2048,2827,888,275,1225,392510,44⟩
  | 5 => ⟨1024,1922,635,288,1191,327767,42⟩
  | 6 => ⟨512,1308,950,523,2426,877596,45⟩
  | 7 => ⟨256,895,520,343,1817,400286,41⟩
  | 8 => ⟨2048,2826,5874,1825,8105,17350380,55⟩
  | 9 => ⟨1024,1921,1424,647,2671,1546424,47⟩
  | 10 => ⟨512,1307,7697,4236,19648,75007065,58⟩
  | 11 => ⟨256,894,1331,878,4647,2753034,47⟩

/-- The scale-one upper charge; its lower-order terms are normalized at the reference length. -/
def charge (N k v M h : ℕ) (θ : ℝ) : ℝ :=
  let f := v*(2*M+1)
  let g := h*(2*M+1)
  (2*f-1 : ℕ)*g + θ*(g+f+4*(k:ℝ)*f*g) + (N:ℝ)*f +
    (48*(k:ℝ)^2*h+16*k)*θ^2*v*M + 8*(k:ℝ)*N*θ*v*M

/-- Every term of the canonical envelope scales with degree at most two.
Already at the reference block length, this retains the denominators of
the normalized lower-order terms. -/
private theorem envelope_scaled {b N k A v M h : ℕ} {θ : ℝ}
    (hb : 0 < b) (hk : 0 < k) (hkA : k<A) (hAN : A≤N) (hθ₁ : 1≤θ)
    (hθ : (N-k:ℕ) ≤ θ*(A-k:ℕ)) :
    finiteLengthMcaEnvelope (agreementIncidenceRatio (b*N) (b*k-1) (b*A))
      (b*N) (b*k-1) v M h ≤ (b:ℝ)^2*charge N k v M h θ := by
  let D := b*k-1
  have hD : (D:ℝ) ≤ (b:ℝ)*k := by exact_mod_cast Nat.sub_le (b*k) 1
  have hrest : ((b*N-D-1:ℕ):ℝ) ≤ (b:ℝ)*N := by exact_mod_cast (show b*N-D-1 ≤ b*N by omega)
  have hθ0 : 0 ≤ θ := by linarith
  have hb' : (1:ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0:ℝ) ≤ b := by positivity
  have hRatio : agreementIncidenceRatio (b*N) D (b*A) ≤ θ := by
    have hbk := Nat.mul_pos hb hk
    have ha := Nat.mul_lt_mul_of_pos_left hkA hb
    have hn := Nat.mul_le_mul_left b hAN
    have eN : b*N-D=b*(N-k)+1 := by dsimp [D]; rw [Nat.mul_sub]; omega
    have eA : b*A-D=b*(A-k)+1 := by dsimp [D]; rw [Nat.mul_sub]; omega
    unfold agreementIncidenceRatio
    rw [eN,eA]
    apply (div_le_iff₀ (by positivity)).mpr
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hθ hb0]
  have hR0 : 0 ≤ agreementIncidenceRatio (b*N) D (b*A) := by
    unfold agreementIncidenceRatio
    positivity
  let f := v*(2*M+1)
  let g := h*(2*M+1)
  let a₀ : ℝ := ((2*f-1:ℕ):ℝ)*g+θ*(g+f)
  let a₁ : ℝ := θ*(4*(k:ℝ)*f*g)+N*f+16*(k:ℝ)*θ^2*v*M
  let a₂ : ℝ := 48*(k:ℝ)^2*h*θ^2*v*M+8*(k:ℝ)*N*θ*v*M
  change finiteLengthMcaEnvelope _ _ D _ _ _ ≤ _
  calc _ ≤ ((2*f-1:ℕ):ℝ)*g+θ*(g+f+4*((b:ℝ)*k)*f*g)+((b:ℝ)*N)*f+
          (48*((b:ℝ)*k)^2*h+16*((b:ℝ)*k))*θ^2*v*M+
          8*((b:ℝ)*k)*((b:ℝ)*N)*θ*v*M := by
            simp only [finiteLengthMcaEnvelope]
            change ((2*f-1:ℕ):ℝ)*g+agreementIncidenceRatio (b*N) D (b*A)*(g+f+4*(D:ℝ)*f*g)+
                ((b*N-D-1:ℕ):ℝ)*f+(48*(D:ℝ)^2*h+16*D)*(agreementIncidenceRatio (b*N) D (b*A))^2*v*M+
                8*(D:ℝ)*((b*N-D-1:ℕ):ℝ)*agreementIncidenceRatio (b*N) D (b*A)*v*M ≤ _
            gcongr
      _ = a₀+b*a₁+(b:ℝ)^2*a₂ := by dsimp [a₀,a₁,a₂]; ring
      _ ≤ (b:ℝ)^2*(a₀+a₁+a₂) := by
        have h0 : 0≤a₀ := by dsimp [a₀]; positivity
        have h1 : 0≤a₁ := by dsimp [a₁]; positivity
        have hb2 : (b:ℝ) ≤ (b:ℝ)^2 := by nlinarith
        nlinarith only [mul_le_mul_of_nonneg_right (hb'.trans hb2) h0,
          mul_le_mul_of_nonneg_right hb2 h1]
      _ = _ := by dsimp [a₀,a₁,a₂,charge,f,g]; ring

private theorem column_compact (k A m M v h : ℕ) :
    columnSlots k A m M v h = ∑ t∈Finset.range (v+1),
      (min t M+1)*((m*A-k*t)*(h+1-t)) := by
  rfl

private def sumBelow (f : ℕ → ℕ) (start n : ℕ) : ℕ → ℕ
  | 0 => if n=0 then 0 else f start
  | d+1 => if n=0 then 0 else sumBelow f start (n/2) d + sumBelow f (start+n/2) (n-n/2) d

private theorem sumBelow_eq (f : ℕ → ℕ) (d start n : ℕ) (h : n ≤ 2^d) :
    sumBelow f start n d = ∑ i∈Finset.range n, f (start+i) := by
  induction d generalizing start n with
  | zero =>
    norm_num at h
    interval_cases n <;> simp [sumBelow]
  | succ d ih =>
    by_cases hn : n=0
    · simp [hn,sumBelow]
    · rw [sumBelow,ite_eq_right hn,ih,ih]
      · conv_rhs => rw [← Nat.add_sub_of_le (Nat.div_le_self n 2),Finset.sum_range_add]
        simp only [Nat.add_assoc]
      · rw [pow_succ] at h
        omega
      · rw [pow_succ] at h
        omega

private theorem reduce_sum (f : ℕ → ℕ) (n : ℕ) (h : n ≤ 2^15) :
    ∑ i∈Finset.range n, f i = sumBelow f 0 n 15 := by simp [sumBelow_eq f 15 0 n h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private theorem slots (i : Fin 12) : let c := cases i
    rowSlots 4096 c.m c.M c.v c.h < columnSlots c.k c.A c.m c.M c.v c.h := by
  fin_cases i <;> simp only [cases,rowSlots,column_compact] <;>
    rw [reduce_sum _ _ (by decide),reduce_sum _ _ (by decide)] <;> decide

private theorem charges (i : Fin 12) : let c := cases i
    charge 4096 c.k c.v c.M c.h (((4096-c.k:ℕ):ℝ)/(c.A-c.k:ℕ)) ≤ (2:ℝ)^c.bits*4096^2 := by
  fin_cases i <;> norm_num [charge,cases]

/-- The quantitative line error bound holds at any code rate, reference
length and target tolerance whenever the selected slot and charge inequalities
hold. The finite field is arbitrary subject to the recovery characteristic. -/
theorem error_of_squarefree_slots {F : Type} [Field F] [Fintype F] [SampleableType F]
    {b N₀ : ℕ} (hb : 0<b) (c : Case)
    (hd : 2≤c.k ∧ c.k<c.A ∧ c.A≤N₀ ∧ 1≤c.M ∧ c.M≤c.v)
    (hchar : ringChar F=0 ∨ max (b*c.k-1) c.M < ringChar F)
    (hslots : rowSlots N₀ c.m c.M c.v c.h < columnSlots c.k c.A c.m c.M c.v c.h)
    (hcharge : charge N₀ c.k c.v c.M c.h (((N₀-c.k:ℕ):ℝ)/(c.A-c.k:ℕ)) ≤
      (2:ℝ)^c.bits*(N₀:ℝ)^2)
    (dom : Fin (b*N₀) ↪ F) {r : ℝ} (hr : r ≤ 1-(c.A:ℝ)/N₀) :
    mcaError (AffineLineGenerator F) (code dom (b*c.k)) r ≤
      ENNReal.ofReal ((2:ℝ)^c.bits*((b*N₀:ℕ):ℝ)^2/Fintype.card F) := by
  classical
  have hbk : 2≤b*c.k := hd.1.trans (Nat.le_mul_of_pos_left _ hb)
  have hbA := Nat.mul_lt_mul_of_pos_left hd.2.1 hb
  have hn := Nat.mul_le_mul_left b hd.2.2.1
  have hlen : 2≤N₀ := hd.1.trans (hd.2.1.le.trans hd.2.2.1)
  have hNpos : (0:ℝ)<N₀ := by exact_mod_cast (show 0<N₀ by omega)
  let θ : ℝ := ((N₀-c.k:ℕ):ℝ)/(c.A-c.k:ℕ)
  have θprop : 1≤θ ∧ ((N₀-c.k:ℕ):ℝ) ≤ θ*(c.A-c.k:ℕ) := by
    have ha : (0:ℝ)<(c.A-c.k:ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hd.2.1
    exact ⟨(one_le_div ha).mpr (by exact_mod_cast Nat.sub_le_sub_right hd.2.2.1 c.k),
      (div_mul_cancel₀ _ ha.ne').ge⟩
  let N := b*N₀
  let K : ℝ := (2:ℝ)^c.bits * (N:ℝ)^2
  have hline : LineExactAgreementBound dom (b*c.k) (b*c.A) K := by
    apply lineExactAgreementBound_of_exactCorrelatedPair
    intro f g
    have hsucc : b*c.k-1+1=b*c.k := by omega
    obtain ⟨cert⟩ := exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
      (k:=b*c.k) (by omega : 0<b*c.k-1) hsucc.ge dom f g (scaled_slots hb hslots)
    obtain ⟨E,he,hg⟩ := Squarefree.exists_baseExceptional_retainedSquarefreeLineAgreement_of_certificate
      dom f g _ cert hbk hbA.le hn hd.2.2.2.1 hd.2.2.2.2 hchar
    rw [Squarefree.retainedSquarefreeLineAgreementEnvelope_eq_finiteLengthMcaEnvelope] at he
    refine ⟨E,he.trans ((envelope_scaled hb (by omega : 0<c.k) hd.2.1 hd.2.2.1 θprop.1 θprop.2).trans ?_),hg⟩
    calc _ ≤ (b:ℝ)^2*((2:ℝ)^c.bits*(N₀:ℝ)^2) :=
           mul_le_mul_of_nonneg_left hcharge (sq_nonneg _)
         _ = K := by dsimp [K,N]; push_cast; ring
  have threshold : b*c.A ≤ ⌈(Fintype.card (Fin (b*N₀)):ℝ)*(1-r)⌉₊ := by
    have hh : (c.A:ℝ) ≤ (1-r)*N₀ := (div_le_iff₀ hNpos).mp (by linarith)
    calc b*c.A = ⌈((b*c.A : ℕ):ℝ)⌉₊ := (Nat.ceil_natCast _).symm
         _ ≤ _ := Nat.ceil_mono (by rw [Fintype.card_fin]; push_cast; nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg b)])
  exact mcaError_affineLine_le_of_exactAgreement dom K hline r threshold

/-- At any rate and any reference length, a strict shifted-slot surplus and
the displayed squarefree charge imply uniform security on every positive
multiple of the reference block. -/
theorem security_of_squarefree_slots {b p N₀ : ℕ} [Fact p.Prime] [SampleableType (ZMod p)]
    (hb : 0<b) (c : Case) (hd : 2≤c.k ∧ c.k<c.A ∧ c.A≤N₀ ∧ 1≤c.M ∧ c.M≤c.v ∧ c.M≤2^128)
    (hslots : rowSlots N₀ c.m c.M c.v c.h < columnSlots c.k c.A c.m c.M c.v c.h)
    (hcharge : charge N₀ c.k c.v c.M c.h (((N₀-c.k:ℕ):ℝ)/(c.A-c.k:ℕ)) ≤
      (2:ℝ)^c.bits*(N₀:ℝ)^2)
    (dom : Fin (b*N₀) ↪ ZMod p) {r : ℝ} (hr : r ≤ 1-(c.A:ℝ)/N₀)
    (hp : 2^(128+c.bits)*(b*N₀)^2 ≤ p) :
    mcaError (AffineLineGenerator (ZMod p)) (code dom (b*c.k)) r ≤
      ENNReal.ofReal (1/(2:ℝ)^128) := by
  have hbk : 2≤b*c.k := hd.1.trans (Nat.le_mul_of_pos_left _ hb)
  have hbA := Nat.mul_lt_mul_of_pos_left hd.2.1 hb
  have hn := Nat.mul_le_mul_left b hd.2.2.1
  have hp' : 2^128*(2^c.bits)*(b*N₀)^2 ≤ p := by rw [←pow_add]; exact hp
  have hlen : 2≤N₀ := hd.1.trans (hd.2.1.le.trans hd.2.2.1)
  have hNpos : (0:ℝ)<N₀ := by exact_mod_cast (show 0<N₀ by omega)
  have hnpos : 1<b*N₀ := hlen.trans (Nat.le_mul_of_pos_left _ hb)
  have hpow : 1≤2^c.bits := Nat.one_le_pow _ _ (by decide)
  have hlow : 2^128*(b*N₀) ≤ p := by
    have hsq : b*N₀ ≤ (b*N₀)^2 := Nat.le_self_pow (by decide) _
    exact (Nat.mul_le_mul (Nat.le_mul_of_pos_right _ hpow) hsq).trans hp'
  have hchar : ringChar (ZMod p)=0 ∨ max (b*c.k-1) c.M < ringChar (ZMod p) := by
    right
    rw [ZMod.ringChar_zmod_n]
    have hx := hd.2.2.2.2.2
    apply max_lt
    · have := Nat.le_of_lt hbA
      omega
    · omega
  apply (error_of_squarefree_slots hb c ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.1⟩
    hchar hslots hcharge dom hr).trans
  rw [ZMod.card]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_div_iff₀ (by exact_mod_cast (Fact.out : p.Prime).pos) (by norm_num : (0:ℝ)<2^128)).mpr
  have hcast : (2:ℝ)^128*(2:ℝ)^c.bits*((b*N₀:ℕ):ℝ)^2 ≤ p := by exact_mod_cast hp'
  linarith

/-- Each row gives a 128-bit bound at all scales and all prescribed domains. -/
theorem uniform_security {b p : ℕ} [Fact p.Prime] [SampleableType (ZMod p)]
    (hb : 0<b) (i : Fin 12) (dom : Fin (b*4096) ↪ ZMod p) {r : ℝ}
    (hr : r ≤ 1-((cases i).A:ℝ)/4096)
    (hp : 2^(128+(cases i).bits)*(b*4096)^2 ≤ p) :
    mcaError (AffineLineGenerator (ZMod p)) (code dom (b*(cases i).k)) r ≤
      ENNReal.ofReal (1/(2:ℝ)^128) := by
  apply security_of_squarefree_slots hb (cases i) _ (slots i) (charges i) dom hr hp
  fin_cases i <;> decide

/-- At length `2^30` in the BLS scalar field, the four largest radii in the
table all qualify. Every prescribed domain of that length is allowed. -/
theorem bls_production [SampleableType (ZMod BlsScalarSubgroup.P)]
    (dom : Fin (262144*4096) ↪ ZMod BlsScalarSubgroup.P) (j : Fin 4) :
    let c := cases ⟨8+j.val,by omega⟩
    mcaError (AffineLineGenerator (ZMod BlsScalarSubgroup.P)) (code dom (262144*c.k))
      (1-(c.A:ℝ)/4096) ≤ ENNReal.ofReal (1/(2:ℝ)^128) := by
  apply uniform_security (by decide) ⟨8+j.val,by omega⟩ dom le_rfl
  fin_cases j <;> decide

private theorem slots_double {n k A m M v h : ℕ}
    (hs : rowSlots n m M v h < columnSlots k A m M v h) :
    rowSlots (2*n) m M v h < columnSlots (2*k) (2*A) m M v h := by
  have hrow : rowSlots (2*n) m M v h = 2*rowSlots n m M v h := by
    unfold rowSlots
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hcol : columnSlots (2*k) (2*A) m M v h = 2*columnSlots k A m M v h := by
    rw [column_compact,column_compact,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    have hsub : m*(2*A)-(2*k)*t = 2*(m*A-k*t) := by rw [Nat.mul_sub]; ac_rfl
    rw [hsub]; ring
  rw [hrow,hcol]
  omega

set_option maxRecDepth 200000 in
/-- At the 246-bit production prime the same four largest radii qualify.
At eighth rate, normalizing the lower-order terms at length 8192 suffices. -/
theorem prime246_production [SampleableType (ZMod FourRateListPrime246.P)]
    (dom : Fin (262144*4096) ↪ ZMod FourRateListPrime246.P) (j : Fin 4) :
    let c := cases ⟨8+j.val,by omega⟩
    mcaError (AffineLineGenerator (ZMod FourRateListPrime246.P)) (code dom (262144*c.k))
      (1-(c.A:ℝ)/4096) ≤ ENNReal.ofReal (1/(2:ℝ)^128) := by
  by_cases h : j=2
  · subst j
    let c : Case := ⟨1024,2614,7697,4236,19648,75007065,57⟩
    have hslots : rowSlots 8192 c.m c.M c.v c.h < columnSlots c.k c.A c.m c.M c.v c.h :=
      @slots_double 4096 512 1307 7697 4236 19648 75007065 (slots 10)
    apply security_of_squarefree_slots (b:=131072) (N₀:=8192) (by decide) c
      (by decide) hslots _ dom _ (by decide)
    · norm_num [c,charge]
    · norm_num [c,cases]
  · apply uniform_security (by decide) ⟨8+j.val,by omega⟩ dom le_rfl
    fin_cases j <;> first | decide | contradiction

#print axioms prime246_production
#print axioms error_of_squarefree_slots
#print axioms security_of_squarefree_slots
#print axioms uniform_security
#print axioms bls_production
end ProximityGap.ScaledSquarefreeSafety
