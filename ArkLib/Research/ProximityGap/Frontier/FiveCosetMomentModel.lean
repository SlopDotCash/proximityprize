/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Five raw moments of the real period histogram

At the production length, a real list with one entry per multiplicative coset can realize
simultaneously the first five period sums at vanishing third/fifth returns and exact
minimal fourth energy. A coordinate has absolute value within 1/2700 of the full subgroup
size. The constructed list is a statement about these scalar moment constraints.
-/

noncomputable section

namespace ArkLib.ProximityGap.Frontier.FiveCosetMomentModel

abbrev Atoms := List (ℕ × ℝ)

def moment (a : Atoms) (r : ℕ) : ℝ := (a.map (fun q ↦ (q.1:ℝ)*q.2^r)).sum

def mass (a : Atoms) : ℕ := (a.map Prod.fst).sum

def row (k : ℕ) (x : ℝ) : Atoms :=
  [(522*k, 1/2700-x), (1755*k, x-2/2700), (2540*k, 3/2700-x),
   (1980*k, x-4/2700), (810*k, 5/2700-x), (137*k, x-6/2700)]

def base (n : ℝ) : Atoms := row 6 0 ++ row 32 (n/2) ++ row 7 n

theorem base_mass (n : ℝ) : mass (base n)=348480 := by norm_num [mass,base,row]

theorem base_odd (n : ℝ) : moment (base n) 1 = -1 ∧
    moment (base n) 3 = -n^2 ∧ moment (base n) 5 = -n^4 := by
  refine ⟨?_,?_,?_⟩ <;> norm_num [moment,base,row] <;> ring

def histogram (a : Atoms) : List ℝ := a.flatMap (fun q ↦ List.replicate q.1 q.2)

theorem histogram_moment (a : Atoms) (r : ℕ) :
    ((histogram a).map (·^r)).sum = moment a r := by
  induction a with
  | nil => simp [histogram,moment]
  | cons h t ih => simpa [histogram,moment] using congrArg ((h.1:ℝ)*h.2^r + ·) ih

theorem histogram_length (a : Atoms) : (histogram a).length = mass a := by
  induction a with
  | nil => rfl
  | cons h t ih => simp [histogram,mass]

def pairs (k : ℕ) (u : ℝ) : Atoms := [(k,u),(k,-u)]

theorem append_moment (a b : Atoms) (r : ℕ) :
    moment (a++b) r=moment a r+moment b r := by simp [moment]

theorem append_mass (a b : Atoms) : mass (a++b)=mass a + mass b := by simp [mass]

theorem pairs_odd (k : ℕ) (u : ℝ) {r : ℕ} (hr : Odd r) : moment (pairs k u) r=0 := by
  simp [pairs,moment,hr.neg_pow]

theorem pairs_even (k : ℕ) (u : ℝ) {r : ℕ} (hr : Even r) :
    moment (pairs k u) r=2*k*u^r := by
  simp [pairs,moment,hr.neg_pow]
  ring

/-- Two groups of pairs match the residual variance and fourth moment. -/
theorem pairs_fill {N J : ℕ} (hJ : 0<J) (hlt : J<N) {s t : ℝ} (hs : 0<s)
    (hlo : s^2/N≤t) (hhi : t≤s^2/J) :
    ∃ u v : ℝ, 0≤u ∧ 0≤v ∧ u^2≤s/J ∧ v^2≤s/J ∧
      J*u^2+(N-J:ℕ)*v^2=s ∧ J*u^4+(N-J:ℕ)*v^4=t := by
  have hJR : 0 < (J:ℝ) := by exact_mod_cast hJ
  have hNR : 0 < (N:ℝ) := by exact_mod_cast (hJ.trans hlt)
  have hltR : (J:ℝ)<N := by exact_mod_cast hlt
  have hstep : s^2/N < s^2/J := by gcongr
  let k := Real.sqrt ((t-s^2/N)/(s^2/J-s^2/N))
  have hk : 0≤k := Real.sqrt_nonneg _
  have hk2 : k^2=(t-s^2/N)/(s^2/J-s^2/N) := Real.sq_sqrt (by positivity)
  have hle : k≤1 := by
    have hh : (t-s^2/N)/(s^2/J-s^2/N) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    nlinarith
  have hgap : 0 < s/J-s/N := by apply sub_pos.mpr; exact div_lt_div_of_pos_left hs hJR hltR
  let a := s/N+k*(s/J-s/N)
  let b := (1-k)*(s/N)
  have ha : 0≤a := by dsimp [a]; positivity
  have hb : 0≤b := by dsimp [b]; positivity
  have ha' : a ≤ s/J := by dsimp [a]; nlinarith [mul_nonneg (sub_nonneg.mpr hle) hgap.le]
  have hb' : b ≤ s/J := by
    dsimp [b]
    calc (1-k)*(s/N) ≤ 1*(s/N) := by gcongr; linarith
      _ ≤ s/J := by linarith
  refine ⟨Real.sqrt a, Real.sqrt b, Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_, ?_, ?_, ?_⟩
  · rwa [Real.sq_sqrt ha]
  · rwa [Real.sq_sqrt hb]
  · rw [Real.sq_sqrt ha, Real.sq_sqrt hb, Nat.cast_sub hlt.le]
    dsimp [a,b]
    field_simp
    ring
  · rw [show (4:ℕ)=2*2 by rfl, pow_mul, pow_mul, Real.sq_sqrt ha, Real.sq_sqrt hb, Nat.cast_sub hlt.le]
    have hk' : k^2*(s^2/J-s^2/N)=t-s^2/N := (eq_div_iff (by linarith)).mp hk2
    calc (J:ℝ)*a^2+((N:ℝ)-J)*b^2 = s^2/N+k^2*(s^2/J-s^2/N) := by
           dsimp [a,b]
           field_simp
           ring
      _ = t := by rw [hk']; ring


theorem base_bounds {n : ℝ} (hn : 1 ≤ n) :
    ∀ q ∈ base n, |q.2|≤n := by
  intro q hq
  simp [base,row] at hq
  rcases hq with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
  all_goals rw [abs_le]; constructor <;> norm_num <;> linarith

theorem base_spike (n : ℝ) : (3654, 1/2700-n) ∈ base n := by simp [base,row]

theorem moment_bounds (a : Atoms) {n : ℝ} (_hn : 0≤n)
    (hb : ∀ q ∈ a, |q.2| ≤ n) {r : ℕ} (hr : Even r) :
    0 ≤ moment a r ∧ moment a r ≤ (mass a:ℝ)*n^r := by
  induction a with
  | nil => simp [moment,mass]
  | cons h tail ih =>
    obtain ⟨h0,h1⟩ := ih (fun q hq ↦ hb q (by simp [hq]))
    have hpow : h.2^r ≤ n^r := hr.pow_abs h.2 ▸ pow_le_pow_left₀ (abs_nonneg _) (hb h (by simp)) _
    have hnon := hr.pow_nonneg h.2
    change 0 ≤ (h.1:ℝ)*h.2^r+moment tail r ∧ _ ≤ ((h.1+mass tail:ℕ):ℝ)*n^r
    push_cast
    rw [add_mul]
    exact ⟨add_nonneg (by positivity) h0, add_le_add (mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ) ≤ h.1)) h1⟩

theorem model_of_feasible (n p : ℝ) (N J rem : ℕ) (hJ : 0<J) (hlt : J<N)
    (hs : 0<(p-n-moment (base n) 2)/2)
    (hlo : ((p-n-moment (base n) 2)/2)^2/N ≤ (3*p*(n-1)-n^3-moment (base n) 4)/2)
    (hhi : (3*p*(n-1)-n^3-moment (base n) 4)/2 ≤ ((p-n-moment (base n) 2)/2)^2/J)
    (hcap : (p-n-moment (base n) 2)/2/J ≤ n^2) (hn : 1≤n) :
    ∃ xs : List ℝ, xs.length = 348480+2*N+rem ∧ (1/2700-n)∈xs ∧
      (∀ x∈xs, |x| ≤ n) ∧ (xs.map (·^1)).sum = -1 ∧ (xs.map (·^2)).sum = p-n ∧
      (xs.map (·^3)).sum = -n^2 ∧ (xs.map (·^4)).sum = 3*p*(n-1)-n^3 ∧
      (xs.map (·^5)).sum = -n^4 := by
  obtain ⟨u,v,hu,hv,hu',hv',hs',ht'⟩ := pairs_fill hJ hlt hs hlo hhi
  have hu'' : |u| ≤ n := by rw [abs_of_nonneg hu]; nlinarith [hu'.trans hcap]
  have hv'' : |v| ≤ n := by rw [abs_of_nonneg hv]; nlinarith [hv'.trans hcap]
  let A := base n ++ pairs J u ++ pairs (N-J) v ++ [(rem, (0:ℝ))]
  refine ⟨histogram A, ?_, ?_, ?_, ?_⟩
  · rw [histogram_length]
    simp only [A,append_mass,base_mass]
    simp [mass,pairs]
    omega
  · have h := base_spike n
    simp only [histogram,List.mem_flatMap,List.mem_replicate]
    refine ⟨(3654,1/2700-n),?_, by norm_num⟩
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))
  · intro x hx
    obtain ⟨q,hq,hx⟩ := List.mem_flatMap.mp hx
    have hqx := (List.mem_replicate.mp hx).2
    subst x
    simp [A,pairs] at hq
    rcases hq with ha|rfl|rfl|rfl|rfl|rfl
    · exact base_bounds hn _ ha
    all_goals simp [hu'',hv'',show 0≤n by linarith]
  · simp only [histogram_moment, A, append_moment]
    obtain ⟨h1,h3,h5⟩ := base_odd n
    simp only [pairs_odd _ _ (by decide : Odd 1), pairs_odd _ _ (by decide : Odd 3),
      pairs_odd _ _ (by decide : Odd 5), pairs_even _ _ (by decide : Even 2),
      pairs_even _ _ (by decide : Even 4), h1,h3,h5]
    have hz (r : ℕ) (hr : r≠0) : moment [(rem, (0:ℝ))] r = 0 := by simp [moment,zero_pow hr]
    simp only [hz _ (by decide : 1≠0), hz _ (by decide : 2≠0), hz _ (by decide : 3≠0),
      hz _ (by decide : 4≠0),hz _ (by decide : 5≠0), add_zero, true_and]
    exact ⟨by linarith, by linarith, trivial⟩

/-- The first five moment equalities permit a large coordinate in every production-band index. -/
theorem production_model (k : ℕ) (hk : 2^128 ≤ k) :
    let n : ℝ := 2^30
    let p : ℝ := n*k+1
    ∃ xs : List ℝ, xs.length = k ∧ (1/2700-n)∈xs ∧
      (∀ x∈xs, |x|≤n) ∧ (xs.map (·^1)).sum = -1 ∧ (xs.map (·^2)).sum = p-n ∧
      (xs.map (·^3)).sum = -n^2 ∧ (xs.map (·^4)).sum = 3*p*(n-1)-n^3 ∧
      (xs.map (·^5)).sum = -n^4 := by
  dsimp only
  let n : ℝ := 2^30
  let p := n*k+1
  let N := (k-348480)/2
  let J := k/16
  let s := (p-n-moment (base n) 2)/2
  let t := (3*p*(n-1)-n^3-moment (base n) 4)/2
  have hJ : 0<J := by dsimp [J]; omega
  have hlt : J<N := by dsimp [N,J]; omega
  have hJR : 0<(J:ℝ) := by exact_mod_cast hJ
  have hNR : 0<(N:ℝ) := by exact_mod_cast hJ.trans hlt
  have hN : (k:ℝ) ≤ 3*N := by exact_mod_cast (show k≤3*N by dsimp [N]; omega)
  have hJ' : 16*(J:ℝ)≤k := by exact_mod_cast (show 16*J≤k by dsimp [J]; omega)
  have hJ'' : (k:ℝ)≤32*J := by exact_mod_cast (show k≤32*J by dsimp [J]; omega)
  have hk' : (2:ℝ)^128≤k := by exact_mod_cast hk
  have hn : (1:ℝ)≤n := by norm_num [n]
  obtain ⟨hs0,hs1⟩ := moment_bounds (base n) (by linarith : 0≤n) (base_bounds hn) (by decide : Even 2)
  obtain ⟨ht0,ht1⟩ := moment_bounds (base n) (by linarith : 0≤n) (base_bounds hn) (by decide : Even 4)
  rw [base_mass] at hs1 ht1
  have sLo : 2*n*k/5 ≤ s := by dsimp [s,p,n] at *; norm_num only [Nat.reducePow,Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, Nat.cast_mul, reduceCtorEq] at *; linarith
  have sHi : s ≤ n*k/2 := by dsimp [s,p,n] at *; norm_num only [Nat.reducePow,Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, Nat.cast_mul, reduceCtorEq] at *; linarith
  have tLo : n^2*k ≤ t := by dsimp [t,p,n] at *; norm_num only [Nat.reducePow,Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, Nat.cast_mul, reduceCtorEq] at *; linarith
  have tHi : t ≤ 3*n^2*k/2 := by dsimp [t,p,n] at *; norm_num only [Nat.reducePow,Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, Nat.cast_mul, reduceCtorEq] at *; linarith
  have hs : 0<s := lt_of_lt_of_le (by positivity) sLo
  have hlo : s^2/N ≤ t := by
    apply (div_le_iff₀ hNR).2
    calc s^2 ≤ (n*k/2)^2 := pow_le_pow_left₀ hs.le sHi 2
      _ ≤ (n^2*k)*N := by nlinarith [mul_nonneg (show 0≤n^2*k by positivity) (sub_nonneg.mpr hN)]
      _ ≤ t*N := by gcongr
  have hhi : t ≤ s^2/J := by
    apply (le_div_iff₀ hJR).2
    calc t*J ≤ (3*n^2*k/2)*J := by gcongr
      _ ≤ (2*n*k/5)^2 := by nlinarith [mul_nonneg (show 0≤n^2*k by positivity) (sub_nonneg.mpr hJ')]
      _ ≤ s^2 := pow_le_pow_left₀ (by positivity) sLo 2
  have hcap : s/J≤n^2 := by
    apply (div_le_iff₀ hJR).2
    apply sHi.trans
    dsimp [n]
    norm_num
    linarith
  have hrem : 348480+2*N+(k-348480)%2=k := by dsimp [N]; omega
  simpa only [hrem] using (model_of_feasible n p N J ((k-348480)%2) hJ hlt hs hlo hhi hcap hn)

#print axioms production_model
#print axioms model_of_feasible
#print axioms base_odd
#print axioms pairs_fill

end ArkLib.ProximityGap.Frontier.FiveCosetMomentModel
