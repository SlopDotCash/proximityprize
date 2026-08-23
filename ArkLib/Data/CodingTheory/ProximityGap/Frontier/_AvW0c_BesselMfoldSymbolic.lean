/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Central
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvW0_BesselIdentity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvUC_BesselIdentityFormalized
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvRem_BesselMfold

/-!
# STEP-1 Bessel identity: the `m`-fold decoupling iterated on the ACTUAL energy (#444)

This brick closes the rung explicitly DEFERRED by `_AvRem_BesselMfold` ("It does NOT mechanically
iterate the bijection to a single closed `Z_r(μ_{2m}) = Edef r m` for symbolic `m`"). We carry out
exactly that iteration on the genuine `Finset.card` energy.

## What was already landed (build on, exact names)

* `_AvUC.zeroSum_negPair_eq_centralBinom` — the `m = 1` base: `Z_r({1,−1}) = centralBinom r`, a real
  `Finset.card` bijection.
* `_AvRem.zeroSumCount_union_eq_binom_convolution` — the two-direction step on real energy: under the
  Lam–Leung additive-decoupling `AdditivelyDecoupled G H`,
  `Z_N(G ∪ H) = Σ_{a≤N} C(N,a) · Z_a(G) · Z_{N−a}(H)`.

## What this brick adds (the named gap)

We package a *family* of `m` directions as a `List (Finset F)` in which each direction is
additively-decoupled from the union of the directions after it (the Lam–Leung separation, which holds
for the distinct antipodal directions of `μ_{2m}`). We then prove, **by induction on the list**, that
the zero-sum count of the whole union equals the iterated binomial multi-convolution of the
per-direction counts:

  `zeroSumCount (⋃ Ds) N = mfoldConv (Ds.map zeroSumCount) N`,

where `mfoldConv fs N` is the `List`-folded binomial convolution
`mfoldConv [] N = [N = 0]`, `mfoldConv (f :: fs) N = Σ_{a≤N} C(N,a)·f a·mfoldConv fs (N−a)`.

This is the EXACT `Finset`-card realization of the `m`-fold EGF convolution `cpow` (the recursion in
`_AvW0.cpow`): `mfoldConv` is the position-level (binomial-weighted) analogue of the direction-level
`cpow`, and at `N = 2r` with every per-direction count `= centralBinom` it specializes to the
Bessel coefficient `(2r)!·cpow I0c m r = Edef r m`.

We close the bridge fully at the head:
* `zeroSumCount_mfold` — the iterated decoupling identity (genuine `Finset.card`, all `N`, all `m`).
* `mfoldConv_negPair` — for the all-`{1,−1}` family the multi-convolution evaluated at `N = 2r`
  equals `(2r)! · cpow I0c m r = Edef r m` (the Bessel RHS), via `centralBinom r = (2r)!·I0c r`.
* `bessel_mfold_realization` — composing the two: the zero-sum count of `m` decoupled copies of a
  `centralBinom`-direction equals `Edef r m` on the nose. (The honest residual is geometric: that
  `μ_{2m}`'s `m` antipodal directions ARE such a decoupled family — that is the Lam–Leung input,
  already a named/proved in-tree fact; here the *combinatorial* iteration is fully discharged.)

## Honest scope (#444)

This is **char-0 ONLY** and closes the *combinatorial* half of STEP-1 (the multinomial bijection
given Lam–Leung), iterated to symbolic `m` on the actual energy — the piece the predecessor bricks
left as "named". It does NOT touch the char-`p` excess `W_r` (the open kernel); the prize wall is
unchanged. Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`, no `native_decide`.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.NegationClosedWalk
open ArkLib.ProximityGap.Frontier.AvRem (AdditivelyDecoupled zeroSumCount_union_eq_binom_convolution)

namespace ArkLib.ProximityGap.Frontier.Step1Bessel

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The `List`-folded binomial multi-convolution (position-level analogue of `cpow`). -/

/-- The iterated binomial convolution of a list of per-direction counts:
`mfoldConv [] N = [N = 0]`, `mfoldConv (f :: fs) N = Σ_{a≤N} C(N,a) · f a · mfoldConv fs (N−a)`. -/
def mfoldConv : List (ℕ → ℕ) → ℕ → ℕ
  | [],      N => if N = 0 then 1 else 0
  | f :: fs, N => ∑ a ∈ Finset.range (N + 1), (N.choose a) * (f a * mfoldConv fs (N - a))

/-! ## A decoupled family: each direction decoupled from the fold of those after it. -/

/-- The union (fold) of a list of directions. -/
def unionFold : List (Finset F) → Finset F
  | []      => ∅
  | D :: Ds => D ∪ unionFold Ds

/-- A list of directions is **head-decoupled** when each direction is additively-decoupled from the
union of all directions after it. For the distinct antipodal directions of `μ_{2m}` this is exactly
the Lam–Leung two-power separation, listed. -/
def HeadDecoupled : List (Finset F) → Prop
  | []      => True
  | D :: Ds => AdditivelyDecoupled D (unionFold Ds) ∧ HeadDecoupled Ds

/-- The empty union has only the empty tuple as a zero-sum tuple, so `Z_∅(N) = [N = 0]`. -/
theorem zeroSumCount_empty (N : ℕ) :
    zeroSumCount (∅ : Finset F) N = if N = 0 then 1 else 0 := by
  classical
  unfold zeroSumCount
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    -- the unique empty tuple `Fin 0 → F` is vacuously a member and sums to 0
    rw [if_pos rfl]
    have : ((Fintype.piFinset (fun _ : Fin 0 => (∅ : Finset F))).filter (fun c => ∑ i, c i = 0))
        = {fun i => i.elim0} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨?_, ?_⟩
      · simp only [Finset.mem_filter, Fintype.mem_piFinset]
        exact ⟨fun i => i.elim0, by simp⟩
      · intro c _; funext i; exact i.elim0
    rw [this, Finset.card_singleton]
  · -- no `Fin N → ∅` tuple exists for `N > 0`, so the filtered set is empty
    rw [if_neg (by omega)]
    rw [Finset.card_eq_zero]
    rw [Finset.filter_eq_empty_iff]
    intro c hc
    simp only [Fintype.mem_piFinset] at hc
    exact absurd (hc ⟨0, hN⟩) (Finset.notMem_empty _)

/-! ## The main iteration: zero-sum count of a head-decoupled union = the multi-convolution. -/

/-- **STEP-1, the `m`-fold decoupling on the actual energy.** For a head-decoupled list of
directions, the zero-sum count over the whole union equals the iterated binomial multi-convolution of
the per-direction zero-sum counts. Proved by induction on the list, using the two-direction
decoupling `zeroSumCount_union_eq_binom_convolution` at each step. -/
theorem zeroSumCount_mfold (Ds : List (Finset F)) (hdec : HeadDecoupled Ds) (N : ℕ) :
    zeroSumCount (unionFold Ds) N = mfoldConv (Ds.map (fun D => zeroSumCount D)) N := by
  classical
  induction Ds generalizing N with
  | nil =>
      simp only [unionFold, mfoldConv, List.map_nil]
      exact zeroSumCount_empty N
  | cons D Ds ih =>
      obtain ⟨hDdec, htail⟩ := hdec
      simp only [unionFold, List.map_cons, mfoldConv]
      rw [zeroSumCount_union_eq_binom_convolution D (unionFold Ds) hDdec N]
      apply Finset.sum_congr rfl
      intro a ha
      rw [ih htail (N - a)]

/-! ## Specialization to the all-`{1,−1}` family: the Bessel coefficient on the nose.

For the family `[negPair, …, negPair]` (`m` copies), every per-direction count is
`Z_a(negPair) = if a even then centralBinom (a/2) else 0`, and `centralBinom k = (2k)!·I0c k`, so the
multi-convolution at `N = 2r` equals `(2r)!·cpow I0c m r = Edef r m`. -/

open ArkLib.ProximityGap.Frontier.AvUC (negPair zeroSum_negPair_eq_centralBinom)
open ArkLib.ProximityGap.Frontier.AvW0 (cpow I0c Edef)

/-- The per-direction count of the single antipodal direction `{1,−1}`, as a closed function of the
tuple length: `centralBinom (a/2)` for even `a`, `0` for odd `a`. -/
theorem zeroSumCount_negPair_closed (a : ℕ) :
    zeroSumCount negPair a = if a % 2 = 0 then Nat.centralBinom (a / 2) else 0 := by
  rcases Nat.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- a = 2k
    have ha2 : a % 2 = 0 := by omega
    have hak : a = 2 * k := by omega
    rw [if_pos ha2, hak, zeroSum_negPair_eq_centralBinom k]
    congr 1; omega
  · -- a = 2k+1, odd ⇒ no zero-sum tuple (sum of an odd number of ±1 is odd, ≠ 0)
    rw [if_neg (by omega)]
    classical
    unfold zeroSumCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c hc hcsum
    simp only [Fintype.mem_piFinset] at hc
    -- each c i ∈ {1,-1}; #+ + #- = a (odd); ∑ c i = #+ - #-; vanishing ⟹ #+ = #- ⟹ a even
    set P := Finset.univ.filter (fun i => c i = (1 : ℚ)) with hP
    set Nn := Finset.univ.filter (fun i => c i = (-1 : ℚ)) with hN
    have hdisj : Disjoint P Nn := by
      rw [Finset.disjoint_filter]; intro i _ h1 h2; rw [h1] at h2; norm_num at h2
    have hunion : P ∪ Nn = Finset.univ := by
      apply Finset.eq_univ_of_forall; intro i
      rcases (ArkLib.ProximityGap.Frontier.AvUC.mem_negPair).mp (hc i) with h1 | h1
      · exact Finset.mem_union_left _ (by rw [hP]; simp [h1])
      · exact Finset.mem_union_right _ (by rw [hN]; simp [h1])
    have hsplit : P.card + Nn.card = a := by
      have := Finset.card_union_of_disjoint hdisj
      rw [hunion] at this
      simpa [Finset.card_univ, Fintype.card_fin] using this.symm
    have hsumval : ∑ i, c i = (P.card : ℚ) - (Nn.card : ℚ) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => c i = (1:ℚ)) c]
      have hpart1 : ∑ i ∈ P, c i = (P.card : ℚ) := by
        rw [hP]; rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]; simp
      have hpart2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ c i = (1:ℚ)), c i = -(Nn.card : ℚ) := by
        have hcongr : Finset.univ.filter (fun i => ¬ c i = (1:ℚ))
            = Finset.univ.filter (fun i => c i = (-1:ℚ)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rcases (ArkLib.ProximityGap.Frontier.AvUC.mem_negPair).mp (hc i) with h1 | h1
          · rw [h1]; norm_num
          · rw [h1]; norm_num
        rw [hcongr]
        rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one, neg_inj]
        rw [hN]
      rw [hpart1, hpart2]; ring
    have hsum0 : (P.card : ℚ) - (Nn.card : ℚ) = 0 := hsumval ▸ hcsum
    have heq : P.card = Nn.card := by
      have : (P.card : ℚ) = (Nn.card : ℚ) := by linarith
      exact_mod_cast this
    -- a = P.card + Nn.card = 2 * P.card is even, contradicting a odd (a % 2 = 1)
    omega

/-- `centralBinom k = (2k)! · I0c k` (over `ℚ`): the central binomial is the EGF coefficient scaled
by `(2k)!`. -/
theorem centralBinom_eq_factorial_mul_I0c (k : ℕ) :
    (Nat.centralBinom k : ℚ) = ((2 * k).factorial : ℚ) * I0c k := by
  unfold ArkLib.ProximityGap.Frontier.AvW0.I0c
  rw [Nat.centralBinom_eq_two_mul_choose]
  have hk : ((2 * k).choose k : ℚ) = ((2*k).factorial : ℚ) / ((k.factorial : ℚ) ^ 2) := by
    have hpos : (0 : ℚ) < (k.factorial : ℚ) ^ 2 := by positivity
    rw [eq_div_iff (ne_of_gt hpos)]
    have hcast : ((2*k).choose k * k.factorial * (2*k - k).factorial : ℕ) = (2*k).factorial :=
      Nat.choose_mul_factorial_mul_factorial (by omega)
    have hQ : ((2*k).choose k : ℚ) * (k.factorial : ℚ) * ((2*k - k).factorial : ℚ) = ((2*k).factorial : ℚ) := by
      exact_mod_cast hcast
    have h2kk : (2 * k - k : ℕ) = k := by omega
    rw [h2kk] at hQ
    rw [pow_two]; linarith [hQ]
  rw [hk]; ring

/-! ## The realization bridge: the all-`negPair` multi-convolution IS the Bessel coefficient.

We show `(mfoldConv (replicate m Znp) N : ℚ) = if N even then N! · cpow I0c m (N/2) else 0`, where
`Znp = zeroSumCount negPair`. Composed with `zeroSumCount_mfold` (at `N = 2r`) this gives
`Z_r(⋃ m copies) = Edef r m` — the Bessel identity on the actual energy. -/

/-- Abbreviation for the single-direction `{1,−1}` zero-sum count. -/
def Znp : ℕ → ℕ := fun a => zeroSumCount (negPair) a

/-- `Znp` in closed form: `centralBinom (a/2)` for even `a`, `0` for odd. -/
theorem Znp_closed (a : ℕ) : Znp a = if a % 2 = 0 then Nat.centralBinom (a / 2) else 0 :=
  zeroSumCount_negPair_closed a

/-- **The normalization bridge.** The `m`-fold binomial multi-convolution of the single-direction
count, over ℚ, equals the `(N)!`-scaled `m`-fold EGF convolution of `I0c` (the Bessel coefficient),
supported on even `N`. Proved by induction on `m`; the key per-term identity is
`C(2r,2j)·centralBinom j·(2(r−j))! = (2r)!·I0c j`. -/
theorem mfoldConv_replicate_negPair (m N : ℕ) :
    ((mfoldConv (List.replicate m Znp) N : ℕ) : ℚ)
      = if N % 2 = 0 then (N.factorial : ℚ) * cpow I0c m (N / 2) else 0 := by
  induction m generalizing N with
  | zero =>
      simp only [List.replicate_zero, mfoldConv]
      rcases Nat.eq_zero_or_pos N with hN0 | hN0
      · -- N = 0: LHS = 1, RHS = 0! · cpow I0c 0 0 = 1·1 = 1
        subst hN0
        simp [ArkLib.ProximityGap.Frontier.AvW0.cpow]
      · -- N > 0: LHS = 0; RHS even-branch has cpow I0c 0 (N/2) = [N/2 = 0] = 0 (N>0)
        rw [if_neg (by omega : ¬ N = 0)]
        by_cases hpar : N % 2 = 0
        · rw [if_pos hpar]
          have hcp : ArkLib.ProximityGap.Frontier.AvW0.cpow I0c 0 (N / 2) = 0 := by
            unfold ArkLib.ProximityGap.Frontier.AvW0.cpow
            rw [if_neg (by omega : ¬ N / 2 = 0)]
          rw [hcp]; push_cast; ring
        · rw [if_neg hpar]; push_cast; ring
  | succ m ih =>
      simp only [List.replicate_succ, mfoldConv]
      -- the convolution sum; only even `a` contribute (Znp odd = 0)
      rcases Nat.even_or_odd N with ⟨r, hr⟩ | ⟨r, hr⟩
      · -- N = 2r even.  N/2 = r.
        rw [if_pos (by omega)]
        have hNr : N / 2 = r := by omega
        rw [hNr]
        -- unfold cpow I0c (m+1) r = Σ_{j≤r} I0c j · cpow I0c m (r-j)
        have hcpow : cpow I0c (m + 1) r
            = ∑ j ∈ Finset.range (r + 1), I0c j * cpow I0c m (r - j) := rfl
        rw [hcpow, Finset.mul_sum]
        -- push cast through the LHS sum
        push_cast
        -- Step A: rewrite each LHS term to its ℚ value; odd a → 0, even a=2j → the per-term.
        have hterm : ∀ a ∈ Finset.range (N + 1),
            (N.choose a : ℚ) * ((Znp a : ℚ) * ((mfoldConv (List.replicate m Znp) (N - a) : ℕ) : ℚ))
              = if a % 2 = 0 then
                  (N.choose a : ℚ) * ((Nat.centralBinom (a/2) : ℚ)
                    * ((N - a).factorial : ℚ) * cpow I0c m ((N - a)/2))
                else 0 := by
          intro a ha
          rw [Finset.mem_range] at ha
          by_cases hpar : a % 2 = 0
          · rw [if_pos hpar]
            rw [Znp_closed, if_pos hpar]
            rw [ih (N - a)]
            -- N - a even since N, a both even
            have hNa : (N - a) % 2 = 0 := by omega
            rw [if_pos hNa]
            ring
          · rw [if_neg hpar]
            rw [Znp_closed, if_neg hpar]
            push_cast; ring
        rw [Finset.sum_congr rfl hterm]
        -- Step B: the if-supported sum over range(N+1) reindexes to range(r+1) via a ↦ 2j.
        -- First drop odd terms, then biject even a=2j with j∈range(r+1).
        rw [← Finset.sum_filter]
        -- the filter {a ∈ range(N+1) : a even} biject with range(r+1) via j ↦ 2j
        rw [show (Finset.range (N + 1)).filter (fun a => a % 2 = 0)
              = (Finset.range (r + 1)).image (fun j => 2 * j) from ?_]
        · rw [Finset.sum_image (by intro x _ y _ h; dsimp only at h; omega)]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mem_range] at hj
          -- per-term identity: C(2r,2j)·centralBinom(j)·(2(r-j))! = (2r)!·I0c j
          have h2j : (2 * j) / 2 = j := by omega
          have hNmaj : N - 2 * j = 2 * (r - j) := by omega
          rw [h2j, hNmaj]
          have hNmaj2 : (2 * (r - j)) / 2 = r - j := by omega
          rw [hNmaj2]
          -- C(N,2j)·centralBinom j·(2(r-j))! = N!·I0c j   (N = 2r)
          have hkey : (N.choose (2*j) : ℚ) * (Nat.centralBinom j : ℚ) * ((2*(r-j)).factorial : ℚ)
              = (N.factorial : ℚ) * I0c j := by
            rw [centralBinom_eq_factorial_mul_I0c j]
            -- C(N,2j) = N!/((2j)!(N-2j)!),  N-2j = 2(r-j)
            have hchoose : (N.choose (2*j) : ℚ) * (((2*j).factorial : ℚ) * ((2*(r-j)).factorial : ℚ))
                = (N.factorial : ℚ) := by
              have hnat : (N.choose (2*j) * (2*j).factorial * (N - 2*j).factorial : ℕ) = N.factorial :=
                Nat.choose_mul_factorial_mul_factorial (by omega)
              have hQ : (N.choose (2*j) : ℚ) * ((2*j).factorial : ℚ) * ((N - 2*j).factorial : ℚ)
                  = (N.factorial : ℚ) := by exact_mod_cast hnat
              rw [hNmaj] at hQ; linarith [hQ]
            -- now assemble
            have h2jpos : ((2*j).factorial : ℚ) ≠ 0 := by positivity
            field_simp [ArkLib.ProximityGap.Frontier.AvW0.I0c] at hchoose ⊢
            nlinarith [hchoose, sq_nonneg ((j.factorial : ℚ))]
          -- goal: C(N,2j)·(centralBinom j · (2(r-j))! · cpow I0c m (r-j)) = N!·(I0c j · cpow I0c m (r-j))
          have hgoal : (N.choose (2*j) : ℚ) * ((Nat.centralBinom j : ℚ) * ((2*(r-j)).factorial : ℚ) * cpow I0c m (r-j))
              = (N.factorial : ℚ) * (I0c j * cpow I0c m (r-j)) := by
            calc (N.choose (2*j) : ℚ) * ((Nat.centralBinom j : ℚ) * ((2*(r-j)).factorial : ℚ) * cpow I0c m (r-j))
                = ((N.choose (2*j) : ℚ) * (Nat.centralBinom j : ℚ) * ((2*(r-j)).factorial : ℚ)) * cpow I0c m (r-j) := by ring
              _ = ((N.factorial : ℚ) * I0c j) * cpow I0c m (r-j) := by rw [hkey]
              _ = (N.factorial : ℚ) * (I0c j * cpow I0c m (r-j)) := by ring
          convert hgoal using 2
        · -- the index-set equality {a ∈ range(N+1) : even} = image (2·) (range(r+1))
          ext a
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
          constructor
          · rintro ⟨haN, hpar⟩
            exact ⟨a / 2, by omega, by omega⟩
          · rintro ⟨j, hj, rfl⟩
            exact ⟨by omega, by omega⟩
      · -- N odd: every term has either Znp(a)=0 (a odd) or mfoldConv(N-a)=0 (N-a odd)
        rw [if_neg (by omega)]
        push_cast
        rw [Finset.sum_eq_zero]
        intro a ha
        rw [Finset.mem_range] at ha
        rcases Nat.even_or_odd a with ⟨j, hj⟩ | ⟨j, hj⟩
        · -- a even ⇒ N - a odd ⇒ mfoldConv = 0 by IH
          have hmf0 : ((mfoldConv (List.replicate m Znp) (N - a) : ℕ) : ℚ) = 0 := by
            rw [ih (N - a), if_neg (by omega)]
          rw [hmf0]; ring
        · -- a odd ⇒ Znp a = 0
          have hZ0 : ((Znp a : ℕ) : ℚ) = 0 := by rw [Znp_closed, if_neg (by omega)]; norm_num
          rw [hZ0]; ring

/-- **The Bessel identity on the actual energy.** For ANY head-decoupled family `Ds` of `m`
single-antipodal-pair directions (each with per-direction zero-sum count `= Znp = zeroSumCount
negPair`, i.e. `centralBinom`-supported — the count of every `{±w}` direction), the zero-sum count of
the whole union at length `2r` equals the Bessel coefficient `Edef r m = (2r)!·[x^{2r}] I₀(2x)^m`.

This composes the two landed halves:
* `zeroSumCount_mfold` — the combinatorial `m`-fold decoupling on the genuine `Finset.card` energy;
* `mfoldConv_replicate_negPair` — the EGF normalization (the binomial multi-convolution IS the
  `(2r)!`-scaled `cpow I0c`).

The hypotheses (`HeadDecoupled Ds` and per-direction count `= Znp`) are exactly the geometric input
the Lam–Leung two-power theorem supplies for the `m = n/2` distinct antipodal directions of `μ_n`
(`n = 2m`); the *combinatorial identity* — the whole STEP-1 content modulo that geometric input — is
discharged here axiom-clean over ℚ. -/
theorem bessel_identity_on_energy {m : ℕ} (Ds : List (Finset ℚ)) (hdec : HeadDecoupled Ds)
    (hlen : Ds.length = m) (hcount : ∀ D ∈ Ds, (fun a => zeroSumCount D a) = Znp) (r : ℕ) :
    ((zeroSumCount (unionFold Ds) (2 * r) : ℕ) : ℚ) = Edef r m := by
  -- the mapped count list is `replicate m Znp`
  have hmap : Ds.map (fun D => fun a => zeroSumCount D a) = List.replicate m Znp := by
    rw [← hlen]
    apply (List.eq_replicate_iff).mpr
    refine ⟨by rw [List.length_map], ?_⟩
    intro f hf
    rw [List.mem_map] at hf
    obtain ⟨D, hD, rfl⟩ := hf
    exact hcount D hD
  rw [zeroSumCount_mfold Ds hdec (2 * r)]
  -- now LHS = mfoldConv (Ds.map zeroSumCount) (2r); rewrite the map; apply the normalization
  have hthis : Ds.map (fun D => zeroSumCount D) = List.replicate m Znp := hmap
  rw [hthis, mfoldConv_replicate_negPair m (2 * r)]
  rw [if_pos (by omega : (2 * r) % 2 = 0)]
  have h2r : (2 * r) / 2 = r := by omega
  rw [h2r]
  rfl

#print axioms zeroSumCount_empty
#print axioms zeroSumCount_mfold
#print axioms zeroSumCount_negPair_closed
#print axioms centralBinom_eq_factorial_mul_I0c
#print axioms mfoldConv_replicate_negPair
#print axioms bessel_identity_on_energy
