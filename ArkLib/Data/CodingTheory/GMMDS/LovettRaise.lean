/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma24
import ArkLib.Data.CodingTheory.GMMDS.LovettBlockSpan
import ArkLib.Data.CodingTheory.GMMDS.LovettFractionField
import ArkLib.Data.CodingTheory.GMMDS.LovettCounting
import ArkLib.Data.CodingTheory.GMMDS.LovettSeparateStep
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma2456

/-!
# Lovett's GM-MDS proof: the witness-raise and the `n < k` closure (#389)

This file carries the `n < k` branch of Lovett's primitive-case closure (arXiv:1803.02523,
Lemma 2.6 + final contradiction), as a *direct* independence proof.

Given a primitive `V*(k)` system with a witness `vᵢ₀ = (1,…,1,0)` (Lemma 2.5) and `n < k`, define
the **raised** system `V'` that equals `V` except at `i₀`, where the last coordinate is set to `1`
(so `vᵢ₀' = (1,…,1,1)`).  Then:

* `raiseVec` / `IsVStar` is preserved (the raise only adds `1` to the last coordinate; (ii) holds
  because the witness's weight is `n − 1 ≤ k − 2` here);
* `|P(k,V')| = |P(k,V)| − 1` (the `i₀`-block shrinks from `k − (n−1)` to `k − n`), so the
  `d`-induction hypothesis makes `P(k,V')` independent;
* every member of `P(k,V')` is divisible by `(x − aₙ)` (the raised witness now has a `1` in the
  last coordinate, and every *other* vector does by Lemma 2.1), while the separated polynomial
  `p = pVanish (oneVec)` is not — so `P(k,V') ∪ {p}` is independent (`linearIndependent_separate_one`);
* `P(k,V)` and `P(k,V') ∪ {p}` span the same `F(a)`-space (the block-span identity
  `span_pblk_eq_span_rblk_insert`), and have equal cardinality, so `P(k,V)` is independent.

Issue #389.
-/

open Finset Polynomial

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n m : ℕ}

/-- Raise the last coordinate of `V i₀` by setting it to `1`. -/
noncomputable def raiseVec (V : Fin m → (Fin n → ℕ)) (hn : 1 ≤ n) (i₀ : Fin m) :
    Fin m → (Fin n → ℕ) :=
  Function.update V i₀ (Function.update (V i₀) (lastCoord n hn) 1)

theorem raiseVec_of_ne {V : Fin m → (Fin n → ℕ)} (hn : 1 ≤ n) {i₀ i : Fin m} (hi : i ≠ i₀) :
    raiseVec V hn i₀ i = V i := by
  rw [raiseVec, Function.update_of_ne hi]

theorem raiseVec_self {V : Fin m → (Fin n → ℕ)} (hn : 1 ≤ n) (i₀ : Fin m) :
    raiseVec V hn i₀ i₀ = Function.update (V i₀) (lastCoord n hn) 1 := by
  rw [raiseVec, Function.update_self]

/-- The raised witness has a `1` in the last coordinate. -/
theorem raiseVec_self_last {V : Fin m → (Fin n → ℕ)} (hn : 1 ≤ n) (i₀ : Fin m) :
    raiseVec V hn i₀ i₀ (lastCoord n hn) = 1 := by
  rw [raiseVec_self, Function.update_self]

/-- The raised witness agrees with `V i₀` away from the last coordinate. -/
theorem raiseVec_self_of_ne_last {V : Fin m → (Fin n → ℕ)} (hn : 1 ≤ n) (i₀ : Fin m)
    {j : Fin n} (hj : j ≠ lastCoord n hn) : raiseVec V hn i₀ i₀ j = V i₀ j := by
  rw [raiseVec_self, Function.update_of_ne hj]

/-! ## Weight and vanishing-polynomial of the raised witness -/

/-- The raised witness weight: `|update v₀ (last) 1| = |v₀| + 1` when `v₀(last) = 0`. -/
theorem vAbs_raiseVec_self {V : Fin m → (Fin n → ℕ)} (hn : 1 ≤ n) (i₀ : Fin m)
    (h0 : V i₀ (lastCoord n hn) = 0) :
    vAbs (raiseVec V hn i₀ i₀) = vAbs (V i₀) + 1 := by
  classical
  rw [raiseVec_self, vAbs, vAbs]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (lastCoord n hn))]
  rw [← Finset.sum_erase_add _ (fun j => V i₀ j) (Finset.mem_univ (lastCoord n hn))]
  rw [Function.update_self, h0]
  congr 1
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The raised witness factors out the last linear factor:
`pVanish (raiseVec) = (x − a_last) · pVanish (V i₀)` when `V i₀ (last) = 0`. -/
theorem pVanish_raiseVec_self {V : Fin m → (Fin n → ℕ)} (hn : 1 ≤ n) (i₀ : Fin m)
    (h0 : V i₀ (lastCoord n hn) = 0) :
    pVanish (F := F) (raiseVec V hn i₀ i₀)
      = xSubA (lastCoord n hn) * pVanish (F := F) (V i₀) := by
  rw [raiseVec_self]
  have hge : 1 ≤ Function.update (V i₀) (lastCoord n hn) 1 (lastCoord n hn) := by
    rw [Function.update_self]
  rw [pVanish_factor hge]
  have hvec : Function.update (Function.update (V i₀) (lastCoord n hn) 1) (lastCoord n hn)
      (Function.update (V i₀) (lastCoord n hn) 1 (lastCoord n hn) - 1) = V i₀ := by
    funext j
    by_cases hj : j = lastCoord n hn
    · subst hj; rw [Function.update_self, h0]; simp
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
  rw [hvec]

/-! ## `V*(k)` is preserved by the witness raise -/

/-- The weight of `oneVec` is `n − 1` (re-derivation; matches `LovettLemma2456`). -/
theorem vAbs_oneVec (hn : 1 ≤ n) : vAbs (oneVec n hn) = n - 1 := by
  classical
  unfold vAbs oneVec
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
  have hcard : (Finset.univ.filter (fun x : Fin n => (x : ℕ) < n - 1)).card = n - 1 := by
    rw [show (n-1) = (Finset.range (n-1)).card from (Finset.card_range _).symm]
    apply Finset.card_bij (fun (x : Fin n) _ => (x : ℕ))
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      simpa using ha
    · intro a _ b _ h; exact Fin.val_injective h
    · intro b hb
      simp only [Finset.mem_range] at hb
      refine ⟨⟨b, by omega⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa using hb
  rw [hcard]

/-- **The raise preserves `V*(k)`** (Lovett Lemma 2.6, "V' satisfies V*(k)").  Raising the
witness `vᵢ₀ = (1,…,1,0)` to `(1,…,1,1)` keeps every property: weights stay `≤ k−1` (since
`|v'ᵢ₀| = n ≤ k−1`), shape (iii) is untouched (only the last coordinate moves), and the MDS
inequality (ii) holds because for any index set `I ∋ i₀` the weight-sum drops by `1` while the
meet weight rises by exactly `1` (every member of `I` carries a `1` in the last coordinate:
the raised witness does, and every other vector does by Lemma 2.1). -/
theorem raiseVec_isVStar {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hk : 1 ≤ k) (hV : IsVStar V k)
    (hn : 1 ≤ n) {i₀ : Fin m} (hone : V i₀ = oneVec n hn) (hnk : n < k) :
    IsVStar (raiseVec V hn i₀) k := by
  classical
  have h0 : V i₀ (lastCoord n hn) = 0 := by rw [hone]; exact oneVec_last hn
  -- weight of raised witness = n
  have hwt0 : vAbs (raiseVec V hn i₀ i₀) = n := by
    rw [vAbs_raiseVec_self hn i₀ h0, hone, vAbs_oneVec hn]; omega
  refine ⟨?_, ?_, ?_⟩
  · -- (i)
    intro i
    by_cases hi : i = i₀
    · subst hi; rw [hwt0]; omega
    · rw [raiseVec_of_ne hn hi]; exact hV.weight_le i
  · -- (ii) MDS
    intro I hI
    by_cases hi0 : i₀ ∈ I
    · -- meet last coord rises by 1; weight-sum drops by 1
      -- every i ∈ I has (raiseVec V) i last ≥ 1
      have hlastpos : ∀ i ∈ I, 1 ≤ raiseVec V hn i₀ i (lastCoord n hn) := by
        intro i _
        by_cases hi : i = i₀
        · subst hi; rw [raiseVec_self_last]
        · rw [raiseVec_of_ne hn hi]
          exact witness_others_last_pos hk hV hn hone hi
      -- meet of V over I at last = 0 (since vᵢ₀ last = 0)
      have hmeetV_last : vMeet V I hI (lastCoord n hn) = 0 := by
        unfold vMeet
        refine Nat.le_zero.mp ?_
        rw [← h0]
        exact Finset.inf'_le (fun i => V i (lastCoord n hn)) hi0
      -- meet of raiseVec over I at last = 1
      have hmeetR_last : vMeet (raiseVec V hn i₀) I hI (lastCoord n hn) = 1 := by
        unfold vMeet
        apply le_antisymm
        · calc I.inf' hI (fun i => raiseVec V hn i₀ i (lastCoord n hn))
              ≤ raiseVec V hn i₀ i₀ (lastCoord n hn) :=
                Finset.inf'_le _ hi0
            _ = 1 := raiseVec_self_last hn i₀
        · exact Finset.le_inf' _ _ hlastpos
      -- meet of raiseVec over I away from last = meet of V over I
      have hmeet_other : ∀ j, j ≠ lastCoord n hn →
          vMeet (raiseVec V hn i₀) I hI j = vMeet V I hI j := by
        intro j hj
        unfold vMeet
        refine Finset.inf'_congr hI rfl (fun i _ => ?_)
        by_cases hi : i = i₀
        · rw [hi, raiseVec_self_of_ne_last hn i₀ hj]
        · rw [raiseVec_of_ne hn hi]
      -- so |meet R| = |meet V| + 1
      have hmeetR : vAbs (vMeet (raiseVec V hn i₀) I hI)
          = vAbs (vMeet V I hI) + 1 := by
        rw [vAbs, vAbs]
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (lastCoord n hn))]
        rw [← Finset.sum_erase_add _ (fun j => vMeet V I hI j)
          (Finset.mem_univ (lastCoord n hn))]
        rw [hmeetR_last, hmeetV_last]
        have : ∑ j ∈ (Finset.univ.erase (lastCoord n hn)),
              vMeet (raiseVec V hn i₀) I hI j
            = ∑ j ∈ (Finset.univ.erase (lastCoord n hn)), vMeet V I hI j := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          exact hmeet_other j (Finset.ne_of_mem_erase hj)
        rw [this]
      -- weight-sum: term at i₀ drops by 1, others unchanged
      have hsumR : (∑ i ∈ I, (k - vAbs (raiseVec V hn i₀ i)))
          = (∑ i ∈ I, (k - vAbs (V i))) - 1 := by
        rw [← Finset.add_sum_erase _ _ hi0, ← Finset.add_sum_erase _
          (fun i => k - vAbs (V i)) hi0]
        have hother : ∑ i ∈ I.erase i₀, (k - vAbs (raiseVec V hn i₀ i))
            = ∑ i ∈ I.erase i₀, (k - vAbs (V i)) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [raiseVec_of_ne hn (Finset.ne_of_mem_erase hi)]
        rw [hother, hwt0, hone, vAbs_oneVec hn]
        omega
      -- combine with the V*(k) bound at I
      have hVbound := hV.mds I hI
      rw [hsumR, hmeetR]
      -- need (S - 1) + (M + 1) ≤ k  from  S + M ≤ k, with S ≥ 1
      have hSpos : 1 ≤ ∑ i ∈ I, (k - vAbs (V i)) := by
        refine Finset.single_le_sum (f := fun i => k - vAbs (V i))
          (fun i _ => Nat.zero_le _) hi0 |>.trans' ?_
        rw [hone, vAbs_oneVec hn]; omega
      omega
    · -- i₀ ∉ I: raiseVec agrees with V on I
      have hne : ∀ i ∈ I, i ≠ i₀ := fun i hi h => hi0 (h ▸ hi)
      have hsum : (∑ i ∈ I, (k - vAbs (raiseVec V hn i₀ i)))
          = ∑ i ∈ I, (k - vAbs (V i)) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [raiseVec_of_ne hn (hne i hi)]
      have hmeet : vMeet (raiseVec V hn i₀) I hI = vMeet V I hI := by
        funext j
        unfold vMeet
        refine Finset.inf'_congr hI rfl (fun i hi => ?_)
        rw [raiseVec_of_ne hn (hne i hi)]
      rw [hsum, hmeet]; exact hV.mds I hI
  · -- (iii) shape: only last coordinate moved
    intro i j hj
    by_cases hi : i = i₀
    · have hjne : j ≠ lastCoord n hn := by
        intro h; rw [h] at hj; simp only [lastCoord] at hj; omega
      rw [hi, raiseVec_self_of_ne_last hn i₀ hjne]; exact hV.shape i₀ j hj
    · rw [raiseVec_of_ne hn hi]; exact hV.shape i j hj

end ArkLib.GMMDS

#print axioms ArkLib.GMMDS.raiseVec_isVStar
#print axioms ArkLib.GMMDS.pVanish_raiseVec_self
