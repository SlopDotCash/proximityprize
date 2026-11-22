/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicFourPairPrime
import ArkLib.Research.ProximityGap.Frontier.ReflectionListThreshold
import ArkLib.Research.ProximityGap.Frontier.SmoothPowerOrbit

/-! # Three transpositions and the corresponding list boundary on arbitrary dyadic cosets -/

namespace ProximityGap.DyadicFourPairSmooth
open ReflectionListSampling Code
variable {I : Type} [Fintype I] {p : ℕ} [Fact p.Prime]

/-- A classification of disjoint pairs on a power orbit holds on every scaled, reindexed coset. -/
theorem dihedral_of_power (D : I ↪ ZMod p) [ReedSolomon.Smooth D] {m L : ℕ} (hn : Fintype.card I=2^m)
    (root_cap : ∀ (z : ZMod p), IsPrimitiveRoot z (2^m) → ∀ (g : Fin L × Fin 2 ↪ Fin (2^m))
      (a b c : ZMod p), a^2+b*c≠0 →
      (∀ i,c*z^(g (i,0)).val*z^(g (i,1)).val-a*(z^(g (i,0)).val+z^(g (i,1)).val)=b) →
      a=0 ∨ c=0 ∧ b=0) (q : Fin L × Fin 2 ↪ I) (a b c : ZMod p) (det : a^2+b*c≠0)
    (law : ∀ i, c*D (q (i,0))*D (q (i,1))-a*(D (q (i,0))+D (q (i,1)))=b) : a=0 ∨ c=0 ∧ b=0 := by
  obtain ⟨z,s,f,hz,hD⟩ := SmoothPowerOrbit.reindex D hn
  let g := q.trans f.toEmbedding
  have det' : (a*(s:ZMod p))^2+b*(c*(s:ZMod p)^2)≠0 := by
    rw [show (a*(s:ZMod p))^2+b*(c*(s:ZMod p)^2)=(a^2+b*c)*(s:ZMod p)^2 by ring]
    exact mul_ne_zero det (pow_ne_zero _ s.ne_zero)
  have law' (i : Fin L) : c*(s:ZMod p)^2*z^(g (i,0)).val*z^(g (i,1)).val-
      (a*(s:ZMod p))*(z^(g (i,0)).val+z^(g (i,1)).val)=b := by
    have h := law i
    simp only [hD] at h
    change c*(s:ZMod p)^2*z^(f (q (i,0))).val*z^(f (q (i,1))).val-
      (a*(s:ZMod p))*(z^(f (q (i,0))).val+z^(f (q (i,1))).val)=b
    linear_combination h
  rcases root_cap z hz g _ b _ det' law' with h|⟨h,hb⟩
  · exact Or.inl ((mul_eq_zero.mp h).resolve_right s.ne_zero)
  · exact Or.inr ⟨(mul_eq_zero.mp h).resolve_right (pow_ne_zero _ s.ne_zero),hb⟩

/-- On every ordering of a smooth coset in the height-12 field range, four
disjoint transpositions force the involution to be dihedral. -/
theorem dihedral (D : I ↪ ZMod p) [ReedSolomon.Smooth D] {m : ℕ} (hn : Fintype.card I=2^m)
    (large : 12^(2^m).totient<p^2) (q : Fin 4 × Fin 2 ↪ I) (a b c : ZMod p) (det : a^2+b*c≠0)
    (law : ∀ i, c*D (q (i,0))*D (q (i,1))-a*(D (q (i,0))+D (q (i,1)))=b) : a=0 ∨ c=0 ∧ b=0 :=
  dihedral_of_power D hn (fun _ hz => DyadicFourPairPrime.dihedral hz large) q a b c det law

/-- Three is the row cap at every dyadic order satisfying the pair norm test. -/
theorem cap [DecidableEq I] (D : I ↪ ZMod p) [ReedSolomon.Smooth D] {m : ℕ} (hn : Fintype.card I=2^m)
    (large : 12^(2^m).totient<p^2) : PairCap D 3 := by
  obtain ⟨e,he⟩ := SmoothDomainMcaEquivalence.coset_equiv D
  exact pairCap_of_involutions D (by decide)
    (fun i => he i ▸ mul_ne_zero (ReedSolomon.Smooth.a D).ne_zero (e i).val.ne_zero) (dihedral D hn large)

/-- The first list-budget violation is n−k−1 on the explicit three-pair
budget interval. Width and ordering of the coset are arbitrary. -/
theorem threshold [DecidableEq I] (D : I ↪ ZMod p) [ReedSolomon.Smooth D] {e k r B : ℕ}
    [NeZero k] (hn : Fintype.card I=2^e) (large : 12^(2^e).totient<p^2) (length : 2^e=k+3+r)
    (hr : 2≤r) (payment : r≤k ∨ ((r+1).choose 2-(r+1)/2)*(k+2)≤2*(2*k+2).choose (k+1))
    (upper : bound k r 3≤B) (lower : (k+3+r)*B < (k+3+r).choose (k+1)) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    Lambda (interleavedCodeSet (κ:=Fin m) (ReedSolomon.code D k : Set (I → ZMod p))) δ ≤ (B : ℕ∞) ↔
    δ < ((r+2 : ℕ):ℝ)/(Fintype.card I:ℝ) :=
  threshold_of_payment D (hn.trans length) hr (endpoint_payment_wide payment) (cap D hn large) (by decide)
    upper lower m hm δ

end ProximityGap.DyadicFourPairSmooth
#print axioms ProximityGap.DyadicFourPairSmooth.threshold
