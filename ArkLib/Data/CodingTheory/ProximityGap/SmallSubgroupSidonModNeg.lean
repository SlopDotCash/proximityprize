/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.SmallSubgroupSidon
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg

open Polynomial
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

/-- **The small-subgroup δ\* input, stated literally.** For a primitive `n`-th root `ζ ∈ ZMod p`
(`p` prime, `p > 2`) with `p > 4^{φ(n)} = 2^n`, the `n`-th roots of unity `μ_n ⊆ F_p` are
`SidonModNeg`: no nontrivial additive parallelogram. -/
theorem smallSubgroup_sidonModNeg {n : ℕ} (hn : 0 < n) {p : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n) (hbig : 4 ^ n.totient < p) :
    SidonModNeg (Finset.univ.filter (fun x : ZMod p => x ^ n = 1)) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  intro a ha b hb c hc d hd hsum
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, hab0⟩ := hcon
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc hd
  obtain ⟨a', ha'lt, ha'⟩ := hζ.eq_pow_of_pow_eq_one ha
  obtain ⟨b', hb'lt, hb'⟩ := hζ.eq_pow_of_pow_eq_one hb
  obtain ⟨c', hc'lt, hc'⟩ := hζ.eq_pow_of_pow_eq_one hc
  obtain ⟨d', hd'lt, hd'⟩ := hζ.eq_pow_of_pow_eq_one hd
  subst ha' hb' hc' hd'
  have hdist : ¬ ((a' = c' ∧ b' = d') ∨ (a' = d' ∧ b' = c')) := by
    rintro (⟨e1, e2⟩ | ⟨e1, e2⟩)
    · exact h1 (by rw [e1]) (by rw [e2])
    · exact h2 (by rw [e1]) (by rw [e2])
  exact absurd
    (prime_le_of_zeta_parallelogram hn hp2 hζ ha'lt hb'lt hc'lt hd'lt hsum hab0 hdist)
    (by omega)
