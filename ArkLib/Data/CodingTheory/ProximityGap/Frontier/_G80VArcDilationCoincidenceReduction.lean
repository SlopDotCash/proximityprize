/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80WArcPairCountIdentity

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# LANE G80V (#466, 2026-07-10): the DILATION-COINCIDENCE reduction — the b-averaged same-arc
  pair count factors EXACTLY through n evaluations of the Fourier-free floor object
  `R(d) = #{v ≠ 0 : arcIndex(dv) = arcIndex(v)}` (axiom-clean exact identities).

## The reduction

G80W pinned the pair-form certificate: bound the same-arc pair count of `b·μ_n` for EVERY
dilation `b`. This lane proves the exact orbit-average structure of that object. For a
multiplicatively closed `H ⊆ (ZMod p)^*` (`|H| = n`):

* `pair_decomposition` : for every `b`, the same-arc pair count of `b·H` decomposes EXACTLY
  as `Σ_{d ∈ H} #{y ∈ H : arcIndex(b·d·y) = arcIndex(b·y)}` — pairs are indexed by their
  ratio `d = x/y ∈ H`.
* `grand_dilation_identity` : summing over ALL dilations `b ≠ 0`,
  `Σ_{b≠0} pairCount(b·H) = |H| · Σ_{d∈H} R(d)`, where
  `R(d) := #{v ≠ 0 : arcIndex(d·v) = arcIndex(v)}` is the DILATION-COINCIDENCE count — a pure
  floor/lattice (Steinhaus three-distance–type) quantity with NO Fourier and NO subgroup
  content: the subgroup enters ONLY through which `n` points `d ∈ H` are sampled.
* `dilCoincidence_one` : `R(1) = p − 1` (the diagonal term).
* `grand_upper_of_R_bound` : if `R(d) ≤ ρ` for the `n − 1` nontrivial ratios `d ∈ H \ {1}`,
  then `Σ_{b≠0} pairCount ≤ |H|·((p−1) + (|H|−1)·ρ)` — the b-AVERAGED pair certificate holds
  with excess governed by `ρ` alone.

Probe (`scratchpad/probe_g80v.py`, five cells up to `n=32, p=1153, K=16`): identity EXACT
everywhere; `R(1) = p−1` exact; on `μ_n \ {1}` the coincidence counts are near-generic —
`max R/(p/K) ∈ [1.00, 1.50]`, no subgroup anomaly. So the b-averaged certificate is REAL with
`ρ ≈ p/K` (mean pair excess `≈ n + n²·(R̄·K/p)/K ≈ n + O(n²/K)`).

## Honest scope

The b-AVERAGE is not the max: the prize needs the pair certificate at EVERY `b` (equivalently
the sup over `b` of the per-orbit coincidence sum `Σ_{d∈H} #{y ∈ H : …}`, where `y` ranges
over the SUBGROUP, not over all `v`) — averaging frees `y` to sweep `F_p^*` and is exactly
where max-vs-mean (the wall) hides. What is new here: (i) the certificate's average form
reduces to `n` evaluations of a classical Fourier-free lattice function `R`, (ii) `R` on
subgroup points is measured near-generic, and (iii) any future pointwise-in-`b` version of the
`R`-reduction inherits a ready consumer chain (G80W → G80Y → G80X). CORE remains OPEN /
ON-BGK. No axioms, no sorry.

Issue #466. Axiom-clean.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G80VArcDilationCoincidenceReduction

open ArkLib.ProximityGap.Frontier.G80ZArcArithmeticInstantiation

variable {p : ℕ} [Fact p.Prime] [NeZero p]

/-- The dilation-coincidence count: how many nonzero `v` keep their arc under dilation by
`d`. A pure floor/lattice object — no Fourier, no subgroup. -/
def dilCoincidence (p : ℕ) [NeZero p] (K : ℕ) (d : ZMod p) : ℕ :=
  ((Finset.univ.erase (0 : ZMod p)).filter
    (fun v => arcIndex K (d * v) = arcIndex K v)).card

variable (H : Finset (ZMod p)) (h0 : (0 : ZMod p) ∉ H)
  (hdiv : ∀ x ∈ H, ∀ y ∈ H, x * y⁻¹ ∈ H)
  (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)

include h0 hdiv hmul in
/-- **Ratio decomposition of the same-arc pair count**: pairs `(x, y) ∈ H²` are indexed
exactly by their ratio `d = x·y⁻¹ ∈ H` and second coordinate. -/
theorem pair_decomposition (K : ℕ) (b : ZMod p) :
    ((H ×ˢ H).filter
        (fun q => arcIndex K (b * q.1) = arcIndex K (b * q.2))).card
      = ∑ d ∈ H,
          (H.filter (fun y => arcIndex K (b * (d * y)) = arcIndex K (b * y))).card := by
  have hpart : (H ×ˢ H).filter
      (fun q => arcIndex K (b * q.1) = arcIndex K (b * q.2))
      = H.biUnion (fun d =>
          (H.filter (fun y => arcIndex K (b * (d * y)) = arcIndex K (b * y))).image
            (fun y => (d * y, y))) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_product, mem_biUnion, mem_image]
    constructor
    · rintro ⟨⟨hx, hy⟩, hcond⟩
      have hy0 : y ≠ 0 := fun h => h0 (h ▸ hy)
      have hxy : x * y⁻¹ * y = x := by field_simp
      exact ⟨x * y⁻¹, hdiv x hx y hy, y, ⟨hy, by rw [hxy]; exact hcond⟩, by rw [hxy]⟩
    · rintro ⟨d, hd, y', ⟨hy', hcond⟩, heq⟩
      have hfirst : d * y' = x := congrArg Prod.fst heq
      have hsecond : y' = y := congrArg Prod.snd heq
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [← hfirst]
        exact hmul d hd y' hy'
      · rw [← hsecond]
        exact hy'
      · rw [← hfirst, ← hsecond]
        exact hcond
  rw [hpart, Finset.card_biUnion ?_]
  · exact Finset.sum_congr rfl fun d _ =>
      Finset.card_image_of_injective _ (fun a b' hab => by
        injection hab with h1 h2)
  · intro d hd d' hd' hne
    refine Finset.disjoint_left.mpr ?_
    rintro ⟨u, v⟩ hmem hmem'
    simp only [mem_image, mem_filter] at hmem hmem'
    obtain ⟨y1, ⟨hy1, _⟩, heq1⟩ := hmem
    obtain ⟨y2, ⟨hy2, _⟩, heq2⟩ := hmem'
    injection heq1 with hu1 hv1
    injection heq2 with hu2 hv2
    have hv0 : v ≠ 0 := fun h => h0 (h ▸ (hv1 ▸ hy1))
    have h1' : d * v = u := by rw [← hv1]; exact hu1
    have h2' : d' * v = u := by rw [← hv2]; exact hu2
    exact hne (mul_right_cancel₀ hv0 (h1'.trans h2'.symm))

/-- **Orbit sweep**: for fixed nonzero `y` and ratio `d`, summing the coincidence indicator
over all dilations `b ≠ 0` gives exactly `R(d)` — substituting `v = b·y` sweeps `F_p^*`. -/
theorem sum_dilations_eq_dilCoincidence (K : ℕ) (d y : ZMod p) (hy : y ≠ 0) :
    ∑ b ∈ Finset.univ.erase (0 : ZMod p),
      (if arcIndex K (b * (d * y)) = arcIndex K (b * y) then 1 else 0)
      = dilCoincidence p K d := by
  rw [dilCoincidence, Finset.card_filter]
  refine Finset.sum_nbij' (fun b => b * y) (fun v => v * y⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hb ⊢
    exact mul_ne_zero hb hy
  · intro v hv
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hv ⊢
    exact mul_ne_zero hv (inv_ne_zero hy)
  · intro b _
    field_simp
  · intro v _
    field_simp
  · intro b _
    rw [show b * (d * y) = d * (b * y) by ring]

include h0 hdiv hmul in
/-- **The grand dilation identity**: the b-averaged same-arc pair count of the orbit `b·H`
factors exactly through the dilation-coincidence counts at the `|H|` ratios. -/
theorem grand_dilation_identity (K : ℕ) :
    ∑ b ∈ Finset.univ.erase (0 : ZMod p),
      ((H ×ˢ H).filter
        (fun q => arcIndex K (b * q.1) = arcIndex K (b * q.2))).card
      = H.card * ∑ d ∈ H, dilCoincidence p K d := by
  have hstep : ∀ b ∈ Finset.univ.erase (0 : ZMod p),
      ((H ×ˢ H).filter
        (fun q => arcIndex K (b * q.1) = arcIndex K (b * q.2))).card
        = ∑ d ∈ H,
            (H.filter (fun y => arcIndex K (b * (d * y)) = arcIndex K (b * y))).card :=
    fun b _ => pair_decomposition H h0 hdiv hmul K b
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hswap : ∑ b ∈ Finset.univ.erase (0 : ZMod p),
      (H.filter (fun y => arcIndex K (b * (d * y)) = arcIndex K (b * y))).card
      = ∑ y ∈ H, ∑ b ∈ Finset.univ.erase (0 : ZMod p),
          (if arcIndex K (b * (d * y)) = arcIndex K (b * y) then 1 else 0) := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  have hinner : ∀ y ∈ H,
      ∑ b ∈ Finset.univ.erase (0 : ZMod p),
        (if arcIndex K (b * (d * y)) = arcIndex K (b * y) then 1 else 0)
        = dilCoincidence p K d := by
    intro y hy
    exact sum_dilations_eq_dilCoincidence K d y (fun h => h0 (h ▸ hy))
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]

/-- The diagonal term: dilation by `1` keeps every arc, `R(1) = p − 1`. -/
theorem dilCoincidence_one (K : ℕ) : dilCoincidence p K 1 = p - 1 := by
  rw [dilCoincidence]
  have : (Finset.univ.erase (0 : ZMod p)).filter
      (fun v => arcIndex K ((1 : ZMod p) * v) = arcIndex K v)
      = Finset.univ.erase (0 : ZMod p) := by
    refine Finset.filter_true_of_mem fun v _ => ?_
    rw [one_mul]
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

include h0 hdiv hmul in
/-- **The b-averaged pair certificate from an `R`-bound**: if the coincidence count is at
most `ρ` at every nontrivial ratio of `H`, the summed pair count obeys the exact budget
`|H|·((p−1) + (|H|−1)·ρ)`. -/
theorem grand_upper_of_R_bound (K : ℕ) (ρ : ℕ) (h1 : (1 : ZMod p) ∈ H)
    (hR : ∀ d ∈ H, d ≠ 1 → dilCoincidence p K d ≤ ρ) :
    ∑ b ∈ Finset.univ.erase (0 : ZMod p),
      ((H ×ˢ H).filter
        (fun q => arcIndex K (b * q.1) = arcIndex K (b * q.2))).card
      ≤ H.card * ((p - 1) + (H.card - 1) * ρ) := by
  rw [grand_dilation_identity H h0 hdiv hmul K]
  refine Nat.mul_le_mul_left _ ?_
  rw [← Finset.add_sum_erase _ _ h1, dilCoincidence_one]
  have hcard : (H.erase 1).card = H.card - 1 := Finset.card_erase_of_mem h1
  calc (p - 1) + ∑ d ∈ H.erase 1, dilCoincidence p K d
      ≤ (p - 1) + ∑ _d ∈ H.erase 1, ρ := by
        gcongr with d hd
        exact hR d (Finset.mem_of_mem_erase hd) (Finset.ne_of_mem_erase hd)
    _ = (p - 1) + (H.card - 1) * ρ := by
        rw [Finset.sum_const, smul_eq_mul, hcard]

end ArkLib.ProximityGap.Frontier.G80VArcDilationCoincidenceReduction

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80VArcDilationCoincidenceReduction.pair_decomposition
#print axioms
  ArkLib.ProximityGap.Frontier.G80VArcDilationCoincidenceReduction.sum_dilations_eq_dilCoincidence
#print axioms
  ArkLib.ProximityGap.Frontier.G80VArcDilationCoincidenceReduction.grand_dilation_identity
#print axioms
  ArkLib.ProximityGap.Frontier.G80VArcDilationCoincidenceReduction.dilCoincidence_one
#print axioms
  ArkLib.ProximityGap.Frontier.G80VArcDilationCoincidenceReduction.grand_upper_of_R_bound
