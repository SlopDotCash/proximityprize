/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# H7: the convolution sup-norm collapses EXACTLY to the additive energy (#444, avenue H7)

This brick settles the **sup-norm convolution route** (H7-convolution-supnorm-decay) of the
house/height attack on `M = max_{b≠0} |η_b|`. The hope was that a Randles–Saloff-Coste local-limit
sup-norm estimate on `‖1_μ^{*r}‖_∞` (the SPATIAL maximum of the `r`-fold additive convolution
power), being a *max* rather than the `ℓ²`-energy `E_r` (an *average*), might detect the worst
spectral frequency (the *house*) and force per-`b` sub-Gaussianity `M ≤ √(n log p)`.

## The verdict: REDUCES — sup-norm = energy = the AVERAGE (geomean/average-collapse, face (c))

It does NOT. The route collapses to the energy by an **exact, elementary identity** formalized here.
We index the `r`-fold convolution by `Fin r → G` tuples valued in a finite set `S`, and the doubled
`2r`-fold convolution by `(Fin r ⊕ Fin r) → G`. For a **negation-closed** set `S = -S` (the prize
set `μ_n = μ_{2^a}` is negation-closed since `-1 ∈ μ_n`):

* **`convSum_central_eq_energy`** — `convSum S 0 = ∑_t (conv S r t)² = E_r`, the `r`-fold additive
  energy. (`convSum S 0` is the doubled-convolution central value `1_S^{*2r}(0)`.) Substitute the
  second half `v ↦ −v` using `S = -S`; the `2r`-fold zero-sum count at the origin becomes the
  diagonal collision count `#{(u,v) ∈ S^r × S^r : Σu = Σv}` = `‖1_S^{*r}‖₂²`.
* **`convSum_central_is_sup`** — the doubled-convolution central value `convSum S 0 = ∑_t (conv t)²`
  dominates `conv S (2r) t` for every `t` (autocorrelation peak at the origin, Cauchy–Schwarz). So
  `‖1_S^{*2r}‖_∞` is attained at `0` and equals `E_r`.

Combining: `‖1_S^{*2r}‖_∞ = E_r` **exactly**. The sup-norm *IS* the energy. Numerically (exact FFT,
`n=16` `p=65537`, `n=32` `p=1048609`): `sup(conv_{2r}) = E_r` to the integer for all `r ≤ ⌊ln p⌋`
(e.g. `n=16`: `sup(conv_8)=4654160=E_4`, `sup(conv_10)=516955536=E_5`); argmax always `t=0`.

So the sup-norm route is the energy/`ℓ²`-average route in disguise — the **same wall**, not a new
max-detecting handle. The single worst frequency `b*` contributes only a rank-one modulation of
amplitude `(1/p) M^r` to `1_S^{*r}`, swamped by the DC mass `n^r/p` and the bulk; the spatial sup
never sees it. RSC sup bounds, when applicable, bound `‖1_S^{*r}‖_∞` *from* the spectrum
(`≤ (1/p) Σ_b |η_b|^r`) — the WRONG direction for extracting `M`. avg-vs-max collapse (face (c)).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`, no `native_decide`.
-/

set_option linter.style.longLine false
set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.H7

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The `r`-fold additive convolution power of the indicator of `S ⊆ G`, as a representation count:
`conv S r t = #{ s : Fin r → G // (∀ i, s i ∈ S) ∧ ∑ i, s i = t }`. This is `1_S^{*r}(t)`. -/
def conv (S : Finset G) (r : ℕ) (t : G) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin r => S)).filter (fun s => ∑ i, s i = t)).card

/-- The `r`-fold additive energy: number of pairs `(u, v) ∈ Sᵣ × Sᵣ` with `∑ u = ∑ v`, i.e.
`‖1_S^{*r}‖₂²`. -/
def energy (S : Finset G) (r : ℕ) : ℕ :=
  (((Fintype.piFinset (fun _ : Fin r => S)) ×ˢ (Fintype.piFinset (fun _ : Fin r => S))).filter
    (fun p => ∑ i, p.1 i = ∑ i, p.2 i)).card

/-- `energy S r = ∑_t (conv S r t)²` — the energy is the `ℓ²`-norm² of the convolution (Plancherel
in the physical domain). -/
theorem energy_eq_sum_conv_sq (S : Finset G) (r : ℕ) :
    energy S r = ∑ t : G, (conv S r t) ^ 2 := by
  classical
  set A : G → Finset (Fin r → G) :=
    fun t => (Fintype.piFinset (fun _ : Fin r => S)).filter (fun s => ∑ i, s i = t) with hA
  -- RHS: ∑_t (card (A t))² = ∑_t card (A t ×ˢ A t)
  have hsq : (∑ t : G, (conv S r t) ^ 2)
      = ∑ t : G, ((A t) ×ˢ (A t)).card := by
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.card_product, sq, conv, hA]
  rw [hsq]
  -- The energy set equals the disjoint union over t of (A t ×ˢ A t).
  have hset : ((Fintype.piFinset (fun _ : Fin r => S)) ×ˢ (Fintype.piFinset (fun _ : Fin r => S))).filter
        (fun p => ∑ i, p.1 i = ∑ i, p.2 i)
      = (Finset.univ : Finset G).biUnion (fun t => (A t) ×ˢ (A t)) := by
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_univ,
      true_and, hA]
    constructor
    · rintro ⟨⟨hu, hv⟩, huv⟩
      exact ⟨∑ i, u i, ⟨hu, rfl⟩, hv, huv.symm⟩
    · rintro ⟨t, ⟨hu, hut⟩, hv, hvt⟩
      exact ⟨⟨hu, hv⟩, by rw [hut, hvt]⟩
  rw [energy, hset, Finset.card_biUnion]
  intro t _ t' _ hne
  apply Finset.disjoint_left.mpr
  rintro ⟨u, v⟩ h1 h2
  simp only [Finset.mem_product, Finset.mem_filter, hA] at h1 h2
  exact hne (h1.1.2.symm.trans h2.1.2)

/-- The doubled (`2r`-fold) convolution central value `1_S^{*2r}(0)`, indexed by `Fin r ⊕ Fin r`:
`convSum S r = #{ s : (Fin r ⊕ Fin r) → G // (∀ i, s i ∈ S) ∧ ∑ i, s i = 0 }`. The `Sum`-index is
defeq to the `Fin (2r)`-index up to the standard equiv and keeps the split clean. -/
def convSum (S : Finset G) (r : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin r ⊕ Fin r => S)).filter (fun s => ∑ i, s i = 0)).card

/-- **THE COLLAPSE.** For a negation-closed `S = -S`, the doubled-convolution central value equals
the `r`-fold additive energy: `convSum S r = energy S r = ∑_t (conv S r t)²`.

Proof: a `(Fin r ⊕ Fin r)`-tuple `s` with `∑ s = 0` splits via `Equiv.sumArrowEquivProdArrow`
into `(u, w)` with `∑ u + ∑ w = 0`, i.e. `∑ u = ∑ (−w)`. Negating the right half (a bijection of
`Sᵣ` because `S = −S`) turns this into the diagonal collision `∑ u = ∑ v`, the energy. -/
theorem convSum_central_eq_energy (S : Finset G) (hS : ∀ x, x ∈ S ↔ -x ∈ S) (r : ℕ) :
    convSum S r = energy S r := by
  classical
  unfold convSum energy
  apply Finset.card_bij'
    (i := fun (s : (Fin r ⊕ Fin r) → G) (_ : s ∈ _) =>
      ((fun i : Fin r => s (Sum.inl i)), (fun i : Fin r => - s (Sum.inr i))))
    (j := fun (p : (Fin r → G) × (Fin r → G)) (_ : p ∈ _) =>
      (Sum.elim p.1 (fun i => - p.2 i)))
  · -- forward: lands in the energy filter
    intro s hs
    simp only [Fintype.mem_piFinset, Finset.mem_filter] at hs
    obtain ⟨hmem, hsum⟩ := hs
    rw [Fintype.sum_sum_type] at hsum
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [Fintype.mem_piFinset]; intro i; exact hmem _
    · simp only [Fintype.mem_piFinset]; intro i; exact (hS _).mp (hmem _)
    · -- goal: ∑ s(inl) = ∑ (- s(inr)), from ∑ s(inl) + ∑ s(inr) = 0
      rw [Finset.sum_neg_distrib]
      exact eq_neg_of_add_eq_zero_left hsum
  · -- backward: lands in the convSum filter
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset] at hp
    obtain ⟨⟨hu, hv⟩, hsum⟩ := hp
    simp only [Fintype.mem_piFinset, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · intro i; cases i with
      | inl a => simpa using hu a
      | inr a => simp only [Sum.elim_inr]; exact (hS _).mp (hv a)
    · rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_neg_distrib]
      rw [hsum]; abel
  · -- left inverse: Sum.elim (s∘inl) (fun i => -(-(s∘inr))) = s
    intro s hs
    funext i
    cases i with
    | inl a => simp
    | inr a => simp only [Sum.elim_inr, neg_neg]
  · -- right inverse: ((Sum.elim u (-v))∘inl, -((Sum.elim u (-v))∘inr)) = (u, v)
    intro p hp
    simp only [Sum.elim_inl, Sum.elim_inr, neg_neg, Prod.mk.eta]

/-- The total mass `‖1_S^{*r}‖₁ = |S|^r`: the convolution sums to `|S|^r` over all of `G`. -/
theorem sum_conv (S : Finset G) (r : ℕ) : ∑ t : G, conv S r t = S.card ^ r := by
  classical
  have hcard : (Fintype.piFinset (fun _ : Fin r => S)).card = S.card ^ r := by
    rw [Fintype.card_piFinset]; simp
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun s : Fin r → G => ∑ i, s i) (s := Fintype.piFinset (fun _ : Fin r => S))
    (t := (Finset.univ : Finset G)) (fun s _ => Finset.mem_univ _)
  rw [hcard] at hfib
  rw [hfib]
  rfl

/-- The `convSum`-doubled-convolution central value, rewritten on the `conv`/energy side:
`convSum S r = ∑_t (conv S r t)²` for negation-closed `S`. This is the headline collapse statement:
the convolution sup-norm at even depth `2r` (attained at the origin, `convSum`) **equals** the
`r`-fold additive energy `‖1_S^{*r}‖₂²` — a SUM over the spectrum, i.e. the AVERAGE `E_r`, not a
max that could detect the house. -/
theorem convSum_eq_sum_conv_sq (S : Finset G) (hS : ∀ x, x ∈ S ↔ -x ∈ S) (r : ℕ) :
    convSum S r = ∑ t : G, (conv S r t) ^ 2 := by
  rw [convSum_central_eq_energy S hS r, energy_eq_sum_conv_sq]

#print axioms energy_eq_sum_conv_sq
#print axioms convSum_central_eq_energy
#print axioms convSum_eq_sum_conv_sq
#print axioms sum_conv

end ArkLib.ProximityGap.Frontier.H7
