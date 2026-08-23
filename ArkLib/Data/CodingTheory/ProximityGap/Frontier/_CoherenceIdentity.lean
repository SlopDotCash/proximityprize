/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Coherence identity — the RIP / compressed-sensing NO-GO (#407/#444)

**Negative guardrail (exotic-math sweep).** This file proves the route *"bound the prize sup-norm
`M(n)` by invoking restricted-isometry-property (RIP) / compressed-sensing machinery on the DFT
submatrix"* is **structurally consuming, not producing**: the prize quantity `M(n)` IS *exactly*
the mutual coherence of that submatrix, and the RIP constant `δ_k` has the coherence as a **lower**
bound. So any RIP statement *consumes* `M(n)` as an input; it cannot *produce* the `√(log)`
cancellation. It does **not** close the prize — the `L^∞` `√(log)` core (the BGK/Paley wall)
survives. See #407, #444, and the exotic sweep.

## The math

The prize sup-norm is `M(n) = max_{d≠0} ‖η_d‖`, `η_d = Σ_{x∈μ_n} ψ(d·x)` (additive character
`ψ = e_p`). Form the DFT submatrix `Φ` with columns `φ_b`, `φ_b[x] = ψ(b·x)` (`x ∈ μ_n`).

**(1) Column-difference invariance** (the load-bearing identity, `inner_phi_eq_eta`):
`⟨φ_b, φ_{b'}⟩ = Σ_{x∈μ_n} conj(ψ(b·x))·ψ(b'·x) = Σ_{x∈μ_n} ψ((b'−b)·x) = η_{b'−b}`,
so the Gram entry depends only on `d = b'−b`. Hence the mutual coherence

> `coherence(Φ) = max_{b≠b'} ‖⟨φ_b,φ_{b'}⟩‖ = max_{d≠0} ‖η_d‖ = M(n)` (`coherence_eq_M`).

**(2) RIP floor** (monotonicity, `coherence_le_rip`): `δ_k(Φ)` is the sup over a *nested* family of
support sets (the `k`-subsets), so `δ_k ≥ δ_2` for `k ≥ 2`, and `δ_2 = coherence`. Hence every RIP
constant is `≥ coherence = M(n)/n`. RIP *consumes* `M(n)`; it cannot generate the cancellation.

## Honesty (project §6)

This is a **NEGATIVE** brick. The genuine new content is the coherence IDENTITY `coherence_eq_M`
(column-difference invariance is exact, axiom-clean). The RIP-floor part is a one-line abstract
monotonicity wrapper (`Finset.sup'` over nested index sets): it records that RIP has `coherence`
as a floor, hence cannot *produce* the prize, only consume it. It does **NOT** prove
`M(n) ≤ C√(n log q)` — that `L^∞` factor is the open BGK/Paley-conjecture core. All theorems are
`sorry`-free and axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

The self-contained `phi`/`eta` here matches the in-tree
`ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G d = Σ_{y∈G} ψ(d·y)`; `inner_phi_eq_eta`
identifies the Gram entry with that `eta`.

## References
- [Donoho–Stark, Tropp] mutual coherence ≥ RIP floor (`δ_2 = coherence`, `δ_k ≥ δ_2`).
- [BGK] Bourgain–Glibichuk–Konyagin — the best proven incomplete-character-sum bound (the wall).
- #407, #444, the exotic-math sweep.
-/

set_option linter.style.longLine false


open Finset AddChar

namespace ProximityGap.Frontier.CoherenceIdentity

variable {F : Type*} [Field F]

/-- The subgroup Gauss sum at frequency `d`: `η_d = Σ_{x∈G} ψ(d·x)` (matches the in-tree
`SubgroupGaussSumSecondMoment.eta`). -/
noncomputable def eta (ψ : AddChar F ℂ) (G : Finset F) (d : F) : ℂ := ∑ x ∈ G, ψ (d * x)

/-- The DFT submatrix column `φ_b` at frequency `b`, as a function on the domain `G`:
`φ_b[x] = ψ(b·x)`. -/
noncomputable def phi (ψ : AddChar F ℂ) (b : F) : F → ℂ := fun x => ψ (b * x)

/-- The (Hermitian) inner product of two columns restricted to the domain `G`:
`⟨φ_b, φ_{b'}⟩ = Σ_{x∈G} conj(φ_b x)·φ_{b'} x`. -/
noncomputable def innerPhi (ψ : AddChar F ℂ) (G : Finset F) (b b' : F) : ℂ :=
  ∑ x ∈ G, (starRingEnd ℂ) (phi ψ b x) * phi ψ b' x

/-- **Column-difference invariance — the load-bearing identity.** For any additive
character `ψ`, the Gram entry of two DFT columns over the subgroup domain `G` depends only on the
frequency *difference*: `⟨φ_b, φ_{b'}⟩ = η_{b'−b}`. Proof: `conj(ψ(b·x))·ψ(b'·x) = ψ(−b·x)·ψ(b'·x)
= ψ((b'−b)·x)` by additivity, then sum over `x ∈ G`. This is the structural reason the mutual
coherence collapses to the single-difference sup-norm `M(n)`. (Only character additivity and the
positive ring characteristic are needed — not primitivity of `ψ`.) -/
theorem inner_phi_eq_eta [Finite F] {ψ : AddChar F ℂ} (G : Finset F) (b b' : F) :
    innerPhi ψ G b b' = eta ψ G (b' - b) := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  rw [innerPhi, eta]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [phi]
  rw [AddChar.starComp_apply hchar, AddChar.inv_apply, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The **coherence** of the DFT submatrix over `G`: the max Gram-entry magnitude over distinct
column pairs `b ≠ b'`, taken over the (nonempty) index set of pairs. -/
noncomputable def coherence [Fintype F] [DecidableEq F] (ψ : AddChar F ℂ) (G : Finset F)
    (hpair : (Finset.univ.filter (fun p : F × F => p.1 ≠ p.2)).Nonempty) : ℝ :=
  (Finset.univ.filter (fun p : F × F => p.1 ≠ p.2)).sup' hpair
    (fun p => ‖innerPhi ψ G p.1 p.2‖)

/-- The prize **sup-norm** `M(n) = max_{d≠0} ‖η_d‖`, taken over the (nonempty) nonzero frequencies. -/
noncomputable def M [Fintype F] [DecidableEq F] (ψ : AddChar F ℂ) (G : Finset F)
    (hd : (Finset.univ.filter (fun d : F => d ≠ 0)).Nonempty) : ℝ :=
  (Finset.univ.filter (fun d : F => d ≠ 0)).sup' hd (fun d => ‖eta ψ G d‖)

/-- The value-set of column-pair coherences equals the value-set of nonzero-frequency sup-norms.
The map `(b,b') ↦ b'−b` sends distinct pairs onto nonzero differences bijectively-on-values, and
`inner_phi_eq_eta` rewrites each entry. This is the set-level core of `coherence_eq_M`. -/
theorem coherence_image_eq_M_image [Fintype F] [DecidableEq F] (ψ : AddChar F ℂ) (G : Finset F) :
    (Finset.univ.filter (fun p : F × F => p.1 ≠ p.2)).image
        (fun p => ‖innerPhi ψ G p.1 p.2‖)
      = (Finset.univ.filter (fun d : F => d ≠ 0)).image (fun d => ‖eta ψ G d‖) := by
  ext v
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p.2 - p.1, ?_, ?_⟩
    · exact sub_ne_zero.mpr (Ne.symm hp)
    · rw [inner_phi_eq_eta]
  · rintro ⟨d, hd, rfl⟩
    refine ⟨(0, d), ?_, ?_⟩
    · exact (Ne.symm hd)
    · rw [inner_phi_eq_eta]; simp

/-- **The coherence identity: `coherence(Φ) = M(n)`.** The mutual coherence of the DFT submatrix
equals the prize sup-norm `max_{d≠0}‖η_d‖`. Both are the `Finset.sup'` of the same value-set
(`coherence_image_eq_M_image`), so they are equal. This is the genuine content: the prize quantity
IS a coherence, hence any RIP/compressed-sensing bound has it as an *input*, not an output. -/
theorem coherence_eq_M [Fintype F] [DecidableEq F] (ψ : AddChar F ℂ) (G : Finset F)
    (hpair : (Finset.univ.filter (fun p : F × F => p.1 ≠ p.2)).Nonempty)
    (hd : (Finset.univ.filter (fun d : F => d ≠ 0)).Nonempty) :
    coherence ψ G hpair = M ψ G hd := by
  rw [coherence, M]
  -- Rewrite each `sup'` of `f` as a `sup'` of `id` over the image Finset (= the value-set).
  have hL : (Finset.univ.filter (fun p : F × F => p.1 ≠ p.2)).sup' hpair
        (fun p => ‖innerPhi ψ G p.1 p.2‖)
      = ((Finset.univ.filter (fun p : F × F => p.1 ≠ p.2)).image
          (fun p => ‖innerPhi ψ G p.1 p.2‖)).sup' (hpair.image _) id :=
    Finset.sup'_comp_eq_image hpair id
  have hR : (Finset.univ.filter (fun d : F => d ≠ 0)).sup' hd (fun d => ‖eta ψ G d‖)
      = ((Finset.univ.filter (fun d : F => d ≠ 0)).image (fun d => ‖eta ψ G d‖)).sup'
          (hd.image _) id :=
    Finset.sup'_comp_eq_image hd id
  rw [hL, hR]
  -- The two image Finsets are equal (`coherence_image_eq_M_image`), so the `sup'`s coincide.
  exact Finset.sup'_congr _ (coherence_image_eq_M_image ψ G) (fun a _ => rfl)

/-! ### The RIP floor (abstract monotonicity wrapper).

The genuine new content is the coherence identity above. The RIP-floor part is the abstract fact
that `δ_k` is a `Finset.sup'` over a *nested* (larger) index family than `δ_2`, so `δ_2 ≤ δ_k`;
combined with `δ_2 = coherence` (the definition), every RIP constant is `≥ coherence = M(n)/n`.
We state the monotonicity abstractly: if the `k`-index Finset contains the `2`-index Finset, the
`sup'` is monotone. RIP therefore CONSUMES the prize, it cannot produce it. -/

/-- **Abstract RIP-floor monotonicity.** For any real-valued objective `g`, if the index Finset
`S2` (the column-pair index = the `δ_2`/coherence support) is contained in `Sk` (the `δ_k` support
of `k`-subsets, which includes all pairs), then `sup'_{S2} g ≤ sup'_{Sk} g`: the RIP constant
`δ_k` is bounded BELOW by the coherence `δ_2`. This is the one-line reason RIP cannot generate
cancellation below the coherence floor — `M(n)` is consumed, not produced. -/
theorem coherence_le_rip {ι : Type*} (g : ι → ℝ) (S2 Sk : Finset ι)
    (hsub : S2 ⊆ Sk) (h2 : S2.Nonempty) :
    S2.sup' h2 g ≤ Sk.sup' (h2.mono hsub) g :=
  Finset.sup'_mono g hsub h2

end ProximityGap.Frontier.CoherenceIdentity

/-! ## Axiom audit — kernel-clean (`propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`). -/
#print axioms ProximityGap.Frontier.CoherenceIdentity.inner_phi_eq_eta
#print axioms ProximityGap.Frontier.CoherenceIdentity.coherence_image_eq_M_image
#print axioms ProximityGap.Frontier.CoherenceIdentity.coherence_eq_M
#print axioms ProximityGap.Frontier.CoherenceIdentity.coherence_le_rip
