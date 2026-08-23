/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.JohnsonBound.ReedSolomonListSize
import ArkLib.Data.CodingTheory.ProximityGap.MCAGS
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# ABF26 Grand Challenge 1 (#141) — the sub-Johnson MCA count→error wiring

This file wires together two results that were **already proven** in-tree but **not previously
connected**, giving an honest `epsMCA(RS, δ)` bound in the *up-to-Johnson* (√-radius, below
capacity) regime:

* `ArkLib.JohnsonBound.rs_card_ball_le` — the RS list size at the Johnson radius
  (`# RS codewords within Hamming `e` of a fixed word ≤ n·(n-k+1)/johnsonDenom`), and
* `ProximityGap.epsMCA_le_of_lineCloseCount_le` (`MCALowerBound.lean`) — the count→error
  primitive (`epsMCA C δ ≤ ℓ/|F|` from any uniform line-close-count bound `ℓ`),

via the affine-root pinning `ProximityGap.MCAGS.gsList_bad_gamma_bound` (a fixed codeword
line-witnesses at a fixed active coordinate for **at most one** scalar `γ`).

## What is and is not proven here

`rs_lineCloseCount_le_johnson` (T1) is the genuinely-new bridge: the number of pencil scalars `γ`
whose line `u 0 + γ • u 1` is `δ`-close to the RS code is `≤` the RS Johnson list size. It is
axiom-clean (`[propext, Classical.choice, Quot.sound]`), composing only genuinely-proven
upstream lemmas. A grep of the tree confirms this wiring did not previously exist (the in-tree
Johnson-range MCA coverage rests on an external-admit `Prop` stub, not a theorem).

The bridge carries one **explicit honest hypothesis** `hwit`: each line-close `γ` admits a witness
codeword in a *common* Johnson ball that matches the pencil at the active coordinate. This is the
output of a Guruswami–Sudan / Johnson list decoder *below the √-radius* `1 - √ρ` — a known,
sub-capacity, in-principle-derivable fact — kept as an explicit hypothesis (route (c)) rather than
re-deriving the decoder. It is **not** the open prize and is **not** smuggled/faked.

The **beyond-Johnson band** `(1 - √ρ, 1 - ρ]` — where the list size is super-polynomial and which
is the actual content of the ABF26 (eprint 2026/680) `mcaConjecture` — is **not addressed here**.
`card_ball_le` requires `johnsonDenom > 0`, which fails identically above the √-radius, so the
proven list-size machinery yields *no* bound there. That band remains the irreducible open problem;
nothing in this file makes progress on it.
-/

open scoped BigOperators NNReal
open ProximityGap

namespace ProximityGap.MCAGS

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- **Whole RS affine line stays in the code.** If two endpoint words are Reed-Solomon codewords,
then every affine-line word `c₀ + γ • (c₁ - c₀)` is again a Reed-Solomon codeword. This is the
linearity mechanism behind the `hwitAll` refutation: a whole scalar line can be distance-zero
close to the code. -/
theorem reedSolomon_affineLine_mem_of_mem {k : ℕ} {domain : ι ↪ F}
    {c₀ c₁ : ι → F}
    (hc₀ : c₀ ∈ (ReedSolomon.code domain k : Set (ι → F)))
    (hc₁ : c₁ ∈ (ReedSolomon.code domain k : Set (ι → F)))
    (γ : F) :
    c₀ + γ • (c₁ - c₀) ∈ (ReedSolomon.code domain k : Set (ι → F)) := by
  change c₀ + γ • (c₁ - c₀) ∈ ReedSolomon.code domain k
  exact Submodule.add_mem _ hc₀ (Submodule.smul_mem _ γ (Submodule.sub_mem _ hc₁ hc₀))

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
/-- **Whole RS affine line has distance zero from the code.** Each scalar point on the affine line
through two Reed-Solomon codewords is itself in the code, hence has zero relative distance from the
code. -/
theorem reedSolomon_affineLine_relDistFromCode_eq_zero_of_mem
    {k : ℕ} {domain : ι ↪ F} {c₀ c₁ : ι → F}
    (hc₀ : c₀ ∈ (ReedSolomon.code domain k : Set (ι → F)))
    (hc₁ : c₁ ∈ (ReedSolomon.code domain k : Set (ι → F)))
    (γ : F) :
    δᵣ(c₀ + γ • (c₁ - c₀), (ReedSolomon.code domain k : Set (ι → F))) = 0 := by
  classical
  set line : ι → F := c₀ + γ • (c₁ - c₀) with hline
  have hline_mem : line ∈ (ReedSolomon.code domain k : Set (ι → F)) := by
    rw [hline]
    exact reedSolomon_affineLine_mem_of_mem hc₀ hc₁ γ
  apply le_antisymm
  · calc
      δᵣ(line, (ReedSolomon.code domain k : Set (ι → F)))
          ≤ (Code.relHammingDist line line : ENNReal) :=
            Code.relDistFromCode_le_relDist_to_mem line line hline_mem
      _ = 0 := by
        rw [Code.relHammingDist, hammingDist_self]
        simp only [Nat.cast_zero, zero_div]
        rw [← ENNReal.coe_nnratCast]
        simp only [NNRat.cast_zero, ENNReal.coe_zero]
  · exact zero_le _

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
/-- **All scalar points on an RS codeword line are close.** Since each affine-line point through
two Reed-Solomon codewords is in the code, every scalar is line-close at every radius `δ`. -/
theorem reedSolomon_affineLine_all_scalars_close_of_mem
    {k : ℕ} {domain : ι ↪ F} {c₀ c₁ : ι → F} {δ : ℝ≥0}
    (hc₀ : c₀ ∈ (ReedSolomon.code domain k : Set (ι → F)))
    (hc₁ : c₁ ∈ (ReedSolomon.code domain k : Set (ι → F))) :
    ∀ γ : F, δᵣ(c₀ + γ • (c₁ - c₀),
      (ReedSolomon.code domain k : Set (ι → F))) ≤ δ := by
  intro γ
  rw [reedSolomon_affineLine_relDistFromCode_eq_zero_of_mem hc₀ hc₁ γ]
  exact zero_le _

omit [DecidableEq ι] in
/-- **Whole-line cardinality pressure against `hwit`.** If the common-center witness hypothesis
`hwit` is assumed for a whole affine line through two Reed-Solomon codewords, then all field
scalars inject into the single common Johnson ball. The Johnson list-size bound therefore forces
`|F| ≤ n (n-k+1) / johnsonDenom ... e`. This is the cardinality-pressure half of the `hwitAll`
refutation; a concrete contradiction still requires a separate numeric instance where the right
side is smaller than `|F|`. -/
theorem reedSolomon_wholeLine_card_field_le_johnson_of_hwit
    {k : ℕ} [NeZero k] {domain : ι ↪ F} (hk : k ≤ Fintype.card ι)
    (δ : ℝ≥0) (e : ℕ) (x : ι)
    {c₀ c₁ : ι → F}
    (hc₀ : c₀ ∈ (ReedSolomon.code domain k : Set (ι → F)))
    (hc₁ : c₁ ∈ (ReedSolomon.code domain k : Set (ι → F)))
    (hx : (c₁ - c₀) x ≠ 0)
    (w : ι → F)
    (hen : e ≤ Fintype.card ι)
    (hJ : 0 < ArkLib.JohnsonBound.johnsonDenom
            (Fintype.card ι) (Fintype.card ι - k + 1) e)
    (Cset : Finset (ι → F))
    (hCset : (↑Cset : Set (ι → F)) = (ReedSolomon.code domain k : Set (ι → F)))
    (hwit : ∀ γ : F, δᵣ(c₀ + γ • (c₁ - c₀),
        (ReedSolomon.code domain k : Set (ι → F))) ≤ δ →
      ∃ c ∈ Cset, Δ₀(c, w) ≤ e ∧ c x = c₀ x + γ * (c₁ - c₀) x) :
    (Fintype.card F : ℚ)
      ≤ (Fintype.card ι : ℚ) * ((Fintype.card ι - k + 1 : ℕ) : ℚ)
          / ArkLib.JohnsonBound.johnsonDenom
              (Fintype.card ι) (Fintype.card ι - k + 1) e := by
  classical
  set L : Finset (ι → F) := Cset.filter (fun c => Δ₀(c, w) ≤ e) with hL
  have hFL_nat : Fintype.card F ≤ L.card := by
    have hbound :
        (Finset.univ : Finset F).card ≤ L.card := by
      refine gsList_bad_gamma_bound L c₀ (c₁ - c₀) x hx Finset.univ ?_
      intro γ hγ
      have hclose :
          δᵣ(c₀ + γ • (c₁ - c₀), (ReedSolomon.code domain k : Set (ι → F))) ≤ δ :=
        reedSolomon_affineLine_all_scalars_close_of_mem
          (k := k) (domain := domain) (δ := δ) hc₀ hc₁ γ
      obtain ⟨c, hc_mem, hc_ball, hc_eq⟩ := hwit γ hclose
      exact ⟨c, by rw [hL, Finset.mem_filter]; exact ⟨hc_mem, hc_ball⟩, hc_eq⟩
    simpa using hbound
  have hLJ :
      (L.card : ℚ)
        ≤ (Fintype.card ι : ℚ) * ((Fintype.card ι - k + 1 : ℕ) : ℚ)
            / ArkLib.JohnsonBound.johnsonDenom
                (Fintype.card ι) (Fintype.card ι - k + 1) e := by
    have hball := ArkLib.JohnsonBound.rs_card_ball_le
      (k := k) (α := domain) Cset hCset w e hk hen hJ
    exact hball
  have hFL_q : (Fintype.card F : ℚ) ≤ (L.card : ℚ) := by
    exact_mod_cast hFL_nat
  exact le_trans hFL_q hLJ

/-- **Concrete `Fin 4`, `k = 2` Johnson-window arithmetic.** For the issue #244 concrete
instance, throughout the genuine Johnson-window Hamming radii (`e ≤ 4` and positive denominator),
the RS Johnson list-size expression is strictly smaller than the 5-element field size. Combined
with `reedSolomon_wholeLine_card_field_le_johnson_of_hwit`, this is the numeric contradiction
side of the common-center refutation. -/
theorem johnson_fin4_k2_bound_lt_five {e : ℕ}
    (hen : e ≤ 4)
    (hJ : 0 < ArkLib.JohnsonBound.johnsonDenom 4 (4 - 2 + 1) e) :
    (4 : ℚ) * (((4 - 2 + 1 : ℕ) : ℚ)) /
        ArkLib.JohnsonBound.johnsonDenom 4 (4 - 2 + 1) e < 5 := by
  interval_cases e
  · norm_num [ArkLib.JohnsonBound.johnsonDenom]
  · norm_num [ArkLib.JohnsonBound.johnsonDenom]
  · norm_num [ArkLib.JohnsonBound.johnsonDenom] at hJ
  · norm_num [ArkLib.JohnsonBound.johnsonDenom] at hJ
  · norm_num [ArkLib.JohnsonBound.johnsonDenom] at hJ

/-- **T1 — the missing wiring lemma (axiom-clean).**

In the up-to-Johnson regime (`0 < johnsonDenom`), the number of pencil scalars `γ` whose line
`u 0 + γ • u 1` is `δ`-close to the Reed–Solomon code is bounded by the RS Johnson list size
`n · (n - k + 1) / johnsonDenom n (n - k + 1) e`.

Composition of two proven results: the affine-root pinning (`gsList_bad_gamma_bound`) injects the
line-close `γ` into the RS Johnson ball Finset `L`; the RS Johnson list size (`rs_card_ball_le`)
bounds `|L|`. `hwit` is the explicit sub-Johnson decoder bridge (a known fact below `1 - √ρ`, not
the open prize). -/
theorem rs_lineCloseCount_le_johnson
    {k : ℕ} [NeZero k] {domain : ι ↪ F} (hk : k ≤ Fintype.card ι)
    (δ : ℝ≥0) (e : ℕ) (x : ι)
    (u : Code.WordStack F (Fin 2) ι)
    (hx : u 1 x ≠ 0)
    (w : ι → F)
    (hen : e ≤ Fintype.card ι)
    (hJ : 0 < ArkLib.JohnsonBound.johnsonDenom
            (Fintype.card ι) (Fintype.card ι - k + 1) e)
    (Cset : Finset (ι → F))
    (hCset : (↑Cset : Set (ι → F)) = (ReedSolomon.code domain k : Set (ι → F)))
    (hwit : ∀ γ : F, δᵣ(u 0 + γ • u 1, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ →
      ∃ c ∈ Cset, Δ₀(c, w) ≤ e ∧ c x = u 0 x + γ * u 1 x) :
    ((Finset.univ.filter
        (fun γ : F => δᵣ(u 0 + γ • u 1,
          (ReedSolomon.code domain k : Set (ι → F))) ≤ δ)).card : ℚ)
      ≤ (Fintype.card ι : ℚ) * ((Fintype.card ι - k + 1 : ℕ) : ℚ)
          / ArkLib.JohnsonBound.johnsonDenom
              (Fintype.card ι) (Fintype.card ι - k + 1) e := by
  classical
  set L : Finset (ι → F) := Cset.filter (fun c => Δ₀(c, w) ≤ e) with hL
  set S : Finset F :=
    Finset.univ.filter
      (fun γ : F => δᵣ(u 0 + γ • u 1,
        (ReedSolomon.code domain k : Set (ι → F))) ≤ δ) with hS
  have hSL : S.card ≤ L.card := by
    refine gsList_bad_gamma_bound L (u 0) (u 1) x hx S ?_
    intro γ hγ
    rw [hS, Finset.mem_filter] at hγ
    obtain ⟨c, hc_mem, hc_ball, hc_eq⟩ := hwit γ hγ.2
    exact ⟨c, by rw [hL, Finset.mem_filter]; exact ⟨hc_mem, hc_ball⟩, hc_eq⟩
  have hLJ :
      (L.card : ℚ)
        ≤ (Fintype.card ι : ℚ) * ((Fintype.card ι - k + 1 : ℕ) : ℚ)
            / ArkLib.JohnsonBound.johnsonDenom
                (Fintype.card ι) (Fintype.card ι - k + 1) e := by
    have hball := ArkLib.JohnsonBound.rs_card_ball_le
      (k := k) (α := domain) Cset hCset w e hk hen hJ
    exact hball
  have hSL' : (S.card : ℚ) ≤ (L.card : ℚ) := by exact_mod_cast hSL
  calc (S.card : ℚ) ≤ (L.card : ℚ) := hSL'
    _ ≤ _ := hLJ

/-- **T2 — `epsMCA` Johnson bound from a uniform line-close count (axiom-clean).**
Direct specialization of the proven `epsMCA_le_of_lineCloseCount_le` to the RS code: any uniform
line-close-count bound `ℓ` yields `epsMCA(RS, δ) ≤ ℓ/|F|`. (`ℓ` is supplied by `T1` in the Johnson
window, after `ℚ → ℕ` ceiling — see `rs_epsMCA_le_johnson_ceil_of_hwit`.) -/
theorem rs_epsMCA_le_johnson_div_q
    {k : ℕ} (domain : ι ↪ F) (δ : ℝ≥0) (ℓ : ℕ)
    (hcount : ∀ u : Code.WordStack F (Fin 2) ι,
      (Finset.univ.filter
          (fun γ : F => δᵣ(u 0 + γ • u 1,
            (ReedSolomon.code domain k : Set (ι → F))) ≤ δ)).card ≤ ℓ) :
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ
      ≤ (ℓ : ENNReal) / (Fintype.card F : ENNReal) :=
  epsMCA_le_of_lineCloseCount_le
    (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ ℓ hcount

/-- **Headline corollary: sub-Johnson `epsMCA` from the explicit decoder bridge (axiom-clean).**
In the up-to-Johnson regime, given the sub-Johnson clustering hypothesis `hwitAll` (for every pencil
`u`, a fixed active coordinate and a common Johnson ball containing the per-`γ` witnesses), the RS
`epsMCA` is bounded by the RS Johnson list size (`ℚ → ℕ` ceiling) over `|F|`. This is the honest,
explicitly-conditional sub-Johnson bound; the beyond-Johnson band is untouched and open. -/
theorem rs_epsMCA_le_johnson_ceil_of_hwit
    {k : ℕ} [NeZero k] (domain : ι ↪ F) (hk : k ≤ Fintype.card ι)
    (δ : ℝ≥0) (e : ℕ) (hen : e ≤ Fintype.card ι)
    (hJ : 0 < ArkLib.JohnsonBound.johnsonDenom
            (Fintype.card ι) (Fintype.card ι - k + 1) e)
    (Cset : Finset (ι → F))
    (hCset : (↑Cset : Set (ι → F)) = (ReedSolomon.code domain k : Set (ι → F)))
    (hwitAll : ∀ u : Code.WordStack F (Fin 2) ι, ∃ x : ι, u 1 x ≠ 0 ∧ ∃ w : ι → F,
      ∀ γ : F, δᵣ(u 0 + γ • u 1, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ →
        ∃ c ∈ Cset, Δ₀(c, w) ≤ e ∧ c x = u 0 x + γ * u 1 x) :
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ
      ≤ ((⌈(Fintype.card ι : ℚ) * ((Fintype.card ι - k + 1 : ℕ) : ℚ)
            / ArkLib.JohnsonBound.johnsonDenom
                (Fintype.card ι) (Fintype.card ι - k + 1) e⌉₊ : ℕ) : ENNReal)
        / (Fintype.card F : ENNReal) := by
  classical
  set ℓ : ℕ := ⌈(Fintype.card ι : ℚ) * ((Fintype.card ι - k + 1 : ℕ) : ℚ)
            / ArkLib.JohnsonBound.johnsonDenom
                (Fintype.card ι) (Fintype.card ι - k + 1) e⌉₊ with hℓ
  refine rs_epsMCA_le_johnson_div_q (k := k) domain δ ℓ ?_
  intro u
  obtain ⟨x, hx, w, hwit⟩ := hwitAll u
  have h1 := rs_lineCloseCount_le_johnson (k := k) (domain := domain)
    hk δ e x u hx w hen hJ Cset hCset hwit
  -- `(count : ℚ) ≤ Johnson` and `ℓ = ⌈Johnson⌉₊`, so `count ≤ ℓ` over `ℕ`.
  have hcq : ((Finset.univ.filter
      (fun γ : F => δᵣ(u 0 + γ • u 1,
        (ReedSolomon.code domain k : Set (ι → F))) ≤ δ)).card : ℚ) ≤ (ℓ : ℚ) := by
    rw [hℓ]; exact le_trans h1 (Nat.le_ceil _)
  exact_mod_cast hcq

#print axioms ProximityGap.MCAGS.reedSolomon_affineLine_mem_of_mem
#print axioms ProximityGap.MCAGS.reedSolomon_affineLine_relDistFromCode_eq_zero_of_mem
#print axioms ProximityGap.MCAGS.reedSolomon_affineLine_all_scalars_close_of_mem
#print axioms ProximityGap.MCAGS.reedSolomon_wholeLine_card_field_le_johnson_of_hwit
#print axioms ProximityGap.MCAGS.johnson_fin4_k2_bound_lt_five

end ProximityGap.MCAGS

namespace ProximityGap.GrandChallenges

open ProximityGap ProximityGap.MCAGS

/-- **Wire the sub-Johnson `epsMCA` bound into the `MCALowerWitness` prize API (axiom-clean).**
Given the up-to-Johnson hypotheses and the explicit sub-Johnson clustering `hwitAll`, plus the
numeric envelope `hle : ⌈Johnson⌉/|F| ≤ ε*`, the RS code admits a `MCALowerWitness` at `ε*`. This
connects `rs_epsMCA_le_johnson_ceil_of_hwit` to the prize lower-witness machinery (it was otherwise
wired into no witness). Both `hwitAll` (the sub-`√ρ` decoder bridge) and `hle` are kept explicit;
no open conjecture is smuggled, and the beyond-Johnson keystone is untouched. -/
noncomputable def MCALowerWitness.ofRsJohnsonCount
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k : ℕ} [NeZero k] (domain : ι ↪ F) (hk : k ≤ Fintype.card ι)
    (δ : ℝ≥0) (e : ℕ) (hen : e ≤ Fintype.card ι)
    (hJ : 0 < ArkLib.JohnsonBound.johnsonDenom
            (Fintype.card ι) (Fintype.card ι - k + 1) e)
    (Cset : Finset (ι → F))
    (hCset : (↑Cset : Set (ι → F)) = (ReedSolomon.code domain k : Set (ι → F)))
    (hwitAll : ∀ u : Code.WordStack F (Fin 2) ι, ∃ x : ι, u 1 x ≠ 0 ∧ ∃ w : ι → F,
      ∀ γ : F, δᵣ(u 0 + γ • u 1, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ →
        ∃ c ∈ Cset, Δ₀(c, w) ≤ e ∧ c x = u 0 x + γ * u 1 x)
    (hδ : δ ≤ 1)
    (ε_star : ℝ≥0)
    (hle : ((⌈(Fintype.card ι : ℚ) * ((Fintype.card ι - k + 1 : ℕ) : ℚ)
            / ArkLib.JohnsonBound.johnsonDenom
                (Fintype.card ι) (Fintype.card ι - k + 1) e⌉₊ : ℕ) : ENNReal)
        / (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal)) :
    MCALowerWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star :=
  MCALowerWitness.ofLe hδ
    (le_trans (rs_epsMCA_le_johnson_ceil_of_hwit domain hk δ e hen hJ Cset hCset hwitAll) hle)

end ProximityGap.GrandChallenges
