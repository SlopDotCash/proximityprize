/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# LANE G99 (#466, 2026-07-10): the Erdős–Turán / Esseen harmonic-ladder certificate with the
  EXACT in-tree second moment, and a NON-FOURIER small-ball rigidity theorem for dilated orbits

## The question this lane answers

`DISPROOF_LOG.md` `[door-iv-phaseset-smallball]` poses, verbatim: *"Any Littlewood-Offord /
Halász small-ball bound that does NOT route through multiplicative energy?"*. This file gives
the exact quantitative content of the Fourier-side (Esseen/Erdős–Turán) answer, and an
elementary POSITIVE answer at containment scale on the non-Fourier side.

## Part 1 — the Esseen/ET harmonic ladder with the exact `L²` input (Fourier test side)

Erdős–Turán bounds the star discrepancy of the dilated value multiset
`{val(b·x)/p : x ∈ μ_n}` by `n/(H+1) + 3·Σ_{h≤H} ‖η_{hb}‖/h` — an `l¹`-average over a SPARSE
harmonic ladder of the SAME period field `η`. Per the G78/G80Z circularity doctrine this is
the legal direction (Fourier duality on the TEST indicator, not an assumed cancellation of the
field being bounded). The only unconditional input available is the exact in-tree second
moment `Σ_b ‖η_b‖² = q·n` (`subgroup_gaussSum_secondMoment`, no Weil). This file pins the
exact chain:

* `eta_mul_mem` : η is CONSTANT on μ_n-cosets of frequencies (`η_{c·u} = η_c`, `u ∈ G`) —
  the n-fold spectral degeneracy that upgrades the frequency-level Parseval to coset level.
* `sum_nonzero_eta_sq` : `Σ_{b≠0} ‖η_b‖² = q·|G| − |G|²` exactly (DC-subtracted Parseval, r=1).
* `ladder_sq_le_of_injective` : any `H` distinct nonzero frequencies carry `l²` ladder mass
  `≤ q·|G| − |G|²` (hypothesis-free fallback).
* `ladder_sq_le_of_distinct_cosets` : if the ladder frequencies hit pairwise DISTINCT cosets,
  the mass drops by the exact factor `n`: `Σ_{h<H} ‖η_{c_h}‖² ≤ q − |G|` — b-UNIFORM, because
  dilation permutes cosets.
* `sum_range_inv_sq_le_two` : `Σ_{h<H} 1/(h+1)² ≤ 2` (elementary partial Basel bound).
* `ladder_weighted_l1_le_of_distinct_cosets` (HEADLINE A) : Cauchy–Schwarz weld —
  `Σ_{h<H} ‖η_{c_h}‖/(h+1) ≤ √2·√(q − |G|)`, uniformly in the dilation `b`.
* `gaussPeriod_harmonic_ladder_bound` : the concrete instantiation `c_h = (h+1)·b`.
* `arc_discrepancy_of_erdosTuran_hypothesis` : the explicitly-CONDITIONAL composition — IF
  classical Erdős–Turán (NOT formalized here; Fejér-kernel analysis) is granted as a
  hypothesis for the family, THEN `D* ≤ n/(H+1) + 3√2·√(q−n)`.
* `completion_correlation_identity` / `completion_arc_deviation_bound` (HEADLINE B) : the
  hypothesis-free exact-completion baseline for ANY test set: for all finsets `S, I`,
  `|q·#(S∩I) − |S|·|I|| ≤ √(|I|(q−|I|))·√(|S|(q−|S|))` — two exact Parsevals + Cauchy–Schwarz,
  no kernel, no truncation, no side condition.
* `esseen_loop_resolution_floor` : the AM–GM floor `2√(2πnΔ) ≤ 2πn/K + KΔ` for the G80Z
  consumer loop `M ≤ 2πn/K + K·Δ` — the no-contraction record (see scope below).

**Where the certificate is nontrivial (exact, probe-verified `g99_probe.py`).** The arc
certificate `n/(H+1) + 3√2·√(q−n)` beats the trivial cap `n` iff `n ≳ (3√2)·√q`, i.e. ONLY in
the dense regime `n ≫ √q` (probe: nontrivial at `p=257, n=128` and `p=65537, n=4096`; vacuous
by factor ≈ 68 at the prize shape `p=65537, n=16`, where truth is `D* = 6` and the certificate
is `≈ 1086`). Feeding it back through the G80Z consumer, the loop value is always
`≥ 2√(2πnΔ)`; with `Δ` at the certified scale `√(q−n)` this floor exceeds BOTH the trivial `n`
(thin regime, resolution-blocked at `K ≥ 2`) and the elementary Gauss-sum-decomposition
ceiling `√q` (dense regime) — the ET/Esseen self-reference is quantitatively NON-CONTRACTING
with the exact `l²` input, extending G78's KM-loop verdict to the Esseen loop with sharp
constants. Orbit collisions are handled exactly: at v₂-structured primes the smooth subgroup
CONTAINS small integers (at `p=65537`, `μ₁₆ = ⟨4⟩ ∋ 4, 16, 64`; `ord(2)=32` puts `2 ∈ μ_n` for
all dyadic `n ≥ 32`), so the distinct-coset hypothesis fails already at `H ∈ {1,…,3}` there —
it is carried as an explicit arithmetic side condition, with the injective-frequency fallback
unconditional.

## Part 2 — the non-Fourier certificate (HEADLINE C): integer-lift multiplicative rigidity

`dilated_orbit_short_interval_rigidity` / `not_dilated_orbit_subset_interval`: for `p` prime,
`x` of order `n ≥ 3` (i.e. `xⁿ = 1`, `x² ≠ 1`) and ANY `b ≠ 0`, the dilated orbit
`{b·x^k mod p}` is NOT contained in any interval of length `V` once `2V² < p`. Proof
mechanism — NO Fourier analysis, NO multiplicative energy, NO Weil: lift the consecutive
differences `m_k := valMinAbs(b·x^{k+1} − b·x^k)` to ℤ; the mod-p identity
`m_j·m_k ≡ m_0·m_{j+k}` has both sides `< 2V² < p` in absolute value, hence holds in ℤ; the
integer sequence is then geometric (`m_k·m_0^k = m_0·m_1^k`) and `x`-periodicity forces
`m_0^n = m_1^n`, so `m_1 = ±m_0`, which pins `x = ±1` — contradicting `x² ≠ 1`. This is a
Littlewood–Offord-type small-ball statement (total-mass concentration in one arc is
impossible below scale `√(p/2)`) obtained purely from the multiplicative structure lifted to
ℤ — the certificate side of the ledger, b-uniform, at every scale `V < √(p/2)`.

## Honest scope

* Part 1 formalizes the LADDER estimates and the exact-completion baseline; classical
  Erdős–Turán itself (Fejér/Vaaler kernel) is NOT formalized — the one theorem consuming it
  says so in its name and takes it as an explicit hypothesis. Nothing here bounds `M` at the
  prize shape; the probe-verified verdict is that this route is VACUOUS in the thin window
  and dominated by the `√q` Gauss-sum ceiling in the dense window. CORE remains OPEN/ON-BGK.
* Part 2 is unconditional and axiom-clean but certifies only CONTAINMENT-refutation
  (small-ball probability `< 1` at scale `√(p/2)`), far from the per-arc occupancy deviation
  `≲ √(n log q)/K` that the G80Z consumer needs. It does NOT touch the wall. Its value: it is
  a genuinely non-Fourier, non-energy anti-concentration mechanism for exactly the object the
  `[door-iv-phaseset-smallball]` entry asked about.

Issue #466. Axiom-clean; no `sorry`, no new axioms.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G99ErdosTuranLadderCertificate

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

/-! ## Part 1a — coset invariance and the exact DC-subtracted second moment -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **η is constant on μ-cosets of frequencies.** If `G` is closed under multiplication and
avoids `0`, then multiplying the frequency by any `u ∈ G` leaves the period untouched:
`η_{c·u} = η_c`. This is the exact `n`-fold spectral degeneracy of the period field. -/
theorem eta_mul_mem (ψ : AddChar F ℂ) {G : Finset F} (hG0 : (0 : F) ∉ G)
    (hcl : ∀ u ∈ G, ∀ v ∈ G, u * v ∈ G) {u : F} (hu : u ∈ G) (c : F) :
    eta ψ G (c * u) = eta ψ G c := by
  have hu0 : u ≠ 0 := fun h => hG0 (h ▸ hu)
  have himg : G.image (fun y => u * y) = G := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact hcl u hu y hy
    · rw [Finset.card_image_of_injective _ (mul_right_injective₀ hu0)]
  calc eta ψ G (c * u) = ∑ y ∈ G, ψ (c * (u * y)) := by
        unfold eta
        exact Finset.sum_congr rfl (fun y _ => by rw [mul_assoc])
    _ = ∑ z ∈ G.image (fun y => u * y), ψ (c * z) := by
        rw [Finset.sum_image (fun y _ y' _ h => mul_right_injective₀ hu0 h)]
    _ = eta ψ G c := by rw [himg]; rfl

/-- The DC frequency carries the full mass: `η_0 = |G|`. -/
theorem eta_zero (ψ : AddChar F ℂ) (G : Finset F) : eta ψ G 0 = (G.card : ℂ) := by
  unfold eta
  simp

/-- **The exact DC-subtracted second moment (Parseval at r = 1):**
`Σ_{b≠0} ‖η_b‖² = q·|G| − |G|²`. This is the ONLY unconditional `l²` input available to the
Esseen/Erdős–Turán ladder. -/
theorem sum_nonzero_eta_sq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
  have hsplit : ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 + ‖eta ψ G 0‖ ^ 2
      = ∑ b : F, ‖eta ψ G b‖ ^ 2 :=
    Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (0 : F))
  have htotal := subgroup_gaussSum_secondMoment hψ G
  have h0 : ‖eta ψ G 0‖ ^ 2 = (G.card : ℝ) ^ 2 := by
    rw [eta_zero]
    simp
  have := hsplit.trans htotal
  linarith [this, h0]

/-! ## Part 1b — ladder second-moment bounds (frequency level and coset level) -/

/-- **Frequency-level ladder mass (hypothesis-free fallback).** Any family of `H` distinct
NONZERO frequencies carries `l²` mass at most the full DC-subtracted Parseval budget
`q·|G| − |G|²`. -/
theorem ladder_sq_le_of_injective {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {H : ℕ} {c : ℕ → F} (hc0 : ∀ h ∈ Finset.range H, c h ≠ 0)
    (hinj : ∀ h₁ ∈ Finset.range H, ∀ h₂ ∈ Finset.range H, c h₁ = c h₂ → h₁ = h₂) :
    ∑ h ∈ Finset.range H, ‖eta ψ G (c h)‖ ^ 2
      ≤ (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
  rw [← sum_nonzero_eta_sq hψ G]
  have himg : ∑ h ∈ Finset.range H, ‖eta ψ G (c h)‖ ^ 2
      = ∑ t ∈ (Finset.range H).image c, ‖eta ψ G t‖ ^ 2 := by
    rw [Finset.sum_image hinj]
  rw [himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun t _ _ => by positivity)
  intro t ht
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp ht
  exact Finset.mem_erase.mpr ⟨hc0 h hh, Finset.mem_univ _⟩

/-- **Coset-level ladder mass — the exact factor-`n` upgrade.** If the ladder frequencies hit
pairwise DISTINCT `G`-cosets, the coset degeneracy `eta_mul_mem` compresses the budget by
exactly `n = |G|`: `Σ_{h<H} ‖η_{c_h}‖² ≤ q − |G|`. This is b-UNIFORM: dilating a ladder by
any `b ≠ 0` permutes cosets and preserves the hypothesis shape. -/
theorem ladder_sq_le_of_distinct_cosets {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} (hG0 : (0 : F) ∉ G) (hcl : ∀ u ∈ G, ∀ v ∈ G, u * v ∈ G)
    (hGne : G.Nonempty) {H : ℕ} {c : ℕ → F} (hc0 : ∀ h ∈ Finset.range H, c h ≠ 0)
    (hdis : ∀ h₁ ∈ Finset.range H, ∀ h₂ ∈ Finset.range H, h₁ ≠ h₂ →
      ∀ u₁ ∈ G, ∀ u₂ ∈ G, c h₁ * u₁ ≠ c h₂ * u₂) :
    ∑ h ∈ Finset.range H, ‖eta ψ G (c h)‖ ^ 2 ≤ (Fintype.card F : ℝ) - G.card := by
  have hn : (0 : ℝ) < G.card := by exact_mod_cast Finset.card_pos.mpr hGne
  -- the disjoint union of the dilated cosets
  set T : Finset F := (Finset.range H).biUnion (fun h => G.image (fun u => c h * u)) with hT
  have hdisT : Set.PairwiseDisjoint ↑(Finset.range H)
      (fun h => G.image (fun u => c h * u)) := by
    intro h₁ hh₁ h₂ hh₂ hne
    refine Finset.disjoint_left.mpr (fun a ha₁ ha₂ => ?_)
    obtain ⟨u₁, hu₁, he₁⟩ := Finset.mem_image.mp ha₁
    obtain ⟨u₂, hu₂, he₂⟩ := Finset.mem_image.mp ha₂
    exact hdis h₁ (Finset.mem_coe.mp hh₁) h₂ (Finset.mem_coe.mp hh₂) hne u₁ hu₁ u₂ hu₂
      (he₁.trans he₂.symm)
  -- per-coset: the coset carries |G| copies of ‖η_{c_h}‖²
  have hcoset : ∀ h ∈ Finset.range H,
      ∑ t ∈ G.image (fun u => c h * u), ‖eta ψ G t‖ ^ 2
        = (G.card : ℝ) * ‖eta ψ G (c h)‖ ^ 2 := by
    intro h hh
    rw [Finset.sum_image (fun u _ u' _ hu =>
      mul_left_cancel₀ (hc0 h hh) hu)]
    have : ∀ u ∈ G, ‖eta ψ G (c h * u)‖ ^ 2 = ‖eta ψ G (c h)‖ ^ 2 := fun u hu => by
      rw [eta_mul_mem ψ hG0 hcl hu]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  -- total coset mass ≤ full nonzero Parseval budget
  have hTsub : T ⊆ Finset.univ.erase (0 : F) := by
    intro t ht
    obtain ⟨h, hh, htmem⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp htmem
    have hu0 : u ≠ 0 := fun h' => hG0 (h' ▸ hu)
    exact Finset.mem_erase.mpr ⟨mul_ne_zero (hc0 h hh) hu0, Finset.mem_univ _⟩
  have hsumT : ∑ t ∈ T, ‖eta ψ G t‖ ^ 2
      = (G.card : ℝ) * ∑ h ∈ Finset.range H, ‖eta ψ G (c h)‖ ^ 2 := by
    rw [hT, Finset.sum_biUnion hdisT, Finset.sum_congr rfl hcoset, Finset.mul_sum]
  have hbudget : ∑ t ∈ T, ‖eta ψ G t‖ ^ 2
      ≤ (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
    rw [← sum_nonzero_eta_sq hψ G]
    exact Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun t _ _ => by positivity)
  have hqn : (G.card : ℝ) * ∑ h ∈ Finset.range H, ‖eta ψ G (c h)‖ ^ 2
      ≤ (G.card : ℝ) * ((Fintype.card F : ℝ) - G.card) := by
    rw [← hsumT]
    calc ∑ t ∈ T, ‖eta ψ G t‖ ^ 2
        ≤ (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := hbudget
      _ = (G.card : ℝ) * ((Fintype.card F : ℝ) - G.card) := by ring
  exact le_of_mul_le_mul_left hqn hn

/-! ## Part 1c — the harmonic weights and the Cauchy–Schwarz weld -/

/-- Elementary partial Basel bound: `Σ_{h<H} (1/(h+1))² ≤ 2` (indeed `≤ 2 − 1/H`). -/
theorem sum_range_inv_sq_le_two (H : ℕ) :
    ∑ h ∈ Finset.range H, (1 / ((h : ℝ) + 1)) ^ 2 ≤ 2 := by
  have haux : ∀ K : ℕ, ∑ h ∈ Finset.range (K + 1), (1 / ((h : ℝ) + 1)) ^ 2
      ≤ 2 - 1 / ((K : ℝ) + 1) := by
    intro K
    induction K with
    | zero => norm_num
    | succ K ih =>
      rw [Finset.sum_range_succ]
      have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
      have hK2 : (0 : ℝ) < (K : ℝ) + 2 := by positivity
      have hstep : (1 / (((K + 1 : ℕ) : ℝ) + 1)) ^ 2
          ≤ 1 / ((K : ℝ) + 1) - 1 / ((K : ℝ) + 2) := by
        push_cast
        rw [div_sub_div _ _ (ne_of_gt hK1) (ne_of_gt hK2)]
        rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
        ring_nf
        nlinarith [sq_nonneg ((K : ℝ) + 1)]
      have hcast : (((K + 1 : ℕ) : ℝ) + 1) = (K : ℝ) + 2 := by push_cast; ring
      calc ∑ h ∈ Finset.range (K + 1), (1 / ((h : ℝ) + 1)) ^ 2
            + (1 / (((K + 1 : ℕ) : ℝ) + 1)) ^ 2
          ≤ (2 - 1 / ((K : ℝ) + 1)) + (1 / ((K : ℝ) + 1) - 1 / ((K : ℝ) + 2)) :=
            add_le_add ih hstep
        _ = 2 - 1 / ((K : ℝ) + 2) := by ring
        _ = 2 - 1 / (((K + 1 : ℕ) : ℝ) + 1) := by rw [hcast]
  cases H with
  | zero => simp
  | succ K =>
    refine (haux K).trans ?_
    have : (0 : ℝ) < 1 / ((K : ℝ) + 1) := by positivity
    linarith

/-- **HEADLINE A — the Esseen/Erdős–Turán ladder certificate.** Under the distinct-coset
hypothesis, the harmonically-weighted `l¹` ladder is bounded by `√2·√(q − |G|)`, UNIFORMLY in
the base point of the ladder. This is exactly the quantity classical Erdős–Turán consumes:
`D* ≤ n/(H+1) + 3·(this sum)`. -/
theorem ladder_weighted_l1_le_of_distinct_cosets {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} (hG0 : (0 : F) ∉ G) (hcl : ∀ u ∈ G, ∀ v ∈ G, u * v ∈ G)
    (hGne : G.Nonempty) {H : ℕ} {c : ℕ → F} (hc0 : ∀ h ∈ Finset.range H, c h ≠ 0)
    (hdis : ∀ h₁ ∈ Finset.range H, ∀ h₂ ∈ Finset.range H, h₁ ≠ h₂ →
      ∀ u₁ ∈ G, ∀ u₂ ∈ G, c h₁ * u₁ ≠ c h₂ * u₂) :
    ∑ h ∈ Finset.range H, ‖eta ψ G (c h)‖ / ((h : ℝ) + 1)
      ≤ Real.sqrt 2 * Real.sqrt ((Fintype.card F : ℝ) - G.card) := by
  have hCS := Real.sum_sqrt_mul_sqrt_le (Finset.range H)
    (f := fun h : ℕ => (1 / ((h : ℝ) + 1)) ^ 2)
    (g := fun h : ℕ => ‖eta ψ G (c h)‖ ^ 2)
    (fun h => by positivity) (fun h => by positivity)
  have hL : ∑ h ∈ Finset.range H, ‖eta ψ G (c h)‖ / ((h : ℝ) + 1)
      = ∑ h ∈ Finset.range H,
        Real.sqrt ((1 / ((h : ℝ) + 1)) ^ 2) * Real.sqrt (‖eta ψ G (c h)‖ ^ 2) := by
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)]
    rw [div_eq_mul_inv, mul_comm, one_div]
  have hf2 : Real.sqrt (∑ h ∈ Finset.range H, (1 / ((h : ℝ) + 1)) ^ 2) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt (sum_range_inv_sq_le_two H)
  have hg2 : Real.sqrt (∑ h ∈ Finset.range H, ‖eta ψ G (c h)‖ ^ 2)
      ≤ Real.sqrt ((Fintype.card F : ℝ) - G.card) :=
    Real.sqrt_le_sqrt (ladder_sq_le_of_distinct_cosets hψ hG0 hcl hGne hc0 hdis)
  calc ∑ h ∈ Finset.range H, ‖eta ψ G (c h)‖ / ((h : ℝ) + 1)
      = ∑ h ∈ Finset.range H,
          Real.sqrt ((1 / ((h : ℝ) + 1)) ^ 2) * Real.sqrt (‖eta ψ G (c h)‖ ^ 2) := hL
    _ ≤ Real.sqrt (∑ h ∈ Finset.range H, (1 / ((h : ℝ) + 1)) ^ 2)
          * Real.sqrt (∑ h ∈ Finset.range H, ‖eta ψ G (c h)‖ ^ 2) := hCS
    _ ≤ Real.sqrt 2 * Real.sqrt ((Fintype.card F : ℝ) - G.card) :=
        mul_le_mul hf2 hg2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The concrete Gauss-period instantiation: the ladder `c_h = (h+1)·b` over the dilation
`b`. The distinct-coset hypothesis here says exactly: no ratio `h'/h` of ladder indices lies
in `G` (mod p) — an arithmetic condition on `(G, H)` alone, INDEPENDENT of `b`. -/
theorem gaussPeriod_harmonic_ladder_bound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} (hG0 : (0 : F) ∉ G) (hcl : ∀ u ∈ G, ∀ v ∈ G, u * v ∈ G)
    (hGne : G.Nonempty) {H : ℕ} {b : F}
    (hc0 : ∀ h ∈ Finset.range H, ((h + 1 : ℕ) : F) * b ≠ 0)
    (hdis : ∀ h₁ ∈ Finset.range H, ∀ h₂ ∈ Finset.range H, h₁ ≠ h₂ →
      ∀ u₁ ∈ G, ∀ u₂ ∈ G, ((h₁ + 1 : ℕ) : F) * b * u₁ ≠ ((h₂ + 1 : ℕ) : F) * b * u₂) :
    ∑ h ∈ Finset.range H, ‖eta ψ G (((h + 1 : ℕ) : F) * b)‖ / ((h : ℝ) + 1)
      ≤ Real.sqrt 2 * Real.sqrt ((Fintype.card F : ℝ) - G.card) := by
  exact ladder_weighted_l1_le_of_distinct_cosets
    (c := fun h : ℕ => ((h + 1 : ℕ) : F) * b) hψ hG0 hcl hGne hc0 hdis

/-- **The explicitly-CONDITIONAL Erdős–Turán composition.** Classical Erdős–Turán (star
discrepancy `D* ≤ n/(H+1) + 3·ladder`; Fejér-kernel analysis, NOT formalized in this
repository) is taken as a HYPOTHESIS `hET`; the unconditional ladder certificate then yields
the closed-form arc bound. Nontrivial (below the trivial cap `n`) iff `q − n < (n − n/(H+1))²/18`,
i.e. only in the dense regime `n ≳ 3√2·√q` — vacuous at every thin/prize-shape cell. -/
theorem arc_discrepancy_of_erdosTuran_hypothesis {Dstar L n H q g : ℝ}
    (hET : Dstar ≤ n / (H + 1) + 3 * L)
    (hL : L ≤ Real.sqrt 2 * Real.sqrt (q - g)) :
    Dstar ≤ n / (H + 1) + 3 * (Real.sqrt 2 * Real.sqrt (q - g)) := by
  linarith

/-! ## Part 1d — the exact-completion baseline (hypothesis-free) and the loop floor -/

/-- **The exact completion identity (cross-Parseval):**
`Σ_b Î(b)·conj(Ŝ(b)) = q·#(S ∩ I)` for arbitrary finsets `S, I ⊆ F` — pure additive-character
orthogonality, mirroring `subgroup_gaussSum_secondMoment` off the diagonal. -/
theorem completion_correlation_identity {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (S I : Finset F) :
    ∑ b : F, eta ψ I b * (starRingEnd ℂ) (eta ψ S b)
      = (Fintype.card F : ℂ) * ((S ∩ I).card : ℂ) := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a
    rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  calc ∑ b : F, eta ψ I b * (starRingEnd ℂ) (eta ψ S b)
      = ∑ b : F, ∑ t ∈ I, ∑ y ∈ S, ψ (b * (t - y)) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        have hconjeta : (starRingEnd ℂ) (eta ψ S b) = ∑ y ∈ S, ψ (-(b * y)) := by
          rw [eta, map_sum]
          exact Finset.sum_congr rfl (fun y _ => hconj (b * y))
        have hL : eta ψ I b = ∑ t ∈ I, ψ (b * t) := rfl
        rw [hconjeta, hL, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        refine Finset.sum_congr rfl (fun y _ => ?_)
        have harg : b * t + -(b * y) = b * (t - y) := by ring
        rw [← AddChar.map_add_eq_mul, harg]
    _ = ∑ t ∈ I, ∑ y ∈ S, ∑ b : F, ψ (b * (t - y)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ t ∈ I, ∑ y ∈ S, (if t = y then (Fintype.card F : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [AddChar.sum_mulShift (t - y) hψ]
        simp [sub_eq_zero]
    _ = ∑ t ∈ I, (if t ∈ S then (Fintype.card F : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [Finset.sum_ite_eq S t (fun _ => (Fintype.card F : ℂ))]
    _ = (Fintype.card F : ℂ) * ((S ∩ I).card : ℂ) := by
        rw [Finset.sum_ite_mem]
        rw [Finset.sum_const, nsmul_eq_mul, Finset.inter_comm]
        ring

/-- **HEADLINE B — the hypothesis-free exact-completion arc bound.** For EVERY pair of
finsets `S, I ⊆ F` (no structure assumed on either):
`|q·#(S∩I) − |S|·|I|| ≤ √(|I|(q−|I|))·√(|S|(q−|S|))`. Two exact Parsevals + Cauchy–Schwarz —
no kernel, no truncation, no side condition. NOTE the honest scope: with `S = b·μ_n` and `I`
an arc this bound is `≈ √(n·|I|)`, which never beats the trivial cap `min(|S|,|I|)` as an
equidistribution statement; it is recorded as the exact unconditional baseline the
Fourier-side route cannot improve without either coset structure (HEADLINE A) or a genuinely
non-Fourier certificate (Part 2 / the BGK–Cilleruelo–Garaev frontier). -/
theorem completion_arc_deviation_bound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (S I : Finset F) :
    |(Fintype.card F : ℝ) * ((S ∩ I).card : ℝ) - (S.card : ℝ) * I.card|
      ≤ Real.sqrt ((I.card : ℝ) * ((Fintype.card F : ℝ) - I.card))
        * Real.sqrt ((S.card : ℝ) * ((Fintype.card F : ℝ) - S.card)) := by
  -- step 1: the nonzero-frequency sum equals the (real) deviation
  have hid := completion_correlation_identity hψ S I
  have hsplit : ∑ b ∈ Finset.univ.erase (0 : F), eta ψ I b * (starRingEnd ℂ) (eta ψ S b)
        + eta ψ I 0 * (starRingEnd ℂ) (eta ψ S 0)
      = ∑ b : F, eta ψ I b * (starRingEnd ℂ) (eta ψ S b) :=
    Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (0 : F))
  have h0 : eta ψ I 0 * (starRingEnd ℂ) (eta ψ S 0) = ((I.card : ℂ)) * ((S.card : ℂ)) := by
    rw [eta_zero, eta_zero]
    simp
  have herase : ∑ b ∈ Finset.univ.erase (0 : F), eta ψ I b * (starRingEnd ℂ) (eta ψ S b)
      = (Fintype.card F : ℂ) * ((S ∩ I).card : ℂ) - (I.card : ℂ) * (S.card : ℂ) := by
    have := hsplit.trans hid
    rw [h0] at this
    linear_combination this
  -- step 2: bound the norm of the erased sum
  have hnorm : ‖∑ b ∈ Finset.univ.erase (0 : F), eta ψ I b * (starRingEnd ℂ) (eta ψ S b)‖
      ≤ Real.sqrt ((I.card : ℝ) * ((Fintype.card F : ℝ) - I.card))
        * Real.sqrt ((S.card : ℝ) * ((Fintype.card F : ℝ) - S.card)) := by
    calc ‖∑ b ∈ Finset.univ.erase (0 : F), eta ψ I b * (starRingEnd ℂ) (eta ψ S b)‖
        ≤ ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ I b * (starRingEnd ℂ) (eta ψ S b)‖ :=
          norm_sum_le _ _
      _ = ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ I b‖ * ‖eta ψ S b‖ := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [norm_mul, RCLike.norm_conj]
      _ ≤ Real.sqrt (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ I b‖ ^ 2)
            * Real.sqrt (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ S b‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = Real.sqrt ((I.card : ℝ) * ((Fintype.card F : ℝ) - I.card))
            * Real.sqrt ((S.card : ℝ) * ((Fintype.card F : ℝ) - S.card)) := by
          rw [sum_nonzero_eta_sq hψ I, sum_nonzero_eta_sq hψ S]
          congr 1 <;> · congr 1; ring
  -- step 3: the deviation is real, so its absolute value is the norm of the complex sum
  have hcast : (((Fintype.card F : ℝ) * ((S ∩ I).card : ℝ) - (S.card : ℝ) * I.card : ℝ) : ℂ)
      = ∑ b ∈ Finset.univ.erase (0 : F), eta ψ I b * (starRingEnd ℂ) (eta ψ S b) := by
    rw [herase]
    push_cast
    ring
  have habs : |(Fintype.card F : ℝ) * ((S ∩ I).card : ℝ) - (S.card : ℝ) * I.card|
      = ‖∑ b ∈ Finset.univ.erase (0 : F), eta ψ I b * (starRingEnd ℂ) (eta ψ S b)‖ := by
    rw [← hcast, Complex.norm_real, Real.norm_eq_abs]
  rw [habs]
  exact hnorm

/-- **The Esseen-loop resolution floor (no-contraction record).** The G80Z consumer converts
a per-arc deviation certificate `Δ` at `K` arcs into `M ≤ 2πn/K + K·Δ`; by AM–GM the
right-hand side is at least `2√(2πnΔ)` for EVERY `K > 0`. With `Δ` at the unconditional
certified scale `√(q−n)` (HEADLINE A) this floor is `≳ n^{3/4}` at proper subgroups and
`≫ √(n log q)`: the Esseen/Erdős–Turán self-reference cannot contract to the prize scale —
the quantitative extension of G78's KM-loop verdict to the ET loop. -/
theorem esseen_loop_resolution_floor {n Δ K : ℝ} (hn : 0 ≤ n) (hΔ : 0 ≤ Δ) (hK : 0 < K) :
    2 * Real.sqrt (2 * Real.pi * n * Δ) ≤ 2 * Real.pi * n / K + K * Δ := by
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have ha : (0 : ℝ) ≤ 2 * Real.pi * n / K := by positivity
  have hb : (0 : ℝ) ≤ K * Δ := by positivity
  have hprod : (2 * Real.pi * n / K) * (K * Δ) = 2 * Real.pi * n * Δ := by
    field_simp
  have hsq := sq_nonneg (Real.sqrt (2 * Real.pi * n / K) - Real.sqrt (K * Δ))
  have h1 : Real.sqrt (2 * Real.pi * n / K) ^ 2 = 2 * Real.pi * n / K := Real.sq_sqrt ha
  have h2 : Real.sqrt (K * Δ) ^ 2 = K * Δ := Real.sq_sqrt hb
  have hmul : Real.sqrt (2 * Real.pi * n / K) * Real.sqrt (K * Δ)
      = Real.sqrt (2 * Real.pi * n * Δ) := by
    rw [← Real.sqrt_mul ha, hprod]
  nlinarith [hsq, h1, h2, hmul]

/-! ## Part 2 — the NON-FOURIER small-ball certificate: integer-lift multiplicative rigidity -/

/-- `valMinAbs` recovers small integers exactly: if `2·|z| < p` then the minimal-absolute
representative of `(z : ZMod p)` is `z` itself. -/
theorem valMinAbs_intCast_of_two_mul_abs_lt {p : ℕ} [NeZero p] {z : ℤ}
    (hz : 2 * z.natAbs < p) : ((z : ZMod p)).valMinAbs = z := by
  have hzabs : 2 * |z| < (p : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hz
  have h2 : |z * 2| < (p : ℤ) := by
    rw [abs_mul, abs_two]
    linarith
  have h3 := abs_lt.mp h2
  rw [ZMod.valMinAbs_spec]
  exact ⟨rfl, Set.mem_Ioc.mpr ⟨h3.1, h3.2.le⟩⟩

/-- **HEADLINE C — dilated-orbit short-interval rigidity (difference form).** Let `p` be
prime, `x ∈ ZMod p` with `xⁿ = 1` (`n ≥ 1`) but `x² ≠ 1`, and `b ≠ 0`. If every consecutive
difference of the dilated orbit, `b·x^{k+1} − b·x^k`, has minimal-absolute representative
`< V` with `2V² < p`, we reach a contradiction. Mechanism (NO Fourier, NO multiplicative
energy, NO Weil): the lifted differences `m_k` satisfy `m_j·m_k ≡ m_0·m_{j+k} (mod p)` with
both sides below `p/1` in absolute value, hence EQUAL in ℤ; the lift is therefore a geometric
integer sequence, and periodicity `m_n = m_0` forces `m_1 = ±m_0`, i.e. `x = ±1`. -/
theorem dilated_orbit_short_interval_rigidity {p : ℕ} [hp : Fact p.Prime]
    {x b : ZMod p} {n V : ℕ}
    (hn : 0 < n) (hxn : x ^ n = 1) (hx2 : x ^ 2 ≠ 1) (hb : b ≠ 0)
    (hV : 2 * V ^ 2 < p)
    (hm : ∀ k : ℕ, (b * x ^ (k + 1) - b * x ^ k).valMinAbs.natAbs < V) : False := by
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  have hx1 : x ≠ 1 := fun h => hx2 (by rw [h]; norm_num)
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hxn
    exact zero_ne_one hxn
  -- the integer lift of the consecutive differences
  set m : ℕ → ℤ := fun k => (b * x ^ (k + 1) - b * x ^ k).valMinAbs with hmdef
  have hcast : ∀ k : ℕ, ((m k : ℤ) : ZMod p) = b * x ^ (k + 1) - b * x ^ k := fun k =>
    ZMod.coe_valMinAbs _
  have hm0ne : ∀ k : ℕ, m k ≠ 0 := by
    intro k hk
    have : b * x ^ (k + 1) - b * x ^ k = 0 := by
      rw [← hcast k, hk]
      norm_num
    have hfac : b * x ^ k * (x - 1) = 0 := by
      linear_combination this
    rcases mul_eq_zero.mp hfac with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact hb h'
      · exact pow_ne_zero k hx0 h'
    · exact hx1 (by linear_combination h)
  have habs : ∀ k : ℕ, |m k| < (V : ℤ) := by
    intro k
    have := hm k
    have h1 : |m k| = ((m k).natAbs : ℤ) := (Int.natCast_natAbs _).symm
    rw [h1]
    exact_mod_cast this
  -- the key mod-p identity, upgraded to ℤ by size
  have hkey : ∀ j k : ℕ, m j * m k = m 0 * m (j + k) := by
    intro j k
    have hmod : (((m j * m k - m 0 * m (j + k)) : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [hcast j, hcast k, hcast 0, hcast (j + k)]
      ring
    have hdvd : (p : ℤ) ∣ (m j * m k - m 0 * m (j + k)) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hmod
    have hsize : |m j * m k - m 0 * m (j + k)| < (p : ℤ) := by
      have h1 : |m j * m k| < (V : ℤ) * V := by
        rw [abs_mul]
        exact mul_lt_mul'' (habs j) (habs k) (abs_nonneg _) (abs_nonneg _)
      have h2 : |m 0 * m (j + k)| < (V : ℤ) * V := by
        rw [abs_mul]
        exact mul_lt_mul'' (habs 0) (habs (j + k)) (abs_nonneg _) (abs_nonneg _)
      have h3 : (2 : ℤ) * V ^ 2 < (p : ℤ) := by exact_mod_cast hV
      calc |m j * m k - m 0 * m (j + k)| ≤ |m j * m k| + |m 0 * m (j + k)| := abs_sub _ _
        _ < (V : ℤ) * V + (V : ℤ) * V := by linarith
        _ = 2 * (V : ℤ) ^ 2 := by ring
        _ < (p : ℤ) := h3
    have := Int.eq_zero_of_abs_lt_dvd hdvd hsize
    linarith [this]
  -- the lift is a geometric integer sequence
  have hgeom : ∀ k : ℕ, m k * m 0 ^ k = m 0 * m 1 ^ k := by
    intro k
    induction k with
    | zero => ring
    | succ k ih =>
      have hstep : m 1 * m k = m 0 * m (k + 1) := by
        have := hkey 1 k
        rwa [Nat.add_comm 1 k] at this
      calc m (k + 1) * m 0 ^ (k + 1) = (m 0 * m (k + 1)) * m 0 ^ k := by ring
        _ = (m 1 * m k) * m 0 ^ k := by rw [← hstep]
        _ = m 1 * (m k * m 0 ^ k) := by ring
        _ = m 1 * (m 0 * m 1 ^ k) := by rw [ih]
        _ = m 0 * m 1 ^ (k + 1) := by ring
  -- periodicity: m n = m 0
  have hper : m n = m 0 := by
    have hx' : b * x ^ (n + 1) - b * x ^ n = b * x ^ (0 + 1) - b * x ^ 0 := by
      rw [pow_succ, hxn, zero_add, pow_one, pow_zero, one_mul, mul_one]
    show (b * x ^ (n + 1) - b * x ^ n).valMinAbs = (b * x ^ (0 + 1) - b * x ^ 0).valMinAbs
    rw [hx']
  -- specialize the geometric law at k = n and cancel m 0
  have hpow : m 0 ^ n = m 1 ^ n := by
    have h := hgeom n
    rw [hper] at h
    exact mul_left_cancel₀ (hm0ne 0) h
  -- |m 0| = |m 1|, hence m 1 = ± m 0
  have hnatAbs : (m 0).natAbs = (m 1).natAbs := by
    have h1 : ((m 0).natAbs) ^ n = ((m 1).natAbs) ^ n := by
      have := congrArg Int.natAbs hpow
      rwa [Int.natAbs_pow, Int.natAbs_pow] at this
    exact Nat.pow_left_injective hn.ne' h1
  have hpm : m 1 = m 0 ∨ m 1 = -m 0 := by
    rcases Int.natAbs_eq_natAbs_iff.mp hnatAbs.symm with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- both cases pin x = ±1, contradicting x² ≠ 1
  rcases hpm with h | h
  · -- m 1 = m 0 ⟹ b(x−1)² = 0 ⟹ x = 1
    have heq : ((m 1 : ℤ) : ZMod p) = ((m 0 : ℤ) : ZMod p) := by rw [h]
    rw [hcast 1, hcast 0] at heq
    have hfac : b * ((x - 1) * (x - 1)) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact hb h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact hx1 (by linear_combination h'')
      · exact hx1 (by linear_combination h'')
  · -- m 1 = −m 0 ⟹ b(x²−1) = 0 ⟹ x² = 1
    have heq : ((m 1 : ℤ) : ZMod p) = -((m 0 : ℤ) : ZMod p) := by
      rw [h]
      push_cast
      ring
    rw [hcast 1, hcast 0] at heq
    have hfac : b * (x ^ 2 - 1) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact hb h'
    · exact hx2 (by linear_combination h')

/-- The interval `{a, a+1, …, a+V−1} ⊆ ZMod p`. -/
def interval {p : ℕ} (a : ZMod p) (V : ℕ) : Finset (ZMod p) :=
  (Finset.range V).image (fun i : ℕ => a + (i : ZMod p))

/-- **HEADLINE C, interval form.** For `p` prime, `x` of order `n ≥ 3` (encoded as `xⁿ = 1`,
`x² ≠ 1`) and ANY dilation `b ≠ 0`: as soon as `2V² < p`, the dilated orbit `{b·x^k}` is NOT
contained in any interval of length `V`. Instantiated at a generator `x` of `μ_n`, this says:
NO dilate of the smooth subgroup concentrates in ANY arc of length `< √(p/2)` — a b-uniform,
completely elementary, NON-Fourier anti-concentration certificate at total-mass scale. -/
theorem not_dilated_orbit_subset_interval {p : ℕ} [hp : Fact p.Prime]
    {x b : ZMod p} {n V : ℕ} {a : ZMod p}
    (hn : 0 < n) (hxn : x ^ n = 1) (hx2 : x ^ 2 ≠ 1) (hb : b ≠ 0)
    (hV : 2 * V ^ 2 < p) :
    ¬ (∀ k : ℕ, b * x ^ k ∈ interval a V) := by
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  intro hsub
  refine dilated_orbit_short_interval_rigidity hn hxn hx2 hb hV (fun k => ?_)
  obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp (hsub (k + 1))
  obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp (hsub k)
  rw [Finset.mem_range] at hi hj
  have hdiff : b * x ^ (k + 1) - b * x ^ k = (((i : ℤ) - (j : ℤ) : ℤ) : ZMod p) := by
    rw [← hie, ← hje]
    push_cast
    ring
  have hijV : ((i : ℤ) - (j : ℤ)).natAbs < V := by omega
  have hsmall : 2 * ((i : ℤ) - (j : ℤ)).natAbs < p := by
    have hV1 : 1 ≤ V := by omega
    have : 2 * ((i : ℤ) - (j : ℤ)).natAbs < 2 * V := by omega
    have hVsq : 2 * V ≤ 2 * V ^ 2 := by nlinarith
    omega
  rw [hdiff, valMinAbs_intCast_of_two_mul_abs_lt hsmall]
  exact hijV

end ArkLib.ProximityGap.Frontier.G99ErdosTuranLadderCertificate

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G99ErdosTuranLadderCertificate.eta_mul_mem
#print axioms
  ArkLib.ProximityGap.Frontier.G99ErdosTuranLadderCertificate.sum_nonzero_eta_sq
#print axioms
  ArkLib.ProximityGap.Frontier.G99ErdosTuranLadderCertificate.ladder_sq_le_of_injective
#print axioms
  ArkLib.ProximityGap.Frontier.G99ErdosTuranLadderCertificate.ladder_sq_le_of_distinct_cosets
#print axioms
  ArkLib.ProximityGap.Frontier.G99ErdosTuranLadderCertificate.sum_range_inv_sq_le_two
#print axioms
  ArkLib.ProximityGap.Frontier.G99ErdosTuranLadderCertificate.ladder_weighted_l1_le_of_distinct_cosets
#print axioms
  ArkLib.ProximityGap.Frontier.G99ErdosTuranLadderCertificate.gaussPeriod_harmonic_ladder_bound
#print axioms
  ArkLib.ProximityGap.Frontier.G99ErdosTuranLadderCertificate.arc_discrepancy_of_erdosTuran_hypothesis
#print axioms
  ArkLib.ProximityGap.Frontier.G99ErdosTuranLadderCertificate.completion_correlation_identity
#print axioms
  ArkLib.ProximityGap.Frontier.G99ErdosTuranLadderCertificate.completion_arc_deviation_bound
#print axioms
  ArkLib.ProximityGap.Frontier.G99ErdosTuranLadderCertificate.esseen_loop_resolution_floor
#print axioms
  ArkLib.ProximityGap.Frontier.G99ErdosTuranLadderCertificate.valMinAbs_intCast_of_two_mul_abs_lt
#print axioms
  ArkLib.ProximityGap.Frontier.G99ErdosTuranLadderCertificate.dilated_orbit_short_interval_rigidity
#print axioms
  ArkLib.ProximityGap.Frontier.G99ErdosTuranLadderCertificate.not_dilated_orbit_subset_interval
