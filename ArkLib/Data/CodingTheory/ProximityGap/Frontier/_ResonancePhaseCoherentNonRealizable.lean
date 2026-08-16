/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumWorstCase
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceStickelbergerCeilingDiagnostic

/-!
# Door-(ii) constraint: the phase-aligned resonator is NON-REALIZABLE (issue #444, Lane 3)

`_ResonanceStickelbergerCeilingDiagnostic` proved that the Stickelberger-phase-aligned
("Candidate 3") resonator's coherent value is the triangle SATURATION `((m-1)√q+1)/m ≈ √q`
(an UPPER extreme, not a floor), and stated the residual `PhaseCoherentUniform ψ d` — the
hypothesis that some FIXED nonnegative weight `w` makes the completion sum coherent at EVERY
frequency `b ≠ 0` simultaneously, i.e. forces every period to attain the saturation value. That
file proved only the FORWARD direction (`phaseCoherentUniform_forces_saturation`): coherence ⇒
every `‖η_b‖` equals the saturation value. The diagnostic asserted in prose that
`PhaseCoherentUniform` is FALSE (contradicting the Parseval average) but did NOT close it.

**This file closes it, axiom-clean.** The phase-aligned resonator is non-realizable: in the prize
regime `4d ≤ q − 1` (always true since `q ≈ n^β`, `β ≈ 4–5`, `d = n`), `PhaseCoherentUniform ψ d`
is FALSE. The lever is the EXACT second moment `∑_b ‖η_b‖² = q·d`
(`subgroup_gaussSum_secondMoment`): if every nonzero period saturated to `≈ √q`, the `q − 1`
nonzero periods alone would contribute `≳ (q−1)·q/4` to a sum that is exactly `q·d`, forcing
`q − 1 < 4d` — false in the regime. The completion/√q-resonator route therefore CANNOT deliver a
`b`-uniform lower bound on `M`; it is a door-(ii) (√q-completion) object that overshoots, exactly
as the tetrachotomy demands. No CORE upper bound, no cancellation, no anti-concentration claim.

PROBE: `scripts/probes/probe_phasecoherent_refute.py` (exact complex `η` over thin `μ_n`, `p ≫ n³`,
n = 8,16,32). The claimed-coherent second moment `(q−1)·sat²` exceeds the true `qn − n²` by a factor
`≈ q/n` GROWING in n (70, 257, 1025), and the measured `M` (6.9, 11.1, 17.2) sits FAR below the
saturation value (23.5, 64, 181). The contradiction is reproducible, not larped.

Honesty (§6 contract): this is a Lane-3 constraint lemma (a refuted-lever lock backing the
no-fifth-door), not a CORE result. It proves the phase-aligned resonator is non-realizable; it does
NOT prove any bound on `M` beyond the already-in-tree `‖η_b‖ ≤ √q`.
-/

set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase
open ArkLib.ProximityGap.Frontier.RES2Diagnostics

namespace ArkLib.ProximityGap.Frontier.ResonancePhaseCoherentNonRealizable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `η_0 = |G|` (the trivial frequency sums the all-ones character). -/
theorem eta_zero (ψ : AddChar F ℂ) (G : Finset F) :
    eta ψ G 0 = (G.card : ℂ) := by
  simp [eta, AddChar.map_zero_eq_one]

/-- `‖η_0‖² = |G|²` for the torsion subgroup `G`, as a real number. -/
theorem norm_eta_zero_sq (ψ : AddChar F ℂ) (G : Finset F) :
    ‖eta ψ G 0‖ ^ 2 = (G.card : ℝ) ^ 2 := by
  rw [eta_zero ψ G, Complex.norm_natCast]

/-- **The second moment over the NONZERO frequencies, exactly.**
`∑_{b≠0} ‖η_b‖² = q·|G| − |G|²` (peel off the trivial frequency from the Parseval total). -/
theorem secondMoment_nonzero {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b ∈ (univ.erase (0 : F)), ‖eta ψ G b‖ ^ 2
      = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
  have htotal := subgroup_gaussSum_secondMoment hψ G
  have hsplit : ∑ b : F, ‖eta ψ G b‖ ^ 2
      = ‖eta ψ G 0‖ ^ 2 + ∑ b ∈ (univ.erase (0 : F)), ‖eta ψ G b‖ ^ 2 := by
    rw [← Finset.sum_erase_add univ _ (Finset.mem_univ (0 : F))]
    ring
  rw [hsplit, norm_eta_zero_sq] at htotal
  linarith [htotal]

/-! ## The non-realizability theorem -/

/-- **The phase-aligned resonator is NON-REALIZABLE in the prize regime.**

In the regime `4d ≤ q − 1` (equivalently `q ≥ 4d + 1`; always satisfied when `q ≈ d^β`, `β ≥ 4`,
since then `q ≫ d`), the uniform phase-coherence hypothesis `PhaseCoherentUniform ψ d` is FALSE.

If it held, then for every `b ≠ 0`,
`m·‖η_b‖ = (m−1)·√q + 1` with `m = (q−1)/d`, hence `m²·‖η_b‖² ≥ (m−1)²·q`.
Summing over the `q − 1` nonzero frequencies and using the exact second moment
`∑_{b≠0}‖η_b‖² = q·d − d² ≤ q·d` gives `(q−1)·(m−1)²·q ≤ m²·q·d`, i.e.
`(q−1)·(m−1)² ≤ m²·d`. With `m ≥ 2` (from `q − 1 ≥ 2d`), `(m−1)²/m² ≥ 1/4`, so `(q−1)/4 ≤ d`,
contradicting `4d ≤ q − 1`. -/
theorem not_phaseCoherentUniform_of_prizeRegime
    {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hregime : 4 * d ≤ Fintype.card F - 1) :
    ¬ PhaseCoherentUniform ψ d := by
  intro hcoh
  -- abbreviations
  set q : ℕ := Fintype.card F with hq
  set m : ℕ := (Fintype.card F - 1) / d with hm
  -- m·d = q − 1, and m ≥ 1 (in fact ≥ 4 once we use the regime)
  have hmd : m * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  -- from the regime, q − 1 ≥ 4d ⇒ m ≥ 4 ⇒ m ≥ 2
  have hm4 : 4 ≤ m := by
    by_contra hlt
    push_neg at hlt
    -- m ≤ 3 ⇒ m·d ≤ 3d < 4d ≤ q − 1 = m·d, contradiction
    have : m * d ≤ 3 * d := by
      have : m ≤ 3 := by omega
      exact Nat.mul_le_mul_right d this
    rw [hmd] at this
    omega
  have hm2 : 2 ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  -- the per-frequency saturation, from coherence
  have hsat := phaseCoherentUniform_forces_saturation hcoh
  -- card of the torsion subgroup is d
  have hcard : (torsion F d).card = d := card_torsion hd hd0
  -- For each b ≠ 0:  m²·‖η_b‖² ≥ (m−1)²·q   (square the saturation, drop the +1 cross terms ≥ 0)
  have hper : ∀ b ∈ (univ.erase (0 : F)),
      ((m : ℝ) - 1) ^ 2 * (q : ℝ) ≤ (m : ℝ) ^ 2 * ‖eta ψ (torsion F d) b‖ ^ 2 := by
    intro b hb
    have hbne : b ≠ 0 := Finset.ne_of_mem_erase hb
    have hsb := hsat b hbne
    -- hsb : ((q−1)/d : ℕ) * ‖η_b‖ = ((q−1)/d − 1 : ℕ)·√(card F) + 1
    -- fold `Fintype.card F` back to `q` (set only rewrote pre-existing hyps)
    rw [← hq] at hsb
    -- ((q − 1)/d : ℕ) = m and ((q−1)/d − 1 : ℕ) = m − 1 as nats
    have hmcast : (((q - 1) / d : ℕ) : ℝ) = (m : ℝ) := by rw [hm, hq]
    have hm1cast : (((q - 1) / d - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have hge : (1 : ℕ) ≤ (q - 1) / d := by
        have : m = (q - 1) / d := by rw [hm, hq]
        rw [← this]; omega
      have : (((q - 1) / d - 1 : ℕ) : ℝ) = (((q - 1) / d : ℕ) : ℝ) - 1 := by
        push_cast [hge]; ring
      rw [this, hmcast]
    rw [hmcast, hm1cast] at hsb
    -- now hsb : (m : ℝ) * ‖η_b‖ = ((m : ℝ) − 1) * √q + 1
    set e : ℝ := ‖eta ψ (torsion F d) b‖ with he
    have hsqrtq : Real.sqrt (q : ℝ) ^ 2 = (q : ℝ) := by
      rw [Real.sq_sqrt (by positivity)]
    have hm1nn : (0 : ℝ) ≤ (m : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      linarith
    have hsqrtnn : (0 : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
    -- (m·e)² = ((m−1)√q + 1)² = (m−1)²q + 2(m−1)√q + 1 ≥ (m−1)²q
    have hsq : ((m : ℝ) * e) ^ 2 = ((m : ℝ) - 1) ^ 2 * (q : ℝ)
        + (2 * ((m : ℝ) - 1) * Real.sqrt (q : ℝ) + 1) := by
      rw [hsb]
      have : (((m : ℝ) - 1) * Real.sqrt (q : ℝ) + 1) ^ 2
          = ((m : ℝ) - 1) ^ 2 * (Real.sqrt (q : ℝ)) ^ 2
            + (2 * ((m : ℝ) - 1) * Real.sqrt (q : ℝ) + 1) := by ring
      rw [this, hsqrtq]
    have hcross : (0 : ℝ) ≤ 2 * ((m : ℝ) - 1) * Real.sqrt (q : ℝ) + 1 := by positivity
    have hlhs : ((m : ℝ) * e) ^ 2 = (m : ℝ) ^ 2 * e ^ 2 := by ring
    nlinarith [hsq, hcross, hlhs]
  -- Sum the per-frequency lower bound over the q − 1 nonzero frequencies.
  have hcardE : (univ.erase (0 : F)).card = q - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hsum_lb : ((q : ℝ) - 1) * (((m : ℝ) - 1) ^ 2 * (q : ℝ))
      ≤ (m : ℝ) ^ 2 * (∑ b ∈ (univ.erase (0 : F)), ‖eta ψ (torsion F d) b‖ ^ 2) := by
    have hconst : ∑ _b ∈ (univ.erase (0 : F)), (((m : ℝ) - 1) ^ 2 * (q : ℝ))
        = ((univ.erase (0 : F)).card : ℝ) * (((m : ℝ) - 1) ^ 2 * (q : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hsumineq : ∑ b ∈ (univ.erase (0 : F)), (((m : ℝ) - 1) ^ 2 * (q : ℝ))
        ≤ ∑ b ∈ (univ.erase (0 : F)), (m : ℝ) ^ 2 * ‖eta ψ (torsion F d) b‖ ^ 2 :=
      Finset.sum_le_sum hper
    rw [hconst, hcardE] at hsumineq
    rw [← Finset.mul_sum] at hsumineq
    -- ((q − 1 : ℕ) : ℝ) = (q : ℝ) − 1  (q ≥ 1)
    have hq1 : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      have : 1 ≤ q := by rw [hq]; exact Fintype.card_pos
      push_cast [this]; ring
    rw [hq1] at hsumineq
    exact hsumineq
  -- The exact nonzero second moment: ∑_{b≠0}‖η_b‖² = q·d − d² ≤ q·d.
  have hexact := secondMoment_nonzero hψ (torsion F d)
  rw [hcard] at hexact
  have hle_qd : (∑ b ∈ (univ.erase (0 : F)), ‖eta ψ (torsion F d) b‖ ^ 2)
      ≤ (q : ℝ) * (d : ℝ) := by
    rw [hexact, hq]; nlinarith [sq_nonneg ((d : ℝ))]
  -- Combine: (q−1)(m−1)²q ≤ m²·(q·d).
  have hcombine : ((q : ℝ) - 1) * (((m : ℝ) - 1) ^ 2 * (q : ℝ))
      ≤ (m : ℝ) ^ 2 * ((q : ℝ) * (d : ℝ)) := by
    have hm2nn : (0 : ℝ) ≤ (m : ℝ) ^ 2 := by positivity
    calc ((q : ℝ) - 1) * (((m : ℝ) - 1) ^ 2 * (q : ℝ))
        ≤ (m : ℝ) ^ 2 * (∑ b ∈ (univ.erase (0 : F)), ‖eta ψ (torsion F d) b‖ ^ 2) := hsum_lb
      _ ≤ (m : ℝ) ^ 2 * ((q : ℝ) * (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hle_qd hm2nn
  -- Now derive a contradiction with the regime.
  -- Reals: q ≥ 1, m ≥ 2, m·d = q − 1.
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by rw [hq]; exact_mod_cast Fintype.card_pos
  have hmR2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hmdR : (m : ℝ) * (d : ℝ) = (q : ℝ) - 1 := by
    have : ((m * d : ℕ) : ℝ) = ((Fintype.card F - 1 : ℕ) : ℝ) := by rw [hmd]
    have hq1nat : ((Fintype.card F - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      have : 1 ≤ Fintype.card F := Fintype.card_pos
      rw [hq]; push_cast [this]; ring
    push_cast at this
    rw [hq1nat] at this
    linarith [this]
  -- regime in reals: 4d ≤ q − 1 = m·d  ⇒  4 ≤ m (already have), and we need (q−1) ≤ 4d false.
  have hregimeR : 4 * (d : ℝ) ≤ (q : ℝ) - 1 := by
    have hnat : ((4 * d : ℕ) : ℝ) ≤ ((Fintype.card F - 1 : ℕ) : ℝ) := by exact_mod_cast hregime
    have hq1nat : ((Fintype.card F - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      have : 1 ≤ Fintype.card F := Fintype.card_pos
      rw [hq]; push_cast [this]; ring
    rw [hq1nat] at hnat
    push_cast at hnat
    linarith [hnat]
  -- From hcombine, dividing by q > 0:  (q−1)(m−1)² ≤ m²·d.
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith [hqR]
  have hred : ((q : ℝ) - 1) * ((m : ℝ) - 1) ^ 2 ≤ (m : ℝ) ^ 2 * (d : ℝ) := by
    have := hcombine
    -- divide both sides by q
    nlinarith [hcombine, hqpos, sq_nonneg ((m : ℝ) - 1), hdR]
  -- Substitute q − 1 = m·d into hred and cancel the common positive factor m·d:
  --   (m·d)·(m−1)² ≤ m²·d  ⇒  d·m·[(m−1)² − m] ≤ 0  ⇒  (m−1)² ≤ m  (d,m > 0)
  -- i.e. m² − 3m + 1 ≤ 0, impossible for m ≥ 4 (m² − 3m + 1 ≥ 16 − 12 + 1 = 5 > 0).
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith [hmR2]
  have hmR4 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
  have hsub : ((m : ℝ) * (d : ℝ)) * ((m : ℝ) - 1) ^ 2 ≤ (m : ℝ) ^ 2 * (d : ℝ) := by
    have h := hred
    rw [← hmdR] at h
    exact h
  -- the regime gives m ≥ 4; (m−1)² ≤ m needs m ≤ ~2.62, contradiction.
  nlinarith [hsub, hmpos, hdR, hmR4, sq_nonneg ((m : ℝ) - 1)]

end ArkLib.ProximityGap.Frontier.ResonancePhaseCoherentNonRealizable

#print axioms
  ArkLib.ProximityGap.Frontier.ResonancePhaseCoherentNonRealizable.eta_zero
#print axioms
  ArkLib.ProximityGap.Frontier.ResonancePhaseCoherentNonRealizable.secondMoment_nonzero
#print axioms
  ArkLib.ProximityGap.Frontier.ResonancePhaseCoherentNonRealizable.not_phaseCoherentUniform_of_prizeRegime
