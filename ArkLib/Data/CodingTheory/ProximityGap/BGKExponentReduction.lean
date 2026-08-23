/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum

/-!
# PIECE B — the BGK / di Benedetto power-saving exponent as a named literature Prop (#407)

This file formalizes the **honest state-of-the-art** incomplete-character-sum upper bound for a
thin multiplicative subgroup `G = μ_n ≤ F_p^*`, as the named (NOT fabricated) literature input,
together with the real **reduction wiring** that threads it into the live in-tree consumer
`WorstCaseIncompleteSumBound`.

## The target (honest SOTA, NON-prize)

For `B := max_{b≠0} ‖η_b‖` (`η_b = eta ψ G b = Σ_{x∈G} ψ(b·x)`, the incomplete subgroup Gauss
sum / non-principal eigenvalue of the generalized Paley graph `Cay(F_p, μ_n)`):

* **[BGK06]** Bourgain–Glibichuk–Konyagin, *Estimates for the number of sums and products and for
  exponential sums in fields of prime order*, J. London Math. Soc. **73** (2006) 380–398: for every
  `ε > 0` there is `δ = δ(ε) > 0` with `B ≤ n^{1-δ}` whenever `n > p^ε` (qualitatively
  `B ≤ n^{1-o(1)}`; the constant `δ` is ineffective/tiny). Expository proof: Kowalski,
  *Exponential sums over small subgroups, revisited*, arXiv:2401.04756.

* **[diB20]** di Benedetto–Garaev–García–González-Sánchez–Shparlinski–Trujillo, *New estimates for
  exponential sums over multiplicative subgroups and intervals in prime fields*, J. Number Theory
  (2020), arXiv:2003.06165, Thm 3.1: `B ≲ n^{2689/2880} · p^{1/72}`, whose **corollary** for
  `n > p^{1/4}` is the headline power-saving `B ≤ n^{1 - 31/2880 + o(1)}` (i.e. cancellation
  exponent `δ = 31/2880 ≈ 0.0108`, the current SOTA). This does **not** reach the conjectured
  Ramanujan / Paley-Graph value `B ≤ √(2 n ln q)` (`δ = 1/2`); it is the honest open state.

## The reduction chain (named inputs + real wiring)

The deep sum–product proof of BGK is NOT formalized here. Instead, following the literature
structure, we name TWO inputs and wire them:

1. `SumProductEnergyBound G c` : the **additive-energy** estimate
   `E(G) ≤ n^{3-c}` (`c > 0`), the sum–product output that the BGK proof consumes (the additive
   energy of a multiplicative subgroup is sub-`n^3`). NAMED Prop, not proved.

2. `BGKCharSumBound C G δ` : the **character-sum** conclusion
   `∀ b ≠ 0, ‖η_b‖ ≤ C · n^{1-δ}` (the BGK / di Benedetto bound itself). NAMED Prop, not proved.

The PROVEN content (axiom-clean) is the *wiring around* these inputs:

* `worstCaseIncompleteSumBound_of_bgk` : `BGKCharSumBound C G δ ⟹ WorstCaseIncompleteSumBound`
  at scale `M = (C·n^{1-δ})²` — threads BGK into the live energy/incidence consumer.
* `diBenedetto_charSum_of_named` / `bgk_charSum_of_named` : the conditional headline
  `B ≤ C·n^{1 - 31/2880}` (di Benedetto) and `B ≤ C·n^{1-δ}` (BGK), each `of_BGK` (i.e. assuming
  the named character-sum Prop), with the literature exponents pinned as definitions.
* `worstCaseIncompleteSumBound_diBenedetto` : the di Benedetto exponent, fully threaded into
  `WorstCaseIncompleteSumBound` at `M = (C·n^{1 - 31/2880})²`.
* `energy_envelope_of_sumProduct` : the additive-energy input, used (not decorative): the
  4th-moment identity `Σ_b ‖η_b‖⁴ = q·E(G)` plus `SumProductEnergyBound` give the genuine
  `L⁴`-envelope `‖η_b‖⁴ ≤ q·n^{3-c}` per frequency — the elementary half of the BGK chain.

**Honesty (non-negotiable):** `SumProductEnergyBound` and `BGKCharSumBound` are the literature
theorems, stated as `def … : Prop` and never asserted/`sorry`-ed. The chain *around* them is
real and axiom-clean. The di Benedetto exponent `δ = 31/2880` is the genuine SOTA and is strictly
below the prize exponent `1/2`, so this is explicitly a NON-prize-closing result.

All proofs axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #407.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

namespace ArkLib.ProximityGap.BGKExponentReduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The named literature inputs (two Props; never asserted) -/

/-- **Sum–product additive-energy input** (NAMED, not proved): the additive energy of the smooth
subgroup `G = μ_n` is sub-`n^3`, `E(G) ≤ n^{3-c}` with cancellation exponent `c > 0`. This is the
additive-combinatorics output that the BGK / di Benedetto exponential-sum proof consumes (a
multiplicative subgroup has small additive energy by sum–product / Rudnev point–plane). It stays a
`def … : Prop`; the deep proof is not formalized here. -/
def SumProductEnergyBound (G : Finset F) (c : ℝ) : Prop :=
  (addEnergy G : ℝ) ≤ (G.card : ℝ) ^ (3 - c)

/-- **BGK / di Benedetto character-sum input** (NAMED, not proved): every nonzero frequency `b`
has `‖η_b‖ ≤ C · n^{1-δ}`, the power-saving exponential-sum bound for the thin multiplicative
subgroup `G = μ_n`. `δ` is the cancellation exponent: BGK gives some `δ > 0` (`n^{1-o(1)}`); di
Benedetto pins `δ = 31/2880`. This is the deep theorem itself, stated as a `def … : Prop` and
never asserted. -/
def BGKCharSumBound (C : ℝ) (ψ : AddChar F ℂ) (G : Finset F) (δ : ℝ) : Prop :=
  ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ C * (G.card : ℝ) ^ (1 - δ)

/-! ## The literature exponents, pinned as definitions -/

/-- **The di Benedetto SOTA cancellation exponent** `δ = 31/2880 ≈ 0.0108`. From [diB20] Thm 3.1
corollary for `n > p^{1/4}`: `B ≤ n^{1 - 31/2880 + o(1)}`, the best *proven* power saving. -/
noncomputable def diBenedettoDelta : ℝ := 31 / 2880

/-- **The prize cancellation exponent** `δ = 1/2` (Ramanujan / Paley-Graph-Conjecture value): the
prize floor `B ≤ √(2 n ln q)` needs `δ = 1/2 - o(1)`. Open; far beyond the proven SOTA. -/
noncomputable def prizeDelta : ℝ := 1 / 2

/-- The proven SOTA exponent is strictly below the prize exponent: `31/2880 < 1/2`. This is the
honest gap — di Benedetto is the state of the art and is NOT prize-closing. -/
theorem diBenedettoDelta_lt_prizeDelta : diBenedettoDelta < prizeDelta := by
  unfold diBenedettoDelta prizeDelta; norm_num

/-- The di Benedetto exponent is a genuine power saving over the trivial Weil/total bound: the
cancellation exponent is strictly positive, `0 < 31/2880`. -/
theorem diBenedettoDelta_pos : 0 < diBenedettoDelta := by
  unfold diBenedettoDelta; norm_num

/-! ## Wiring 1 — BGK character-sum input ⟹ live `WorstCaseIncompleteSumBound` -/

/-- **BGK ⟹ the in-tree open worst-case incomplete-sum residual.** From `BGKCharSumBound C ψ G δ`
(`‖η_b‖ ≤ C·n^{1-δ}` for all `b ≠ 0`) we get `‖η_b‖² ≤ (C·n^{1-δ})²`, which is exactly
`WorstCaseIncompleteSumBound ψ G M` at `M = (C·n^{1-δ})²`. This threads the named BGK bound into
the LIVE consumer `addEnergy_le_of_worstCase` / the interior-`δ*` incidence chain. -/
theorem worstCaseIncompleteSumBound_of_bgk {ψ : AddChar F ℂ} {G : Finset F} {C δ : ℝ}
    (h : BGKCharSumBound C ψ G δ) :
    WorstCaseIncompleteSumBound ψ G ((C * (G.card : ℝ) ^ (1 - δ)) ^ 2) := by
  intro b hb
  exact pow_le_pow_left₀ (norm_nonneg _) (h b hb) 2

/-- **End-to-end BGK additive-energy budget.** Composing `worstCaseIncompleteSumBound_of_bgk` with
the in-tree consumer `addEnergy_le_of_worstCase`: a BGK bound at `(C, δ)` yields
`q·E(G) ≤ |G|⁴ + (C·n^{1-δ})²·(q·|G|)`. The honest energy envelope delivered by the SOTA. -/
theorem addEnergy_le_of_bgk {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {C δ : ℝ}
    (hC : 0 ≤ C) (h : BGKCharSumBound C ψ G δ) :
    (Fintype.card F : ℝ) * (addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 4
        + (C * (G.card : ℝ) ^ (1 - δ)) ^ 2 * ((Fintype.card F : ℝ) * G.card) :=
  addEnergy_le_of_worstCase hψ G (by positivity) (worstCaseIncompleteSumBound_of_bgk h)

/-! ## Wiring 2 — the conditional headline `B ≤ n^{1-c} of_BGK` at the literature exponents -/

/-- **The conditional BGK headline `B ≤ C·n^{1-δ}`** (`of_BGK`): assuming the named character-sum
Prop `BGKCharSumBound C ψ G δ`, every nonzero frequency satisfies `‖η_b‖ ≤ C·n^{1-δ}`. This is the
honest restatement of the named input — the deep proof is the literature's, not ours. -/
theorem bgk_charSum_of_named {ψ : AddChar F ℂ} {G : Finset F} {C δ : ℝ}
    (h : BGKCharSumBound C ψ G δ) :
    ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ C * (G.card : ℝ) ^ (1 - δ) :=
  h

/-- **The conditional di Benedetto headline `B ≤ C·n^{1 - 31/2880}`** (`of_BGK`): assuming the
named character-sum Prop at the di Benedetto exponent `δ = 31/2880`, every nonzero frequency
satisfies `‖η_b‖ ≤ C·n^{1 - 31/2880}`. This is the SOTA bound, pinned at the literature exponent. -/
theorem diBenedetto_charSum_of_named {ψ : AddChar F ℂ} {G : Finset F} {C : ℝ}
    (h : BGKCharSumBound C ψ G diBenedettoDelta) :
    ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ C * (G.card : ℝ) ^ (1 - diBenedettoDelta) :=
  h

/-- **The di Benedetto exponent, threaded into the live residual** (`of_BGK`): the named SOTA
character-sum Prop discharges `WorstCaseIncompleteSumBound` at `M = (C·n^{1 - 31/2880})²`. This is
the honest SOTA contribution to the interior-`δ*` energy/incidence chain. -/
theorem worstCaseIncompleteSumBound_diBenedetto {ψ : AddChar F ℂ} {G : Finset F} {C : ℝ}
    (h : BGKCharSumBound C ψ G diBenedettoDelta) :
    WorstCaseIncompleteSumBound ψ G ((C * (G.card : ℝ) ^ (1 - diBenedettoDelta)) ^ 2) :=
  worstCaseIncompleteSumBound_of_bgk h

/-! ## Wiring 3 — the additive-energy input, genuinely used (the L⁴ envelope) -/

/-- **The sum–product additive-energy input, used (not decorative): the per-frequency `L⁴`
envelope.** The in-tree 4th-moment identity `Σ_b ‖η_b‖⁴ = q·E(G)` (`subgroup_gaussSum_fourthMoment`)
plus the named `SumProductEnergyBound G c` (`E(G) ≤ n^{3-c}`) give, for every `b`,

  `‖η_b‖⁴ ≤ q · n^{3-c}`.

This is the elementary (4th-moment) half of the BGK reduction chain: a single term is `≤` the full
moment, which equals `q·E(G) ≤ q·n^{3-c}`. (The deep BGK exponent comes from the *iterated* dyadic
sum–product amplification, not from this single 4th moment alone — but the energy input is genuinely
wired here, demonstrating it is a real consumer.) -/
theorem energy_envelope_of_sumProduct {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    {c : ℝ} (h : SumProductEnergyBound G c) (b : F) :
    ‖eta ψ G b‖ ^ 4 ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ (3 - c) := by
  -- a single 4th-power term is at most the full 4th moment
  have hterm : ‖eta ψ G b‖ ^ 4 ≤ ∑ b' : F, ‖eta ψ G b'‖ ^ 4 :=
    Finset.single_le_sum (f := fun b' : F => ‖eta ψ G b'‖ ^ 4)
      (fun i _ => by positivity) (Finset.mem_univ b)
  rw [subgroup_gaussSum_fourthMoment hψ G] at hterm
  -- `q·E(G) ≤ q·n^{3-c}` from the named energy bound
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  calc ‖eta ψ G b‖ ^ 4
      ≤ (Fintype.card F : ℝ) * (addEnergy G : ℝ) := hterm
    _ ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ (3 - c) := mul_le_mul_of_nonneg_left h hq

end ArkLib.ProximityGap.BGKExponentReduction

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
#print axioms ArkLib.ProximityGap.BGKExponentReduction.diBenedettoDelta_lt_prizeDelta
#print axioms ArkLib.ProximityGap.BGKExponentReduction.diBenedettoDelta_pos
#print axioms ArkLib.ProximityGap.BGKExponentReduction.worstCaseIncompleteSumBound_of_bgk
#print axioms ArkLib.ProximityGap.BGKExponentReduction.addEnergy_le_of_bgk
#print axioms ArkLib.ProximityGap.BGKExponentReduction.bgk_charSum_of_named
#print axioms ArkLib.ProximityGap.BGKExponentReduction.diBenedetto_charSum_of_named
#print axioms ArkLib.ProximityGap.BGKExponentReduction.worstCaseIncompleteSumBound_diBenedetto
#print axioms ArkLib.ProximityGap.BGKExponentReduction.energy_envelope_of_sumProduct
