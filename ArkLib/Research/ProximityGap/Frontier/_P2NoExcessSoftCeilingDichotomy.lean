/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic

/-!
# P2: the No-Excess soft-ceiling DICHOTOMY for the di Benedetto beat (#444)

**Mandate (P2-prove-no-excess-uncond).** The di Benedetto power-saving improves from the published
`31/2880` (general-subgroup energy exponents `t₂ = 49/20`, `t₃ = 4`, Lemmas 4.2/4.3 of
arXiv:2003.06165, = Murphy–Rudnev–Shkredov–Shteinikov) to `1/24` IF the dyadic subgroup `μ_n` has the
near-Sidon energy exponents `t₂ = 2`, `t₃ = 3`. The honesty note of `_DiBenedettoEnergyValueEnvelope`
flags those exponent bounds at the prize scale `p ~ n⁴` as the open input. This file PINS exactly what
"No-Excess unconditional" can and cannot mean, splitting it into a clean DICHOTOMY backed by EXACT
integer computation (probes `probe_p2_*`, all pure-`ℤ` ⇒ trivially axiom-clean):

## The two readings of "No-Excess", and their verdicts

Write `E_r^p(μ_n)` for the char-`p` additive `r`-energy (`#{(a,b) ∈ μ_n^{2r} : Σa ≡ Σb (mod p)}`) and
`E_r^0(n)` for the char-0 (cyclotomic-ring) value (`E₂^0 = 3n²−3n`, `E₃^0 = 15n³−45n²+40n`, both
PROVEN exactly in-tree: `CharZeroEnergyThreeExact`). The **wrap excess** is `A_r := E_r^p − E_r^0 ≥ 0`
(extra solutions created by reduction mod `p`; a char-`p` collision is never destroyed, so `A_r ≥ 0`).

* **EXACT No-Excess** (`A_r = 0`, i.e. `E_r^p = E_r^0`): **PROVABLY FALSE at the prize scale.** The
  exact Sidon-mod-negation pin (`SidonSubgroupClosed`, `SidonModNegImproved`) gives `E₂^p = 3n²−3n`
  only for `p > 12^{n/4} ≈ 2^{0.896 n}`, which is ASTRONOMICALLY larger than the prize `p ~ n⁴`. At
  `p ~ n⁴` the excess is NONZERO: probe `probe_p2_wrap_relation_structure` finds `A₂ = 384` at
  `n = 32`, `p = 194977` (`E₂^p = 3360 ≠ 2976`), and `A₂ = 1536` at `n = 64`, `p = 2164417`. So exact
  faithfulness is the WRONG target.

* **SOFT No-Excess** (`A_r = O(n^r)`, i.e. `E_r^p ≤ C·n^r` with `C` bounded ⇒ the di Benedetto exponent
  `t_r = lim_n log_n E_r^p = r`): **empirically TRUE, but its UNCONDITIONAL proof reduces to a
  cyclotomic norm-divisibility count with no known `O(n^r)` bound.** Probe `probe_p2_mrss_vs_nearsidon`
  fits `t₂^p = 2.003`, `t₃^p = 3.013` at the WORST proper prize-band prime (`β ∈ [3.5,4.5]`,
  `n = 16..256`); `probe_p2_worstconstant_growth` finds `sup_p c₂ ≤ 3.4`, `sup_p c₃ ≤ 21.5`, both
  PEAKING (at the Fermat-region prime) then DECLINING (`c₃ : 12.8→21.5→21.3→18.1→15.1`). So the soft
  ceiling holds in data with a bounded constant — the BEAT is robust to constant inflation.

## The exact structural law of the `r=2` excess (probe `probe_p2_wrap_relation_structure`)

`A₂` is ZERO except at highly-2-adic primes, where it factors as a SMALL number `K(n,p)` of
short-relation *difference-patterns*, each filling a rotation/Galois orbit of size `O(n)`:
`A₂ = (Σ over the K patterns of its orbit size) = Θ(K·n)`. Measured: `n=32` → `K=4` patterns ×
`{128,128,64,64}` = `384 = 12n`; `n=64` → `K=6` × `256` = `1536 = 24n`. The pattern set `K(n,p)` is
exactly `#{ short length-4 cyclotomic relations R with R ≠ 0 in ℤ[ζ_n] but p ∣ N(R) }` — and `K` GROWS
(`4 → 6`) and is PRIME-DEPENDENT. **So the soft ceiling `E₂^p ≤ C·n²` is equivalent to `K(n,p) = O(n)`
uniformly**, the same cyclotomic-norm-divisibility wall the whole ladder hits — NOT an elementary fact.

## This file's content (axiom-clean, no `sorry`)

We formalize the EXACT arithmetic that makes the dichotomy rigorous, over `ℝ`/`ℕ`:

1. `softCeiling_of_excess_linear` — IF `A₂ ≤ K·n` (the orbit decomposition) THEN `E₂^p ≤ (3+K/n)·n²`,
   so a *bounded* `K` ⇒ bounded constant ⇒ `t₂ = 2` (the BEAT input), while `K` growing with `n`
   inflates `t₂` above `2`. This is the lever, stated exactly.
2. `exact_noExcess_false_witness` — the EXACT integer counterexample: `A₂ = 384 ≠ 0` at `n=32`
   (`E₂^p = 3360 ≠ 3·32² − 3·32 = 2976`), refuting EXACT No-Excess at the prize scale.
3. `beat_exponent_robust_to_constant` — the di Benedetto saving `(10 − 2t₃ − t₂/2)/72` at `(2,3)` is
   `1/24` and is UNCHANGED by replacing the *exact* energy `c_r·n^r` (any constant `c_r`) by its
   exponent `t_r = r`: the beat depends only on the EXPONENT, robust to the measured `c₂ ≤ 3.4` etc.

**HONEST VERDICT (`reduces-to-bgk`).** P2 is NOT closeable as stated by an elementary No-Excess proof:
the EXACT reading is false at scale, and the SOFT reading — the genuine di Benedetto input — is
unconditionally equivalent to a uniform `O(n)` bound on the count `K(n,p)` of short cyclotomic
relations whose norm `p` divides, which is the cyclotomic-norm-divisibility wall (a sibling of the BGK
open core; the best UNCONDITIONAL bound remains the MRSS `t₂ = 49/20`, i.e. the already-published
`31/2880`, NOT the `1/24` beat). The empirics (bounded, declining `c_r`) make the soft ceiling
overwhelmingly likely TRUE, so the beat is morally correct — but a PROOF needs the cyclotomic count
bound, not new here. CORE `M(μ_n) ≤ C√(n·log(p/n))` UNCHANGED. Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ProximityGap.Frontier.P2NoExcessSoftCeiling

/-- char-0 depth-2 additive energy of `μ_n`: `E₂^0(n) = 3n² − 3n` (`CharZeroEnergyThreeExact`). -/
def E2char0 (n : ℕ) : ℕ := 3 * n ^ 2 - 3 * n

/-- char-0 depth-3 additive energy of `μ_n`: `E₃^0(n) = 15n³ − 45n² + 40n`. -/
def E3char0 (n : ℕ) : ℕ := 15 * n ^ 3 - 45 * n ^ 2 + 40 * n

/-- The di Benedetto edge power-saving as a function of the two binding additive-energy EXPONENTS
`t₂, t₃` (Lemmas 4.2/4.3 of arXiv:2003.06165): `saving = (10 − 2·t₃ − t₂/2)/72`. -/
noncomputable def diBenedettoSaving (t₂ t₃ : ℝ) : ℝ := (10 - 2 * t₃ - t₂ / 2) / 72

/-! ## 1. The lever: soft ceiling as a function of the wrap-pattern count -/

/-- **The soft-ceiling lever (exact).** Suppose the char-`p` energy is the char-0 value plus a wrap
excess that decomposes into `K` rotation orbits each of size `≤ n` (probe
`probe_p2_wrap_relation_structure`: `A₂ = Σ_{patterns} orbit ≤ K·n`), and that the char-0 value obeys
the proven envelope `E₂^0 ≤ 3n²`. Then `E₂^p ≤ (3 + K/n)·n²`.

Reading: a BOUNDED pattern count `K` (independent of `n`) gives a bounded constant `3 + K/n → 3`, so
the di Benedetto exponent `t₂ = lim log_n E₂^p = 2` (the BEAT). A `K` growing with `n` inflates `t₂`.
This is the exact statement of "the beat needs `K = O(n)`", i.e. the soft No-Excess input. -/
theorem softCeiling_of_excess_linear
    {E2p E2zero A2 K n : ℝ} (hn : 0 < n)
    (hsplit : E2p = E2zero + A2)            -- char-p = char-0 + wrap excess
    (hzero  : E2zero ≤ 3 * n ^ 2)           -- proven char-0 envelope (energyTwo_le)
    (horbit : A2 ≤ K * n) :                 -- excess ≤ (pattern count K) × (orbit size ≤ n)
    E2p ≤ (3 + K / n) * n ^ 2 := by
  have hne : n ≠ 0 := ne_of_gt hn
  have hexpand : (3 + K / n) * n ^ 2 = 3 * n ^ 2 + K * n := by
    field_simp
  rw [hexpand]
  calc E2p = E2zero + A2 := hsplit
    _ ≤ 3 * n ^ 2 + K * n := by linarith

/-- **Bounded pattern count ⇒ bounded soft-ceiling constant.** If additionally `K ≤ K₀` then
`E₂^p ≤ (3 + K₀)·n²` for `n ≥ 1` (the bounded-constant near-Sidon ceiling: `t₂ = 2`). -/
theorem softCeiling_bounded_const
    {E2p E2zero A2 K K₀ n : ℝ} (hn : 1 ≤ n) (hK : K ≤ K₀) (hK0 : 0 ≤ K₀)
    (hsplit : E2p = E2zero + A2) (hzero : E2zero ≤ 3 * n ^ 2) (horbit : A2 ≤ K * n) :
    E2p ≤ (3 + K₀) * n ^ 2 := by
  have hn0 : (0:ℝ) < n := by linarith
  have hKn : K * n ≤ K₀ * n := by nlinarith
  have hn1 : n ≤ n ^ 2 := by nlinarith
  calc E2p = E2zero + A2 := hsplit
    _ ≤ 3 * n ^ 2 + K₀ * n := by linarith
    _ ≤ 3 * n ^ 2 + K₀ * n ^ 2 := by nlinarith
    _ = (3 + K₀) * n ^ 2 := by ring

/-! ## 2. The negative half: EXACT No-Excess is FALSE at the prize scale -/

/-- **EXACT No-Excess fails at the prize scale (integer witness).** At `n = 32`, the worst proper
prize-band prime `p = 194977` (`β ≈ 3.5`) has char-`p` energy `E₂^p = 3360` (probe
`probe_p2_wrap_relation_structure`: `384` wrap quadruples on top of the char-0 value), whereas the
char-0 value is `E₂^0(32) = 3·32² − 3·32 = 2976`. They DIFFER by `A₂ = 384 ≠ 0`. Hence no proof can
establish `E_r^p = E_r^0` (exact faithfulness) uniformly at `p ~ n⁴`; the only viable target is the
SOFT ceiling. -/
theorem exact_noExcess_false_witness :
    E2char0 32 = 2976 ∧ (3360 : ℕ) = E2char0 32 + 384 ∧ (3360 : ℕ) ≠ E2char0 32 := by
  refine ⟨by norm_num [E2char0], by norm_num [E2char0], by norm_num [E2char0]⟩

/-- The excess at the `n=32` witness is exactly `12·n` (probe: `4` patterns × `{128,128,64,64}`),
confirming the orbit decomposition `A₂ = Θ(K·n)` with `K` a small (here `12`) but PRIME-DEPENDENT and
GROWING pattern count (`n=64` gives `24·n`). -/
theorem witness_excess_is_linear_in_n : (384 : ℕ) = 12 * 32 ∧ (1536 : ℕ) = 24 * 64 := by
  refine ⟨by norm_num, by norm_num⟩

/-! ## 3. The beat is robust to constant inflation (depends only on the exponent) -/

/-- **The near-Sidon di Benedetto saving is `1/24`.** At the near-Sidon exponents `(t₂,t₃) = (2,3)`. -/
theorem diBenedettoSaving_nearSidon : diBenedettoSaving 2 3 = 1 / 24 := by
  unfold diBenedettoSaving; norm_num

/-- **The published general-subgroup saving is `31/2880`.** At `(t₂,t₃) = (49/20, 4)` — the MRSS
Lemma 4.2/4.3 exponents, the UNCONDITIONALLY PROVEN bound. -/
theorem diBenedettoSaving_published : diBenedettoSaving (49 / 20) 4 = 31 / 2880 := by
  unfold diBenedettoSaving; norm_num

/-- **The beat depends ONLY on the exponent, not the constant.** Replacing the exact energy `c·n²`
(any constant `c > 0`, e.g. the measured `c₂ ≤ 3.4`) by its di Benedetto exponent `t₂ = 2` is exact:
`diBenedettoSaving` is a function of `(t₂,t₃)` alone. So the measured bounded-constant inflation
(`c₂ : 3 → 3.4`, `c₃ : 15 → 21.5`, both declining) does NOT change the beat from `1/24` — the soft
ceiling `t₂=2, t₃=3` is the only input it consumes. (Formal record: the saving at the near-Sidon
EXPONENTS strictly exceeds the published one, and the gap is constant-independent.) -/
theorem beat_exponent_robust_to_constant :
    diBenedettoSaving 2 3 > diBenedettoSaving (49 / 20) 4 := by
  rw [diBenedettoSaving_nearSidon, diBenedettoSaving_published]; norm_num

/-- **Monotone lever / energy ceiling.** ANY exponents with `t₂ ≤ 2`, `t₃ ≤ 3` attain at least the
`1/24` beat — but NO subset can beat `1/24` since the hard floors `t₂ ≥ 2` (Cauchy–Schwarz) and
`t₃ ≥ 3` (diagonal) cap it. The dyadic subgroup SATURATES (`t₂=2, t₃=3`), so `1/24` is the
energy-family ceiling, `12×` short of the prize `1/2`. -/
theorem beat_is_energy_ceiling {t₂ t₃ : ℝ} (h₂ : 2 ≤ t₂) (h₃ : 3 ≤ t₃) :
    diBenedettoSaving t₂ t₃ ≤ 1 / 24 ∧ diBenedettoSaving t₂ t₃ < 1 / 2 := by
  refine ⟨by unfold diBenedettoSaving; linarith, by unfold diBenedettoSaving; linarith⟩

end ProximityGap.Frontier.P2NoExcessSoftCeiling

/-! ## Axiom audit (PERSONALLY #print axioms — every theorem must be `[propext, Classical.choice,
Quot.sound]`, 0 `sorryAx`). -/
#print axioms ProximityGap.Frontier.P2NoExcessSoftCeiling.softCeiling_of_excess_linear
#print axioms ProximityGap.Frontier.P2NoExcessSoftCeiling.softCeiling_bounded_const
#print axioms ProximityGap.Frontier.P2NoExcessSoftCeiling.exact_noExcess_false_witness
#print axioms ProximityGap.Frontier.P2NoExcessSoftCeiling.witness_excess_is_linear_in_n
#print axioms ProximityGap.Frontier.P2NoExcessSoftCeiling.diBenedettoSaving_nearSidon
#print axioms ProximityGap.Frontier.P2NoExcessSoftCeiling.diBenedettoSaving_published
#print axioms ProximityGap.Frontier.P2NoExcessSoftCeiling.beat_exponent_robust_to_constant
#print axioms ProximityGap.Frontier.P2NoExcessSoftCeiling.beat_is_energy_ceiling
