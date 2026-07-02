# #466 Round 1 — research plan (2026-07-01)

**Mission (dossier v3 §0):** attack `M(μ_n) ≤ C·√(n·log(p/n))` at β≈4, n=2^μ — equivalently the
`δ* = (1−ρ) − m*/n` pin — through every open angle in dossier §6, propose→refute discipline,
honesty contract binding. A refutation with a countermodel is a win; only "proven" is sacred.

## Lanes (this round)

### L — Lean bankables (resolve the §12 new-phantom flags)
- **L1 `LineListMCAWeld.lean`** (re-derive): `mcaEventFilter_card_le_lineList_mul_of_far`
  (far, nonvanishing direction, threshold `a ≤ (1−δ)n` ⟹ `#bad ≤ Λ·⌊n/a⌋`),
  `mcaDeltaStar_ge_of_farLineListBudgeted` (floor from far-line budget `Λ ≤ L`,
  `L·⌊n/a⌋ ≤ q·ε*`), refuter `aligned_line_lambda_ge_q` (constant-on-big-set directions force
  `Λ ≥ q` — the far-restriction is forced). Substrate verified on main:
  `badScalars_eq_explainable` (`FarCosetExplosion:65`), `lineBadScalars`/`lineAppearingCodewords`/
  `lineBadScalars_card_le_lineAppearingCodewords_card_mul` (`LineListReduction:54/64/383`),
  `le_mcaDeltaStar_of_good` (`MCAThresholdLedger:97`). Missing middle link to derive:
  explainable-filter ⊆ lineBadScalars. **Success:** axiom-clean compile. **Kill:** a real
  type-level mismatch between `mcaEvent` bad-scalar sets and `lineBadScalars` (would itself be a
  finding — the thread's claim was then wrong in substance, not just unlanded).
- **L2 `MomentExponentThreshold.lean`** (re-derive): `θ(r,β) = (β+r−1)/(2r)`;
  `1/2 < θ` always; `θ < 1 ↔ β − 1 < r`; strict antitonicity; `θ(3,4)=1`, `θ(4,4)=7/8`.
  Elementary real arithmetic. **Success:** axiom-clean compile.

### P — decisive probes (Tier-2, never run)
Regime discipline for ALL probes (the #400 trap): proper subgroup `μ_n ⊊ F_p^×`, `p ≡ 1 mod n`,
`p ≥ n^4` (β≥4 unless testing β-dependence), multiple primes, exclude correlated directions
`X^{n/2} = ±1`. A verdict needs ≥2 primes and ≥2 octaves of n where feasible.
- **P1 anti-resonance** (Chapman–Mudgal 2605.15434 shape): is the worst frequency `b*`
  anti-resonant (Ramanujan-sum / low-divisor-correlation structure)? **Decides** whether the
  resonance dichotomy could split the sup over b. Kill: b* is resonance-neutral (dilation
  invariance makes the statistic b-blind).
- **P2 non-backtracking / Ihara–Bass** (2606.27075): compute the NB spectrum of
  `Cay(F_p, μ_n)`; the dossier calls NB "the only sliver that could beat √q". **Decides:** does
  the NB radius at thin n see anything the adjacency spectrum (= the η_b themselves) doesn't?
  Kill: Ihara–Bass is a deterministic function of the adjacency spectrum on a regular graph ⟹
  b-blind relabeling (expected — but must be MEASURED, not assumed).
- **P3 Kravchuk moment-interlacing** (2604.09533): compute the scaling limit `SCL_ρ` of the
  largest-root bound vs Johnson `1−√ρ` at prize rates. Kill: reproduces Johnson exactly.
- **P4 Hankel / Jacobi turnover structure** (dossier Tier-1 #3): compute recurrence coefficients
  `b_k` of the empirical spectral measure of `{η_b}` (n = 8…64, several β≈4 primes); locate
  turnover `k*`; TEST candidate b_k-native inequalities (Hankel-PSD ratios, `b_{k+1}²−b_k²`
  bounds, early-warning functionals) for whether ANY bounds `k*` from ≤O(log p) moments.
  This is the one non-magnitude seam — the probe designs the conjecture to attack.
- **P5 windowed SumsetExtremal at small n** (dossier Tier-1 #1): n=8 (q≈4129+), n=16 if
  feasible (q≈65537+): exhaustively compare worst ≥2-Fourier-component (spread) direction
  incidence vs worst monomial incidence at in-window δ. **Decides** the guarded crux at the
  smallest honest scales. Either outcome is a major data point (spread wins in-window ⟹ the
  windowed conjecture is FALSE and the catalogue route dies; monomials win ⟹ first in-window
  evidence for the guard-cell route).
- **P6 di Benedetto effective-1/2 accounting** (dossier Tier-1 #5, "attack #5" never run):
  full exponent bookkeeping of the di Benedetto pipeline with EXACT μ_n energies
  (T₂=3n²−3n, T₃=15n³−45n²+40n, T₅.. ladder) over all parameter choices at β=4; also test the
  shifted/trilinear variants. **Decides:** the max achievable exponent with structure-aware
  inputs; kill = plateau at ≈0.9583 (the known SOTA-closeness ceiling).

### E — the essay + refute cycle
Essay (`deltastar-466-essay-novel-mathematics-2026-07-01.md`): the missing mathematics stated
for a working analyst; every live avenue; NEW proposed machinery (each stated as a refutable
conjecture with a concrete test); candidate closure proofs written out honestly to their gap.
Then EVERY essay proposal gets an adversarial refutation pass (probe or exponent accounting or
Lean gate); survivors get proof attempts; everything recorded.

### F — fold-back
Round log appended to dossier v3; findings posted to #466; all artifacts landed on main;
DISPROOF_LOG entries for refutations; repeat with any newly-opened threads.

## Verification protocol
Every lane's verdict is checked by an independent skeptic (regime errors, b-blindness,
sampling artifacts, budget conflation, the correlated-direction trap). Lean lanes: pg-iterate +
axiom audit + one locked build before landing. No verdict from a single prime or single n.

## Success/termination criteria for the round
- Both phantom bricks re-landed (or their claims refuted in substance).
- All six probes DECIDED (verdict + countermodel/evidence), not merely run.
- Essay written; every new proposal attacked; survivors (if any) escalated to proof attempts.
- Dossier updated; the honest outcome recorded either way. The core stays OPEN unless a proof
  survives the full contract (axiom-clean, no silent discharge).
