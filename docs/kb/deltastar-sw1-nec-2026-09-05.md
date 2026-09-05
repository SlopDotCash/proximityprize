# SW1 lane NEC — is "δ*-pin ⟹ M-bound" a theorem or a meta-claim? (2026-09-05)

Read-only audit lane. No Lean was run, no file edited; this note is the only artifact.
Classification vocabulary: dossier v4 §6. Verdict on CORE: **OPEN / ON-BGK** (unchanged).

## 0. Verdict

**The necessity direction `δ*-pin ⟹ M(μ_n)-bound` is NOT a Lean theorem anywhere in the cone.**
What is machine-checked two-sided is purely definitional bookkeeping on the incidence side:

- `epsMCA C δ ≤ B/q ⟺ WorstCaseIncidenceBounded C δ B` (`_TwoSidedCapstone.lean:145`), and
- `δ < mcaDeltaStar C (E/q) → WorstCaseIncidenceBounded C δ E` (`OpenCoreConverse.lean:172`).

`WorstCaseIncidenceBounded` (WCI) is a combinatorial statement about bad-scalar counts of the
code; it mentions no character sum. A whole-cone grep (§9) finds **zero** theorems whose
hypothesis is `WorstCaseIncidenceBounded` / `mcaDeltaStar` / `epsMCA` and whose conclusion is
`WorstCaseIncompleteSumBound`, `DCEnergyBound`, `WallHolds`, `GaussianEnergyBound`, `ShawGapLaw`
or `SignedDeepCancellation`. Every formal arrow between the Fourier layer and δ* runs
**Fourier ⟹ δ\*** and is either (a) conditional on named glue proven vacuous at the prize budget
(`RealizedIncidenceBudget`, `charSumIncidenceBudget`), or (b) carries WCI itself as a hypothesis
with the Fourier input inert (`prizeFloor_of_BGK_and_incidence`: proof term is
`worstCaseIncidence_pin … hIncidence`; `hBGK` unused).

Worse for the necessity claim: the campaign's own rounds 13/14 prove (identity + Hölder, axiom-
clean; separation itself probe-measured) that worst-case incidence is **not a function of `M`**
(`_R13HyperplaneSecondMoment`) and that `M ≤ B` does **not** imply `WallHolds`
(`_R14SupNormWeakerThanWall`): "the two open Props are INDEPENDENT" (DISPROOF_LOG:485). So the
"twelve technologies re-derive `M(μ_n)`" / "provably the Paley object" sentence of v3 §0.2 is a
**meta-claim over a class of methods** (second-order / single-moment certifiers:
`MetaTheoremSecondOrderCap`, `_MomentLadderExceedsPrize`) plus prose — not an implication from
the prize predicate. **A bypass route is logically open in the formal record.** The only file
titled "necessity" (`_CoreA7_NecessityTight`) is a `Nat.find` unfolding over abstract
`ℕ → ℕ → ℕ` functions under an identification hypothesis, disconnected from `mcaDeltaStar` and
from any character sum.

Classification of this lane's output: **refutation/no-go of the necessity claim *as stated***
(absence-of-theorem, grep-verified, plus the campaign's own kernel separation results). It is
**not** a refutation of CORE and moves no bracket. Dossier v4 §1 already omits the sentence.

## 1. Target

Determine, at theorem level, whether "any proof of the prize floor must contain the square-root
cancellation certificate" is (i) an implication `δ*-pin ⟹ M-bound` from the prize predicate,
or (ii) a meta-theorem over a class of methods; answer questions (a)(b)(c) of the lane brief.

## 2. What was tried

Read: dossier v3 §0.1–2, §1.1, §1.4, §2.2–2.5, §4, §9, §11.6, §12, §45; dossier v4 §1, §6;
doctrine v2 §1–2; root `PROXIMITY_PRIZE_WORKBENCH.lean` §3, §6–§8b, §9–§10, axiom audit;
DISPROOF_LOG entries O165, O186, `466-r12/r13/r14`. Read the Lean source of every declaration
in §3–§4 below. Greps in §9. No `lake`, no `pg-iterate`, no edits.

## 3. Exact statements (verbatim signatures; `…` = elided binders)

Prize predicate (real-valued encoding), `GrandChallenges.lean:96`:
```
def grandMCAChallenge … (C : LinearCode ι F) (ε_star : ℝ≥0) : Prop :=
  ∃ δ_C_star : ℝ≥0, δ_C_star ≤ 1 ∧
    epsMCA (F := F) (A := F) ((C : Set (ι → F))) δ_C_star ≤ (ε_star : ENNReal) ∧
    ∀ δ : ℝ≥0, δ_C_star < δ → δ ≤ 1 →
      epsMCA (F := F) (A := F) ((C : Set (ι → F))) δ > (ε_star : ENNReal)
```
Collapse (`Collapse.lean:161`): `grandMCAChallenge C ε* ↔ epsMCA C 1 ≤ ε*` (Finding F6). The
faithful object is the lattice max `mcaLatticeThreshold` (`Lattice.lean:104`, `Finset.max'`).

§4.5 draft conjecture, `GrandChallenges.lean:650` (NOT the prize predicate; docstring: lives in
an `\ignore{…}` block of the [ABF26] source):
```
def mcaConjecture : Prop :=
  ∃ c₁ c₂ c₃ : ℝ, ∀ {ιC …} {FC …} (domain : ιC ↪ FC) (k : ℕ) (δ : ℝ≥0),
      0 < k → (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC →
      epsMCA (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC))) δ ≤
        ENNReal.ofReal
          (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃)
```
`mcaConjectureBound n q k δ c₁ c₂ c₃ := (1/q) * n^c₁ / ((k/n)^c₂ * (1 - k/n - δ)^c₃)` (:623).

Threshold ledger, `MCAThresholdLedger.lean:86/97/127`:
```
noncomputable def mcaDeltaStar (C : Set (ι → A)) (εstar : ℝ≥0∞) : ℝ≥0 :=
  sSup (mcaGoodRadii (F := F) (A := A) C εstar)   -- {δ | δ ≤ 1 ∧ epsMCA C δ ≤ εstar}
theorem le_mcaDeltaStar_of_good … (hδ : δ ≤ 1) (hgood : epsMCA C δ ≤ εstar) :
    δ ≤ mcaDeltaStar C εstar
theorem mcaDeltaStar_le_of_bad … (hbad : εstar < epsMCA C δbad) :
    mcaDeltaStar C εstar ≤ δbad
```

Open core Prop and pin, `OpenCoreConditionalPin.lean:105/135`:
```
def WorstCaseIncidenceBounded (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card ≤ B
theorem worstCaseIncidence_pin … (hδ : δ ≤ 1) (hI : WorstCaseIncidenceBounded C δ B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar C εstar
```

The machine-checked two-sidedness, `Frontier/_TwoSidedCapstone.lean:145`,
`OpenCoreConverse.lean:269`:
```
theorem epsMCA_le_iff_worstCaseIncidenceBounded (C …) (δ : ℝ≥0) (B : ℕ) :
    epsMCA C δ ≤ (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ↔ WorstCaseIncidenceBounded C δ B
theorem deltaStar_iff_incidence_budget (C …) {δ : ℝ≥0} {E : ℕ} (hδ1 : δ ≤ 1) :
    (δ < mcaDeltaStar C (E / q) → WorstCaseIncidenceBounded C δ E)
    ∧ (WorstCaseIncidenceBounded C δ E → δ ≤ mcaDeltaStar C (E / q))
```

Fourier-layer Props. `InteriorWorstCaseIncompleteSum.lean:59`:
`def WorstCaseIncompleteSumBound (ψ : AddChar F ℂ) (G : Finset F) (M : ℝ) : Prop :=
∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ^ 2 ≤ M`. `DCEnergyCorrection.lean:38`:
`def DCEnergyBound (G : Finset F) (r : ℕ) : Prop :=
q·E_r(G) − |G|^{2r} ≤ q·(2r−1)‼·|G|^r`. `_WallCapstone.lean:88`:
`def WallHolds G : Prop := ∀ r : ℕ, DCEnergyBound G r`. `ShawGapLaw` (root workbench:480):
`∀ b ≠ 0, ‖eta ψ D b‖ ≤ C * √(|D| * logb 2 (q/|D|))`; `ShawFlatnessConjecture` (:492):
`∃ C > 0, ∀ F ψ D, ψ.IsPrimitive → |D|² ≤ q → ShawGapLaw ψ D C`.
**`HyperplaneCancellation`: no Lean declaration exists** (5 docstring mentions, 0 defs).

Cross-form bridge, `Frontier/_AssaultV2_CrossFormBridge.lean:83` (Fourier layer only):
```
theorem dcEnergyBound_iff_signedDeepCancellation {ψ} (hψ : ψ.IsPrimitive) (G) (r) :
    DCEnergyBound G r ↔ SignedDeepCancellation ψ G r
```

Floor-from-BGK, `Frontier/_PrizeFloorOfBGK.lean:112/162` (hBGK inert — proof term is
`worstCaseIncidence_pin … hIncidence hbudget`):
```
theorem prizeFloor_of_BGK_and_incidence (C) (εstar) {ψ} (hψ) {G} {M} (hM0 : 0 ≤ M)
    (hBGK : WorstCaseIncompleteSumBound ψ G M) {δ} {B} (hδ : δ ≤ 1)
    (hIncidence : WorstCaseIncidenceBounded C δ B) (hbudget : B / q ≤ εstar) :
    δ ≤ mcaDeltaStar C εstar
theorem prizeFloor_window_of_BGK_and_incidence {p n} … (hBGK …)
    (hIncidence : WCI (evalCode g n ((r-2)*m)) δwin B) (hBudget : B / p ≤ εstar) :
    δwin ≤ mcaDeltaStar (evalCode …) εstar ∧
      mcaDeltaStar (evalCode …) εstar ≤ (1 - ((r-2)*m+1)/n) - 1/(C*L)
    -- ceiling half = kkh26_mcaDeltaStar_le_capacity_sub_log (unconditional)
```

KKH26 ceiling, `KKH26PolyFieldCeiling.lean:215` (named input `TZPrimeSupply n β supply`,
`KKH26ThornerZaman.lean:111`, := `supply ≤ (tzWindow n β).card`):
```
theorem kkh26_mcaDeltaStar_le_of_TZ {n β supply} [NeZero n]
    (hTZ : TZPrimeSupply n β supply) {μ m r} (hμ : 1 ≤ μ) (hm : 1 ≤ m)
    (hn : n = 2^μ * m) (hr2 : 2 ≤ r) (hr : r ≤ 2^(μ-1)) (hx …) (hpl …) (hcount …) :
    ∃ p, p.Prime ∧ p ≡ 1 [MOD n] ∧ n^β ≤ p ∧ p ≤ 2·n^β ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ εstar < (2^r * C(2^(μ-1), r)) / p,
          mcaDeltaStar (F := ZMod p) (evalCode g n ((r-2)*m)) εstar ≤ 1 - r / 2^μ
```

Meta-theorem, `MetaTheoremSecondOrderCap.lean:112/154` (about certifiers `g` of ONE moment):
```
theorem secondMoment_method_floor (g : ℝ → ℝ)
    (hg : ∀ (η : ι → ℝ) (b : ι), |η b| ≤ g (∑ i, (η i) ^ 2)) {S : ℝ} (hS : 0 ≤ S) :
    Real.sqrt S ≤ g S
theorem momentDepth_method_floor {r} (hr : 1 ≤ r) (g : ℝ → ℝ)
    (hg : ∀ (η : ι → ℝ) (b : ι), |η b| ≤ g (∑ i, (η i) ^ (2 * r))) {S} (hS : 0 ≤ S) :
    Real.sqrt S ≤ g (S ^ r)
```

Rigidity, `Frontier/_DeltaStarBindingRigidity.lean:85` (pure real inequalities; no δ*, M,
code):
```
theorem deltaStar_determination_all_or_nothing {n L c : ℝ} (hn : 1 < n) (hL1 : 1 < L)
    (hLn : L < n) (hc : 0 < c) (hLpoly : L < n ^ (2 * c)) :
    (√n < √(n * L) ∧ √(n * L) < n) ∧ √(n * L) < n ^ ((1 : ℝ) / 2 + c)
```

Master-gap identity, `Frontier/_BridgeB01.lean:66` (ℚ) and
`Frontier/_BchksF3_RetargetedReduction.lean:237` (ℝ) — abstract reals, definitional hyps:
```
theorem deltaStar_master_gap_identity (n k s deltaStar rho mstar : ℚ) (hn : n ≠ 0)
    (hρ : rho = k / n) (hms : mstar = s - k) (hδ : deltaStar = 1 - s / n) :
    deltaStar = 1 - rho - mstar / n
```

"Necessity" file, `Frontier/_CoreA7_NecessityTight.lean:93/109/282` — abstract functions,
`mStar := Nat.find`, identification is a hypothesis:
```
def BCHKSBudget (Sigma : ℕ → ℕ → ℕ) (s r B : ℕ) : Prop := Sigma s r ≤ B
theorem mStar_le_iff_BCHKS_window (D budget Sigma smap rmap n) (hex)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m)) (M : ℕ) :
    mStar D budget n hex ≤ M ↔ ∃ m ≤ M, BCHKSBudget Sigma (smap n) (rmap n m) (budget n)
theorem BCHKS_necessary … (hident …) (M)
    (hno : ¬ BCHKSWindowHolds Sigma smap rmap budget n M) : M < mStar D budget n hex
```
Its E1 hypotheses use `deltaStar = 1 - rho - (mstar - 1) / n` (:184, :198, :228) — the form
`_BridgeB01` corrected to `mstar / n` on 2026-06-16.

Other cited kernels:
`floorClosureBudgetedMaxAtField_univ_iff_floorGood_and_worstCaseIncidenceBounded`
(`_FloorClosureContract.lean:519`, `↔ ¬FloorBad (2^a) q ∧ WCI C δ B`, definitional);
`exists_singleStackDominationCertificate_iff_worstCaseIncidenceBounded`
(`StackMaximizerDomination.lean:138`, finite max, definitional);
`lineEta_image_eq_globalImage` (`TwoDAnnihilatorLineParseval.lean:148`, equality of magnitude
images, `b₀ ≠ 0`); `swarm_sub_burgess` (`_P1RateQuarterCrossConeBridge.lean:168`,
`N^4 < P ∧ P < N^6`, `norm_num`); ERM (`_EnergyRatioMonotoneReduction.lean:71/113/140`):
`EnergyRatioMonotone G := ∀ k ≥ 1, E_{k+1} ≤ (2k+1)|G|·E_k`; `gaussianEnergyBound_of_ERM` and
`worstCaseIncompleteSumBound_of_ERM` are forward only; ERM is refuted globally (docstring,
n=32, r=6).

## 4. Implication graph

File key (all under `ArkLib/Data/CodingTheory/ProximityGap/` unless noted): OCP =
`OpenCoreConditionalPin.lean`; OCC = `OpenCoreConverse.lean`; MTL = `MCAThresholdLedger.lean`;
TSC = `Frontier/_TwoSidedCapstone.lean`; WC = `Frontier/_WallCapstone.lean`; R13 =
`Frontier/_R13HyperplaneSecondMoment.lean`; R14 = `Frontier/_R14SupNormWeakerThanWall.lean`;
PFB = `Frontier/_PrizeFloorOfBGK.lean`; CSB = `CharSumDeltaStarBridge.lean`; MT =
`MetaTheoremSecondOrderCap.lean`; A7 = `Frontier/_CoreA7_NecessityTight.lean`; SMD =
`Frontier/StackMaximizerDomination.lean`; FCC = `Frontier/_FloorClosureContract.lean`; OPN =
`OrbitCountPinNecessity.lean`; MOS = `Frontier/_MomentOptimizedSupNorm.lean`; CFB =
`Frontier/_AssaultV2_CrossFormBridge.lean`; ERM = `Frontier/_EnergyRatioMonotoneReduction.lean`;
ELC = `Frontier/EnergyLogConvexRatioMonotone.lean`; KPF = `KKH26PolyFieldCeiling.lean`; PCC =
`Frontier/PrizeConditionalPinCapstone.lean`; MLE = `Frontier/_MomentLadderExceedsPrize.lean`;
DBR = `Frontier/_DeltaStarBindingRigidity.lean`; B01 = `Frontier/_BridgeB01.lean`; TDA =
`Frontier/TwoDAnnihilatorLineParseval.lean`; P1X = `Frontier/_P1RateQuarterCrossConeBridge.lean`;
GC = `GrandChallenges.lean`; COL = `Collapse.lean`; WB = root `PROXIMITY_PRIZE_WORKBENCH.lean`.
"δ*" = `mcaDeltaStar`. Two long names are abbreviated with `…` (full names in §3).

| arrow | Lean name | file:line | dir · conditions |
|---|---|---|---|
| WCI C δ B ⟹ ε_mca ≤ B/q | `epsMCA_le_of_worstCaseIncidence` | OCP:115 | ⟹ · none |
| ε_mca ≤ B/q ⟹ WCI | `worstCaseIncidenceBounded_of_epsMCA_le` | TSC:104 | ⟹ · none |
| ε_mca ≤ B/q ⟺ WCI | `epsMCA_le_iff_worstCaseIncidenceBounded` | TSC:145 | ⟺ · definitional |
| WCI ∧ B/q ≤ ε* ∧ δ ≤ 1 ⟹ δ ≤ δ* | `worstCaseIncidence_pin` | OCP:135 | ⟹ · hδ, hbudget |
| δ < δ*(E/q) ⟹ WCI C δ E | `worstCaseIncidence_of_lt_mcaDeltaStar` | OCC:172 | ⟹ · strict int. |
| both halves packaged | `deltaStar_iff_incidence_budget` | OCC:269 | <⟹ / ⟹≤ · δ ≤ 1 |
| ε_mca ≤ ε* ∧ δ ≤ 1 ⟹ δ ≤ δ* | `le_mcaDeltaStar_of_good` | MTL:97 | ⟹ · none |
| ε* < ε_mca(δbad) ⟹ δ* ≤ δbad | `mcaDeltaStar_le_of_bad` | MTL:127 | ⟹ · none |
| WCI ⟺ ∃ dominating stack ≤ B | `exists_singleStackDominationCert…_iff_…` | SMD:138 | ⟺ · finite |
| WCI ∧ floorGood ⟺ closure(univ) | `floorClosureBudgetedMaxAtField_univ_iff_…` | FCC:519 | ⟺ |
| WCI(n) ∧ factorization ⟹ N_u ≤ d | `orbitCount_le_of_worstCaseIncidenceBounded` | OPN:128 | ⟹ |
| WallHolds ⟹ ‖η_b‖^{2r} ≤ q·Wick_r | `charSum_of_wallHolds` | WC:98 | ⟹ · ψ primitive |
| WallHolds ⟹ ‖η_b‖ ≤ √(2e n(ln q+1)) | `supNorm_le_of_wallHolds` | MOS:251 | ⟹ · e ≤ q |
| DCEnergyBound ⟺ SignedDeep | `dcEnergyBound_iff_signedDeepCancellation` | CFB:83 | ⟺ · Fourier |
| ERM ∧ GEB 1 ⟹ ∀r GEB r ⟹ WCISB | `gaussianEnergyBound_of_ERM` | ERM:113/140 | ⟹ · ERM refuted |
| supNorm ≤ (2r+1)|G| ⟹ ERM-step r | `erm_step_of_supNorm` | ELC:178 | ⟹ · reverse absent |
| ‖η_b‖ ≤ B ∧ ⌈|G|+qB⌉/q ≤ ε* ⟹ δ ≤ δ* | `le_mcaDeltaStar_of_charSumBound` | CSB:223 | ⟹ · VACUOUS |
| WallHolds ∧ RealizedIncBudget ⟹ δ ≤ δ* | `wall_capstone` | WC:176 | ⟹ · glue vacuous |
| hBGK ∧ WCI ∧ budget ⟹ δ ≤ δ* | `prizeFloor_of_BGK_and_incidence` | PFB:112 | ⟹ · hBGK INERT |
| + KKH26 ceiling ⟹ window bracket | `prizeFloor_window_of_BGK_and_incidence` | PFB:162 | ⟹ |
| TZ supply ⟹ ∃p, δ*(evalCode) ≤ 1−r/2^μ | `kkh26_mcaDeltaStar_le_of_TZ` | KPF:215 | ⟹ · TZ named |
| ceiling ∧ ε_mca(edge) ≤ ε* ⟹ δ* = edge | `prize_deltaStar_eq_edge` | PCC:70 | = · hfloor named |
| ∑_{s₀}‖I_H‖² = q∑_{b∈H}‖η_b‖² | `incidenceSum_sq_sum_offsets` | R13:91 | = · ψ primitive |
| sup M ⟹ ‖I_H(s₀)‖ ≤ |H|·M only | `incidenceSum_norm_le_card_mul_supBound` | R13:216 | ⟹ · :243 |
| sup B ⟹ only A_r ≤ |H|B^{2r} | `supBound_sumPow_le` | R14:80 | ⟹ · — |
| Wick₁ < projection at wall const | `wick_lt_supProjection_r1` | R14:106 | < · q,n ≥ 1 |
| |η b| ≤ g(∑η²) ∀η ⟹ √S ≤ g S | `secondMoment_method_floor` | MT:112 | ⟹ · class: g(2nd mom.) |
| |η b| ≤ g(∑η^{2r}) ∀η ⟹ √S ≤ g(S^r) | `momentDepth_method_floor` | MT:154 | ⟹ · class: g(1 mom.) |
| √(n log(q/n)) < (qE_r)^{1/2r} ∀r | `moment_ladder_exceeds_prize` | MLE:49 | < · log(q/n) < n |
| scale inequalities only | `deltaStar_determination_all_or_nothing` | DBR:85 | ineq · no δ*, no M |
| δ* = 1−ρ−m*/n | `deltaStar_master_gap_identity` | B01:66 | = · 3 defn. hyps |
| m* ≤ M ⟺ ∃m≤M, Σ ≤ budget | `mStar_le_iff_BCHKS_window` | A7:109 | ⟺ · hident; Nat.find |
| ¬BCHKSWindow ⟹ M < m* | `BCHKS_necessary` | A7:282 | ⟹ · hident; abstract |
| line |η| image = global image | `lineEta_image_eq_globalImage` | TDA:148 | = · b₀ ≠ 0 |
| N⁴ < P < N⁶ | `swarm_sub_burgess` | P1X:168 | num · norm_num |
| mcaConjecture ⟹ lower witnesses | `nonempty_mcaLowerWitness_of_mcaConjecture` | GC:>650 | ⟹ |
| grandMCAChallenge ⟺ ε_mca(C,1) ≤ ε* | `grandMCAChallenge_iff_epsMCA_one` | COL:161 | ⟺ · F6 |
| Shaw gap B ⟹ all moments | `shaw_offdiag_moment_le` | WB:407 | ⟹ · sup bound B |
| WorstCaseIncidenceBound ⟹ bad ≤ B | `badScalars_card_le_of_worstCase` | WB:340 | ⟹ · none |

**Arrows asserted in prose with NO Lean declaration (grep-verified):**
WCI ⟹ `WorstCaseIncompleteSumBound`; WCI ⟹ `DCEnergyBound`/`WallHolds`; `δ ≤ mcaDeltaStar` ⟹
any Fourier bound; `ShawGapLaw ⟺ WorstCaseIncidenceBound`; `(R) ⟸ ShawFlatness`;
`ERM-at-r ⟺ M² ≤ (2r+1)n`; `m* = m_KKH26 ⟺ M ≤ M_KKH26`; `HyperplaneCancellation` (no def);
Tetrachotomy, Arithmetic Uncertainty Principle, bounded-complexity principle (no decls).

## 5. The three answers

**(a) Is there a Lean theorem "mcaDeltaStar/mcaConjecture at δ inside the window ⟹
WorstCaseIncompleteSumBound / DCEnergyBound / ShawGapLaw"?** **No.** Grep over the cone (§9)
for any theorem with a Fourier-layer conclusion and a `mcaDeltaStar`/`epsMCA`/
`WorstCaseIncidenceBounded` hypothesis returns nothing; the only `_of_worstCaseIncidenceBounded`
theorems are combinatorial repackagings (`OrbitCountPinNecessity.lean:128/144/326`,
`StackMaximizerDomination.lean:103`, `_StackCandidateFamilyMax.lean:179`,
`_StackProfileRefinement.lean:170`). What IS proved instead: (i) `δ < mcaDeltaStar C (E/q) →
WorstCaseIncidenceBounded C δ E` (`OpenCoreConverse.lean:172`) and the iff `epsMCA ≤ B/q ⟺ WCI`
(`_TwoSidedCapstone.lean:145`) — necessity of the *incidence* Prop, a definitional unfolding of
`epsMCA` as a sup of per-stack probabilities, with the constant `B = E` exact; (ii) every
Fourier ⟹ δ* arrow carries either the naive budget `⌈|G|+q·B⌉/q ≤ ε*`
(`CharSumDeltaStarBridge.lean:223`, `_WallCapstone.lean:176`; docstrings state it forces
`B ≈ 0` at the prize) or WCI itself as a hypothesis (`_PrizeFloorOfBGK.lean:112/162`, hBGK
inert). Direction proved: **incidence ⟹ floor and floor(strict) ⟹ incidence; never
incidence ⟹ M.** Moreover `_R13HyperplaneSecondMoment.lean:91/216/243` +
`_R14SupNormWeakerThanWall.lean:80/106` pin the formal gap: a sup-bound `M` yields only the
`s₀`-average `√|H|·M` and the pointwise triangle scale `|H|·M`; DISPROOF_LOG:485 records "the
two open Props are INDEPENDENT".

**(b) Is the Meta-Theorem about all proofs or a class of methods?** **A class of methods.** Its
formal hypotheses are `hg : ∀ (η : ι → ℝ) (b : ι), |η b| ≤ g (∑ i, (η i) ^ 2)` (second moment)
and `hg : ∀ η b, |η b| ≤ g (∑ i, (η i) ^ (2 * r))` (one fixed depth) — i.e. certifiers
`g : ℝ → ℝ` that are functions of a *single* power sum, valid for *all* real families; the
witness is the spike. Nothing about SDP/Delsarte-LP/cumulants/"the Shaw operator" is formalized
as a class, and no theorem quantifies over proofs of `epsMCA ≤ ε*`. The dossier's "every
second-order / energy / spectral / LP method provably caps at Johnson/√p" (v3 §4.1) is the
one-moment-certifier theorem plus an informal extension; the Tetrachotomy (§4.2), Arithmetic
Uncertainty Principle (§4.3) and bounded-complexity principle (§4.4) have no Lean declarations.

**(c) Does the prize predicate require an EXACT determination, or is a floor
`δ* ≥ 1−√ρ + c` already prize-relevant?** The formal predicate requires exactness:
`grandMCAChallenge` (`GrandChallenges.lean:96`) demands a `δ*` with `epsMCA C δ* ≤ ε*` **and**
`∀ δ, δ* < δ → δ ≤ 1 → epsMCA C δ > ε*` (maximality); `GrandMCAResolution` (:185) carries the
same `maximal` field. The repo's record of [ABF26] p.5 (`GrandChallenges.lean` header):
"determine the largest `δ*_C ∈ [0, 1]` such that `ε_mca(C, δ*_C) ≤ ε*`" (dossier v3 §1.1:
"**Determine** the largest δ*"). Under the formal statement a floor `1−√ρ+c` is an
`MCALowerWitness` (:198) — "**Lower one-sided progress** … Forces `δ* ≥ δ` for any resolution"
— and the header explicitly counts it as prize progress: "any theorem of the form
`ε_mca(RS[F,L,k], δ) ≤ ε*` for some computable `δ`-expression … yields a constructive witness".
It is not a resolution. Two caveats: the real-valued encoding collapses (`Collapse.lean:161`:
`grandMCAChallenge C ε* ↔ epsMCA C 1 ≤ ε*`), so exactness formally lives on the `1/n`-lattice
(`mcaLatticeThreshold`, `Lattice.lean:104`, whose *existence* is trivial); and `mcaConjecture`
(:650) is not the prize predicate at all but the §4.5 draft polynomial bound (`\ignore{}`
block), which does not mention δ*.

## 6. Honesty gaps — dossier prose STRONGER than the checked theorem

1. v3 §0.2 "plain-RS δ\* in the window IS the Paley/BGK object, **provably**" / "Twelve
   independent technologies re-derive `M(μ_n)`": no theorem; 0 DISPROOF_LOG hits for "twelve
   independent"; v4 §1 drops the sentence but v3 stays the canonical §0 cite.
2. "The wall is two-sided, **necessary**" (v3 §0.2): the machine-checked iff is
   `epsMCA ≤ B/q ⟺ WCI` — bookkeeping on the incidence side; no arrow to the wall.
3. `HyperplaneCancellation` is treated as a named Prop (v3 §0.2, DISPROOF_LOG:477/556,
   `_TwoSidedCapstone` docstring, `_R13`): **no declaration**. Formal stand-ins are
   `RealizedIncidenceBudget` (`_WallCapstone.lean:121`) and `IncidenceFromWallGlue`
   (`_TwoSidedCapstone.lean:249`), both naive and vacuous at the prize budget by their own docs.
4. v3 §4.1 Meta-Theorem "every … SDP/Delsarte-LP, cumulants, the Shaw operator … provably
   caps": formal content is one-moment certifiers only (§5b).
5. v3 §4.2–4.4 Tetrachotomy / Arithmetic Uncertainty Principle / bounded-complexity principle:
   prose, no Lean objects.
6. `_CoreA7_NecessityTight` header "BCHKS 1.12 is NECESSARY … no closure of the prize can avoid
   proving BCHKS": theorems are over abstract `D Sigma : ℕ → ℕ → ℕ` with `hident` as hypothesis,
   `BCHKSBudget := Sigma s r ≤ B`, `mStar := Nat.find` (necessity is definitional); never
   touches `mcaDeltaStar` or a character sum; E1 hypotheses use the off-by-one `(mstar−1)/n`
   that `_BridgeB01`/`_BchksF3` corrected to `mstar/n`.
7. `_DeltaStarDefinitive.lean:178` docstring "proven two-sided reduction of the interior reach
   to `BGKFloor`": the theorem is a conjunction of three disconnected facts; `G` in part (b) is
   unrelated to `C`; "(b) necessity" is `moment_route_insufficient` over abstract count
   functions.
8. `EnergyLogConvexRatioMonotone.lean:32` names `erm_at_deep_presupposes_supNorm` as HEADLINE;
   no such theorem exists; the landed `erm_step_of_supNorm` (:178) is supNorm ⟹ ERM-step.
9. v3 §1.4 "`m* = m_KKH26 ⟺ M ≤ M_KKH26` via `_EnergyRatioMonotoneReduction`": that file has
   forward implications only and refutes ERM globally (DISPROOF_LOG:481 already flags the iff).
10. Root workbench §9 "`ShawFlatnessConjecture ⟺ WorstCaseIncidenceBound ⟺ monomial-extremal
    optimality`" and §3 "`(R) ⟸ ShawFlatness`": no theorem links `ShawGapLaw`/`ShawFlatness`
    to `cosetLowWeight`; landed arrows are `badScalars_card_le_of_worstCase` (:340) and
    `shaw_offdiag_moment_le` (:407), both one-directional and on different objects.
11. `deltaStar_determination_all_or_nothing`: name and v3 §0.7 ("δ\*-irrelevant by …") promise
    a δ\* statement; the theorem is three real inequalities on scales with no δ\*, `M`, or code.
12. `_PrizeFloorOfBGK` name/`hBGK`: the BGK hypothesis is inert (proof =
    `worstCaseIncidence_pin`); the docstring says so, but v3 §0.2 reads the same file as
    "necessity" while only §2.5's "floor ⟸ incidence bound" row is the honest reading.
13. `GrandChallenges.lean` header cites `GrandChallengeCollapse.lean` — absent; content is
    `Collapse.lean` (dangling reference).
14. `DISPROOF_LOG.md` is duplicated end-to-end (line 2882 = 28149, 10735 = 36002; 53,709
    lines); every ledger grep count is doubled.

## 7. What a bypass-seeking lane would have to prove (not provably equivalent to the wall)

1. Target: `WorstCaseIncidenceBounded (evalCode g n k) δ E` at a window `δ` with `E/p ≤ ε*`,
   or (equivalently, `StackMaximizerDomination.lean:138`) one dominating stack within budget.
2. Route it through the arithmetic of the specific stack (monomial pencils, R9; coset dichotomy
   of `LineListMCAWeld`; the P1 `SwarmResidual` sub-Burgess LIST problem, kernel-pinned DISTINCT
   from the B-side wall by `swarm_sub_burgess`) — never via `max_b|η_b|`, `E_r`, `DCEnergyBound`.
3. Provably-equivalent-to-WCI (hence NOT a bypass, but NOT the wall either): `epsMCA ≤ E/q`,
   `δ < mcaDeltaStar`, field closure(univ), single-stack domination, orbit certificate.
4. Provably-equivalent-to-the-wall (avoid): `WallHolds`, `DCEnergyBound`@r,
   `SignedDeepCancellation`, `WorstCaseIncompleteSumBound`, `GaussianEnergyBound`, ERM-at-r.
5. Nothing in Lean forbids (1) without (4); R13/R14 show WCI is phase-sensitive and `M` is not
   determined by it either way. Doctrine v2 §1 "(THE ATOM) … a winning proof must supply" is a
   meta-claim over the recorded gauges (G77), not a theorem — a heuristic, not a gate.

## 8. What remains / classification

- Exact pin: none produced. Unconditional component: none new. Conditional reduction: none new.
- Refutation/no-go (this note): the *necessity claim as stated* has no theorem; a bypass is
  formally unblocked. Open residual: CORE unchanged, **OPEN / ON-BGK**.
- Next concrete step: a lane that attacks WCI at a window radius for a *structured* maximizer
  (R9 monomial extremal) using only incidence/algebra, with `pg-iterate` on a Mathlib-only file.

## 9. Ledger greps run (DISPROOF_LOG.md, root, 53,709 lines — duplicated ×2)

`necess` 104 · `bypass` 40 · `converse` 121 · `not a function of M` 4 · `World II` 8 ·
`INDEPENDENT` 1034 · `twelve independent` 0 · `class-level` 0 · `Meta-Theorem` 74 ·
`provably the` 0. Entries read: O165 (:10735), O186 (:15829), `466-r12/r13/r14` (:470–600).
Cone greps: decl-level regex for every name in §3; `_of_(worstCaseIncidenceBounded|
mcaDeltaStar|epsMCA)` (38 hits, none Fourier-valued); `^(def|theorem) …HyperplaneCancellation`
(0); `sorry|axiom |admit|native_decide|sorryAx` over the 29 cited files (all hits are docstring
prose "NO sorryAx"); all 29 files are imported in `ArkLib.lean`.

## 10. References

`docs/kb/deltastar-DOSSIER-v3-2026-07-01.md` §0, §1.1, §1.4, §2.2–2.5, §4, §9, §11.6, §12,
§45; `docs/kb/deltastar-DOSSIER-v4-2026-08-16.md` §1, §6;
`docs/kb/deltastar-466-tool-shape-doctrine-v2-2026-07-10.md` §1–2;
`PROXIMITY_PRIZE_WORKBENCH.lean` §3, §6–§8b, §9–§10; `DISPROOF_LOG.md` O165, O186,
`466-r12/r13/r14`; [ABF26] as recorded in `GrandChallenges.lean` header and the
`mcaConjecture` docstring (draft-source caveat, verified 2026-06-03 there).

## Verification addendum (independent re-check, 2026-09-05 evening)

`scripts/pg-iterate.sh` was re-run on every `Frontier/_SW1_*.lean` file left untracked by
the SW1 round.  Result: `_SW1_F3_MasterHypothesisVacuous.lean` and
`_SW1_TRANSV_HeightCeiling.lean` compile axiom-clean; `_SW1_F1_UniformSylvesterRefuted.lean`
(≈20 elaboration errors, 6 `sorryAx` fallbacks), `_SW1_F3_UnionRankExact.lean` (4 errors at
lines 223–229, `hrank_false_of_mcaEvent_witness` and `pairJoint_of_hrank` depend on
`sorryAx`), `_SW1_HD_HasseDavenportCosetLadder.lean` (unknown identifiers
`FiniteField.primitiveChar_to_Complex*`, `ladder_coset_pair` on `sorryAx`) and
`_SW1_SPARSE_RootLocusAverage.lean` (2 errors) do **not**.  Any "axiom-clean" claim above
about those four files is therefore unverified until they are repaired; the master-hypothesis
vacuity (`not_stripMasterHypothesis*`, `syz46_antecedent_false`) **is** verified.  The four
broken files are deliberately left uncommitted.
