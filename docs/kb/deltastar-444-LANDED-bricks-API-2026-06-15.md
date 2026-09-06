# δ* Prize (#444) — LANDED bricks: actionable API handoff

*Reusable axiom-clean bricks + exact engines. Import and build on these; do NOT redo the work. Real signatures copied from files (verified on fork/main, 2026-06-15). Linked from issue #444 §5.*

## §5 — LANDED (Actionable Handoff)

All Lean signatures below are copied from the actual files (verified on the stated branch, 2026-06-15). Unless flagged otherwise each file ends with `#print axioms` self-asserting `{propext, Classical.choice, Quot.sound}` (axiom-clean, no `sorryAx`). Build idiom throughout: run `scripts/pg-warm.sh` ONCE (pre-builds substrate oleans, takes the lock), then iterate per-file with `scripts/pg-iterate.sh <path>` (= `lake env lean`, ~30–75s, NO lock → parallel). Files marked "fork/main only" are not in the `claude-iid-push` checkout — obtain with `git show fork/main:<path>`.

---

### A. Keystones — the single open core, stated and isolated

**OpenCoreConditionalPin** — the entire remaining open content of δ* in ONE Prop, with the implication proven.
`ArkLib/Data/CodingTheory/ProximityGap/OpenCoreConditionalPin.lean` (fork/main, commit `d689f92b7`) · namespace `ProximityGap.OpenCoreConditionalPin`
```lean
def WorstCaseIncidenceBounded (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)).card ≤ B
theorem epsMCA_le_of_worstCaseIncidence (C) (δ) {B} (hI : WorstCaseIncidenceBounded C δ B) :
  epsMCA C δ ≤ (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
theorem worstCaseIncidence_pin (C) (εstar) {δ B} (hδ : δ ≤ 1)
  (hI : WorstCaseIncidenceBounded C δ B) (hbudget : (B:ℝ≥0∞)/(Fintype.card F) ≤ εstar) :
  δ ≤ mcaDeltaStar C εstar
theorem worstCaseIncidence_pin_budget (C) {δ E} (hδ : δ ≤ 1) (hI : WorstCaseIncidenceBounded C δ E) :
  δ ≤ mcaDeltaStar C ((E:ℝ≥0∞)/(Fintype.card F))
theorem worstCaseIncidence_pin_of_orbitCount (C) (εstar) {δ S d n} (hδ : δ ≤ 1) (hS : 0 < S)
  (hsupply : S * d = n) (horbit : ∀ u, ∃ N, (#bad u) = N * S ∧ N ≤ d)
  (hbudget : (n:ℝ≥0∞)/(Fintype.card F) ≤ εstar) : δ ≤ mcaDeltaStar C εstar
```
*Proves:* isolates ALL remaining open prize content into the single Prop `WorstCaseIncidenceBounded C δ B` (worst-case far-line incidence I(δ) ≤ B over every stack) and proves (axiom-clean) it implies the δ* lower pin `δ ≤ mcaDeltaStar C ε*`. The Prop at window radius δ* = 1−ρ−H(ρ)/(β log n), budget B ≈ q·ε* ≈ n, IS the recognized-open explicit-μₙ list-decoding prize core. The implication is proven; the Prop itself is unproven (best unconditional = BGK n^{1−o(1)}, vacuous at B ≈ n).
*Consume:* `import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin`. To pin δ* from below, prove/assume `WorstCaseIncidenceBounded C δ B`, then `worstCaseIncidence_pin C εstar hδ hI hbudget` discharges `δ ≤ mcaDeltaStar C εstar`. For ε* = E/q use `worstCaseIncidence_pin_budget` (the open core alone suffices, no side condition). For the orbit-count attack surface use `worstCaseIncidence_pin_of_orbitCount` (supply per-stack #bad = N·S with N ≤ d, S·d = n). Routes through `MCAThresholdLedger.le_mcaDeltaStar_of_good` + `OrbitCountCrossingLaw.crossing_law`.
*Reproduce:* `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/OpenCoreConditionalPin.lean` (warm deps first: `scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw`).

**MetaTheoremSecondOrderCap** — certifies WHY every 2nd-order / energy / SDP / Parseval method is capped at √S, pins the only escape to moment depth r→∞.
`ArkLib/Data/CodingTheory/ProximityGap/MetaTheoremSecondOrderCap.lean` (fork/main, commit `758bdeb1b`) · namespace `ProximityGap.MetaTheoremSecondOrderCap`
```lean
def spike (b₀ : ι) (v : ℝ) : ι → ℝ := fun i => if i = b₀ then v else 0
theorem abs_le_sqrt_secondMoment (η : ι → ℝ) (b : ι) : |η b| ≤ Real.sqrt (∑ i, (η i)^2)
theorem secondMoment_method_floor (g : ℝ → ℝ)
  (hg : ∀ η b, |η b| ≤ g (∑ i, (η i)^2)) {S} (hS : 0 ≤ S) : Real.sqrt S ≤ g S   -- [Nonempty ι]
theorem sup_le_moment_root (η) {r} (hr : 1 ≤ r) (b) : |η b| ≤ (∑ i, |η i|^(2*r))^((1:ℝ)/(2*r))
theorem momentRoot_one_eq_sqrt (η) : (∑ i, |η i|^(2*1))^((1:ℝ)/(2*1)) = Real.sqrt (∑ i, (η i)^2)
theorem momentDepth_method_floor {r} (hr : 1 ≤ r) (g)
  (hg : ∀ η b, |η b| ≤ g (∑ i, (η i)^(2*r))) {S} (hS : 0 ≤ S) : Real.sqrt S ≤ g (S^r)
noncomputable def gapFactor (m r : ℕ) : ℝ := (m:ℝ)^((1:ℝ)/(2*r))
theorem flat_gapFactor_antitone {m} (hm : 1 ≤ m) {r s} (hr : 1 ≤ r) (hrs : r ≤ s) : gapFactor m s ≤ gapFactor m r
theorem flat_gapFactor_tendsto_one {m} (hm : 1 ≤ m) : Tendsto (fun r => gapFactor m r) atTop (𝓝 1)
```
*Proves:* (1) any method g consuming only ∑η² satisfies g(S) ≥ √S (spike witness) — no 2nd-order argument reaches the prize floor √(n·log(q/n)) ≪ √S = √(n·q). (2) No single fixed depth r beats √S either (spike's depth-r moment = Sʳ ∀r). (3) The flat-profile gap factor is exactly m^{1/(2r)}, antitone in r and → 1. Net: the prize core is irreducibly a high-moment (r ≈ log q) statement; rules out the entire variance/energy/Parseval/SDP class.
*Consume:* `import ArkLib.Data.CodingTheory.ProximityGap.MetaTheoremSecondOrderCap`. Pure real-analysis (`η : ι → ℝ`, no coding-theory deps). To certify a proposed bound is doomed: if it consumes only ∑η², instantiate `secondMoment_method_floor g hg hS` for the √S floor it cannot beat. For the valid route: `sup_le_moment_root η hr b`, then minimize over r and feed a depth-r moment bound. Use as the no-go citation when reviewing any δ* conjecture proof.
*Reproduce:* `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/MetaTheoremSecondOrderCap.lean` (no substrate warm — Mathlib-only, ~18s).

**RigidityReductionPrizeScale** — at prize scale, char-p far-line incidence I_p(δ) = char-0 I₀(δ) for the full odd rigidity system.
`ArkLib/Data/CodingTheory/ProximityGap/RigidityReductionPrizeScale.lean` (fork/main, commit `f414cf059`) · namespace `ProximityGap.RigidityReductionPrizeScale`
```lean
def CharPOnlyWitness (p r : ℕ) (B : ℤ) : Prop := ∃ N : ℤ, N ≠ 0 ∧ (p:ℤ)^r ∣ N ∧ |N| ≤ B
theorem no_charPOnly_witness {p r B} (hPB : B < (p:ℤ)^r) : ¬ CharPOnlyWitness p r B
theorem incidence_eq_of_charPexcessFree {p r B} (B0 Bp : Finset ι) (hsub : B0 ⊆ Bp)
  (hwit : ∀ α ∈ Bp, α ∉ B0 → CharPOnlyWitness p r B) (hPB : B < (p:ℤ)^r) : Bp.card = B0.card
theorem charPexcessFree_iff_prizeThreshold {k p} (hk : 0 < k) (heven : 2*(k/2) = k) :
  ((2*k)^(2*k) : ℤ) < (p:ℤ)^(k/2) ↔ (2*k)^4 < p
theorem incidence_charIndependent_fullSystem {p} (hp : (2^30)*2^128 ≤ p) (B0 Bp) (hsub)
  (hwit : ∀ α ∈ Bp, α ∉ B0 → CharPOnlyWitness p ((2^30/2)/2) ((2*(2^30/2))^(2*(2^30/2)))) : Bp.card = B0.card
theorem single_readout_threshold_not_prize : ((2^30)*2^128 : ℕ) < (2*(2^30/2))^(2*(2^30/2))
```
*Proves:* B₀ ⊆ B_p always; a char-p-only bad index forces a nonzero integer norm N with pʳ ∣ N, |N| ≤ (2k)^{2k} — impossible once B < pʳ (`no_charPOnly_witness`). For the full odd system r = k/2 the gap ⟺ (2k)⁴ < p, which holds at prize scale (2¹²⁰ < 2¹⁵⁸), collapsing the prize to the q-free char-0 incidence law. Honest negative half `single_readout_threshold_not_prize`: a single r=1 readout does NOT meet the threshold (matches the DISPROOF_LOG n=32 deg-3 h₃ excess prime).
*Consume:* `import ArkLib.Data.CodingTheory.ProximityGap.RigidityReductionPrizeScale`. Supply (a) `hsub : B0 ⊆ Bp`, (b) the NAMED Galois-divisibility hyp `hwit` (one unformalized cyclotomic-norm input, carried explicitly — needs NumberField/Algebra.norm machinery absent from Mathlib), then `incidence_charIndependent_fullSystem hp B0 Bp hsub hwit` gives `Bp.card = B0.card`. Arithmetic core `no_charPOnly_witness` is reusable standalone. Do NOT apply to single readouts.
*Reproduce:* `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/RigidityReductionPrizeScale.lean` (warm: `scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.BadPrimeNormBound`).

---

### B. Bracket + spectral bridge — two-sided δ* frame

**PrizeConditionalPinCapstone** — the honest assembly point: δ* pinned to an explicit closed value, resting on ONE open hypothesis. *(fork BRANCHES only — NOT fork/main.)*
`Research/ProximityPrize/Frontier/PrizeConditionalPinCapstone.lean` on `fork/claude-cliff-confinement` (commit `1ae3ae2e4`), also `fork/claude-cube-reframing`, `fork/claude-sqrtcancel-session` · namespace `ArkLib.ProximityGap.KKH26`
```lean
noncomputable def prizeEdge (n m r : ℕ) (C L : ℝ≥0) : ℝ≥0 :=
  (1 - ((r-2:ℕ)*m + 1 : ℕ)/(n:ℝ≥0)) - 1/(C*L)
theorem prizeEdge_le_one (n m r C L) : prizeEdge n m r C L ≤ 1
theorem prize_deltaStar_eq_edge {p n} [Fact p.Prime] [NeZero n] {μ m r} (hμ : 1 ≤ μ) {g}
  (hm : 1 ≤ m) (hn : n = 2^μ*m) (hg : orderOf g = 2^μ*m) (hp : (2^μ)^2^(μ-1) < p)
  (hr2 : 2 ≤ r) (hr : r ≤ 2^(μ-1)) (εstar) (hεstar : εstar < (2^r*(2^(μ-1)).choose r)/(p:ℝ≥0∞))
  {C L} (hC : 0 < C) (hL : 0 < L) (hregime : (2:ℝ≥0)^μ ≤ C*L) (hgap : …)
  (hfloor : epsMCA (evalCode g n ((r-2)*m)) (prizeEdge n m r C L) ≤ εstar) :
  mcaDeltaStar (evalCode g n ((r-2)*m)) εstar = prizeEdge n m r C L
```
*Proves:* pins δ* = `prizeEdge = (1−ρ) − 1/(C·L)` (one window rung below capacity) for the concrete smooth-domain RS code `evalCode g n ((r−2)·m)` at prize scale, via `le_antisymm`: CEILING proven (Kambiré/KKH26 bad-line family, needs only Thorner–Zaman supply); FLOOR = the SINGLE open input `hfloor`. HONEST correction documented in-file: `hfloor` is STRICTLY FINER than BGK/Paley M(n) ≤ C√(n log m) — the only M→epsMCA route is vacuous at q·ε* ≈ n (overshoots by √m). So the prize is pinned modulo realized-incidence, NOT modulo M.
*Consume:* obtain via `git show fork/claude-cliff-confinement:Research/ProximityPrize/Frontier/PrizeConditionalPinCapstone.lean` or check out a carrying branch (its dep `KKH26AsymptoticCeiling` IS on fork/main). Supply the regime hypotheses + the single open `hfloor`, then `prize_deltaStar_eq_edge … hfloor` yields the exact δ*. Ceiling auto-discharged by `kkh26_mcaDeltaStar_le_capacity_sub_log` (fork/main `KKH26AsymptoticCeiling.lean:118`). Do NOT attempt `hfloor` from an M(n) char-sum bound — that route is documented vacuous.
*Reproduce:* `scripts/pg-iterate.sh Research/ProximityPrize/Frontier/PrizeConditionalPinCapstone.lean` (warm: `scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.KKH26AsymptoticCeiling`), ~56s.

**DeltaStarPinchBracketD3** — two-sided bracket on δ* for thin n=2^μ; REFUTES a pinch (constant ≈1/8 gap).
`ArkLib/Data/CodingTheory/ProximityGap/DeltaStarPinchBracketD3.lean` (fork/main) · namespace `ArkLib.ProximityGap.KKH26`
```lean
theorem kkh26_ceiling_rate_locked {p n} [Fact p.Prime] [NeZero n] {μ r} (hμ : 1 ≤ μ) {g}
  (hn : n = 2^μ) (hg : orderOf g = 2^μ) (hp : (2^μ)^2^(μ-1) < p) (hr2 : 2 ≤ r) (hr : r ≤ 2^(μ-1))
  (εstar) (hεstar : εstar < (2^r*(2^(μ-1)).choose r)/(p:ℝ≥0∞)) :
  mcaDeltaStar (evalCode g n ((r-2)*1)) εstar ≤ 1 - (r:ℝ≥0)/(2:ℝ≥0)^μ
def OverDetFloorGood (C) (εstar) (δbind) : Prop := δbind ≤ 1 ∧ epsMCA C δbind ≤ εstar
theorem deltaStar_two_sided_bracket … (hfloor : OverDetFloorGood (evalCode g n ((r-2)*1)) εstar δbind) :
  δbind ≤ mcaDeltaStar … ∧ mcaDeltaStar … ≤ 1 - (r:ℝ≥0)/(2:ℝ≥0)^μ
theorem bracket_gap_eq {μ r} (δbind δceil) (hceil : δceil = 1 - (r:ℝ≥0)/(2:ℝ≥0)^μ) :
  δceil - δbind = (1 - (r:ℝ≥0)/(2:ℝ≥0)^μ) - δbind
```
*Proves:* UPPER side unconditional δ* ≤ 1 − r/2^μ with r RATE-LOCKED (r = k+1, NOT free to minimize — naive free-min gives a spurious 0.5 below the exact 0.5625). LOWER side via the NAMED `OverDetFloorGood`. Numerics (GPU-checked to n=38) show the floor sits a CONSTANT ≈1/8 δ-gap below the KKH26 ceiling at ρ=1/4 that does NOT shrink with n — refutes a pinch; the remaining open quantity IS this gap.
*Consume:* `import ArkLib.Data.CodingTheory.ProximityGap.DeltaStarPinchBracketD3`. For the unconditional ceiling apply `kkh26_ceiling_rate_locked` (no floor obligation). For the lower side supply an `OverDetFloorGood` witness and apply `deltaStar_two_sided_bracket`; lower conjunct discharged internally by `MCAThresholdLedger.le_mcaDeltaStar_of_good`. `bracket_gap_eq` rewrites the gap to canonical form.
*Reproduce:* `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/DeltaStarPinchBracketD3.lean`. Numeric pinch evidence: `python3 scripts/probes/probe_wf3D3_pinch.py` (sweeps n∈{16,32}, prints floor vs δ_ceil + pinch verdict).

**IncidencePeriodBridge** — far-line incidence (face F1) = Gaussian-period spectrum (face F2), term-by-term and in L².
`ArkLib/Data/CodingTheory/ProximityGap/IncidencePeriodBridge.lean` (fork/main) · namespace `ArkLib.ProximityGap.IncidencePeriodBridge`
```lean
noncomputable def lineIncidence (G : Finset F) (s₀ s₁ : F) : ℕ :=
  (Finset.univ.filter (fun γ : F => s₀ + γ*s₁ ∈ G)).card
theorem conj_eta {ψ} (G) (b) : (starRingEnd ℂ) (eta ψ G b) = ∑ y ∈ G, ψ (-(b*y))
theorem lineIncidence_zero_dir (G) (s₀) : lineIncidence G s₀ 0 = (if s₀ ∈ G then Fintype.card F else 0)
theorem lineIncidence_period_sum {ψ} (hψ : ψ.IsPrimitive) (G) (s₀ s₁) :
  (lineIncidence G s₀ s₁ : ℂ) = ∑ b ∈ univ.filter (fun b => b*s₁ = 0), (starRingEnd ℂ)(eta ψ G b)*ψ(b*s₀)
theorem incidence_l2_eq_period_l2 {ψ} (hψ : ψ.IsPrimitive) (G) :
  (∑ s₀, (lineIncidence G s₀ 0 : ℝ)^2) = (Fintype.card F)*∑ b, ‖eta ψ G b‖^2
```
*Proves:* the affine-line incidence I(s₀,s₁) = ∑_{b⊥s₁} conj(η_b)·ψ(b·s₀) (Fourier-inversion: only s₁⊥ frequencies survive, b=0 gives η₀=|G|); and ∑_{s₀} I(s₀,0)² = q·∑_b‖η_b‖² (both = q²·|G|). The exact no-√-loss bridge identifying the incidence count controlling δ* with the per-frequency period M(n) = max_{b≠0}‖η_b‖ — quantitative skeleton of wall W4. No field-size/regime hypotheses.
*Consume:* `import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge` (transitively brings `SubgroupGaussSumSecondMoment`). To rewrite incidence → period spectrum, apply `lineIncidence_period_sum hψ`; to transfer L² energy apply `incidence_l2_eq_period_l2 hψ` and combine with `subgroup_gaussSum_secondMoment` to get q²·|G|. `conj_eta`/`lineIncidence_zero_dir` are helper rewrites.
*Reproduce:* `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/IncidencePeriodBridge.lean`.

**GaussPeriodParsevalFloor** — the PROVEN √n lower half of the spectral frame for M(n).
`ArkLib/Data/CodingTheory/ProximityGap/GaussPeriodParsevalFloor.lean` (fork/main) · namespace `ArkLib.ProximityGap.GaussPeriodParsevalFloor`
```lean
theorem sum_sq_erase_zero {ψ} (hψ : ψ.IsPrimitive) (G) :
  ∑ b ∈ univ.erase (0:F), ‖eta ψ G b‖^2 = (Fintype.card F)*G.card - (G.card:ℝ)^2
theorem exists_eta_sq_ge_parseval_floor {ψ} (hψ : ψ.IsPrimitive) (G) (hq : 2 ≤ Fintype.card F) :
  ∃ b : F, b ≠ 0 ∧ ((Fintype.card F)*G.card - (G.card:ℝ)^2)/((Fintype.card F)-1) ≤ ‖eta ψ G b‖^2
```
*Proves:* ∑_{b≠0}‖η_b‖² = q·n − n² = (q−n)·n; by pigeonhole some b≠0 has ‖η_b‖² ≥ n(q−n)/(q−1) ≈ n, so M(n) ≥ √n — the unavoidable Alon–Boppana/Parseval floor. The matching upper M(n) ≤ C√(n·log(1/ε*)) is the open BGK/Paley wall (named-open, NOT this file).
*Consume:* `import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodParsevalFloor`. Apply `exists_eta_sq_ge_parseval_floor hψ hq` for the √n floor on the worst non-principal period. Use `sum_sq_erase_zero` directly for the exact nonzero-frequency energy (q−n)·n.
*Reproduce:* `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/GaussPeriodParsevalFloor.lean`.

---

### C. Moment–energy ladder — Parseval substrate → DC-subtraction → deep-tail

**SubgroupGaussSumMoment** *(SUBSTRATE — every moment/energy brick consumes this)* — the even-moment Parseval law ∑_b‖η_b‖^{2r} = q·E_r.
`ArkLib/Data/CodingTheory/ProximityGap/SubgroupGaussSumMoment.lean` (fork/main, commit `4cb5d5582`) · namespace `ArkLib.ProximityGap.SubgroupGaussSumMoment`
```lean
noncomputable def rEnergy (G : Finset F) (r : ℕ) : ℕ :=
  ∑ v ∈ piFinset (fun _:Fin r => G), ∑ w ∈ piFinset (fun _:Fin r => G), (if ∑ i, v i = ∑ i, w i then 1 else 0)
theorem subgroup_gaussSum_moment {ψ} (hψ : ψ.IsPrimitive) (G) (r) :
  ∑ b : F, ‖eta ψ G b‖^(2*r) = (Fintype.card F)*rEnergy G r
theorem eta_pow (ψ) (G) (b) (r) : eta ψ G b ^ r = ∑ v ∈ piFinset (fun _:Fin r => G), ψ (b*∑ i, v i)
```
*Proves:* ∑_{b∈F}‖η_b‖^{2r} = q·E_r(G) where E_r = r-fold additive energy, via character orthogonality (the ONLY analytic input the whole ladder uses). Defines `rEnergy` and the expansion atom `eta_pow`.
*Consume:* `import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment`. `subgroup_gaussSum_moment` turns any per-frequency sup goal into E_r (then `Finset.single_le_sum`). `eta` comes from `SubgroupGaussSumSecondMoment`. Use `rEnergy` as the canonical r-fold-energy name.
*Reproduce:* `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/SubgroupGaussSumMoment.lean`.

**DCSubtractedMoment** — the DC-subtracted Parseval identity isolating the prize object.
`ArkLib/Data/CodingTheory/ProximityGap/DCSubtractedMoment.lean` (fork/main) · namespace `ArkLib.ProximityGap.DCSubtractedMoment`
```lean
theorem eta_zero (ψ) (G) : eta ψ G 0 = (G.card : ℂ)
theorem sum_nonzero_moment {ψ} (hψ : ψ.IsPrimitive) (G) (r) :
  ∑ b ∈ univ.erase (0:F), ‖eta ψ G b‖^(2*r) = (Fintype.card F)*rEnergy G r - (G.card:ℝ)^(2*r)
```
*Proves:* ∑_{b≠0}‖η_b‖^{2r} = q·E_r − |G|^{2r} (full moment minus DC term ‖η₀‖^{2r}=|G|^{2r}). Since M(n) excludes b=0 and M^{2r} ≤ this, A_r = E_r − |G|^{2r}/q is the right object.
*Consume:* `import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment`. `sum_nonzero_moment` is the foundational rewrite: `rw [← sum_nonzero_moment hψ G r]` then bound a single term with `Finset.single_le_sum`. `eta_zero` discharges the DC value.
*Reproduce:* `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/DCSubtractedMoment.lean`.

**DCEnergyEssential** — machine-checks ★★ that DC subtraction is ESSENTIAL: raw E_r ≤ Wick is FALSE at prize.
`ArkLib/Data/CodingTheory/ProximityGap/DCEnergyEssential.lean` (fork/main) · namespace `ArkLib.ProximityGap.DCEnergyEssential`
```lean
theorem q_mul_energy_ge_dc {ψ} (hψ) (G) (r) : (G.card:ℝ)^(2*r) ≤ (Fintype.card F)*rEnergy G r
theorem energy_ge_dc {ψ} (hψ) (G) (r) (hq : 0 < Fintype.card F) :
  (G.card:ℝ)^(2*r)/(Fintype.card F) ≤ rEnergy G r
theorem not_gaussianEnergyBound_of_dc_gt_wick {ψ} (hψ) (G) (r) (hq)
  (hdc : (doubleFactorial (2*r-1))*(G.card)^r < (G.card)^(2*r)/(Fintype.card F)) : ¬ GaussianEnergyBound G r
theorem not_gaussianEnergyBound_of_card_pow_gt {ψ} (hψ) (G) (r) (hq) (hG : 0 < G.card)
  (htrig : (Fintype.card F)*(doubleFactorial (2*r-1)) < (G.card)^r) : ¬ GaussianEnergyBound G r
```
*Proves:* E_r ≥ |G|^{2r}/q (DC mass). When |G|^r > q·(2r−1)‼ the raw `GaussianEnergyBound` (the named open input of the in-tree non-DC chain) is PROVABLY FALSE. Crossover at n=64; vacuous for all n≥64 at optimal r≈ln q. Only the DC-subtracted A_r ≤ Wick is non-vacuous.
*Consume:* `import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyEssential`. Use `not_gaussianEnergyBound_of_card_pow_gt` to DISCHARGE any "assume `GaussianEnergyBound G r` at prize r" (trigger `htrig`: q·(2r−1)‼ < |G|^r). `energy_ge_dc`/`q_mul_energy_ge_dc` give the reusable DC lower bound.
*Reproduce:* `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/DCEnergyEssential.lean`. Crossover: `python3 scripts/probes/probe_dc_essential.py`.

**DCMomentSupBound** — the sharp DC-subtracted per-frequency Wick-capable bound.
`ArkLib/Data/CodingTheory/ProximityGap/DCMomentSupBound.lean` (fork/main) · namespace `ArkLib.ProximityGap.DCMomentSupBound`
```lean
theorem eta_pow_le_dc {ψ} (hψ) (G) (r) {b} (hb : b ≠ 0) :
  ‖eta ψ G b‖^(2*r) ≤ (Fintype.card F)*rEnergy G r - (G.card:ℝ)^(2*r)
theorem eta_pow_le_dc_of_energyBound {ψ} (hψ) {G r} (h : GaussianEnergyBound G r) {b} (hb : b ≠ 0) :
  ‖eta ψ G b‖^(2*r) ≤ (Fintype.card F)*((doubleFactorial (2*r-1))*(G.card)^r) - (G.card:ℝ)^(2*r)
```
*Proves:* for b≠0, ‖η_b‖^{2r} ≤ q·E_r − |G|^{2r} (one non-DC term ≤ DC-subtracted total) — strictly sharper than the non-DC bound because the principal-character mass is removed.
*Consume:* `import ArkLib.Data.CodingTheory.ProximityGap.DCMomentSupBound`. `eta_pow_le_dc` discharges the per-b≠0 single-term sup UNCONDITIONALLY (needs ψ primitive + b≠0). At the prize feed `DCEnergyCorrection.DCEnergyBound` via `eta_pow_le_of_dcEnergyBound` (non-vacuous), not the raw form.
*Reproduce:* `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/DCMomentSupBound.lean`.

**DCEnergyCorrection + DCEnergyBaseCase + DCEnergyRungTwo + DCOptimized + DCWorstCaseWiring** — the cleared (division-free) Wick-capability pin: DCEnergyBound Prop, r=1,2 proven, floor-reaching M ≤ √(2e·n·ln q).
`ArkLib/Data/CodingTheory/ProximityGap/DCEnergyCorrection.lean` | `DCEnergyBaseCase.lean` | `DCEnergyRungTwo.lean` | `DCOptimized.lean` | `DCWorstCaseWiring.lean` (all fork/main)
```lean
def DCEnergyBound (G) (r) : Prop :=                                           -- DCEnergyCorrection
  (Fintype.card F)*rEnergy G r - (G.card:ℝ)^(2*r) ≤ (Fintype.card F)*((doubleFactorial (2*r-1))*(G.card)^r)
theorem eta_pow_le_of_dcEnergyBound {ψ} (hψ) {G r} (h : DCEnergyBound G r) {b} (hb : b ≠ 0) :
  ‖eta ψ G b‖^(2*r) ≤ (Fintype.card F)*((doubleFactorial (2*r-1))*(G.card)^r)
theorem dcEnergyBound_one {ψ} (hψ) (G) : DCEnergyBound G 1                    -- DCEnergyBaseCase (r=1 free)
theorem dcEnergyBound_two_rootsOfUnity {m} (hm : 1 ≤ m) {p} [Fact p.Prime] …  -- DCEnergyRungTwo (E₂=3n²−3n)
  (hp : 12^(2^m).totient < p^2) {ω} (hω : IsPrimitiveRoot ω (2^m)) {ψ} (hψ) :
  DCEnergyBound ((range (2^m)).image (ω^·)) 2
theorem eta_sq_le_dcOptimized {ψ} (hψ) {G r} (hr : 1 ≤ r) (hrq : Real.log (Fintype.card F) ≤ r)  -- DCOptimized
  (h : DCEnergyBound G r) {b} (hb : b ≠ 0) : ‖eta ψ G b‖^2 ≤ 2*Real.exp 1*(G.card)*(r:ℝ)
theorem worstCaseBound_of_dcEnergyBound {ψ} (hψ) {G r} (hr) (hrq) (h : DCEnergyBound G r) :  -- DCWorstCaseWiring
  WorstCaseIncompleteSumBound ψ G (2*Real.exp 1*(G.card)*(r:ℝ))
```
*Proves:* `DCEnergyBound G r` is the TRUE prize hypothesis A_r ≤ Wick (q·E_r − |G|^{2r} ≤ q·(2r−1)‼·|G|^r), TRUE at prize unlike raw E_r ≤ Wick. PROVEN at r=1 (free) and r=2 (dyadic μ_{2^m} via exact E₂=3n²−3n at Sidon threshold); only r≥3 (specifically r≈ln q) open. Floor-reaching is FORMAL: `eta_sq_le_dcOptimized` gives M ≤ √(2e·n·ln q), wired to the δ* consumer by `worstCaseBound_of_dcEnergyBound`. The ONLY open input of the end-to-end conditional prize bound is A_r ≤ Wick at r≈ln q (= the BGK/Anomaly-Suppression inequality).
*Consume:* `import` the relevant module(s). To get the prize sup-norm: supply `DCEnergyBound G r` at r≥max(1,ln q) and apply `eta_sq_le_dcOptimized` (or `worstCaseBound_of_dcEnergyBound` for the δ* form). The hypothesis is discharged for free at r=1 (`dcEnergyBound_one`) and r=2 dyadic (`dcEnergyBound_two_rootsOfUnity`); r≥3 is the single open BGK input.
*Reproduce:* `scripts/pg-iterate.sh` on each of the five files.

**CharPMomentRecursion** — exact one-step additive-moment recursion E_{r+1} = n·E_r + cross_r + free ceiling E_{r+1} ≤ n²·E_r.
`ArkLib/Data/CodingTheory/ProximityGap/CharPMomentRecursion.lean` (fork/main) · namespace `ArkLib.ProximityGap.CharPMomentRecursion`
```lean
noncomputable def freq (G) (r) (d : F) : ℕ := ∑ v ∈ piFinset (fun _:Fin r => G), (if ∑ i, v i = d then 1 else 0)
theorem freq_succ (G) (r) (d) : freq G (r+1) d = ∑ s ∈ G, freq G r (d - s)
theorem rEnergy_eq_sum_freq_sq (G) (r) : rEnergy G r = ∑ d : F, freq G r d ^ 2
theorem autocorr_le_energy (G) (r) (δ : F) : autocorr G r δ ≤ rEnergy G r
theorem rEnergy_succ (G) (r) : rEnergy G (r+1) = G.card*rEnergy G r + ∑ s ∈ G, ∑ t ∈ G.erase s, autocorr G r (s-t)
theorem rEnergy_succ_le (G) (r) : rEnergy G (r+1) ≤ G.card^2 * rEnergy G r
```
*Proves:* exact recursion E_{r+1} = |G|·E_r + cross_r (off-diagonal autocorrelations), and the unconditional free ceiling E_{r+1} ≤ |G|²·E_r. Everything EXACT, char-p, any finite G, no Weil/sum-product/Lam–Leung. Honest scope: ceiling is the non-prize deep regime.
*Consume:* `import ArkLib.Data.CodingTheory.ProximityGap.CharPMomentRecursion`. `rEnergy_succ` is the exact ladder; `rEnergy_succ_le` is telescopeable (as CharPDeepMomentTail does). `rEnergy_eq_sum_freq_sq` bridges energy↔ℓ²(f_r); `autocorr_le_energy` discharges the off-diagonal bound.
*Reproduce:* `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/CharPMomentRecursion.lean`.

**CharPDeepMomentTail** — telescopes to closed forms E₀=1, E₁=|G|, E_r ≤ |G|^{2r}, and ‖η_b‖ ≤ q^{1/2r}|G| (HONESTLY off-prize, → trivial floor).
`ArkLib/Data/CodingTheory/ProximityGap/CharPDeepMomentTail.lean` (fork/main) · namespace `ArkLib.ProximityGap.CharPDeepMomentTail`
```lean
theorem rEnergy_zero (G) : rEnergy G 0 = 1
theorem rEnergy_one (G) : rEnergy G 1 = G.card
theorem rEnergy_le_pow (G) (r) : rEnergy G r ≤ G.card^(2*r)
theorem rEnergy_le_pow_sharp (G) (r) (hr : 1 ≤ r) : rEnergy G r ≤ G.card^(2*r-1)
theorem eta_pow2r_le_card_mul_energy {ψ} (hψ) (G) (r) (b) : ‖eta ψ G b‖^(2*r) ≤ (Fintype.card F)*rEnergy G r
theorem eta_pow2r_le {ψ} (hψ) (G) (r) (b) : ‖eta ψ G b‖^(2*r) ≤ (Fintype.card F)*(G.card:ℝ)^(2*r)
theorem eta_le_rpow {ψ} (hψ) (G) (r) (hr : 1 ≤ r) (b) :
  ‖eta ψ G b‖ ≤ (Fintype.card F)^(((2*r:ℕ):ℝ))⁻¹ * (G.card:ℝ)
```
*Proves:* unconditional 2r-th-root sup-norm ‖η_b‖ ≤ q^{1/(2r)}·|G| ∀b,r. HONESTLY off-prize: q^{1/(2r)} → 1, so this route only reaches the trivial |G|=n floor (no √-cancellation). Marks the trivial ceiling any prize attempt must escape.
*Consume:* `import ArkLib.Data.CodingTheory.ProximityGap.CharPDeepMomentTail`. `rEnergy_zero`/`rEnergy_one` are exact anchors; `eta_pow2r_le_card_mul_energy` discharges single-term ≤ q·E_r; `eta_le_rpow` marks the |G| floor that no prize bound may stay at.
*Reproduce:* `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/CharPDeepMomentTail.lean`.

**CoshMGFIdentity** — root-free, max-free MGF restatement of the prize core; floor-reaching is empirical (probe).
`Research/ProximityPrize/Frontier/CoshMGFIdentity.lean` (fork/main) · namespace `ProximityGap.Frontier.CoshMGFIdentity`
```lean
theorem coshMGF_eq_evenMoment_tsum {ψ} (hψ) (G) (y : ℝ) :
  (∑ b, Real.cosh (‖eta ψ G b‖*y)) = ∑' r, ((Fintype.card F)*rEnergy G r)*y^(2*r)/((2*r).factorial)
theorem cosh_supNorm_le_coshMGF (G) (y) (b₀) : Real.cosh (‖eta ψ G b₀‖*y) ≤ ∑ b, Real.cosh (‖eta ψ G b‖*y)
theorem cosh_period_le_evenMoment_tsum {ψ} (hψ) (G) (y) (b₀) :
  Real.cosh (‖eta ψ G b₀‖*y) ≤ ∑' r, ((Fintype.card F)*rEnergy G r)*y^(2*r)/((2*r).factorial)
```
*Proves:* exact ∑_b cosh(‖η_b‖y) = ∑_r (q·E_r/(2r)!)·y^{2r}, so ‖η_{b₀}‖ ≤ arcosh(RHS(y))/y, optimisable in y. Floor-reaching (min_y arcosh(p·I₀(2y)^{n/2})/y beats √(2n log m) at n=8) is the EMPIRICAL probe claim — turning it into the prize constant needs the open saddle asymptotics of I₀(2y)^{n/2}.
*Consume:* `import Research.ProximityPrize.Frontier.CoshMGFIdentity`. `cosh_period_le_evenMoment_tsum hψ G y b₀` bounds a single period without √ or max. The y-optimisation/saddle asymptotics is the OPEN consumer.
*Reproduce:* `scripts/pg-iterate.sh Research/ProximityPrize/Frontier/CoshMGFIdentity.lean`. Floor-reaching: `python3 scripts/probes/probe_cosh_identity_mgf.py`.

---

### D. Incidence + census — over-determined far-line counts (p-independence)

**OverdetIncidenceMaxClosedForm** — exact closed form of the over-det far-line incidence MAX (D1).
`ArkLib/Data/CodingTheory/ProximityGap/OverdetIncidenceMaxClosedForm.lean` (fork/main) · namespace `ArkLib.ProximityGap.OverdetIncidence`
```lean
def overdetIncidenceMax (m : ℕ) : ℕ := 2*m^3 - 2*m^2 + 1     -- = n³/32 − n²/8 + 1 (n=4m), dir (n/2, n/2−1)
theorem overdetIncidenceMax_values : overdetIncidenceMax 2 = 9 ∧ … ∧ overdetIncidenceMax 10 = 1801
theorem overdetIncidenceMax_bulk (m) : 2*m^3 - 2*m^2 = 2*m^2*(m-1)
theorem overdetIncidenceMax_gt_budget {m} (hm : 2 ≤ m) : overdetIncidenceMax m > 4*m
```
*Proves:* I_max(n) = n³/32 − n²/8 + 1 at rate k=2, s=k+2, thin μ_n; `overdetIncidenceMax_gt_budget` (I_max > budget n=4m) is the arithmetic core of "binding s* is ALWAYS over-determined" ⟹ δ* is p-INDEPENDENT (decoupled from the open p-dependent BGK max). p-independence since disc(x^{2^μ}−1) = ±n^n is a power of 2.
*Consume:* `import ArkLib.Data.CodingTheory.ProximityGap.OverdetIncidenceMaxClosedForm`. `overdetIncidenceMax_gt_budget hm` discharges "binding witness s* is never the over-det boundary" for m≥2. `overdetIncidenceMax_values` certifies the empirical sequence. Does NOT close CORE (the s*(n,k) budget-crossing asymptotic stays open). Pure ℕ arithmetic, Mathlib.Tactic only.
*Reproduce:* `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/OverdetIncidenceMaxClosedForm.lean`. Data: `scripts/rust-pg` `pg <n> 2`.

**OverdetIncidenceUnionCount** — union-of-per-witness-singletons counting bridge ⟹ p-independent count (D2).
`Research/ProximityPrize/Frontier/OverdetIncidenceUnionCount.lean` (fork/main) · namespace `ProximityGap.Frontier.OverdetIncidenceUnionCount`
```lean
theorem card_filter_exists_subsingleton_le {F}[Fintype F][DecidableEq F]{σ}[DecidableEq σ]
  (T : Finset σ) (Q : σ → F → Prop) [...] (hsub : ∀ S ∈ T, {γ | Q S γ}.Subsingleton) :
  (univ.filter (fun γ => ∃ S ∈ T, Q S γ)).card ≤ T.card
theorem farIncidence_affine_le_witnesses {F}[Field F][Fintype F]{V}[Module F V]
  (T) (W : σ→Submodule F V) (a b : σ→V) (hfar : ∀ S ∈ T, b S ∉ W S) :
  (univ.filter (fun γ => ∃ S ∈ T, a S + γ•b S ∈ W S)).card ≤ T.card
theorem farIncidence_shape_le_bigWitnesses … (hcover) (hpin : …) :
  (incidence filter).card ≤ (univ.filter big).card        -- matches B1IncidenceBridge.farIncidence verbatim
```
*Proves:* the far-incidence count is the union of per-witness γ-sets; each far-witness set is a subsingleton (≤1 γ, from `_wf2NH`), so incidence ≤ #witnesses uniformly in F (no p-dependence). `farIncidence_shape_le_bigWitnesses` matches the deployed `B1IncidenceBridge.farIncidence`, reducing the open `WorstCaseFarIncidenceBounded` to the p-independent big-witness count.
*Consume:* `import Research.ProximityPrize.Frontier.OverdetIncidenceUnionCount`. Apply `farIncidence_affine_le_witnesses` with `hfar : ∀ S∈T, b S ∉ W S` to bound incidence by the witness count. For the deployed filter, discharge `hpin` via `_wf2NH.incidence_subsingleton_of_not_mem`. Does NOT close CORE (decay-vs-budget threshold separate).
*Reproduce:* `scripts/pg-iterate.sh Research/ProximityPrize/Frontier/OverdetIncidenceUnionCount.lean`.

**ConverseLamLeung2Power** — vanishing 2^a-root sums = antipodal (char-0) (D5).
`ArkLib/Data/CodingTheory/ProximityGap/ConverseLamLeung2Power.lean` (fork/main; deps `LamLeungTwoPow.lean`, `VanishingRootSumHeightGate.lean`) · namespace `ArkLib.ProximityGap.RouVanishingCount`
```lean
theorem lowHalf_powers_linearIndependent {a} (ha : 1 ≤ a) {ζ} (hζ : IsPrimitiveRoot ζ (2^a)) :
  LinearIndependent ℤ (fun j : Fin (2^(a-1)) => ζ^(j:ℕ))
def ExponentAntipodal (a) (S : Finset ℕ) : Prop := ∀ j < 2^(a-1), (j ∈ S ↔ j + 2^(a-1) ∈ S)
theorem zero_sum_imp_antipodal {a} (ha : 1 ≤ a) {ζ} (hζ : IsPrimitiveRoot ζ (2^a)) {S}
  (hS : S ⊆ range (2^a)) (hsum : ∑ i ∈ S, ζ^i = 0) : ExponentAntipodal a S
theorem noSpuriousVanishing_charZero_twoPower {m} {ζ} (hζ : IsPrimitiveRoot ζ (2^(m+1))) :
  NoSpuriousVanishing (Polynomial.nthRootsFinset (2^(m+1)) (1:F))
```
*Proves:* over a char-0 field, S ⊆ {0..2^a−1} has Σζⁱ = 0 IFF antipodal — the char-0 content of `NoSpuriousVanishing` for n=2^a (the input making over-det incidence p-independent and E_r(μ_n) ≤ (2r−1)‼·n^r hold in char 0). Open residual: char-p transfer at r≈ln q.
*Consume:* `import ArkLib.Data.CodingTheory.ProximityGap.ConverseLamLeung2Power`. `zero_sum_imp_antipodal` converts a vanishing 2^a-root-sum into antipodality; `noSpuriousVanishing_charZero_twoPower` discharges `NoSpuriousVanishing` in char 0. Char-0 ONLY — does NOT supply the prize-prime transfer.
*Reproduce:* `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/ConverseLamLeung2Power.lean`.

**wf3D4 monomial-worst orbit asymmetry** — only a monomial direction is a dilation eigenvector (n-uniform structural skeleton).
`Research/ProximityPrize/Frontier/_wf3D4_monomial_worst_orbit.lean` (fork/main; ArkLib.lean:1070) · namespace `ProximityGap.Frontier.wf3D4`
```lean
theorem monomial_dilated_line (μ) (b) (a : F[X]) (γ) : (a + C γ*X^b).comp (C μ*X) = a.comp (C μ*X) + C (γ*μ^b)*X^b
theorem eigen_coeff (μ c) (f) (h : f.comp (C μ*X) = C c*f) (j) (hj : f.coeff j ≠ 0) : μ^j = c
theorem orbit_closed_dir_forces_monomial (μ c) (f) (h : f.comp (C μ*X) = C c*f) (hdistinct : …) : f.support.card ≤ 1
theorem multiterm_not_eigen (μ) (f) (hmulti : 2 ≤ f.support.card) (hdistinct : …) : ¬ ∃ c, f.comp (C μ*X) = C c*f
def badSet {V}[AddCommGroup V][Module F V] (W : Submodule F V) (a b : V) : Set F := {γ | a + γ•b ∈ W}
theorem badSet_subsingleton_far {V}{W}{a b} (hb : b ∉ W) : (badSet W a b).Subsingleton
theorem badSet_closed_under_reparam (W) (a b) (r : F→F) (hr : …) : ∀ γ ∈ badSet W a b, r γ ∈ badSet W a b
def MonomialIsWorstFarDirection (I) (IsFar IsMonomialDir) : Prop      -- named open quantitative core
def TwoTermNotBetterThanMonomial (I) (IsFar IsMonomialDir) : Prop     -- named open 2-term comparison
```
*Proves:* only a monomial f=X^b is a dilation eigenvector, so only its bad-γ set carries the ⟨μ^{b−a}⟩-orbit alignment; multi-term dirs lose it AND pay the subsingleton over-det bound. Anchor (exact, p-indep): n=16,k=4,r=10 worst monomial a=10,b=4 has I=89 orbit-closed; every 2-term dir I≤89, no nontrivial orbit. Residual I(2-term)≤I(monomial) left as named open Props.
*Consume:* `import Research.ProximityPrize.Frontier._wf3D4_monomial_worst_orbit`. `multiterm_not_eigen` discharges "no scalar c with f∘D_μ=c·f"; `badSet_subsingleton_far hb` bounds a far witness's γ-set by ≤1; `badSet_closed_under_reparam` (r = ·*μ^{b−a}) asserts monomial orbit-closure. The two open Props are the obligations a δ* worst-direction proof must discharge.
*Reproduce:* `scripts/pg-iterate.sh Research/ProximityPrize/Frontier/_wf3D4_monomial_worst_orbit.lean`. Anchor: `probe_wf3D4_orbit_asymmetry.py`.

**wf3D5 Lam-Leung cyclotomic orbit backbone** — I(n) = 1 + (n/2)·O(n) free-action divisibility atom.
`Research/ProximityPrize/Frontier/_wf3D5_lamleung_orbit_backbone.lean` (fork/main; ArkLib.lean:1071) · namespace `ProximityGap.Frontier.wf3D5`
```lean
theorem smul_eq_self_iff_one (g : H) (u : H) : g * u = u ↔ g = 1
theorem orbit_card_eq_card (G : Subgroup H) [Fintype G] (u) [Fintype (orbit G u)] : card (orbit G u) = card G
theorem card_dvd_of_free_orbits (G : Subgroup H) [Fintype G] {β} [MulAction G β] [Fintype β] …
  (hfree : ∀ ω : orbitRel.Quotient G β, card ω.orbit = card G) : card G ∣ card β
```
*Proves:* the nonzero bad-γ set is a union of full ⟨ζ^{a−b}⟩=μ_{n/2}-orbits (size n/2), so (n/2) ∣ (I(n)−1) STRUCTURALLY and p-independently. Exact: I(16)=89=1+8·11, I(24)=217=1+12·18, I(32)=529=1+16·33 (identical across primes). Residual open: closed form for O(n).
*Consume:* `import Research.ProximityPrize.Frontier._wf3D5_lamleung_orbit_backbone`. Instantiate `card_dvd_of_free_orbits` with G=μ_{n/2}, β=nonzero-bad-scalar set, discharge `hfree` via `orbit_card_eq_card`, get (n/2) ∣ #bad. Feeds wf3D6. `smul_eq_self_iff_one`/`orbit_card_eq_card` are reusable free-action lemmas (Mathlib lacks the packaged form).
*Reproduce:* `scripts/pg-iterate.sh Research/ProximityPrize/Frontier/_wf3D5_lamleung_orbit_backbone.lean`. Anchor: `scripts/probes/probe_farline_incidence_exact.py`.

**wf3D6 over-det Johnson-lock orbit-budget arithmetic** — crossing I≤n governed by O≤2 (companion to D4/D5).
`Research/ProximityPrize/Frontier/_wf3D6_overdet_johnson_lock.lean` (fork/main; ArkLib.lean:1072) · namespace `ProximityGap.Frontier.wf3D6`
```lean
theorem incidence_le_budget_iff_orbits_le_two (n half O z) (hn : n = 2*half) (hz : z ≤ 1) (hpos : 1 ≤ half) :
  z + half*O ≤ n ↔ (half*O ≤ n - z)
theorem one_orbit_within_budget (n half O z) (hn) (hz) (hpos) (hO : O ≤ 1) : z + half*O ≤ n
theorem three_orbits_overflow (n half O z) (hn) (hpos) (hO : 3 ≤ O) : n < z + half*O
```
*Proves:* with I = z + (n/2)·O (z∈{0,1}) and budget n, the crossing I≤n ⟺ O≤2; ≤2 orbits within budget, ≥3 overflow. Since O(c)=RS list size collapses to ≤2 at Johnson, pins c*=k−1, s*=n/2−1, δ*=1/2+1/n → 1/2 (Johnson) with NO climb — over-det far-line is Johnson-locked, no second horn.
*Consume:* `import Research.ProximityPrize.Frontier._wf3D6_overdet_johnson_lock`. Pure-ℕ; feed half=n/2, O = wf3D5 orbit count, z = γ=0 flag. `three_orbits_overflow`/`one_orbit_within_budget` give the two regimes; `incidence_le_budget_iff_orbits_le_two` is the exact iff. The O(c)=list-size collapse at Johnson is the documented non-Lean structural input.
*Reproduce:* `scripts/pg-iterate.sh Research/ProximityPrize/Frontier/_wf3D6_overdet_johnson_lock.lean` (axioms: propext only, pure-ℕ omega). Data: `scripts/rust-pg/src/main.rs` (n≤28) + `src/bin/crossdeep.rs` (n=32).

**DecouplingCrossingDepthRateConstant** — corrects §6 2nd-horn: crossing depth c* is CONSTANT in rate k, not Θ(n).
`Research/ProximityPrize/Frontier/DecouplingCrossingDepthRateConstant.lean` (fork/main; *NOT in working tree — `git show fork/main:<path>`*) · namespace `ArkLib.ProximityGap.DecouplingCrossingDepthRateConstant`
```lean
def bindingWitnessSize (k c : ℕ) : ℕ := k + c
def crossingDepth (k c : ℕ) : ℕ := bindingWitnessSize k c - k
theorem crossingDepth_rate_constant (k c) : crossingDepth k c = c
theorem crossingDepth_rate_flat (k₁ k₂ c) : crossingDepth k₁ c = crossingDepth k₂ c
def crossingDistanceNumer (n k c : ℕ) : ℕ := n - bindingWitnessSize k c
theorem crossingDistanceNumer_eq (n k c) (h : k + c ≤ n) : crossingDistanceNumer n k c = n - k - c
theorem capacity_defect_eq (n k c) (h : k + c ≤ n) : (n - k) - crossingDistanceNumer n k c = c
theorem crossingDepth_pos_all_rates (k c) (hc : 1 ≤ c) : 1 ≤ crossingDepth k c
theorem crossingDepth_no_collapse (k c) : crossingDepth (k+1) c = crossingDepth k c
theorem prior_rate_law_refuted_at_n20_k9 : (10-1:ℕ)-9 = 0 ∧ crossingDepth 9 4 = 4 ∧ crossingDepth 9 4 ≠ (10-1:ℕ)-9
```
*Proves:* the prior Θ(n) rate-law is REFUTED — s*(n,k)=k+c*(n), so c* = s*−k is CONSTANT in k (n=20: c*=4 ∀k∈{5..9}). Formalizes the capacity-defect law δ* = (1−ρ) − c/n (fixed Θ(1/n) below KKH26 edge at every rate), bounded-positive c* never collapsing to 0. The far-line/numeric face is strictly OFF the BGK wall at every accessible rate; no second horn. NOT a CORE closure.
*Consume:* `import Research.ProximityPrize.Frontier.DecouplingCrossingDepthRateConstant` (minimal-import, pure-ℕ/omega). `crossingDepth_rate_constant`/`_rate_flat` for rate-flatness; `crossingDistanceNumer_eq` then `capacity_defect_eq` for the δ*=(1−ρ)−c/n form; `crossingDepth_pos_all_rates` (hc : 1 ≤ c) for "no BGK re-coupling at any rate"; `prior_rate_law_refuted_at_n20_k9` is the citable refutation. s* values come from the rust probe, not re-derived in Lean.
*Reproduce:* `scripts/pg-iterate.sh` (after `git show fork/main:<path>` to obtain it). Engine: `scripts/rust-pg/src/bin/secondhorn.rs`, `cargo run --release --manifest-path scripts/rust-pg/Cargo.toml --bin secondhorn -- <n> <k> [mult=4]`. Python: `scripts/probes/probe_407_decoupling_secondhorn_boundary.py`.

**UncertaintyTwoPowerSparseFloor** — dyadic 2^s sparse-zero floor (2^s−1)·n/2^s; floor RISES with sparsity.
`Research/ProximityPrize/Frontier/UncertaintyTwoPowerSparseFloor.lean` (fork/main; ArkLib.lean:977, commit `f6ef429c3`) · namespace `ProximityGap.UncertaintyTwoPowerSparseFloor`
```lean
theorem card_filter_dvd_range_pow (μ s) (hsμ : s ≤ μ) : ((range (2^μ)).filter (fun j => 2^s ∣ j)).card = 2^(μ-s)
theorem primRoot_pow_eq_one_iff_dvd {μ s} (hsμ) {ζ} (hζ : IsPrimitiveRoot ζ (2^μ)) (j) : (ζ^j)^(2^μ/2^s) = 1 ↔ 2^s ∣ j
theorem card_sparse_root_eq {μ s} (hsμ) {ζ} (hζ) : ((range (2^μ)).filter (fun j => (ζ^j)^(2^μ/2^s) ≠ 1)).card = 2^μ - 2^(μ-s)
theorem sparse_floor_closed_form {μ s} (hsμ) {ζ} (hζ) : (…).card = (2^s - 1)*2^(μ-s)
theorem sparse_floor_strict_mono {μ s s'} (hss' : s < s') (hs'μ : s' ≤ μ) : (2^s-1)*2^(μ-s) < (2^s'-1)*2^(μ-s')
```
*Proves:* for each order 1≤s<μ the sparse witness has t=2^s nonzero terms and exactly (2^s−1)·n/2^s roots in μ_n; subsumes the binomial n/2 (s=1) and trinomial floors. The floor RISES toward n as t grows, so NO uncertainty/sparse-poly route gives a sub-(1−1/t)·n upper bound on s* for n=2^μ. Localizes the open core AWAY from s* (the prize is the LIST size, not s*).
*Consume:* `import Research.ProximityPrize.Frontier.UncertaintyTwoPowerSparseFloor`. `sparse_floor_closed_form` for the exact root count; `primRoot_pow_eq_one_iff_dvd` is the reusable order-2^s factor-through; `sparse_floor_strict_mono` refutes any candidate sub-(1−1/t)n single-witness bound.
*Reproduce:* `scripts/pg-iterate.sh Research/ProximityPrize/Frontier/UncertaintyTwoPowerSparseFloor.lean`.

**CrossCellShkredovBound** — exact crossCell = N₀(G,r)−2·N₀(H,r), char-0 crossCell(n,4)=3n²/2, BCHKS-1.12-as-written FALSE at prize depth.
`ArkLib/Data/CodingTheory/ProximityGap/CrossCellShkredovBound.lean` (fork/main; ArkLib.lean:726, commits `eef47ce41`/`235dac66d`/`5a8d7fd42`) · namespace `ArkLib.ProximityGap.CrossCellShkredovBound`
```lean
noncomputable def crossCell (H : Finset F) (ζ : F) (r : ℕ) : ℕ := N0 (H ∪ H.image (ζ*·)) r - 2*N0 H r
theorem crossCell_add_two_diag (hζ : ζ≠0) (hdisj) (hr : 1≤r) : 2*N0 H r + crossCell H ζ r = N0 (H ∪ H.image (ζ*·)) r
theorem crossCell_eq_zero_of_r_eq_one (hζ) (hdisj) (hr1) : crossCell H ζ 1 = 0
def CrossCellAbsoluteBound (H) (ζ) : Prop := ∀ r ≥ 2, (crossCell H ζ r : ℚ)*q ≤ (2^r)*(H.card)^r
theorem N0_gap_of_absoluteBound (hζ) (hdisj) (hbound : CrossCellAbsoluteBound H ζ) (hr : 2≤r) :
  (N0 G r : ℚ)*q ≤ (2*N0 H r)*q + (2^r)*(H.card)^r
```
*Proves:* exact dyadic-descent decomposition crossCell = N₀(G,r)−2·N₀(H,r) (G=μ_n=H∪ζH, H=μ_{n/2}), with r=1 vanishing. Probe pins crossCell(n,4)=3n²/2 (= E(μ_n)−2E(μ_{n/2}), Lam-Leung readout), p-independent and super-random. KEY DISPROOF: `CrossCellAbsoluteBound` (BCHKS-1.12 as written) is FALSE at every prize depth (r=4 reads q ≤ (2/3)n², violated by 2¹²⁸; true only at r₀≫89). The genuine open object is the depth-correct char-0 vanishing-sums/Lam-Leung bound at r≈ln q.
*Consume:* `import ArkLib.Data.CodingTheory.ProximityGap.CrossCellShkredovBound`. `crossCell_add_two_diag` splits N₀(G,r); `N0_gap_of_absoluteBound` iterates down the 2-power tower. WARNING: do NOT treat `CrossCellAbsoluteBound` as the open wall pointwise — FALSE at feasible depth; only its asymptotic form is the real open core. crossCell(n,4)=3n²/2 is the char-0 sanity anchor.
*Reproduce:* `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/CrossCellShkredovBound.lean`. Probes: `python3 scripts/probes/probe_407_crosscell_absbound_false_at_prize.py`; `python3 scripts/probes/probe_407_crosscell_superrandom_pindep.py`.

**E2W4CyclotomicNonCollision + e2=0 census 4|w resonance** — K(n,w)=n/4−1 iff 4∣w; width-4 case formalized.
`ArkLib/Data/CodingTheory/ProximityGap/E2W4CyclotomicNonCollision.lean` (fork/main; ArkLib.lean:860, PR#433 `8989889e2`) · namespace `ArkLib.ProximityGap.E2W4CyclotomicNonCollision`. General-w resonance is PROBE-ONLY: `scripts/probes/probe_407_e2_census_general_k_resonance.py`, `…_n64_shallow.py`.
```lean
def Cd₀NonCollision (G : Finset F) : Prop :=
  ∀ t∈G, ∀ t'∈G, (t+t⁻¹)≠0 → (t'+t'⁻¹)≠0 → (t+t⁻¹)≠(t'+t'⁻¹) → ∀ u∈G, (t'+t'⁻¹) ≠ u*(t+t⁻¹)
theorem orbits_distinct_of_nonCollision {G} (hG : FinSubgroup G) (hNC : Cd₀NonCollision G) {t t'} … :
  ¬ (∃ u ∈ G, -(t'+t'⁻¹)⁻¹ = u * (-(t+t⁻¹)⁻¹))
theorem badScalar_orbits_distinct_of_nonCollision … :
  ¬ (∃ u ∈ G, -(e1 (quadT x' t'))⁻¹ = u * (-(e1 (quadT x t))⁻¹))   -- with badScalarSet_card_eq_orbit_mul ⇒ K=n/4−1
```
*Proves (probe):* the e2=0 census orbit count K(n,w)=n/4−1 EXACTLY iff 4∣w (a 4|w resonance), K≤1 within budget otherwise. Width-4 (w=4) is formalized axiom-clean: actual F_q dilation-orbit count = combinatorial model n/4−1, proven over ℂ (cos strictly-anti, not Kronecker) and good primes over F_p (bad primes = finite/small norm divisors). Thickness-invariant (vanishes for random domains).
*Consume:* `import ArkLib.Data.CodingTheory.ProximityGap.E2W4CyclotomicNonCollision`. `orbits_distinct_of_nonCollision` (granting `Cd₀NonCollision`, discharged over ℂ) gives distinct F_q orbits, then `badScalarSet_card_eq_orbit_mul` gives K=n/4−1. The general-w resonance is NOT Lean-formalized.
*Reproduce:* `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/E2W4CyclotomicNonCollision.lean` (8 #print axioms). Probes: `python3 scripts/probes/probe_407_e2_census_general_k_resonance.py`; `…_n64_shallow.py`. Commits `5a17bd3ee`, `f1d5de96e`, `74a54cdce`, `8989889e2`.

**γ-census worst-line closed form γ_worst(n,r=3)=n·C(n/4,2)+1** *(PROBE only)*.
`scripts/probes/probe_407_census_gamma_mechanism.py` (orbit mechanism, #orbits=C(n/4,2)) + `scripts/probes/probe_407_census_gamma_budget_n32.py` (budget margin) — fork/main.
*Proves:* the corrected CensusDomination object (#distinct-γ, since epsMCA≤#bad/p) on the worst far line has the exact p-independent closed form n·C(n/4,2)+1 (anchors 97/897/7681 at n=16/24/32), mechanism = n× μ_n coset multiplicity × C(n/4,2) cyclotomic-pair orbits + 1 (γ=0). Stays within KKH26 budget with asymptotically STABLE margin ~0.19 to n=64 — corroboration, NOT asymptotic closure.
*Consume:* numerics only. To Lean-formalize γ_worst, compose wf3D5's orbit divisibility with the C(n/4,2) pair count; the +1 is wf3D6's z≤1.
*Reproduce:* `python3 scripts/probes/probe_407_census_gamma_mechanism.py`; `python3 scripts/probes/probe_407_census_gamma_budget_n32.py`. Commits `681e3edbb`, `88032c70f`.

---

### E. Reduction + list — floor ⟺ explicit-RS list past Johnson

**MCADeltaStarListReduction + SuperCodeListBridge + B1IncidenceBridge** — exact in-regime reduction: proximity-gap floor ⟺ sub-Johnson explicit-RS single-word list (NO √-loss).
`ArkLib/Data/CodingTheory/ProximityGap/MCADeltaStarListReduction.lean` | `SuperCodeListBridge.lean` | `B1IncidenceBridge.lean` (all fork/main) · namespaces `ProximityGap.Ownership` / `ProximityGap.FarCosetExplosion` / `ProximityGap.WireB1ToIncidence`
```lean
theorem mcaBad_card_le_singleWordList (dom : Fin n ↪ F) {k a} (ha : 1 ≤ a) (hk : k < n) (hdom : ∀ i, dom i ≠ 0)
  {δ} (u₀) (haδ : (a:ℝ≥0) ≤ (1-δ)*Fintype.card (Fin n)) :
  (mcaBad (rsCode dom k) δ u₀ (fun i => (dom i)^k)).card
    ≤ ((univ.filter (fun Q => Q ∈ rsCode dom (k+1) ∧ a ≤ (agreeSet Q u₀).card)).card) * (n / a)
theorem mcaDeltaStar_ge_of_uniform_mcaBad (C) {δ} (hδ : δ ≤ 1) {εstar B}
  (hcard : ∀ u : WordStack F (Fin 2) (Fin n), ((mcaBad C δ (u 0) (u 1)).card : ℝ) ≤ B)
  (hε : ENNReal.ofReal (B/Fintype.card F) ≤ εstar) : δ ≤ mcaDeltaStar C εstar
theorem explainableScalars_card_le_superList (C : Submodule F (ι→F)) (δ) (u₀ u₁) (hu₁ : u₁ ∉ C) :  -- √-free bridge
  (explainableScalars C δ u₀ u₁).card ≤ (univ.filter (fun e => e ∈ (C ⊔ span F {u₁}) ∧
    ∃ S, (S.card:ℝ≥0) ≥ (1-δ)*Fintype.card ι ∧ ∀ i ∈ S, e i = u₀ i)).card
def WorstCaseFarIncidenceBounded (C) (δ) (B : ℕ) : Prop :=          -- the named open core (B1IncidenceBridge)
  ∀ u₀ u₁, FarFromCode C δ u₁ → farIncidence C δ u₀ u₁ ≤ B
theorem epsMCA_le_of_worstCaseFarIncidence … (hB : WorstCaseFarIncidenceBounded C δ B) (hfar : FarFromCode C δ u₁) :
  (#bad-γ : ℝ≥0∞) ≤ (B : ℝ≥0∞)
```
*Proves:* in the BChKS (a<q/(2n)) regime, the floor (epsMCA small for ALL far stacks) is bounded by — and at budget q·ε*=n EQUIVALENT to — the sub-Johnson worst-case single-word list size of explicit smooth RS, NO √-loss (the super-code bridge replaces the Johnson √ with a +1-dimension argument). This is why ONE list-decoding bound closes BOTH grand challenges; worst-case word pinned 2-sparse x^a+γx^b.
*Consume:* `import ArkLib.Data.CodingTheory.ProximityGap.MCADeltaStarListReduction`. To push δ* up: supply uniform B with `∀ u, (mcaBad C δ (u 0) (u 1)).card ≤ B` + `ENNReal.ofReal(B/|F|) ≤ ε*`, then `mcaDeltaStar_ge_of_uniform_mcaBad` gives `δ ≤ mcaDeltaStar C ε*`; discharge `hcard` via `mcaBad_card_le_singleWordList`. For the √-free far-line→super-code step, `import …SuperCodeListBridge` and apply `explainableScalars_card_le_superList`. Single remaining open obligation: `WorstCaseFarIncidenceBounded` (B1IncidenceBridge) = the BGK char-sum wall.
*Reproduce:* `scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/MCADeltaStarListReduction.lean` (after `scripts/pg-warm.sh`). In-file `#print axioms`. NOTE: files on fork/main, not claude-iid-push (`git show fork/main:<path>`).

**AUDIT-GUARD co-import integrity (MCAGSUniversalReduction)** — restores whole-library build; standing audit harness.
`ArkLib/Data/CodingTheory/ProximityGap/MCAGSUniversalReduction.lean` (fork/main) + `scripts/proximity_prize_cleanroom_audit.py` + `scripts/proximity_prize_cleanroom_targets.txt` · namespace `ProximityGap.MCAGS`
```lean
abbrev CapacityListCoveringBound (m : ℕ) : Prop := UniversalGSListMassBound m   -- now an ALIAS (was a duplicate decl)
theorem epsMCAgsPrizeUniversal_of_capacityListCovering (m) (h : CapacityListCoveringBound m) :
  epsMCAgsPrizeUniversalConjecture m := epsMCAgsPrizeUniversalConjecture_of_UniversalGSListMassBound m h
```
*Proves:* removes a duplicate `epsMCAgsPrizeUniversalConjecture` decl that made two modules un-co-importable and broke `lake build ArkLib`; `CapacityListCoveringBound` is now a definitional alias of the canonical `UniversalGSListMassBound`, delegating to the canonical proof. The audit script (ALLOWED_AXIOMS = {propext, Classical.choice, Quot.sound}) co-imports all prize-apex targets and FAILS on a duplicate decl, forbidden axiom, or residual/goal-equivalent hypothesis. Reduction is axiom-clean, open input named explicitly.
*Consume:* `import ArkLib.Data.CodingTheory.ProximityGap.MCAGSUniversalReduction`, supply `h : CapacityListCoveringBound m` (= `UniversalGSListMassBound m`, the open research input), apply `epsMCAgsPrizeUniversal_of_capacityListCovering m h` for the field-universal prize conjecture. Add new prize producers to `proximity_prize_cleanroom_targets.txt` (status `active`/`pending`) to keep them guarded.
*Reproduce:* `python3 scripts/proximity_prize_cleanroom_audit.py` (post-build, oleans built first via `scripts/pg-warm.sh`).

---

### F. Engines + probes — exact δ* / list-size measurement (NOT char-sum proxies)

**GPU/CUDA + Rust-pg far-line engine** — exact, p-independent over-det δ*, m*.
`scripts/rust-pg/src/main.rs` (git-tracked, fork/main); `scripts/rust-pg/cuda/{ladder_core.h,ladder.cu,ladder_cpu.cpp,run_sweep.sh,NEBIUS_RUNBOOK.md}` (UNTRACKED scratch — present on disk, volatile).
```rust
fn incidence(a,b,n,mu,mua,mub,k,p,s,invd) -> u64   // distinct γ s.t. xᵃ+γxᵇ is deg<k-explainable on s of μ_n; u64::MAX if saturated
fn main()  // `pg <n> <k>` sweeps s∈(k+2..n), prints s*=first s with maxI≤budget(=n) and δ*=(n−s*)/n
           // `pg n k a b` = single-dir I(s) decay; `pg n k curve` = full sweep
// cuda/ladder_core.h: Hash128 subset_member_hash(...) — interpolate deg<k codeword through k pts, count agreement, 128-bit coeff hash (early-exit); SHARED by CUDA + CPU twin
```
*Proves:* exact p-independent (prize-scale p~n⁴, p≡1 mod n, PROPER μ_n) over-det δ*. README+commit `b66b7f769`: δ* = 1/2 + (1/(2ρ)−1)/n at budget=n; VALIDATED δ*(μ_16,k=4)=9/16 (`pg 16 4` → s*=7, δ*=0.5625, argmax (10,4)). The far-line incidence is exact (no √-loss) and p-independent — why over-det δ* DECOUPLES from the open BGK max. CUDA ladder extends list-size L(word,t) to n=64,128.
*Consume:* `cd scripts/rust-pg && cargo build --release`; `./target/release/pg <n> <k>` for s*,δ* (cost ~2ⁿ, n≤28 feasible). GPU: scp `cuda/` to an H200, `nvcc -O3 -arch=sm_90 -o ladder ladder.cu`, MANDATORY self-test `./ladder 16 4 self` (must print MATCH) before trusting, then `./run_sweep.sh <n> <k> 8`. Use to calibrate any closed-form δ* conjecture against wall W1 before formalizing.
*Reproduce:* `cd /Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib/scripts/rust-pg && cargo build --release && ./target/release/pg 16 4` → s*=7, δ*=0.5625 (=9/16), argmax (10,4).

**listsize.rs — direct explicit-RS worst-window list size = 2 (dilation orbit, p-indep)**.
`scripts/rust-pg/src/bin/listsize.rs` (fork/main, commit `e728a7a2c`); note `docs/kb/listdecoding-dilation-orbit-law-CONFIRMED.md` (fork/main).
```rust
fn list_size(w, mu, k, p, t) -> usize   // # distinct deg<k codewords agreeing with w on ≥t points of μ_n (parallel k-subset interp + HashSet dedup)
fn big_prime(n) -> u64                   // smallest prime > n⁴ with n | p−1 (prize-scale proper μ_n ⊊ F_p*)
```
*Proves:* first DIRECT literal-codeword-count (not a proxy) of the worst-case list size of explicit smooth-domain RS in the window interior. Exact, p-independent: deep in the window L=2 CONSTANT (= μ_n dilation orbit), extremal word x^{n/2}; near capacity L spikes ~n²/2. PROVEN LOWER bound: μ_n acts on the list ⟹ worst list ⊇ one orbit = O(1). Floor ⟺ no codeword outside the dilation orbit = same BGK wall in clean list terms. BKR superpoly route closed in-regime (needs a subfield, impossible over prime F_p).
*Consume:* ground-truth list-size oracle — test any claimed worst-case word / δ* candidate before trusting a char-sum proxy. The proven L≥orbit feeds the floor statement; open upper half L≤orbit is the BGK wall. Pairs with `mcaBad_card_le_singleWordList`.
*Reproduce:* `git show fork/main:scripts/rust-pg/src/bin/listsize.rs`; from `scripts/rust-pg`: `cargo build --release --bin listsize && ./target/release/listsize <n> <k>` (cost ~C(n,k), n≤~32). Data table in `docs/kb/listdecoding-dilation-orbit-law-CONFIRMED.md`. Source on fork/main only.

**C8/Q1 Chai-Fan pencil bad-set empty through weight 4 at d=16/32 (n=64/128)** *(PROBE; corrects an earlier false refutation)*.
`scripts/probes/probe_444_q1_d32_cleanup.py` (fork/main, commit `de40196bf`); companion `scripts/probes/probe_444_step_deep.py`.
*Proves:* the Q1/Chai-Fan pencil (ePrint 2026/861) bad-set V_d^prim is exhaustively EMPTY through weight 4 at d=16 AND d=32 (prize scale); char-p apparent violations are mod-p pigeonhole noise (0/64 cross-prime survival), restoring self-similarity (*)_d past d=16. OVERTURNS the prior `probe_407_close_actionorbit_q1_dichotomy.py` "Q1 fails at d=32" verdict (was noise). HONESTY: the antipodal-free non-ℂ relation is a NECESSARY SURROGATE not literally the pencil bad-set (a char-p-only witness T={3,36,50,52} exists); "through weight 4" is a hard ceiling — higher-weight Lenstra surplus is open.
*Consume:* verified-empty input for the Q1/action-orbit pencil bad-count being O(1) at n=128; template for the correct cross-prime test distinguishing a structural integer point from mod-p noise. Do NOT re-cite the old "Q1 fails" verdict.
*Reproduce:* `git show fork/main:scripts/probes/probe_444_q1_d32_cleanup.py` then `python3 scripts/probes/probe_444_q1_d32_cleanup.py` (exact big-int MITM, no deps). fork/main only.

**Deep-hole classification + monomial-far-line-worst-at-binding** *(PROBE; companion Lean on fork/main)*.
`scripts/probes/probe_407_deephole_classification.py`, `…_concentration.py`, `probe_407_genericstack_vs_monomial_worst.py` (fork/main, commits `196c44557`, `4622b3267`); companion Lean `SumsetExtremalityReduction.lean` / `MonomialLineListBridge.lean` (fork/main).
*Proves:* (1) deep holes of explicit smooth RS over μ_n are EXACTLY the monomials x^j (finite ~n/4 family, covering radius n−k); x^{n/2}-family are concentration words, not deep holes. (2) At the binding radius (a≥6) the monomial far-line pins #bad=1 while every generic/structured far stack gives EXACTLY 0 — so restricting the whole analysis to monomial directions does NOT under-count the true B=max over all far stacks. Both validate the prize reduces to the monomial char-sum (BGK/Paley wall), not a larger generic-stack object. HONESTY: engine-evidence supporting but not PROVING the monomial restriction.
*Consume:* use the classification to justify reducing the worst-case sup to the finite monomial family (import companion `MonomialLineListBridge.lean`/`SumsetExtremalityReduction.lean` for the proven monomial-extremality half: bad scalars of X^{rm}+γX^{(r−1)m} = exactly C(s,r)). Use the genericstack probe as empirical discharge of "is the worst stack a monomial?" feeding `WorstCaseFarIncidenceBounded`. Do NOT treat either as a closure.
*Reproduce:* `python3 scripts/probes/probe_407_deephole_classification.py` (needs sympy); `…_concentration.py` (sympy); `python3 scripts/probes/probe_407_genericstack_vs_monomial_worst.py` (pure Python, exact). fork/main only.

**True-core budget-conflation CORRECTION** *(PROBE; DISPROOF-LOG entry, not a closure)*.
`scripts/probes/probe_407_truecore_budget_conflation.py` (fork/main, commit `d5165ebfd`). Canonical Lean object: `OpenCoreConditionalPin.lean` (`WorstCaseIncidenceBounded`).
*Proves (rule-4 correction):* the prior "first floor-consistent signal" (ratio #bad/budget ~0.26) was a JOINT artifact of (1) BUDGET CONFLATION — the per-band census budget ~n²/2 sums to 3^{n/2} (exponential), not q·ε*~n, so normalizing a Θ(n²) count by a Θ(n²) census gives flat 0.26 by construction; and (2) an UNDERCOUNTING engine dropping collinear-but-NOROOT subsets (n=8 line(4,2): published 5 vs correct 17). Corrected collinearity-determinant engine gives #bad = 17,232,2320,~20224 at n=8,16,32,64 = SUPER-LINEAR — Johnson-side, NOT floor. Honest caveat: a=3 reads δ~1, OUTSIDE the prize window.
*Consume:* read as a DISPROOF-LOG correction — do NOT cite the 0.26 "canonical floor signal". When measuring canonical #bad, use the collinearity-determinant engine (`nbad_correct`), normalize by B=⌊q·ε*⌋~n NOT the per-band census. The true open object is `WorstCaseIncidenceBounded` at the WINDOW radius δ* ∈ (1−√ρ, 1−ρ−Θ(1/log n)) — still open/unmeasured.
*Reproduce:* `git show d5165ebfd:scripts/probes/probe_407_truecore_budget_conflation.py > /tmp/tc.py && python3 /tmp/tc.py` (the file is also present at `scripts/probes/probe_407_truecore_budget_conflation.py` on fork/main).

---

### NOT-LOCATED (flagged honestly — do NOT cite as landed)

**N9 over-det Betti point-count |V_4|=48 (codim-2 over-det subgroup count)** — *status: NOT-LOCATED.*
The claimed result (|V_4| = #{x ∈ μ_8⁴ : Σx=0 AND Σx²=0} = 48, identical at q=73/193/521, ⟹ N9 Deligne/Weil-II lever vacuous over the subgroup) appears ONLY in the issue #444 §7 body. I searched fork/main, claude-iid-push, claude-cliff-confinement, and the working tree: **no committed Lean file or probe computes this specific two-constraint |V_4|=48 cross-prime number.** The committed Betti probes `scripts/probes/probe_betti_independent.py` (`primitive_betti_general_closed_form(d,nvar) = ((d−1)^nvar + (−1)^nvar(d−1))/d`) and `probe_fermat_betti.py` compute only the SINGLE-constraint (codim-1) Betti closed form and the GLT Fermat-curve error model — NOT the codim-2 V_4. Treat as UNVERIFIED-claimed.
*To verify:* write an exact-arithmetic enumeration — pick p∈{73,193,521} (all ≡1 mod 8), build μ_8=⟨g^{(p−1)/8}⟩, brute-force count (x₁,x₂,x₃,x₄)∈μ_8⁴ with Σxᵢ≡0 and Σxᵢ²≡0, confirm =48 identical across the three primes and the "2 μ_4-cosets × 4! orderings" decomposition. The codim-1 analogue `primitive_betti_general_closed_form` can be adapted.
*Reproduce:* n/a — no committed reproduce command. Closest existing: `python3 scripts/probes/probe_betti_independent.py` (codim-1, not V_4).