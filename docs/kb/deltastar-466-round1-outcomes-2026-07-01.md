# #466 Round 1 — outcomes (2026-07-01)

Executes `deltastar-466-research-plan-round1-2026-07-01.md` end-to-end. Two sessions ran the
round concurrently on this checkout (this note is the merged record): session A ran lanes
L1/L2 + probes P1–P6 + the gates; session B ran Tier-1 items 5 and 3 independently
(`_BGKEffectiveHalfPlateau.lean`, `deltastar-466-bgk-effective-half-plateau-2026-07-01.md`).
Where the two overlap (attack #5) the kills are INDEPENDENT and complementary — the
double-refereed standard is met inside a single round.

## L — the §12 phantom bricks are RE-LANDED (both, axiom-clean, real build)

- **L1 `LineListMCAWeld.lean`** (root, canonical): `mcaDeltaStar_ge_of_farLineListBudgeted`
  is now a THEOREM on main. The re-derivation is *stronger* than the #464 thread's claimed
  shape, on three axes:
  1. **Witness farness is free** (`no_direction_codeword_on_witness_of_mcaEvent`): badness
     with witness `S` forbids ANY codeword from agreeing with the direction on `S` — the
     `¬pairJointAgreesOn` clause supplies the farness the thread assumed. Corollary
     (`mcaEvent_false_of_direction_mem`): **aligned directions have zero bad scalars** —
     the maximal line lists of aligned lines are harmless.
  2. **Direction-shift invariance** (`mcaEvent_direction_sub_codeword_iff`): badness is a
     coset invariant of the direction. With the **coset dichotomy**
     (`farFromCode_of_forall_coset_supportEligible`), every stack reduces to either a far
     direction or a large-zero (≥ a zero coordinates) representative — so the weld's
     residual branch is EXACTLY the line-list stack's named low-profile obligation, not
     the cruder "some coordinate vanishes" branch.
  3. The far restriction is FORCED as a theorem: `aligned_line_lambda_ge_q` (Λ ≥ q on
     aligned lines) + `not_uniform_lineListBudgeted_of_lt_card` (no uniform all-lines
     budget < q exists). Round-1's independent derivation (generic
     `explainableScalars` chain + the constant-patch refuter) is preserved at
     `Frontier/LineListMCAWeldRound1.lean` (namespace `…​.Round1`).
- **L2 `MomentExponentThreshold.lean`** (root): `θ(r,β) = (β+r−1)/(2r)`; `1/2 < θ` always
  (`half_lt_momentExponent`); excess EXACTLY `(β−1)/(2r)` (`momentExponent_sub_half`);
  non-trivial ⟺ `r > β−1`; **the one-rung window** (`nontrivial_le_crossover_iff_eq`):
  for integer depths, non-trivial ∧ pre-DC-crossover ⟺ `r = β`; anchors `θ(3,4)=1`,
  `θ(4,4)=7/8`, `θ(89,4)=46/89`.

## P — probe verdicts (all six DECIDED)

- **P1 anti-resonance (Chapman–Mudgal shape): REFUTED (b-blind).** Worst-coset resonance
  statistics (multiplicative order, Ramanujan-sum means c_q for q ≤ 32, gcd structure,
  Diophantine proximity, QR fraction) are indistinguishable from a random coset across all
  primes/sizes (percentiles ~0.13–0.999 scattered, |corr| ≤ 0.08); the dilation symmetry
  makes the statistic family b-blind, as the kill-branch predicted.
- **P2 non-backtracking/Ihara–Bass: REFUTED (deterministic monotone relabeling).** The NB
  spectrum of `Cay(F_p, μ_n)` is verified to machine precision to be the Ihara–Bass image
  of the adjacency data; the NB radius is the monotone image of M itself (argmax_b
  preserved; `ρ_NB/√q ≈ 2.4` vs Ramanujan 1). Joins the door-(iv) closures.
- **P3 Kravchuk moment-interlacing: REFUTED (no in-window bound).** The literal
  largest-root reading `SCL_A → 1/2 + √(ρ(1−ρ))` is WEAKER than Johnson at every prize
  rate; the "excess" reading `SCL_B = √(ρ(1−ρ))` lands between capacity and Johnson but is
  direction-INVALID (interlacing bounds max agreement from BELOW; exact countermodel with
  matching first-k moments and max agreement = m; the Binomial(m,1/2) premise has no
  nontrivial MDS instance).
- **P4 Hankel/Jacobi turnover: DATA LANDED; the seam is DAMAGED but not closed.**
  Measured: turnover `k* ≈ (0.60–0.72)·ln(p/n)` (consistent with form-D core ⟺
  `k* = O(log p)`); real ensembles indistinguishable from matched iid-Gaussian controls
  (independence localization re-confirmed in b_k coordinates); spacing law `b_j² − b_{j−1}²
  ≤ (1.014)·n` holds on ALL instances (a new clean empirical law); structured primes
  (Fermat/high-v₂) visible in `b₃,b₄` at z ≈ 285–1215 where matched raw moments see z ≈ 5.5
  — recurrence coefficients DO carry amplified structure signal. BUT the per-prime noise
  floor swamps `q_j` beyond j ≈ 4–5 (gen1/gen2 same-β divergence), so **no O(1)-window
  Hankel functional pins k\* per-prime** — the early-warning hope in its naive form is
  dead; what survives is the b₃/b₄ structured-prime sensitivity and the spacing law as
  constraints any future b_k-native inequality must respect.
- **P5 windowed SumsetExtremal: REFUTED at n=16 (pending §"replication" caveat).** At
  n=8 (two generic primes ≥ n⁴): exact TIES between best spread and best monomial at all
  window levels — weak extremality holds. At n=16, k=4, q=65537: **spread directions
  strictly beat every monomial in-window** at a=5 (4277 vs 4267) and a=7 (14 vs 9,
  brute-verified witnesses `sp2_7_13_c1`, `sp2_4_8_c27628`). Caveat being closed in-round:
  65537 is the Fermat prime (v₂(p−1)=16, maximally structured); replication at generic
  primes 65617/65633 [RESULT FOLDED IN BELOW — see the addendum at the end of this note].
- **P6 di Benedetto effective-1/2 push (= Tier-1 item 5, "attack #5"): REFUTED, twice
  independently.**
  - *Session A (`probe_466_dibenedetto_push.py`, exact-rational exponent calculus over the
    full parameterized 2003.06165 proof shape; self-test reproduces `1−31/2880` and the
    `β = 191/40` triviality boundary exactly):* the paper's arities (3,3,2) are OPTIMAL in
    the sound multilinear family at proven inputs (nothing in the sweep beats `1−31/2880`
    at β=4); under UNATTAINABLY perfect char-0 energies (`t_m = m` for all m) the family
    is dominated by the 1-round+bilinear chain, whose exponent is **EXACTLY
    `momentExponent(s,β)`** — the BG chain with perfect inputs IS the pure moment ladder
    (machine-checked identity at s = 4…89). Reaching θ = 1/2 requires trilinear prefactor
    κ → 0 or residual coefficients c → 1/2, i.e. a p-power-free multilinear bound — which
    IS the open √-cancellation. Circularity quantified; the multilinear rounds only trade
    unavailable deep energies for available shallow ones, at the plateau's cost.
  - *Session B (`_BGKEffectiveHalfPlateau.lean`, axiom-clean):* the iterated-BGK explicit
    corpus (Shkredov 1705.09703 Cor. 16 per Kowalski's exposition): at β=4 the explicit
    n-saving is `1/16384` (8192× short of 1/2), the p-saving `1/65536` vs the in-tree
    gate's required `ν ≥ 1/8`; the prize scale sits `2^{738}` below the Cor.-16
    applicability floor; `1/2^{k+2} < 1/2` for EVERY depth k
    (`half_unreachable_at_any_depth`); the trilinear ceiling `1/24` dominates iteration by
    > 682×.
  - *A-priori kill (standing):* `deltaStar_determination_all_or_nothing` makes any fixed
    power-saving θ > 1/2 irrelevant to δ\* regardless.
  **Tier-1 item 5 is CLOSED.**
- **TPS boundary (essay §2.5): CONFIRMED** (`probe_466_tps_boundary.py`): with the most
  sieve-optimistic bookkeeping, `r_cross = 4/5/6` at `β = 4/5/6`, stable over
  `n = 2^20…2^40` — the typical-prime sieve closes exactly the fixed-depth regime
  (`r ≈ β`) and no more; now THREE independent methods (DC-crossover, moment-exponent
  threshold, typical-prime sieve) place the unconditional boundary at `r ≈ β`.

## E — essay proposals: status after the refute pass

- **γ₂-degeneration: PROVEN (gate landed).** `_GammaTwoDegenerationGate.lean`: on
  exchangeable flat-covariance families every second-order metric is discrete ⟹ chaining
  = union bound = form (A). Chaining is the wall's statement, not a route around it.
- **Vertical MSS: DEAD (gate landed).** `_VerticalMSSGate.lean`: no interlacing mechanism
  over the prime index + the averaged-moment ∃-guarantee is exactly the (bad) mean — kills
  every future "average the char-poly/spectrum over p" proposal in one stroke.
- **CMK (Christoffel–Markov–Krein edge-crowding): OPEN, survives round 1** — the one new
  machinery not yet refuted. P4's data supplies its ingredients (Hermite-consistent bulk
  to j ≈ 4–5, spacing law, near-edge crowding measurable). Next round: attempt the
  abstract moment-problem theorem (equal atoms + Parseval + `K^r`-Wick-to-depth-`2log q`
  ⟹ `M² ≤ C(K)·n·log q`), or refute it by an explicit measure. The composition CMK ∘ TPS
  remains the round's one genuinely new closure shape.
- **SST (sparse-section transference): OPEN, untested** — needs the dual-minima probe;
  carried to round 2. The support-orbit compression question (dilation action on
  relation-supports — never consumed by any lane) stands.
- **TPS beyond r ≈ β:** named as the divisor-equidistribution problem; carried as prose.

## Fold-back state

Survivor list after round 1 (replaces dossier §6 Tier-1): ① windowed SumsetExtremal —
**see P5/replication** (if the generic-prime replication confirms: the guard-cell
catalogue route DIES and the conjecture must be re-guarded or abandoned); ② line-list
low-profile obligations (UNCHANGED — now the weld consuming them is real); ③ Hankel seam
NARROWED (b₃/b₄ structure sensitivity + spacing law; naive early-warning dead); ④
uniform-in-μ floor-bad (untouched this round); ⑤ ~~di Benedetto effective-1/2~~ CLOSED;
NEW ⑥ CMK moment-problem rigidity (+ CMK∘TPS composition); NEW ⑦ SST dual-minima probe.

## ADDENDUM — P5 generic-prime replication (filled at round close)

See `deltastar-466-p5-replication-2026-07-01.md` (written when the 65617/65633 runs
complete; the P5 verdict above is final only jointly with it).
