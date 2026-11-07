# The Proximity Prize: where the wall is, why it stands, and the cracks worth hitting

*A working essay for #444 — primary-synthesis draft (BGK/Paley, history, comparable quantities, the
live lead, the future). The 100 code-insights and the attack verdicts are merged from the parallel
research workflow. Honesty contract throughout: nothing called proven that isn't; the core is the
recognized-open thin-subgroup √-cancellation wall.*

## I. What the prize actually is, stripped to one inequality

Two grand challenges — Grand-MCA (mutual correlated agreement) and Grand-list-decoding — are, for
explicit smooth-domain Reed–Solomon codes, **one wall with two names** (`LDLeMCANoGo`: `δ*_LD ≥
δ*_MCA`, so list-decoding is the *weaker* challenge; pinning MCA pins both). The governing law is an
exact in-tree identity:

> `δ* = sup{ δ : I(δ) ≤ q·ε* }`,  `I(δ) = max_{u₀,u₁} #{γ : u₀ + γ·u₁ is δ-close to RS[k]}`.

Dilation symmetry forces the extremal `(u₀,u₁)` to be **monomial** directions `(X^a, X^b)`, and the
whole thing collapses, across ~20 provably-equivalent faces, onto a single analytic quantity:

> **`M(n) = max_{b≢0} |Σ_{x∈μ_n} e_p(b x)| ≤ C·√(n·log m)`**, `C = O(1)`,

for a **thin** dyadic multiplicative subgroup `μ_n ⊂ F_p*`, `n = 2^μ`, `p ≡ 1 (mod n)`, `q = p ≈ n^β`,
`β ≈ 4–5`, `ε* = 2⁻¹²⁸`, budget `q·ε* ≈ n`, `m = (p−1)/n = 2¹²⁸`. This is the sup-norm of a thin
incomplete Gauss sum / Gauss period; equivalently the second eigenvalue `λ₂(Cay(F_p, μ_n))` of the
**generalized Paley graph**. The conjecture says the periods are sub-Gaussian: their max over `m`
cosets is at most `√(log m)` times the RMS `√n`.

Everything that matters about the prize is in three numbers: the **target** `√(n log m)`, the **proven
floor** `M ≥ √n` (Parseval; the graph is *not* Ramanujan, `M > 2√n`), and the **state of the art**
`M ≤ n^{1−o(1)}` (BGK). The prize is the gap between SOTA `n^{0.989…}` and target `n^{0.5}` — a full
half-power — at the single hardest point `β ≈ 4` where every known power-saving vanishes.

## II. BGK and Paley, in depth — why the half-power is open

**BGK (Bourgain–Glibichuk–Konyagin).** For a multiplicative subgroup `G ⊂ F_p*` of order `|G| = H`,
BGK-type sum-product bounds give `max_{b≠0}|Σ_{x∈G} e_p(bx)| ≤ H^{1−δ}` for an effective `δ > 0` *as
long as `H > p^ε`*. The mechanism is additive-energy / sum-product amplification: a subgroup with large
exponential sum would have large additive energy `E(G)`, but multiplicative structure forces `E(G)`
small (a subgroup can't be approximately additively closed unless it is almost all of `F_p`). The
quantitative `δ` degrades as `H` shrinks relative to `p`. di Benedetto–Solymosi-type refinements push
`δ` but **collapse precisely at `H ~ p^{1/4}`** — and the prize lives at `n = H ≈ p^{1/4}` (β≈4),
exactly where the gain `→ 0`. This is the **Burgess barrier**: below `p^{1/4}` no unconditional
power-saving is known for a single multiplicative subgroup. The prize asks not just for *some*
power-saving but for the *optimal* square-root cancellation (up to `√log`), at the worst point. No
technique in the literature reaches it.

**Paley.** `M(n) = λ₂(Cay(F_p, μ_n))`. For the classical Paley graph (`μ = QR`, `H = (p−1)/2`,
*thick*) the graph is essentially Ramanujan: `λ₂ ≈ √p/2 ≈ √H`, optimal. The Paley Graph Conjecture
(Bourgain) — that thin Cayley graphs on multiplicative subgroups still have near-optimal `λ₂` — is the
general open statement; our prize is its sharpest thin-dyadic instance. "Near-Ramanujan for thin
multiplicative Cayley graphs" is the same object as BGK and the same object as the prize. The √log slack
between the proven floor and the target IS the conjecture; closing it is closing Paley.

**Why the moment method funnels here and stops.** The clean reduction: `M(n)^{2r} ≤ (1/n)·Σ_b η_b^{2r}
= (p/n)·E_r(μ_n)`, and if the **DC-subtracted energy** `A_r := E_r − n^{2r}/q ≤ (2r−1)‼·n^r` (the
Gaussian/Wick bound), then minimizing over `r ≈ log m` gives exactly `M ≤ √(2n log m)`. The char-0
Wick bound `E_r ≤ (2r−1)‼ n^r` is **proven** (Lam–Leung: vanishing sums of 2-power roots are ±-pairs;
union bound over the `(2r−1)‼` matchings) and now **Lean-formalized** (`_CharZeroWickEnergy.lean`,
axiom-clean — independently re-verified this session). The wall is the **char-p transfer at depth
`r ≈ ln q ≈ 89`**: in `F_p` there are *spurious* mod-p collisions `Σζ^{a_i} ≡ Σζ^{b_j} (mod p)` that
don't hold in `ℤ[ζ]`. The crude norm bound (no spurious solutions while `(2r)^{n/2} < p`) holds only
for `n < 2 log q / log log q ≈ 40` — vacuous at the prize `n = 2³⁰`. Whether the spurious excess stays
sub-Wick collectively at depth `log m` is the open question, and the §4 second-order meta-theorem proves
no *2nd-order* method (energy, L², spectral λ₂, SDP/Delsarte, cumulant-2, Shaw operator) can do better
than the trivial `n` — because `(q·E_r)^{1/2r} ≥ n` from the DC term alone. So the proof must be
genuinely higher-order, and the 3-property necessary condition (b-sensitive + deterministic-archimedean
+ L∞) shows every classical tool fails at least one requirement.

## III. The comparable quantities — what "moving, not closing" means

Write `defect m* := s* − k`, so `δ* = (1−ρ) − m*/n`. The *same* `m*` recurs across rates and is the
real scalar to understand:
- ρ=½, full direction range: `m* ≡ 3` for n=12,16,20,24 → a clean `δ* = ½ − 3/n` (capacity − 3/n).
- ρ=⅛, char-0 full range: `m* = log₂ n` exactly at n=16,32 → candidate `δ* = (1−ρ) − log₂n/n`.
- ρ=¼: the `b<s`-capped engine matches the Plotkin proxy `½+1/n` up to n=28, then *artifact*-jumps
  at n=32 (the engine excludes the antipodal binder `(n/2, n/2−1)` — documented gotcha).

Every "open avenue" in the 100-route ledger is either (a) one of the ~20 faces of `M(n)` (exact), or
(b) a lossy projection (energy → δ* loses a √; census → Johnson; circle-method → RMS not sup). The
discipline the prize demands — and the user's instruction — is to reject anything that merely *renames*
or *moves* `M(n)`; only a bound on the char-p structural count at depth `log m`, or a genuinely
BGK-independent handle, can *close*.

## IV. The one live, BGK-independent cracks

Three places the wall is genuinely thinner:

1. **The smoothness lever (A1).** Every BGK reduction treats `μ_n` as an abstract subgroup and is blind
   to the *explicit* structure `x_i = g^i`. The 3rd factorial moment of the explicit-`μ_n` list exceeds
   the random-RS value by *exactly* the torus-normalizer involution energy `~n⁴/8` — a Weil-(1,1)-pencil
   conic-incidence count, **not a character sum**, so it dodges the §4 meta-theorem on a technicality.
   The risk is signal strength (`q⁻⁴`). This is the single most BGK-independent object in the cone.

2. **The combinatorial decoupling (the live lead).** The δ*-binding far-line incidence is **exactly
   quantized and p-independent**: `I(a,b;w) = N·S + 1`, `S = n/gcd(b−a,n)`, `N` = #nonzero
   dilation-orbits of bad γ; `δ*` is where the worst-direction `N` drops to ~1 (proven: a far direction
   forces ≤1 γ per witness, *verbatim over every F_p*). So at the binding radius `δ*` is a
   **p-independent, gating-blind, monomial-dominated combinatorial** quantity — *distinct* from the
   p-dependent BGK period. **If** `m*` (the orbit-count crossing depth) has a closed combinatorial form
   **and** far lines are extremal (`WorstCaseFarIncidenceBounded`), the prize is a computable
   combinatorial quantity, off the √-cancellation wall. The catch is the extremality bridge is open, and
   far-line δ* is provably an *upper* bound on the true MCA δ* — so the combinatorial value gives the
   ceiling unless the bridge is closed.

3. **The floor side (A3).** The entire campaign only ever bounded δ* from *above*; the floor was never
   pushed past `(1−√ρ)/2`. The reverse LD⇒MCA dictionary (`exists_interleavedList_card_gt_of_epsMCA_gt`)
   could show smooth `μ_n` forces a *smaller* list than a random domain in `(halfJ, J)` — a higher thin
   floor. This is the one direction the forward Johnson machinery structurally cannot produce, and it is
   the direction the prize actually needs.

## V. Why it has been hard, and what is likely to fall

The campaign (#232→#444, ~1200 comments, a 100-route DEAD ledger) has done something rare: it has
*proven* the elimination of every elementary and second-order route as a theorem, formalized the entire
axiom-clean substrate, and proven that numerics cannot settle floor-vs-Johnson at any feasible `n` (the
two laws coincide through n=64; separate only at n≥128, brute-force-infeasible). That is why it is hard:
the easy half is done and certified dead, and the remaining half is a recognized 25-year-open problem in
analytic number theory that needs a genuinely new sum-product / effective-equidistribution / monodromy
input — or the one structural escape (smoothness / combinatorial decoupling) actually closing.

**Most likely to fall, in order:** (1) the *ceiling* refinements (KKH26 s=128 via Thorner–Zaman PNT —
pure analytic NT, will fall when formalized); (2) a *closed combinatorial form for `m*`* via the
Lam–Leung orbit-count (decoupled from BGK, computable — this is the live lead, and its value, even as a
ceiling, is publishable); (3) the *floor* up to full Johnson via the reverse dictionary (A3). The prize
itself — the floor in the window interior — falls only if the smoothness lever (A1) or the extremality
bridge genuinely closes; absent that, it waits on external mathematics.

*(Sections VI — the 100 code-insights — and VII — the ranked attack angles with verdicts — are merged
from the parallel research workflow upon completion.)*

---

## VI. One hundred insights from the current code (bugs / novel math / feasible ideas)

*Generated by a parallel research agent over the ~1839-file ProximityGap cone; tags: [BUG/STALE], [NOVEL], [IDEA]. Anchors in parentheses.*

Below are 100 concrete observations from the current ProximityGap cone (file/theorem anchors in parentheses). Tags: [BUG/STALE] stale claim, mislabel, vacuous-in-regime; [NOVEL] genuine in-tree math; [IDEA] grounded new conjecture/route.

1. [BUG/STALE] DCEnergyCorrection.DCEnergyBound and CumulantGaussPeriodBound.CumulantEnergyBound are byte-identical Props (q*E_r - n^{2r} <= q*Wick) in two namespaces, each with its own consumer chain and falsification hook — a true duplication to consolidate into one object.
2. [NOVEL] The whole moment route is correctly re-anchored on the DC-subtracted bound: DCEnergyCorrection.eta_pow_le_of_dcEnergyBound gives non-vacuous per-frequency bounds at the prize, where the in-tree GaussianEnergyBound is false.
3. [BUG/STALE] GaussianEnergyBound (E_r <= Wick) is documented (DCEnergyCorrection header) as FALSE for n>=64, r~ln q because n^{2r}/q >> Wick; hence DCMomentSupBound.eta_pow_le_dc_of_energyBound is labeled 'strictly sharper' yet is VACUOUS at the prize (its hypothesis is the false GaussianEnergyBound) — only the DCEnergyBound variant is usable.
4. [NOVEL] DCEnergyRungTwo.dcEnergyBound_two_rootsOfUnity discharges the BGK r=2 rung UNCONDITIONALLY for mu_{2^m} via the exact Sidon-mod-negation energy E_2 = 3n^2-3n; with DCEnergyBaseCase the open core is genuinely r>=3 only.
5. [NOVEL] DCEnergyRungThree.dcEnergyBound_three_of_repThree reduces the r=3 DC rung to the single char-p residual RepThree (order-6 antipodal pairing), the exact analog of the landed r=2 Sidon pin.
6. [NOVEL] EtaShallowTailUncond.eta_pow_le_shallow_uncond is a fully-unconditional ceiling M <= (n^{2r}(q-n))^{1/(2(r+1))} at every order r, built only from the textbook E_r <= n^{2r-1} (card_fiber_le_card_pow + rEnergy_le_card_pow) — no char-p/BGK input.
7. [NOVEL] The shallow-tail file pins exactly where the trivial energy bound stops helping: the reachable band is q <~ n^{r/(r-1)}, shrinking to q<~n as r grows, so the deep sub-Gaussian tail at r~ln q is provably unreachable from the trivial bound.
8. [BUG/STALE] ShawFlatnessRefuted.shaw_flatness_false_mu_n requires p>2^n (Sidon threshold) — the small-subgroup regime n<log p, NOT the prize regime n~p^{1/4}; the refutation is real but its concrete mu_n instance is off-regime.
9. [NOVEL] The general form worst_period_sq_gt_two_card needs only the energy floor 3n^2-3n plus a prize-compatible field-size condition, so the L^4/L^2 forcing M^2 > 2n is prize-applicable whenever the energy floor holds — a usable lower bracket.
10. [IDEA] ShawFlatnessRefuted + EtaShallowTailUncond together two-side-bracket the true constant: sqrt(3n-3) <= M (energy floor via L^4/L^2) and M <= (n^{2r}(q-n))^{1/(2(r+1))}; tightening the upper side toward sqrt(n log m) is exactly the prize.
11. [BUG/STALE] MCADeltaStarCapacity.rs_mcaDeltaStar_le_capacity (delta* <= 1-(k+1)/n) carries hsmall: q < (n-k)*2^128; at prize (q~n*2^128, n-k~n(1-rho)) this is FALSE, so the capacity ceiling is vacuous in the prize regime (sub-prize fields only).
12. [NOVEL] OpenCoreConditionalPin isolates the ENTIRE open content into one Prop WorstCaseIncidenceBounded and proves (axiom-clean) the conditional delta* pin through three faces (raw, budget E/q, orbit-count) — the honest 'closed conditional conjecture'.
13. [NOVEL] SumsetExtremalityReduction.worstCaseIncidence_of_monomial_extremal collapses the |A|^{2n}-fold open-core quantifier to the n^2-size monomial sub-family, conditioned on one empirically-supported SumsetExtremal Prop — a major structural reduction.
14. [NOVEL] SumsetExtremality.incCount_comp_perm proves the far-line incidence count is exactly invariant under any code automorphism (Z/n dilations for RS/mu_n), justifying the monomial fundamental domain rigorously.
15. [NOVEL] MCAEigenstackOrbitLaw.mcaEvent_eigenstack_iff + orderOf_dvd_card_of_mul_mem give field-independent orbit arithmetic: a multiplicative eigenstack's bad-scalar count is eps + (#orbits)*ord(a^{-1}c), eps in {0,1} — the mechanism behind the 'flat numerator'.
16. [NOVEL] OverdetIncidenceMaxClosedForm.overdetIncidenceMax_gt_budget proves the over-determined incidence MAX 2m^3-2m^2+1 strictly exceeds budget n=4m for all m>=2 — the arithmetic core of 'binding s* is always over-determined => delta* p-independent'.
17. [BUG/STALE] OverdetIncidenceMaxClosedForm establishes the closed form only at s=k+2, k=2 by decide on m=2..10; its cyclotomic derivation and the general s-dependence (the actual s*(n,k) asymptotic) are NOT formalized — the antipodal-direction value is asserted from probes.
18. [BUG/STALE] DISPROOF_LOG O181/2026-06-15: the decoupling crossing-depth rate-law c*=n(1/2-rho)-1=Theta(n) from DecouplingDecayCrossingDepth.lean was REFUTED — that file fixed k=n/4 and extrapolated; the true c*(n,k) is RATE-CONSTANT O(1) (s*=k+c*(n)); flag any downstream use of the Theta(n) law.
19. [BUG/STALE] DISPROOF_LOG 2026-06-15: the 'first floor-consistent canonical #bad signal' (shallow band ~0.26) is a JOINT artifact of census-vs-eps* budget conflation (3^{n/2} per-band census, not q*eps*~n) and an undercounting collinearity engine (n=8 line(4,2): published 5 vs correct 17).
20. [NOVEL] CrossCellShkredovBound.crossCell_add_two_diag lands the exact dyadic-descent decomposition 2*N0(H,r)+crossCell = N0(G,r) (faithful N-subtraction via the proven one-sided descent) — the named off-diagonal cross-resonance object.
21. [BUG/STALE] CrossCellShkredovBound.CrossCellAbsoluteBound is explicitly a Prop that is POINTWISE FALSE at finite n for every r>=3 (probe: p=97,n=8,r=4 gives 9312>4096; violation grows with p) — labeled 'open' but satisfiable only asymptotically; a textbook 'open wall actually false at depth' case.
22. [NOVEL] CrossCellShkredovBound documents the ShkredovDiagonalBound is REFUTED (crossCell/(2 N0(H,r)) grows to 85 at n=8,r=10) AND that H is Sidon-like (E_3(H)/|H|^3 -> 1), so BSG/sum-product has no additive structure to exploit — kills the higher-energy route cleanly.
23. [NOVEL] CumulantFermatObstruction.fermat65537_n64_r2_excess is an exact integer witness (E_2(mu_64 in F_65537)=19776) refuting the cumulant bound at r=2; the moment certificate (~38.27) falls below the true M (~43.63) — consumer-level (not single-r) failure at the Fermat prime.
24. [NOVEL] PairingResidualFailsAtPrize.not_pairing_residual_of_card_pow_gt: by modus tollens on the DC-essential refutation, the char-0 antipodal-pairing residual H itself MUST be false at prize scale — pins where the Lam-Leung pairing route breaks.
25. [NOVEL] CapacityVacuity.exists_codeword_hammingDist_le_redundancy proves MDS covering radius <= redundancy via pure Lagrange interpolation (no parity-check), giving the cleanest formal 'why the prize is open': at capacity the CA premise is satisfied by every word.
26. [IDEA] CapacityVacuity flags Okamoto 2025/1712 (Syndrome-Space Lens) as the syndrome-space form; memory marks Okamoto's capacity claim 'suspect' (contradicts proven impossibility) — worth a Lean cross-check that the cited Lemma 3.1/Thm 5.1 only gives vacuity, not a capacity MCA bound.
27. [NOVEL] GaussPeriodParsevalFloor.exists_eta_sq_ge_parseval_floor: some b!=0 has |eta_b|^2 >= n(q-n)/(q-1) ~ n, so the sqrt(n) floor is unavoidable (Alon-Boppana side) — the proven lower half of the spectral frame.
28. [NOVEL] GeneralizedPaleyRamanujan reframes M(n) as lambda_2(Cay(F_q,mu_n)) (Liu-Zhou Thm 115) and names the live target as near-Ramanujan-up-to-sqrt(log): |eta_b|^2 <= C*n*log(q/n), strictly weaker than the legacy 2sqrt(n) ceiling kept only for back-compat.
29. [NOVEL] GeneralizedPaleyRamanujan.nearRamanujan_of_depthLogSubGaussian + its converse establish a two-way dictionary between the Paley face and the single structural constant Lambda^2 (DepthLogSubGaussian) — they are equivalent up to a log comparison, unifying the faces.
30. [NOVEL] Frontier._BGKSOTAInsufficiency.bgk_value_exceeds_prizeTarget_eventually proves the clean real-analysis wall: for any delta<1/2, C*n^{1-delta} eventually exceeds C'*sqrt(n*L), i.e. n^{1/2-delta}->infinity dominates the constant-index log factor.
31. [IDEA] _BGKSOTAInsufficiency.bgk_tight_refutes_prizeFloor shows: IF the SOTA bound were tight at exponent 0.989 the prize floor would be FALSE — so the prize being TRUE requires the SOTA upper bound to be loose (true M much smaller than guaranteed n^{0.989}); a useful logical inversion.
32. [BUG/STALE] _BGKSOTAInsufficiency.diBenedettoDelta := 11/1000 is hard-coded as the SOTA exponent; the docstring's claim 'valid for n>=q^{1/4}' means even this exponent is OUTSIDE the prize regime (n~q^{1/4}), so the named SOTA is doubly inapplicable — worth flagging the regime mismatch in the headline.
33. [NOVEL] Frontier._MetaTheoremSecondOrderFloor.momentDepth_method_floor proves the spike (sqrt(S),0,...,0) saturates EVERY moment rung at sqrt(S), so no single-depth-moment method can beat sqrt(S) at any order r — a clean universal no-go.
34. [BUG/STALE] The momentDepth no-go is about methods reading only the TOTAL moment sum(eta_i)^{2r}; the BGK/cumulant route reads per-frequency structure differently, so the no-go does not actually preclude the working DC-subtracted route — the 'no tighter bound from any direction' capstone overstates if read naively.
35. [NOVEL] _NoTighterBoundCapstone.secondMoment_does_not_determine_sup gives an explicit countermodel (sqrt2,-sqrt2,0,0) vs (1,1,-1,-1): identical 1st/2nd moments, different sup — proving any b-symmetric statistic is blind to the worst frequency.
36. [NOVEL] MomentCountSupBound.forall_le_of_sum_pow_lt uses integer-rounding of the Markov tail count (#exceedances < 1 => 0) to convert a strict moment bound into a sup bound — a genuinely useful sharpening primitive.
37. [BUG/STALE] MomentCountSupNotSharper.count_threshold_not_below_perterm PROVES the integer-count route is NOT asymptotically sharper than the per-term root bound (same infimal threshold T_r=(sum a^r)^{1/r}); so MomentCountSupBound's docstring claim 'sharper than the per-term bound' is only true at the measure-zero boundary.
38. [NOVEL] FourthMomentCLT.fourth_moment_le_of_dc derives the sub-Gaussian fourth moment sum|eta_b|^4 <= 3*q*n^2 from DCEnergyBound G 2 — period kurtosis <= 3(1+o(1)), the provable instance of the period CLT. **Correction (audit 2026-10-28, PG-030):** this is a Gaussian-comparison fourth-moment *upper bound* under the explicit `DCEnergyBound G 2` assumption, not an instance of a CLT; moment domination (even `A_r <= Wick` for all r) does not give distributional convergence.
39. [NOVEL] ConverseLamLeung2Power.zero_sum_imp_antipodal proves the CONVERSE Lam-Leung for 2-power order in char 0 (vanishing 2^a-root sum => antipodal set) purely from minpoly degree phi(2^a)=2^{a-1}, no Lam-Leung machinery — a self-contained characterization.
40. [NOVEL] ConverseLamLeung2Power.lowHalf_powers_linearIndependent uses minpoly.IsIntegrallyClosed.degree_le_of_ne_zero over Z to get integer linear independence of low-half powers — a reusable cyclotomic-independence primitive.
41. [NOVEL] BoundedCyclotomicIndep.BoundedHalfBasisIndep names the precise char-p object: unbounded HalfBasisIndepZ is ALWAYS false in char p (g=(p,0,..)) but the bounded-coefficient version can hold above a prime threshold; the prize is exactly this at support C~2 ln q. **Correction (audit 2026-10-28, PG-031):** in the prize regime this premise is false, not open: it needs `(C+1)^N <= |F|` (`not_boundedHalfBasisIndep_of_card_lt`) and is refuted in Lean at n=16, p=65537, C=4 (`not_boundedHalfBasisIndep_zmod65537`); C bounds each coefficient, not the support.
42. [NOVEL] AntipodalBalanceBounded.antipodal_balance_of_boundedIndep gives the bounded char-p swap for the one char-0 step inside count_antipodal: ED^N=-1 + bounded indep + bounded weights => equal antipodal weights — the bounded ladder lever.
43. [IDEA] The chain BoundedHalfBasisIndep (r=2 instance landed = sidonModNeg_improved at p>12^phi(n)) => antipodal balance => char-p Wick ladder => prize reduces the whole BGK wall to ONE named threshold (bounded cyclotomic indep at support ~2 ln q mod the prize prime) — a sharp, attackable formulation. **Correction (audit 2026-10-28, PG-031):** the chain is a valid conditional reduction, but its premise is false at prize parameters (see item 41), so it does not reduce the prize to an open threshold.
44. [NOVEL] HeightGatePowerMean.abs_norm_pow_le_power_mean generalizes the AM-GM height-gate to every even moment 2r: |N(alpha)|^{2r} <= ((1/m)sum|sigma alpha|^{2r})^m — the r-parametrized substrate the moment tower needs (vs a fixed-r house bound).
45. [NOVEL] HeightGatePowerMean.abs_norm_pow_le_card_mul_max_moment is the directly-consumable shape: per-conjugate moment cap M => |N|^{2r} <= M^m, exactly what GaussPeriodMomentBound feeds the energy bound into.
46. [NOVEL] Frontier._DonohoStarkTight.donoho_stark_tight proves the Donoho-Stark uncertainty principle on Z_N has NO slack (delta_0 saturates |supp|*|supp F| = N), the crux of the c.349 reframing: saturating configs leave nothing to exploit.
47. [IDEA] The Tao/uncertainty frame (_PrizeFactWorkspace section 6): far-line s* = n - min|support| of a (k+2)-Fourier-sparse function on Z_n; sharp UP holds only for PRIME N (=>capacity), composite/prime-power UP is genuinely OPEN (Chebotarev arXiv:2412.08600) — a fresh literature anchor, though likely reduces to the same BGK wall via Lam-Leung.
48. [BUG/STALE] _PrizeFactWorkspace.DefectGrowthClass := True is an honest placeholder marker (clearly labeled), but the central pivot question (is m* = Theta(sqrt n) [BGK] or O(log n) [near-capacity]?) has NO Lean object encoding it — the campaign's deciding scalar is prose-only.
49. [BUG/STALE] _PrizeFactWorkspace section 3 documents an engine ARTIFACT (scripts/rust-pg/src/main.rs:149 caps far dirs b in [k,s), EXCLUDING the antipodal binder (n/2,n/2-1)); the published n>=32 rho=1/4 delta* ground-truth values carry this artifact and follow the Plotkin proxy -> Johnson, not the true worst direction.
50. [IDEA] The bifurcation m*=sqrt(n)-1 vs m*=2log2(n)-5 COINCIDE through n=64 and separate only at n>=128 (brute-force-infeasible) — numerics provably cannot settle floor-vs-Johnson at feasible n; this is the precise reason a thinness-essential PROOF (not computation) is mandatory.
51. [NOVEL] MCAThresholdLedger is the clean bracket engine: mcaDeltaStar = sSup of good radii, with le_mcaDeltaStar_of_good / mcaDeltaStar_le_of_bad and the proven mca_good_set_downward_closed (epsMCA monotone) — every pin routes through it.
52. [NOVEL] MCAThresholdLedger.candidate_floor_is_exact_REFUTED and candidate_uptocapacity_REFUTED give machine-checked countermodels (constCode over ZMod 3 has eps_mca(1/3)=1>1/3) showing eps_mca genuinely grows with delta and the prize MUST fix |F| large.
53. [NOVEL] CumulantGaussPeriodBound.cumulant_eq is the exact DC-subtracted moment identity sum_{b!=0}|eta_b|^{2r} = q*E_r - n^{2r}, the foundation under both the cumulant and DC chains.
54. [NOVEL] CumulantGaussPeriodBound.cumulantBound_iff_le_diag_add_principal makes the random/diag split concrete: random = principal n^{2r}/q (equidistribution baseline), diag = (2r-1)!!*n^r (Wick) — pins the abstract split of _ConstantIndexMomentGate.
55. [IDEA] Because DCEnergyBound = CumulantEnergyBound, the proven r=1,2 unconditional rungs (DCEnergyRungTwo) immediately discharge the cumulant chain too — the worstCaseIncompleteSumBound_of_cumulantBound consumer is unconditionally usable at r<=2 right now (combine across the duplicated files).
56. [NOVEL] EnergyBoundImplication.dcEnergyBound_of_gaussianEnergyBound proves the DC subtraction strictly ENLARGES the valid regime (raw bound => DC bound, and DC survives where raw fails) — the DC correction is mandatory, not cosmetic.
57. [NOVEL] DCMomentSupBound.eta_pow_le_dc is the unconditional single-far-term bound |eta_b|^{2r} <= q*E_r - n^{2r} (single term <= DC-subtracted sum), the right object since M excludes b=0.
58. [NOVEL] PrizeEnergyHeadline.prize_addEnergy_of_dcEnergyBound chains DCEnergyBound at r~ln q + regime q>=n^2 to E(G)=O(n^2 log q) in one front door — the corrected, non-vacuous version of the energy headline.
59. [NOVEL] PrizeSupNormHeadline.prize_supNorm_bound instantiates at r=ceil(ln q): |eta_b|^2 <= 2e*n*ceil(ln q), i.e. M <= sqrt(2e*n*ln q), the clean citable conditional prize bound (open input = DCEnergyBound at ceil ln q).
60. [IDEA] HeightGatePowerMean's per-conjugate moment cap M^m and the period moment chain are two formalizations of the SAME power-mean lever (Galois conjugates of the Gauss period sum = the n periods); wiring abs_norm_pow_le_card_mul_max_moment to eta_pow_le_dc could give a house-theoretic second proof of the sup-norm bound.
61. [NOVEL] CrossCellShkredovBound.N0_gap_of_absoluteBound is the closure-mechanism shape: an absolute crossCell bound iterates the dyadic descent down the 2-power tower (q>>2^r|H|^r) to the clean N0(G,r) ~ 2*N0(H,r) fixed point.
62. [IDEA] The honest open form is crossCell H zeta r <= 2^r|H|^r/q (= BCHKS Conj 1.12) and crossCell tracks the random expectation to O(1) with NO anomalous excess — suggesting the genuine obstruction is purely the arithmetic of mod-p spurious collisions, not additive structure.
63. [NOVEL] MCAEigenstackOrbitLaw.DemoF5 reproduces the sharp eps_mca(C542,1/4)>=4/5 from ONE badness certificate + the orbit law (vs four hand-built certificates in DeltaStarExactPinF5) — demonstrates the symmetry engine compresses the lower-bound proof.
64. [IDEA] The eigenstack orbit law (count = eps + #orbits*ord(a^{-1}c)) + over-det quantization I(a,b;w)=N*S+1 are two exact combinatorial identities for the SAME incidence; combining them could give a closed N-vs-budget crossing law decoupled from BGK (the live p-independent path).
65. [NOVEL] OpenCoreConditionalPin.worstCaseIncidence_pin_of_orbitCount routes the orbit-count form (N_u <= d with S*d=n) through OrbitCountCrossingLaw.crossing_law into the delta* pin — the orbit-count face of the conditional pin is axiom-clean.
66. [IDEA] SumsetExtremal (the named residual) is tested but unproven; the equivariance core incCount_comp_perm already proves invariance, so the missing piece is only that the worst ORBIT REPRESENTATIVE is monomial — a finite per-orbit optimization, potentially closable by the height-gate AM-GM on the monomial directions.
67. [BUG/STALE] GeneralizedPaleyRamanujan keeps BOTH GeneralizedPaleyRamanujan (legacy 2sqrt(n), refuted by the energy floor M>2sqrt(n) per GaussPeriodParsevalFloor header) AND the live near-Ramanujan Prop — the legacy bridge worstCaseIncompleteSumBound_of_ramanujan is provably never satisfiable for mu_n, so it is a dead (vacuous) consumer.
68. [NOVEL] The Parseval floor M>2sqrt(n) (graph NOT Ramanujan) and the legacy 2sqrt(n) ceiling are mutually contradictory for mu_n — the codebase correctly retires the literal-Ramanujan target; the surviving object is near-Ramanujan-up-to-sqrt(log).
69. [IDEA] EtaShallowTailUncond at r=0 recovers the Parseval value M<=sqrt(q-n), and GaussPeriodParsevalFloor gives M>=sqrt(n(q-n)/(q-1)); these pinch at the floor scale, confirming the shallow tail's r=0 rung is tight — the only freedom is climbing r toward ln q.
70. [NOVEL] PairingResidualFailsAtPrize formalizes the modus-tollens 'mapped wall': holding the unconditional combinatorial inputs (negation-closure energy<->zero-sum, matching count <=(2r-1)!!) fixed, the char-p anomaly destroys the antipodal-pairing structure — locating the breakage precisely.
71. [IDEA] The non-antipodal zero-sum 2r-tuples (the char-p extra solutions PairingResidualFailsAtPrize forces to exist) ARE exactly the crossCell off-diagonal mass; equating not_pairing_residual with crossCell>0 could unify the pairing and dyadic-descent faces into one count.
72. [BUG/STALE] DeltaStarPinchBracketD3 OverDetFloorGood is a named hypothesis (the lower bracket is NOT a Lean brick); only the KKH26 ceiling side is unconditional, so deltaStar_two_sided_bracket's lower bound is consumed, not proven — honest but the 'bracket' is half-conditional.
73. [NOVEL] DeltaStarPinchBracketD3 makes a crucial correction: the KKH26 ceiling 1-r/2^mu is rate-LOCKED at r=k+1 (the bad line lives on the degree-(r-2)m eval code), NOT free to minimize over r; naive minimization gives a spurious 0.5 below the exact 0.5625 (a self-flagging error check).
74. [NOVEL] DeltaStarPinchBracketD3 REFUTES the pinch: floor and ceiling differ by a constant ~1/8 at rho=1/4 (n=16,32) that does NOT shrink with n — so far-line floor != KKH26 ceiling, and the gap IS the open residual.
75. [IDEA] If the constant ~1/8 gap is genuinely n-independent (two-point fit), then far-line delta* = capacity - Theta(1)/8 stays a fixed fraction below capacity at rho=1/4 — consistent with m*=O(1)/bounded (near-capacity, upper-bound-only), supporting the non-BGK horn of the pivot question.
76. [NOVEL] CapacityVacuity.forall_exists_codeword_hammingDist_le_of_capacity proves that at any budget t>=n-deg every word (even adversarial) has a codeword within budget — the precise information-theoretic obstruction behind the open prize, with an explicit Lagrange witness.
77. [IDEA] The shallow-tail band q<~n^{r/(r-1)} crosses the prize q~n^4 at r=4/3 (i.e. r=2 gives q<~n^2, r=3 gives q<~n^{3/2}); so the unconditional ceiling is sub-sqrt(q) only up to r~2 at the prize rate — quantifies that the prize needs the conditional deep tail, not the trivial one.
78. [NOVEL] DCMomentSupBound + GaussPeriodMomentBound show four packagings (Markov tail, integer-count, EVT histogram, per-term root) all optimize the SAME object min_r (q*A_r)^{1/(2r)} on the DC-subtracted moment — MomentCountSupNotSharper proves none escapes, a clean 'all routes funnel to one wall' result.
79. [IDEA] Since the r=1,2 DC rungs are unconditional and FourthMomentCLT gives sub-Gaussian kurtosis, a Lean-formalized moment-tower interpolation (proving A_r grows sub-Wick from the r<=2 base + a recursion) could push the unconditional reach past r=2 — the autocorrelation recursion E_{r+1}=n*E_r+cross_r (F6) is the candidate engine.
80. [NOVEL] MCAThresholdLedger.mcaGoodRadii_le_of_bad's proof re-derives epsMCA monotonicity inline via Pr_le_Pr_of_implies on the mcaEvent witness — a reusable monotonicity-by-event-implication pattern.
81. [BUG/STALE] OpenCoreConditionalPin header states best-known unconditional incidence bounds are n^{1-o(1)} (vacuous at budget ~n in the window interior); EtaShallowTailUncond's r=1 Parseval bound M<=sqrt(q-n) is actually a BETTER-than-n^{1-o(1)} unconditional bound in the over-determined regime — the header understates the in-tree unconditional reach.
82. [IDEA] worstCaseIncidence_pin_budget (open core I(delta)<=E alone => delta<=delta*) plus the over-det quantization I=N*S+1 means the pin reduces to N*S+1<=n; with S=n/gcd(b-a,n) the worst direction is gcd=n/2 (S=2), so N<=(n-1)/2 — a concrete combinatorial inequality to attack for the upper-bound-only delta*.
83. [NOVEL] AntipodalBalanceBounded reduces a vanishing weighted half-basis+antipode sum to coefficient differences a_j-b_j bounded by C, killed by BoundedHalfBasisIndep — the bounded-independence mechanism is genuinely characteristic-uniform (works in any field).
84. [IDEA] Combining ConverseLamLeung2Power (char-0 vanishing 2^a-root sums = antipodal only) with BoundedHalfBasisIndep at support C~2 ln q gives the exact statement: the prize holds iff no nontrivial bounded-coefficient (<=2 ln q) relation among 2^{mu-1} half-basis powers exists mod the prize prime — a single clean number-theoretic conjecture. **Correction (audit 2026-10-28, PG-031):** no "iff" is proved (only the conditional direction), and the "no relation" side is false at prize parameters by counting (`(C+1)^N > |F|`, `not_boundedHalfBasisIndep_of_card_lt`).
85. [NOVEL] HeightGatePowerMean is built directly on Mathlib's NumberField.House and Algebra.norm_eq_prod_embeddings, showing the period sup-norm = house of a degree-m algebraic integer (face F5) is formalizable with existing Mathlib — a route that does not need new cyclotomic API.
86. [BUG/STALE] _MetaTheoremSecondOrderFloor.periods_secondMoment_method_floor requires hGF: n^2 <= q*n (i.e. n<=q), always true, so it is non-vacuous; but its conclusion bounds via sqrt(qn-n^2)~sqrt(qn) — confirming second-moment methods are sqrt(q)-lossy, which the prize must avoid, NOT a defect but a sharp negative result.
87. [IDEA] secondMoment_does_not_determine_sup's countermodel pair (sqrt2,-sqrt2,0,0)/(1,1,-1,-1) is the discrete analog of the spike-vs-flat dichotomy; the periods are FLAT (memory: exchangeable white-noise, autocov = -Var/(m-1)), so the prize-relevant statement is 'periods are far from the spike' — a measurable genericity invariant to formalize.
88. [NOVEL] The cone correctly distinguishes proven-floor (M~sqrt(n), Parseval) from open-ceiling (M<=C sqrt(n log m)); the entire campaign reduces to the single ratio M/sqrt(n) = Theta(sqrt(log m)) slack, named consistently across GaussPeriodParsevalFloor, _PrizeFactWorkspace, _BGKSOTAInsufficiency.
89. [IDEA] OverdetIncidenceMax 2m^3-2m^2+1 at s=k+2 vs budget 4m: the over-det MAX is cubic so it ALWAYS exceeds linear budget; this is exactly why binding s* must climb (over-det never binds) — formalizing the full s-dependence I(s) (decreasing in s) and its budget-crossing would CLOSE the char-0 over-det asymptotic (the one remaining char-0 item, decoupled from BGK).
90. [BUG/STALE] OverdetIncidenceMax_values uses `decide` on m up to 10 (values to 1801) — fine, but the closed form is fit to the published sequence, not derived; if the published sequence itself carries the main.rs:149 b-range artifact, the closed form could be the artifact-direction value, not the true antipodal MAX. Cross-check against lcfast.
91. [NOVEL] DCEnergyRungTwo's energy<->moment bridge rEnergy G 2 = addEnergy G is read off TWO fourth-moment Parseval identities (subgroup_gaussSum_moment at r=2 and subgroup_gaussSum_fourthMoment), a clean two-identity cancellation — reusable for higher r if the analogous moment identities are landed.
92. [IDEA] The prize sup-norm bound M<=sqrt(2e n ln q) (PrizeSupNormHeadline) is conditional on DCEnergyBound at ceil(ln q)~89; since r=1,2 are unconditional and the bound only needs ONE good r (min over r), proving DCEnergyBound at any single r in [2, ln q] that already gives sub-sqrt(q log) would suffice — the optimization is over r, lowering the proof target.
93. [NOVEL] _DonohoStarkTight + the prime-only sharp UP (Tao) give a structural explanation for WHY 2-power (composite) smooth domains are the hard case: prime N => sharp UP => capacity reachable; N=2^mu => only weak Donoho-Stark => the open prize — the hardness is intrinsic to compositeness.
94. [IDEA] Frontier._TwoPowerRootDescent / _DyadicTowerDescent + CrossCellShkredovBound.N0_gap_of_absoluteBound are two descent mechanisms on the SAME 2-power tower; reconciling the dyadic-descent N0 recursion with the root-descent could yield an inductive proof of A_r<=Wick by tower depth (the recursion is even-tau-exact, odd-tau-amplifies per memory — the residual is the odd-part amplification).
95. [BUG/STALE] Several headline files (PrizeEnergyHeadline, PrizeSupNormHeadline, _NoTighterBoundCapstone) assert 'A_r <= Wick is true at every prize prime' from probe evidence; but CumulantFermatObstruction PROVES it FALSE at the Fermat prime p=65537,n=64 — the headlines should say 'true at GENERIC (non-2-power-structured) primes', the genericity caveat is load-bearing and sometimes dropped.
96. [IDEA] The cumulant is provably NON-uniform in p (generic-true, Fermat-false per not_cumulantBound_of_excess); so any delta* pin must be conditioned on an explicit genericity invariant of p (e.g. v_2(p-1) bounded, or beta-gating) — naming that invariant as a Lean Prop is a concrete missing brick.
97. [NOVEL] MomentCountSupBound.exceedance_card_eq_zero_of_sum_pow_lt gives the exact integer-count corollary (#{a_b>T}=0 when moment<T^r), the cleanest 'sup from moment' primitive — generally useful beyond this cone (e.g. spectral gap arguments).
98. [IDEA] Bridging SumsetExtremalityReduction (monomial collapse) with HeightGatePowerMean (monomial = house of algebraic integer): the MonomialIncidenceBounded input is exactly a house bound on the n^2 monomial directions, so abs_norm_pow_le_card_mul_max_moment IS the lever the reduction was designed to consume — the two files are one unfinished pipeline.
99. [BUG/STALE] The cone has ~1839 Lean files with heavy redundancy (DCEnergyBound=CumulantEnergyBound; GeneralizedPaleyRamanujan keeps a refuted legacy Prop; multiple near-Ramanujan/sub-Gaussian/Lambda definitions for one object M(n)); the ~20-equivalent-faces design (good for attack surfaces) has drifted into definitional duplication that obscures which Prop is the canonical open core.
100. [IDEA] The single most actionable closed-form target: prove the over-det incidence I(s) is monotone DECREASING in s and crosses budget n at s* = k + c*(n) with c*(n)=O(log n) (DISPROOF_LOG: c* is rate-constant, {3,4} wobble at small n) — this is char-0, p-independent, decoupled from BGK, and would pin delta* = (1-rho) - O(log n)/n as a proven UPPER bound (near-capacity), separating it from the BGK sqrt(n) horn at the level of a combinatorial inequality.

---

## VII. Attack verdicts (this round) and the regime-audit

**Attacks executed, adversarially scoped (none closed — honest):**

- **A1 — smoothness lever (M3 / Weil torus-normalizer pencil), the most BGK-independent object.** REDUCES TO WALL. The smooth-vs-random 3rd-factorial-moment separation has an *exact closed cyclotomic form* `D3 = n⁴/8` (q-independent: `n⁴/8 − n³/4 + 3n²/4 − n/2`), BUT the random baseline `E_rand[Σ_φ t₂³] = Θ(n²·q)` grows linearly in q, so the relative signal is `q⁻Θ(1)` — washed out at the prize. The one lever that exploits explicit smoothness `x_i=g^i` is provably too weak by a power of q.
- **A3 — floor-side (push δ\* UP via reverse LD⇒MCA dictionary), the abandoned half.** REDUCES TO WALL. The A3 premise (smoothness shrinks the interleaved list in `(halfJohnson, Johnson)`) is FALSE: the list cliff is **domain-invariant** — max pairwise RS agreement = `k−1` for smooth / random / AP domains alike (pure MDS Singleton, proven axiom-clean). So the unconditional floor stays at half-Johnson; no thin advantage on the floor side.
- **Tao composite-order UP (sharp prime-power uncertainty for Z_{2^μ}).** REFUTED, three ways. The proposed sharp UP is false: the subgroup binomial `X^{n/2}+1` has DFT-support `{0, n/2}` of size `2 ≤ k+2`, so `min|support|` is NOT large; the ±-pair (Lam–Leung) structure does not force `min|support| ≥ n−k−O(log n)`. Prime N ⇒ sharp UP ⇒ capacity; `N=2^μ` ⇒ only weak Donoho–Stark — the *compositeness* is the intrinsic source of hardness (insight #93).

**Regime-audit — refuted methods that may have been tested only out-of-prize-regime:**

- **RETEST #1 (strongest, still owed): the "worst-case is uniformly a small subgroup `μ_{s*}`" (R1/R2) dichotomy.** A clean *closure reduction* (prize ⟺ R1/R2) resting on `s* ~ log n / log log n` being SMALL. Its falsification probe was run ONLY at n=8,16, where `s* ~ 2` is below the resolution floor; the log itself flags "could be a small-n artifact" and *downgraded* (did not kill) the reduction. The exact "Kambiré-stack-is-worst" test at n=64,128,256 (via `scripts/rust-pg lcfast`, exact stack construction, not the `n%(b−a)` proxy) is explicitly **still owed**. This is the clearest case of refutation-pressure applied out of the resolvable regime, and it is a *potential closure*.
- **RETEST #2 (qualified): the linear mass law `Σ a_c ≤ 2n`.** Refuted only at `q=Θ(n)` (q=n=19; q=101,n=80; first violation p=n=41), where random words realize quadratic supply. At the prize `q≈n⁴` the supply `C(n,k+m+1)/q^{m+1}` collapses to the `Θ(n)` partition floor, so the linear law is not obviously violated in-regime — but the team already replaced it with the regime-aware `CappedSupplyTwoRegimeLaw`. Regime-robust-as-corrected; worth a one-line adversarial sanity probe at large q.
- **Correctly-scoped artifacts (no retest):** `perLine_cap_REFUTED` (p=n+1 rank-jump only; the MAX-level claim is correctly stated), the `d=2b` separation (n=8 < pencil capacity; corrected at n=18), the "sparse-density 4%" (a small-subset-cap artifact; true density →1 for n≥128). All three are honestly handled in-tree.

---

## VIII. Open attack angles, ranked by COMPLETENESS (closing the math, not moving the quantity)

Ranked by *whether success closes the math with no open sub-lemma* (completeness), then feasibility.

1. **[CLOSURE-CAPABLE, char-0, FEASIBLE] The over-det incidence monotone-crossing closed form (insights #89, #100).**
   Prove `I(s)` (over-det far-line incidence) is monotone DECREASING in `s` and crosses budget `n` at
   `s* = k + c*(n)` with `c*(n) = O(log n)` (DISPROOF_LOG: `c*` is rate-constant, {3,4}-wobble at small n).
   This is char-0, p-independent, DECOUPLED from BGK. Success pins `δ* = (1−ρ) − O(log n)/n` as a PROVEN
   UPPER bound (near-capacity), separating it from the BGK √n horn at the level of a *combinatorial
   inequality*. Caveat: this is the *ceiling*; it CLOSES the prize only composed with #2.
2. **[THE closure bridge] `SumsetExtremalityReduction` + `HeightGatePowerMean` = one unfinished pipeline
   (insights #13, #98).** `SumsetExtremalityReduction` collapses the `|A|^{2n}` open-core quantifier to the
   `n²` monomial sub-family *conditioned on* `SumsetExtremal` (far lines extremal); `HeightGatePowerMean`'s
   `MonomialIncidenceBounded` is exactly a house bound on those `n²` directions. Closing `SumsetExtremal`
   (the extremality bridge `WorstCaseFarIncidenceBounded`) turns the combinatorial ceiling (#1) into the
   true δ\*. This is the single highest-completeness target; it is the recognized hard core.
3. **[RETEST, potential closure] R1/R2 small-subgroup dichotomy at n=64,128,256 (regime-audit #1).** If the
   worst-stack `s*` genuinely shrinks like `log n/log log n` in-regime, the prize reduces to R1/R2. Owed
   test; cheap-ish via the orbit-count form (no subset enumeration).
4. **[depth-reduction, FEASIBLE] DCEnergyBound at a single `r ∈ [2, ln q]` (insights #4, #5, #92).** The
   moment bound needs only ONE good `r` (min over r). r=2 is unconditional (Sidon `E_2=3n²−3n`); r=3
   reduces to the single char-p residual `RepThree`. Proving any single mid-depth rung that already gives
   sub-√(q log) would suffice — a strictly lower proof target than full-depth `r≈89`. BUT subject to the
   §4 meta-theorem (single-depth-moment caps at √S) — completeness-limited unless combined.
5. **[p-genericity, structural] Name the explicit p-genericity invariant (insights #95, #96).** `A_r≤Wick`
   is generic-true, Fermat-false (`CumulantFermatObstruction`). A δ\* pin must be conditioned on an explicit
   invariant of p (`v₂(p−1)` bounded / β-gating). Naming it as a Lean Prop is a concrete missing brick;
   does not close but sharpens and is honest.

**Net verdict this round:** no angle closed. The two completeness-capable directions are (1)+(2): the
char-0 combinatorial ceiling is *feasible and decoupled from BGK*, but the *floor* still routes through the
extremality bridge (2), which is the recognized open core. The next iteration attacks (1) and (3) directly
(they are computable), and probes whether the (1)→(2) composition can be made unconditional.
