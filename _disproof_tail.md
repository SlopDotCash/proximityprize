**Where the open core sits:** the corrected route is now fully plumbed — step functions (in-tree), errorBound monotonicity (in-tree), floor-cell threshold transport + monotone-ε export (this entry). The single remaining input is the genuine §5 strict-interior producer (`δ_ε_correlatedAgreementCurves` at one strict radius per cell, the BCIKS20 Steps 5–7 content), plus the genuinely-square lattice branch behind `BoundaryCardLatticeData`.

### O68 — the coefficient-general slice theorem: the de Bruijn engine machine-checked

`LamLeungTwoPow.vanishing_coeff_slices` (axiom-clean, 0 sorry): ANY vanishing
ℚ-coefficient combination of p^(m+1)-th roots of unity has all p coefficient slices
equal. Upgrades O66 from subset indicators to arbitrary coefficients — exactly the engine
the two-prime (de Bruijn) CRT double-slice induction needs, whose slice differences carry
{−1,0,1} coefficients. The mixed-radix third pillar now has its core mechanism formal;
what remains of de Bruijn is the CRT bookkeeping (apply this at prime 1 with coefficients
in prime 2's field, then descend).
### O78 — #304's two reduced cores fused into ONE Prop consumed by ONE theorem: `BCIKS20RemainingCore` ⟹ Theorem 1.5 (nubs, 2026-06-10)

O70 left the strict branch as `StrictCoeffPolysResidualLarge` + `BoundaryProbabilityResidual`; O76/O78 left the boundary as the corrected floor-matched threshold route. This pass welds them: the corrected boundary obligation REDUCES to the same large-sector residual at the working radius, because at any strict radius the §6.2 boundary residual is vacuous (`¬ δ' < 1 − √ρ` unreachable) — so the entire #304 debt is one obligation kind at (at most) two radii per floor cell.

**Bricks (`BCIKS20/RemainingCore.lean`, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings):**
* `BCIKS20RemainingCore k deg domain δ δ'` (line 84) — **the one named Prop**: `StrictCoeffPolysResidualLarge(δ) ∧ StrictCoeffPolysResidualLarge(δ')`.
* `correlatedAgreement_of_remainingCore` (line 149) — **the wiring theorem**: `δ' < 1 − √ρ` + `⌊δ'n⌋ = ⌊δn⌋` + the core ⟹ `δ_ε_correlatedAgreementCurves` at δ with `ε = max (errorBound δ) (errorBound δ')`. Strict interior: conjunct 1 through the O70 front door at the literal `errorBound δ` (boundary residual discharged by vacuity, `correlatedAgreementCurves_strict_of_remainingCore`). Closed boundary (`errorBound δ = 0`): conjunct 2 through the front door at δ' + the O76 floor transport, max realized by the honest `errorBound δ' > 0` (`correlatedAgreementCurves_floorMatched_of_remainingCore`). Glue: `correlatedAgreementCurves_mono_eps` (CA is antitone in ε).
* `remainingCore_boundary_witness` + `correlatedAgreementCurves_boundary_witness` — the core is SATISFIABLE at the O76 closed-boundary instance (ZMod 5, n=4, deg=2, k=1, δ' = 1/4; rate = 1/2 kernel-checked via `rateOfLinearCode_eq_div'`), and the pipeline then exports an UNCONDITIONAL in-tree closed-boundary CA at threshold `max(0, 4/5)` — true content, exhaustively pre-verified by the O78 floor-cell probe (390,625 stacks, fired 60,625, 0 violations). Honest caveat in-file: at toy q both conjuncts hold vacuously (δ not strictly interior; `(1−ρ)/2 = 1/4` exactly) — the witness certifies consistency, not large-q content.

**Probe (`probe_remaining_core_wiring.py`, exact arithmetic, exit 0):** 8,255 grid points, 0 violations — every one of the 8,113 non-lattice boundaries admits the canonical floor-matched strict `δ' = ⌊δn⌋/n` with `errorBound δ' > 0` (24,040 Johnson-window + 8,412 UDR instantiations over q ∈ {5, 97, BabyBear, M61}); `errorBound(boundary) = 0` always (the refuted-shape ε never exported); the 142 lattice points admit NO strict floor-matched radius and stay honestly behind `BoundaryCardLatticeData`; O76 witness reproduced to the digit.

**Where #304 now sits:** the issue can be re-scoped verbatim as "remaining = `BCIKS20RemainingCore` (RemainingCore.lean:84), consumed by `correlatedAgreement_of_remainingCore` (line 149), plus the square-lattice endpoint branch behind `BoundaryCardLatticeData`". Producers target a single obligation kind — `StrictCoeffPolysResidualLarge` at one radius per floor cell — and every discharge flows to Theorem 1.5 with zero plumbing left.
### O79 — the Steps 5–7 capture kernel gets its statement and its first proven sub-obligation: capture IS affine decodability, and the Hensel-stream output shape now reaches the Claim-1 consumer

O71/Hab25Claim1 pinned the #302 chain's single deep input to the per-cell `hsteps57` hypothesis of `claim1_dichotomy` (capture-above-threshold by one degree-`< k` affine pair), but nothing in-tree PRODUCED `AffineCaptured` — the #304/#138/#139 Hensel stream (HPzBridge/HenselDatum, MatchingExtractor, Claims 5.8/5.9) terminates on a different surface: per-`z` decoded-polynomial identities `P z = v₀ + z·v₁`. This pass builds the seam and the kernel's canonical form.

**Bricks (`Hab25CaptureKernel.lean`, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings):**
- `McaDecode` + `McaDecode.mcaEvent` / `exists_mcaDecode_of_mcaEvent` — the polynomial-side destructuring of one `mcaEvent` witness (witness set `S`, degree-`< k` decoded polynomial `P` agreeing with the fold on `S`, the ¬pairJointAgreesOn clause verbatim), FAITHFUL in both directions via `ReedSolomon.mem_code_iff_exists_polynomial`.
- `McaDecode.affineCaptured` — **the capture bridge** (first sub-obligation): a decode whose polynomial is the specialization `a + γ·b` yields `AffineCaptured domain k δ u γ (a,b)` verbatim.
- `affineCaptured_iff_exists_mcaDecode` — **the canonical form**: under the degree bounds, affine capture ⟺ the specialization `a + γ·b` is itself an mcaEvent decode of `γ`. The `hsteps57` residual is now stated on the surface the §5 machinery natively produces.
- `hsteps57_of_decode_family_pinning` / `cell_card_le_of_decode_family_pinning` — the kernel consumer-shaped and composed with the proven dichotomy: per-cell decode family **K1** (`∀ γ ∈ Ecell, ∃ d : McaDecode, d.P = P γ` — production lane: the PROVEN `MatchingExtractor.matchingFactor_dvd_of_orderM_and_count` + GS interpolation; the planned degree-budget root-count brick turned out already in-tree and was composed, not re-proved) plus affine pinning **K4** (`T < |Ecell| → ∃ v₀ v₁ (deg < k), ∀ γ ∈ Ecell, P γ = v₀ + γ·v₁`) give the literal `hsteps57`, hence `|Ecell| ≤ T`. K2 (matching factor) and K3 (cell assignment, `gsFactorIndex`) were already in-tree.

**Falsify-first probe (`probe_capture_kernel_bridge.py`, exit 0):** decode equivalence exhaustive over GF(3) n=3 (2,187 pairs) + 1,000 planted/random GF(5) n=4 stacks (5,000 checks), 0 mismatches; `AffineCaptured` clauses verbatim on 1,678 pinned-cell members, 0 failures; all 839 maximal affine cells obey `|cell| ≤ n`. **Negative control:** in every one of the 839 multi-scalar bad sets the maximal affine cell was a STRICT subset (bad sets up to 4 with unrelated decodes) — the pinning hypothesis is substantive, not auto-true, even at toy q.

**Where the open core sits:** the kernel is now exactly K4's antecedent-to-witness step — `T < |Ecell|` must PRODUCE the affine pencil (BCIKS20 Claim 5.7 pigeonhole incidence + Claims 5.8/5.9 Hensel-branch degree/Z-linearity + Appendix C), per cell of the GS factor decomposition. The #138/#139 HenselNumerator stream's open cores are this statement; everything from its output shape down to `mca_johnson_bound_CONJECTURE` at `parℓ = Fin 2` is machine-checked wiring.
### O79 — de Bruijn capstone step (2) LANDED: the CRT exponent bijection turns subset sums of μ_n into coprime-grid double sums, composed with the O73 engine (and the predecessor's orphan repaired)

O73's "what remains" list left step (2) — the exponent bijection μ_{p^a} × μ_{q^b} ≃ μ_n converting subset sums of μ_n into the grid double sums `crt_fiber_slice` consumes — as ZMod.chineseRemainder bookkeeping. It is now a theorem, with one normalization surprise and one swarm-hygiene catch.

**Normalization (falsified-first, `probe_crt_exponent_bijection.py`, 82,405 checks / 0 violations, exhaustive over all 2^n subsets at n = 12, 15; non-coprime control N=4,M=6 fails as expected):** the brief's Bezout identity ζ^e = ζ^{e_p·u·q^b + e_q·v·p^a} is the INVERSE direction and is never needed. The formalized direction is the forward grid map g(j,c) = j·M + c·N mod n — `ζ^{g(j,c)} = ξ^j·η^c` is trivial exponent arithmetic, bijectivity is injectivity (mod-N/mod-M reduction + coprime unit cancellation) + cardinality.

**Bricks (`CRTExponentGridSum.lean`, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings):**
* `gridMap_inj` / `gridMap_surj` / `pow_gridMap` — the CRT bijection [0,N)×[0,M) ≃ ZMod(N·M) and the intertwining ζ^{g(j,c).val} = (ζ^M)^j·(ζ^N)^c.
* `subset_sum_eq_grid_double_sum` — **the deliverable**: Σ_{e∈S} ζ^e.val = Σ_{(j,c)∈gridSet S} (ζ^M)^j·(ζ^N)^c for any S : Finset (ZMod (N·M)), 0/1 indicator weights (bare Finset.sum over the CRT preimage), over any Monoid+AddCommMonoid — primitivity not needed for the identity.
* `fiber_slice_of_vanishing_subset_sum` — the composition with `crt_fiber_slice`: vanishing subset sums of μ_n exponents have μ_q-shift invariant K-valued fiber sums over their CRT grid set, under the packet-minpoly hypothesis at the second prime. Step (2) is discharged AND typed against the step-(0) engine; steps (1) (packet minpoly over ℚ(ζ_{p^a})) and (3) (disjoint-packet positivity — the genuinely de Bruijn part) remain the open frontier.
* Non-vacuity kernel-checked at a genuine two-prime point (N=2, M=3, ζ=3 ∈ ZMod 7 primitive 6th root, S={0,1,3}, sum value 3 ≠ 0 by `decide`) and at a nonempty vanishing sum (N=1, q=2, ζ=−1, S=μ₂ full).

**Swarm-hygiene catch (the O72-addendum lesson, again, in the other direction):** the rate-limited predecessor lane committed the probe ("orphaned by rate-limit, verified green", 72656ea65) and left `CRTExponentBijection.lean` UNTRACKED in the working tree — its 6 main theorems elaborate axiom-clean, but its non-vacuity example FAILS (7 unsolved-goals errors: positional `by norm_num` arguments elaborated against unassigned metavariables for N, q, Q'), so the file as a whole does not pass the runnable-witness gate. The fix is elaboration-order, not math: pin N, q, Q', i, i', s by name. `CRTExponentGridSum.lean` supersedes the orphan, which should be dropped, not committed. Lesson: a file whose #print axioms lines succeed can still be red — read the whole compiler output, not the axiom tail.
### O79 — de Bruijn step (1) CLOSED: the packet minimal polynomial over the coprime cyclotomic extension is a theorem, and the CRT fiber-slice goes unconditional (nubs, 2026-06-10)

O73 (CRTDoubleSlice) left the engine `slice_of_packet_minpoly` carrying its load-bearing hypothesis — `minpoly K η = Σ_{t<p} X^{tq}` over `K = ℚ(ζ_{p^a})` — as named residual (1). Discharged.

**Bricks (`CRTPacketMinpoly.lean`, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings):**
* `minpoly_adjoin_primitiveRoot_eq_packet` — for distinct primes `p ≠ q`, `b ≥ 1`, primitive roots `ξ` (order `p^a`), `η` (order `q^b`) in ANY char-0 field: `minpoly ℚ⟮ξ⟯ η = Σ_{t<q} X^(t·q^(b-1))` — `Φ_{q^b}` stays irreducible over the coprime cyclotomic extension, in packet form. Engine: `minpoly ∣ Φ_{q^b}` pinched against the totient tower bound `φ(p^a)·φ(q^b) = φ(p^aq^b) = [ℚ(ξη):ℚ] ≤ φ(p^a)·[ℚ⟮ξ⟯⟮η⟯:ℚ⟮ξ⟯]` (`cyclotomic_eq_minpoly_rat` + `adjoin.finrank` + `Module.finrank_mul_finrank` + a hand-rolled ℚ-linear embedding `ℚ⟮ξη⟯ ↪ ℚ⟮ξ⟯⟮η⟯`; the coprime-order product is primitive via `Commute.orderOf_mul_eq_mul_orderOf_of_coprime`), closed by `eq_of_monic_of_dvd_of_natDegree_le` + `cyclotomic_prime_pow_eq_geom_sum`. The brief's worked case is an in-file one-liner: `minpoly ℚ(i) ζ₃ = 1 + X + X²`.
* `crt_fiber_slice_coprimePrimePowers` — **the headline**: `crt_fiber_slice` at `K = ℚ⟮ξ⟯` with the hypothesis GONE. A vanishing double sum `Σ_{(j,c)∈I} ξ^j·η^c = 0` over the coprime grid `range(p^a) ×ˢ range(q^b)` has μ_q-shift invariant fiber sums `Σ_j [(j, i·q^(b-1)+s) ∈ I]·ξ^j` — unconditionally, for any two primitive roots in any char-0 field (ℂ instantiation witnessed in-file).

**Falsify-first probe (`probe_crt_packet_minpoly.py`, exact, no floats, exit 0):** 24/24 — packet form at 9 prime powers; the claim's equivalent tower equality as FULL RANK of the φ(n)×φ(n) CRT power matrix over `ℚ[x]/Φ_n` at 10 coprime pairs up to (27,4)/(25,3); 5 overlap controls all rank-deficient. Honest boundary measured: (6,4) with gcd 2 is still full-rank (`φ(6)φ(4) = φ(12)` — linearly disjoint quadratics), so the obstruction is totient multiplicativity, not gcd per se — the theorem's prime-power coprimality is sufficient, not tight.

**Where the de Bruijn frontier moves:** a parallel lane's `CRTExponentGridSum.lean` (step (2), `fiber_slice_of_vanishing_subset_sum`) carries exactly this minpoly statement as its open `hmin` hypothesis — composing the two (one `rw` of `ζ^(q·Q')` into ξ-form) yields the full two-prime subset-sum fiber slice with no hypothesis; deliberately not built this pass to avoid depending on an unlanded sibling file. After that splice, the only genuinely de Bruijn content left is residual (3): indicator fiber sums force DISJOINT rotated packets (positivity).
### O84 — O77's extraction residual DISCHARGED on δ < d/(3n): the bracket is unconditional there, the bracket window forces r = s, and the (d−1)/2n mechanism is refuted in between

O77 reduced the Theorem-Q upper half to one residual: the affine-root extraction (per stack a pair (e₀,e₁), wt(e₁) ≤ W, every mcaEvent-bad γ a root of e₀+γe₁ at a support coord), with the docstring asserting it "provably true in unique decoding δ < (d−1)/2n". This pass proves it — on the honest window — and measures exactly where the asserted mechanism dies.

**Bricks (`TheoremQUDExtraction.lean`, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings):**
- `exists_affine_pair` — **the extraction, per stack, on 3(n−t) < d** (t = ⌈(1−δ)n⌉₊): with two distinct bad scalars, the affine solve c₁ = (γ₁−γ₂)⁻¹(w₁−w₂), c₀ = w₁−γ₁c₁ of their closeness codewords gives e = u − c vanishing on S₁∩S₂ (wt(e₁) ≤ 2(n−t)); for ANY further bad γ the discrepancy codeword d_γ = w_γ−(c₀+γc₁) has wt ≤ (n−t)+2(n−t) < d, so d_γ = 0 — the decoding law is affine in γ — and ¬pairJointAgreesOn pins a coordinate where e₀+γe₁ = 0 with e₁ ≠ 0. (≤ 1 bad scalar: indicator pair, weight 1. W = 2(n−t)+1.)
- `epsMCA_le_of_uniqueDecoding` — the engine fired with the residual DISCHARGED: ε_mca(C,δ) ≤ (2(n−t)+1)/q for any F-linearly-closed C of min distance ≥ d on 3(n−t) < d. **The library's THIRD upper window, δ < d/(3n) — strictly wider than O78's unconditional d/(4n)**, same O(δn)/q shape; `evalCode_min_weight` + `evalCode_lin_closed` instantiate the Theorem-Q family (d = n−k+1 by root counting).
- `theoremQ_epsMCA_two_sided_uniqueDecoding` — **the bracket with NO extraction hypothesis**: B/q ≤ ε_mca(evalCode H ((r−1)m), δ) ≤ (2(n−t)+1)/q under Theorem-Q hypotheses + the window.
- `window_forces_r_eq_s` — **where the bracket lives**: the lower window (1−δ)n ≤ rm and the upper window 3(n−t) < n−(r−1)m+1 are jointly satisfiable ONLY at r = s. At the O68 point (16,2,8,5) the intersection is EMPTY (lower t ≤ 10, upper t ≥ 14) — the two-sided statement is honest but vacuous in the list-decoding regime, exactly the Johnson-to-capacity gap restated. At r = s the bracket is real: C(s,s)=1 forces B ≥ 1, so 1/q ≤ ε_mca ≤ (2(n−t)+1)/q; hypothesis spine witnessed satisfiable at ZMod 13, H = {1,5,8,12}, (n,s,m,r) = (4,2,2,2), δ = 0 (`theoremQ_ud_window_satisfiable` + the headline fired in-file).

**Falsify-first probe (`probe_ud_affine_extraction.py`, exact GF(97) + Berlekamp–Welch, exit 0):** C1 in-window (RS(16,8), e ≤ 2): 80 stacks, 69 multi-bad, 0 violations (affine law, root property, count ≤ 2(n−t)+1 — bound observed). C2 the hunt (e ∈ {3,4}, i.e. (d/(3n), (d−1)/(2n)]): a g-planting construction (error pair arranged so a third bad scalar decodes to line+g, g a weight-d codeword) **breaks the affine decoding law in 24/24 planted stacks at each e** — O77's docstring mechanism (unique nearest codewords are affine in γ throughout unique decoding) is FALSE strictly past d/(3n). But badCount never exceeded 2(n−t)+1 (max 3 ≪ W), so the extraction STATEMENT — equivalent, via the indicator pair, to the per-stack badCount bound — remains open there; only the codeword-subtraction proof route is closed. C3: r = s instance (97,12,4,3,4), t = 11, δ = 1/12: deep-quotient line carries exactly 1 bad scalar (lower-consistent), 20 stress stacks ≤ 2 (upper-consistent).

**Where the open core sits:** the unconditional upper floor moved from d/(4n) (O78) to d/(3n); the unpinned window is now (d/(3n), δ_wit], with three recorded approaches on one surface (O77 conditional d/(2n) — mechanism now refuted, statement open; O78 unconditional d/(4n); this unconditional d/(3n)). Closing (d/(3n), (d−1)/(2n)] needs a badCount bound that survives non-affine decoding laws — the probe says the count stays small even where the law breaks, so the gap is a counting question, not a structure question.
### O85 — the "zero plumbing" claim made a theorem: the general-L interleaved conversion lands on the epsMCA surface (and the natural-radius hypothesis shape with it)

Duplicate-guard note first: this lane's assigned brick (the mcaEvent↔mcaBadSet bridge + the unconditional δ < d/(4n) window) had ALREADY landed as `EpsMCAInterleavedUD.lean` (commit 7b84d23e7, the O78 entry); it was cold-verified (exit 0, axiom-clean ×7) and not redone — grep the tree, not the log. What the O78 record still owed was its own closing sentence: "any future interleaved-list bound L(2δ) … converts to ε_mca ≤ (1+2δn·L)/q with zero plumbing left" was a REMARK — only the L = 1 slice was a theorem, and the general conversion lived solely on the exact-count surface.

**Bricks (`EpsMCAInterleavedList.lean`, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings):**
* `epsMCA_le_of_interleavedList_card_le` — **the general-L conversion**: PairClosed C (every F-linear code), uniform interleaved list bound L at the collapse floor 2t−n (t = ⌈(1−δ)n⌉₊) ⟹ ε_mca(C,δ) ≤ (1+(n−(2t−n))·L)/|F| — in δ-units (1+2δn·L)/q, the [GCXK25]-shaped conversion of ABF26 §5 stated on the prize surface. O78's window is the L=1 slice; the proof is the bridge + the O74 collapse + `epsMCA_le_of_badCount_le`, three rewrites total.
* `epsMCA_le_of_interleavedList_card_le_doubledRadius` — the same conclusion from a list bound at the **natural radius** ⌈(1−2δ)n⌉₊ — the hypothesis an actual Λ(C^{≡2},2δ) ≤ L statement provides — via two new bricks: `interleavedList_card_anti` (the m=2 interleaved list is antitone in the agreement floor) and `ceil_doubled_radius_le` (**the floor bridge**: ⌈(1−2δ)n⌉₊ ≤ 2⌈(1−δ)n⌉₊ − n for EVERY δ; ℝ≥0 truncation absorbs δ ≥ 1/2).
* `epsMCA_le_interleaved_trivial` + `interleavedList_card_le_sq` — non-vacuity with teeth: every linear code at every δ satisfies the conversion with the trivial L = |C|², so the general theorem is satisfiable far beyond the unique-decoding window (weak, but no window hypothesis at all).

**Falsify-first probe (`probe_epsmca_interleaved_list.py`, exit 0):** floor bridge exact-rational (ℝ≥0/ℕ truncation semantics), 9,420 (n,δ) points, 0 failures; exhaustive F₃ over 3 codes × 8 δ = 110,808 (stack,δ) checks of bridge + antitonicity + the composed natural-radius bound, 0 failures, SATURATED in 8,424 cases; bad counts controlled by full 2^n subset enumeration (7,200 controls, 0 mismatches). Honesty (C3): the L(a₀) ≥ 2 regime occurs 82,035 times in the sweep yet the bad count never strictly exceeds the L=1 form at q=3 — O74's factor-free refinement (#bad ≤ 1 + #Λ₂) remains open and unrefuted; this conversion transports exactly the proven collapse, no more.

**Where this sits:** the upper-half pipeline for #232 is now hypothesis-shaped end to end — any future interleaved (m=2) list bound for explicit smooth-domain RS at radius 2δ, Johnson-type or otherwise, converts to a two-sided-comparable ε_mca ≤ (1+2δn·L)/q in one application with no floor bookkeeping left. The open core is unchanged: produce L(2δ) beyond unique decoding (the gap (d/(4n), δ*] where the O68 lower bound C(s,r)/q lives), or settle O74's factor-free refinement.
### O86 — the LATTICE leaf of the corrected boundary route: quantitative-threshold-alone REFUTED at a lattice endpoint; the leaf PROVEN down to the single §5 extraction residual

O76/O78 left the corrected boundary route fully plumbed off the lattice (floor-matched strict radius + §5 threshold + floor-cell monotonicity) with two named inputs open, one being the genuinely-square lattice branch behind `BoundaryCardLatticeData` (three inputs: two Johnson cardinality bounds + the §5 coefficient-polynomial extraction). At a lattice endpoint the corrected route's machinery is provably unavailable: no floor-matched strict sub-radius exists (`not_exists_lt_floor_eq_of_lattice`) and `errorBound(1−√ρ) = 0` makes the §5-form threshold vacuous — the in-tree threshold→cardinality conversion (`goodCoeffsCurve_card_bounds_of_prob_threshold`) has side conditions requiring `k ≤ k·errorBound·q = 0`. This pass settles what the honest lattice hypothesis is.

**REFUTED (probe witness): the field-quantitative threshold alone does not suffice.** `probe_boundary_lattice_threshold.py` (exact, exit 0; 4 lattice endpoints deg·n square, 2,424 stacks, threshold fired on 355): over GF(11), n=8, deg=2, k=1 (deg·n = 16 = 4², δ·n = 4 integral), the stack u₀=(4,6,1,0,9,2,0,8), u₁=(4,10,0,4,2,7,9,3) has |good| = 10 > 9 = (n+1)k yet NO jointAgreement — and its per-z decoding lists admit a choice P with no coefficient polynomial B (exhaustive). So `Pr > k·(n+1)/q` cannot replace the refuted nonemptiness hypothesis on its own; the §5 extraction is load-bearing. Tightness: the no-jointAgreement maximum |good| EXCEEDS (n+1)k at that point (10 > 9) and saturates it exactly at q=11/n=9/deg=1 (10 = 10). The composite (threshold + extraction) survived all 4 points, 0 violations.

**PROVEN (`BoundaryLatticeThresholdLeaf.lean`, axiom-clean, 0 sorry, 0 warnings): the lattice leaf reduces to the extraction alone.**
* `card_gt_of_prob_gt_latticeThreshold` — `Pr[curve δ-close] > k·(n+1)/|F|` ⟹ `|good| > (n+1)·k`, unconditionally in δ: the positive replacement for the boundary-degenerate errorBound conversion (`latticeThresholdEps = (n+1)/|F| > 0` vs `errorBound(1−√ρ) = 0`).
* `jointAgreement_of_latticeThreshold_of_coeffPolys` — per stack: quantitative threshold + §5 extraction ⟹ `jointAgreement`, at every radius including the exact lattice endpoint, via the in-tree assembly bridge; both `BoundaryCardLatticeData` cardinality inputs are discharged by the threshold.
* `LatticeCoeffPolyExtraction` / `BoundaryCardLatticeThresholdResidual` — the extraction-only residual surface and the corrected lattice-leaf surface (the refuted `BoundaryCardLatticeResidual` with nonemptiness replaced by the quantitative threshold); `boundaryCardLatticeThresholdResidual_of_extraction` closes the latter from the former. Consumer shape: `correlatedAgreementCurves_of_latticeExtraction` yields `δ_ε_correlatedAgreementCurves` with `ε = (n+1)/|F|`.
* Witness namespace: the whole spine fires end-to-end at the genuine lattice endpoint ZMod 11 / Fin 8 / deg 2 — `sqrtRate·8 = √16 = 4` exact, `⌊δn⌋ = δn` (`latticeW`), zero stack has `Pr = 1 > 9/11` and forced extraction (a `natDegree < 2` polynomial vanishing on ≥ 4 of 8 distinct evaluation points is 0); satisfiability certified, no unsatisfiable-hypothesis leaf. (Bookkeeping: the brief's other suggested piece — floor-cell threshold monotonicity — was already landed by a parallel lane as O78/`BoundaryThresholdFloorCell.lean`; duplicate guard caught it before writing.)

**Where the open core sits:** both leaves of the boundary quantization split now rest on exactly one kind of input each — the strict-interior §5 producer per floor cell (non-lattice, O78) and `LatticeCoeffPolyExtraction` at the endpoint (lattice, this entry). Both are the BCIKS20 §5 list-decoding extraction content; the boundary plumbing is complete and the extraction is provably not droppable on either branch.

### O85 — census C3 PROVEN at every radix: single-class words are fiber-aligned (nubs, 2026-06-10)

(Record note first: O70's bookkeeping correction is confirmed from this seat — my O69
commit `2dcc9cfd9` did NOT contain the announced `weight_ge_live_image`; a landing-loop
error dropped the working-tree edit (branch snapshot taken before commit). The content
was independently supplied at every depth by O70's `live_card_le_weight`. Thanks to the
cold audit; loop fixed — snapshots now taken post-staging, pushed diffs verified against
claims.)

New brick `ArkLib/Data/CodingTheory/ProximityGap/SingleClassWeight.lean` (axiom-clean):
the census C3 rigidity (0/95,623 violations in O69's data) is now a theorem, and it
holds at EVERY radix `m ∣ n`, not just 2-powers:

* `single_class_weight`: on a full `n`-th-root domain (`|H| = n = s·m`, `0 ∉ H`), a
  single-coefficient-class word `f = X^r·g(X^m)` has EXACT weight
  `n − m·#{slice zeros in the image domain}` — its zero set is a union of full `m`-power
  fibers (`SmoothFiberCount.preimage_card_eq` does the counting). Single-class = fiber-aligned.
* `dvd_sub_weight_of_single_class`: hence `m ∣ n − w`.

Contrapositive, in branch language: at any weight with `2^ℓ ∤ n − w`, the depth-`ℓ`
fold tree provably keeps ≥ 2 alive branches — narrowness in the coefficient tree exists
ONLY at coset-compatible weights (the O46/O47 boundary), at every level and every radix.
Together with O70's root-coherence theorem the structural story is: low weight forces
slices to share roots; fiber-misaligned weight forbids slice concentration. The
surviving frontier is unchanged and now sharply framed: the per-locus COUNT — bound
#{f : deg f < k, all 2^ℓ slices vanishing on a common locus Z}; for fixed Z the slices
live in root-forced subspaces of total dimension k − 2^ℓ·|Z| (the linear-algebra brick
queued next), and the open content is the union over loci versus the weight filter.

### O69 — CLASS-CHART BOUNDS: the scaling-orbit theorem formalized + the A–S decomposition + a kernel-checked orbit pin (ClassChartBounds.lean)

The provable parts of the O51 program, axiom-clean ([propext, Classical.choice, Quot.sound], 0 sorry):

* **The weighted-scaling fiber bijection as a CARD equality** (`psumFiber_scaling_card`): for λ ≠ 0,
  S ↦ λ·S bijects the (a₁,…,a_t)-power-sum fiber over D₀ onto the (λa₁,…,λ^t a_t)-fiber over λ·D₀;
  on scaling-invariant domains fiber cardinality is a weighted-projective orbit invariant
  (`psumFiber_orbit_card`), the zero class is the fixed point (`zero_fiber_scaling_mem`), and any
  uniform bound need only be certified on an orbit transversal (`psumFiber_card_le_of_orbit_rep`).
* **The conditional Aliev–Smyth uniform bound** (`nonzero_fiber_card_le`): with the named hypotheses
  `ASIsolatedBound` (A–S Thm 1.1, arXiv:0704.1747, isolated torsion points of V(p−a) ⊆ 𝔾_m^w; constant
  abstract) and `CosetFamilyBound` (per-coset tower count, O46–O50), every nonzero-class fiber is
  ≤ C + B uniformly — the isolated ⊔ coset-family decomposition is machine-checked, and transfers
  along whole orbits (`nonzero_fiber_card_le_orbit`).
* **Kernel instance with an honest correction**: at ZMod 13, w = 3, t = 2 the strict probe dichotomy
  ("nonzero ⟹ ≤ 2") is FALSE — but the failure is structured: zero fiber = 4 (`zero_psum_fiber_F13`),
  all nonzero ≤ 4 (`nonzero_fiber_card_le_four_F13`), and the 12 maximal nonzero classes are EXACTLY
  ONE weighted orbit {(5λ,4λ²)} (`nonzero_fiber_le_two_or_rep_orbit_F13`); the part-1 theorem then pins
  the whole orbit from the single decided representative (`orbit_of_rep_card_F13`). Fiber card really
  is an orbit invariant, visible in the kernel. advancesOpenCore=false (A–S itself stays a hypothesis).

### O70 — MIXED-RADIX TOWER LAW CONFIRMED EXHAUSTIVELY at n=12,18,24,36: 86/86 (n,t) fibers set-equal to the divisor-coset prediction (numeric lane). Probes (/tmp/mixed_tower_probe.py, /tmp/mixed_tower_debruijn_check.py; tables /tmp/mixed_tower_results.txt, /tmp/mixed_tower_tables.json) over F_p, p=1000000009 ≡ 1 mod 72 (cross-checked p=2000000089; char-0 conclusive by the Z[zeta] sandwich): for every t=1..n-1, the window fiber {S ⊆ mu_n : e_1=..=e_t=0} EQUALS the disjoint unions of rotated mu_d-cosets, d|n, d>t (generated by the divisibility-minimal divisors > t — up to 3 generators, e.g. Dmin(36,3)={4,6,9}). Pure size-kill law (mu_d dies iff d ≤ t), plateaus between consecutive divisors, totals e.g. |F_36(t)|: 10^6, 22^3, 1036, 100, 22, 10, 4, 2. de Bruijn upgraded from O67's sampling to EXHAUSTIVE censuses: all 10^4 (n=24, full 2^24) and all 10^6 (n=36, complete MITM census) vanishing subset sums decompose into disjoint prime packets; independent backtracking decomposer agrees. Count structure: naive size-multiset formula REFUTED (mu_4-coset = CRT column meets every mu_9-coset = CRT row ⟹ zero weight-13 members at (36,3)); exact law F_n(t) ≅ F_lcm(Dmin)(t)^(n/lcm) verified 25/25 — the numerical shadow of the O68 double-slice/CRT induction, fixing the formalization route for the two-prime full_tower analogue. Bonus: O49 threshold visible (F_13, n=12: 316 vs 100 fiber members). Newton e-window == p-window checked directly at n=12,18 all t.
