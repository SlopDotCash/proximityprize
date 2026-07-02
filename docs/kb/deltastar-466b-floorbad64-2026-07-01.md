# #466 round 2, lane FLOOR64 — the uniform-in-μ floor-bad characterization at rung n = 64

Date: 2026-07-01.  Status: **probe + KB note (no prize claim)**.  Dossier v3 §9 / Tier-1 item 4.
Probe: `scripts/probes/probe_466b_floorbad64.py` (output `scripts/probes/_out_466b_floorbad64.txt`).
Scanner of record: `scripts/probes/floor_scan_exact.c` (source reused as the definition; no C
compiler on this box, so the Python engines below are a *reconstruction* and were therefore
ground-truth-revalidated in full before any n=64 claim, per the lane contract).

## 0. Verdict table (headline)

| rung | prime(s) | method | verdict |
|---|---|---|---|
| n=16 | 17 | full scan (2304), rank port AND vectorized q-engine | **BAD, 160/2304** (= recorded ground truth) |
| n=16 | all other 29 split primes ≤ 1601 (incl. every n=64 target) | full scans | all **good** (law: floor-bad(16) = {17}) |
| n=32 | 97 | full scan (15,366,400) | **BAD, exactly 32 realizable** (NEW exact count; C scanner had short-circuited); all 32 = ONE translation orbit; rank-port cross-checked on all 32 |
| n=32 | 193, 257, 353, 449, 577, 673 | full scans | all **good** (= recorded ground truth, revalidated) |
| n=32 | 641, 769, 1153, 1217 | full scans | all **good** (**NEW coverage**; floor-bad(32) = {97} now verified through 1217) |
| n=64 | 193 (conjectured bad) | see §3 — batteries only | **UNDECIDED at this compute** (no bad pattern found; full enumeration infeasible) |
| n=64 | 257, 449, 577, 641, 769, 1153, 1217 | sampling + tower kills | **no bad pattern found** (coverage quantified in §3; NOT a good-verdict) |

**The conjecture floor-bad(64) = {193} is neither confirmed nor refuted.** The n=64 pattern
space is `4·C(16,12)²·C(16,8)² = 2,194,622,670,240,000 ≈ 2.2·10¹⁵` — full enumeration is
out of reach (the n=32 scan rate here was ~15.4M patterns / 50-110 s; n=64 patterns are ~4×
costlier ⇒ a full n=64 scan is ~10⁷ CPU-hours). Both one-sided directions that WERE feasible
were executed: (i) massive validated coverage batteries at 193; (ii) refutation hunts at the
seven successor primes. Neither fired.

## 1. The q-formulation (engine of this lane; proven equivalent to the rank scanner)

`rank[M_A] = rank[M_A|b_A]`  ⟺  ∃ f (deg < n/2), g with `x^{3n/4} + g·x^{n/2} − f(x) = 0` on A
⟺  ∃ monic q, deg q = D := 3n/4 − |A|, such that h = q·P_A has zero coefficients at every
degree in (n/2, 3n/4), where `P_A = Π_{a∈A}(x − a)` (h vanishes on the |A| distinct points of
A iff P_A | h; the coefficient window IS the binder shape). Since P_A is monic the top D
window rows are unit-triangular in q, so **q is uniquely determined by back-substitution** and
realizability = vanishing of the remaining `n/4 − 1 − D` residuals (n=16: 1, n=32: 3, n=64: 7).
No rank computation, fully vectorizable. Validated three ways: (a) exact port of the C rank
scanner agrees pattern-by-pattern at n=16 on 12 primes; (b) scalar-q vs rank-port vs batched
engine agree on random patterns at (17,16), (97,16), (97,32), (193,32), (193,64), (257,64);
(c) reproduces both recorded ground truths exactly (17 → 160/2304; 97 BAD / six goods at n=32).

## 2. Structure of the n=32 badness at 97 (new data)

- Exactly **32 realizable patterns = one translation orbit** (j ↦ j+1 on discrete logs;
  translation-invariance of realizability is a one-line theorem: x ↦ g0⁻¹x preserves the
  binder coefficient shape). Orbit representative (c0 = 0):
  `A = {0,1,3,6,8,9,11,12,16,17,18,19,20,21,22,23,24,25,29,30}` (contains a 10-run).
- **Not** antipode-closed; **no** Galois image (j ↦ uj, u ∈ {3,5,7,9,15}) is bad — the orbit
  is rigid, not symmetric.
- Witness autopsy at the rep: q = x⁴ + 73x³ + 25x² + 49x + 21 has **no roots in F₉₇**, dense
  coefficients, no subfield/coset structure; binder g = 71. The mechanism is an opaque rigid
  rank-degeneracy — there is **no transferable algebraic template** (this is why the 193-side
  of the n=64 rung resists: nothing to lift).
- Bad-prime pattern density at n=32 is 32/15.4M ≈ 2·10⁻⁶ (vs 160/2304 ≈ 7·10⁻² at n=16):
  the badness *sparsifies* rapidly up the tower. If the trend continues (~1 orbit at the bad
  prime), the n=64 bad set at 193 would have density ~10⁻¹³ — invisible to any sampling.
  **Uniform sampling can support but never decide the BAD direction at n=64.**

## 3. The n=64 rung: what was actually established

### 3.1 Tower-reduction theorem (proved in §4; machine-corroborated)
Any pattern closed under the antipode x ↦ −x (exponents j ↦ j+32) is realizable at rung 64
iff its halved image is realizable at rung 32 at the same prime (h ↦ h_even = H(x²) keeps the
binder window and halves the rung; conversely lift). Iterating: x²-fiber-pure patterns reduce
to rung 32, x⁴-fiber-pure to rung 16. **Corollary of the full scans above:** at ALL eight
n=64 target primes (193, 257, 449, 577, 641, 769, 1153, 1217), every antipode-closed n=64
pattern is NOT realizable (all eight are n=32-good and n=16-good). Machine corroboration:
none of 97's 32 bad n=32-patterns is antipode-closed (97 is n=16-good), as predicted.
**Consequence: any n=64 badness must be antipode-ASYMMETRIC** — this kills the natural
symmetric lift `S ↦ S ∪ (S+32)` as a construction and prunes the search to asymmetric strata.

### 3.2 Coverage batteries at p = 193 (found-bad would be certain; not-found = stratum coverage only)
- **Uniform**: 12,000,000 patterns, 0 realizable (fraction 5.5·10⁻⁹ of the space).
- **Perturbed-lift**: antipodal lifts of ALL 32 bad 97-patterns, each perturbed by 1–3
  asymmetric in-class swaps: 150,000/seed × 32 seeds = 4.8M near-lift patterns, 0 realizable.
  (The unperturbed lifts are dead by §3.1.)
- **Run-biased strata** (97's rep has a half-length run): patterns containing a random cyclic
  20-run and 24-run: 1.5M each, 0 realizable.
- All engines used were the ground-truth-revalidated ones of §1.

### 3.3 Successor primes (the feasible refutation direction — did not fire)
1,000,000 uniform n=64 patterns at each of 257, 449, 577, 641, 769, 1153, 1217: 0 realizable.
Plus the §3.1 kills of all symmetric strata at every one of them. **No refutation certificate
was found**; a single realizable pattern at any of these would have refuted the smallest-prime
law with a checkable certificate — the probe emits one automatically (`emit_certificate`,
independently verified through the rank formulation) if a future run fires.

## 4. Proof of the tower reduction (elementary, recorded for reuse)

Let A ⊆ μ_n be antipode-closed, h = x^{3n/4} + g·x^{n/2} + f (deg f < n/2, sign convention
h|_A = 0). Both h(x) and h(−x) vanish on A (−A = A); h_even := (h(x)+h(−x))/2 = x^{3n/4} +
g·x^{n/2} + f_even (n/4 even degrees survive: 3n/4 ≡ 0, n/2 ≡ 0 mod 2) vanishes on A and is a
polynomial in x²: h_even = H(x²) with H = y^{3m/4} + g·y^{m/2} + f̃ (deg f̃ < m/2), m := n/2 —
exactly the rung-m binder shape — and H vanishes on the squared image A² ⊂ μ_m, which has the
same class profile and adjacency (squaring halves discrete logs *after* the pairing j ~ j+n/2;
classes mod 4 map to classes mod 4 with rotation preserved). Conversely if H is a rung-m
witness on B ⊂ μ_m, then H(x²) is a rung-n witness on the preimage (an antipode-closed rung-n
pattern). ∎  (At rung 64 with q-degrees: 40-point antipode-closed pattern ↦ 20-point rung-32
pattern; the parity-split of the constraint rows shows the same thing on the q-side.)

## 5. Honest scope, and what would decide the rung

- **What this lane proved**: the reconstruction-validated verdicts of §0 (all "full scan"
  rows are exact, two-engine, cross-checked); the tower-reduction theorem; the new exact
  count + orbit structure at 97; floor-bad(32) = {97} through 1217.
- **What it did not prove**: any n=64 verdict at any prime. "0 hits in N samples" at 193 is
  NOT evidence of 193-goodness (the conjecture predicts 193 is BAD via ~a rigid orbit that
  sampling cannot see); at the successor primes it is likewise only coverage.
- **What would decide it**: (BAD side at 193) an algebraic construction of the rigid orbit —
  the 97 autopsy shows no visible template, so this needs a new idea, e.g. treating the
  35-row rank-deficiency-7 condition as an intersection in the Grassmannian of the moment
  curve, or the DFT reformulation: ∃ vector supported on [0..31]∪{32}∪{48} (34 positions)
  whose μ_64-DFT vanishes on an adjacent (12,12,8,8) 40-set — a vanishing-structure /
  uncertainty question over F_p where the composite modulus 64 makes the naive Chebotarev/
  Tao-type uncertainty fail. (GOOD side at 193, = refuting the law) full enumeration, ~10⁷
  CPU-hours — a GPU port of the q-engine (7 residuals, no linear algebra) at ~10⁹ patterns/s
  would need ~25 days·GPU: *borderline feasible as a dedicated campaign, not in-session*.
- **Probe-regime note**: the #400 trap (p ≳ n⁴, decorrelated directions) governs character-sum
  probes; floor-bad is a rank/divisibility object whose conjectured law is *about* the
  smallest split primes — small p here is the object, not an artifact. μ_64 is proper
  (index ≥ 3) in every field used.
- **Meta-verdict unchanged** (dossier §9): floor-goodness is necessary-not-sufficient for the
  δ*-pin; this rung is obstruction-cartography, not a prize route.

## 6. Reusable artifacts

- `probe_466b_floorbad64.py` subcommands: `selftest`, `validate16`, `scan32 <p>…`,
  `scan16grid`, `sample64 <p> <N> [uniform|nearsym] [seed]`, `runbias64 <p> <N> <runlen>`,
  `bad32 <p>` (orbit analysis), `lift64 <p>`, `certify64 <p> <c0> <j,…>` (independent
  rank-formulation certification of any claimed pattern).
- The q-engine (unique-q back-substitution) is a ~30× speedup over rank scanning and is the
  right kernel for any future GPU full-enumeration campaign at n=64.
