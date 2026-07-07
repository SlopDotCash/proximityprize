# The Ethereum Proximity Prize δ\* — the two open problems, stated for an analytic number theorist (#466, after 14 rounds)

> **⚠️ SUPERSEDED (2026-07-07).** This is the v1 statement. Rounds 15–20 corrected Problem B
> (the all-offset form is FALSE — diagonal spike; the live form is the off-diagonal
> `AwaySupBound`), added an unconditional `n√q` partial theorem, a two-sided tower⟺sup
> equivalence (constant 3) at depth ≥ log₃ q, and reduced the r=2 rung to a pinned Stepanov
> formalization gap. **Read the definitive current statement:
> `docs/kb/deltastar-466-expert-statement-v2-2026-07-07.md`.** The round-15 correction appendix
> below is retained but v2 subsumes it.

This is the campaign's definitive, corrected problem statement. Fourteen rounds of route-elimination
(as theorems), machine-checked reduction, and adversarial verification have reduced the $1,000,000
grand challenge to **two precisely-stated, independent, recognized-open problems in analytic number
theory.** This note states them for an expert, with the exact machine-checked reduction chain and an
honest account of what is known. Nothing here is claimed proven that is not axiom-clean in Lean; the
two cores are named open `Prop`s.

## 0. The reduction chain (machine-checked, both layers)

For explicit smooth-domain Reed–Solomon codes `RS[F_q, μ_n, k]` in the window interior, `n = 2^μ ≈
2^30`, `q ≈ n·2^128`, `p ≈ n^4` (β ≈ 4), `μ_n ⊊ F_p^×` the order-`n` dyadic subgroup, index `m =
(p−1)/n ≈ 2^128`:

```
   δ*-floor  ⟺(outer iff, BOTH directions, axiom-clean: _TwoSidedCapstone.lean, round 14)
   WorstCaseIncidenceBounded C δ E   (= ∀ stacks u, #bad-scalars(u) ≤ E,  E ≈ q·ε* ≈ n)
   ⟸(one-directional named glue IncidenceFromWallGlue: the √q·B budget bookkeeping)
   Problem A (WallHolds)  ∧  Problem B (HyperplaneCancellation)
```

The outer equivalence is machine-checked in both directions. The inner step is one-directional (its
reverse-side non-vacuous budget is exactly Problem B). Problems A and B are **independent** — round 13
proved `A ⇏ B`, round 14 proved `B ⇏ A` (`_R14SupNormWeakerThanWall.lean`); neither is the sole
bottleneck. Both are ON-BGK: instances of the thin-2-power square-root-cancellation problem, best
proven `n^{1−o(1)}` (BGK) at β = 4, target `≈ √n`.

---

## 1. Problem A — the moment tower (WallHolds): DC-subtracted char-p Wick bound at logarithmic depth

Let `η_b = Σ_{x∈μ_n} e_p(bx)` be the Gauss period (the non-principal eigenvalue of the generalized
Paley graph `Cay(F_p, μ_n)`; Liu–Zhou Thm 115). Let `E_r = (1/q)·#{(h_1,…,h_{2r}) ∈ μ_n^{2r} :
Σ_{i≤r} h_i ≡ Σ_{i>r} h_i (mod p)}` be the `2r`-th additive-energy moment.

> **PROBLEM A.** For every `r` up to `r ≈ ln q ≈ 89`, the DC-subtracted moment satisfies the
> Wick/Gaussian bound
> ```
>       A_r := q·E_r − n^{2r}  ≤  q·(2r−1)‼·n^r      (equivalently  W_r ≤ n^{2r}/p, W_r ≥ 0).
> ```

`W_r = E_r^{(p)} − E_∞` is the **wraparound count** — the number of sparse ±1 relations of `2^μ`-th
roots of unity that vanish mod `p` but not over `ℤ[ζ_n]` — a **nonnegative integer count** (so there
is nothing to cancel: Problem A is an *unsigned* counting inequality, not an oscillatory-sum bound;
`_WallBetaPlusOneLocalization`). Equivalent forms (dossier §2): the effective worst-case vertical
Sato–Tate; the wraparound variance law; the early Jacobi turnover `k* = O(log p)`.

- **What Problem A gives (machine-checked):** `WallHolds ⟹ M := max_{b≠0}‖η_b‖ ≤ √(2e·n·(ln q+1))`
  (`_MomentOptimizedSupNorm.lean`, round 13, axiom-clean — the moment method: 2r-th root, minimize
  over `r ≈ ln q`). So A is *strictly stronger* than the Paley-graph sup-norm bound `M ≤ 2√n`
  (`M` is a lossy projection of the whole moment profile; the interchange is one-way, round 14).
- **Status:** open; fixed-`r` closes unconditionally at every scale (canonical width-four ladder
  n=16…32768); the entire residual is the **joint limit** `r ≈ ln q` *and* `n = 2^30`. The frontal
  norm/conjugate-count assault reduces to it: the sole unconditional tool `|N(α)| ≤ (2r)^{n/2}` is
  vacuous at the prize for `n ≥ 64` (`gate_vacuous_at_prize`, round 12). Raw (DC-*un*subtracted)
  `E_r ≤ (2r−1)‼·n^r` is FALSE past the DC crossover `r ≈ β` — the DC subtraction is mandatory.

---

## 2. Problem B — the worst-case incidence cancellation (HyperplaneCancellation): BCHKS Conjecture 1.12

Let `H` be the far-coset frequency hyperplane (a subgroup of `F_p^×` of index `deg`, `|H| ≈ q/deg`),
and `I_H(s_0) = Σ_{b∈H} conj(η_b)·ψ(b·s_0)` the signed incidence sum.

> **PROBLEM B.** For the *worst* offset `s_0`,
> ```
>       ‖I_H(s_0)‖  ≤  √|H| · M       (i.e. √q·B — full square-root cancellation over the hyperplane).
> ```

This is the per-frequency square-root cancellation of the Paley/BCHKS Conjecture 1.12 — a
**phase-correlation** statement about the *joint* configuration of the Gauss-period phases over the
hyperplane.

- **Why B is NOT implied by A (machine-checked identity, round 13):**
  `Σ_{s_0} ‖I_H(s_0)‖² = q·Σ_{b∈H}‖η_b‖²` (`_R13HyperplaneSecondMoment.lean`, pure orthogonality). So
  the sup-norm `M` (all Problem A gives) controls only the **`s_0`-average** of the incidence:
  `‖I_H‖ ≤ √|H|·M` *on average*. The far-coset adversary picks the **worst** `s_0` — which reaches the
  diagonal Gauss-period `|H|·M`-scale — and a same-moduli two-spectra witness (identical `{‖η_b‖}`,
  hence identical `M`, but worst-case incidence differing by `√|H|`) proves the worst-case value is
  provably *not a function of* `M`. B is a genuinely distinct, phase-sensitive input.
- **Status:** open (BCHKS Conjecture 1.12); the naive triangle bound gives only `|H|·M` (the vacuous
  `q·B` budget); the `√q·B` cancellation is the recognized open floor. The in-tree `V=F` syndrome
  hyperplane is degenerate (`{b:b·s_1=0}={0}`), so B is stated for the nontrivial higher-dimensional
  analogue (the honest model of the incidence geometry).

---

## 3. Why these two, and why independent

The 14-round campaign's cartographic result is that **every** approach to δ\* funnels to A, to B, or
to their conjunction — and that A and B are the two irreducible, orthogonal faces:

- **A is the phase-blind (moment/energy) face**; **B is the phase-correlation (sup-over-offset) face.**
  `A ⇏ B` (moments are phase-blind); `B ⇏ A` (a single spectral radius is a lossy projection of the
  moment tower). No named glue reduces one to the other.
- **The no-go landscape is complete** (dossier §4, §21): the Meta-Theorem caps every second-order
  method at Johnson/√p; the Tetrachotomy admits no fifth door (every p-adic / cohomological /
  model-theoretic / spectral functor lands in an archimedean-place-free or signed target, but the
  wraparound is an unsigned archimedean modulus — round 11); the AUP quantifies the phase deficit.
  All Tier-1/2/3 levers, seven out-of-domain complete-proof chains, the entire line-list closure
  route, the floor-successor conjecture (refuted at n=64), and both round-10 machineries
  (automatic-sequence, transfer-operator) are decided, each with a countermodel, exact identity, or
  standing filter.

## 4. What an expert would need to supply

- **For Problem A:** a bound on short (`≤ 2 ln q`-term) `±1`-relations of `2^μ`-th roots of unity
  vanishing mod `p`, staying within `K^r` of the Gaussian (Wick) rate uniformly to `r ≈ ln q` at
  `n = 2^{30}`, `p ≈ n^4`. The char-0 analogue is a theorem (Lam–Leung / Bessel); the residual is
  purely the char-p wraparound at logarithmic depth. Must use thinness (`n ≤ p^{1/4}`)
  load-bearingly — `Sh > √2` occurs only below β = 4.
- **For Problem B:** worst-case square-root cancellation of the signed Gauss-period incidence over the
  far-coset hyperplane — a joint/phase statement no moment bound reaches. This is BCHKS 1.12 in the
  thin-2-power regime.

Both are recognized ≈25-year-open analytic number theory. The campaign's product is the complete,
machine-checked reduction *to* them, with route-elimination proven as theorems — **not** a solution.

## 5. Honesty contract

Nothing above is claimed proven that is not axiom-clean in Lean (`#print axioms ⊆ {propext,
Classical.choice, Quot.sound}`, no `sorryAx`). Problems A (`WallHolds`) and B
(`HyperplaneCancellation`) are named open `Prop`s. The reduction's outer layer is machine-checked both
ways; the inner layer is one-directional named glue whose reverse is exactly Problem B. **CORE OPEN,
ON-BGK. No fabricated closure.**

<sub>🤖 #466, 2026-07-04, consolidated after 14 rounds (Fable rounds 1, 10–14; the parallel session's
rounds 2–9). The single dossier is `docs/kb/deltastar-DOSSIER-v3-2026-07-01.md` (§0–§24); the Lean
capstones are `Frontier/_WallCapstone.lean`, `_TwoSidedCapstone.lean`, `_MomentOptimizedSupNorm.lean`,
`_R13HyperplaneSecondMoment.lean`, `_R14SupNormWeakerThanWall.lean`.</sub>

---

## ⚠️ Round-15 correction (2026-07-07) to Problem B's statement

Problem B as stated above (worst case over ALL offsets `s₀`) is **false for a trivial structural
reason**: the χ₀/diagonal term gives `I_H(s₀) ≈ |H|` at every `s₀ ∈ μ_n` (exactly
`I_H(s₀ ∈ μ_n) = (Σ_{b∈H}‖η_b‖²)/n`; Lean brick `_R15GaussDecompDiagonalSpike.lean`,
real-build axiom-clean). Round 13's "worst-case reaches the diagonal `|H|·M` scale" is this spike.
**The correct open statement is off-diagonal:**

> **PROBLEM B (corrected).** For every `s₀ ∉ μ_n` (equivalently, after χ₀-subtraction),
> `‖I_H(s₀)‖ ≤ C·√|H|·M` with `C = O(1)` (measured `C ∈ [0.61, 1.61]` at all accessible scales).

Known unconditionally (round 15): `‖I_H(s₀ ∉ μ_n)‖ ≤ n√p` (Gauss-sum decomposition + triangle),
which beats the trivial `|H|·M` budget by `n^{3/2}/deg` at prize scale. The corrected B reduces
per-χ (a `√deg` loss) to square-root cancellation of the twisted thin-subgroup sums
`T_χ(s₀) = Σ_{x∈μ_n} χ̄(s₀−x)` — the same thin-2-power wall in a cleaner scalar family — and its
diagonal-subtracted `s₀`-moment tower obeys Wick empirically at every accessible scale
(`_R15IncidenceMomentInterchange.lean` has the conditional interchange: a proven
diagonal-subtracted Wick tower gives corrected B up to `√(2e·ln q)`). See dossier §25.
