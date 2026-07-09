# #407 — path `gauss-sum-explicit-1712`: Mohammadi/KU explicit Gauss-sum bounds are VACUOUS at the prize (sharpened wall)

Date: 2026-06-13. Honesty contract applies — this is a NEGATIVE result (precise obstruction), not a closure.

## Assignment
Use improved Gauss-sum bounds (arXiv:1712.00761, Mohammadi) + ultra-short trace sums
(arXiv:2302.13670, Kowalski–Untrau) for the incomplete-sum sup-norm
`M = max_{b≠0} |∑_{x∈μ_n} ψ(bx)|`, in the prize regime. Decide if non-vacuous vs trivial `n` / Weil `√q`,
and how close to `√(n log(q/n))`.

## Papers (now ON DISK + read; the prompt's tags resolved):
- **1712.00761 = Mohammadi, "Improved bounds on Gauss sums in arbitrary finite fields"** (v2 2018).
  Object `S_N(a) = ∑_{x∈F_q} ψ_a(x^N)`. **Key identity (eq 3): `S_N(a) = 1 + N·S(a,H)`**, `H` = group
  of `N`-th powers, `|H| = (q-1)/N`, `S(a,H) = ∑_{h∈H} ψ_a(h)`. Main results: Thm 2 eq (18)
  `max|S_N| ≪ q^{(7-2η)/8} N^{(1+η)/4} + q^{7/8}N^{8/33}` (η=1/33); Cor 7 best line `q^{229/264}N^{17/66}`.
  **Nontrivial only for `N ≤ q^{1/2+1/68}`** (i.e. `|H| ≥ q^{1/2-1/68} ≈ q^{0.485}`). Engine = sum-product
  additive-energy `E^+(H) ≤ |H|^{3-2η}` (Zhelezov), valid only `|H| ≥ q^{1/2}`.
  **Lemma 14 (the master bridge, = standard [5 eq 3.7]):**
  `max_a |S(a,H)| ≤ min{ (q·E^+(H)/|H|)^{1/4}, q^{1/8}·E^+(H)^{1/4} }` — this is exactly the in-tree
  L⁴/L⁸ moment arrow `B ≤ (q·E_r)^{1/2r}` at r=2,4.
- **2302.13670 = Kowalski–Untrau, "Ultra-short sums of trace functions".** Purely DISTRIBUTIONAL
  (equidistribution to a sum-of-Sato–Tate measure) at **fixed degree `d`, field `→∞`**. Moment formula
  `E(|Φ(U)|²)=|Z_g|=d` is the variance, NOT a pointwise bound. **No sup-norm lever; wrong (fixed-d) regime.**
  Its effective/quantitative companion is 2505.22059 (already proven vacuous, synthesis §7).

## REGIME CORRECTION (load-bearing; the prompt's prose was internally inconsistent)
Prompt prose said "m=(q-1)/n~2^128 CONSTANT ⟹ μ_n positive-proportion, n≫√q". This is **self-contradictory**:
m constant ⟹ n = (q-1)/m ≈ q/2^128, so **n/q = 2^{-128} (TINY proportion)** and **n=2^a ≪ √q=2^{(a+128)/2}
ALWAYS** (a≤40 ⟹ a < (a+128)/2). The hard params (n=2^a a≤40, q=n·2^128, m=2^128) are unambiguous and
agree with RESEARCH_SYNTHESIS_407: **μ_n is THIN**, `n = q^δ`, `δ = a/(a+128) ∈ [0.07, 0.238]` — far below
`q^{1/4}`, below BGK `q^{3/7}`, astronomically below Mohammadi's window `q^{0.485}`. Do NOT treat as positive-proportion.

## DICTIONARY (verified)
`μ_n` (my dyadic subgroup, |·|=n) = Mohammadi's `H` ⟹ Mohammadi's index `N = (q-1)/n = m ≈ 2^128`.
`M = max_b|η_b| = max_a|S(a,H)| = (1/m)·max_a|S_m(a) − 1|`.

## VERDICT: every Mohammadi estimate is VACUOUS at the prize (probe-verified, scripts/probes/probe_407_mohammadi_*.py)
1. **Out of range.** Prize needs `N=m=2^128`; Mohammadi valid only `N ≤ q^{1/2+1/68} ≈ 2^86`. Gap `~2^42`.
   Mohammadi controls LARGE subgroups (`|H| ≥ q^{0.485}`); the prize μ_n is the OPPOSITE tiny corner.
2. **Even extrapolated**, Cor 7 top line `q^{229/264}N^{17/66}/N` gives `M ~ 2^{24.7}..2^{50.7}` (a=10..40),
   ≥ trivial `n=2^a` for every a — worse than trivial.
3. **Weil/completion** (eq 4) gives `M ≤ ((m-1)q^{1/2}+1)/m ~ √q = 2^{(a+128)/2}`, which is `2^{(128-a)/2}`
   times WORSE than trivial `n`. Completion loses the whole point in the thin regime.
4. **Theorem 3** (incomplete consecutive-power sums) ≥ `q^{1/8} = 2^{(a+128)/8}` > n for a<18; also vacuous.

## THE SHARP NEW NUMBER (genuine, machine/probe-verified) — the deep-moment wall in the CONSTANT-m regime
Lemma 14 generalizes to `M ≤ (q·E_r(μ_n))^{1/2r}` (the in-tree arrow). With the PROVEN char-0 energy
`E_r(μ_n) = (2r−1)!!·n^r` (Lam–Leung; defect `n^{2r}/q < 1` here for a≤40, so the char-0 value is EXACT):
`M ≤ q^{1/2r}·n^{1/2}·((2r−1)!!)^{1/2r}`. Reaching `√(n ln q)` needs `r* = ½ ln q ≈ 44–58`, but the char-0
energy is valid only to `r_max = 1 + 128/a ∈ [4.2, 13.8]` (where `n^r < q`). **Depth deficit
`r*/r_max ≈ 3.5–13.9`** (grows in a). At the deepest reliable `r = r_max`, `q^{1/2r_max} = n^{1/2}`, so
`M ≲ n^{1/2}·n^{1/2} = n` — essentially TRIVIAL.

**This is STRICTLY WORSE than the synthesis's `n^{3/4}` wall** (`CharSumMomentDeepWall.lean`), because that
file assumes `p ~ n^5` (r_max=7), whereas the corrected constant-m regime has `p ~ n·2^128` (p exponentially
larger rel. to n) ⟹ `r_max` smaller ⟹ moment stalls at `n`, not `n^{3/4}`. Same wall, sharper in this regime.

## BOTTOM LINE
The assigned explicit-Gauss-sum tool addresses the WRONG corner of the subgroup-size axis (large H);
the prize μ_n is thin. Both papers are vacuous at the prize: Mohammadi by range + sum-product needing
`|H|≥q^{0.485}`; KU by being fixed-degree distributional with no sup-norm. **No new bound on M; no closure.**
The single transferable lever (cross_path_lever): Lemma 14 = `M ≤ (q·E_r)^{1/2r}` is the exact same
energy-to-house arrow as the in-tree moment method, and the char-0 energy `E_r=(2r−1)!!n^r` (clean here,
defect<1) is EXACT to `r_max=1+128/a` — i.e. the ENTIRE residual is the char-0→char-p energy transfer at
deep `r ∈ (r_max, ½ln q]`, the named open core (face 3, `GaussianEnergyBound`). Confirms, does not move, the wall.
