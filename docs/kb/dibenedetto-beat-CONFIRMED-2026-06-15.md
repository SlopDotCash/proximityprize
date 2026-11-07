# CONFIRMED: beating di Benedetto for the 2-power subgroup (#444) — exponent 0.9892 -> 0.9583, extends into the prize regime

> **Correction (2026-10-28 audit, T48; see also R-260).** This summary is conditional and over-scoped:
> - **Arithmetic.** The displayed rewrite `|H|^{65/72} p^{1/72} = |H|^{1 − 1/24} p^{1/72}` is false:
>   `65/72 ≠ 23/24`. Only after substituting `p = |H|^4` does `65/72 + 4/72 = 23/24` give `|H|^{23/24}`.
>   The table's conditional `β = 4` / `β = 5` exponents do match the original `65/72` expression.
> - **Hypothesis range.** The [published Theorem 3.1](https://arxiv.org/html/2003.06165v1) assumes
>   `p^{1/4} < H < p^{1/2}`. The `β = 4` row sits at the excluded endpoint, and the `β = 5` row and the
>   `p^{1/7}` threshold lie outside the range. Extending below `p^{1/4}` needs a separately checked
>   argument and its own energy inputs, so "extends into the prize regime" is not established.
> - **Energy inputs need characteristic transfer.** `T_2(μ_n) = 3n² − 3n` and
>   `T_3(μ_n) = 15n³ − 45n² + 40n` are characteristic-zero values. They are not universal identities
>   over `F_p`, and "E_3 is p-INVARIANT" and "EXACT ... to n<=64 incl extreme structured primes"
>   describe selected primes only. Recorded thin cells refute the universal equalities: `μ₃₂ ⊆ F₃₂₉₉₃`
>   has `T_2 = 3744 ≠ 2976`, and `n = 64`, `p = 17318209` has `T_2 = 13632 ≠ 12096` (T91). These cells
>   do not refute every weaker, suitably restricted `O(n³)` hypothesis.
>
> No new analytic estimate is certified by this correction; the note is kept as history.

GOAL ACHIEVED (rigorously verified Phase 2, against the arXiv LaTeX source /tmp/ExpSum-IntSubgr.tex).

## Result
For H = mu_n (2^mu-th roots of unity in F_p), specializing di Benedetto et al (arXiv:2003.06165) Thm 3.1 with
the 2-power subgroup's additive energies:
  max_a |Sum_{x in mu_n} e_p(ax)|  <<  |H|^{65/72} p^{1/72}  =  |H|^{1 - 1/24} p^{1/72},   nontrivial for |H| > p^{1/7}.

| regime | di Benedetto (general) | 2-power mu_n (this) |
|---|---|---|
| beta=4 (H=p^{1/4}) | H^{0.98924} (saving 31/2880) | H^{23/24}=H^{0.9583} (saving 1/24, 3.9x larger) |
| beta=5 (H=p^{1/5}) | TRIVIAL (vanishes, theta<0.2094) | H^{35/36}=H^{0.972} (nontrivial) |
| nontriviality threshold | p^{40/191}=p^{0.2094} | p^{1/7}=p^{0.143} (covers prize q^{1/4..1/5}) |

## Why it works (verified)
- di Benedetto Thm 3.1: 3-fold trilinear descent; T_3(H)<<H^4 (Lemma 4.3, used TWICE: X,Y legs), T_2(H)<<H^{49/20}
  (Lemma 4.2, once: Z leg). Hexp=(6-t3)+(6-t3)+(4-t2)/2; saving at H=p^{1/4} = (Hexp-4)/72; Delta^72 descent is
  ENERGY-INDEPENDENT. General t2=49/20,t3=4 => Hexp=191/40 => 31/2880 (reproduced verbatim).
- 2-power mu_n: T_2(mu_n)=3n^2-3n (t2=2, PROVEN Sidon floor), T_3(mu_n)=15n^3-45n^2+40n=O(n^3) (t3=3). =>
  Hexp=7 => saving 1/24, exponent 23/24, threshold p^{1/7}.
- SUBSTITUTION VALID (verbatim defTm): T_m(H)=#{h_1+..+h_m=h_{m+1}+..+h_{2m}, h_i in H} = additive energy of H
  ITSELF (not a sumset); the step Sum_x J(x)^2 <= T_3(H) is a valid subset inequality. All energy uses are of H.
- NO OBSTRUCTION (5 adversarial candidates all refuted): sumset-vs-set, descent re-introduction, t3 floor,
  antipodal collapse (J(0)^2<=T_3 absorbs -1 inflation), second p^{1/4} barrier (the prefactor is energy-indep).
- Linchpin MACHINE-VERIFIED: T_2,T_3 EXACT (diff=0) to n<=64 incl extreme structured primes (v2 up to 25).

## Status: CONFIRMED conditional on one clean lemma
The only non-rigorous-for-all-n piece: T_3(mu_n)=O(n^3) for ALL n (the "No-Excess" statement). VERIFIED EXACT to
n<=64; the char-0 closed form E_3(mu_n)=15n^3-45n^2+40n is in-tree (#407); E_3 is p-INVARIANT (unlike E_4 which
first fails at structured primes). Proving all-n = a vanishing-sums-of-<=6-2-power-roots count (Lam-Leung style)
= a single Lean No-Excess brick. With it, the beat is unconditional.

## Honest caveat
NOT a prize closure: 0.9583 >> 1/2. The 1/24 saving is energy-driven and capped by the Delta^72 descent (even
the absolute Sidon floor gives only Hexp=7). Reaching exponent 1/2 at beta~4 = the untouched BGK/BCHKS wall;
that requires beating the p^{1/4} trilinear prefactor (Lemma 4.1), which is an arbitrary-set bound with no known
subgroup improvement. This is a genuine SOTA-closeness improvement that newly covers the prize regime, firmly
on the high side of the wall.
