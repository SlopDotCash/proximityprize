# N4-leeyang — the Gauss period polynomial as root location: complete chain, and its death

**Issue #466 · novel-math lane N4 (Lee-Yang / geometry of polynomials / root location) · 2026-07-02**

Status: **COMPLETE CHAIN, SELF-REFUTED at step 7.** The lane converts the prize sup-norm into the
house of one integer polynomial and develops the full Fujiwara / Lee-Yang / Newton apparatus to
the prize point. It dies exactly where every other lane dies — the deep-moment wall — and it is
killed *twice on the way* (max-form root bounds are worse than Johnson; shallow-weighted tests
are blind to the lone spike). N4 is the **root-location twin** of the round-1 CMK lone-spike
refutation: the extremal object is a lone spike, and the entire real-rootedness / Newton-
inequality / Laguerre–Pólya machinery contributes **0 bits**.

Probe: `scripts/probes/probe_466_novel_N4_periodpoly.py` → `_out_466_novel_N4_periodpoly.txt`
(exact integer power sums, Newton coefficients, Fujiwara profile, K=2 integer countermodel,
K=4 spike+bulk class floor, prize-point depth table). Prior art it extends:
`Frontier/_wf9G3_periodpoly_coeff_nogo.lean` (#444 G3, axiom-clean) and the R1 CMK lone-spike
refutation (`docs/kb/deltastar-466-cmk-refuted-2026-07-01.md`).

---

## The key observation (the lane's premise, which is TRUE and exact)

For `μ_n ⊂ F_p^×` of order `n = 2^μ`, `p ≡ 1 (mod n)`, `m = (p-1)/n`, the periods
`η_b = Σ_{x∈μ_n} e_p(bx)` are **constant on the `m` cosets of `μ_n`** (`η_{bt}=η_b` for `t∈μ_n`)
and **real** (`-1∈μ_n` since `n` even ⟹ `η_{-b}=η_b=conj(η_b)`). The `m` distinct values
`η_0,…,η_{m-1}` are the conjugate **Gaussian periods** generating the unique degree-`m` subfield
of `Q(ζ_p)`, hence the roots of a **monic, integer, totally-real** polynomial
`P_m(x)=∏_j(x-η_j) ∈ Z[x]` of degree `m`. Therefore

> **M(n,p) = max_{b≠0}|η_b| = max_j|η_j| = house(P_m).**

The sup-norm IS root location of one integer polynomial. This is genuinely a new encoding (only
#444 G3 touched it, and only for the max-form bound). Everything below is honest development of
that encoding to its exact death.

---

## The complete step-numbered chain (with prize-point constants)

Prize point: `n = 2^30`, `p ~ n^4 = 2^120` (β=4 diagonal) and the exact prize index `m = 2^128`
(`p ~ 2^158`). Target `C·√(n·log(p/n)) = √(n ln m) ≈ 2^18`.

**Step 0 — reduction (PROVEN, exact).** `M = house(P_m)`. Tool: Galois theory of `Q(ζ_p)/Q`.
Constant: `deg P_m = m ∈ {2^90 (β4), 2^128 (prize)}`, monic ∈ `Z[x]`, all roots real.

**Step 1 — power sums, char-0-clean at shallow depth (PROVEN, exact).**
`s_r := Σ_j η_j^r = (p·N_0(r) − n^r)/n`, `N_0(r)=#{x∈μ_n^r : Σx_i≡0}`. Tool: additive-character
orthogonality. Exact identities (verified): `s_1=−1`, `s_2=p−n`. Probe confirms `N_0(4)=3n²−3n`
(char-0 Wick, zero wraparound excess) at n=8,16.

**Step 2 — Newton triangularity (PROVEN, exact).** `e_1,…,e_K` ⟺ `s_1,…,s_K` bijectively via
Newton's identities. **Consuming coefficients `e_1..e_K` = consuming moments `s_1..s_K`.**
Shallow coefficients ⟺ shallow moments. Verified exactly to K=4: `e_2=(s_1²−s_2)/2`, so
`|e_2|=(p−n−1)/2 = Θ(p)`.

**Step 3 — the intended lever: Fujiwara/Cauchy/Lagrange root bound.**
`M ≤ 2·max_{k=1..m}|e_k|^{1/k}` (last term halved). Tool: Fujiwara. This is the whole point of
the encoding — a NON-moment, root-geometry bound.

**Step 4 — DEATH #1: the max-form binds at k=2 → √(2p), worse than Johnson.**
The Wick law (probe P1, ratio→1) gives `|e_{2s}| ~ (s_2/2)^s/s! = (p/2)^s/s!`, hence
`|e_{2s}|^{1/2s} ~ √(p/2)·(s!)^{−1/2s}` is **strictly decreasing in s**, and odd `e` are tiny
(cancellation). So `max_k|e_k|^{1/k}` is at the smallest even index `k=2`:
`M ≤ 2|e_2|^{1/2} = √(2(p−n−1)) = Θ(√(nm)) = 2^{60.5}` (β4) / `2^{79.5}` (prize) —
**worse than Johnson `√p`**, loose vs target by `√(2(m−1)/log m) → ∞`. This is exactly the
machine-checked G3 obstruction (`_wf9G3_periodpoly_coeff_nogo.lean`), now *explained* by the Wick
coefficient law. Every monotone-in-`max_k|e_k|^{1/k}` bound (Cauchy, Lagrange, Kojima) shares it.

**Step 5 — DEATH #2: shallow-weighted / partial disk tests are blind to the spike.**
The natural escape is a bound *weighted toward large k*, where `|e_k|^{1/k}` is small.
- **Schur–Cohn / Routh–Hurwitz** (test: are all roots in the disk of radius `R=target`?) is a
  conjunction of `m` determinant conditions in `e_1..e_m` — using it needs **deep** coefficients
  `e_k` up to `k=m` = deep moments = the wall. A truncation to shallow `e_1..e_K` certifies
  nothing about the disk (the countermodel below satisfies every shallow condition with
  `house = √p`).
- **Geometric-mean / product bounds** (via `|e_m|^{1/m} = geo-mean|η_j|`) bound the geometric
  mean, not the max. A lone spike has `geo-mean ~ √n` but `house ~ √p`. Blind.

So no root-location functional that reads only shallow, provable coefficients escapes step 4.

**Step 6 — the fundamental obstruction: the class floor / lone-spike countermodel.**
The best house bound ANY consumer of `e_1..e_{2s}` (= moments to depth `s`) can certify is the
**class floor** `S_{2s} =` max house over all real measures of mass `m` matching those moments.
- **K=2 (explicit integer countermodel, probe P3a):** spike at `s≈⌊√(s_2)⌋`, `a` atoms at `+1`,
  `c` at `−1`, rest `0` — a monic **integer-root** polynomial matching `s_1,s_2` **exactly** with
  `house = s ≈ √p`. At n=8: `house 62` vs true `M=7.56`. `S_2 = √p = ` Johnson exactly.
- **K=4 (spike+bulk class floor, probe P3b):** one spike `±s` + symmetric bulk `±t` on the other
  `m−1` atoms is the upper principal representation; solving `s²+(m−1)t²=s_2`, `s⁴+(m−1)t⁴=s_4`
  gives `S_4 = √( (s_2 + √((m−1)(m·s_4 − s_2²)))/m ) → (3pn)^{1/4}` as `m→∞`. At n=8: `house
  15.33` (2.03× truth); prize: `S_4 = (3pn)^{1/4} = 2^{47.4} ≫ target 2^{18}`.

**Real-rootedness + integrality + Newton inequalities + Laguerre–Pólya impose NO house bound
below `S_{2s}`.** The apparatus is 0 bits: the extremal object is a lone spike, precisely the R1
CMK lone-spike measure. N4 = the root-location twin of that moment-problem death.

*Honest subtleties surfaced by the probe (both genuine, both worth recording):*
1. **Integrality of `P_m` does NOT give integer roots.** A pure integer-root multiset forces
   `x³≡x (mod 6)` (Fermat), hence `s_3≡s_1 (mod 6)` — which the true periods VIOLATE
   (`s_3−s_1=−63` at n=8). So a K≥3 integer-root countermodel needs irrational monic-integer
   quadratic packs (e.g. golden `x²∓x−1`, house φ) to break the odd congruence; the clean
   real-rooted realization is the spike+bulk of P3b. (This is why the earlier `probe_..._leeyang.py`
   K=4 integer search returned empty — a real obstruction, not a bug.)
2. **Finite-budget power-mean feasibility.** A house-`s` spike needs the bulk to carry `s_2` at
   small `s_4`, requiring `≳ s_2²/s_4` bulk atoms; the countermodel needs `m ≳ s_2²/s_4`, which is
   `~ m/3` at β=4 (satisfied with room) but marginal at tiny `n`, where the finite budget itself
   already pins the house near the truth. This is why the K=4 floor is only 2–3× truth at n=8,16
   and only blows up to `(3pn)^{1/4}` asymptotically — consistent, not contradictory.

**Step 7 — DEATH #3 (terminal): the optimized ladder reaches target ORDER but only at the wall.**
`S_{2s}/√n = √(2s/e)·m^{1/2s}`, minimized at `s* = ln m`, giving
`min_s S_{2s} = √(2 n ln m)` — the **target order**, constant `√2`. But the minimizer sits at
**coefficient depth `k* = 2s* = 2 ln m ≈ 125` (β4) / `≈ 177` (prize).** Via Newton (step 2) that
is power sums `s_r` to `r ~ ln m`, i.e. the wraparound counts `N_0(2 ln m)` whose **char-p
excess over the char-0 Wick value is exactly the prize's open content** (the `≤ 2 ln p`-term
`±1`-relations of `2^μ`-th roots mod `p`). Shallow, char-0-clean depth (K=2, K=4) delivers only
`√(2p) / (3pn)^{1/4} ≫ target`. **The lane is a faithful re-encoding of the moment ladder and
dies at the identical depth `r ~ ln p`.**

---

## Verdict

The root-location encoding is exact and the chain is complete, but it adds **no leverage**:
1. its native tool (max-form root bounds) is **worse** than Johnson (√(2p), binds at k=2);
2. every shallow-weighted or partial root-location test is **blind to the lone spike**;
3. optimally consuming coefficients = optimally consuming moments, reaching `√(2 n ln m)` **only**
   at depth `2 ln m` = the deep-wraparound wall.

**Standing filter (new, for this lane's family):** *any proposal using real-rootedness /
Newton inequalities / Lee–Yang / Laguerre–Pólya / Schur–Cohn / Routh–Hurwitz on the period
polynomial must first beat the K=2 integer lone-spike countermodel (house `√p`, matching `s_1,s_2`
exactly) and the K≥4 spike+bulk class floor `(3pn)^{1/4}`.* Root geometry sees only the moments
it is fed, and the extremal geometry is a spike — the same object that killed CMK in round 1.

No closure is claimed; the core stays **OPEN, ON-BGK**. A complete chain, honestly killed at its
own step 7, is this lane's deliverable.
