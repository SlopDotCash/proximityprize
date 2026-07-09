# δ* / #407 — Conjecture 41 (Chai–Fan, ePrint 2026/858) in the escape-clause / degeneracy branch

**Actionable A31** (merged 232-T11). Date 2026-06-14. Type: math-analysis + probe.
Probe: `scripts/probes/sweep_A31_conj41.py` (exact integer + mod-p arithmetic, runs in ~1 min).
Status: **PARTIAL** — a precise structural reconciliation that *relocates* the c≥3 open question
and removes a genuine internal tension in the program; the field-independent fiber-size bound
itself stays open (it is the same wall as A21 / A08, via the class-syndrome dictionary).

---

## 0. The object and the precise A31 question

Conjecture 41's matrix for a weight-`w` support family `{E_i}` with twists `{γ_i}` is the
**twisted double block**

```
A = stack over i of  [ N_{E_i} | γ_i · N_{E_i} ]
```

where the `c` normal rows of `E` are the coefficient vectors of `Λ_E · X^r`, `r < c`
(`Λ_E = ∏_{a∈E}(X−a)`, monic of degree `w`), living in `F^D × F^D`, `D = w + c`. The conjecture's
"open-set rank lemma" predicts `M_true ≤ ⌊(2D−1)/c⌋` (linear, `O(D/c)`).

* The **printed `M_true ≤ ⌊(2D−1)/c⌋` form is REFUTED** (DISPROOF_LOG O43/O44; the machine-checked
  witness `conj41_violation_witness` over `ZMod 17` in `TopDirectionLineCount.lean`).
* The **dichotomy form** survives *only through its escape clause*, which O42 showed is
  load-bearing on the **class syndrome**.
* Via the **(ii)⟷(iii) weld** (O42 pt 3, formalized by `loc_coeff_esymm` /
  `point_compat_iff_esymm_zero` / `zero_fiber_filter_eq`), the c≥3 rank lemma (formulation (iii))
  and the t≥2 multi-symmetric concentration (formulation (ii)) are *literally the same number* at a
  class syndrome.

**A31 question (verbatim):** for the twisted `[N|γN]` double blocks with **distinct γ_i**, *when*
does the symmetric-function fiber contain a **non-degenerate (genuine-`M_true`) syndrome** — a real
list element with all Vandermonde error values nonzero — rather than a Remark-31 false positive
(error vector supported only on the vertex set `W`)?

---

## 1. The decisive finding: there are TWO different "class windows", and they were conflated

The program uses two genuinely different "class" / "equal-window" conditions, and the central
A31 insight is that **they are not the same window** and **they carry the open content on opposite
sides**:

| name | window shared | # constraints | role |
|---|---|---|---|
| **O44 top-line window** | `e_1, …, e_{c-1}` | `c−1` | γ-free part of compatibility on the top-direction line `s(γ)=s₁+γ·u_top`; the spread direction is `e_c` |
| **O42 deficiency window** | `e_1, …, e_{w−c}` | `w−c` | the *full locator window above degree c*; drives the `equal_window_image` `(3c−1)`-dim collapse → rank ≤ `6c−2` |

These coincide only when `c−1 = w−c`, i.e. `w = 2c−1`. The flagship O43 witness is `w=6, c=3`:
O44 shares `e_1,e_2` (2 eqns); O42 shares `e_1,e_2,e_3` (3 eqns) — **O42 is strictly stronger.**

### What the probe shows (all exact, char-0 and mod a prize-shaped prime `p ≈ N⁴`, `N | p−1`)

**EXP1 / EXP4 — the disproof-side lower bound lives on the O44 window.**
The worst class-line genuine `M_true` (= # distinct `e_c` values over the `e_1..e_{c-1}` fiber,
restricted to supports with all error values nonzero) for `w=6, c=3`:

```
 N:        8   9  10  11  12  13  14  15  16
 M_true:   1   2   3   4   5   7   9   9  13      ceiling ⌊(2D−1)/c⌋ = 5 (constant)
```

It **grows with N**, **crosses the refuted ceiling 5 at N=13**, and is **field-independent**
(char-0 value = `F_p` value exactly, every row). The `N=14` row reproduces the O43 flagship
witness exactly: worst class `(e_1,e_2)=(39,589)`, 10 supports, `M_true = 9 > 5`.

**EXP2 — the escape clause does NOT bite the genuine fiber (the key degeneracy-branch result).**
In the worst O44 class at `N=14, w=6, c=3` (`p=38431`): **all 10 class members are genuine**
(all Vandermonde error values nonzero), **0 degenerate**. Same at `N=13, w=5, c=4`. So:

> On the O44 window the entire fiber spread is genuine `M_true` mass — the escape clause /
> Remark-31 exclusion is **empty** there.

This is the direct A31 answer: a non-degenerate (genuine-`M_true`) syndrome is present **whenever
the `e_1..e_{c-1}` fiber has distinct points** (which is automatic for any support of distinct field
elements — the natural error value at `x∈E` is the locator derivative `∏_{y≠x}(x−y) ≠ 0`). The
fiber *always* contains genuine syndromes; the only question is *how many distinct `e_c`-values*
it spreads over.

**EXP3 / EXP6 — the deficiency branch lives on the SEPARATE, stronger O42 window, and is rare.**
- On the **O44** family (share `e_1..e_{c-1}`), the distinct-γ twisted block is **full column rank**
  (`rank = 2D`, 40/40 random γ) at every realizable class size — i.e. it is **not** in the
  deficiency branch.
- The **O42** deficiency (`rank ≤ 6c−2 < 2D`, every γ) requires the **full window** `e_1..e_{w−c}`
  AND `mc > 6c−2` (so `m ≥ 7` at `c=3`). A family of `m ≥ 7` supports sharing the full window is a
  genuine PTE configuration. EXP6 builds one (9 antipodal-triple supports sharing `e_1,e_2,e_3` at
  `p ≈ 10⁶`) and confirms **rank = 16 = 6c−2 for every γ (0/30 full rank)** — exactly reproducing
  O42. But at the small explicit domains (`N=14`, `w=6`) the largest *full-window* class has only
  **1** support: the deficiency branch is essentially **empty** there, while the O44 window already
  carries `M_true = 9`.

---

## 2. The reconciliation (resolves a real internal tension)

O42 reported "the conjecture lives ENTIRELY in its degeneracy branch; the kernel is the
class-syndrome scaling family." O43/O44 reported "genuine `M_true = 9` mass with all error values
nonzero." Read naively these look contradictory (degenerate kernel vs genuine mass). A31 resolves
it:

> **They are talking about two different families on two different windows.**
> The O42 *degenerate* kernel is the scaling family of a **full-window** (`e_1..e_{w−c}`) PTE family
> — its kernel `(v,0),(0,v)` is the homogeneous class-syndrome direction, genuinely degenerate.
> The O43/O44 *genuine* `M_true` is the `e_c`-spread of a **weaker** (`e_1..e_{c-1}`) fiber — that
> spread is full-rank and entirely non-degenerate. The escape clause excludes the O42 degenerate
> direction (correctly) but does **nothing** to the O44 genuine spread (which is why the printed
> `M_true ≤ ⌊(2D−1)/c⌋` form fails on top-direction lines: the clause `⟨Λ_E, u_top⟩ = 0` is
> *always* true by degree and so excludes far more than the degenerate configs — the "unintended
> exclusion" O43 flagged, here pinned at `c≥3`).

**Net for the c≥3 rank lemma:** the conjecture's *full-rank* branch fails on cliques
(`Conjecture41CliqueKernelStructure.lean`, unconditional) **and** on full-window PTE families
(O42/EXP6, every γ). Its *degeneracy* branch correctly excludes the homogeneous class-syndrome
direction. But the **prize-relevant `M_true`** is neither of those — it is the `e_c`-spread of the
weaker `e_1..e_{c-1}` fiber, which is genuine, field-independent, and grows past the ceiling.

---

## 3. Where the genuine open question now sits (the same wall as A21 / A08)

After A31 the c≥3 question is precisely:

> **Open (formulation (ii), purest form):** bound, field-independently, the worst `e_c`-spread of
> the `e_1..e_{c-1}` fiber of weight-`w` subsets of the smooth domain `μ_n` —
> `Spread(n,w,c) := max_{class κ} #{ e_c(E) : E ⊆ μ_n, |E|=w, (e_1..e_{c-1})(E)=κ }`.

This is *exactly* the A21 esymm-fibre-count object `F(n,w,m)` (with `m = c−1`) and the A08
window-interior worst-direction object, reached through the class-syndrome dictionary — confirming
the actionable's "same wall as A21/A08" claim with a concrete identification. The probe shows
`Spread` grows (super-`⌊(2D−1)/c⌋`) on the explicit additive domain; whether it stays `O(n)` or
goes super-linear on the *multiplicative* prize domain `μ_n` (the δ* = 1−ρ−Θ(1/log n) question) is
the open core, unchanged by A31.

What A31 *does* settle:
1. **The degeneracy branch is not where the prize `M_true` lives** — it is a separate, rarer
   full-window PTE family whose kernel is genuinely degenerate. Pursuing the degeneracy branch
   for an `M_true` upper bound is a category error.
2. **The escape clause cannot rescue the linear `⌊(2D−1)/c⌋` bound** — it is vacuous on exactly
   the (`e_1..e_{c-1}`) fiber that carries the growing genuine count.
3. **The genuine-syndrome existence question has a trivial answer**: every distinct-point support in
   the fiber is genuine (locator-derivative error values are nonzero). The content is entirely the
   *count* (the `e_c`-spread), i.e. formulation (ii).

---

## 4. Honesty

This is a **structural reconciliation + numerical evidence**, not a closure. No `δ*` bound is proven.
The probe is exact (integer / mod-p, no sampling) on small prize-shaped cases `N=8..16`, `w∈{5,6,7,8}`,
`c∈{3,4,5}`, `p ≈ N⁴` with `N | p−1`. The field-independent `Spread(n,w,c)` bound on `μ_n` — the actual
prize quantity — is OPEN and identical to A21/A08. The O42 deficiency and the O43/O44 genuine count
are both reproduced exactly, which is the basis for the reconciliation claim.

**Artifacts:** `scripts/probes/sweep_A31_conj41.py`; this note.
**In-tree substrate referenced:** `TopDirectionLineCount.lean` (decoupling, `point_compat_iff_esymm_zero`,
`zero_fiber_filter_eq`, `loc_coeff_esymm`, `conj41_violation_witness`),
`Conjecture41CliqueKernelStructure.lean` (clique full-rank failure),
`NormalRankSharpThreshold.lean` (cyclic/PTE deficiency), DISPROOF_LOG O40–O45.
