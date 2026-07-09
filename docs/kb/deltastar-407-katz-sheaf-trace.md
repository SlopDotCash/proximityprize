# δ* (#407) — Katz sheaf-trace × generic-chaining (route 103, A14): sheaf IDENTIFIED, conductor COMPUTED — bounded-conductor is FALSE, Deligne buys nothing (2026-06-14)

**Status:** actionable A14 (merged 407-T03 / 357-T01 / 232-T01), the "single most-promising
never-tried direction" flag. Route 103 first step executed in full. **Verdict: OPEN / no closure —
the sheaf is identified exactly, its conductor is computed exactly as a function of window weight
`w`, and the conductor is the *full dual-subcode size* `q^{n-k-1}`, independent of `w`, so Deligne/Weil
is strictly worse than the trivial bound.** The "Krawtchouk = Kloosterman trace function" hope is
true at the level of the *weight* `K_{wt(a)}` but does NOT make the *sum over the dual code* a
bounded-conductor 1-parameter trace function. Honest negative with a precise structural reason.
Artifacts: `scripts/probes/sweep_a14_katz_sheaf_conductor.py` (exact, 5 prize-shaped instances).

This is **distinct** from the already-in-tree `Frontier/EffKatzConductorBarrier.lean`, which computes
the conductor of the *frequency-side* sheaf `b ↦ η_b = Σ_{x∈μ_n} e_p(bx)` (the Gauss-period family,
1-dimensional FT of the `n`-point set `μ_n`, rank `n`). A14 is the **message-side** object: the
sheaf on the `u_0`-space whose trace function is the Krawtchouk-weighted *dual-code* sum — a different
sheaf living on a different space, never identified before.

## 1. The object, written explicitly (the route-103 first step)

The binding far-line MCA incidence (in-tree `FarCosetExplosion.epsMCA_ge_far_incidence`,
`ShellFourierKrawtchouk.shell_fourier`, validated EXACTLY by `scripts/probes/probe_dualcode_krawtchouk.py`)
is, for `C = RS[F_q, μ_n, k]`, far direction `u_1`, offset `u_0`, window radius `r = ⌊δ n⌋` (so the
**window weight `w` of A14 is `w = n − r`**, the agreement count; equivalently parametrize by `r`):

> **`M(u_0) = (|F||C|/|V|) · ( |B| + S(u_0) )`,  with**
> **`S(u_0) = Σ_{a ∈ D, a ≠ 0} K_{wt(a)} · e_p(a · u_0)`,  `D = C^⊥ ∩ u_1^⊥`  (dim `n−k−1`).**

Here:
* `e_p(·) = ψ(·)` is the additive character of `F_q` (`q = p` or `p^f`);
* `D = C^⊥ ∩ u_1^⊥` is the **dual subcode**: the dual of the *extended* code `C + ⟨u_1⟩` (dim `k+1`),
  so `dim D = n − k − 1`, `|D| = q^{n−k−1}`;
* `K_{wt(a)} = \widehat{1_B}(a) = Σ_{v: wt(v) ≤ r} ψ(a·v)` is the **Krawtchouk weight**; by
  `ShellFourier.shell_fourier` it depends only on `wt(a)` and equals `Σ_{j≤r} K_j(wt a)` (the
  partial-sum Krawtchouk / the Fourier transform of the radius-`r` Hamming ball). This is the
  "Krawtchouk weights ARE Kloosterman-type trace functions" of the A14 brief — and it is true: a
  single `q`-ary Krawtchouk value `K_j(x)` is (up to normalization) a value of a Kloosterman/Jacobi-type
  exponential sum (the binomial/hypergeometric sheaf), so `x ↦ K_j(x)` IS a trace function of a
  bounded-conductor sheaf *in the weight variable `x`*. **But that is the wrong variable** — see §3.

`S(u_0)` is exactly the A14 template `S(u_0) = Σ_{ξ∈D} (\text{trace fn})(ξ) · e(ξ·u_0)` with
trace function `ξ ↦ K_{wt(ξ)}` over the dual subcode `D`.

## 2. The sheaf, identified

`u_0 ↦ S(u_0)` is the **trace function of the additive Fourier transform `FT_ψ(G)`** of the
**weighted punctual (skyscraper) sheaf**
> **`G = Σ_{a ∈ D, a ≠ 0} K_{wt(a)} · δ_a`**
on `𝔸^n_{u_0}` (equivalently `D \ {0}` is a 0-dimensional closed subscheme of `𝔸^n`, and `G` is the
skyscraper with stalk `K_{wt(a)}` at each point `a`). This is the *same shape* as the in-tree
frequency-side computation (`EffKatzConductorBarrier`: `b ↦ η_b` is `FT_ψ(δ_{μ_n})`), but here:
* the support is the **dual subcode `D` of size `q^{n−k−1}`**, NOT the `n`-point set `μ_n`;
* the weights are the **Krawtchouk values `K_{wt(a)}`**, NOT all `1`.

It is **not** a geometrically irreducible middle-extension sheaf of small generic rank (no
Kloosterman/hypergeometric sheaf of bounded rank governs it): `FT_ψ` of a skyscraper supported on `M`
distinct points is, generically, a sheaf whose generic rank / sum-of-Betti-numbers is `Θ(M)` — it is
a sum of `M` distinct rank-1 Artin–Schreier sheaves `K_{wt(a)} · 𝓛_{ψ(a·u_0)}`, one per dual codeword.

## 3. The conductor, computed as a function of window weight `w` (the A14 deliverable)

**The conductor of `FT_ψ(G)` = the number of ACTIVE dual codewords**
> **`cond(FT_ψ(G)) = #{a ∈ D \ {0} : K_{wt(a)} ≠ 0}` (= generic rank on `𝔸^n`, the distinct
> Artin–Schreier frequencies `a`).**

Measured EXACTLY (`sweep_a14_katz_sheaf_conductor.py`, all rows `#active = |D|−1` exactly):

| RS code | `dim D` | `|D|−1` | conductor `#active` (every `w`) | line-restriction rank (`≤ q−1`) |
|---|---|---|---|---|
| `F_7, n=6, k=2`  | 3 | 342 | **342** | 1–4 |
| `F_5, n=4, k=1`  | 2 | 24  | **24**  | 3 |
| `F_5, n=4, k=2`  | 1 | 4   | **4**   | 3 |
| `F_11, n=5, k=2` | 2 | 120 | **120** | 6 |
| `F_13, n=4, k=2` | 1 | 12  | **12**  | 6 |

**Dependence on window weight `w`: NONE.** Across every radius `r = 1 .. n−1` (= every window weight
`w = n − r`), `#active = |D| − 1 = q^{n−k−1} − 1` *exactly* in all five families. The Krawtchouk weight
`K_{wt(a)}` vanishes only on the (thin) integer roots of the partial-sum Krawtchouk polynomial, which
no nonzero dual codeword hit in any swept instance. So:

> **`cond(FT_ψ(G)) = q^{n−k−1} − 1`, INDEPENDENT of the window weight `w`, EXPONENTIAL in `n`.**

This is the answer A14 asked for. The conductor is **not** `O(1)`, **not** `O(w)`, **not** `poly(n)` —
it is the full dual-subcode cardinality.

## 4. Is `u_0 ↦ S` a trace function of a geom-irreducible sheaf of bounded conductor? — NO

Deligne's theorem for `FT_ψ(G)` gives, for the trace function on `𝔽_q`-points,
> `|S(u_0)| ≤ cond(FT_ψ(G)) · √q = (q^{n−k−1} − 1) · √q`.

But the **trivial bound** is `|S(u_0)| ≤ Σ_{a∈D}|K_{wt(a)}| ≤ |D| · |B| = q^{n−k−1} · |B|`, with
`|B| = #{wt ≤ r} ≤ q^r`. The Deligne bound `q^{n−k−1}√q` is **larger** than the trivial bound for
small `r`, and at no window weight does it beat the target. **Deligne/Weil buys nothing here**: the
square-root cancellation is per-frequency, but there are `q^{n−k−1}` frequencies, so the conductor
prefactor eats the entire gain. This is the *message-side* incarnation of the same wall the
frequency-side note recorded (`deltastar-407-effective-katz-family-moments-nogo`): the conductor
barrier does not vanish, it sits in the *number of dual codewords*.

**Why "Krawtchouk = Kloosterman trace function" does not rescue it.** The brief's hope is that because
`x ↦ K_j(x)` is itself a bounded-conductor Kloosterman/binomial trace function, the sum `S` should be a
short, structured, bounded-conductor object. The flaw is variable-mismatch: the Kloosterman structure
is in the **weight variable `x = wt(a)`** (a 1-dim sheaf on `𝔸^1_x`), but `S` sums `e_p(a·u_0)` over the
**`(n−k−1)`-dimensional dual code `a ∈ D`**, fibering the weight over the code. To exploit the weight's
sheaf structure one would need the dual codewords `a` to be *evaluations of a low-degree curve* so that
`a ↦ (wt(a), a·u_0)` becomes a 1-parameter family — which is exactly the GG25 curve-decodability
hypothesis (issue #334 B2), itself open. Absent that, the sum is over a full `q^{n−k−1}`-point variety
and the Krawtchouk-as-Kloosterman fact is *inert*.

**The line-restriction red herring (recorded so no one re-walks it).** Restricting to a generic
1-parameter line `u_0 = b + t·v` (the object a *1-variable* Katz/Adolphson–Sperber argument would see)
collapses the rank to `≤ q − 1` (data: line_rank 1–6), because the frequencies collide under
`a ↦ a·v mod q`. This collapse is *destructive interference of the cancellation*, not a real
conductor reduction: the `q^{n−k−1}` distinct `a` are projected onto ≤ `q−1` residues and their
Krawtchouk-weighted contributions **add coherently within each residue class**, so the 1-dim sheaf has
small rank but its trace can be as large as the un-cancelled sum. The genuine sheaf is `n`-dimensional;
a 1-parameter chaining/equidistribution argument **cannot recover the `n`-dim cancellation**.

## 5. Does RS-structured chaining entropy convert `√q` into `√(n·log(q/n))`? — NO via this sheaf

The second half of A14: even granting a per-`u_0` `√q` bound, can generic-chaining over the RS-structured
`u_0`-family beat the union bound and produce the prize `√(n·log(q/n))`? Two independent obstructions,
both already localized in-tree:

1. **The metric is flat (already proven, `deltastar-salem-zygmund-...` §SELF-REFUTATION).** For the
   companion Gauss-period family the increment metric `d(c,c') = ‖η_c − η_{c'}‖_{ψ₂}` is *flat*
   (`≈ √(2n)` for every distinct pair), so `γ₂ ≈ √(2n)·√(log m)` and **chaining = union bound** — there
   is no multi-scale RS geometry to exploit. The same flatness holds for the `S(u_0)`-family: distinct
   `u_0`'s give near-orthogonal frequency vectors over the full dual code, so the chaining entropy
   integral `∫√(log N(ε)) dε` is dominated by the single coarsest scale = `√(log |support|)` = the
   union bound. Chaining needs increment geometry; the RS dual code supplies none here.

2. **Even with a flat-metric `√(n log N)`, `N = q^{n−k−1}` ⟹ `√(n·(n−k−1)·log q)`**, which is
   `√(n²·log q)` scale — *worse* than the trivial `q^{n−k−1}`, and a factor `√n · √(log q / log(q/n))`
   above the prize target `√(n log(q/n))`. The chaining "entropy" of the full dual code is `(n−k−1)log q`,
   not `log(q/n)`; the RS structure does not thin it to the `log(q/n)` the prize needs. The only way to
   get `log(q/n)` is to chain over the `m = (q−1)/n` Gauss-period indices (the *frequency* side), which
   is the recognized open core (`B(μ_n) ≤ √(n log(q/n))`, the B-form), **not** the message-side dual-code
   sheaf.

So this sheaf is the *wrong sheaf* for the chaining route: its entropy is `(n−k−1)log q` (full dual
code), and chaining cannot drop it to `log(q/n)`.

## 6. The one non-vacuous lever (where a real attack would have to go)

The conductor would drop to `poly(n, w)` **iff** the active dual-subcode point set `{a ∈ D : K_{wt(a)}≠0}`
were the image of a **low-degree curve** `t ↦ a(t)` (then `S(u_0) = Σ_t K_{wt(a(t))} e_p(a(t)·u_0)` is a
genuine 1-parameter trace function and the Krawtchouk-as-Kloosterman fact + Deligne give `√q` with
*bounded* conductor `O(deg · w)`). For `C = RS[μ_n,k]`, `D = (C+⟨u_1⟩)^⊥` is a *generalized RS / twisted*
code; whether `D \ {0}` lies on a bounded-degree curve in `𝔸^n` is **exactly the GG25 curve-decodability
question** (issue #334 B2, open, its own multi-brick project). So route 103 reduces, cleanly and
honestly, to: **is the dual subcode `(RS+⟨u_1⟩)^⊥` curve-structured?** — the same wall as B2, now reached
from the sheaf/conductor side. This is the precise place a Katz-sheaf attack must engage; the conductor
computation here proves the *unstructured* sheaf gives nothing.

## 7. Honest verdict (contract)

**No closure. No new bound on the prize incidence.** Delivered (A14 deliverable, all rigorous/measured):
(a) explicit `S(u_0) = Σ_{a∈D} K_{wt(a)} e_p(a·u_0)`; (b) sheaf identified as `FT_ψ` of the
Krawtchouk-weighted skyscraper on the dual subcode `D = C^⊥∩u_1^⊥`; (c) conductor computed EXACTLY
`= #active dual codewords = q^{n−k−1}−1`, **independent of window weight `w`, exponential in `n`**;
(d) proof that Deligne/Weil for this sheaf is *worse than trivial* (conductor prefactor eats all
cancellation); (e) the Krawtchouk-as-Kloosterman fact is inert because the structure is in the wrong
(weight) variable; (f) chaining over the `u_0`-family cannot reach `√(n log(q/n))` because the RS dual
code's metric is flat and its entropy is `(n−k−1)log q` not `log(q/n)`; (g) the single non-vacuous
lever = curve-structure of the dual subcode = GG25/B2, open. This is one of the two families flagged to
"beat W4 without BGK/GRH"; it is now **decisively localized as not beating W4 in its unstructured form**,
and reduced to B2 in its structured form. Not fabricated.

## Reproduce
- `scripts/probes/sweep_a14_katz_sheaf_conductor.py` — exact `#active`/conductor sweep over window
  weight `w`, 5 prize-shaped RS instances (`F_5,7,11,13`), + line-restriction-rank contrast.
- `scripts/probes/probe_dualcode_krawtchouk.py` — the underlying EXACT identity
  `S = Σ_{a∈D} K_{wt a} e_p(a·u_0)` ⟺ extended-code list size (in-tree, three-way unification).

## Cross-refs
- `Frontier/EffKatzConductorBarrier.lean` — the *frequency-side* conductor (`b↦η_b`, rank `n`); A14 is
  the *message-side* companion (`u_0↦S`, conductor `q^{n-k-1}`).
- `docs/kb/deltastar-407-effective-katz-family-moments-nogo-2026-06-13.md` — the moments-of-the-family
  conductor wall (Rojas-León large monodromy); same wall, frequency side.
- `docs/kb/deltastar-salem-zygmund-gausssum-chaining-2026-06-13.md` — the flat-metric ⟹ chaining =
  union-bound refutation reused in §5.
- issue #334 B2 / GG25 Def 3.1 curve decodability — the one lever (§6).
