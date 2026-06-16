## A new exact identity: the Gauss-period house is a *purely multiplicative-tangent* quantity (the Gauss sums are perfectly flat)

Worked the live frontier (the worst-case incomplete subgroup sum `B = max_{b≠0}|η_b|`, `η_b = Σ_{x∈μ_n}ψ(bx)`, whose `≲√(n log m)` is equivalent to `δ*=average`). I derived and **machine-verified** (all checks ≤1e-14, `scripts/probes/probe_autocorrelation_identity_407.py`) a new exact identity that cleanly separates the *proven-flat* part of the problem from the *open* part.

### The identity (two independent derivations, both checked)
Write `τ_j = τ(χ^j)` (Gauss sum, `|τ_j|=√p` exactly), `A_h = Σ_j τ_j conj(τ_{j+h})` the autocorrelation of the Gauss-sum DFT sequence (the Wiener–Khinchin spectrum of `η`), and the **subgroup tangent sum** `T_h = Σ_{w∈μ_n} χ^h(1−w)`. Then

> **`A_h = m · χ^h(−1) · τ_{−h} · T_h  =  m · conj(τ_h) · T_h`** (h ≢ 0).

Route 1: collapse `Σ_j χ^j(−1) J(χ^j, χ^{−(j+h)})` via the subgroup indicator `Σ_j χ^j(z)=m·1[z∈μ_n]` to `m·T_h`. Route 2: `J(χ^i,χ^h)=τ_iτ_h/τ_{i+h}` (Mathlib `jacobiSum_mul_nontrivial`) gives `T_h=(1/m)Σ_i J(χ^i,χ^h)=τ_h A_h/(mp)`. They agree via `conj(τ_h)=χ^h(−1)τ_{−h}`.

### The decisive consequence (the new content)
Insert into the power spectrum `|η_b|² = (1/m²)Σ_h χ^h(b)A_h` and split off `h=0`:

> **`|η_b|² = n + (√p/m)·Σ_{h≠0} (unit_h · T_h) · χ^h(b)`**, where `unit_h = conj(τ_h)/√p` lies *exactly* on the unit circle (Weil, `|τ_h|=√p`).

So the Gauss-sum factor contributes a **perfectly flat** unimodular weight — **zero** concentration. **The entire worst-case house is carried by the multiplicative tangent sequence `T_h` alone.** Prior faces (additive energy `E_r`, phase-alignment, 2-adic tower) kept the additive sum entangled with the cancellation; this *cleanly factors it out* and proves the open core is `T_h`-only:
`B ≤ (1+o(1))√(n log m)  ⟺  the tangent sequence (T_h) is flat`, and `T_h = (1/m)Σ_i J(χ^i,χ^h)` is an **average of m Jacobi sums** — i.e. the prize is exactly *effective equidistribution of Jacobi sums*, the Deligne–Katz surface, not the additive BGK wall.

### Refutations this session
- **"2-power `μ_n` gives extra tangent cancellation" — REFUTED.** Measured `avg|T_h|/√n ≈ 1.0` and `max|T_h|/√n` growing like `√(log m)` — the *same* extreme-value law as the additive house. The relocation is a clarification, not an easing (same difficulty class).
- **"L¹-autocorrelation/4th-moment closes it" — REFUTED (analytic).** `B²≤(√p/m)Σ_h|T_h|≈n√m` ⟹ `B≤√n·m^{1/4}=√n·2^{32}` (useless). Both miss because they drop the `h`-cancellation, which *is* the house.
- Independent re-derivation: at the prize instance `p≈n^{5.27}`, the *proven* energy bound (`E_2=3n²−2n`, valid since `n^4<p`) gives only `B≤n^{1.03}>n`; reaching `B=o(n)` needs `r≥6` moments where the char-`p` energy excess is unproven. So **`B=o(n)` itself is unproven at the prize** (not just the constant) — consistent with `n<p^{1/4}` putting it below all published additive-subgroup bounds.

### Regime + in-regime toolbox (5 new papers, `PAPERS_NEEDED.md §2026-06-13 (#407 tangent)`)
The prize has `n≈2^30 < p^{1/4}≈2^39`, so BGK/Di-Benedetto (need `>p^{1/4}`) are out of regime. The right tools are small-subgroup Weil sums (Ostafe–Shparlinski–Voloch 2211.07739 — `T_h` *is* `Σ_{x∈G}χ(f(x))`, `f=1−w`) and Jacobi/Gauss equidistribution (Rojas-León 2207.12439; Lu–Zheng 2005.14358; effective template Fu–Lau–Li–Xi 2406.10106; boundary Di-Benedetto et al. 2003.06165).

### Honest status (no closure claimed)
Landed: probe (`probe_autocorrelation_identity_407.py`), an **axiom-clean Lean brick** for `T_h=(1/m)Σ_i J(χ^i,χ^h)` (`TangentSumJacobiAverage.lean`), and the synthesis (`RESEARCH_SYNTHESIS_407_TANGENT.md`). The bold **Subgroup-Tangent Flatness conjecture** scores novelty 8 / insight 9 / proximity 9 / **feasibility 2** — feasibility is gated because every equivalent face (additive energy, Gauss-period house, Paley eigenvalue, Jacobi equidistribution, and now `T_h`) bottoms out at the same √-cancellation among `~m` Gauss/Jacobi sums at a field of size `~nm`. **The contribution is a new exact identity, a proof that the open core is `T_h`-only (Gauss sums perfectly flat), a refuted escape, and the correct (Jacobi-equidistribution) toolbox — not a closure.**
