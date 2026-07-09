## Empirical transfer-threshold law `τ_r ~ n^{(r+3)/2}` — the char-0→F_p energy transfer is MUCH cheaper than the crude `C^{φ(n)}` bound, but the window needs deep moments, so the wall stands (sharply)

Built two reproducible FFT probes (`scripts/probes/probe_energy_transfer_threshold.py`,
`probe_moment_transfer_threshold.py`; one FFT gives both `B=max_{b≠0}|η_b|` and the moments
`E_r=(1/p)∑_b|η_b|^{2r}`). Measured for `μ_{2^a}`, `a=3..6`, sweeping `p`. Clean findings:

### 1. The energy transfers at `p ≳ n³` (not `C^{φ(n)}`)
`E(μ_{2^a}) = 3n²−3n` **exactly** (the char-0 Sidon value) once `p ≳ n³`:
- `n=16`: E inflated (912) at p≈n²; **exactly 720=3·256−48 for p≥4129≈n³**.
- `n=32`: inflated (3744) at p≈n²; **exactly 2976 for p≥32801≈n³**.
- `n=64`: inflated (13632) at p≈n²; **exactly 12096 for p≥262337≈n³**.

So the additive energy `E=O(n²)` genuinely holds in the prize regime (`p~n·2^128 ≫ n³`) — the F₁₇
`repCount=3` inflation that refuted the rigidity lead is a **tiny-prime artifact** (`p=17 ≪ n³`).

### 2. The higher-moment threshold law: `τ_r ~ n^{(r+3)/2}`
`E_r` reaches its char-0 value once `p > τ_r`, with (from the data) `τ₂~n^{2.5}, τ₃~n³, τ₄~n^{3.5},
τ₅~n⁴` — a clean **`τ_r ~ n^{(r+3)/2}`** (increment ½ per moment). This is **far below** the crude
height bound `C(w,⌊w/2⌋)^{φ(n)}` the floor-attack used — confirming that critique was correct.

### 3. ...but it does NOT escape the wall, because the window needs DEEP moments
The prize window `δ∈(1−√ρ,1−ρ)` is agreement `t=(1−δ)n∈(0.5n,0.71n)`, i.e. ladder depth
`r=t/m ~ Θ(n)` (≈0.25n–0.35n for m=2). So the window's floor needs `E_{Θ(n)}`, with threshold
`τ_{Θ(n)} ~ n^{Θ(n)} ≫` any prize prime. The low moments (r≤7) that transfer cheaply correspond to
agreement `rm≤14`, i.e. `δ≈1` — the trivial deep-error region, **not** the window. So the sharp
threshold law confirms the wall *at the relevant depth*, it doesn't break it.

### 4. The L⁴ energy ≠ the L∞ max (correcting the earlier "iff")
`B/√n` **grows** with p: 2.8 (n=8), 3.6 (n=16), 4.06 (n=32)… consistent with `B ~ √(n·log(q/n))`
(the `ShawGapLaw`). So `E=O(n²)` (L⁴-average, transfers at n³) does **NOT** imply `B=O(√n)` (L∞ max,
the wall). The prior "E=O(n²) ⟺ B=O(√n)" was an overstatement: `exists_charSum_ge_of_energy'` only
lower-bounds the max by the average (`max ≥ Ω(√n)`); the max can — and empirically does — exceed it.
The floor needs the deep moments / the L∞ max, both `n^{Θ(n)}`-threshold or growing.

**Net:** genuine empirical research that **sharpens** the wall's location (a clean `τ_r~n^{(r+3)/2}`
law and `E=3n²−3n` for `p≳n³`), and confirms the prize floor is the *deep-moment / L∞-max* wall, not
the cheaply-transferable L⁴ energy. No closure; reproducible probes committed. The wall stands.
