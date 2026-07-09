## Moment/distribution sweep: the sub-Gaussian "deep-moment validity" input is REFUTED as stated — but the regime distinctions reopen the power-of-2 case, and the right open object is now pinpointed (Untrau growing-n)

Targeted sweep on the *exact* quantity the prize needs — the **high moments / value distribution**
of `η_b = ∑_{x∈μ_n} e_p(bx)` (NOT the max, which is the classical wall). Decisive, partly
self-correcting findings:

### 1. The sub-Gaussian moment form is FALSE (honest correction to my own conjecture)
`M_r = (1/p)∑_b|η_b|^{2r} = E_r(μ_n)` (the r-th additive energy). The clean sub-Gaussian target
`E_r ≤ c^r·r!·n^r` (constant `c`) is **refuted**: Shkredov (arXiv:1102.1172) gives
`E_3(μ_n) ≪ n³·log n`, and my FFT probe confirms a *growing* correction
(`E_3/(6n³)` = 1.67, 2.06, 2.27 at n=8,16,32). So the subgroup character sums are **not
sub-Gaussian**; `PROXIMITY_PRIZE_CONJECTURE.lean`'s `DeepMomentValidity` is corrected to flag this.
**Nuance:** `E_2 = 3n²−3n` *is* clean (no log) in the prize regime `p > n³` (probe-exact) — the
classical Konyagin–Shkredov `n²·log n` is the **large-subgroup `n ~ √p`** regime, not the prize
`n ~ p^{1/5}`. The honest input is the poly-log-corrected `E_r ≤ (C·g(n))^r·r!·n^r`, which still
yields `B ≲ √(n·log q·log n)` via the (proven) moment arrow — a `√log n` factor off the target
`√(n·log(q/n))`. Whether that gap matters at `ε* = 2⁻¹²⁸` is the sharpened open question.

### 2. The right theory exists for this exact object — but in the wrong regime, with the prize case OPEN
**Untrau (arXiv:2112.05441, MPCPS 2024)** studies *exactly* `η_b` for a multiplicative subgroup,
proving it equidistributes (as b varies) on the **d-cusp hypocycloid** — but for **fixed** subgroup
order `d = n`; the limit is bounded, **not Gaussian**. **Kowalski–Untrau (arXiv:2302.13670)** ("ultra-
short sums") compute the bounded-limit moments and **explicitly flag the growing-`n` small-subgroup
case as open** (lines 820/830). So the precise open object is the **growing-`n` value distribution of
`η_b`** — a clean, named, attackable target that the analytic-number-theory community has *posed but
not solved*. This is a genuinely better-specified handle than "the 25-year wall."

### 3. The prize is unclaimed, and the near-capacity disproof does NOT cover power-of-2 domains
Authoritative (June 2026): the $1M prize is **unclaimed**; conditions still being finalized. The
near-capacity *failure* result (**KKH26 eprint 2026/782**, fleshed out in **Kambiré arXiv:2604.09724**)
disproves proximity gaps near capacity for **general cyclic prime-field subgroups** `⟨ξ⟩ ⊂ F_p^×` via
the subgroup-sumset bound `|H^{(+r)}| ≥ (s/2r)^r` — but it "**fundamentally requires the cyclic
multiplicative-subgroup structure over a prime field**" and **does not address the prize's power-of-2
FFT domains**. This is exactly the "many true statements fail in the prize regime" point: the
**power-of-2 case is genuinely distinct** and is *not* killed by the known disproof — leaving open
whether `δ*` reaches near-capacity specifically for `μ_{2^a}`.

### 4. Grandiose 2026 claims — relocate the wall (discounted)
`eprint 2026/858` / `2026/861` (FRI above Johnson) are unconditional **only for sparse adversaries**,
general case rests on an unproven "sparse-worst-case dominance conjecture"; `eprint 2025/1712`
("Syndrome-Space Lens, complete resolution to capacity") is **contradicted** by the KKH26/CS25
disproofs. None solves the grand challenge.

**Net:** the input I conjectured is corrected (not sub-Gaussian; poly-log factors), the right open
object is sharpened to Untrau's **growing-n subgroup-sum distribution** (community-posed, open), and
the prize's **power-of-2 domains are not covered by the near-capacity disproof** — a regime-specific
opening worth targeting. Prize unclaimed; nothing fabricated.
