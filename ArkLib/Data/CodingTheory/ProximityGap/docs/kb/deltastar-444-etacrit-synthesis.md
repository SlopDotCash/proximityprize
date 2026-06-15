# The η_crit synthesis: descent + Action–Orbit norm bound + the wall, unified (#444)

*Status: ANALYSIS, pending rigorous verification (`wf_444_etacrit_synthesis.js` running). NOT
claimed proven. The chain below has two named risk points (R1, R2) the workflow is adjudicating;
if either fails, the δ*-lower-bound conclusion does not follow and this reduces to the known wall.
Honesty contract: nothing here is a closure until the risk points are cleared.*

## 1. The convergence

Two independent threads of this session land on the **same** object:
- **Even/odd descent (list side):** the window list of the binding word `x^{s}+1` (agreement
  `s`, all roots of `f−u` in `μ_n`) `= #{size-s subsets T⊆μ_n : p_1(T)=⋯=p_c(T)=0 mod p}`, where
  `c = s−k` is the gap width (verified `n=16`: list = count = 4 = the 4 binomial cosets).
- **Action–Orbit norm bound (Chai–Fan 2026/861; in-tree `Sweep_A10`, axiom-clean
  `badPrimeBound_core`):** a **non-coset** defect `T` (so `β_T = Σ_{x∈T} ζ^{idx(x)} ≠ 0` over `ℂ`
  by 2-power Lam–Leung rigidity) with `c` vanishing power sums mod `p` forces `c` distinct primes
  above `p` to divide `β_T`, so `p^c | N(β_T) ≤ |T|^{φ(n)} = s^{n/2}`. **Defect ⟹ `p ≤ s^{n/(2c)}`.**

## 2. The η_crit boundary (the new quantitative content)

At a window-interior radius `δ = 1−ρ−η`: `s = (ρ+η)n`, `k = ρn`, so the gap width is
**`c = s−k = ηn`**, and the norm ceiling is

> `p ≤ s^{n/(2c)} = s^{1/(2η)}`.

The defect is **provably absent** (binding list = char-0 coset count, `O_ρ(1/η)`, ≪ budget `n`)
**iff** `log₂ p > (1/2η)·log₂ s`, i.e.

> **`η > η_crit`,  `η_crit = μ / (2(128+μ)) + o(1)`**  (prize params `log₂ p ≈ 128+μ`, `n=2^μ`).

For `μ=30`: `η_crit ≈ 0.095`. Two regimes:
- **`η > η_crit` (deep window):** norm ceiling `< p`, defect ruled out, **list provably bounded.**
- **`η < η_crit` (near capacity, where δ* lives at `η = Θ(1/μ) ≈ 0.033`):** ceiling `≫ p`
  (`2^{Θ(μ²)}` vs `2^{O(μ)}`), norm bound **vacuous** — the open char-p defect = the BGK wall.

`η_crit` **grows** with `μ` (→ 1/2) while `η_{δ*} = Θ(1/μ)` **shrinks** — the gap **widens** at scale.

## 3. The potential δ*-lower-bound (and why it may NOT hold — the risk points)

IF the binding object for δ* were the single-word list, then for `η > η_crit` all such radii are
"good" (list ≪ budget), giving **`δ* ≥ (1−ρ) − η_crit`** — and since `η_crit < √ρ−ρ` for every
prize rate, that is a **beyond-Johnson lower bound**. That would be a real partial result.

**Why this is NOT yet a result — the two risk points the workflow is checking:**
- **R1 (binding object).** The dossier pins δ* via the **far-line / MCA incidence**
  `I(δ) = max_{u_0,u_1} #{γ : u_0+γu_1 is δ-close}` — a count of **field elements γ**, governed by
  a **single** linear condition (`o_1=0`), NOT the many-condition single-word list. The norm bound
  bounds the many-condition object; the far-line is `c=1` (ceiling `s^{n/2}`, astronomically
  vacuous). This is exactly the campaign's "Action–Orbit is δ*-irrelevant" verdict. **If the
  δ*-binding object is the `c=1` far-line incidence, η_crit does NOT bound δ*.**
- **R2 (LD ⟹ MCA).** Even a clean beyond-Johnson *list-decoding* bound (the LD challenge) only
  gives the δ* (MCA) bound through the **open** collapse B4 (`LD ⟹ MCA`, ABF26 §5). So a clean LD
  bound is necessary, not sufficient, for δ*.

## 4. Honest reading

The η_crit boundary is a **sharp, correct** statement about *when the Action–Orbit/descent norm
bound is non-vacuous* (`η > η_crit`), unifying the descent + Action–Orbit + the wall into one
condition-count picture. It **explains precisely** why every clean route (Action–Orbit, the
descent, the moment method at depth `r ≈ c`) is "δ*-irrelevant": they all live at large `c`
(`η > η_crit`), while δ* lives at `c = ηn` with `η = Θ(1/μ) < η_crit`, where the bound is vacuous.

Whether η_crit yields an actual **δ*-lower-bound** hinges on R1+R2. If the δ*-binding object is the
single-condition far-line incidence (R1 fails) — as the campaign's audited verdict holds — then
this is a sharp re-confirmation of the wall, not a bypass. **No closure claimed; pending the
workflow.**

## 5. Reproduce
```
python3 -u /tmp/defect_onset.py     # n=16: ZERO defects at any prime (too rigid)
python3 -u /tmp/condcount.py        # condition-count c vs list size vs norm ceiling
```
In-tree: `Frontier/Sweep_A10_ActionOrbitBadPrime.lean` (badPrimeBound, p ≤ b²),
`Frontier/Sweep_A40_EvenOddDescentIdentity.lean` (descent identity).
