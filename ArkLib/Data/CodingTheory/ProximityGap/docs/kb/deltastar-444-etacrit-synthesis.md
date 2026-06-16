# The η_crit synthesis: descent + Action–Orbit norm bound + the wall, unified (#444)

*Status: ANALYSIS, workflow-verified with a KEY CORRECTION (see §0). NOT a closure. The
δ*-lower-bound does NOT follow (R1 fails); this is a sharp re-confirmation of the wall from a new
unified direction. Honesty contract held.*

## 0. ⚠️ CORRECTION (workflow `wf_444_etacrit_synthesis` Verify-1): the exponent is `⌈c/2⌉`, not `c`

My step "`c` vanishing power sums ⟹ `p^c | N(β_T)`" is **FALSE**. For `n = 2^μ`, the Galois group
of `ℚ(ζ_n)/ℚ` is the **odd** residues mod `n` (units = odd numbers), so only **odd** indices `j`
give genuine automorphisms `σ_j` and distinct primes. The first `c` power sums contain only
`⌈c/2⌉` odd indices, so **`p^{⌈c/2⌉} | N(β_T) ≤ s^{n/2}`**, giving the corrected ceiling
**`p ≤ s^{(n/2)/⌈c/2⌉} ≈ s^{n/c}`** (the *square* of the claimed `s^{n/(2c)}`). Verified exactly:
`c=2 → v_p(N)=1` (15/15 defects), `c=3 → v_p=2` (12/12); `v_p ≥ c` held in 0/27. The Lean
`badPrimeBound_core` (`Sweep_A10`) is itself sound — it binds `K = n/8` (the fixed Q1 odd-window
count), and my error was plugging the descent's `c = ηn` into the `c`-exponent slot.

**Corrected boundary:** `η_crit ≈ μ/(128+μ) ≈ 0.19` (μ=30) — *double* the earlier 0.095. Since the
window width is `√ρ−ρ ≈ 0.19–0.23`, **`η_crit ≈ the window width`**: the clean region `η > η_crit`
is **Johnson-adjacent** (a thin sliver at the window edge, or empty for `ρ=1/16` where
`√ρ−ρ=0.1875 < η_crit`). The ENTIRE window interior — including all of δ* (`η ≈ 1/μ ≈ 0.033`) — is
the **wall**. This *strengthens* the synthesis: it shows the norm bound barely reaches past
Johnson, exactly matching "Johnson is the closed/open boundary." Also: "non-coset" should read
**"non-antipodal-balanced"** (β_T = 0 ⟺ T is a union of `{x,−x}` pairs, Lam–Leung at 2).

---

## 0b. The two attack routes FAIL (workflow + direct verification) — the route is structurally insufficient

- **Sharper-than-AM-GM norm bound → reduces to BGK, AND still insufficient.** The defect conjugates
  have **√-cancellation**: `|σ_j(β_T)| ≈ √s` (measured n=32: mean 1.74–2.74 vs √s=2.45–3.16), so
  `|N(β_T)| ≈ s^{n/4} ≪ s^{n/2}` — AM-GM is wildly loose. Sharpening `N ≤ s^{n/2}` to `s^{n/4}`
  requires `|σ_j(β_T)| ≤ √s` on the **worst** defect, but `σ_j(β_T)=Σ_{x∈T}ζ^{j·idx(x)}` is an
  **incomplete character sum** → that bound IS the BGK wall. **And even granting full √-cancellation,
  the ceiling improves only to `η_crit' = μ/(2(128+μ)) ≈ 0.095`, STILL above δ*'s `η ≈ 1/μ ≈ 0.033`.**
  So the norm route is structurally insufficient for δ* **even if BGK were solved**.
- **2-power char-p rigidity → FAILS, defects exist mod p.** Concrete non-antipodal-balanced
  vanishing-power-sum defects exist, e.g. `T(idx)=(0,1,2,8,12,30)` at `n=32, p=97` (and many more).
  The char-0 cyclotomic rigidity does NOT transfer: it relies on the `Φ_d` being irreducible, but
  `Φ_d` **splits** mod `p` (`p≡1 mod n`), letting subsets mix roots across `Φ_d`'s with vanishing
  power sums. The powers-of-2 resultant coprimality is irrelevant (the issue is splitting, not
  coprimality). This IS the additive-energy defect = the wall.

**Net of §0–§0b:** every route in the descent / Action–Orbit / norm-bound family bounds the rigid,
Johnson-adjacent **word-list** for `η > η_crit` (AM-GM `≈0.19`; idealized-BGK `≈0.095`), but δ*
lives at `η = Θ(1/log n) ≈ 0.033`, structurally below even the idealized threshold. **No bypass; the
wall stands. The prize core remains the open char-p defect at `η < η_crit'`.**

---

*(Original analysis below; the `η_crit` value is superseded by §0/§0b, but the structure stands.)*

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

## §0c. The UNIFYING META-THEOREM (the complete why-δ*-resists, after 6 directions)

Every floor method this session — even/odd descent, Action–Orbit norm bound (η_crit), DFT/lacunary
rigidity, binary-multiples/correlation-attack, and over-determination (C-NEW-1: defect dies for
`c/s ≥ ~0.4–0.5`) — cleans the char-p defect only in a **constant-`η` regime** `η ≥ η_thresh`
(η_crit ≈ 0.095–0.19; over-determination ≈ `ρ`). The reason is structural and uniform:

> **The worst-case window list at radius `δ = capacity − η` = char-0 coset count (`poly(1/η)`,
> closed) + char-p defect. The defect is provably 0 (list bounded) for every FIXED `η > 0` at
> accessible scale, but δ* sits at `η = Θ(1/log n)` — at the precise ratio `c/s = η/(ρ+η)` where
> the defect first reaches the budget `n`. Since `Θ(1/log n) < η_thresh` for every constant
> `η_thresh` at prize scale (`μ=30`), δ* lies in the defect-PRESENT regime that no constant-`η`
> floor method touches. Pinning δ* ⟺ bounding the char-p defect at `η → 0` ⟺ effective
> thin-subgroup Gauss-sum equidistribution = the open BGK/Paley wall.**

Verified pivot: at δ*'s ratio `c/s ≈ 0.35` defects EXIST (n=32: 15 non-coset defects at `c=2,s=6`);
at `c/s ≥ 0.5` they vanish (the `x^{n/4}+1` case, proven cosets-only to n=64). So δ* is exactly the
crossover, and it is `Θ(1/log n)`-deep — below every constant clean threshold. This subsumes the
η_crit no-go (`Sweep_A43`) and explains, in one statement, why all six directions + the campaign's
190+ conjectures + the parallel ceiling table (every √-cancellation method caps below `δ=1/2`)
terminate at the same wall. No constant-`η` method can reach a `Θ(1/log n)`-deep threshold.
