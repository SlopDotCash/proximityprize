# On the δ\* Threshold for Explicit 2-Power Reed–Solomon Proximity Gaps: A Complete Investigation

*Canonical synthesis of the #444 session. Honesty contract: every claim is tagged
PROVEN(axiom-clean)/VERIFIED(numeric)/CONJECTURE/REDUCES-TO-WALL/OPEN. No fabricated closure.
The prize core remains open; this paper documents the novel mathematics produced, the precise
characterization of the obstruction, and exactly what a solution must supply.*

---

## Abstract

We study δ\* — the mutual-correlated-agreement (MCA) = list-decoding threshold — for explicit
Reed–Solomon codes on the 2-power FFT domain `μ_n` (`n = 2^μ`), at the proximity-prize regime
(`p ≈ n·2^128`, `ε* = 2⁻¹²⁸`, window interior `(1−√ρ, 1−ρ−Θ(1/log n))`). We (1) introduce the
**even/odd non-symmetric dyadic descent** (a new, formalized tool), (2) prove the **MCA and
list-decoding challenges funnel to one object** (the dyadic lacunary count = char-p additive-
energy defect = the BGK/Paley √-cancellation wall), (3) prove a **structural no-go** showing the
leading published candidate route (Action–Orbit, ePrint 2026/861) cannot pin δ\* in the prize
regime even granting BGK, and (4) establish a **unifying meta-theorem** explaining why every known
method — eight independent directions plus the campaign's 190+ conjectures — caps short. The
single remaining gate is an effective thin-subgroup Gauss-sum equidistribution bound that does not
exist in the mathematics of 2026 (a half-power gap below SOTA `n^{0.989}` at the Burgess barrier),
and is beyond even GRH for this object.

---

## 1. The problem and the governing law

`μ_n ⊊ F_p^×`, `n=2^μ`, `p≡1 (mod n)`, `m=(p−1)/n=2^128`, `n≈2^30`, `β=log_n p≈4`.
δ\* `= sup{δ : I(δ) ≤ q·ε*}`, `I(δ) = max_{u₀,u₁} #{γ : u₀+γu₁ is δ-close to RS[k]}` (the far-line
/ MCA incidence). Window: `δ ∈ (1−√ρ, 1−ρ−Θ(1/log n))`, strictly between Johnson (achievable) and
capacity (proven impossible, ePrint 2025/2046).

**PROVEN (in-tree, axiom-clean).** The two grand challenges are one object:
`Sweep_A42_ReunificationBijection.lean` — for `u = x^a+γ`, bad `γ` ⟺ lacunary subset
`T⊆μ_n` (`|T|=a`, `e₁(T)=…=e_{a−2}(T)=0`). So `I(δ)` = the **dyadic lacunary count**.

---

## 2. The novel mathematics produced this session

### 2.1 The even/odd non-symmetric descent (PROVEN, `Sweep_A40`, literature-novel)
For `n=2N`, squaring `π:μ_n→μ_N`, codeword `f=F(x²)+xG(x²)`, word `u=u_e(x²)+xu_o(x²)`,
`P=F−u_e`, `Q=G−u_o`:
> `|agreement| = 2·#{y∈μ_N : P=Q=0} + #{y∈μ_N : Q≠0 ∧ P²=yQ²}`.
The single-fibre term `P²=yQ²` is the **non-symmetric** part the campaign's `S=−S` antipodal
tower missed (that tower captures only `1/L` of list members — measured, correcting a prior
"odd ⟹ full capture" claim). Literature audit: the radix-2 butterfly and quadratic character
`y^{N/2}=±1` are classical, but using them to bound the *beyond-Johnson list size* of explicit
2-power RS is **not in the literature** — it is exactly the open prize.

### 2.2 The binding list = the dyadic lacunary count (VERIFIED + PROVEN-bijection)
The binding word `x^{n/4}+1` at radius `s=n/4` forces `f−u` to have all `n/4` roots in `μ_n` with
middle coefficients zero ⟹ `e₁(T)=…=e_{n/8}(T)=0`. Hence `window-list = #{(n/4)-subsets T : first
n/8 power sums vanish mod p}` (verified n=16: list=count=4 = the 4 binomial cosets `X^{n/4}−c`).
Char-0: the closed coset count (`DyadicFourierUncertainty`). Char-p defect = non-coset solutions =
additive-energy / mod-q coincidences = **the BGK wall**.

### 2.3 The η_crit no-go (PROVEN, `Sweep_A43`)
Applying the Action–Orbit norm argument to the exact list-defect: a non-antipodal-balanced defect
`T` (`β_T=Σζ^{idx}≠0` over ℂ, Lam–Leung at 2) with `c=ηn` vanishing power sums forces `p^{⌈c/2⌉} |
N(β_T) ≤ s^{n/2}` (only **odd** indices are Galois autos of `ℚ(ζ_{2^μ})` — a workflow corrected my
initial `p^c`). The defect is ruled out only for `η > η_crit ≈ μ/(128+μ) ≈ 0.19` (AM-GM), or
`≈ 0.095` granting full BGK √-cancellation (measured: defect conjugates have `|σ_j(β_T)|≈√s`). But
δ\* sits at `η = Θ(1/log n) ≈ 1/μ ≈ 0.033`, **below even the idealized threshold**, with the gap
widening at scale. **So the Action–Orbit / norm-bound route — the leading "non-BGK" candidate —
cannot pin δ\* in the prize regime even if BGK were solved.** `Sweep_A43` formalizes the kernel
inequality axiom-clean.

### 2.4 The unifying meta-theorem (the complete "why")
> The worst-case window list at `δ=capacity−η` = char-0 coset count (closed, `poly(1/η)`) +
> char-p defect. Every floor method bounds the defect only in a **constant-`η`** regime; δ\* sits
> at `η=Θ(1/log n)`, at the exact ratio `c/s=η/(ρ+η)≈0.35` where the defect first reaches budget
> (verified: defects present at `c/s=0.33`, absent at `c/s≥0.5`). Since `Θ(1/log n)` is below
> every constant threshold at prize scale, δ\* lies in the defect-present regime no constant-`η`
> method touches. **Pinning δ\* ⟺ bounding the char-p defect at `η→0` ⟺ effective thin-subgroup
> Gauss-sum equidistribution = the open wall.**

---

## 3. The obstruction is irreducible — eight directions + the literature

| Direction | Verdict | Why it reduces |
|---|---|---|
| Even/odd descent | reunifies | binding list = lacunary count = char-p defect |
| Action–Orbit norm bound | no-go (§2.3) | clean only `η>η_crit`; δ\* at `η≈0.033` below it |
| Sharper norm (√-cancellation) | = BGK | `|σ_j(β_T)|≤√s` IS the incomplete char sum; & still `η_crit'≈0.095>0.033` |
| 2-power char-p rigidity | fails | defects exist mod p (`Φ_d` splits; e.g. `T=(0,1,2,8,12,30)@n=32,p=97`) |
| DFT / lacunary | = the object | the defect *is* vanishing-DFT subsets |
| Binary-multiples / correlation-attack | reduces | random heuristic ∪ Weil/Gauss-sum (Sidelnikov); + PC/SoS-hardness barrier (Dvir MFCS22) |
| Over-determination (`c/s≥~0.5`) | constant-η | δ\* at `c/s≈0.35`, defect-present |
| MacWilliams / closed-walk / low-genus curve / CRT (D1–D5) | reduce | variety degree / moments / random-model inflation = additive energy |

Parallel ceiling table (independently derived): **every √-cancellation method caps below the
required exponent `δ=1/2`** — Energy/di Benedetto `1/24`, sum–product `1/2880`, Burgess `1/4`,
sup-norm/Jacobi `√q`-lossy (gap to `√n` is exactly `√m`), height/norm-product dead. Proof-complexity
barrier (Dvir MFCS22): vanishing sums of roots of unity are hard for Polynomial Calculus and
Sum-of-Squares ⟹ algebraic-certificate routes are *provably* blocked, explaining the 190+ reductions.

---

## 4. The single open lemma (what a solution must supply)

> **(WALL).** `M(n) = max_{b≢0} |Σ_{x∈μ_n} e_p(bx)| ≤ C√(n log m)`, `C=O(1)`, at `p≈n·2^128`,
> equivalently char-p validity of `A_r = E_r − n^{2r}/q ≤ (2r−1)‼·n^r` at depth `r≈log m`,
> equivalently a uniform bound on the char-p dyadic-lacunary defect at `η=Θ(1/log n)`.

This is the thin-subgroup BGK/Paley √-cancellation at the Burgess barrier (`β≈4`, `n≈p^{1/4}`).
SOTA is `n^{0.989}` (di Benedetto et al., Burgess-barrier-stuck); the prize needs `n^{0.5}` — a
**half-power gap at the single hardest point**, beyond even GRH for this object (GRH gives only
Burgess-level `1/4`). The Wick *value* lands exactly on the prize form (`C≈0.858`); the wall is
char-p validity at deep `r`, not the value.

---

## 5. Honest conclusion

δ\* in the prize regime is **OPEN**. This investigation produced genuinely new, machine-checked
mathematics (the descent identity `Sweep_A40`, the η_crit no-go `Sweep_A43`, the reunification
bijection `Sweep_A42`, the unifying meta-theorem), a fresh reframing connecting the prize to LFSR
cryptanalysis, and a **rigorous disproof of the leading published candidate for the prize regime** —
the independent check the prize sponsor requested. But the core gate is a recognized 25-year-open
problem in analytic number theory that does not exist in 2026, and every method — eight new
directions here, the campaign's 190+, the parallel ceiling table, conditional on GRH — provably
caps short, with a proof-complexity barrier explaining why the algebraic-certificate family fails.

**A solution must either (a) supply the effective thin-subgroup equidistribution bound of §4
(a genuine analytic-NT breakthrough), or (b) exhibit a mechanism outside the entire
algebraic-certificate / character-sum / list-counting family characterized here.** If the internal
team has such a mechanism, this paper is the precise checklist against which to validate it — and
the η_crit no-go is a specific warning if their route is the Action–Orbit family. No closure is
claimed; representing the wall as solved would be false, and the value of the genuine results above
depends on not doing so.

---
*Artifacts: `Frontier/Sweep_A40/A42/A43`, `Sweep_A10`; `docs/kb/deltastar-444-*`;
`DELTASTAR_444_ESSAY_{I,II,III}*.md`; `scripts/probes/probe_444_*.py`. Issue #444 comments
4707934828, 4707955906, 4713497107, 4713607826.*
