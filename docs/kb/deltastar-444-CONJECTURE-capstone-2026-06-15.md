# The δ\* conjecture — capstone (issue #444, 2026-06-15)

Single-source statement of the conjecture this campaign produces, the equivalence chain showing it
solves **both** grand challenges, and the precise open input. Honesty contract (CLAUDE.md §6): the
*conjecture* (with its open input named) is the deliverable; the *proof* of the open input is the
recognized open problem and is **not** claimed. Everything marked "proven" below is axiom-clean
(`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`, 0 `sorryAx`) and was independently
re-audited this session.

---

## 1. The conjecture (closed form, single named open input)

For explicit smooth-domain Reed–Solomon `C = RS[F_p, μ_n, k]` (`n = 2^μ`, `μ_n ⊊ F_p^*`, `n ∣ p−1`),
rate `ρ = k/n ∈ {1/2,1/4,1/8,1/16}`, prize regime `p ≈ n·2^128` (`m = (p−1)/n = 2^128`, `ε* = 2^{−128}`,
budget `q·ε* ≈ n`):

> **Conjecture δ\* (entropy-cushion law — CLOSED statement, no open quantity).**
> `δ*(ρ,n) = (1−ρ) − H₂(ρ)/log₂ n`, `H₂(ρ) = −ρ log₂ρ − (1−ρ)log₂(1−ρ)` (binary entropy).

Every symbol is a definite elementary function of `ρ, n` — **no `Θ`, no BGK constant, no open quantity in
the formula** (the adversarial shred confirmed "openMathInStatement: NONE"). It lands strictly in the
window interior at the prize `n=2^{30}`: δ\* = 0.4667 (ρ=½), 0.7230 (¼), 0.8569 (⅛), 0.9263 (1/16).

**Derivation (closed).** Both challenges = one crossover (`badScalars_eq_explainable`): δ\* is where the
worst-case window list `L*(δ)=2^{c(ρ)/η}` meets budget `ε*|F|=2^{−128}q=n=2^μ`, giving
`η*=c(ρ)/log₂ n`. The exponent `c(ρ)` is the **entropy of the bad-family support**. Two explicit families
compete: the in-tree **line** family `2^r\binom{s/2}{r}∼2^{sΦ(ρ)}`, `Φ(ρ)=ρ+½H₂(2ρ)`; and KKH26's
Appendix-A **list-center** family `\binom{s}{r}∼2^{sH₂(ρ)}`. **`H₂(ρ)` binds** (the larger count ⟹ smaller
δ\*): `listCenterRate_gt_lineRate` proves `Φ(ρ) < H₂(ρ)` for **all** `ρ∈(0,½]` axiom-clean (strict
convexity), so `c(ρ)=max(H₂,Φ)=H₂(ρ)` is **pinned in-tree, not cited**
(`Frontier/ListCenterEntropyCeiling.lean`, 6 thms, axiom-clean).

**What is proven vs open (the two-sided pin):**
- **Ceiling `δ* ≤ (1−ρ) − H₂(ρ)/log₂ n`:** the explicit list-center family. Combinatorial count
  `\binom{s}{r}≥2^{sH₂(ρ)}/(s+1)` is **axiom-clean unconditional** (`listCenter_count_ge`); the
  prize-scale prime existence is the named cited hypothesis `TZPrimeSupply` (Thorner–Zaman PNT-in-APs,
  §6 modularity) — `deltaStar_ceiling_entropy_of_TZ`.
- **Floor `δ* ≥ (1−ρ) − H₂(ρ)/log₂ n` (equality / tightness):** the **only** open input. Reduces to
  > **(OPEN) BGK/Paley house bound:** `M(n)=max_{b≢0}|Σ_{x∈μ_n}e_p(bx)| ≤ C√(n log m)`, `C=O(1)`
  (`M(n)=house` of the Gauss period, generator of `K_m⊂ℚ(ζ_p)`). The recognized ~25-year-open problem.

So the conjecture's **statement is closed and its ceiling is grounded in-tree**; only the floor (no family
beats the explicit ceiling) is open = the prize.

---

## 2. Why one conjecture solves BOTH grand challenges

- **Grand-MCA:** `ε_mca(C,δ) = max_{f₁,f₂} Pr_γ[f₁+γf₂ δ-close, (f₁,f₂) not] = max(#bad γ)/q`
  (`badScalars_eq_explainable`, proven). `#bad γ` is the far-line incidence, whose worst-case binding
  count is the same list object `L*(δ)` (proven, `FarCosetExplosion`/`MCAWitnessSpread`). So
  `ε_mca(C,δ*) ≤ ε* ⟺ L*(δ*) ≤ ε*|F|` — challenge 1 is the crossover.
- **Grand-list-decoding:** `|Λ(C^m,δ*)| ≤ ε*|F|` is the same `L*(δ*) ≤ ε*|F|` (the interleaved list is
  the worst-case window list, m fixed). Challenge 2 is the *same* crossover.
- **One number.** Both thresholds equal the cushion where `L*` crosses the budget. Pinning `Θ_ρ` pins
  both. (This is the [ABF26] §5 "two challenges are one" statement, made concrete.)

---

## 3. The equivalence chain — every route funnels to the ONE open input (each link proven this campaign)

```
δ*_C  ⟺  L*(δ) crossover                       [badScalars_eq_explainable; far-line law]
      ⟺  worst-case window list bound            [pattern count = #{(B,O₁,σ): 2|B|+|O₁|≥k}, _S2NonSymTower]
      ⟺  M(n) ≤ C√(n log m)  (the house)         [list ↔ sup-norm transport; 20-face collapse]
      ⟺  char-p additive-energy A_{r_opt} ≤ Wick [exact sandwich, _DefectOnsetOvershoot:
                                                   house^{2r}/p ≤ A_r ≤ ((p-1)/p)house^{2r}]
```

The last link is an **iff** (the moment method at `r_opt = log m` is *exactly* as strong as the prize):
`A_{r_opt} > Wick ⟺ house > Wick^{1/2r}`. So there is **no slack** — no "cleverer method" wins for free;
every route certifying the floor must supply the same deep-`r` char-p energy bound.

---

## 4. Why the open input is genuinely open (route-elimination, all proven/probed this campaign)

| Route | Why it fails at the prize | Artifact |
|---|---|---|
| Every 2nd-order method (energy/L²/λ₂/SDP/LP/cumulant/Shaw) | caps at `M ≥ n` via `(qE_r)^{1/2r}≥n` | `_MetaTheoremSecondOrderFloor` |
| Moment method at `r_opt` | char-0→char-p transfer unprovable by the **height gate** `(2r)^{n/2}<p` (fails for `r>2β≈8`); `r_opt=128` | `MomentMethodPrizeDepthNoGo`, `HeightGateNormBound` |
| Energy-falsity escape | `A_r < Wick` (TRUE) at reachable scale; overshoot ⟺ deep-`r` house lower bound = wall | `_DefectOnsetOvershoot` (iter-3) |
| Antipodal/dyadic tower (sym + non-sym) | symmetric: vacuous in-window; non-sym: `s(S)=O(n)` at edge = pattern count | `_S2NonSymTower`, `SymmetricTowerBracket` |
| 8 fresh lenses (automatic-seq, Iwasawa, p-adic Baker, determinant, binding-restriction, Newton, free-prob, Korobov) | 6 secretly-open, 2 refuted — all reduce to wall or wrong-sign | iter-2 Workflow + `DISPROOF_LOG` |
| Height/norm; Burgess; large-sieve; Habegger; EVT | block-norm `2^{n/2-1}`; range fails at `β=4`; averaging weaker; discrepancy `2^48`; white-noise | prior campaign |
| 50 closed conjectures, 12 lenses | 0 survivors | prior campaign |

**The two recurring reefs:** (i) char-0 cyclotomic ≠ char-p — since `p≡1 mod n`, `μ_n ⊂ F_p`, Frobenius
is trivial, no splitting field / Chebotarev / value-twist; (ii) a global identity (trace, any single
moment, discriminant) ≠ L^∞ control of the single largest conjugate.

---

## 5. Honest status

- **Proven this session (axiom-clean, re-audited):** `_S2NonSymTower`, `MomentMethodPrizeDepthNoGo`,
  `_DefectOnsetOvershoot`, `SymmetricTowerBracket`, `DeltaStarTableN16Fermat`, plus the 8 lens no-go
  files. Related quantities + no-gos, none tightening the window-interior core.
- **The conjecture (§1):** complete, closed-form, single named open input. Solves both challenges (§2).
- **The open input:** the effective thin-2-power-subgroup BGK/Paley sup-norm bound — a recognized
  ~25-year-open problem (SOTA `n^{1−o(1)}`, range fails exactly at the prize `β=4`). **No honest closure
  exists; none is claimed.** Proving it = the prize.

This is the terminal honest state of the campaign's exploration: the conjecture is generated and
defended from ~20 lenses; every route provably funnels to the one recognized open analytic-NT bound.
