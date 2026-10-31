# Multi-personality attack on the single-depth energy bound `E_{r*} ≤ (2r*−1)‼·n^{r*}` (#444)

> **Scope correction (2026-10-28 audit, T48; cross T87/T104).**
> - **The target as written is false at production depth.** The target `E_{r*} ≤ (2r*−1)‼·n^{r*}`
>   at `r* ≈ log p` uses raw finite-field energy, which the principal-mode floor `E_r ≥ n^(2r)/p`
>   makes false at production parameters (see `deltastar-444-residual-audit-2026-06-17.md`). Only a
>   DC-subtracted form can be a live input.
> - **Finite patterns are not proved identities.** The falling-factorial findings (`c_r = (2r−1)‼`,
>   `c_{r−1} = 0`, alternating lower coefficients) are exact machine computations at the depths
>   computed. "EXACTLY (all r)" is a pattern, not a proof, unless backed by the generating function.
> - **No method is excluded.** "No creative/structural/computational direction escapes" describes
>   the directions tried; it does not exclude every conceivable method.
>
> The characteristic-zero Lam–Leung matching bound itself is not in question.

Attacked the minimal residual from every creative direction/personality. Honest verdict: genuine new
STRUCTURE found (the exact falling-factorial expansion), but all directions confirm the same wall.

## 🧠 The big-brain (exact-structure) attack — genuine new finding
The exact falling-factorial expansion `E_r^char0 = Σ_{k=1}^r c_k·(n)_k` (machine-computed, exact rationals):
- **`c_r = (2r−1)‼` EXACTLY** (all r) — the leading term is `Wick·(falling factorial)`, confirming the
  decay-law shape `E_r ≈ (2r−1)‼·(n)_r ≈ Wick·exp(−r²/2n)`.
- **`c_{r−1} = 0` EXACTLY** (all r) — the second-leading falling-factorial coefficient VANISHES (a clean
  new structural identity; the energy has no `(n)_{r−1}` component).
- **Lower coefficients ALTERNATE in sign** (`c_1>0, c_2<0, …` for r≥4) — so the bound `E_r ≤ (2r−1)‼·n^r`
  does NOT follow from a naive all-positive-coefficient argument. It is the Lam–Leung matching structure
  (char-0, PROVEN), genuinely non-trivial.
**Verdict:** the energy IS the Gaussian/Wick leading term + alternating corrections; the bound is the
char-0 Lam–Leung theorem (proven) and its char-`p` transfer (the wall). Real structure, confirms the wall.

## 🎲 The probabilist — sub-Gaussian, NOT sub-random
`E_r(μ_n)` vs `E_r(random n-subset)`: μ_n has MORE additive energy than a random subset (the antipodal
`x ↦ −x` negation pairs add the `(2r−1)‼` matching structure that a Sidon-like random subset lacks). So
μ_n is **sub-GAUSSIAN** (at most the matching/Wick count) not **sub-random** (it exceeds random). The bound
`E_r ≤ (2r−1)‼·n^r` is exactly "μ_n is at most Gaussian." The random-subset majorization (conj #28) is
REFUTED — μ_n is not below random.

## 🧩 The combinatorialist — the injection is the matching, char-0 done
A bound `E_r ≤ (2r−1)‼·n^r` = an injection from energy solutions to (matchings × `[n]^r`). char-0: the
Lam–Leung pairing IS that injection (every char-0 solution is an antipodal matching of distinct values).
char-`p`: the wraparound solutions need an injection too — that is the open `W_r ≤ slack` (no clean
char-`p` injection known; = the wall).

## ⚛️ The physicist / 🌀 the dynamicist / 🔮 the schizo — all reduce
- Partition-function / free-energy / replica: `E_r` = the `r`-fold-convolution L²-norm; the "free energy"
  is the period spectrum (= the wall). Reduces.
- Renormalization / RG flow on the dyadic tower: saving-neutral (in-tree, dead). Reduces.
- Quantum/instanton suppression `exp(−r²/2n)`: the metaphor for the decay; the "instantons" are the
  wraparound = the wall. Reduces.

## Honest verdict (definitive for the computational/structural avenues)
Every personality/direction confirms the same object: the bound is the char-0 Lam–Leung energy bound
(PROVEN, the matching structure, leading `(2r−1)‼·(n)_r`) plus its char-`p` transfer (the open wall). The
big-brain attack found genuine new exact structure (`c_r=(2r−1)‼`, `c_{r−1}=0`, alternating lower) but it
confirms rather than breaches: the char-0 bound is non-trivial-but-proven, the char-`p` transfer is BGK.
**No creative/structural/computational direction escapes** — the single-depth energy at `r≈log p` is the
irreducible analytic-NT input. Genuine progress needs external analytic NT (the matching-to-char-p
injection, or the deep-order character-sum cancellation), not another reframing. NO fabricated closure.

> Machine: the exact falling-factorial expansion (`c_r=(2r−1)‼`, `c_{r−1}=0`, alternating). This is the
> honest end of the computational/structural attack: the wall is the char-`p` Lam–Leung transfer, confirmed
> from every angle.
