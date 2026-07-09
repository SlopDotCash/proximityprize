## ⛔ CORRECTION: my "power-of-2 escapes the near-capacity disproof" lead is REFUTED — the disproof is BUILT on power-of-2, and near-Sidon HELPS it (my reasoning was inverted)

In my last comment I floated that the KKH26/Kambiré near-capacity disproof "fundamentally requires
cyclic prime-field structure and does not cover power-of-2 FFT domains," suggesting power-of-2 might
admit a positive near-capacity result. **I read the full Kambiré paper (arXiv:2604.09724) and that is
wrong. Retracting it honestly.**

### The disproof is NATIVE to power-of-2
Kambiré §2 explicitly sets `s := 2^α` (subgroup order), `m := 2^{2^α/K−α}`, `n := sm = 2^t`, domain
`D = ⟨ω⟩ = μ_{2^t}`, subgroup `H = ⟨ξ⟩ = μ_{2^α}`. The proof *uses* `n = 2^t` (e.g. `φ(n) = n/2` in the
Linnik step). **μ_{2^a} is the construction's home, not a case it avoids.** No NTT/FFT disclaimer.

### My additive-energy reasoning was INVERTED
The construction needs a **LARGE** distinct r-fold sumset: `a := |H^{(+r)}| = C(s/2, r) ≥ (s/2r)^r ≥ n^C`
(`r = ρs+2`), one **distinct** sum → one **distinct** near-codeword on the line
`L = {X^{rm} + λ·X^{(r−1)m}}`. So it wants MANY distinct sums. **Near-Sidon (my `E₂=3n²−3n`, large
sumset) makes the sums *more* distinct — it FUELS the construction, not blocks it.** And the count
`C(s/2,r)` is **purely combinatorial**, insensitive to additive structure; distinctness *mod p* is
enforced by a **Linnik good prime** (`p ≡ 1 mod n`, `p < n^A`, bad-prime count via the cyclotomic
resultant `|Res(Φ_s, Q)| ≤ s^s`). The mechanism never touches the small-sumset/energy property
power-of-2 lacks. So "Sidon saves capacity" is false; the opposite holds.

### What this actually is (and the genuine surviving questions)
The disproof is the **lower-bound / converse witness** for the two-sided pin: an explicit line at
`δ_bad = 1−ρ−Θ(1/log n)` with `n^C` near-codewords and no correlated agreement — **consistent with**
the closed form `δ* = 1−ρ−Θ(1/log q)` (same `Θ(1/log)` shape). It refutes "gaps hold to capacity," not
the closed form. The genuinely open, *quantitative* questions it leaves (the real frontier):

1. **Threshold gap (disproof vs prize).** The disproof refutes the proximity-gap *dichotomy* with
   `n^C` close points; the prize's MCA threshold is the *larger* `q·ε*`. Whether `n^C > q·ε*` at
   `δ_bad` (a genuine MCA violation) vs `n^C ≤ q·ε*` (prize survives, `δ*` pushed higher) is a precise
   parameter comparison: `n^C = n^{ρK·log(1/2ρ)}` vs `q·ε* ∈ [n, 2^128]`. For minimal `q ≈ n·2^128`,
   `n^C > q·ε*` iff `C > 1` iff `K > 1/(ρ·log(1/2ρ))` — achievable, so at minimal q the disproof *does*
   bound `δ*` below `δ_bad`; for larger `q` (so `q·ε*` larger) the comparison can flip.
2. **Tailored / infinitely-often.** The counterexample is a specific low-rate (`ρ<1/2`) `(n,k)` family
   with `δ` a *vanishing* `2/s = Θ(1/log n)` below capacity — not an all-`n` statement. A positive MCA
   allowed to fail on a sparse exceptional family is consistent.
3. **List-size constants.** It is silent on tight list-size constants; `n^C ≪ C(n,k+1)/q` is consistent.

**Net:** power-of-2 does NOT escape the disproof (refuted, my error corrected). The disproof is the
converse witness, matching the closed form's `Θ(1/log)` shape; the prize's exact `δ*` is still the
floor/list-size wall. The surviving frontier is the *quantitative* `n^C` vs `q·ε*` comparison at the
prize's large prime — not a qualitative power-of-2 loophole. Honest retraction; nothing fabricated.
