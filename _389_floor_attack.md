## Floor attack: a clean divided-difference identity, a char-0 confirmation of N_fib, and a REFUTED mechanism (honest)

Attacking `PrizeFloorStatement` (the optimality) directly. Three results, one a refutation.

### 1. Clean identity (the explainable-subset count is exactly the binomial moment)
For a word `w`, let `M(w) = #{(k+1)-subsets S ⊆ μ_n : w|_S extends to a deg<k poly}` = `#{S : the
(k+1)-point divided difference [w;S] = 0}`. Because two codewords agree on `≤ k-1` points, **every
explainable `(k+1)`-subset lies in exactly ONE agreement set**, so
> `M(w) = Σ_c C(a_c, k+1)` exactly  (`a_c` = agreement(c,w)),
and `[w;·]` is **linear in `w`**: for `w = Σ_m w_m x^m`, `[w;S] = Σ_{m≥k} w_m · h_{m-k}(S)`, a linear
combination of **complete homogeneous symmetric functions** `h_j(S)` of the subset. So `M(w)` is the
zero-fibre of a symmetric functional, and the worst-case `M` ranges over `span{h_0,…,h_{n-1-k}}`.

### 2. Char-0 confirmation of N_fib
The fibre of `h_1(S) = ΣS` is, EXACTLY (exact `ℤ[ζ_n]`, `probe_symfib_exact.py`), the antipodal
formula `C(s/2 − r%2, ⌊r/2⌋)` at every scale tested (μ₈,μ₁₆,μ₃₂; r=3..9). Independent confirmation
that `N_fib` = the `ΣS=0` subset-sum fibre.

### 3. REFUTED mechanism (the lead it gives)
I conjectured a proof route: *`h_1` (= the monomial `x^{k+1}`) maximizes the subset fibre by
antipodal rigidity (higher `h_m` split the `{ΣS=0}` classes).* **Refuted, exact char-0:** `h_2` has a
strictly larger fibre than `h_1` (80 vs 35 at μ₁₆, r=7), and the multiplicative `∏S` is far larger
(715 = C(16,7)/16) — though `∏S` is *not* a valid word-functional (nonlinear in `w`), so it does NOT
correspond to a real list.

**The structural lesson (why it's genuinely the profile, not the aggregate).** A high-`M` word like
`x^{k+2}+c·x^k` spreads its explainable subsets across MANY low-agreement codewords (each
`a_c = k+1`, contributing `C(k+1,k+1)=1`), so its `M` is large but its list at the deep radius `t`
is small. Also the *pure* monomial `x^{k+1}` has agreement `≤ k+1` with EVERY codeword (roots of a
degree-`k+1` polynomial), so its deep list is 0 — the real extremizer is the **2-term tower word**
`x^{rm}+λx^{(r-1)m}`, whose agreement comes from `m`-power *subgroup fibres* (high, concentrated).
So the floor is NOT `max_w M(w)` (that's `h_2`/profile-blind); it is the concentration of the
agreement profile at the prize radius — exactly what `N_fib` (the tower fibre) captures and a generic
high-`M` word does not. The aggregate-count route is dead; the live target is the profile inequality.

(Negative result logged per the contract. The identity `M(w)=Σ_c C(a_c,k+1)` and the
divided-difference ⇒ `span{h_j}` framing are reusable; `probe_symfib_exact.py` reproduces.)
