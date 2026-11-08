# The Prize Core, Distilled — the 2-power incomplete-character-sum sup-norm (#407)

After reducing every face of δ* (MCA, list-decoding, moment, phase, concentration, cyclotomic) to a
single object and pruning the dead routes, the proximity prize is **one analytic statement**.

## The statement
Let `n = 2^μ`, `p` prime with `p ≡ 1 (mod n)`, in the **prize regime** `p ≈ n^4 … n^5` (so `n ≈ p^{1/4..1/5}`,
`n ≪ √p`). Let `μ_n ⊂ F_p^*` be the `n`-th roots of unity, `e_p(t) = exp(2πi t/p)`, and
`S_b = Σ_{x∈μ_n} e_p(b x)`.

> **CORE.**  `max_{b ≢ 0 (p)} |S_b| ≤ C·√(n · log(p/n))`  for an absolute constant `C`.

This pins `δ* = 1 − ρ − H(ρ)/(β log₂ n)` (worst-case) and solves both grand challenges (MCA = explicit-RS
list-decoding to capacity on the smooth FFT domain). Empirically the constant is `≈ 1.2` (n=8…256, multi-prime).

> **Normalization corrections (2026-10-28 audit, T48; cross R-262).** Fix these before calling the
> forms below exact equivalents.
> - **Complete monomial sum.** Over the full field the identity is
>   `Σ_{y∈F_p} e_p(b·y^m) = 1 + m·S_b`, and the nonzero-`y` sum equals `m·S_b`. So the Weil bullet's
>   `S_b = (1/m)Σ_y e_p(b y^m)` must either exclude `y = 0` or subtract the `1`.
> - **Jacobi cocycle.** `u_s u_t = (J(χ_0^s, χ_0^t)/√p)·u_{s+t}` holds only when `χ_0^s`, `χ_0^t` and
>   the product `χ_0^{s+t}` are all nontrivial. For an inverse pair (`s + t ≡ 0 mod m`) one has
>   `|J| = 1` and `g(χ)g(χ̄) = χ(−1)·p`, so the displayed law fails.
> - **Raw vs DC-corrected moments.** Keep the distinction drawn in the energy bullet below. Raw-energy
>   Wick bounds are impossible at production depth because of the principal term `n^(2r)/q`.
>   Nonprincipal (DC-subtracted) moments are different objects, and they are not shown useless by
>   that argument.
>
> The equivalences claimed among the five forms, and between them and `δ*`, are proposed
> reformulations, not all proved.

## Five equivalent forms
1. **Incomplete character sum** (above). `S_b` is real (`−1 = ζ_n^{n/2} ∈ μ_n`), `= 2Σ_{j} cos(2π b x_j/p)`.
2. **Gauss-phase DFT.** `S_b = (n/(p−1))[−1 + √p · P(b)]`, `P(b) = Σ_{t=1}^{m−1} u_t · χ̄_0^t(b)`,
   `m = (p−1)/n`, `u_t = g(χ_0^t)/√p` unimodular Gauss phases with the **Jacobi cocycle**
   `u_s u_t = (J(χ_0^s,χ_0^t)/√p)·u_{s+t}`. CORE ⟺ `max_{b}|P(b)| ≤ C'√(m log m)`.
3. **2-adic cocycle.** `S_b(μ_{2^{j+1}}) = S_b(μ_{2^j}) + S_{bz}(μ_{2^j})` (real). With
   `r_j = |S_b(μ_{2^{j+1}})| / max(|S_b(μ_{2^j})|,|S_{bz}(μ_{2^j})|) ∈ [√2,2]`, `M(n)=∏_j r_j`. CORE ⟺
   no tower-path `b` has persistent alignment: `Σ_j log(r_j/√2) = O(log log p)` for **every** `b`.
4. **Additive–multiplicative concentration.** `|S_b|` large ⟺ the multiplicative coset `b·μ_n` is
   additively concentrated near `0 (mod p)` (a Bohr set). CORE = no coset clusters beyond `√(n log)`.
5. **Autocorrelation flatness.** `|S_b|² = Σ_h r(h) e_p(bh)`, `r(h)=|μ_n ∩ (μ_n+h)|`. CORE = max Fourier
   coefficient of the additive autocorrelation of `μ_n` is `≤ n log(p/n)`.

## Why every standard tool fails (the precise obstructions — do not re-attempt)
- **Weil / monomial sums:** `S_b = (1/m)Σ_y e_p(b y^m)`, degree `m = p^{3/4}` ≫ `√p` ⟹ Weil vacuous (`=n²`).
- **Energy / moments (any order):** char-0 energy `E_r = (2r)![x^r] I₀(2√x)^{n/2}` (proven) `~ n^r`, which
  falls **below** the diagonal `n^{2r}/q` at depth `r* → β+1`; for `r > r*`, Fourier positivity
  (`Σ_{b≠0}|S_b|^{2r} = qE_r^{Fp} − n^{2r} ≥ 0`, `E^{char0} ≤ E^{Fp}`) **forces** the char-`p` anomaly
  `≥ n^{2r} − qE^{char0} > 0`. So deep-moment validity is *provably false* at the depth `r ≍ log q` the
  floor needs — the moment route caps at the **trivial** bound `n`. (Even ideal char-0 explodes:
  `bound/floor = 1.15→6420` over `n=2^4…2^30`.)
- **BGK / Bourgain–Glibichuk–Konyagin:** `≤ n^{1−δ'}`, `δ' ≈ 0.08` for `δ=1/4` ⟹ `≈ n^{0.92}`. The CORE
  needs `n^{1/2+o(1)}` — a gap of `n^{0.42}`. Insufficient.
- **Resonance (Bondarenko–Seip/Soundararajan):** fails — the Jacobi cocycle combination law is
  *contractive* (`|J|≤√p`), the eval set is the full (rigid) character group, and a hard Parseval
  ceiling caps concentration; Deligne equidistribution forbids the linear phases resonance needs.
- **#400 cyclotomic coset-rigidity:** refuted (`Θ(n²)`, not `O(n)`).

## The one provable foothold (landed)
`RootSumNormBound.lean` (axiom-clean): a sum of `≤ m` roots of unity has `|N_{ℚ(ζ_n)/ℚ}| ≤ m^{n/2}`, so a
nonzero such sum is never `≡ 0 mod 𝔭` once `m^{n/2} < p`. Secures the anomaly `A_r = 0` only for `r ≈ 2`.

## The clean sub-problems for specialists (pick one)
- **(SP1) The sup-norm directly:** prove form 1/2 — Bourgain's incomplete-sum conjecture for 2-power
  subgroups at `|H| = q^{1/4}`. (The whole prize.)
- **(SP2) The cocycle large-deviation:** prove form 3 — a worst-path/Lyapunov bound on the real
  2-adic Gauss-period cocycle. Local, self-similar; the most "dynamical" form.
- **(SP3) The autocorrelation:** prove form 5 — flat Fourier spectrum of `r(h)=|μ_n∩(μ_n+h)|`.
