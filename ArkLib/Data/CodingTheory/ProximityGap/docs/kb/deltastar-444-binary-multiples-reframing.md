# The defect = low-weight binary multiples of a BCH generator (#444, fresh reframing)

*Status: NEW reframing (exact), pending literature verdict on whether the fast-correlation-attack
/ low-weight-multiple literature offers a non-Johnson, non-character-sum handle. Honesty: this is
expected to reduce to the additive-energy / BGK wall (the structured deviation from the random
model), but it connects the prize to an external technique family the campaign has never mined.*

## The reframing (exact)

The prize "defect" — the char-p extra solutions making the binding list reach budget — equals,
exactly:

> **the number of weight-`s` binary (`{0,1}`-coefficient) multiples of
> `g(X) = ∏_{j=1}^{c}(X − ζ^j)` in `F_p[X]/(X^n−1)`**, where `ζ` is a primitive `n`-th root of
> unity in `F_p`, `c ≈ ηn` consecutive-root constraints, `s ≈ (ρ+η)n` the weight.

*Proof.* A defect is a size-`s` subset `T ⊆ μ_n` with `p_j(T) = Σ_{x∈T} x^j ≡ 0 (mod p)` for
`j = 1..c`. Writing `v = 1_T ∈ {0,1}^n` (indicator on `Z/n ≅ μ_n`), `p_j(T) = Σ_i v_i ζ^{ij} =
\hat v(j)` is the DFT of `v` at frequency `j` (over `F_p`). So `p_j(T)=0` for `j=1..c` ⟺
`v(ζ^j)=0` for `j=1..c` ⟺ `g(X) = ∏_{j=1}^c (X−ζ^j) | v(X)` in `F_p[X]/(X^n−1)`. ∎

So the prize is exactly: **how many low-weight binary codewords does the Reed–Solomon / BCH
cyclic code `(g)` (designed distance `c+1`) have?** — the "code ∩ hypercube" weight count.

## Why this is a genuinely new lens (and the connection)

- The `{0,1}`-coefficient (binary) constraint is the hard part. MacWilliams gives the `F_p`-weight
  distribution of `(g)`, but **NOT** the binary-entry count — that restriction is the open object.
- Finding/counting **low-weight binary multiples of a feedback polynomial** is the central step of
  **fast correlation attacks** on LFSR stream ciphers (Meier–Staffelbach; Canteaut–Trabbia;
  Chose–Joux–Mitton; Wagner's `k`-sum / generalized birthday; BKW). This technique family is
  **absent from the campaign's dead ledger** (one passing DISPROOF_LOG mention of "correlation
  attack" only). If any of it gives a *rigorous structured upper bound* (not just the random
  heuristic `C(n,s)/p^c`, which is `≈ 0` at prize and ignores the algebraic structure), it would
  be a new handle.

## The expected reduction (honest pre-registration)

The random-model count `C(n,s)/p^c` is vanishingly small at the prize (`2^{0.81n}` vs `p^c =
2^{19.75n}`), yet the actual count must reach the budget `n` near δ* — so the count is dominated
by the **structured deviation** from random, which is precisely the additive energy of `μ_n` =
the BGK wall. Fast-correlation-attack theory typically only provides (a) the random heuristic
(an *underestimate*, blind to structure) or (b) a character-sum bound (= the wall). So the
**likely** verdict is reduce-to-wall — but the literature check is the point: a structured
low-weight-multiple bound, if one exists, is the one unexplored external resource.

## What a positive result would need

A bound on weight-`s` binary multiples of `g = ∏(X−ζ^j)` that is (i) above the random model,
(ii) below the budget `n` for `p > n^{4}` at `c = ηn` with `η = Θ(1/log n)`, and (iii) does not
factor through `max_b |Σ_{x∈μ_n} e_p(bx)|` (BGK). No such bound is known; the literature check
determines whether the correlation-attack family contains one.

(Reframing exact; verdict pending agent `aa984…`.)
