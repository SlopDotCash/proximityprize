# Essay II — Shredding Essay I (the adversarial pass)

*No mercy. Every direction and construct in Essay I is attacked for larp, hidden reduction,
vacuity, or false novelty. Verdicts: DEAD (reduces/refuted), LARP (not real content),
HIGH-RISK (likely reduces, unverified), or SURVIVES (genuinely live after attack).*

## 0. The framing itself is a larp

Essay I promised "25 research directions which have **provably never been tried** and **do not
or cannot reduce** to an unknown quantity." **Both halves are unsatisfiable and I knew it.**
- "Provably never tried": the campaign refuted 179+ conjectures across 12+ lenses; I cannot
  *prove* any direction is untried, only that it is absent from the written DEAD ledger. The
  honest claim is "not in the ledger," which is weaker.
- "Cannot reduce to open math": the prize *is* an open analytic-NT problem; any direction that
  pins δ\* must either bypass the BGK sup-norm or prove it. "Closed" is the *goal*, not a
  property I can assert in advance. Presenting the list as pre-certified closed was dishonest.

The correct frame, used from here on: directions are **bypass-candidates** (avoid the sup-norm)
or **climb-candidates** (prove it); each is tagged with the *specific* mechanism by which it
would collapse, and survives only until that mechanism is shown to fire.

## 1. Climb-candidates — all DEAD or HIGH-RISK (the wall is the wall)

- **R6 (Bombieri–Pila determinant method) — HIGH-RISK→DEAD.** The determinant method counts
  integral points of bounded *height* on a variety over `ℚ`/`ℤ`. Our anomaly is **lattice points
  of a prime ideal `𝔭 ⊂ ℤ[ζ_n]` reduced mod `p`** — not an affine variety over `ℚ`, and the
  "height" (archimedean size `2r = O(log m)`) is tiny, so the method's `O(H^ε)` savings are a
  *constant factor*, not the `√m` needed. Mismatched category. **Dead.**
- **R7 (Yu p-adic linear forms in logs) — DEAD by vacuity.** Yu's effective constants scale like
  `(degree)^{O(degree)}` — for `ℚ(ζ_n)`, degree `= n/2 = 2^29`. The bound is astronomically
  weaker than `1`; it cannot constrain a single anomaly term, let alone the count. Vacuous.
- **R8 (Schinzel–Zassenhaus / Dimitrov) — DEAD.** Dimitrov gives `house(θ) ≥ 2^{1/(4m)} ≈ 1`;
  we need an *upper* bound near `√(n log m)`. A near-`1` *lower* bound on the house plus the
  trace/norm (= moment) constraints is exactly the eliminated moment method. Wrong direction,
  wrong magnitude.
- **R13 (interval concentration) / R21 (sum-product expansion) — DEAD.** Both are literally the
  BGK/Burgess statement (`M` large ⟺ `μ_n` concentrates ⟺ subgroup fails to expand). `μ_n` has
  maximal doubling (it's a subgroup), so Plünnecke/PFR is vacuous — the ledger's refutation.
  Reduce-to-wall verbatim.
- **R17 (tropical/Newton-polygon), R19 (restriction/decoupling), R22 (theta/Eisenstein–cusp) —
  DEAD or fails criterion (c).** Tropicalization and decoupling control `L^p`/averages, not the
  `L^∞` single-peak — they violate the §0 necessary condition (c) "genuinely L-infinity." The
  theta/cusp bound at *fixed level `p`* is the vacuous effective-equidistribution discrepancy
  `m/√q = 2^{48}`.
- **M25 (depth-uniform char-p Lam–Leung with `r²/n` error) — LARP.** This is the open core
  *restated with an error-term costume*. "`A_r ≤ Wick·(1+r²/n)` proven for all `r ≤ n/2`" is
  exactly "char-p validity of the energy bound at depth," i.e., **the wall**. The `r²/n` error
  is asserted with zero justification. Naming the wall is not a new construct.
- **M11 (twisted Stickelberger annihilator), M6/M22 (anomaly theta / quotient sieve), M17
  (Igusa zeta) — HIGH-RISK, all effective-equidistribution in disguise.** Each rewrites the
  anomaly count as a different analytic object (theta coeff, local zeta, sieved sum), but the
  bound needed is always the *cuspidal/error term at fixed level*, which is the vacuous
  discrepancy. Stickelberger annihilation reduces *search* (find a short vector) but not
  *counting* (how many short vectors) — and counting is what the anomaly is.

**Verdict on climb-candidates:** every single one reduces to, or is weaker than, the open
BGK/ideal-SVP-counting wall. This re-confirms the 79+50+50 sweep from new angles. **No climb
survives.** Stop trying to climb.

## 2. The three SEAMS, attacked

### SEAM C (quotient 2-adic, R5/M3/M24) — DEAD by flatness.
The period sequence `b ↦ η_b` on `ℤ/m` has multiplicative DFT `η̂(χ) = Σ_b χ(b)η_b`, which is a
**Gauss sum of magnitude `√p` for every non-trivial `χ`** (Weil; the in-tree "tangent
autocorrelation" already records `|τ_h| = √p` exactly). A **flat** spectrum is the *worst case*
for any uncertainty principle: Donoho–Stark/Tao give only the trivial bound when `|η̂|` is
constant. So R5/M3 are **vacuous** — the quotient side is as flat as the domain side. M24
(`𝔭`-adic valuation spectrum) is more interesting but the pairwise valuations `v_𝔭(η_b−η_{b'})`
are governed by the *same* Gauss-sum differences; no free lower bound. **SEAM C dead.**

### SEAM B (protocol restriction, R4/R12/R16/M4/M21/M23) — DEAD as stated, ONE thin survivor.
ABF26 defines MCA as `max` over **adversarial** `(u₀,u₁)` of `Pr_γ[bad]` — the adversary picks
the worst direction *before* the challenge `γ`. So δ\*_Π = δ\* with Π = all directions; the
protocol does **not** restrict the direction family. R12/M4 as stated are **dead**. R4/R16
(genus/Chabauty on the `γ`-fibre) reintroduce the outer sum over `~m` fibres (the P4 Carlitz
failure) and Chabauty needs `ℚ` (not `F_p`). **One thin survivor:** the *correlated-agreement
premise* assumes the words `u_i` are already `δ`-close to the code on a common set — this is a
genuine sub-variety restriction (M23, discriminant stratification of "already-correlated"
directions). Whether it excludes the binding antipodal direction is **untested**. Tag M23
**HIGH-RISK, one experiment away from a verdict** (does the binding `b*` direction satisfy the
correlated-agreement premise? if not, the premise restricts the worst case).

### SEAM A (the list, not the sup) — the ONLY genuine survivor, but it is NOT a bypass.
This is the honest one, and it needs the harshest scrutiny:

- **The brutal truth: proving the window list is `O(1)` (or poly) for all 2-power `n` IS the
  grand list-decoding challenge.** It is not a bypass *of* the prize — it *is* one of the two
  prize challenges. The window-list law `L* = 2^{Θ(1/η)}` has a *proven lower bound* (KKH26 bad
  family) and an *open upper bound* (= the challenge). So "SEAM A" is "solve the prize via the
  list side instead of the MCA side." Fine — but no free lunch; the data (constancy) is
  *evidence*, the upper bound is the *whole problem*.
- **The symmetric tower is provably worthless as an upper bound.** Just measured (this session,
  `probe_444_nonsym_list_recursion.py`, two primes, p-independent): the antipodal-symmetric
  agreement sets capture **exactly 1 of L** list members in the window interior — for BOTH the
  consecutive worst word AND the "odd" worst word. The campaign's claim that odd words give
  "7/7 symmetric capture" is **FALSE** (measured 1/7). So R-anything built on `S = −S` descent
  is **dead**. The squaring identity on symmetric sets is a size-`≈1` lower bound. Useless.
- **R3 (sparse-roots), R9 (catalecticant/slice-rank), R10 (LLL/containers), R18 (BGM explicit
  list-decoding), R23 (complement energy) — HIGH-RISK.** Sparse-root bounds (R3) are
  Johnson-capped for the *non-sparse* binding `f` (the ledger's Kelley–Owen horn). Catalecticant
  (R9) is the refuted slice-rank object (`μ_n` cyclic, `d=1`). BGM (R18) is for *random* points;
  smooth points are the open case. Containers (R10) likely recover the energy bound. None is
  obviously dead, none is obviously live — they need the descent below to give them teeth.
- **R24 (Kolmogorov incompressibility) — LARP.** "The worst word is `O(log n)` bits so its list
  is determined" confuses *determined* with *bounded*. A determined quantity needs no
  incompressibility argument and gets no bound from one. Circular. Dead.

## 3. What actually survives, and the one new thing worth proving

After the shred, the survivors are **not** a list of 50. They are:

1. **The even/odd non-symmetric descent (R1/R2/M1/M2/M18), made precise this session.** This is
   the genuinely new construct and it does NOT use `S = −S`. The identity
   `|S| = 2·#roots_{μ_N}(gcd(P,Q)) + #{y: Q≠0, P²=yQ²}` (with `P=F−u_e, Q=G−u_o`, single-fiber
   term degree `O(k)`) reduces the consecutive-word list to **monomial-word lists on `μ_N`**.
   The recursion **closes** (monomials descend to monomials). **The entire question becomes: is
   the monomial-word window list constant in `N`?** This is concrete, falsifiable, and under
   test right now. If monomial lists grow, SEAM A is dead too; if they are constant with a clean
   recursion, this is a proof path for the explicit-2-power-RS list-decoding bound.
2. **M8 (plurality margin) / R14** — possibly a cheaper sufficient object than the full list;
   untested.
3. **M23 (correlated-agreement premise restriction)** — one experiment from a verdict.

Everything else is the wall wearing a hat, a vacuous import, or a larp.

## 4. The honest reduction-risk of the survivor

Even the descent has a named failure mode: **the single-fiber term `#{y: P²=yQ²}` could couple
the `(F,G)` pairs so that the list count is a *product* of monomial lists that grows.** And the
monomial list itself, if it grows like `gcd`-orbits times something `n`-dependent, kills it. The
descent is a *reduction*, and reductions are only as good as their base case. The base case is
the monomial list. **Test the base case before believing anything.** That is the next move.
