# §6 Self-shred + §7 honest survivors (2026-06-15)

Adversarial attack on `deltastar-444-novel-directions-paper-2026-06-15.md`. I attack the **7 items the
paper itself flagged "live"** (R1, R2, N3, N10, N21, N24, N25) — because if those fall, the paper
contains no closure, only related-quantity deliverables and no-gos. I find that **5 of the 7 are larp**
and pinpoint the exact false step in each. This is the honest core of the method.

## §6.1 The kills (precise false step in each)

**R1 — KILLED (value-scaling ≠ code automorphism).** The claim "the consecutive word `x^{a−1}(x+1)`
is equivalent to the fixed binomial `1+x` up to a list-invariant monomial twist" is FALSE. Multiplying
the *received word* by `x^{a−1}` does **not** preserve the list: a codeword `g` (deg<k) agrees with
`x^{a−1}(x+1)` at `x` iff `g(x)=x^{a−1}(x+1)`, which is **not** the same problem as `g'(x)=1+x` because
`x^{a−1}·g'` has degree up to `k−1+a−1 ≥ k` — it leaves the code. Value-multiplication by a monomial
maps codewords to non-codewords. The only genuine symmetry is **domain dilation** `x↦ζx` (R2), not
value-scaling. R1 conflates the two. **Dead.**

**R2 — DEMOTED (dilation does not collapse to a binomial).** Domain dilation `x↦ζx` is a real code
automorphism, so `list(w) = list(w∘dilation)`. But `(x^a+x^b)∘(ζ·) = ζ^a x^a + ζ^b x^b` — a word with
*different coefficients*, not a global rescale. To reach `1+x^{b−a}` you must factor `x^a(1+x^{b−a})` =
value-scaling = the R1 error again. So dilation **does not** reduce the worst word to a fixed binomial;
it only relates equal-coefficient-pattern words, shrinking the search by a factor `n`. **Survives only
as a search reduction, not a closed count.**

**N21 — KILLED (p ≡ 1 mod n forces trivial Frobenius — no Chebotarev content).** The "effective
Chebotarev on the splitting field of the defect polynomials, closed because abelian" framing rests on a
false premise. Since `n ∣ p−1`, `p` **splits completely** in `ℚ(ζ_n)` (Frobenius is trivial — that is
*precisely why* `ω = ζ_n mod 𝔭` lands in `F_p` itself, degree 1). There is no nontrivial Frobenius to
count, hence no Chebotarev leverage: `f(ω)≡0 mod p` is a *direct evaluation* in `F_p`, not a splitting
condition. **Dead — and the reason (trivial Frobenius) is structural, not fixable.**

**N24 — KILLED (m is a fixed constant; you cannot take it large to suppress).** The "m-fold joint list
is `|F|^{m−1}`-suppressed" idea needs `m→∞`. But the Grand-list-decoding challenge fixes `m` as **a
constant** (and the MCA-relevant case is `m=2`). For fixed small `m`, the joint list of `C^m` is still
governed by the single-code house — the conjunction "S valid for all m" gives `list(C^m) ≤ min_i
list(C)` (a true but useless inequality), **not** a `|F|^{m−1}` collapse. The fabricated rate has no
basis. **Dead.**

**N25 — KILLED (one linear constraint gives no L^∞ control).** The trace identity is real and I can
even pin it exactly: `Σ_{b∈F_p^*} η_b = Σ_{x∈μ_n} Σ_{b≠0} e_p(bx) = Σ_{x∈μ_n}(−1) = −n`, so the `m`
*distinct* periods satisfy `Σ_{periods} η_b = −1`. But this is **one** linear constraint on `2^128`
values; `Im` part `Σ Im(η_b)=0` likewise. One (or two) linear constraints place **no upper bound** on
`max|η_b|` — a single conjugate can be arbitrarily large with the rest compensating. "Phase
conservation caps the house" is false. **Dead as a house-capper** (the trace is just the known first
moment).

**N3 — DEMOTED (asserts the structure that is the whole problem).** The transfer-operator framing is
fine as *bookkeeping*, but "block-triangular over the 2-tower with the non-symmetric part a single
bounded off-diagonal coupling" is **asserted, not derived**. The dyadic squaring identity only
diagonalizes the *symmetric* block; that the non-symmetric coupling is *bounded* is exactly CRACK D's
open question restated in operator language. No free lunch. **Survives only as "build the operator and
measure the off-diagonal norm numerically" — i.e. a probe, not a proof.**

**N10 — SURVIVES, but only as a probe.** "The cross-parity coupling `κ` is an absolute constant" is a
**legitimate, testable empirical hypothesis** (measured `κ=3` at n=16). It is *not* a closure: even if
`κ=O(1)` is measured for all reachable n, *proving* it for all 2-power n is the open part. But unlike
the others it is not larp — it is a real, falsifiable, potentially-theorem-yielding direction. **Keep as
the lead probe.**

## §6.2 The meta-lesson of the shred

Five of seven "live" items died on the **same two reefs** the route-elimination already charted:
(1) *confusing a char-0 cyclotomic symmetry with the char-p `F_p` picture* (R1, N21 — everything is
already in `F_p` because `p≡1 mod n`; there is no field extension, no Frobenius, no value-scaling
symmetry of the code); and (2) *mistaking a single global identity for L^∞ control* (N25 — the trace,
like every moment, is L²/L¹ and the meta-theorem already forbids it). N24 died on misreading the
challenge (fixed `m`). **This is the meta-theorem biting again, in disguise.** The paper's value is
therefore *not* its conjectures — it is the precise post-mortem locating, for each, the exact line where
it rejoins the wall.

## §7 The honest survivor set (what actually gets agent effort)

After the shred, **nothing closes the open core** — consistent with 50-conjecture/route-elimination.
What survives is real but bounded:

### §7a LIVE combinatorial probe (could yield a genuine theorem — the one real lead)
**S1 = CRACK D, sharpened (N10 + R2-as-search + N3-as-bookkeeping).** *Measure, across all reachable
2-power n (16,32,64,128, and partial 256), at fixed (ρ,η):*
  (i) the worst-case window list `L*(n,ρ,η)` over ALL words (not just lacunary) — is it constant?
  (ii) the worst *word* — is it always the consecutive `x^a+x^{a−1}` for ρ<1/4?
  (iii) the cross-parity constant `κ(n) = L*(non-symmetric worst) − tower(symmetric)` — constant?
  (iv) the dyadic transfer operator's non-symmetric off-diagonal norm — bounded?
*Outcome A:* if `L*` GROWS with n → **refutes the floor** (a publishable negative resolving the §6
honest open question on the *under-determined* side). *Outcome B:* if `L*` and `κ` are constant and a
**non-symmetric recursion** emerges → a candidate proof of the list-decoding challenge (off-BGK). Either
way it moves the needle. This is the only direction with a path to the prize that the shred did not kill.

### §7b CLOSED related-quantity deliverables (proven sub-results, honestly not the prize)
- **S2 (R4/R22).** Exact δ\* table for the smallest prize-shaped prime per `n ≤ 38` + the maximal
  exact pins (`F5,F17`-style), as one axiom-clean Lean file. A *proven, finite, unconditional* δ\* fact
  family.
- **S3 (R11/R12).** Port the *unconditional* cores of Chai–Fan 2026/861 (Action–Orbit Thm 2.1) and
  2026/858 (Threshold-Halving result A) and check budget absorption — first unconditional above-Johnson
  bounds in-tree (sidestep the literal MCA prize, but real).
- **S4 (R23/R24).** s=128 KKH26 ceiling rows *conditional on the cited Thorner–Zaman theorem* (closed
  mod citation, legitimate per §6 modularity); GG25 curve-decodability bricks.

### §7c CLOSED no-gos (sharpen the wall, prevent re-tries)
- **S5 (R17/R25).** Axiom-clean: (a) the two-sided bracket gap is a *constant* that cannot shrink;
  (b) the moment method *provably* cannot reach `r*=log m` at the prize (`r_max < r*`). Both formalize
  *why* the wall stands, so no future wave wastes effort.

### §7d The two cracks, restated honestly
- **CRACK D** is genuinely open and **combinatorial** — S1 is its assault.
- **CRACK P** (phase/Stickelberger) survived the paper but the shred shows every *specific* phase
  mechanism (N21, N25, N2-cocycle, N8-Lfunction, N14-odometer) is either trivial-Frobenius-dead or
  relocates to "phases equidistribute" = the wall in finitary form. **CRACK P is the wall wearing a
  2-adic hat.** Demote it: no agent effort until a genuinely new phase invariant appears.

**Net:** one live lead (S1), four closed-deliverable lanes (S2–S5). §8 dispatches agents on these.
No closure of the core is claimed or implied.

## §8 Reconciliation with ESSAY_IV (the prior essay→attack→rewrite cycle) — the S-IV-1 fork is resolved

ESSAY_IV (`DELTASTAR_444_ESSAY_IV.md`) closed on a single empirical fork **S-IV-1**: at the
self-similar worst word, is the list **all-spine** (`M(μ)=0`, every member an even codeword that
descends ⟹ `Λ(μ)=Λ(μ−1)`, list constant by induction ⟹ floor) or **mixed-and-growing**
(`#mixed ↑ n` ⟹ floor refuted on the explicit family)? It left this as "the arbiter."

**Iteration 1 resolves it — and the answer is NEITHER branch fires cleanly.** The fiber identity
`agreement = 2|B| + s(S)` makes "mixed members" precise: `s(S)` = singleton-fiber count = `M(μ)`'s
support. Measured/derived:
- **At the window MIDPOINT** (η≈ρ): `s(S) ≤ 1`, list constant (κ=3 confined) — the *all-spine-ish*
  branch. **But the midpoint is not the prize regime.**
- **At the window EDGE** (η→0, near capacity): `s(S) = O(n)` grows (worst word `x^15+x^4`, list
  273≈n² at n=16) — the *mixed-growing* branch.

**Why this is NOT a clean floor refutation (the subtle correct reading):** the prize lives at the
**cushion** `η = c/log n > 0`, strictly between midpoint and edge. There the window-list law gives
`L*(cushion) = 2^{Θ(1/η)} = n^{Θ/c}` — **polynomial**, not constant and not the edge's blow-up. The
budget is `q·ε* ≈ n = n^1`. So **δ\* is exactly the cushion `c*` where `n^{Θ/c}` crosses `n^1`**, i.e.
`δ* = (1−ρ) − Θ/log n` with `Θ` = the list-growth constant. The list *grows polynomially* at the
cushion (so S-IV-1's "all-spine constant" branch is false there), but it grows *only polynomially*
(so the "refuted" branch is also false) — it pins δ\* at the crossover. **Evaluating that crossover
constant `Θ` is exactly `M(n) ≤ C√(n log m)` = the wall.** ESSAY_IV's `M(μ)` non-packing compounding
bound (S-IV-2) is the same object.

**Net:** the two predecessor cracks (ESSAY_IV's S-IV-1 fork; this paper's CRACK D) are now provably
the *same* crossover-pinning problem, and it is the wall. No branch escapes. The δ\* value is
*determined* (it is the polynomial-crossover cushion) but *uncomputable in closed form* without the
effective BGK constant — which is the recognized open problem. This is the cleanest statement to date
of *why* δ\* is pinned-but-open.
