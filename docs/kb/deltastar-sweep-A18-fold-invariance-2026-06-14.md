# A18 / K1 (#334-T02): KKH26 ceiling-witness fold-invariance — verdict

**Date:** 2026-06-14 · **Status:** REFUTED (strong / ceiling-improving form) · **Type:** numerical-probe
**Artifact:** `scripts/probes/sweep_A18_fold_invariance.py` (exit 0, exact arithmetic over F_q)

## The question

K1 (issue #334 execution-order item 1) asked whether the **KKH26 near-capacity bad line**
— the explicit ceiling witness pinning `δ* ≤ 1 − ρ − Θ(1/log n)` strictly below capacity —
is **fold-invariant** on the smallest smooth (2-adic) tower under the in-tree FRI fold rule,
and, if not, whether **one fold strictly shrinks the bad-event family**, yielding a
**μ-dependent ceiling**

> `mcaDeltaStar(C_{L/H}) ≤ mcaDeltaStar(C_L) − c(μ)`   (strictly *inside* KKH26).

K1 is **mutually-falsifying with K4 (zero-slack):** if the ceiling has per-fold slack, K4 is
wrong; if the ceiling is geometrically fold-stable, K1's strong form dies.

`DISPROOF_LOG.md` (lines 27–55) had killed only the **cheap form** at the **even cofactor**
(an `m`-step: `m` even ⟹ `(e+c)/2` with `c=0` halves `m`, invariant), and explicitly left
open: *"R2 survives only in a narrower form: a bottom-level odd-cofactor statement, or a fold
transport that changes the KKH split parameter `s` rather than merely halving `m`."* This
probe runs exactly that bottom-level (s-step, `m=1`) measurement end-to-end.

## Setup (matches the in-tree object)

KKH26 stack on `H = ⟨g⟩`, `|H| = n = s·m`, `s = 2^μ`, inner group `G = ⟨g^m⟩`, `|G| = s`:
`u₀ = X^{rm}`, `u₁ = X^{(r−1)m}`, bad scalars `λ_S = −∑_{a∈S} a` over `r`-subsets `S ⊆ G`.
Close-point count (KKH26 Prop 1, in-tree `kkh26_badline_closePoints`):
`N_close(s,r) = 2^r·C(2^{μ−1}, r)`; ceiling `δ* ≤ 1 − r/s` (in-tree `kkh26_mcaDeltaStar_le`).

The word-level fold trichotomy is already **proven** in `KKH26FoldTransport.lean`:
- (1) `m` even: exact β-free covariance `→ (s, m/2, r)`; inner group **literally unchanged**
  `(g²)^{m/2} = g^m` (`sq_pow_half`) ⟹ census = same field set.
- (2) `m=1`, `r` even: halving `(X^r, X^{r−1}) → (Z^{r/2}, β·Z^{r/2−1}) = (s/2, 1, r/2)`.
- (3) `m=1`, `r` odd: total collapse to one monomial pencil `(β+λ)·Z^{(r−1)/2}`.

What A18 adds is the **never-measured census + ceiling** through the s-step. The probe
computes the **exact bad-scalar census** `|Λ(s,r)| = #{(−∑_{S} a) mod q}` and `N_close`, and
the ceiling `1 − r/s`, descending the tower, over a clean prime ladder `q ≡ 1 (mod 2^μ)`
(`q ∈ {193, 257, 449, 577}`).

## Findings (exact)

**Q1 — m-step (even cofactor): INVARIANT.** Inner generator fixed; `|Λ|`, `N_close`,
ceiling all identical (`|Λ|: 40→40`, `193→193`; ceiling 0.625, 0.6875 unchanged). Re-confirms
the DISPROOF_LOG even-cofactor result.

**Q2 — s-step (odd-cofactor bottom): the SUPPLY strictly shrinks.** Per fold the bad-event
family collapses:

| descent | `N_close` | `|Λ|` (true) |
|---|---|---|
| (32,8)→(16,4)→(8,2)→(4,1)→collapse | 3294720 → 1120 → 24 → 4 → 1 | (sat) → 449 → 25 → 4 → 1 |
| (16,8)→(8,4)→(4,2)→(2,1)→collapse | 256 → 16 → 4 → 2 → 1 | (sat) → 41 → 5 → 2 → 1 |
| (8,4)→(4,2)→(2,1)→collapse | 16 → 4 → 2 → 1 | 41 → 5 → 2 → 1 |

Both the close-count `N_close` and the census `|Λ|` drop strictly each s-step (and `r` odd
collapses to census 1). Census is field-independent once `q` exceeds it (small-q values equal
to `q` are pure **saturation** `|Λ| ≥ q`, not a real q-dependence: s=16,r=4 → true census 449
stable for `q ≥ 449`; s=8,r=4 → 41 for all q).

**Q3 — μ-dependent ceiling: NO.** The surviving (halving) regime sends `(s,r) → (s/2, r/2)`,
so the relative radius **`r/s` is fold-invariant**, hence the per-fold ceiling change

> `Δ = (1 − r'/s') − (1 − r/s) = 0`   for **every** tested `(s,r)` (32,8)/(16,8)/(64,16)/(32,16).

## Verdict — REFUTED (strong form); K4 zero-slack corroborated

The bad-**event** family (the ε-mass supply `2^r·C(s/2,r)/q`) **strictly shrinks** per
s-step, but this is exactly the budget the KKH26 ceiling **already accounts for** via the
prime threshold `p > s^{s/2}`. The δ-**ceiling** `1 − r/s` is **geometrically fold-stable**
because `r/s` is conserved under the halving. So:

- There is **no** `mcaDeltaStar(C_{L/H}) ≤ mcaDeltaStar(C_L) − c(μ)` of the conjectured form.
  The KKH26 ceiling `1 − ρ − Θ(1/log n)` does not improve per fold.
- A fold-based protocol argument that crosses an s-step **escapes this particular
  construction class** (its supply collapses), but yields **no μ-dependent strengthening**
  of the worst-case ceiling — a fresh bad family at the smaller level reinstates `1 − ρ`.
- **K4 (zero-slack) is corroborated, K1's strong form refuted** (the mutually-falsifying
  pair resolves toward K4): the ceiling has no per-fold slack to give.

## Honest residual / what is NOT closed

This refutes the *ceiling-improving* reading of K1. It does **not** lower-bound `δ*` (it is a
statement about the KKH26 upper-bracket witness, not the prize floor). The open core (the
B/energy/halo/list face, BGK wall) is untouched. The result is **negative and localizing**:
it removes "fold the ceiling down the tower" from the route list and points the supply-shrink
observation back at the ε-budget the threshold ledger already encodes. The shrink magnitude
`2^r·C(s/2,r) → 2^{r/2}·C(s/4,r/2)` is itself the per-s-step factor of the bad-line
construction class and is consistent with the in-tree `KKH26FoldTransport` docstring's
"construction-class supply drops" statement — now quantified end-to-end with the exact census
and the Δ=0 ceiling verdict.
