# Attack #10 — LD⇒MCA collapse (B4) and genuinely-alternate reductions avoiding per-frequency sums

**Date:** 2026-06-27 · **Issue:** #464/#444/#407 · **Angle:** B4 ([ABF26] §5) + orthogonal reductions
**Verdict:** PARTIAL / clean refutation of the route. The LD⇒MCA path does NOT route through the
per-frequency character sum (Paley), but it reaches the prize window **only above list-decoding
capacity for explicit RS**, an equally-open and arguably harder wall. It does not bypass the prize.

---

## 1. The question

The two-sided conditional pin (`Frontier/_PrizeFloorOfBGK.lean`) reduces the prize to
`WorstCaseIncidenceBounded` (BCHKS Conj 1.12, the line-ball incidence with √q cancellation), whose
analytic context is the BGK sup-bound `M = max_{b≠0}|η_b|` = nontrivial eigenvalue of the
generalized Paley graph. ~60 sessions reduce every *analytic* route to this wall.

B4 asks for a **genuinely different reduction**: [ABF26] §5 Theorem 5.1 (GCXK25 Thm 3) turns a
**list-decoding** bound into an **MCA** bound, avoiding the per-frequency sum entirely. Does a
provable interleaved/explicit-RS list-decoding bound imply a good MCA bound inside the window?

## 2. The in-tree substrate (read, all proven)

- `InterleavingStabilityMCA.epsMCA_interleaved_eq` — **EXACT** invariance:
  `ε_mca(C^⋈t, δ) = ε_mca(C, δ)`. Interleaving the code is *free* (no width factor) — but by the
  same token gives **zero** improvement on `δ*`. The Jo26 headline is a stability theorem, not a
  Johnson-beating lever.
- `Connections/ListDecodingAndCA.linear_listSize_to_epsMCA_gcxk25` (T5.1): from a list-decoding
  bound at radius `δ_LD`, list size `L`, slack `η`, produces
  `ε_mca(C, 1 − √(1 − δ_LD + η)) ≤ (L²·δ_LD·n + 1/η)/q`.
  The honest reduction `_of_bad_count` / `_of_residuals` is fully proven; the only open input is
  the GCXK25/GKL24 per-stack bad-count `|Bad| ≤ L²δn + 1/η`. **This input is NOT Paley** — it is a
  first-moment agree-domain count.
- `SubJohnsonListBound`, `JohnsonListBound` — the only *unconditional* list-size regimes.

## 3. The proof attempt (T5.1 as an MCA floor)

To pin `δ*` inside the window via T5.1 we need, at the prize budget `q·ε* = n`:

  (i) the produced MCA radius `r_MCA = 1 − √(1 − δ_LD + η)` to land **above Johnson** `1 − √ρ`;
  (ii) the bound `(L²·δ_LD·n + 1/η)/q ≤ ε* = 2^-128`, i.e. `L²·δ_LD·n + 1/η ≤ n`.

**Gate (i) — the Johnson ceiling of the lift.** This is the load-bearing algebra, formalized
axiom-clean in `Frontier/_Attack10LDtoMCAJohnsonCeiling.lean`:

> `johnsonLiftRadius_gt_johnson_iff`:
> `(1 − √ρ) < (1 − √(1 − δ + η))  ↔  1 − ρ + η < δ`.

So the lifted MCA radius beats Johnson **iff** the list-decoding radius `δ_LD` exceeds
`1 − ρ + η`, i.e. exceeds **list-decoding capacity** `1 − ρ`. The contrapositive
`ldRoute_window_needs_above_capacity` packages this: a *below-capacity* explicit-RS list-decoding
bound yields an MCA radius **at or below Johnson**, never inside the window interior.

**Gate (ii) — the budget.** `q·ε* = n`, so we need `L²·δ_LD·n ≤ n`, i.e. `L²·δ_LD ≤ 1`. With
`δ_LD > 1 − ρ` (forced by (i)) and `δ_LD < 1`, this needs `L = 1` — *unique* decoding — which
is impossible above capacity, where the list size is super-polynomial / unbounded.

## 4. Self-refutation

The route is doubly walled, and **neither wall is Paley**:

1. **(i) forces above-capacity list decoding of the explicit code.** Getting any MCA radius past
   Johnson via T5.1 requires `δ_LD > 1 − ρ`. List-decoding *explicit fixed* RS codes above
   capacity (with bounded list) is itself a major open problem — exactly the Grand List Decoding
   Challenge that ABF26 poses *alongside* the MCA challenge. It is not Paley, but it is not
   provable for explicit RS either; the only proven regimes (`JohnsonListBound`,
   `SubJohnsonListBound`) are at-or-below Johnson and sub-Johnson with no useful list-size.
2. **(ii) the L² budget collapses.** Above capacity the list blows up, so `L²·δ_LD ≫ 1` by an
   astronomical margin; the produced `ε_mca` bound is `≫ 1`, vacuous.

**Interleaving (B4 proper) gives nothing extra.** `epsMCA_interleaved_eq` is an *equality*: the
interleaved code has the *same* `δ*` as the base code. Interleaved list-decoding for explicit RS
still bottoms out at the single-code list-decoding radius; the interleaving width `t` is free but
cannot push `δ*`. So "good interleaved LD ⇒ good MCA" is true but circular — it needs the same
above-capacity LD input.

**Orthogonal-reduction survey (none crosses):**
- (a) BCIKS20 proximity gap / correlated agreement: its CA floor is exactly the line-ball
  incidence object `epsMCA_ge_far_incidence` — that *is* the Paley/incidence wall (face 4), not an
  escape.
- (b) Johnson-bound interleaving: proven up-to-Johnson only; interleaving is `ε`-stable (equality),
  so cannot push past Johnson. This is precisely what `johnsonLiftRadius_gt_johnson_iff` quantifies.
- (c) WHIR/STIR list-decoding machinery (`Whir/MCAJohnson*`): the K4 cell residuals are
  Johnson-regime; the hard-regime files reduce to the same per-cell package supply
  (`Hab25JohnsonPackageSupply.CellPackageSupply` = face 1), i.e. back to the open core.

## 5. Lever analysis — is there a genuinely orthogonal route?

The finding is structurally clean and *positive in a limited sense*: **the LD route is genuinely
orthogonal to Paley** (its open input is a first-moment/list-size count, not a character sum). But
it relocates the prize from one open wall to a *different* open wall:

| Route | Open input | Nature |
|---|---|---|
| Direct floor (`_PrizeFloorOfBGK`) | `WorstCaseIncidenceBounded` | line-ball incidence / Paley √q |
| LD⇒MCA (T5.1) | explicit-RS list-decoding **above capacity** `δ_LD > 1−ρ`, bounded `L` | list-decoding capacity |

The two walls are **provably distinct surfaces** (`johnsonLiftRadius_gt_johnson_iff` separates them
by the capacity threshold), but the LD wall is, if anything, *harder*: capacity list-decodability
of explicit fixed RS is open even non-quantitatively, whereas the incidence side has a proven
average (√|G|) and only the worst-case sup is open. So the LD collapse does **not** bypass the
prize; it is an honest alternate reduction to a sibling open problem.

The one genuinely new, exploitable fact: **interleaving is exactly free** (`epsMCA_interleaved_eq`),
which means any future explicit-RS above-capacity LD bound transfers verbatim to all interleaved
widths with no `δ*` loss. If the LD-capacity wall ever falls for explicit RS, T5.1 + interleaving
stability would close the MCA side *without touching Paley*. That is the only escape hatch this
angle reveals, and it is gated on a different open problem.

## 6. Honest verdict

- **Does NOT close the prize.** The LD route needs above-capacity explicit-RS list decoding.
- **Does NOT reduce to Paley.** Genuinely orthogonal: open input is a list-size/first-moment count.
- **PARTIAL success:** an axiom-clean Lean brick (`_Attack10LDtoMCAJohnsonCeiling.lean`,
  `johnsonLiftRadius_gt_johnson_iff` + `ldRoute_window_needs_above_capacity`) pins the *exact*
  capacity threshold at which the T5.1 lift can enter the window, refuting the below-capacity LD
  route and naming the precise remaining open input.
- **Named open input:** `LD_capacity(explicit RS): δ* ≥ 1−ρ−Θ(1/log n) ⟸ list-decode evalCode at
  radius δ_LD > 1−ρ with L²·δ_LD ≤ 1` — i.e. capacity list-decodability of the explicit
  smooth-domain RS code (Grand List Decoding Challenge), **not** Paley.

This is a clean refutation of the LD⇒MCA route *as a Paley bypass*, plus a positive structural map
of where it actually lands.
