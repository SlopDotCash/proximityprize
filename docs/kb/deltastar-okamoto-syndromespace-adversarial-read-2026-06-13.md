# Adversarial read: Okamoto "Syndrome-Space Lens" (ePrint 2025/1712) — does NOT close the prize

**Verdict: the paper does not resolve the Johnson→capacity gap.** Its genuinely *unconditional*
theorem covers only `δ < (1−ρ)/3`, which is **strictly below the Johnson radius** for every rate.
In the actual open window `(1−√ρ, 1−ρ)` it offers only (a) witness-conditional rigidity whose
witness hypothesis a disjoint-support adversary would violate (a proposed, not yet constructed,
countermodel — see below), or (b) protocol modifications (independent folds / DEEP / STIR) that
*change the protocol* rather than prove CA for plain RS. The "complete resolution up to capacity"
abstract claim comes from **conflating the regime label `Δ≥2` (`k ≤ m−2`) with the much stronger
rigidity hypothesis `(r+1)k < m+1`**. This is consistent with — not a refutation of — the proven
capacity-failure results (Crites–Stewart, BCHKS25, Diamond–Gruen); the paper itself marks `Δ=0`
(capacity) as *vacuous*.

## Notation (paper's own)
`n` length, `d` dim, `m=n−d` parity checks, `t` agreement threshold, `k=n−t` error budget,
`Δ:=t−d=m−k` rank margin, `ρ=d/n`, `δ=k/n=1−t/n`. RS min distance `d_min=m+1`.
Johnson radius `δ_J=1−√ρ`; capacity `δ_c=1−ρ`. Window `= (δ_J, δ_c)`.

## The one load-bearing theorem and its true reach (Thm 7.1)
> **Thm 7.1.** If `z_0,…,z_r` distinct successful challenges and **`(r+1)k < m+1`** (`r≥2`), then
> `Σλ_i e_{z_i} = 0` (the error vectors are linearly dependent).

Proof is correct: the syndrome line `s(z)=A+zB` is affine, so `r+1≥3` points admit annihilation
weights with `Σλ_i=0, Σλ_i z_i=0`; then `w:=Σλ_i e_{z_i}` has `Hwᵀ=Σλ_i s(z_i)=0` (a codeword) and
`wt(w) ≤ (r+1)k < m+1 = d_min`, forcing `w=0`. **The catch is the hypothesis `(r+1)k<m+1`.**

**Translate the hypothesis to the radius.** `(r+1)k < m+1` ⟺ `(r+1)δn < (1−ρ)n+1` ⟺
`δ < (1−ρ)/(r+1) + o(1)`. The hypothesis *weakens* as `r` grows, so the **largest** radius is at
the minimal `r=2`:
> **unconditional rigidity (Thm 7.1/7.2) holds only for `δ < (1−ρ)/3`.**

**This is below Johnson at every rate.** `(1−ρ)/3` vs `1−√ρ`:
- ρ=1/2: `(1−ρ)/3 = 0.167` vs Johnson `0.293` — below.
- ρ=1/4: `0.25` vs `0.5` — below.
- ρ=1/16: `0.3125` vs `0.75` — below.
- ρ→1: `(1−ρ)/3` vs `1−√ρ ≈ (1−ρ)/2` — below.

So `(1−ρ)/3 < 1−√ρ` for all `ρ∈(0,1)`. The unconditional region is **strictly sub-Johnson**, i.e.
*weaker than the classical Guruswami–Sudan/Johnson list-decoding guarantee the field already had*.
It contributes **nothing** in the prize window.

## Why the window is not closed by the paper — the disjoint-support adversary (a proposed countermodel, NOT constructed)
In the region `δ > (1−ρ)/3`, every `r ≥ 2` gives `(r+1)k ≥ 3k > m+1` (up to the `o(1)` rounding), so
**Thm 7.1's hypothesis is false** and that theorem forces no codeword. The only remaining tools are:
- **Thm 6.2 (small-union witness):** rigidity *if* two successful challenges have
  `|T_{z_i} ∪ T_{z_j}| ≤ m−1`. A worst-case adversary would like to choose pairwise-disjoint supports
  of size `k` (one fresh error support per challenge), so that `|T_{z_i}∪T_{z_j}| = 2k`.
  *Correction (audit T157):* an earlier version argued "`k > (m+1)/3`, so `2k > 2(m+1)/3`, which
  exceeds `m−1`". That inequality is **reversed**: `2(m+1)/3 > m−1` holds only for `m < 5`, so for
  every non-tiny code `k > (m+1)/3` does **not** give `2k > m−1`. Indeed, on the intermediate band
  `(1−ρ)/3 < δ ≤ (1−ρ)/2` (roughly `(m+1)/3 < k ≤ (m−1)/2`) disjoint supports have
  `2k ≤ m−1` and **satisfy** the Thm 6.2 witness hypothesis. What is true is the statement restricted
  to the prize window: there `δ > 1−√ρ = (1−ρ)/(1+√ρ) ≥ (1−ρ)/2`, so `k > m/2` and `2k > m > m−1`;
  only in `(δ_J, δ_c)` does a disjoint-support choice defeat the Thm 6.2 witness hypothesis.
  Even there this shows only that **this particular hypothesis** fails; it does not by itself show
  that the line is untrapped or that the CA premise holds with no global structure.
- **Protocol remedies (Δ=1 MCA independent folds, DEEP/STIR, global locator):** these *modify the
  protocol* (add independent randomness / out-of-domain sampling). They give soundness for the
  *modified* system, not a proximity-gap/CA theorem for the **plain** RS code the prize fixes.

**Proposed countermodel (open probe target, NOT constructed or machine-checked):** a small RS code at
a radius in the prize window with a prover whose `M` successful challenges use pairwise-disjoint
size-`k` supports, satisfying the CA premise on all `M` challenges while `A,B ∉` any single
`Span(H_S)` with `|S| ≤ m−1` (not rigid). No such instance has been exhibited: one must actually
produce `A, B` and weight-`k` error vectors `e_{z_i}` with `H e_{z_i}ᵀ = A + z_i B` on disjoint
supports (with `Mk ≤ n`), and then verify non-rigidity. Until that is done this is a conjectured
countermodel, it does **not** machine-check "no unconditional rigidity in the window", and it does
not by itself contradict the paper's abstract. The verdict above rests on the reach calculation for
Thm 7.1 (sub-Johnson), not on this countermodel.

## What the paper *does* correctly establish (kept, not disputed)
- `Δ=0` (capacity) CA premise is information-theoretically vacuous (Thm 5.1/5.2) — matches CS25.
- Knife-edge dichotomy `Δ=1` (Thm 6.1): a hyperplane meets the line in ≤1 point unless globally
  trapped — clean, and it is the syndrome-space restatement of the in-tree far-coset law
  (`epsMCA_ge_far_incidence`) and RVW13 half-threshold.
- Sub-Johnson unconditional rigidity `δ<(1−ρ)/3` (Thm 7.1) — true but weaker than Johnson.
- MCA exponent addition for *independent* folds (Thm 7.3) — a protocol-budgeting rule, not a δ* pin.

## Bottom line for #389
The prize window stays open; this paper relocates nothing into it unconditionally. Its useful
residue for us: the **syndrome-space change of basis** (line vs. union-of-spans) is a clean
formalization frame for face (iv)/(v), and the `Δ=1` hyperplane dichotomy is exactly our far-coset
incidence law. The `(r+1)k<m+1` reach calculation is the lever that exposes every "syndrome-space
resolves CA" claim: demand the radius the *unconditional* step actually reaches, and it lands
sub-Johnson. **No prize closure.**
