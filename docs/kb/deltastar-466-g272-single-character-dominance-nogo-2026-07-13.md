# δ* / #466 — G272: the single order-2 character does not dominate the CORE covariance sign

**Date:** 2026-07-13
**Lane:** direct Opus 4.8 formalizer (cron)
**Branch:** `research/proximity-prize` (never `main`, per #499)
**Status:** LANDED single-character no-go (axiom-clean). CORE remains OPEN / ON-BGK.

## Object

Building on G271, the centered coordinate mass `P(x) = (p·W_G(x) − SW)·(p·R_r(x) − SR)` is constant
on the multiplicative `G`-cosets of `𝔽_p^*` (`G` the order-`n` 2-power subgroup, `SW = n²`,
`SR = Σ R_r`). Hence the sponsor gate factors exactly through the cyclic quotient
`ℤ_m = 𝔽_p^*/G`, `m = (p−1)/n`, and by Plancherel over `ℤ_m`:

```
p·A_r = P(0) + Σ_{j ∈ ℤ_m} Q(j),   Q(j) = n·P(g^j)      (orbit reconstruction, exact)
      = P(0) + Σ_{χ ∈ Ẑ_m} Ŵ(χ) · conj(R̂_r(χ)).
```

## Question resolved (rank-1 from both G270 referee and G271 formalizer handoff)

The G270 census showed the coarse even/odd *families* cancel (magnitudes `10⁴–10⁵ × |A_r|`, opposite
sign). The remaining rank-1 open question: does the **single order-2** (quadratic / Legendre-on-
quotient) character term track `sign(A_r)` where the coarse families fail?

- If **yes** → the target factors through one Jacobi-sum-shaped covariance, a genuinely smaller object
  with classical (Weil) estimates.
- If **no** → the frontier is irreducibly multi-character; effort stays on the full labelled covariance.

## Result: DEAD (single-character dominance refuted)

Canonical CORE model (identical to G269/G271, computation of record): `W_G(x)=#{(y,z)∈G²:2y−z=x}`,
`R_r=dp_r⋆dp_{r-1}`, `A_r=p·Σ W_G R_r − SW·SR`, `SW=n²`, `SR=C(n,r)C(n,r-1)`.

**Correct object (fixes a subtle bug).** The single order-2 term in the Plancherel decomposition is
`Ŵ(χ₂)·conj(R̂_r(χ₂))`, the product of the SEPARATE transforms of the G-invariant profiles `W,R`
restricted to `ℤ_m`, NOT the order-2 Fourier coefficient of the pointwise product `P=W·R` (which
convolves every pair `χ·χ'=χ₂`, a different object). Since `χ₂(j)=(−1)^j` is a real character,
`wchi2=Ŵ(χ₂)=Σ_j w(j)(−1)^j` and `rchi2=R̂(χ₂)=Σ_j r(j)(−1)^j` are exact integers, and the term's
sign is `sign(wchi2·rchi2)`.

Exact integer probe `scripts/probes/g272_single_character_dominance_probe.py` over the balanced
`n=16, r=5` census at every even-`m` prime `p<2600` (22 non-degenerate cells):

- Orbit reconstruction `p·A = P(0) + n·Σ_j w(j)r(j)` holds **exactly in 22/22 cells** (H_const).
- `sign(wchi2·rchi2) = sign(A)` in only **7/22** cells (rate `0.318`, below chance), realizing **all
  four sign combinations** of `(sign A, sign term)`:

  ```
  p = 929:  A = +136655344 > 0   wchi2=3716   rchi2=-7746931   term = -28787595596 < 0   (+, -)
  p = 97:   A = -6285008 < 0     wchi2=194    rchi2=244828     term = +47496632 > 0     (-, +)
  p = 257:  A = -1051408 < 0     wchi2=-257   rchi2=650210     term = -167103970 < 0    (-, -)
  p = 641:  A = +28460944 > 0    wchi2=1282   rchi2=2709507    term = +3473587974 > 0   (+, +)
  ```

- Many cells even have `term=0` (the χ₂ factor vanishes), so the single order-2 term carries no
  reliable sign information at all.

The coarse even-family (of the product) is separately **target-consuming**: its complementary-
threshold lower bound is algebraically equivalent to `A_r > 0`, so it is not a weaker route either.
Only the genuine single order-2 Plancherel term is the candidate weaker object, and it fails.

## Lean payload (axiom-clean)

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G272SingleCharacterDominanceNoGo.lean`, namespace
`ArkLib.ProximityGap.Frontier.G272SingleCharacterDominanceNoGo`, imports `Mathlib.Tactic` only:

- `charTwo f` : the order-2 character functional `Σ_j f(j)(−1)^j` of a quotient profile; applied to
  the centered profiles `w`, `r` it is the exact-integer real transform `Ŵ(χ₂)`, `R̂(χ₂)`.
- `charTwoTerm w r := charTwo w * charTwo r` : the **correct** single order-2 Plancherel term
  `Ŵ(χ₂)·R̂(χ₂)` (product of separate transforms).
- `charTwoTerm_neg_iff_opposite_sign` : the term is negative iff the two factors have opposite strict
  sign, i.e. it is a free product of two independent real transforms.
- `family_split`, `charTwo_eq_even_sub_odd`, `evenFamily_consumes_gate` : coarse even/odd-family
  bookkeeping and the target-consuming equivalence `(evenFamily Q > −(P0 + oddFamily Q)) ↔ gate P0 Q > 0`.
- `term_sign_decouples_pos` / `term_sign_decouples_neg` : recorded decoupling witnesses
  (`0 < A_929 ∧ wchi2_929·rchi2_929 < 0`; `A_97 < 0 ∧ 0 < wchi2_97·rchi2_97`), by `decide`, **axiom-free**.
- `term_sign_agrees_neg` / `term_sign_agrees_pos` : same-sign witnesses (`p=257` both-neg, `p=641`
  both-pos), needed to also refute the anti-correlation law.
- `not_term_certifies_gate_sign` : packaged no-go bundling all four sign combinations.
- `no_fixed_order2_sign_law_either_polarity` : any universal law of **either** polarity
  (`∀ A t, (0<A ↔ 0<t)` or `∀ A t, (0<A ↔ t<0)`) yields `False` on the recorded cells.

Axiom audit: `family_split`, `charTwo_eq_even_sub_odd`, `evenFamily_consumes_gate`,
`charTwoTerm_neg_iff_opposite_sign`, `no_fixed_order2_sign_law_either_polarity` are
`[propext, Classical.choice, Quot.sound]`; the four `decide`-based `term_sign_*` witnesses and
`not_term_certifies_gate_sign` depend on **no axioms**. No `sorryAx`, no `native_decide`.

## Scope / honest boundary

Single-character no-go, not a sponsor covariance estimate and not prize closure. The recorded scalars
`(A, wchi2, rchi2)` are the computation of record (the float-free probe, G214/G220/G266/G269
convention); Lean certifies the abstract functional identities, the target-consuming family
equivalence, and the
two-sided sign-decoupling on the recorded cells, not an in-Lean re-derivation of the orbit sums.

**Positive consequence:** the minimal surviving object is confirmed to be the **full character-
weighted quotient covariance** `Σ_{χ≠1} Ŵ(χ) conj(R̂_r(χ))`. The sign lives in fine multi-character
inter-orbit interference at the square-root-cancellation scale, not in any single character. Surviving
admissible route unchanged: direct row-labelled sponsor Jacobi/cyclotomic covariance proved against
the row label at each rank. Live prize face at `r = 5,6`:
`Re Σ_{χ≠1} Ŵ(χ)·conj(R̂_r(χ)) > threshold`. CORE OPEN / ON-BGK.

## Next formalizer target

The frontier is now irreducibly multi-character. The next genuinely-new invariant is a **two-character
(order-2 ⊕ order-4, or the two lowest-conductor pair) interference test**: does any *fixed pair* of
low-order characters reconstruct `sign(A_r)` across the census where each single character fails? If a
bounded-conductor sub-sum tracks the sign, the target may factor through a small Jacobi-sum family; if
even the low-conductor pair fails, the multi-character irreducibility is quantitatively confirmed and
effort stays on the full labelled sponsor covariance.
