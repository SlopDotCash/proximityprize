# deltastar #466 — SYZ45: the μ-basis imbalance bound `ι ≤ 1` is geometric, not algebraic (2026-07-11)

## TL;DR (the decisive datum)

SYZ44 reduced the rate-`1/2` `SylvesterInjective` residual to **one** open input: the μ-basis
**imbalance bound** `ι = ⌊(a+b+c)/2⌋ − δ₁ ≤ 1` for the reduced pairwise-coprime band triple
`(W_AB, W_AC, W_BC)`, degrees `(a,b,c)`, `δ₁ ≤ δ₂` the two minimal syzygy product-degrees
(`δ₁+δ₂ = a+b+c`).

**Verdict: `ι ≤ 1` is a GEOMETRIC fact about band-realizable overlap triples — NOT a pure
algebraic property of squarefree pairwise-coprime triples, and NOT provable by a
symbolic-determinant factorization.** The hoped-for "resultant factors into root-differences ⇒
squarefreeness forces non-degeneracy ⇒ `ι ≤ 1`" route is **refuted**.

## The three findings

**[A] `ι ≤ 1` is FALSE for arbitrary squarefree pairwise-coprime triples at band degree profiles.**
Balanced band degrees `(4,4,4)` admit `ι = 2` via a **linear dependence** (constant syzygy):
- `𝔽₁₃` witness: roots `{0,1,2,5}, {3,4,7,11}, {6,8,9,12}` give monic squarefree pairwise-coprime
  quartics `f,g,h` with `f + 9g + 3h = 0`; `δ₁ = 4`, `ι = 2`.
- `ℚ` witness: `f = 3g − 2h` with `g` rooted `{0,1,2,3}`, `h` rooted `{4,5,6,7}`; `f` is squarefree
  (irrational roots — squarefree ≠ rational-rooted), pairwise-coprime to `g,h`, and `f − 3g + 2h = 0`.

A constant syzygy has product-degree `max(a,b,c) = 4 < ⌊12/2⌋ − 1`, so `δ₁ ≤ 4 ⇒ ι ≥ 2`.
This matches **Cox–Sederberg–Chen** μ-basis theory for planar rational curves: the μ-basis degrees
satisfy `μ₁ + μ₂ = d` with generic curves **balanced** (`μ₁ = ⌊d/2⌋`), but **unbalanced** μ-bases
(down to `μ₁ = 1`, monoid curves) exist and are **not excluded** by squarefreeness or coprimality.
So `ι ≤ 1` cannot follow from the algebra alone. **Literature verdict: unbalanced μ-bases for
squarefree coprime triples genuinely exist.**

**[B] The symbolic-determinant route is DEAD.** At the first balanced obstruction (`ι ≥ 1`) the
generalized-Sylvester threshold matrix is square; for `(2,2,2)` its determinant is an
**irreducible** degree-3 form in the 6 roots (sympy `factor` returns it unreduced — no
root-difference / discriminant factorization), and its zero locus is met by squarefree coprime
configurations (`ι = 1` is common). For `ι ≥ 2` the obstruction (linear dependence at `(4,4,4)`)
vanishes on a genuine hypersurface that squarefree+coprime configs **do** meet (witnesses [A]). No
protective factorization exists.

**[C] What forces `ι ≤ 1` is the FULL band realizability geometry.** Enforcing jointly:
- each reduced degree `≤ budget = k − 1 − t` (pairwise overlaps `m_XY ≤ k−1`), **and**
- interior slack `a + b + c ≥ 2·budget + 3` (interior cores `3s ≥ 2n+1`) — together forcing
  `min(a,b,c) ≥ 3` near-balance, **and**
- overlap regions are **proper** index-subsets of the evaluation domain (not the whole cyclic
  group),

the probe finds `ι ≤ 1` over **62 000+** configurations (4 roots-of-unity domains + 2 random
domains), **0** violations. Dropping **either** the degree cap (`(1,1,6) ⇒ ι ≥ 2`) **or** the
proper-subset restriction (full `𝔽₁₃^×` partitioned into cosets ⇒ `X⁴ − c` linear dependence,
`ι = 2`) breaks it. Note the `(4,4,4)` `𝔽₁₃` counterexample uses the *entire* group `𝔽₁₃^×`
(a `t=0`, `s=8 = 2n/3` config that **just fails** the strict interior condition `3s ≥ 2n+1`).

**Parity nuance (honest):** the earlier G172 claim "`ι = 1` only at even `a+b+c`" did **not**
reproduce here — on subgroup domains `ι = 1` occurs at *both* parities in the constructive scan
(random domain `p=101` showed even-only). The parity refinement is domain/geometry-specific, not
universal; the main `ι ≤ 1` bound is robust.

## What was proved in Lean (axiom-clean)

`Frontier/_SYZ45ImbalanceBound.lean` (`propext, Classical.choice, Quot.sound` only; no `sorryAx`):
- `imbalance_ge_two_iff_low_syzygy` / `imbalance_le_one_iff`: under SYZ44's degree-sum law,
  `ι ≤ 1` ⟺ no syzygy of product-degree `≤ ⌊total/2⌋ − 2` (pure `ℕ`).
- `imbalance_ge_of_min_syzygy_le`, `equal_degree_dependence_forces_imbalance_ge_two`: a minimal
  syzygy `δ₁ ≤ D` forces `ι ≥ ⌊total/2⌋ − D`; specialised, an equal-degree-`d≥4` constant linear
  dependence forces `ι ≥ 2`.
- `const_dep_is_syzygy`, `const_cofactor_natDegree_le` (polynomial): a nonzero constant linear
  combination is a genuine syzygy of product-degree `≤ max deg`.
- `imbalance_bound_requires_geometry`: the refutation skeleton — a degree-`d≥4` linear-dependence
  witness contradicts a hypothetical purely-algebraic uniform `ι ≤ 1`, so any proof must use band
  geometry.
- `geometric_imbalance_feeds_syz44`: interface discharging SYZ44's `himb_le` slot from the
  geometric `ι ≤ 1`.

## Honest residual

`ι ≤ 1` is **re-identified**, not discharged: it is the geometric "no low-degree linear dependence
among band-realizable overlap triples" property — empirically robust (`62 000+` configs) and
consistent with the balanced-generic μ-basis picture. It is **not** an algebraic identity and the
determinant-factorization proof route is closed. SYZ44's `min_syzygy_out_of_budget` still consumes
`ι ≤ 1` as its one geometric input. CORE remains OPEN / ON-BGK.

Probe: `scripts/probes/probe_syz45_imbalance_bound.py`.
