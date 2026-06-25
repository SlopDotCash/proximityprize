# Issue #464 loop note: the Thorner-Zaman `7/12` gate is arithmetic, not a prize proof

Date: 2026-06-25.

Status: **clarifying progress**, not a delta-star proof.  This note records a direct read of the
Thorner-Zaman arithmetic-progression paper and pins the exponent bookkeeping for the off-BGK
floor-localization lane.

## Evidence checked this pass

- Live issue #464 comment tail through 2026-06-22: still 24 comments; the latest comments are the
  Door-IV receipts.
- `docs/kb/deltastar-DOSSIER-v2-2026-06-22.md`, especially the §16 correction that floor-goodness
  is necessary but not sufficient.
- Local files around the floor lane:
  `_FloorLinnikExponentGate.lean`, `_FloorLinnikThornerZamanArrow.lean`,
  `_FloorLinnikTZClosure.lean`, `_FloorDominationInterface.lean`,
  `_AvD1_KKH26S128.lean`, and `_ThornerZamanPNTStatement.lean`.
- Thorner-Zaman, arXiv:2108.10878, downloaded from arXiv for this pass because no matching local PDF
  was found under `~/papers/arklib`.

I did not re-read every PDF in the 327-PDF local library during this pass.  The targeted PDF read was
only for the least-prime / powerful-modulus exponent question.

## What the paper says that matters here

The basic Thorner-Zaman theorem packages a PNT in APs with a threshold exponent `theta`; in the
generic no-exceptional-zero case the displayed threshold is `7/12`.  Corollary 1.4 gives a safe
all-moduli statement with `x >= q^12`, which is far above the floor lane's sub-quartic target.

The important separate paragraph is the powerful-modulus refinement.  In §3.1 they replace the
zero-free region using Iwaniec's result, write the squarefree kernel of the modulus as `d`, and state
a corollary whose condition is still of the form

```text
h / phi(q) >= x^(7/12 + epsilon).
```

For dyadic moduli `q = 2^a`, the squarefree part `d` is fixed (`2`), so this is the only plausible
unconditional way the floor lane gets a sub-quartic least-prime input without GRH.

## New Lean gate

I added:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PowerfulTZThetaGate.lean
```

The file proves only exponent algebra.  If `x = n^beta`, modulus `q = n = 2^a`, and
`phi(n) = n / 2`, then the main-term side `h / phi(q)` with `h = x` has size

```text
2 * n^(beta - 1).
```

So a threshold `x^tau` is covered by the exponent condition

```text
1 <= beta * (1 - tau).
```

Machine-checked consequences:

- `twelve_fifths_times_one_sub_seven_twelfths`:
  `(12/5) * (1 - 7/12) = 1`.
- `beta_ge_twelve_fifths_gate`:
  any `beta >= 12/5` clears the `tau = 7/12` exponent gate.
- `beta_three_gate_for_seven_twelfths_plus_eps`:
  `beta = 3` clears `tau = 7/12 + epsilon` whenever `epsilon <= 1/12`.
- `beta_three_seven_twelfths_plus_eps_main_term`:
  for `n >= 1`, `n^(3*(7/12+epsilon)) <= 2*n^2` under the same epsilon condition.

Validation:

```text
scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PowerfulTZThetaGate.lean
```

passed in 20 seconds.

## What this fixes

This separates three issues that have been conflated in older notes.

1. **Arithmetic exponent gate.**  The `7/12` threshold really does point to `12/5`, and `beta = 3`
   is safely sub-prize.  That part is now a small Lean theorem.
2. **Analytic prime-count input.**  The Lean theorem does not prove that Thorner-Zaman supplies the
   exact fixed-polynomial-window lower count used by the ArkLib consumer.  Existing files disagree in
   tone: `_ThornerZamanPNTStatement.lean` packages that count as the intended named TZ input, while
   `_AvD1_KKH26S128.lean` warns that the real paper may not deliver the required count in the fixed
   `log x / log q = beta` regime.  The honest way forward is to keep the count as a named analytic
   hypothesis until the paper-to-window conversion is written without handwaving.
3. **Prize consumer.**  Even a perfect least-prime theorem closes only the binder-family floor
   obstruction.  `_FloorDominationInterface.lean` already shows that a delta-star lower pin still
   needs stack domination or a direct `WorstCaseIncidenceBounded` theorem.

So the new Lean file is useful, but only as a guardrail.  It says: if the powerful-modulus PNT count
is available with a `7/12 + epsilon` threshold, then the dyadic floor lane can choose `beta = 3` and
stay below prize scale.  It does not say the analytic count is proven, and it does not say the
floor lane proves the prize.

## Attempted new tool and critique

The tempting new tool is:

```text
PowerfulDyadicPNT(beta=3):
  for all large a, the window [(2^a)^3, 2*(2^a)^3]
  contains a prime p = 1 mod 2^a.
```

Together with `FloorLocalizationUniform`, this would make every prize-scale prime good for the
explicit binder floor predicate.  It is genuinely off-BGK: it is about a prime in an AP, not
Gauss-period cancellation.

But as a delta-star strategy it fails twice.

First, the AP statement must be a real lower count or existence theorem in the fixed dyadic
polynomial window.  The exponent algebra is easy; the analytic theorem is not in Lean and must be
checked against constants, exceptional-zero handling, and the short-interval-to-window conversion.

Second, even if the AP theorem is granted, it only removes one obstruction family.  The universal
MCA lower pin asks for every stack.  A single binder profile being good is logically downstream of
the prize theorem, not upstream of it, unless a new domination theorem identifies that profile as
worst-case.

## What to do next

The next useful work is not another generic Linnik lemma.  The floor lane needs one of:

1. a fully faithful analytic note proving the dyadic `beta = 3` prime-window count from
   Thorner-Zaman §3.1, including the exact quantifier range;
2. the promised `FloorLocalizationUniform` statement from the exact profile scanner, formalized
   against the same finite-field predicate the probes use;
3. a stack-domination theorem or counterexample showing whether binder-family goodness can ever
   imply `WorstCaseIncidenceBounded`.

Absent (3), the off-BGK lane remains obstruction removal.  The prize core remains the universal
incidence / Paley-BGK wall.
