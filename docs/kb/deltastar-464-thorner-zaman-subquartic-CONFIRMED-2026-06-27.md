# δ\* #464 — Thorner–Zaman sub-quartic least-prime exponent: CONFIRMED (12/5)

**Date:** 2026-06-27. **Status:** resolves the §16(C) "UNCONFIRMED" flag of
`deltastar-DOSSIER-v2-2026-06-22.md` in favor of the off-BGK floor route, from the
**verbatim** text of Thorner–Zaman (arXiv:2108.10878, *Refinements to the prime number
theorem for arithmetic progressions*). **Honesty:** this does NOT close the prize — the floor
is necessary-not-sufficient (dossier §16A). It upgrades the campaign's one genuinely-different
route (bad-prime localization) from GRH-conditional to **unconditional**, with an explicit
exponent.

## The question (dossier §16C)

The off-BGK binder-floor closure needs: least prime `≡ 1 (mod 2^a)` is below prize scale
`(2^a)^4`. Ordinary Linnik/Xylouris (`q^{5.18}`) and TZ Corollary 1.4 (`q^12`) both exceed 4.
The dossier flagged the TZ §3 Iwaniec powerful-modulus refinement as the candidate for an
**unconditional sub-quartic exponent**, marked **UNCONFIRMED**.

## The answer (verbatim from the paper)

**Theorem 1.1** defines `θ = 32/37` if a Siegel zero `β₁` exists, **`θ = 7/12` otherwise**.
The asymptotic PNT-in-AP count over `(x−h, x]` holds once `λh/ϕ(q) ≥ x^{θ+ε}`, which eq (1.8)
reduces to
```
h ≥ x^{1−δ₁},  q ≤ x^{δ₂},  δ₁ + (3/2)·δ₂ ≤ 1 − θ − ε,
```
and the paper states: **"If β₁ does not exist, then the 3/2 can be replaced by 1."**

- **General Cor 1.4** (h=x, β₁ may exist, θ=32/37): `(3/2)δ₂ ≤ 1−32/37 = 5/37`, so
  `δ₂ ≤ 10/111`, `q ≤ x^{10/111}` ⟹ **x ≥ q^{111/10} = q^{11.1}** (rounded to `q^12`).
  Insufficient (matches the dossier).
- **Powerful case** (§3.1, Iwaniec eq 3.1 + [15, Lem 6.2]): for a modulus `q` with fixed
  squarefree part `d = ∏_{p|q} p`, the exceptional zero `β₁` satisfies
  `β₁ < 1 − c₁₀/(√d (log d)²)`, hence **β₁ does not exist once `q > exp(√d(log d)²/(50c₁₀))`**.
  Then `θ = 7/12`, coefficient `3/2 → 1`, and with `h = x`, `δ₁ = 0`:
  `δ₂ ≤ 1 − 7/12 = 5/12` ⟹ **x ≥ q^{12/5} = q^{2.4+ε}**.
  (Cor 3.1 / eq (3.2) states the same threshold `h/ϕ(q) ≥ x^{7/12+ε}` directly.)

## Specialization to the prize family `q = 2^a`

`q = 2^a` has fixed squarefree part `d = 2`, so `√d(log d)² ≈ 0.68` is an **absolute constant**;
the Siegel-zero threshold `exp(0.68/(50c₁₀))` is a fixed number independent of `a`. Hence for
all sufficiently large `a`, the dyadic modulus `2^a` has **no exceptional zero**, `λ = 1`,
`θ = 7/12`, and
```
least prime  p ≡ 1 (mod 2^a)   ≪_ε   (2^a)^{12/5 + ε}   =   (2^a)^{2.4 + ε}.
```
(With `h = x = q^{2.4+ε}`, the main term `x/ϕ(q) ≈ q^{1.4} → ∞` dominates the error, so a prime
exists in the AP below `q^{2.4+ε}`.) Effective and unconditional — **no GRH**.

## Consequence for the in-tree floor route

`2.4 < 4`, with margin. The named in-tree input `ThornerZamanPNT` / the supply structure
`KKH26ThornerZaman.TZPrimeSupply` (carried as a named hypothesis) now has a **literature-confirmed
unconditional discharge for the dyadic family at any β ∈ (12/5, 4]**. Concretely:
- the floor-good closure `smallestPrime(1 mod 2^a) < (2^a)^4 ⟹ every prize prime good for the
  binder predicate` is now **unconditional** (was GRH-conditional / TZ-unconfirmed);
- the concrete `tzPrimeSupply_*_two` ladder (β=2, n=32…16384) lives strictly *below* the general
  guarantee β=12/5 — those are explicit β=2 witnesses, consistent with (not implied by) the
  general β=2.4 theorem;
- formalizing TZ Cor 3.1 in Lean remains a large analytic-NT project; the honest in-tree status
  stays a named `ThornerZamanPNT` hypothesis, but its mathematical truth and exponent are now
  pinned, not open.

## What this does NOT do (honesty contract)

- It does **not** pin δ\* in the window interior. Per dossier §16(A), floor-goodness is a
  *consequence* of the prize bound (`δ*-pin ⟹ floor-good`), never the reverse; closing the
  binder family removes one obstruction, the worst-case far-line incidence
  `M(μ_n) = max_{b≠0}‖Σ_{y∈μ_n}ψ(by)‖` (the BGK/Paley wall) is still the gate.
- It does **not** supply a universal stack-domination theorem from the binder predicate to
  `WorstCaseIncidenceBounded`.
- The prize core remains **OPEN and ON-BGK**.

## Net

A real, verifiable advance on the campaign's one off-BGK lever: the analytic input the dossier
flagged "UNCONFIRMED" is **CONFIRMED at exponent 12/5 = 2.4**, unconditional, for the exact
dyadic family the prize uses. Correct dossier §16(C) accordingly. The wall is untouched.

— verified from arXiv:2108.10878 verbatim (Thm 1.1, eq 1.8, Cor 1.4, §3.1 / Cor 3.1, eq 3.2).
