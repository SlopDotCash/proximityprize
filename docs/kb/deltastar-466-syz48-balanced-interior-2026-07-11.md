# δ* / #466 — SYZ48: the balanced-interior kernel is domain-limited, not degree-limited (2026-07-11)

## One-line

On the ~62.3% **balanced interior** of the rate-1/2 band (`max(a,b,c) < ⌊S/2⌋−1`), the μ-basis
imbalance bound `ι ≤ 1` is **NOT** a degree-profile fact — `ι ≥ 2` is band-realizable over large /
algebraically-closed fields (probe: 400/400) — and the *only* thing that rescues it on the prize
domain is the **cyclotomic domain-membership** condition: the combination roots must return to `μ_n`,
which they generically do not. The root-count / level-set bound gives **no** contradiction on the
interior (honest full circle back to the SYZ39 interpolation matrix). CORE remains OPEN / ON-BGK.

## Where this sits

- SYZ44: collapsed rate-1/2 `SylvesterInjective` to one open input, `ι = ⌊S/2⌋ − δ₁ ≤ 1`
  (`S=a+b+c`, `δ₁≤δ₂`, `δ₁+δ₂=S`).
- SYZ45: refuted the pure-algebra hope — `(4,4,4)⇒ι=2` via a constant syzygy, but only for
  non-band-realizable triples (arbitrary root sets).
- SYZ47: proved the imbalance **floor** `δ₁ ≥ max(a,b,c)` on the band triangle, discharging `ι ≤ 1`
  on the *unbalanced strip* `max(a,b,c) ≥ ⌊S/2⌋−1` (~37.7%). The **balanced interior** (~62.3%)
  is left open: the floor there only gives `ι ≤ ⌊d/2⌋`.
- **SYZ48 (this):** dissects the balanced interior exactly, and decides the load-bearing question.

## The exact characterization proven (`_SYZ48BalancedInterior.lean`, axiom-clean)

Chain, all pure-ℕ or polynomial theorems (`#print axioms` = propext/Classical.choice/Quot.sound
only, no `sorryAx`):

1. `balanced_interior_imbalance_ge_two_iff` — under the SYZ44 degree-sum law, on the interior
   `ι ≥ 2 ⟺ ∃ syzygy of product-degree ≤ ⌊S/2⌋−2` (a genuine *low* syzygy strictly beneath the
   SYZ47 floor). `interior_floor_gap`: on the interior `max(a,b,c)+2 ≤ ⌊S/2⌋`, so the floor is
   *consistent with* `ι=2` — it cannot close the interior.

2. `const_ratio_syzygy_dvd` — a constant-cofactor syzygy `C c₀·W_AB + C α·W_AC + C β·W_BC = 0`
   (AB-leading) is **exactly** `W_AB ∣ (C α·W_AC + C β·W_BC)`. The roots of `W_AB` (all `a` of them)
   must be roots of the combination `P := α·W_AC + β·W_BC`, `deg P ≤ max(b,c)`.
   `dvd_scalar_gives_syzygy` = the converse (realizability) direction.

3. `combination_natDegree_le` / `combination_root_card_le` — **level-set / root-count bound:**
   `card (α·W_AC + β·W_BC).roots ≤ max(b,c)` (`Polynomial.card_roots'`). Any constant-ratio level
   set `{x : W_BC(x) = c·W_AC(x)}` has `≤ max(b,c)` points. The cap is the degree, nothing smaller.

4. `dvd_forces_degree_le` — `W_AB ∣ P` (P≠0) ⇒ `a ≤ max(b,c)`. On the *unbalanced* strip (a the
   strict max) this is the SYZ47 contradiction. On the *balanced interior* `a ≤ max(b,c)` holds
   anyway ⇒ **NO contradiction** (`balanced_no_count_obstruction`: `d ≤ max d d`). Full circle:
   the genuine obstruction is the simultaneous SYZ39 interpolation, not a degree count.

5. `imbalance_ge_two_realizable` — a scalar collapse `α·W_AC + β·W_BC = c₀·W_AB` yields `δ₁ ≤ d`
   hence `ι ≥ ⌊d/2⌋ ≥ 2` for `d≥4`. Over a large field unobstructed (pick disjoint `W_AC,W_BC`,
   form `P`, take `W_AB` a squarefree deg-`d` factor). **⟹ degree profile does not force `ι ≤ 1`.**

6. `root_of_dvd_X_pow_sub_one_pow_eq_one` — on-domain constraint: every root `r` of any divisor of
   `Xⁿ−1` satisfies `rⁿ=1` (∈ μ_n). The `μ_n` domain restricts which points `W_AB`'s roots may be.

## Probe (`probe_syz48_balanced_interior.py`) — the decisive numbers

| Experiment | Result |
|---|---|
| [1] in-domain level sets `W_BC − c₀·W_AC` over μ_60/240/336/1008 | mean **≈0.9**, max **4** = max(b,c) bound, **over-bound = 0** (cap tight, locus barely meets μ_n) |
| [2] domain-escape of `α·W_AC+β·W_BC` roots (deg 4) over μ_n | mean **≈0.87–0.97** of 4 roots land in μ_n; **~40%** of trials **ALL** roots leave μ_n |
| [3] balanced-interior `ι` on band-realizable μ_n triples (6000) | **0** `ι≥2` violations, max ι = 1 — reconfirms SYZ45/47 |
| [4] **large-field arbitrary root sets** (𝔽_{10007/100003/1000003}) | balanced-interior `ι≥2` **REALIZED 400/400** |

**Reading:** [4] vs [3] is decisive. Same balanced degree profile ⇒ `ι≥2` freely realizable off-domain
(arbitrary root sets) but 0 realizable on μ_n. The **domain**, not the degree profile, is the lever.
[2] gives the mechanism: the `a` domain-points that `W_AB`'s roots would need do not exist — the
combination roots escape μ_n.

## Verdicts (answers to the SYZ48 questions)

- **Exact characterization:** interior `ι≥2 ⟺ low syzygy (product-degree ≤ ⌊S/2⌋−2) ⟺` constant-ratio
  divisibility `W_AB ∣ (α W_AC + β W_BC)` ⟺ the ratio `W_BC/W_AC` is constant on `W_AB`'s roots.
- **ℚ̄-realizability:** **YES** — balanced-interior `ι≥2` IS band-realizable over large/alg-closed
  fields (400/400). Therefore the **μ_n domain is LOAD-BEARING**; the degree profile alone is
  insufficient. This is the sharpest possible refutation of any "pure-algebra closes the interior" hope.
- **μ_n analysis:** the rescue is exactly cyclotomic — combination roots must return to μ_n
  (`root_of_dvd_X_pow_sub_one_pow_eq_one`), and generically they do not (probe [2]). The level-set /
  root-count bound is tight but **not** contradiction-producing on the interior (`dvd_forces_degree_le`
  gives `a ≤ max(b,c)`, satisfiable). 
- **New lever?** **None exposed.** The interior kernel is confirmed *irreducible at this altitude*: it
  is the on-domain SYZ39 interpolation/cyclotomic-membership condition in final form. CORE OPEN / ON-BGK.

## Artifacts

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ48BalancedInterior.lean` (10 theorems, axiom-clean)
- `scripts/probes/probe_syz48_balanced_interior.py`
- Branch `codex/syz48-balanced-interior` off `fork/research/proximity-prize` @ 658659b0b.
