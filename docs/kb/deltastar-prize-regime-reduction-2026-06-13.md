# δ* in the PRIZE REGIME — exact reduction, regime pin, and the new geometric face (2026-06-13)

Worked out directly against `Research/ProximityPrize/PROXIMITY_PRIZE_WORKBENCH.lean` and the exact `CensusDomination`
definition, while the IACR-blocked papers are fetched manually. This is the regime-pinned
dissection the workbench §0 demands: it throws out everything that lives outside the prize regime
and names exactly what is left.

## 1. The exact object (no hand-waving)

`CensusDomination` (`CensusDominationWeld.lean:69`) is, unwound:
> `∀ u₀ u₁, ∀ a ≥ a₀,  #{ S ⊆ [n], |S|=a :  ∃γ, (u₀+γu₁ agrees with a degree-<k codeword on S)
>   ∧ S carries a non-degenerate (k+1)-tuple } ≤ K.`

This is **exactly the beyond-Johnson list size**: the number of large (`|S|=a > k`) agreement
sets across all scalar combinations. The pin `kkh26_deltaStar_pin_of_censusDomination` turns a
`K`-bound at every deep band `a ≥ rm+1` into `δ* = 1 − r/2^μ`. The **prize budget** is
`K ≤ ε*·q`. In the deployed calibration `q ≈ n·2^{128}`, this is `K ≤ n` — **no slack**.

## 2. Regime pin — the prize is the genuinely hard energy regime

| quantity | prize value | consequence |
|---|---|---|
| subgroup order | `n = 2^μ`, `μ ≤ ~30` (`n ≤ 2^{30}`) | — |
| field | `q ≈ n·2^{128} ≈ 2^{158}` (deployed) | `n ≪ √q = 2^{79}` ✓; `n ≫ log q ≈ 158` ✓ |
| Sidon/cyclotomic-exact `E=3n²−3n`? | needs `q > 2^n` ⇔ `n < log₂q` | **FALSE** (`2^{30} ≫ 158`) — prize is **non-Sidon** |
| halo (subset-sum collisions) | empty iff `q > 2^{N}`, `N=2^{μ−1}` | `2^{158} ≪ 2^{2^{29}}` ⇒ **halo nonempty** (`SubsetSumHaloEnergy`) |

So the prize lives in `n ≪ √q`, **outside** the small-subgroup exact regime: `E(μ_n)` is NOT the
clean `3n²−3n`. Pinning `δ*` needs the **sharp** subgroup additive energy `E(μ_n) = n^{2+o(1)}`.

**Known vs needed (the gap is the prize).**
- Needed for `K ≤ ε*q ≈ n` at deployed `q`: `E(μ_n) = n^{2+o(1)}` (the conjectured truth).
- SOTA unconditional: Shkredov `n^{22/9}=n^{2.444}`, MRSS `n^{49/20}=n^{2.45}`, HBK `n^{5/2}`. **All
  strictly above `n²`.** The `n^{2+o(1)}` conjecture is ~25 years open.
- **Brand-new 2026 check:** Hegyvári, *On the distribution of additive energy revisited*
  (arXiv 2602.01781, Feb 2026) studies the *distribution* of energies (`E₄/|A|E₃ → ∞` regions,
  `k`-fold product covering) — it does **NOT** improve the subgroup energy exponent. The gap
  stands; no 2026 source closes it.

**Verdict:** the deployed-`q` prize is *equivalent* to the open additive-combinatorics exponent.
This is the honest wall, now pinned to one named open inequality.

## 3. The NEW geometric face — Mérai–Shparlinski curve sparsity (the genuinely-new lever)

The newly acquired **Mérai–Shparlinski** (arXiv 1803.02165, *Sparsity of curves…*) bounds the
**incidence** `N_F(A,B) = #{(a,b)∈A×B : F(a,b)=0}` directly (Thm 1.3, Cor 1.2), with the curve
**sparsity** in the exponent — an **L∞** statement, not the **L²** additive energy. The agreement
sets `S` are exactly the `H`-points of the coupling curve `{Y=f(X), deg f<k}` ∩ `{Xⁿ=1}`. The MS
subgroup bound (`A,B` both subgroup-like, `H≈e≈n`, curve degree `d≈k=ρn`) gives the agreement-set
count `≈ d^{3/2} ≈ n^{3/2}` — **independent of `q`**.

**Field-size lever (genuinely new framing).** If the list `≤ n^{3/2}` held in the window, then
`K ≤ n^{3/2} ≤ ε*q` whenever **`q ≳ n^{3/2}·2^{128}`** (e.g. `q ≥ 2^{173}` at `n=2^{30}`). I.e.
*at large enough field the window would close* even without the sharp energy bound. This separates
the prize by field size: deployed `q≈2^{158}` needs the sharp `n²` energy; `q≳n^{3/2}2^{128}` would
only need the MS `n^{3/2}` incidence.

**Why it is not free (the wall, relocated — not removed).** MS Thm 1.3 requires the coupling
polynomial `F(X,Yⁿ)` **absolutely irreducible**. A *large* list ⇔ the interpolation curve
**factors** (many `Y=f(X)` components) ⇔ irreducibility **fails**. So MS gives the poly bound
*exactly when the list is already small*, and is silent exactly when it is large. The open core is
**relocated to a geometric statement**:

> **Face (v) — far-coset-curve irreducibility (new).** For the explicit smooth RS far-coset
> coupling curve, characterise the radius `δ` below which `F(X,Yⁿ)` stays absolutely irreducible.
> That `δ` is `δ*`; MS sparsity then delivers the `n^{3/2}` list bound above it. This is a
> *curve-geometry* form of the open core — never pursued in-tree, and possibly more tractable than
> the L² energy exponent because absolute irreducibility has effective (Noether/Ostrowski) criteria.

## 4. Probe evidence (`probe_window_listsize.py`, exact, smooth RS)

Worst-case list `L(δ)` of `RS[F_p, μ_n, k]` over structured deep-hole words:

| instance | capacity-edge `a=k+1` | window interior |
|---|---|---|
| n=16,k=4 (ρ=¼) | `L=273 > n²=256` | `L=0` (candidate set) |
| n=16,k=8 (ρ=½) | `L=715 ≫ n²` | `L=0` for `a≥10` |

**Reading.** (a) The list **provably exceeds `n^{3/2}` (and `n²`) at the capacity edge** — any list
bound must be **δ-dependent**, blowing up as `δ→1−ρ`; this *confirms* `δ* < capacity` and *refutes*
any unconditional `n^{3/2}` claim. (b) The window-interior worst case is **not resolved** by a small
candidate set — the true worst-word search is infeasible at prize scale (the standing computational
wall). So the probe pins the capacity-edge explosion and the face-(v) irreducibility crossover as
the object to compute, but cannot reach the prize value directly.

## 5. Honest conjecture ledger (ranked per the workbench rubric: novelty / insight / proximity / feasibility)

| candidate | δ* form | nov | ins | prox | feas | status |
|---|---|---|---|---|---|---|
| C-energy | `δ*=1−r/2^μ` via `E(μ_n)=n^{2+o(1)}` | 4 | 6 | **10** | **2** | open: reduces to the 25-yr energy exponent (in-tree) |
| C-MS-field | window closes for `q ≳ n^{3/2}2^{128}` via MS incidence | 8 | 8 | 7 | 4 | **conditional** on face-(v) irreducibility — not closed |
| **C-irred (face v)** | `δ* = sup{δ : far-coset curve `F(X,Yⁿ)` abs. irreducible}` | **9** | **9** | 8 | 5 | **new**; closed *iff* the irreducibility crossover is computed in closed form — the next target |

**None is ≥9 on all four** (the closure/`feas` axis fails — each still defers to one open object).
Per the rubric this means: **keep iterating**; do not claim closure. The honest advance this pass is
**face (v)**: a *new, never-tried geometric form* of the open core (curve irreducibility vs radius)
that (i) is genuinely novel, (ii) connects RS list decoding to effective absolute-irreducibility
criteria, (iii) lives in the prize regime, and (iv) has a concrete path (Noether forms / Stepanov on
the coupling curve) — but is not yet math-complete. It is the most promising next build.

## 6. Next build targets (machinery)
1. Formalize the MS subgroup incidence bound (Thm 1.3) as a named Lean Prop `MSIncidenceBound`.
2. Name face (v) `FarCosetCurveIrreducible dom k δ` and prove `MSIncidenceBound → CensusDomination`
   above the irreducibility radius (the easy direction) — isolating the open core as *one geometric
   Prop* instead of the energy exponent.
3. Probe the irreducibility crossover (`probe_curve_irreducibility.py`): for small smooth RS, factor
   the GS interpolation curve at each band and locate where absolute irreducibility breaks — does it
   coincide with the in-tree exact `δ*` pins? If yes, face (v) is the right form.
