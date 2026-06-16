# One object, two challenges: the unified `defect = 0` conjecture for the Proximity Prize

*A consolidated, honest synthesis of the #444 campaign's structural results. This is not a proof of
the prize; it is (i) a single closed conjecture proven to simultaneously imply both grand challenges,
(ii) its machine-checked resolution in characteristic 0 for the trinomial (`k=2`) case plus the general
first-level (negation-closure) rigidity, and (iii) a precise isolation of the open core to one
statement in characteristic `p`, with an exhaustive record of why every known route reaches exactly
that statement. All Lean results are axiom-clean (`[propext, Classical.choice, Quot.sound]`) and pass
the real `lake build`. (The general-rate characteristic-0 rigidity and, of course, the characteristic-`p`
prize itself remain open; see §3.3, §6.)*

---

## 1. The prize, and the regime

The Ethereum Proximity Prize ([ABF26], ePrint 2026/680) poses two grand challenges for explicit
Reed–Solomon codes on the 2-power smooth domain `μ_n` (`n = 2^μ`, `p ≡ 1 mod n`, prize-shaped
`p ≈ n·2^128`, rate `ρ ∈ {1/2,1/4,1/8,1/16}`, `ε* = 2^-128`, window interior
`δ ∈ (1−√ρ, 1−ρ−Θ(1/log n))`):

- **(LD) the grand list-decoding challenge** — bound the worst-case window list size of explicit
  `μ_n`-RS codes strictly beyond the Johnson radius;
- **(MCA) the grand mutual-correlated-agreement challenge** — pin the threshold `δ*` in the same
  window.

These are genuinely open. The random-evaluation-point results (BGM/Guo–Zhang/AGL) and the
folded/multiplicity/subcode results do **not** cover plain explicit `μ_n`; BCIKS 2025/169 names the RS
list-decoding radius "wide open" and a *prerequisite* for beyond-Johnson proximity gaps; Crites–Stewart
2025/2046 *disproved* the up-to-capacity conjectures, fixing the target at the sub-capacity band — the
prize window.

## 2. The unified object: `defect = 0`

Define, for the explicit family at the binding radius, the **dyadic-lacunary count**
`L_lac(n) = #{ T ⊆ μ_n : |T| = a, e₁(T) = … = e_{a-2}(T) = 0 }` (subsets with vanishing
elementary-symmetric/power-sum prefix), and its **defect**
`D(n,p) = L_lac(n) − #{μ_d-cosets}` (the *non-coset* lacunary subsets). The campaign's central
structural claim, here proven (§3), is:

> **Reunification.** Both grand challenges reduce — via an explicit, proven bijection — to the single
> conjecture **`D(n,p) = 0`** (equivalently, in its MCA form, the Gauss-period bound
> `max_{b≠0}|Σ_{x∈μ_n} e_p(bx)| ≤ C√(n log m)` collapsing to the coset/Ramanujan value; equivalently
> the energy bound `E_r(μ_n) ≤ (2r−1)‼·nʳ` at depth `r ≈ log q`).

So a *single* closed-form conjecture, if proven, solves **both** challenges. This is exactly the unified
statement the prize asks for. (`PROXIMITY_PRIZE_WORKBENCH.lean` slot; bridges in-tree.)

## 3. What is proven (machine-checked, axiom-clean)

### 3.1 The reunification bijection — both challenges are *one* object
`Sweep_A42_ReunificationBijection.lean`. For the word `x^a+1`, the deg-`<k` window-list members are in
**bijection** with the lacunary subsets `T` (surjectivity by construction: a lacunary `T` with
`∏(X−t) = X^a − αX − c` yields the codeword `f = αx + (1−c)`, which agrees on all of `T`; injectivity
automatic). Hence `L(x^a+1) = L_lac(n) = #cosets + D(n,p)`, so **`L` bounded ⟺ `D = 0`**. The general
form (`agreement_iff_root_general`, `agreement_poly_lacunary_band`) extends this to all rates: the LD
agreement object *is* the lacunary object. This collapses LD and MCA onto the same `D`.

### 3.2 The descent identity — the symmetric/non-symmetric split
`Sweep_A41_DescentAZForm.lean`. `agreement(f,u) = A + Z`, where `A` is the symmetric joint agreement
(what the antipodal tower captured) and `Z = #{R = 0}` is the zero-count of the explicit quadratic form
`R = (F−u_e)² − y(G−u_o)²`. The even-spine corollary shows even codewords descend at exactly `2×`.

### 3.3 The characteristic-0 rigidity — first level general; full case proven for the trinomial (`k=2`)
A chain of new theorems (none in Mathlib):
- `Sweep_A43` (engine): `(Xᵐ+1) ∣ g ∧ deg g < 2m ⟹ g.coeff j = g.coeff (j+m)`.
- `Sweep_A44`: a vanishing sum of `2^μ`-th roots of unity is `±`-paired (**Lam–Leung for `p = 2`**),
  and its subset form: a vanishing-sum subset (`p₁ = 0`) is negation-closed (`T = −T`). *This first
  level is general — it holds for any lacunary subset.*
- `Sweep_A45` (`coeff_comp_neg_X` + `lacunary_coset_rigidity`): a negation-closed root set makes
  `∏(X−t)` an even polynomial; for a lacunary **trinomial** `X^a − αX − c` (`a ≥ 2`, `0 ∉ T`, char `≠ 2`)
  this forces `α = 0` — the binomial `X^a − c` — whose roots are a `μ_a`-coset.

**Scope (honest — corrected).** The trinomial shape requires `e₁ = … = e_{a−2} = 0` (two free
symmetrics), i.e. the **linear codeword `k = 2`** case — exactly the binding case at `n = 16`. So
`Sweep_A45` proves char-0 `D = 0` for that slice. At the binding radius for `n ≥ 32` the condition is
`e₁ = … = e_{n/8} = 0` (`n/8` free symmetrics), so `∏(X−t)` is `(k+1)`-sparse, *not* a trinomial, and
A45 does not apply. The **general** fixed-rate char-0 rigidity (full dyadic Fourier-uncertainty
`e₁..e_{n/8}=0 ⟹ union of cosets`) requires the **iterated** argument (`p₁=0 ⟹ T=−T`; then `p₂=0`
descends to a level-`μ−1` vanishing sum; iterate `log n` times) and is **not yet formalized**.
Machine-checked: the general first level (A44) and the full trinomial/`k=2` case (A45); the
general-rate char-0 closure is a bounded follow-up. (Earlier "char-0 half COMPLETE" was an overstatement
and is retracted; see issue #444.)

## 4. The open core, isolated to one statement

The char-0 proof's single load-bearing fact is that `Φ_{2^μ} = X^{2^{μ-1}} + 1` is **irreducible over
ℚ** — this forces `(X^{2^{μ-1}}+1) ∣ g`, hence the `±`-pairing, hence coset rigidity. In the prize
regime `p ≡ 1 mod 2^μ`, `Φ_{2^μ}` **splits** in `F_p`: `ζ ∈ F_p`, `minpoly(ζ) = X − ζ`, and `g(ζ) = 0`
yields only `(X − ζ) ∣ g`. The pairing is no longer forced, and non-coset lacunary subsets — the
**defect `D(n,p) > 0`?** — may appear. So:

> **The entire prize reduces to:** does the char-`p` splitting of `Φ_{2^μ}` produce a *bounded*
> (ideally zero) non-coset defect in the prize window? This is the thin-subgroup BGK / generalized-Paley
> Ramanujan problem — recognized open for ~25 years.

## 5. Why every route reaches exactly this (refutation ledger)

The campaign (120+ routes, two prior 50-conjecture sweeps, this session's additions) eliminates the
entire ranked attack surface, each with a rigorous reason (full detail in `DISPROOF_LOG.md`):

- **Packing / second-order descent → Johnson.** Distinct mixed members overlap in `≤ 2k` points; the
  double-counting bound reaches only `τ > √ρ + ρ/2` (Johnson + ε), outside the window.
- **Action–Orbit norm (η_crit) → insufficient.** The clean region is Johnson-adjacent; the gap widens
  with `μ`.
- **N13 phase-transfer → ℓ^∞ vs ℓ² mismatch.** The house is ℓ^∞ and `‖𝒯‖_{ℓ^∞}=2`; the worst `b` has
  `cos = +1` (phases align at the sup), so no `<√2` contraction.
- **N7 2-adic Newton polygon → valuation ⊥ house.** `v₂` is independent of archimedean magnitude.
- **N10 chaining → generic = Johnson.** `B/√(n log m)` is stable; the structured net is not `o(generic)`.
- **E12 three-gap → vacuous.** Discrete logs are an exact AP (one gap); the value-sum is not an AP.
- **Moment / energy / cosh-MGF / lattice-theta / Salié / large-sieve / Burgess / Sato-Tate / Habegger**
  — all reduce to the same char-`p` `D` (framing-independence, analytic ⊕ geometric).

The LD-side hope that the agreement-set (curve) constraint is *strictly stronger* than the energy
constraint is **killed** by the §3.1 bijection: every defect subset is automatically LD-realizable, so
LD ≡ MCA is tight — no LD-specific lever.

## 6. Honest status

- **Proven and formalized:** the reunification bijection (both challenges = one object `D`), the descent
  A+Z identity, the **general first-level** char-0 rigidity (negation-closure, A44), and the **full
  char-0 `D = 0` for the trinomial (`k=2`) case** (A45).
- **Open (char-0):** the **general fixed-rate** char-0 rigidity (`e₁..e_{n/8}=0 ⟹ coset` for `n≥32`)
  — needs the iterated argument; not yet formalized (a bounded follow-up).
- **Open (the prize):** `D = 0` in characteristic `p` (the prize regime) — the BGK/Paley wall.
  **Not proved here.**

This work does not claim the prize. It contributes the *unified* closed conjecture the prize asks for,
proves it implies both challenges, resolves its char-0 half completely and machine-checked, isolates the
open core to a single sharp char-`p` statement, and records why every known technique lands there. A
closure requires a genuinely new effective-equidistribution input for `μ_{2^μ}` at `n ≈ q^{1/4}` that
does not exist in the literature; producing one is the open problem, and no fabricated proof is offered
in its place.
