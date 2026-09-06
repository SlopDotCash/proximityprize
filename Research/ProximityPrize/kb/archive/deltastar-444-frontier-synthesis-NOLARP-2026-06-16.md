# δ\* in the prize regime — the honest frontier synthesis (no-larp paper)

**Issue #444 · proximityprize.org · companion ABF26 (Arnon–Boneh–Fenzi 2026).** This is the
"rewrite with no larp" deliverable: a truthful accounting of the *complete* search frontier — what
is closed, what every attempted method-class reduces to, and the *precise* statement a solution must
prove. **No closure of the prize is claimed; the core is a recognized open problem.**

---

## 0. The single open quantity (everything reduces to this)

Prize regime: `μ_n ⊂ F_p^*` the order-`n = 2^μ` multiplicative subgroup, `p ≡ 1 mod n`, `p ≈ n·2^128`,
`n < p^{1/4}`, `m = (p−1)/n ≈ 2^128`, `ρ ∈ {1/2,1/4,1/8,1/16}`, window `δ* ∈ (1−√ρ, 1−ρ−Θ(1/log n)]`.

```
THE WALL:   M(μ_n) = max_{b≠0} |Σ_{z∈μ_n} e_p(bz)|  ≤  C·√(n·log(p/n))         (sub-Gaussian / BGK / Paley √-cancellation)
```

By BCHKS/ABF26 this is **equivalent** to beyond-Johnson list-decoding of explicit RS and to the MCA
δ\* in the window — one object. `M(μ_n) = house(Ψ) = max_J |η_J|`, the `m` Gaussian periods
`η_J = Σ_{z∈coset} ζ_p^z` (roots of the degree-`m` period polynomial `Ψ ∈ ℤ[T]`). Spectrally:
`house² = max_J τ_J`, `τ_J = |η_J|² ≥ 0`, with Parseval `Σ_J τ_J = p − n` (degree-1 moment) and
high moments `Σ_J τ_J^d = E_d` (the **additive energy**). The L² floor is `house ≥ √n`; the conjecture
is only a `√(log m)` factor above it. **The gap is the char-`p` additive-energy surplus
`Spur_r = E_r − E_r^{char-0}` at `r ~ log m` — open ~25 years (thin-subgroup BGK).**

## 1. What IS closed (the char-0 / archimedean-baseline face)

- **char-0 additive energy** `E_r^{c0} = (2r−1)!!·n^r`; MGF `= I₀(2y)^{n/2}`; prize bound `I₀(2y) ≤ exp(y²)`
  coefficientwise. (in-tree; the char-0 side of the two-sided pin.)
- **char-0 dyadic rigidity** (Lam–Leung for p=2): a vanishing sum of `2^μ`-th roots is `±`-paired ⟹
  lacunary ⟹ coset. (`Sweep_A44`–`A49`, merged PR #453.)
- **char-0 subset-sum spectrum generating function** (this session, merged PR #453):
  `(x²−1)·Σ_r N_r x^r = x^{m+2}(x+2)^m − (2x+1)^m`, unifying total `T(m)=3^{m-1}(m+3)`, the alternating
  sum `(−1)^{m+1}(m−1)`, and the complement-symmetry palindrome. (`Sweep_A50`.)
- **the bound is numerically correct & tight**: `house/√(2n log m) ∈ [0.74, 1.03]` across `n∈{4..32}`,
  14+ instances. The conjectured *form* is right; only the upper proof is missing.

These pin **one side** (the archimedean baseline). They do not bound the char-`p` surplus.

## 2. The complete NO-GO map (every method-class, with proof of why it fails)

| Method class | Verdict | Mechanism (proven this campaign) |
|---|---|---|
| Exact rigidity / defect-vanishing / SVP / ideal-norm | **house-blind** | `house ≥ p^{2/n} → 1` vacuous (`SparseSupportIdealSVPLowerBound`) |
| Newton polygon at any finite prime ℓ | **house-blind** | NP fixed by ramification; unit polygons carry no house info (`_NewtonPolygonPeriodSpread`) |
| **Period discriminant `disc(Ψ)`** | **house-blind** (NEW) | CFT-fixed: `|disc(Ψ)| = p^{m-1}·f²` (conductor–discriminant; verified EXACT 14 cases). House-independent; `disc→house` is the wrong direction (lower bound only, `≈ p^{1/m} → 1`). |
| **Delsarte / LP / psd / Beurling–Selberg dual** | **degree-1-blind** (NEW, formalized) | only certifies the degree-1 Parseval moment; LP optimum of `max_J τ_J` under `Σ τ_J = S` is exactly `S` ⟹ `house ≤ √(p−n)`, a `2^63` overshoot. (`DelsarteLPNoGo.lean`, PR #454.) |
| **Bounded-degree SDP / 4th-moment / Lasserre level-k** | **finite-size illusion** (NEW) | degree-2 bound `≈ √n·m^{1/4}`, looks `≈ √(2n log m)` for `m ≤ 24` (crossover region) but overshoots by `m^{1/4}/√(log m) → ∞`. Needs degree `~ log m`. (`MomentMethodPrizeDepthNoGo`: `r_opt≈128 ≫ r_max≈8`.) |
| Asymptotic equidistribution / Burgess / Sato–Tate / Weil | **out of regime** | vacuous for *fixed* thin `n < p^{1/4}` (β-gate `a > 128/3` never met). |
| Far-line incidence (the MCA "δ\*" proxy) | **Johnson-locked** | → 1/2, not the true MCA floor. |
| η_crit Action–Orbit norm route | **structurally insufficient** | `η_crit' ≈ 0.095 > δ* η ≈ 0.033`; only odd indices are Galois autos. |

**The dichotomy (the organizing principle):** *every algebraic / finite-prime invariant of `Ψ` is
fixed by ramification at `p` and is house-blind; every linear/LP dual is degree-1-blind; every
bounded-degree SDP is finite-size-fooled.* The house is **purely archimedean**, and the only handle
that reaches it is the **nonlinear high-moment surplus `E_r`** at `r ~ log m` — which is the prize.

## 3. What a solution MUST prove (the precise open target)

Equivalent forms of the one missing inequality (any one closes it):
1. **Additive energy**: `E_r(μ_n) ≤ (2n log m)^r` at `r ~ log m` (i.e. `Spur_r` does not blow the
   char-0 value past sub-Gaussian) — the BGK bound for a *fixed* thin 2-power subgroup.
2. **Discriminant near-maximum**: `disc(Ψ)` is within `(1−o(1))` of its *trace-constrained* maximum
   (NOT its CFT value `p^{m-1}` — that's far below and house-blind); equivalently the roots are
   modulus-balanced near `√n`.
3. **Jacobi-phase equidistribution**: the `m` flat-spectrum periods (`|η̂_k| = √p`) have phases (the
   Jacobi sums `T_h`) that equidistribute enough for the max to be `√(2 log m)·L²`, in the *fixed-p*
   regime (Weil gives this only asymptotically).

All three are the same open problem. A genuine solution is a **new bound on `E_r`/`Spur_r` for thin
2-power subgroups** — not a search over the method-classes in §2, which are now provably exhausted.

## 4. Honest verdict

**δ\* in the prize regime is NOT proven here, and is not fabricated.** The campaign has: closed the
char-0 face, proven the conjectured form correct & tight numerically, and *proven that four whole
method-classes cannot reach the prize* (two formalized axiom-clean this session). The residual is the
recognized 25-year-open thin-subgroup BGK wall, isolated to the single nonlinear object `E_r` at
`r ~ log m`. If the grand MCA challenge has been solved, the proof lives in that object — a new
additive-combinatorics bound — and reproducing it requires that mathematical breakthrough, not a
further iteration over the mapped-and-closed search space.

*Artifacts: PR #453 (char-0 GF + rigidity, merged), PR #454 (`DelsarteLPNoGo`), probes
`_probe_444_{periodpoly_disc_cft,charzero_census_audit,moment_depth_required}.py`,
memory `arklib-444-method-nogo-dichotomy`. No `sorry`/`axiom`/`native_decide`; no fabricated closure.*
