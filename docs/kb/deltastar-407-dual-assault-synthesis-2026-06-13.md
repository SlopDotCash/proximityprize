# #407 dual assault — consolidated synthesis (M(n) face + direct floor face), 11 expert angles (2026-06-13)

> **Scope correction (2026-10-28 audit, T48; cross T87/T104).**
> - **Sum-product row.** "μ_n is JOINTLY Sidon with every dilate (`E^+(μ_n, ξμ_n) = n²`)" is false
>   as a universal statement. Taking `ξ = 1`, or any `ξ ∈ μ_n`, gives the ordinary energy, which is
>   already `3n² − 3n` in characteristic zero for an even dyadic subgroup. In thin prime fields it
>   can be larger still (for example `μ₃₂ ⊆ F₃₂₉₉₃` has `3744`).
> - **Stepanov row.** The heavy-set counts are finite statistics. They do not prove a uniform
>   Gaussian tail.
> - **Amplification row.** The maximum-at-zero identity `max_h |D_r(h)| = D_r(0)` holds for that one
>   positive-definite correlation. It does not eliminate every signed or weighted amplification.
> - **Bottom line.** "None exists in current mathematics" is not established. The angles refute the
>   specific tested routes.
>
> The explicit retraction of the unrealizable, freely chosen Gauss-phase spike (Hasse–Davenport
> row) is correct and is kept.

Two adversarial multi-agent assaults (M(n) character-sum sup-norm; direct floor I(δ)≤q·ε*), 11 completed
expert angles, taken over and synthesized manually after a rate-limit interruption. **Verdict: no proof
(expected — recognized open core), but a COMPLETE, sharp, often-decisive map; every angle resolved with a
formalizable brick; several genuinely NEW results.** All faces provably converge to BGK square-root
cancellation M(n)=max_{b≠0}|Σ_{x∈μ_n}e_q(bx)| ≤ C√(n log q), n≪√q.

## M(n) face — 8 angles (all hit BGK, sharp bricks)
| angle | result |
|---|---|
| **Large sieve / effective Deligne** | **NEW SHARP OBSTRUCTION:** Σ_b|η_b|^{2r}=q·E_r EXACTLY (sieve in b saturated, 0 slack); effective Deligne discrepancy ~ f^r/(r!√q), effective ONLY if f≤√q ⟺ n≳√p. **Prize n≪√p is OVER-DIMENSIONED by √p/n** — the geometric route is dimension-obstructed by construction. |
| **Explicit conductor of M^{*r}** | **NEW — corrects the scaffold:** conductor = dim H¹_c = 2·#{order-n char 2r-tuples, trivial product} ≈ 2(n−1)^{2r−1} ~ n^{2r−1}, **Swan=0 (all tame, NOT factorial-wild)**. So `K=O(1)` is FALSE; Weil-II over the n^{2r−1}-dim H¹_c is lossy by √rank = n^{r−1/2} = exactly the n^{1/2}-per-step L² deficit. |
| **Stepanov auxiliary poly** | **DECISIVE refutation:** K(T)=#{b≠0:|η_b|>c√n}=Θ(p) uniformly (η_b/√n→N(0,1) Gaussian tail, NO β-dep). Auxiliary on heavy set has deg≥K=Θ(p) ⟹ Stepanov multiplicity m<p/K=O(1) ⟹ collapses to m=1 moment. + Frobenius degree cap <p (in-tree). |
| **Amplification / shifted moments** | **Clean refutation:** D_r(h)=Σ_b η_b^r η̄_{b+h}^r = p·Σ_t N_r(t)²e_q(−ht), N_r≥0 ⟹ max_h|D_r(h)|=D_r(0)=p·E_r. ALL amplifiers (self/shift/mixed/twist) collapse to the flat energy; positive-definiteness is the airtight brick. |
| **2-adic tower / Lam–Leung** | **Refutation:** descent M(n)²≤2max_b(|A|²+|B|²)=M(n)²+M_χ(n)², M_χ = quadratic-TWISTED level-n sup-norm, SAME size — self-referential, never descends. cos=1 is trivial realness. Per-level law M(n)²≤(2+Θ(1/log n))M(n/2)². |
| **Hasse–Davenport phases** | HD imposes Θ(f) constraints but leaves f/4 free phase DOF; HD is NECESSARY but INSUFFICIENT — reduces to effective fixed-q equidistribution of the HD-free seed phases (Katz/Rojas-León). **CORRECTION:** the agent's 'coherent-spike recoheres S_b to f−1' insufficiency argument was ADVERSARIALLY REFUTED (2/2) as a domain conflation — it varies the Gauss-sum phases θ_s=arg(g(χ_s)), which are FIXED algebraic numbers (the prize max is over the discrete coset index b ONLY). HD-insufficiency stands via the reduction, NOT the spike. |
| **Bessel moment transfer** | **LANDED axiom-clean bricks** (`Frontier/BesselDeviationLower.lean`, 3 thms, [propext,Classical.choice,Quot.sound]): per-coordinate deviation engine `1−1/k! ≤ C(k,2)` + `bessel_term_ge_gaussian_sub` ⟹ char-0 baseline Gaussian to O(C(r,2)/n) (≤7.6e-6 at n=2^30,r≤128). ALL difficulty isolated in char-p wrap-around excess (overwhelms at r*~½log p). |
| **Sum-product / BSG (2-power)** | μ_n is JOINTLY Sidon with every dilate (E^+(μ_n,ξμ_n)=n² diagonal-only) — the BEST possible additive input — yet BGK/BSG gives ZERO exponent gain (losses regime-driven, seed-energy-independent). |

## Direct floor face — 3 angles (floor = extreme-value, reduces to M(n))
| angle | result |
|---|---|
| **MDS average + concentration** | **NEW — DECISIVE reframing:** closed-form average `E_line[I] ≈ C(n,k+m)·q^{1−m} = q^{−Θ(n/log n)}` at the window interior — ASTRONOMICALLY below n (≈2^{−1e7} at μ=30). The "average≈n" expectation is FALSE in the window interior (only near capacity, η≈0.005). So **the floor is a LARGE-DEVIATION / EXTREME-VALUE statement, NOT concentration** — worst/avg gap = q^{Θ(n/log n)}, unbridgeable by any Chernoff/union bound over n² lines. |
| **Window-interior #distinct-e_m** | **PARITY/VACUITY LAW:** in char 0 (q≫n), m≥2 ⟹ every valid T is antipodal, |T| even, odd t ⟹ I=0; the char-0 window fiber is EMPTY. Floor failure localized ENTIRELY to char-p antipodal-violators; counting via orthogonality re-derives η_b EXACTLY ⟹ = M(n). |
| **B4 interleaved LD⇒MCA** | CIRCULAR: every interleaved bound is a monotone amplification (b+r choose r)·Λ(C)^r (GGR11, r=4–5) of the single-code list; lower bound Λ(C)≤Λ(C^{≡m}) exact. Forcing ≤n needs Λ(C)≤O(1) = the prize. |

## Genuinely NEW results (beyond "it's BGK")
1. **Dimension obstruction** (large sieve): the effective-Deligne/Katz route needs f≤√q ⟺ n≳√p; the prize n≪√p is over-dimensioned — a SHARP reason the geometric route cannot be made effective in-regime. **Corrects/sharpens the MonodromyConductorScaffold open input (II).**
2. **Conductor is rank-driven n^{2r−1}, Swan=0** — `K=O(1)` (scaffold input II) is geometrically FALSE; the cancellation is in the WEIGHTS, not the conductor size. **Scaffold to be corrected.**
3. **Floor = extreme-value not concentration** (MDS average q^{−Θ(n/log n)}) — kills the Poisson-concentration hope at the WINDOW INTERIOR specifically (it only worked near capacity).
4. **Parity/vacuity law** — char-0 floor fiber empty; the entire floor difficulty is the char-p antipodal-violator count = M(n).
5. **Bessel char-0 deviation engine** — axiom-clean landed (the char-0 baseline is provably Gaussian to O(C(r,2)/n)).

## Refutations to log (DISPROOF_LOG)
Stepanov (heavy-set Θ(p) ⟹ multiplicity O(1)); amplification/shifted moments (positive-definite ⟹ flat energy);
2-adic dyadic descent (self-referential M_χ same size); average+concentration at window interior (extreme-value gap);
B4 interleaved (circular amplification); K=O(1) conductor (rank-driven n^{2r−1}).

## Honest bottom line
The prize core survives every angle of a 11-expert adversarial assault — it is the BGK wall, confirmed from
M(n), conductor, Stepanov, amplification, dyadic, large-sieve, MDS-average, combinatorial, and interleaved
directions, each with a sharp formalizable brick. NO proof (none exists in current mathematics). Genuine
advances: the dimension obstruction, the rank-driven conductor (correcting K=O(1)), the floor-is-extreme-value
reframing, the parity/vacuity law, and the landed Bessel char-0 engine. No fabricated closure.
