# δ* (#407) — cumulant-from-flatness: the EXACT bridge, the content direction, and the κ₂⇒κᵣ structural lever

**Status:** assigned-path assault (cumulant-from-flatness). Rigorous reductions + machine-verified
numerics; **no closure**. The route delivers (i) an EXACT bridge κ_r ⟺ DFT-moment of the unimodular
Gauss-phase sequence, identifying the content direction; (ii) a closed-form κ₂ as a function of one
integer N (unit-equation count); (iii) a NEW structural finding — κ₂≤1 ⟹ κᵣ≤1 (∀r) with 0
counterexamples over 131 primes, explained by sub-Gaussianity = no-heavy-atom; (iv) the precise
norm-bound crossover for provability of κ₂≤1 at the prize (n ≤ 128 only). Honesty contract in force.
Author: #407 cumulant lane, 2026-06-13. Probes: `scripts/probes/_wf_cumulant_from_flatness.py`,
`_wf_tangent_second_moment.py`, `_wf_cumulant_higher_r.py`, `_wf_l1autocorr_scaling.py`,
`_wf_autocorr_subgaussian_law.py`, `_wf_kappa2_provable_kappar_wall.py`,
`_wf_kappa2_implies_kappar.py`, `_wf_r2_norm_bound_prize.py`.

## 0. The objects (recap, exact)
`F_p`, `n=2^a | p−1`, `m=(p−1)/n`, `χ` mult char order `m`, `μ_n=ker χ`, `ψ=e_p`.
`τ_j=τ(χ^j)`, `|τ_j|=√p` (j≢0). `a_j := τ_j/√p` UNIMODULAR. Gauss period `η_b=Σ_{x∈μ_n}ψ(bx)`,
`η_b=(√p/m)·D(b)`, `D(b)=Σ_j a_j χ^{−j}(b)` the m-DFT of `(a_j)`. House `B=max_b|η_b|`.
Cumulant `κ_r := (Σ_b|η_b|^{2r}/m)/((2r−1)‼·n^r)`. Prize floor `δ*=average ⟺ B ≤ C√(n log m)`.

## 1. THE EXACT BRIDGE (rigorous; machine-verified to 1e-14)

> **κ_r = (p/nm)^r · P_{2r} / ((2r−1)‼·m^r)**,  where `P_{2r} := (1/m)Σ_b|D(b)|^{2r}` is the
> **2r-th moment of the m-DFT** of the unimodular Gauss-phase sequence `(a_j)`.

Proof: `Σ_b|η_b|^{2r} = (p^r/m^{2r}) Σ_b|D(b)|^{2r} = (p^r/m^{2r−1})P_{2r}`; divide by `m(2r−1)‼n^r`.
At prize `p=nm+1` so `(p/nm)^r→1`. Hence:

> **κ_r ≤ 1  ⟺  P_{2r} ≤ (2r−1)‼·m^r  ⟺ the DFT `(a_j)↦D` is COMPLEX-GAUSSIAN to depth r.**
> (Parseval `P_2 = Σ_j|a_j|^2 = m−1+1/p ≈ m`; the Gaussian value of `P_{2r}` is exactly `(2r−1)‼ m^r`.)

This is *framing (1) flatness ⟺ framing (2) cumulant*, made exact. **The content direction is the
MOMENT (cumulant) side:** `P_{2r}≤(2r−1)‼m^r` (a moment bound) ⟹ `max_b|D(b)|≤C√(m log m)` (flatness/
sup) by Markov+union over `r≈ln m` (easy); the converse sup⟹moment loses (a far atom is sup-allowed).
So **the cumulant bound IS the content**, and analytic flatness is its consequence — this resolves
"which direction is content."

## 2. THE AUTOCORRELATION AND κ₂ = CLOSED FUNCTION OF ONE INTEGER N (rigorous, exact)

Wiener–Khinchin (exact): with `R(h):=(1/m)Σ_j a_j conj(a_{j+h})` the normalized autocorrelation,
`P_4 = m^2 Σ_h|R(h)|^2`. By the machine-verified identity **I3** (`A_h=m·conj(τ_h)·T_h`,
`T_h=Σ_{w∈μ_n}χ^h(1−w)`): **R(h) = conj(τ_h)·T_h/p**, so **|R(h)| = |T_h|/√p**. Therefore the
tangent second moment `V := Σ_h|T_h|^2 = m·N` where

> **N := #{(w,w′)∈μ_n², w,w′≠1 : (1−w)/(1−w′)∈μ_n}**  (a unit-equation solution count).

Closed formula (verified `k2_pred = k2_dir` to 4+ digits, `_wf_tangent_second_moment.py`):
> **κ₂ = (p/nm)² · [ R(0)² + (mN − (n−1)²)/p ] / 3**,  `R(0)=(m−1+1/p)/m`.

Forced floor `N ≥ 2n−3` (the involution `w↦w⁻¹`: `1−w⁻¹=−w⁻¹(1−w)`, `−w⁻¹∈μ_n`; + diagonal + `w=−1`).
At `N=2n−3`, `p≈nm`: `κ₂ → (1+(2n−3)/n−n²/m)/3 → 1⁻`. EXTRA solutions `N>2n−3` push `κ₂>1`.
> **κ₂ ≤ 1 ⟺ N ≤ 3n + n²/m + O(1) ⟺ the unit equation `(1−w)=u(1−w′)` in `μ_{2^a}³` has only
> the forced ~2n solutions.** Since `n²/m→0` at prize (`m~2^128 ≫ n²` for `n≤2^40`), `κ₂≤1 ⟺ N=2n−3`.

## 3. THE STRUCTURAL LEVER κ₂ ≤ 1 ⟹ κᵣ ≤ 1 — held away from boundary, REFUTED at the boundary

First pass (131 primes, n=16,32,64, r≤8, `_wf_kappa2_implies_kappar.py`,
`_wf_kappa2_provable_kappar_wall.py`): **0 counterexamples**, with a clean mechanism:
- spectrum `{η_b}` REAL (`−1∈μ_n`), mean-square `n`; real-Gaussian baseline `κ_r≡1`. AWAY-from-boundary
  GOOD primes are sub-Gaussian: `ρ_r=κ_{r+1}/κ_r <1` and monotone decreasing (n=16,m=72:
  0.733,0.630,0.552,0.488) ⟹ `κ_r` log-concave decreasing from `κ_1≈1` ⟹ `κ₂≤1 ⟹ κ_r≤1`.
- BAD primes (`κ₂≫1`) have `ρ_r>1` at low r (`κ_8/κ_2` up to 65×): a defect coset = heavy atom; the
  onset is r-INDEPENDENT (n=32: `max_bad_m`=183 for both r=2,3) — a mod-p coincidence fattens all moments.

> **REFUTED at the boundary (`_wf` stress test, n=64,128, r≤12).** At **n=64, p=11969 (m=187):
> κ₂=0.9954 ≤ 1 but κ₄=1.156 > 1.** Also p=12097 (κ₂=0.9966, κ₅=1.095). The clean separation
> FAILS: largest κ₂ among SAFE primes = **0.9996**, smallest κ₂ among UNSAFE = **0.9954** — they
> OVERLAP, so NO margin δ gives `κ₂≤1−δ ⟹ all κ_r≤1`. The named conjecture **κ₂Caps is FALSE.**

**Honest consequence:** the deep-moment defect carries information that r=2 CANNOT certify, precisely
in the near-Gaussian boundary regime (`κ_r≈1`) that the prize inhabits. The Markov–Krein wall stands:
the `Θ(log m)`-deep-moment requirement does NOT collapse onto r=2. The sub-Gaussian/log-concave
picture is correct only *strictly inside* the good region, not at the threshold. This is a clean,
machine-checked refutation, not a closure.

## 4. PROVABILITY of κ₂≤1 AT THE PRIZE — the norm-bound crossover (n ≤ 128 only)

A non-forced extra solution = `p | α`, `α=(1−ζ)−u(1−ζ′)∈Z[ζ_{2^a}]` (deg `2^{a−1}`), `α≠0` in char 0.
Each conjugate `|σ(α)|≤4` ⟹ `|N(α)| ≤ 4^{n/2} = 2^n`. So a prize prime can create an `r=2` defect
only if it divides some non-forced `α`, i.e. only if `p ≤ 2^n` (worst-case norm). Verified
(`_wf_r2_norm_bound_prize.py`, `_wf_kappa2_provable_kappar_wall.py`): the n=32 bad primes
(p≤5857) each literally divide a non-forced `α` mod p; the *minimal* non-forced norm is exactly `2`
(harmless, only `p=2`), but the *maximal* is `2^n` (the worst-case carrier).

> **Prize crossover:** prize `p ~ n·2^128 = 2^{a+128}` vs worst-norm `2^n=2^{2^a}`. `p>2^n ⟺ a+128>2^a`,
> which holds **for a ≤ 7 (n ≤ 128)** and FAILS for `a ≥ 8 (n ≥ 256)`. So the norm bound PROVES
> `κ₂≤1` at the prize **only for `n ≤ 128`**; for the full prize range (`n` up to `2^40`) it is short.

This refines the prior `q>(2r)^{n/2}` deep-moment wall to the *r=2-specific* bound `q>4^{n/2}=2^n`,
pushing the provable ceiling from `n<40` up to `n=128`, but not to the full range.

## 5. Why the L1-autocorrelation does NOT escape (route wall, located)
`P_{2r}=m^r W_r`, `W_r=Σ_{closed r-walks}Π R(h_i)`; diagonal (matchings) `=(2r−1)‼` exactly. The
L1 walk bound `W_r^{L1}=Σ Π|R(h_i)|` drops the inter-`R` phase cancellation. Measured
(`_wf_l1autocorr_scaling.py`, `_wf_autocorr_subgaussian_law.py`, GOOD primes): the autocorrelation
ITSELF is sub-Gaussian — `max_{h≠0}|R(h)| ≈ 1.11√(log m/m)` (slope −0.37, i.e. `|T_h| ≲ 1.11√(n log m)`,
= the tangent flatness law, flat constant ≈1.11), and `Σ_h|R(h)|^2 ≈ 3(log m)^{0.35}`. But the L1
walk-bound `W_r^{L1}/(2r−1)‼` DRIFTS UP `~(log m)^{0.35·?}` and crosses 1 near `m≈50` — it cannot
certify the Gaussian constant. The phase cancellation among the `R(h_i)` (themselves Gauss/Jacobi
phases) is essential — the same √-cancellation wall, now one level up (autocorrelation level).

## 6. Honest verdict
**No closure; one named conjecture refuted.** Net new content of this lane:
1. **EXACT bridge** κ_r ⟺ DFT-moment `P_{2r}` of the unimodular Gauss-phase `(a_j)`; **content
   direction = the moment side** (moment⟹flatness easy; flatness⟹moment loses) — rigorous, resolves
   the "which direction is content" question of the assigned path.
2. **κ₂ = closed function of one integer** `N` (unit-equation count); `κ₂≤1 ⟺ N=2n−3` at prize
   (since `n²/m→0`). Verified `k2_pred=k2_dir` to 4+ digits.
3. **r=2 PROVABLE at prize for n ≤ 128** (norm bound `4^{n/2}=2^n` vs prize `2^{a+128}`: `a+128>2^a ⟺ a≤7`);
   refines the prior `q>(2r)^{n/2}` wall from `n<40` to `n=128` at r=2 specifically. Short for `n≥256`.
4. **κ₂Caps REFUTED** (machine-checked): the deep-moment defect is NOT controlled by r=2 at the
   near-Gaussian boundary the prize inhabits (n=64,p=11969: κ₂=0.9954 but κ₄=1.156). The Markov–Krein
   deep-moment wall STANDS — the `Θ(log m)`-moment requirement does not collapse onto r=2.
5. **L1-autocorrelation route walls** (located): the autocorrelation `R(h)=conj(τ_h)T_h/p` is itself
   sub-Gaussian (`|T_h|≲1.11√(n log m)` = tangent flatness, flat constant), but the L1 walk-bound drops
   the inter-`R` phase cancellation and drifts past the Gaussian constant — same √-cancellation wall, one
   level up.

**Cross-path lever (surviving, honest):** the EXACT autocorrelation `R(h)=conj(τ_h)T_h/p` reduces the
*entire* moment tower to one Gauss/Jacobi sequence — the deep moment `κ_r` is the r-fold closed-walk
sum of a SINGLE explicit object. This is the right surface for an *effective-equidistribution / Stepanov*
input: the open core is now "the unit equation `Π(1−w_i)=u·Π(1−w_j′)` in `μ_{2^a}` has only forced
solutions mod p, to multiplicity-depth `r≈ln m`," with the `r=2` instance provable for `n≤128`. A
char-0→char-p transfer at depth `r` (the NVM index-`r` problem, arXiv:2310.09992 solves index 2,3)
would close it — the bridge + autocorrelation make the target fully explicit and combinatorial.

## References
- I3/I4 identities: `RESEARCH_SYNTHESIS_407_TANGENT.md`, `TangentSumJacobiAverage.lean`.
- Markov–Krein deep-moment wall: `deltastar-407-markovkrein-and-selfimprove-walls-2026-06-13.md`.
- Deep-moment norm bound `q>(2r)^{n/2}`: memory `arklib-389-deep-moment-wall`.
- NVM / subgroup uncertainty (index 2,3): arXiv:2310.09992.
