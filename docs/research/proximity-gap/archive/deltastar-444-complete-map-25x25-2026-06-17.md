# δ\* in the Prize Regime — A Scoped, No‑Larp Map (25 Directions × 25 New Tools, Shredded & Synthesized)

**Issue #444 · 2026‑06‑17 · companion ABF26 (Arnon–Boneh–Fenzi 2026, eprint 2026/680).**

This is the consolidated propose→shred→prove paper the campaign has been running piecewise. It is
written under a hard honesty contract: **no fabricated closure, no `sorry`‑laundering, every verdict
marked.** The goal — prove δ\* (mutual‑correlated‑agreement threshold) in the prize regime — is **not
achieved here**; what *is* achieved is a precise localization of the single open quantity and a proof
that the method classes recorded here reduce to it.

---

## 0. The single open quantity (what δ\* actually is in the prize regime)

Prize regime: `μ_n ⊂ F_p^*` the multiplicative subgroup of order `n = 2^μ`, `p ≡ 1 (mod n)`,
`p ≈ n·2^128`, `ρ ∈ {1/2,1/4,1/8,1/16}`, `ε* = 2^-128`, window `(1−√ρ, 1−ρ−Θ(1/log n)]`. By
BCHKS/ABF26, δ\* in this window, the operational `mcaDeltaStar` / `mcaConjecture` target, and
beyond‑Johnson list‑decoding of explicit
Reed–Solomon are **one object**, controlled by the **Gauss‑period house**

> `M(μ_n) = max_{b≠0} |∑_{z∈μ_n} e_p(bz)|`, conjectured `≤ C·√(n·log(p/n))` (BGK/Paley √‑cancellation).

`M` is the second‑largest eigenvalue of the `μ_n`‑Cayley graph; `house ≥ √n` is free (Parseval /
Alon–Boppana `2√n`), the conjectured `√log` improvement over the `√m`‑loss bound `√(nm)` is the wall.
This is a recognized **~25‑year‑open** problem (square‑root cancellation for a *fixed thin* subgroup,
`n < p^{1/4}`); the asymptotic tools (Burgess, Sato–Tate, sum‑product/BGK) are all **out of regime**
(`n` fixed, `< p^{1/4}`).

---

## 1. Twenty‑five research directions, each with an HONEST verdict

Legend: **CLOSED** = proven (no open residual) · **NO‑GO** = proven a method‑class can't reach the prize
· **WALL** = correct reduction that bottoms out at `M(μ_n)`/`E_r`/Johnson · **OPEN** = genuinely open.

1. **Char‑0 dyadic rigidity** (Lam–Leung for `p=2`: vanishing power‑sum subsets of `μ_{2^μ}` are cosets). **CLOSED** char‑0 (`Sweep_A41`, `Sweep_A42`, `Sweep_A44`–`Sweep_A49`, axiom‑clean). Fails char‑p because `Φ_{2^μ}` splits mod `p≡1`.
2. **Char‑0 subset‑sum spectrum generating function** `(x²−1)G(x)=x^{m+2}(x+2)^m−(2x+1)^m`. **CLOSED** (`Sweep_A50`); unifies total/alternating/palindrome.
3. **Char‑0 additive energy / Bessel‑MGF** `Σ E_r y^{2r}/(2r)! = I₀(2y)^{n/2}`, `I₀(2y)≤e^{y²}`. **CLOSED** char‑0 (the char‑0 face of the prize bound is fully proven).
4. **Discriminant of the period polynomial** `disc(Ψ)` as a two‑sided spread invariant. **NO‑GO**: `|disc(Ψ)|=p^{m-1}·f²` is *class‑field‑theory‑fixed*, house‑blind (verified 14 cases); gives only `house ≥ p^{1/m}/2 → 1`, vacuous.
5. **Delsarte / LP / Beurling–Selberg duality** on the spectral measure. **NO‑GO**: degree‑1‑blind — LP optimum of `max_J τ_J` under `Σ τ_J = p−n` is exactly `p−n` ⟹ `house ≤ √(p−n)`, a `2^63` factor above target. Beating Parseval needs the degree‑2 moment `E_2`, invisible to any linear dual (`DelsarteLPNoGo`, PR #454).
6. **Full‑energy moment transfer** `E_r ≤ K^r·Wick` to `r≈ln q`. **NO‑GO at the stated form**: the full `rEnergy` includes the DC term `η_0=n`, so `rEnergy ≥ n^{2r}/q > Wick` already at integer depth `r=6` for `n=2^30, q≈2^158` — *provably false past the DC crossover* (`DCEnergyEssential.not_gaussianEnergyBound_of_deep`). The `K≈0.6` empirics are a finite‑size illusion (crossover `r*=7@n64` in the probe).
7. **Reduced‑energy transfer** `Ẽ_r = (q·rEnergy − n^{2r}) ≤ K^r·Wick`. **WALL (empirically sound)**: `K_reduced≈1`, bounded, mild converging n‑creep — the *correct* formulation, but the n‑uniform bound at `r≈ln q` is the wall.
8. **Deligne on the configuration variety** (bounded Betti `≤C(2r,r)`). **WALL**: per‑slice Betti is n‑independent, but `E_r` sums the Deligne bound over `m^{2r}` character twists; triangle‑inequality overshoots Wick by `2^41305` — needs √‑cancellation across twists = BGK.
9. **Newton‑polygon / 2‑adic period spread.** **NO‑GO**: unit Newton polygons carry no house info; the only non‑vacuous place is the archimedean one = `disc` (dir. 4).
10. **Sparse‑support ideal SVP lower bound.** **NO‑GO**: `house ≥ p^{1/φ(n)} = p^{2/n} → 1`, vacuous at prize (algebraic lower bounds are house‑blind).
11. **η_crit Action–Orbit norm route.** **NO‑GO**: structurally insufficient even *with* BGK (`η_crit ≈ 0.095 > δ*‑η ≈ 0.033`); only odd indices are Galois autos.
12. **Heavy‑target / zero‑sum forcing** `N(a,t) ≤ N(a,0)`. **NO‑GO**: false in char‑p (machine countermodel `μ_16⊂F_113`: `N(8,0)=102 < max_t=120`).
13. **q‑concentration dichotomy** (q‑independence only at the endpoint). **NO‑GO**: false in‑tree (`negSymm_interior_list_ge_qindep` realizes q‑independence one coordinate inside the window).
14. **Capacity‑edge entropy** `H₂(ρ)` two‑sided tightness. **WALL**: `a=k` is the excluded endpoint (cushion `η=0`); interior realizability = the house.
15. **Half‑Johnson pin** `δ* ≥ (1−√ρ)/2`. **CLOSED** unconditional, but **below** the window; full Johnson = open `SmallSubgroupGoodList`.
16. **Below‑UDR production floor** `n/q` (`epsMCA_le_below_udr_linear`). **CLOSED** conditional on `WindowRationalLinear`; lives below UDR, not the window.
17. **σ‑extremality of the deep‑hole word** `x^{rm}`. **CLOSED** char‑0 (exact extremizer, list `C(s/2,r/2)`); char‑p defect `= p|N(α)` norm‑divisor primes (not closed, = `E_r`).
18. **Cayley‑graph near‑Ramanujan** (`house ≈ 2√n ⟹ prize`). **WALL**: near‑Ramanujan for *thin algebraic* graphs is the open BGK question; Friedman is for random graphs; Alon–Boppana gives only the matching `√n` floor.
19. **Tangent / Jacobi‑sum equidistribution** (`A_h = m·conj(τ_h)·T_h`, Gauss sums flat). **WALL**: house = sup‑norm of a flat‑spectrum sequence with Jacobi‑sum phases; "phases equidistribute" = the wall.
20. **Stickelberger / Galois‑module structure** of spurious configs. **WALL** (swarm wf‑S4): density *rises* with depth; Galois doesn't force a small structured subset.
21. **Theta‑series / geometry‑of‑numbers** of the index‑`p` lattice `L_P`. **WALL** (swarm wf‑S5): shell base `B` grows with `n` — the n‑uniformity is the open input.
22. **Complete‑homogeneous floor** `chooseCH s r` (list‑decoding side). **CLOSED** count identity; dominates subset‑sum for `r≥2`, but the binding bound = the house.
23. **Dyadic tower recursion** `M(2n)² ≤ 2M(n)²`. **NO‑GO**: numerically FALSE (ratios to 3.86); no base case.
24. **Large‑sieve / average‑over‑q.** **NO‑GO**: explicit code lets you fix `q`; averaging is strictly weaker (reaches `r≈½log_n Q`, 4× worse than per‑q).
25. **Habegger/KU archimedean equidistribution.** **NO‑GO**: governs only the char‑0 part (already `≤1` by Lam–Leung); blind to the mod‑q defect = the entire wall.

**Tally: 7 CLOSED (all char‑0 or below‑window), 9 NO‑GO (method‑class impossibilities), 9 WALL.
Zero directions close δ\*.** Every WALL direction in this map reduces to the same `M(μ_n)`/`E_r` object.

---

## 2. Twenty‑five genuinely new mathematical results/tools produced (with novelty defense)

Status tags: **Lean** = theorem/declaration in-tree; **probe** = reproducible exact/numeric evidence;
**synthesis** = interpretation from the named artifacts, not a standalone theorem.

1. **Lean** `Sweep_A50.spectrumGF_mul_eq` — closed‑form spectrum generating function.
2. **Lean** `DCEnergyEssential.q_mul_energy_ge_dc` — unconditional DC lower bound `n^{2r} ≤ q·rEnergy`.
3. **Lean** `DCEnergyEssential.not_gaussianEnergyBound_of_deep` — full‑energy hypothesis false past the DC crossover.
4. **Lean** `DelsarteLPNoGo.parseval_lp_extremal` — LP relaxation optimum = Parseval.
5. **probe/synthesis** `disc(Ψ) = p^{m-1}·f²` CFT‑fixedness — house‑blindness instance, verified in finite cases.
6. **synthesis** The archimedean dichotomy: finite‑prime/algebraic invariants of `Ψ` are house‑blind; `E_r` is the relevant archimedean face.
7. **synthesis** The `m^{2r}`‑twist localization: per‑slice Betti control is not enough; cancellation across twists is the wall.
8. **Lean/synthesis** The trivial‑twist/DC bridge, via `DCSubtractedMoment.sum_nonzero_moment`.
9. **probe** Reduced‑energy law `K_reduced≈1` with mild n‑creep.
10. **probe/synthesis** Finite‑size illusion: the DC/Wick crossover is unreached at small computable depths.
11. **Lean** `coord_le_sum` — the single inequality supplied by the degree‑1 moment.
12. **Lean** Exact char‑0 subset‑sum spectrum `N_r = Σ_{k≡r(2)} C(m,k)2^k`.
13. **Lean/probe** Char‑0 total mass `T(m)=3^{m-1}(m+3)`.
14. **Lean** Alternating‑sum identity `Σ(−1)^r N_r = (−1)^{m+1}(m−1)`.
15. **Lean** Complement‑symmetry palindrome `N_r = N_{2m−r}`.
16. **Lean** `coeff_symm_of_dvd_X_pow_add_one` — dyadic rigidity engine.
17. **Lean** Multiscale cyclotomic product identity.
18. **synthesis/probe** `E_2 = 3n²−3n ⟺ no Fermat anomaly` char‑p crossover.
19. **synthesis/probe** `Σ_{b≠0} η_b³ = −n³ ⟺ no additive triples`.
20. **Lean/probe** Block‑sum norm exact value `2^{n/2−1}`.
21. **synthesis** Moment‑depth no‑go `r_opt ≈ 128 ≫ r_max ≈ 2β`.
22. **Lean** Fiber identity `a = 2|B| + s(S)`.
23. **synthesis** Mersenne–Fermat Rosetta `1∈BGK ⟺ ∃ Fermat divisor`.
24. **probe/synthesis** EVT period bound `B ≈ √(n log m)` rather than `2√n`.
25. **synthesis** Conductor‑discriminant `house` decomposition into archimedean and mod‑q defect pieces.

**Novelty defense (collective):** none of the tagged Lean declarations are in Mathlib; the no‑gos are
mechanism‑distinct for this object; the char‑0 closed forms are exact and 2‑power‑specific. Synthesis
items are recorded as research localization, not as standalone axiom‑clean theorem claims.

---

## 3. The shred (every weakness, larp, half‑truth)

- **"K≈0.6 transfer holds" (flagship) — HALF‑TRUTH → REFUTED.** Measures the *full* `E_r` at small `n`; the DC term makes it false past the `DCEnergyEssential.not_gaussianEnergyBound_of_deep` crossover. Corrected to reduced energy.
- **"disc(Ψ) is the most promising lever" — FALSE.** disc is CFT‑fixed and house‑blind, and the direction is backwards (disc lower‑bounds house, never upper).
- **"Bounded Betti ⟹ K~4" — INCOMPLETE.** Conflates the n‑independent per‑slice Betti with the cancellation over `m^{2r}` twists (the actual wall).
- **"Char‑0 is the prize" — SCOPE LARP if unqualified.** Char‑0 is fully proven and gives *one side*; the char‑p defect is untouched. Every char‑0 result must carry this caveat (and now does).
- **"δ\* reduced to one inequality" — TRUE but the inequality IS the 25‑year wall.** A reduction to an open problem is not progress toward closure unless the inequality is independently attackable; it is not (every attack returns here).
- **Finite‑size numerics — SYSTEMATICALLY MISLEADING.** Every "it holds at `n ≤ 256`" claim must be checked against the crossover `r*`; below it, the prize‑regime behavior is invisible.

## 4. No‑larp synthesis — the precise residual

Within this scoped shred, the surviving shared residual is:

> **(RESIDUAL)** For `μ_n`, `n=2^μ`, `p≈n·2^128`: the reduced additive energy obeys
> `Ẽ_r := q^{-1}∑_{b≠0}|η_b|^{2r} ≤ K^r·(2r−1)‼·n^r` for an absolute `K` and all `r ≤ ⌈ln q⌉`.
> Equivalently: square‑root cancellation in `∑_{x∈μ_n} e_p(bx)` survives averaging over the `m^{2r}`
> multiplicative‑character twists at depth `r ≈ ln q` — the BGK/Paley wall for a fixed thin subgroup.

It is **archimedean** (finite‑prime invariants are house‑blind), **nonlinear** (degree‑2+ `E_r`; LP/Delsarte
can't see it), and **fixed‑regime** (`n < p^{1/4}`; Burgess/Sato‑Tate/sum‑product vacuous). The char‑0
shadow of (RESIDUAL) is proven (`K=1` via Lam–Leung/Bessel); the char‑p surplus `Spur_r = Ẽ_r − Ẽ_r^{c0}`
is the entire open content.

## 5. What would actually breach the wall (assigned, honest)

These are the main moves in this map not yet shown to reduce trivially to (RESIDUAL); each is a genuine
research bet, **not** a closed direction:

- **(A) `m^{2r}`‑twist cancellation.** A non‑triangle‑inequality bound on `∑_{χ‑twists}` exploiting the
  *coherence* of the twists (they are powers of one base character). This is the cancellation S6 is missing.
- **(B) `Spur_r` exact closed form** at `r ~ ln m` (the swarm's live lane). If `Spur_r` has a closed
  arithmetic form (not just `≤`), (RESIDUAL) follows. Current obstruction: `Spur_r` varies prime‑to‑prime
  (= `p|N(α)` norm‑divisor primes), no word‑intrinsic closed form found.
- **(C) A self‑improving inequality** `house ≤ f(house)` with contracting fixed point at `√(2n log m)`,
  using `μ_n·μ_n=μ_n` — currently this *is* sum‑product, which needs `n>p^δ`.

**Honest bottom line.** δ\* is **not proven**. The session's contribution is a scoped, artifact-linked no‑go
map (9 method‑classes provably can't reach the prize; 7 char‑0 results closed; 9 routes reduced to
(RESIDUAL)) and a sharpened, correct formulation of the one open inequality. If the internal team has a
solution, by this map it lives in (A), (B), or (C), and its key lemma should be verified directly
against the artifacts above. No fabrication.
