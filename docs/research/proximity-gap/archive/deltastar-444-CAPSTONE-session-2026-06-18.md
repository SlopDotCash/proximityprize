# #444 Capstone — the BGK/Paley wall, formalized and fenced (session 2026-06-18)

This consolidates a multi-workflow session on the Reed–Solomon proximity-gap prize (#444). It is a
**status capstone, not a closure.** The for-all-q prize is the recognized open BGK/Paley conjecture;
what this session did is (a) land ~30 axiom-clean bricks, (b) machine-check that the char-p transfer
**is** the BGK 2r-moment, (c) reduce the *good-prime* prize to one named cyclotomic obligation, and
(d) prove — not merely assert — that every internal, good-prime, moment-route, and ideal-theoretic
angle collapses to the same wall.

## 1. The object and the wall

- Prize ⟺ `M(μ_n) := max_{b≠0} |η_b| ≤ C·√(n·log m)`, `η_b = Σ_{y∈μ_n} e_p(b·y)`, `μ_n` = the
  `2^μ`-th roots of unity in `F_p*`, `n = 2^μ`, THIN regime `n ≈ p^{1/4}` (β=4). Prize exponent
  `n^{1/2}`; SOTA `n^{0.989}` (di Benedetto, arXiv:2003.06165); the gap is a full half-power.
- **For-all-q**: ABF26 §4.5 `mcaConjecture` binds the 3 constants BEFORE the universal over fields.
  So **no single-prime / good-prime / almost-all-prime fact closes the prize** — this is the
  *transfer barrier* and it is why every per-prime result below is honestly scoped as non-closure.

## 2. What is PROVEN (axiom-clean, `[propext, Classical.choice, Quot.sound]`, no sorryAx)

### 2a. The char-p transfer IS the BGK moment (foundational)
- `_AvCP_WrEqMomentIdentity.collision_count_eq_moment`: `p·#{(x,y): S x = S y} = Σ_b η_b·conj(η_b)`,
  assembled to `Σ_{b≠0}|η_b|^{2r} = p·E_r^{Fp} − n^{2r}`. The wraparound excess
  `W_r = E_r^{Fp} − E_r^{char0}` equals the BGK 2r-moment up to `1/p`. Previously a paper claim; now
  machine-checked. **It reduces; it does not bound.**

### 2b. The char-0 side is fully formalized
- Lam–Leung 2-power antipodal balance (`_AvX_LamLeungTwoPowerAntipodalBalan`,
  `_AvX_VanishingTwoPowSumIsAntipodalP`): a vanishing sum of `2^{k+1}`-th roots forces antipodal
  balance / coefficient symmetry `c_i = c_{i+2^k}`. (Lam–Leung J. Algebra 224 (2000), prime-power-2.)
- `cyclotomic(2^{k+1}) R = X^{2^k}+1` (`_AvX_CyclotomicTwoPowEqXPowAddOne`), `ζ^{2^k} = −1`
  (`_AvX_PrimitiveTwoPowRootHalfPowerEq`), antipodal transversal even-card
  (`_AvX_AntipodalTransversalEvenCardLe`) — ToMathlib-grade.
- T₃ closed form `rEnergy μ_n 3 = 15n³−45n²+40n` and the E₃..E₂₉ ladder (in-tree `_AvL*`).
- **HONEST GAP**: the general-r char-0 Wick bound `E_r^{char0} ≤ (2r-1)!!·n^r` (the "K≤1" floor) is
  analytically true (Bessel/Lam–Leung) but is **NOT elementary** — it reduces to
  `reprCount ≤ (2r-1)!!`, which is genuine analytic content not yet in Lean. Only the double-count
  backbone landed.

### 2c. The orthogonality / counting surface (exhausted)
- First moment `Σ_b η_b = q·𝟙[0∈G]` (`_AvY_subgroup_gaussSum_firstMomen`) — moment ladder exact at
  1st/2nd/4th/2r.
- Far-frequency count budget `#{b≠0 : ‖η_b‖²≥q} ≤ n`, q-independent
  (`_AvY_card_large_frequencies_le_pr`) — COUNT, not magnitude.
- `√(3n)` fourth-moment floor (`_AvY_worstCase_period_lower_bound`) — LOWER bound, wrong side.
- Sidon-except-negation `#{(x,y): x+y=c} ≤ 2` for c≠0 (`_AvY_SidonNegRepCountLeTwo`).

### 2d. Fixed-r / almost-all-prime transfer (genuine dents, per-prime not for-all-q)
- `_AvCP_W3UnconditionalOutsideD3.W3_zero_at_prize_prime_n16`: explicit `D_3(16)` (70-elt
  decide-verified, max 41521 < 16⁴) ⟹ **every** prize-regime prime `p ≥ 16⁴` has `W_3 = 0`; onset
  `r_0(16) > 3` unconditionally. The sharpest result that touches β=4 and survives.
- `_AvCP_AlmostAllPrimesNoWraparound.exists_finite_badPrimes`: at fixed r the bad-prime set is finite
  ⟹ `W_r = 0` for almost all p (density-1).

## 3. The fourfold wall equivalence + the one obligation

- `_FourfoldWallEquivalence`: the prize wall = ONE `EventuallyAffine` statement under 4 names
  (pole-order≤2 / m*=O(log n) / O_P≤1 / Iwasawa μ_inv=0).
- `_AvLadderSaddleAssembly`: the **good-prime prize ⟸ `UniformNoWraparoundUpTo r*`** — no short ±1
  cyclotomic relation vanishes mod p below the saddle `r*~log p`. Non-circular. This is the single
  named obligation the good-prime prize reduces to (= the Lam–Leung short-relation wall).

## 4. What was FENCED (proven dead-ends, not assertions)

- **Ideal-theoretic / class-group column FORECLOSED** (`_AvCRT_*`, `_Theta*`, `_Stickelberger*`,
  `_AvSieve1_*`): the wraparound is a RANK-1 single-prime condition (`α` in ONE prime above p, not
  `p|α`), so CRT / valuation / theta / Stickelberger / Herbrand–Ribet all fail identically.
- **Off-BGK p-independent escape CLOSED**: the distinct-γ union-count growth law is super-linear
  `~n^3.88` (`_AvC1_*`), and the per-direction count is super-linear too (`_AvPD_*`) — the off-BGK
  face is the wall in polynomial form, not a bypass.
- **Moment route provably closed**: `moment_ladder_exceeds_prize` (in-tree) + a 27-candidate
  generate→refute loop (0 survivors across all instrument classes). The trap is exact: a flat
  0-dim period set (`Σ|η_b|²=pn`, pinned `m4=3n²−3n`) denies any sub-Wick gain ⟹ the only floor is
  Wick at the saddle ⟹ `(Wick)^{1/2r}=1/2` iff the saddle is q-uniformly optimal = BGK itself. No
  candidate can be both sub-Wick (false by exact data) and Wick-saturating-with-effective-constant
  (= assuming BGK).
- **Modern tools vacuous**: decoupling/restriction/VMVT need curvature; `μ_n` is flat 0-dim.
- **Cofactor / geometry-of-numbers**: `saddle_threshold_vacuous` PROVES the `(2r)^{φ(n)}` norm bound
  excludes nothing at `r*~log p` (φ(n)=n/2 exponential).
- **di-Benedetto regime-gated**: vanishes at β=4; BGK `n^{1-o(1)}` is for-all-q but ineffective. The
  best EFFECTIVE for-all-q exponent in hand is the trivial 1; true SOTA gap = the open interval
  `(1/2, 1)`.

## 5. The only non-foreclosed frontiers (both external, neither a one-shot conjecture)

1. **`UniformNoWraparoundUpTo r*`** — the cyclotomic short-relation conjecture the good-prime prize
   reduces to. A long-term Lean target, not refutable in one round.
2. **A new effective sub-trivial for-all-q subgroup-sum estimate** — none exists in the literature;
   would be a genuine analytic breakthrough. The moment-then-root instrument class is provably
   closed (§4), so any such estimate must come from a genuinely new object NOT factoring through
   `Σ|η_b|^{2r}` or the distinct-γ count.

## 6. Honesty contract (governing all of the above)

Only the word "proven" + an axiom-clean build is sacred. Conjectures/explorations are encouraged and
labeled as such; refutations and reductions are valued results; no closure is claimed for the open
core; the for-all-q prize remains the recognized open BGK/Paley wall. Session commits:
`435466585, b2b93bd83, 497ed0736, 744822787, 28e98e245, 08a6edaa3, 925446492, 45ac2f938`.
