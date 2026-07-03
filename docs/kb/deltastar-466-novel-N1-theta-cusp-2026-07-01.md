# N1-theta-cusp: the modular-form decomposition of the wraparound lattice theta — complete chain, explicit death (#466, 2026-07-01)

> **ADJUDICATED (judge, 2026-07-02): REDUCES_TO_WALL.** Both refuters killed=true; all five
> prize-point exponents independently recomputed by both refuters AND by the judge (exact
> integer representation numbers where feasible) — every displayed digit confirmed. The death
> is the flagged bounded-complexity `(2w)^{n/4}` norm-height wall (dossier §4.4, tetrachotomy
> door (i), #407 exact-norm gate) landed verbatim, plus the missing ⟨S,S⟩ input ≡ the open D2
> Rogers–Siegel gate. Full adjudication in §9 below; one probe-range claim corrected in §1.

> **Lane:** N1-theta-cusp (novel-math round). **Seed:** θ(L_p) is a modular form of weight n/2;
> decompose Eisenstein + cusp; Eisenstein = Siegel main term (allegedly the Wick/DC rate);
> cusp ≤ Ramanujan–Petersson/Deligne (proven, integral weight since n/2 = 2^29 is even).
> **Verdict: the chain is COMPLETE and DEAD at the normalization-transfer step, with the
> arithmetic fully explicit.** It does *not* evade the flagged prior kill ("theta/ideal-lattice:
> exp(Θ(n/2))-weight count = the √n-deficit in lattice clothing") — it lands on it exactly:
> Deligne's per-form exponent `(k−1)/2 = n/4 − 1/2` reproduces the `(2w)^{n/4}` norm-height wall
> verbatim, and the probe pins the same effective range `n ≲ 2^8` as the #407 exact-norm gate.
> Two of the seed's premises are additionally *refuted quantitatively*: the Eisenstein part is
> NOT the Wick prediction at prize indices (off by a factor `10^{3·10^9}`), and the cusp space's
> flagged dimension risk is real but is not even the binding failure — the binding failure is
> that **at index ≪ weight, modularity carries no information at all** (corank ≤ 356 on a
> `10^{80.7}`-dimensional space).
>
> Probe: `scripts/probes/probe_466_novel_theta_cusp.py` →
> `scripts/probes/_out_466_novel_theta_cusp.txt` (exact DP representation numbers at
> n = 8/16/32 on the β=4 diagonal, cross-checked two independent ways, plus the analytic ledger
> to n = 2^30). Everything below marked **[probe]** is machine-verified exact integer data;
> everything marked **[classical]** cites a proven theorem with hypotheses checked; the single
> routine-but-unformalized bridge is flagged in Step 1.

---

## 0. The objects (Step 0 — all verified)

Fix `n = 2^μ`, `p ≡ 1 (mod n)`, `h ∈ F_p^×` of exact order n (so `h^{n/2} = −1`), `μ_n = ⟨h⟩`.

- **The wraparound lattice** `L_p := ker(Z^n → F_p, e_j ↦ h^j)`: index-p sublattice of `Z^n`
  (covolume p), the object of the in-tree verified MGF identity
  `Φ(s) = (p/(p−1))·Θ_{L_p}(s) − e^{ns}/(p−1)` (dossier v2 §"exact identities", verified 1e−11).
  Poisson/orthogonality factorization (elementary):
  `Θ_{L_p}(it) = (1/p)·Σ_{b∈F_p} Π_{x∈μ_n} ϑ(bx/p; t)` — the b-family enters the lattice
  through this single identity, and only through moments (the route addresses face (C)/(A),
  which is legitimate; the b-max face is downstream via the standard moment finisher).
- **(0a) Anchor, unconditional:** `r_{L_p}(2) = n` *exactly*, for every `p ≡ 1 (mod n)`.
  Proof: a norm-2 vector is `±e_i ± e_j`; membership forces `h^i ≡ ∓h^j`, i.e. `j−i ≡ 0`
  (excluded: powers distinct) or `j−i ≡ n/2` (since `−1 = h^{n/2}` has the unique dyadic dlog
  n/2); the vectors are `±(e_i + e_{i+n/2})`, `i = 0..n/2−1`: count `n`. **[probe: exact at all
  four instances]**. So `λ₁(L_p)² = 2`, kissing number n — matches the dossier line.
- **(0b) The char-0 sublattice:** `L_0 := ker(Z^n → Z[ζ_n], e_j ↦ ζ^j) = span_Z{e_i + e_{i+n/2}}`,
  and these generators are *orthogonal of norm 2*, so **`L_0 ≅ √2·Z^{n/2}` exactly**, with
  `θ_{L_0}(τ) = θ₃(2τ)^{n/2}` — a modular form of **weight n/4** on Γ₀(8). By dyadic Lam–Leung,
  L_0 is the *entire* char-0 relation lattice; `L_0 ⊆ L_p` because `p ≡ 1 (mod n)` splits
  (`ζ ↦ h`). Wraparound counts = L_p-points **not** explained by L_0.
- **(0c) Odd-norm diagnostic:** `r_{L_0}(odd) = 0`, so odd-index representation numbers of L_p
  are 100% char-p wraparound. **[probe]**: at n=16, Fermat p=65537 the onset is m=9
  (`r(9)=32`) vs m=13 at the control p=65617 — a representation-number Fermat-anomaly
  detector consistent with the round-1 Hankel detector; n=8/p=4129 is wraparound-free through
  m=14 (consistent with the round-2 "n=8 window provably D4-clean" fact).
- **(0d)** `w := (h^0 mod p, …, h^{n−1} mod p) ∈ L_p` itself (since `Σ_j h^{2j} = 2·Σ_{μ_{n/2}} = 0
  mod p`), so `L_p^*/L_p ≅ (Z/p)²` — used for the level computation below.

## 1. The target in representation-number form (the one routine bridge)

> **(T)** ∃ absolute K: for all `m ≤ 2r*`, `r* = ⌈ln p⌉ ≈ 83–110`:
> `r_{L_p}(m) ≤ K^m · r_pred(m)`, where
> `r_pred(m) := r_{L_0}(m) + (r_{Z^n}(m) − r_{L_0}(m))/p` (Wick + DC, the random-sublattice-
> containing-L_0 mean).

(T) ⟹ form (C)/(A) (DC-subtracted Wick to depth r*) by positive-weight multinomial
resummation: the b-moments are ℓ¹-weighted sums of the fixed-norm counts, and a term-wise
envelope on nonneg summands transfers with the K-slack absorbed — **routine but unformalized;
flagged; it is NOT the death point** (the death is upstream and unconditional). The sparse
{0,±1} vectors of a weight-`w` ±1-relation are exactly the norm-`w` lattice points with
{0,±1} coordinates, so `#relations(w) ≤ r_{L_p}(w)`, and for `w ≪ n` the non-sparse
contribution to `r_{Z^n}(w)` is an `O(w²/n)`-fraction — bounding the full `r_{L_p}` suffices
and loses nothing.

**[probe] (T) is the empirically right statement:** measured `r_{L_p}(m)/r_pred(m)` has
**upper envelope ≤ 1.92** at ALL measured (n, p, m) (n = 8, 16, 32 on the β=4 diagonal,
m ≤ 16). ~~[0.59, 1.92] at all points~~ **[CORRECTED at adjudication (Refuter-B, judge-verified):
one below-prediction point r/pred = 0.234 at (n=16, p=65537, m=9: r=32 vs pred 136.5); over
nonzero-r points the range is [0.234, 1.92]. Below-prediction points are harmless to (T),
which is an upper envelope.]** The ratio is
**1.009 / 0.985 / 1.008 at the DC-dominated depths m = 12, 13, 14 at n = 32** — the
Rogers–Siegel/random-sublattice model is accurate to 1% where the DC term dominates. This is
the sharpest small-scale confirmation to date of the D2 (Rogers–Siegel) shape of the core.

## 2. Step 2 — modularity [classical, unconditional, checks out]

Double the form: `M := L_p(2)` is an even lattice of rank n, `det M = 2^n p²`, and
`θ(τ) := Σ_{a∈L_p} q^{‖a‖²}` is a holomorphic modular form of weight `k = n/2 = 2^29` on
`Γ₀(N)`, `N | 4p²` (from `L_p^* = Z^n + (w/p)Z`: dual norms have denominator p²; 2-part from
the doubling), with character `χ = ((−1)^k det M / ·) = (2^n p² / ·) =` **trivial** (perfect
square: n even, p² square). [Schoeneberg; Shimura. Weight 2^29 is a huge EVEN integer —
integral weight, no half-integral/Waldspurger care needed. This seed premise HOLDS.]

## 3. Step 3 — Eisenstein = Siegel–Weil genus average, and the seed's premise FAILS by 10^{3·10^9}

`θ = E + S` with `E = θ_gen` (the mass-weighted genus average): for rank ≥ 5, `θ_L − θ_gen`
is a cusp form and `θ_gen` is Eisenstein [Siegel 1935; Siegel–Weil]. Coefficients:

> `a_E(m) = π^k m^{k−1} 𝔖(m) / (Γ(k)·p)`, `𝔖(m) ≍ 1` (singular series; L_p is unimodular away
> from {2, p}, two p-Jordan blocks of scale p — local densities bounded by absolute constants).

**At the prize point** (n = 2^30, k = 2^29, p = n^4 = 2^120, prize index m = 2r = 178):

> `a_E(178) = 10^{−2,978,562,816}` **[probe ledger]** — versus the Wick+DC target
> `r_pred(178) = 10^{1300.2}` and the true Wick floor `r_{L_0}(178) = 10^{667.5}`.

So **"Eisenstein = the Wick/DC main term" is FALSE at the prize regime by a factor
`10^{3.0·10^9}`.** The Siegel main term is the *volume* term; volume ≈ count only for
`m ≳ n = 2^30`; the prize depth `m ≈ 178` sits ~6·10^6-fold below that crossover in index.
Equivalently: **L_p is astronomically non-generic in its genus** — kissing number n = 2^30 vs
genus-average kissing `a_E(2) = 10^{−4.0·10^9}`; the measured anomaly ratio `r(2)/a_E(2)`
explodes doubly-exponentially: **254 (n=8) → 4.4·10^3 (n=16) → 1.5·10^7 (n=32)** [probe].
ALL the arithmetic — the Wick main term AND the char-p fluctuation the prize is about — is
**cuspidal** at prize indices.

**Structural rider (new, and a filter for all future automorphic proposals):** the Wick main
term is itself a *lower-weight* theta — `θ_{L_0} = θ₃(2τ)^{n/2}`, weight n/4 — so no
weight-n/2 Eisenstein series can ever reproduce it: any weight-n/2 "main term + error"
decomposition of θ(L_p) necessarily carries the entire Wick term inside its *error* slot at
indices ≪ n. The Eisenstein/cusp split is constitutionally pointed at the wrong main term in
this regime.

**Identification:** "genus average = Eisenstein" IS the Rogers/Siegel mean-value statement;
the pointwise-vs-genus-average gap is exactly the **D2 Rogers–Siegel coupling gate** already
named in the dossier (§3, Tier-2). The modular lane does not bypass D2 — it re-derives it.

## 4. Step 4 — the cusp bound: Deligne applies and is structurally useless (THE DEATH)

`S = Σ_i c_i g_i` over the newform⊕oldform basis of `S_k(Γ₀(4p²))`; Deligne (1974, proven;
holomorphic, integral weight k = 2^29 ≥ 2, hypotheses hold; oldform shifts preserve the
shape): `|a_{g_i}(m)| ≤ d(m)·m^{(k−1)/2}`. Constants at n = 2^30, k = 2^29,
`(k−1)/2 = 268,435,455.5`, prize index m = 178, p = 2^120 (β=4 diagonal) **[probe ledger]**:

| quantity | value |
|---|---|
| trivial count `r_{Z^n}(178)` | `10^{1336.3}` |
| DC target `r_pred(178)` | `10^{1300.2}` |
| Wick floor `r_{L_0}(178)` | `10^{667.5}` |
| Eisenstein `a_E(178)` | `10^{−2,978,562,816}` |
| **Deligne ceiling** `n·d(m)·(m/2)^{(k−1)/2}` | **`10^{523,285,404}`** |
| one-index-step cost `(178/177)^{(k−1)/2}` | `10^{656,791}` |
| `dim S_k(Γ₀(4p²)) ≈ (k−1)/12·6p²` | `10^{80.7}` (β=4) / `10^{103.6}` (literal q ≈ 2^158) |
| max anchor ratio `m/m_a` for a sub-DC output | `1.00001` (< 1 + 1/178 ⟹ **no integer anchor exists**) |

- **(4a)** The anchor is forced: `a_S(2) = n − a_E(2) = 2^30 − 10^{−4·10^9}` (Step 0a + Step 3).
  Any RP-based bound must carry the cusp projection's normalization from a known index; the
  best conceivable output anchored at the kissing number is
  `a_S(178) ≲ n·d(178)·(178/2)^{(k−1)/2} = 10^{523,285,404}` —
  **worse than the trivial counting bound `10^{1336}` by a factor `10^{523,284,068}`.**
- **(4b)** The wall is not about anchor placement: moving even ONE index (177→178) costs
  `10^{656,791}`; staying below the DC target needs anchor ratio ≤ 1 + 1.1·10^{−5}, i.e.
  Δm < 0.002 — **no integer anchor placement survives** (probe column).
- **(4c) Petersson variant — identical wall.** The m-th coefficient functional on
  `S_k(Γ₀(N))` has norm² `(4πm)^{k−1}/Γ(k−1)·(1 + Δ)` with the Petersson–Kloosterman tail
  `Δ ≲ J_{k−1}(4πm/N)-size ~ 10^{−10^{10}}` at m ≤ 356, c ≥ N = 4p² (rigorous diagonal
  dominance; volume normalization ~p² absorbed invisibly at this scale). Anchor ⟹
  `⟨S,S⟩ ≥ n²·Γ(k−1)/(8π)^{k−1}`; the functional at 178 then returns exactly
  `n·(178/2)^{(k−1)/2}` again — the Γ(k−1)'s cancel; **the wall is the conditioning number
  `(m_target/m_anchor)^{(k−1)/2}` of the coefficient functionals, intrinsic to ANY
  normalization routed through a single Hilbert norm on S_k.**
- **(4d) The missing input is the Meta-Theorem's object.** What the route actually needs is an
  *upper* bound on `⟨S,S⟩` (the Petersson mass of θ − E). By Rankin–Selberg unfolding this is
  a weighted second moment of the deviation coefficients — i.e., **a second-order functional
  of the b-family** (through the Step-0 factorization): Meta-Theorem territory (caps at
  Johnson/√p), and it equals the **D2 Rogers–Siegel pointwise variance** for this lattice.
  Even *granted* at its conjectured (genus-typical) size, it re-enters through the
  ill-conditioned functional and reproduces (4a).
- **(4e) The leverage vacuum (the sharpest form of the death).** `dim S_k(Γ₀(4p²)) ≈ 10^{80.7}`;
  the prize needs indices ≤ 2r = 178 (≤ 356 doubled). The evaluation map of S_k onto its
  first 356 coefficients has corank ≤ 356 on a 10^{80.7}-dimensional space: **"S is a cusp
  form of weight 2^29 and level 4p²" constrains the prize-range coefficients only through a
  codimension-≤356 linear condition — modularity is informationless at index ≪ dimension.**
  (Sturm/valence: the form is pinned only by its first ~10^{80} coefficients.) The seed's
  flagged kill-risk (astronomical cusp dimension) is real but is merely the *symptom*; the
  disease is the index-vs-weight regime inversion: every coefficient technology (RP,
  Petersson, circle method) is built for index → ∞ at fixed weight; the prize sits at
  index ≈ 178 vs weight 2^29.

## 5. Step 5 — the death is the flagged kill, exactly (no evasion)

`(k−1)/2 = n/4 − 1/2`, so the RP/Petersson transfer cost is `(m/m₀)^{n/4−1/2}` =
`exp(Θ(n·log r))` — **the same exponential family as the `(2w)^{n/4}` norm-height /
conjugate-count wall** that killed theta/ideal-lattice (#444/#407, dossier §8). The probe
nails the numerical identity of the two walls: the Deligne ceiling beats the trivial count
only up to `n* ∈ (2^7, 2^8)` (n=128: `10^{43.0}` vs trivial `10^{44.1}` — still ahead;
n=256: `10^{88.4}` vs `10^{63.1}` — dead), **the same effective range n ≈ 128–256 as the
#407 exact-norm height gate**. Deligne's `m^{(k−1)/2}` is Frobenius-eigenvalue (Weil I)
bookkeeping: the modular *weight* k = n/2 is the unbounded-complexity parameter that the
bounded-complexity principle (dossier §4.4) predicts must appear — add "weight-n/2 modular
forms / Deligne transfer `(2r)^{n/4}`" to that catalogue next to "degree-n/2 cyclotomic
field" and "`(2w)^{n/4}` norm heights".

Tool-shape autopsy: the route *passes* the Meta-Theorem shape test — per-form RP is genuinely
L∞ and deterministic-archimedean (one of very few proposals not killed on second-orderness).
It dies on **bounded-complexity** instead, and its single second-order step (the ⟨S,S⟩
normalization) is exactly where the prize re-enters (= D2's gate). Tetrachotomy audit: this
was a door-(i) (algebraic geometry / Deligne) attempt; door (i)'s verdict "cost exponential
in the object's forced complexity" reappears with the complexity = the weight.

## 6. Evasions checked (each closed)

1. **Different anchor placement** — killed by (4b): no integer anchor exists.
2. **Petersson norm instead of per-form Deligne** — identical wall (4c); Γ-factors cancel.
3. **Positivity of all r(m) + full moment structure** — the round-2 lone-spike filter:
   positivity/quadrature post-processing of slack inputs adds nothing; here modularity adds
   only a corank-≤356 condition (4e) on top, i.e. nothing.
4. **Harmonic-polynomial thetas** (to isolate sparse vectors) — cuspidal from the start but
   weight *increases* (k = n/2 + deg P): wall strictly worse.
5. **Fricke/Atkin–Lehner W_{p²}** (expansion at the 0-cusp = dual-lattice theta):
   `λ₁(L_p^*)² = p^{−2}·min_{c≠0} Σ_j ‖c h^j‖²`-residues — the dual minimum is a
   "coset of μ_n crowded near 0 mod p" statement ⟺ a large-|η| direction: **the prize object
   again**; circular, no leverage. (Same circularity as the dossier's completion-sum kills.)
6. **Spinor genus refinement** — spinor-exceptional representations concern bounded rank /
   finitely many square-classes; no effect at index ≪ rank.
7. **Genus-r Siegel modular forms** (`θ^{(r)}_{L_p}`, Fourier coefficients at Gram matrices T
   = the r-tuple statistics that build E_r directly) — Siegel–Weil again gives only the genus
   average (= Rogers' formula = D2's average side); the anchor catastrophe is identical
   (T from L_0-configurations are huge, Siegel–Eisenstein negligible), weight still n/2:
   the transfer wall is unchanged and now matrix-indexed. Reduces to D2 + the same death.
8. **Half-integral weight / Shimura lift / Waldspurger** — moot: weight 2^29 is an even
   integer (the one seed premise that fully checks out).

## 7. What survives (bankable, no wall contact)

- **(S1)** The exact unconditional anchor `r_{L_p}(2) = n` (one-paragraph proof, Lean-sized)
  and the odd-index diagnostic (odd norms are pure wraparound; onset(65537) = 9 vs
  onset(65617) = 13 — a rep-number Fermat detector; n=8/p=4129 wrap-free to m=14).
- **(S2)** The Wick+DC random-sublattice model `r_pred` is measured accurate to **1%** at
  DC-dominated depth (n=32, m=12–14) — the sharpest small-scale confirmation of the D2 /
  Rogers–Siegel form of the core; (T) above is its clean statement ("L_p is
  Rogers–Siegel-typical at indices ≤ 2 ln p").
- **(S3)** The **mixed-weight filter**: the Wick main term is a weight-n/4 theta; any
  weight-n/2 automorphic main-term/error decomposition necessarily misfiles it as error at
  prize indices. A priori kill for the whole family of future "Eisenstein-main-term"
  proposals on this object.
- **(S4)** **Two dossier doors are one door:** N1's missing normalization input ⟨S,S⟩ ≡ the
  D2 Rogers–Siegel pointwise-variance gate. Any future resolution of D2's coupling gate feeds
  the modular lane its norm — and even then (4c) shows the per-index transfer still dies;
  conversely the modular framing gives D2 its cleanest invariant statement.

## 8. Honest self-assessment

- The chain has **one** unproven-but-routine step (the Step-1 multinomial bridge, direction
  count-envelope ⟹ moment-envelope, positive weights); it is not load-bearing for the verdict.
- Everything else is classical with hypotheses checked (Schoeneberg/Shimura modularity;
  Siegel–Weil rank ≥ 5; Deligne integral weight ≥ 2; Petersson formula with the Bessel tail
  bounded rigorously at index ≪ weight, level huge).
- The death is **structural, not a loose constant**: (i) the main-term slot points at the
  volume term, off by 10^{3·10^9}; (ii) normalization transfer costs (m/m₀)^{n/4}, off by
  10^{5.2·10^8} *versus the trivial bound*; (iii) modularity is informationless at index ≪
  dimension (corank 356 vs 10^{80.7}). Three independent fatal counts; any one suffices.
- **Self-refutation registered as the lane outcome: the seed mechanism cannot produce the
  prize at any tuning; the CORE stays OPEN, ON-BGK.**

## 9. Adjudication (judge, 2026-07-02) — VERDICT: REDUCES_TO_WALL

**Process:** proposer completed and self-refuted the chain; Refuter-A (arithmetic-vacuity
lens) and Refuter-B (structural-reduction lens) both returned killed=true with independent
recomputations; the judge re-derived every load-bearing number a third time, using **exact
integer arithmetic** for the representation numbers (θ₃-power coefficients by binary
polynomial exponentiation — not asymptotics). Result: **every displayed digit confirmed.**

| quantity (prize point: n=2^30, k=2^29, p=2^120, m=178) | proposer | judge recomputation |
|---|---|---|
| `a_E(178)` (Eisenstein/Siegel main term) | `10^{−2,978,562,816}` | `10^{−2,978,562,816.3}` ✓ |
| Deligne ceiling `n·d(m)·(m/2)^{(k−1)/2}` | `10^{523,285,404}` | `10^{523,285,404.0}` ✓ |
| one-index-step cost `(178/177)^{(k−1)/2}` | `10^{656,791}` | `10^{656,790.7}` ✓ |
| trivial `r_{Z^n}(178)` | `10^{1336.3}` | `10^{1336.3}` ✓ **[exact integer]** |
| Wick floor `r_{L_0}(178)` | `10^{667.5}` | `10^{667.5}` ✓ **[exact integer]** |
| DC target `r_pred(178)` | `10^{1300.2}` | `10^{1300.2}` ✓ |
| max anchor ratio / Δm | `1+1.1·10^{−5}` / 0.002 | `1+1.11·10^{−5}` / 0.0020 ✓ |
| `dim S_k(Γ₀(4p²))` (β=4 / literal q) | `10^{80.7}` / `10^{103.6}` | `10^{80.7}` / `10^{103.6}` ✓ |

**Disputes resolved:**

1. **Step-3 vs Step-4 filing (Refuter-B vs proposer/Refuter-A):** both filings are correct
   and the verdict is insensitive to the choice. Precise resolution: **Step 3 is where the
   seed's *mechanism* dies** (the Eisenstein slot holds the volume term, off by
   `10^{2.98·10^9}`; the Wick main term is a weight-n/4 theta, constitutionally
   unrepresentable in the weight-n/2 main-term slot; so at index 178 ≪ n the decomposition
   is a no-op, S ≈ θ), and **Step 4 is where the *route* dies** (exhaustive check that no
   cusp-side technology substitutes: forced anchor `r(2)=n`, transfer cost
   `(m_t/m_a)^{(k−1)/2}` with no integer anchor placement, Petersson conditioning identical,
   corank ≤ 356 on a `10^{80.7}`-dimensional space).
2. **Proposer/Refuter-A crossover-number discrepancy** (n=128: `10^{43.0}` vs trivial
   `10^{44.1}` [proposer] versus `10^{44.0}` vs `10^{45.4}` [Refuter-A]): traced by the judge
   to the depth convention — proposer's probe used r = 19/22 (≈ floor ln p), Refuter-A used
   r = 20/23 (ceil). Judge recomputed BOTH conventions with exact trivial counts:
   n=2^7 ALIVE either way (43.0 vs 44.3; 44.0 vs 45.6), n=2^8 DEAD either way
   (88.4 vs 63.1; 89.5 vs 65.0). **n\* ∈ (2^7, 2^8) is robust** — same range as the #407
   exact-norm gate; not load-bearing for the prize-point death, which is off by `10^{5.2·10^8}`.
3. **Refuter-B's data correction:** confirmed against the probe output and applied in §1
   (one below-prediction point 0.234 at (16, 65537, m=9); upper envelope 1.92 unaffected;
   (T) is an upper bound, so the correction is cosmetic for the lane but required for reuse).
4. **Normalization generosity (Refuter-A):** confirmed — the proposer's ceiling used the
   route-*favorable* base `(m/2)^{(k−1)/2} = 89^{...}`; the base-m variant gives
   `10^{604,092,528}` (judge-recomputed), i.e. the death is understated, not overstated.

**Why REDUCES_TO_WALL rather than VACUOUS_AT_SCALE:** the constants do die at the prize
point (the method genuinely beats trivial for n ≲ 2^7), but the failure is not a loose
constant — the transfer exponent `(k−1)/2 = n/4 − 1/2` makes the cost
`(2r/2)^{n/4−1/2} = exp(Θ(n log r))`, which is **verbatim the `(2w)^{n/4}` norm-height /
conjugate-count bounded-complexity wall** (dossier §4.4 and §8 "theta/ideal-lattice";
tetrachotomy door (i): Deligne = Weil-I Frobenius bookkeeping with the modular weight
k = n/2 as the forced unbounded-complexity parameter; effective range n\* ∈ (2^7, 2^8)
numerically coincides with the #407 exact-norm gate). Secondary reduction: the single
missing input — an upper bound on `⟨S,S⟩` (Petersson mass of θ − E) — is via
Rankin–Selberg a second-order functional of the b-family (Meta-Theorem-capped) and is
**identically the open D2 Rogers–Siegel pointwise-variance gate** (dossier §6 Tier-2);
and per (4c), even a granted D2 resolution dies on the conditioning ratio. Positivity
post-processing is pre-closed by the round-2 lone-spike filter. No step is mathematically
wrong (not CLOSED_FALSE); nothing survives to escalate (not SURVIVES_ROUND).

**The only rescue shape (recorded for completeness, Refuter-B's steelman, judge-endorsed):**
a coefficient-certification method for `S_k(Γ₀(N))` in the regime **index ≈ log(level),
weight ≈ 2^29** with conditioning subexponential in k — i.e.
`a_S(m) ≤ C^m·m^{o(k)}·(single-anchor data)`, routed through **no** single Hilbert norm
(4c kills all of those) and **not** a linear functional of the first o(dim) coefficients
(4e kills those). No such tool exists in the literature (all coefficient technology is
built for index → ∞ at fixed weight); any candidate must additionally beat the
mixed-weight filter (S3) and would still need the D2-gated `⟨S,S⟩` input.

### DISPROOF-ready summary

> **N1-theta-cusp is dead (REDUCES_TO_WALL; triple-verified arithmetic).** Encoding the
> prize as the representation-number envelope of the wraparound lattice
> `L_p = ker(Z^n → F_p)` makes `θ_{L_p}` a weight-2^29 form on `Γ₀(4p²)`, and every part
> of the modular toolbox then fails structurally at prize index m = 178: (i) the
> Eisenstein/Siegel–Weil slot holds the volume term `10^{−2,978,562,816}`, not the Wick+DC
> main term `10^{1300.2}` — the Wick term is a *weight-n/4* theta invisible to the
> weight-n/2 main-term slot, so the whole count is cuspidal; (ii) every cusp-coefficient
> normalization transfer from the forced anchor `r(2) = n` costs
> `(m_t/m_a)^{(k−1)/2}`, best output `10^{523,285,404}` vs trivial `10^{1336.3}` (worse
> than trivial by `10^{5.2·10^8}`; one index step costs `10^{656,791}`; no integer anchor
> exists); (iii) `dim S_k = 10^{80.7}` vs corank ≤ 356 — modularity is informationless at
> index ≪ dimension. The exponent `(k−1)/2 = n/4 − 1/2` is the `(2w)^{n/4}`
> bounded-complexity wall verbatim (effective range n ≲ 2^8, matching the #407 exact-norm
> gate), and the one missing input `⟨S,S⟩` is the open D2 Rogers–Siegel variance gate —
> the lane re-derives the wall and the open core, and closes the entire family of
> weight-n/2 "Eisenstein-main-term" proposals via the mixed-weight filter (S3).
> **CORE stays OPEN, ON-BGK.**

### Bankable sub-results (land regardless of the kill)

1. **(S1) Exact anchor theorem, Lean-sized:** `r_{L_p}(2) = n` for every `p ≡ 1 (mod n)`,
   h of exact order n (norm-2 membership forces `h^{i−j} ≡ ∓1`; unique dyadic dlog of −1
   is n/2; vectors `±(e_i+e_{i+n/2})`). Judge re-derived the proof; probe-exact at 4
   instances, independently re-verified by Refuter-A at 3. Plus the odd-index diagnostic:
   `r_{L_0}(odd) = 0` ⟹ odd norms are pure wraparound; onset m=9 at Fermat 65537 vs m=13
   at control 65617 — a rep-number Fermat-anomaly detector; n=8/p=4129 wrap-free to m=14
   (consistent with D4-clean).
2. **(S2, strongest) 1%-accurate Rogers–Siegel confirmation:** `r_pred = Wick + DC/p`
   measured at 1.009/0.985/1.008 (n=32, m=12/13/14) — sharpest small-scale confirmation
   of the D2 shape; statement (T) ("L_p is Rogers–Siegel-typical at indices ≤ 2 ln p") is
   D2's cleanest invariant form. Feed to the dossier's Tier-2 D2 decision probe.
   [With the §1 range correction: upper envelope 1.92, one low point 0.234.]
3. **(S3) Mixed-weight filter (a-priori kill for a family):** the Wick main term is
   `θ₃(2τ)^{n/2}`, weight n/4 — any weight-n/2 automorphic main-term/error decomposition
   of `θ_{L_p}` misfiles the main term as error at indices ≪ n. Cite against all future
   Eisenstein-main-term proposals on this object.
4. **(S4) Door unification for the dossier map:** N1's missing normalization input
   `⟨S,S⟩_Pet` ≡ the D2 Rogers–Siegel pointwise-variance gate — two dossier doors are one;
   moreover (4c) shows a D2 resolution would still not open this lane (conditioning
   transfer), so **D2-concentration closes N1 permanently rather than opening it**.
5. **(Refuter-A addendum, judge-verified) Wall-coincidence datum:** the modular crossover
   n\* ∈ (2^7, 2^8) coincides numerically with the #407 exact-norm-gate range (n ≈ 128–256)
   under both depth conventions — strengthening "the two walls are one wall" for the
   §4.4 catalogue, whose new entry reads: *"weight-n/2 modular forms / Deligne transfer
   `(2r)^{n/4}`"*.

<sub>🤖 Lane N1-theta-cusp proposer (Claude Fable 5), 2026-07-01. Probe:
`scripts/probes/probe_466_novel_theta_cusp.py` (exact int64 DP, brute-force + polynomial
cross-checks). No Lean claims made; nothing here is called "proven" beyond the cited
classical theorems and the machine-verified integer data.</sub>

<sub>🤖 Adjudicated by lane judge (Claude Fable 5), 2026-07-02. Judge recomputation:
scratchpad `judge_recompute_N1.py` — exact θ₃-power representation numbers via integer
polynomial exponentiation for `r_{Z^n}(178)`, `r_{L_0}(178)`, and the crossover table;
lgamma ledger for the five automorphic exponents. All values in the §9 table confirmed.
Verdict: REDUCES_TO_WALL (bounded-complexity `(2w)^{n/4}` + D2 gate). Not committed —
awaiting round consolidation per lane protocol.</sub>
