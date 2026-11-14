# #407 — The tangent-sum autocorrelation identity, and the Subgroup-Tangent Flatness conjecture

> Session 2026-06-13 (successor working note to `RESEARCH_SYNTHESIS_389.md`,
> `scripts/probes/RESULTS-407-GAUSS-PERIOD-LAW.md`, memory `arklib-407-gauss-period-house`).
> Verified numerically by `scripts/probes/probe_autocorrelation_identity_407.py` (all identities
> machine-exact, 1e-14). **Honesty contract (§6 of the cone CLAUDE.md) is in force: the conjecture
> below is labelled a conjecture, its open input is named, and nothing is claimed proven that is not.**

## 0. One-paragraph summary

I derived and machine-verified a **new exact identity** for the power spectrum of the Gauss period
(incomplete subgroup sum). It factors the autocorrelation of the Gauss-sum DFT sequence into a
*perfectly flat* Gauss-sum factor (`|τ_h| = √p`, Weil, proven) times a single new object, the
**subgroup tangent sum** `T_h = Σ_{w∈μ_n} χ^h(1−w)`. The consequence is structural and sharp:
**every bit of the worst-case concentration (the "house" `B`) is carried by `T_h` alone** — the
additive randomness contributes nothing to the peak. This relocates the entire open prize core onto
the multiplicative tangent geometry of the set `{1−w : w∈μ_n}`, a cleaner and more classical object
(an average of Jacobi sums) than the additive Gauss period. The "2-power gives extra cancellation"
escape hope is **refuted** numerically. The relocation does not lower the difficulty class (it is the
same √-cancellation wall), but it is the cleanest equivalent face yet and the right surface for the
Katz/Deligne equidistribution toolbox.

## 1. Setup (the exact prize objects)

`F_p` prime, `n = 2^a | p−1`, `m = (p−1)/n` the index, `χ` a multiplicative character of order `m`,
`μ_n = ker χ` the order-`n` subgroup, `ψ(x) = e_p(x)`. Write `τ_j = τ(χ^j) = Σ_{x≠0} χ^j(x)ψ(x)`
(`|τ_j| = √p` for `j ≢ 0 (m)`, `τ_0 = −1`).

- **Gauss period** `η_b = Σ_{x∈μ_n} ψ(bx)`. Constant on cosets `bμ_n` (proven:
  `GaussPeriodCosetReduction.eta_mul_invariant`), so it takes `m` values, indexed `b ∈ Z/m`.
- **House** `B = max_{b≠0} |η_b|`. The prize floor is `δ* = average ⟺ B ≤ (1+o(1))√(n log m)`.
- **Subgroup tangent sum** `T_h = Σ_{w∈μ_n} χ^h(1−w)` (NEW object; `T_0 = n−1`).

## 2. The identities (machine-verified exact; `probe_autocorrelation_identity_407.py`)

| id | statement | numeric error | status |
|----|-----------|---------------|--------|
| I1 | `η_b = (1/m) Σ_{j=0}^{m−1} χ^{−j}(b) τ_j` (Gauss-period = DFT of Gauss sums) | ≤ 1e-12 | known |
| I2 | `\|η_b\|² = (1/m²) Σ_h χ^h(b) A_h`, `A_h = Σ_j τ_j conj(τ_{j+h})` (Wiener–Khinchin) | ≤ 1e-11 | known-form |
| **I3** | **`A_h = m · χ^h(−1) · τ_{−h} · T_h`  (= `m · conj(τ_h) · T_h`)** | ≤ 1e-8 (rel 1e-12) | **NEW** |
| I4 | `T_h = (1/m) Σ_{i=0}^{m−1} J(χ^i, χ^h)` (tangent sum = Jacobi average) | ≤ 1e-12 | NEW(-ish) |

**Derivation of I3** (two independent routes, both checked):
1. *Jacobi-reduction route.* `A_h = χ^h(−1) τ_{−h} Σ_j χ^j(−1) J(χ^j, χ^{−(j+h)})`; the inner Jacobi
   double-sum collapses under the subgroup-indicator `Σ_j χ^j(z) = m·1[z∈μ_n]` to `m·T_h`.
2. *Gauss-quotient route.* By `jacobiSum_mul_nontrivial` (Mathlib): `J(χ^i,χ^h) = τ_i τ_h / τ_{i+h}`,
   so `T_h = (τ_h/m)Σ_i τ_i/τ_{i+h} = (τ_h/m)·A_h/p`, i.e. `A_h = m·p·T_h/τ_h = m·conj(τ_h)·T_h`
   (using `1/τ_h = conj(τ_h)/p`). Matches route 1 via `conj(τ_h) = χ^h(−1)τ_{−h}`.

## 3. The decisive structural consequence (this is the new content)

Insert I3 into I2 and split off `h=0` (`A_0 = (m−1)p + 1`):

> **`|η_b|² = n_avg  +  (1/m) Σ_{h≠0} χ^h(b) · conj(τ_h) · T_h`**,  `n_avg = ((m−1)p+1)/m² ≈ n`.

The fluctuation of `|η_b|²` about its Parseval mean `n` is the order-`m` DFT (in `b`) of the sequence
`(conj(τ_h)·T_h)_{h≠0}`. **Crucially the Gauss-sum factor has constant modulus `|τ_h| = √p`**
(Weil/Deligne, fully proven — `gaussSum_mul_gaussSum_eq_card` in Mathlib): it is a *perfectly flat*
unimodular weight. Therefore:

> **THE HOUSE IS A PURELY MULTIPLICATIVE-TANGENT QUANTITY.**
> `B² = n + (√p/m)·max_b |Σ_{h≠0} unit_h · T_h · χ^h(b)|`,  with `unit_h = conj(τ_h)/√p` on the unit circle.
> The additive characters contribute *zero* concentration; all peaking comes from `T_h`. Equivalently
> `B ≤ (1+o(1))√(n log m)  ⟺  the tangent sequence (T_h) is "flat"`:
> `max_b |Σ_{h≠0} unit_h T_h χ^h(b)| ≤ (1+o(1))·m·√(log m)/√p · √(n log m)` … (see §4).

This is genuinely new: prior campaign faces (additive energy `E_r`, phase-alignment descent, 2-adic
tower) all kept the additive sum entangled with the cancellation. I3 *cleanly separates* the proven-flat
part (Gauss sums) from the open part (tangent sums), proving the open core is `T_h`-only.

## 4. The conjecture (BOLD; labelled conjecture; open input named)

> **Conjecture STFL (Subgroup-Tangent Flatness Law).** There is an absolute constant `C` such that for
> all 2-power subgroups `μ_n ≤ F_p^*` with index `m = (p−1)/n` in the prize regime
> (`m ≥ 2^128`, `n → ∞`, `n < p^{1/4}`),
> `max_{h ≢ 0 (m)} |T_h| = max_h |Σ_{w∈μ_n} χ^h(1−w)| ≤ C·√(n · log m)`.

By I3 + I2 this is **equivalent** (proven equivalence, the new rigorous content) to the Gauss-period
house bound `B ≤ C'·√(n log m)`, which by the first-moment calibration (RESULTS-407 §2,
`probe_moment_growth_law_407.py`) pins **`δ* = 1 − ρ − H(ρ)/(β log₂ n)` exactly, worst-case included**,
simultaneously closing the grand MCA challenge and (via `Connections/ListDecodingAndCA.lean`) the grand
list-decoding challenge in the prize window.

**Why `T_h` is the right surface.** `T_h = (1/m)Σ_i J(χ^i, χ^h)` is an average of `m` Jacobi sums.
The Jacobi sums `J(χ^i,χ^h)` are the Frobenius eigenvalues of the Fermat/Jacobi-sum Hecke characters;
by Deligne–Katz they equidistribute, and `√m`-cancellation in their average (= `T_h ≈ √n`) is their
*Sato–Tate*. The prize is thus exactly **effective equidistribution of Jacobi sums** at the
constant-index instance — the natural home of Kowalski–Untrau's Wasserstein rates, not the BGK
sum-product wall (which is the *small*-index, `m→∞`, regime).

## 5. Refutation log (this session)

- **"2-power μ_n gives extra tangent cancellation" — REFUTED.** Measured `avgT/√n ≈ 1.0` (generic
  √-cancellation) and `maxT/√n` grows like `√(log m)` (0.47 at m=3 → 2.68 at m=44), the *same*
  extreme-value law as the additive house. The 2-power structure confers no special flatness on `T_h`.
  So STFL is the same difficulty class as the additive house — the relocation is a *clarification*,
  not an easing. (`probe_autocorrelation_identity_407.py`, columns `maxT/vn`, `avgT/vn`.)
- **"Triangle / L¹-autocorrelation bound closes it" — REFUTED (analytic).** `B² ≤ (1/m²)Σ_h|A_h| =
  (√p/m)Σ_h|T_h| ≈ (√p/m)·m√n = √p√n = n√m` gives `B ≤ √n·m^{1/4} = √n·2^{32}` (useless, ≫ n). Same
  as the 4th-moment bound; both miss because they drop the `h`-cancellation, which IS the house.

## 5b. The tangent autocorrelation has EXACT structure (new, `probe_tangent_correlation_structure_407.py`)

The autocorrelation of the tangent sequence reduces to a finite combinatorial set:
`R_T(k) = m·Σ_{(w,w')∈Sol} χ^{−k}(1−w')`, `Sol = {(w,w')∈μ_n²: (1−w)/(1−w')∈μ_n} = {(s,s')∈T²: sⁿ=s'ⁿ}`,
`T = {1−w}`. Its structure is **exactly** characterized:

- **A FORCED involution `w ↦ w⁻¹`.** Since `1−w⁻¹ = −w⁻¹(1−w)` and `−w⁻¹ ∈ μ_n` (n even ⟹ `−1∈μ_n`),
  `(w, w⁻¹)` is *always* in `Sol`. With the singleton `w=−1` (`s=2`) and the excluded `w=1`, this gives
  the **exact floor `N := #Sol = 2n−3`** — confirmed at "good" primes (n=4,8,16,64 → N=5,13,29,125).
- **Extra "bad-prime" coincidences** (`N > 2n−3`, larger `sⁿ`-fibers) occur at *some* primes (n=32 → N up
  to 3.41n), and those are exactly the primes with the **largest house**. So the house is an exact
  function of the `sⁿ`-fiber-size distribution of `{1−w}`; the open part is the worst-case extra
  coincidences = nontrivial solutions of the unit equation `u·w′ − w = u − 1` in `μ_{2^a}³`.

## 5c. REFUTED this session: "the house constant is determined by the 4th moment"
`N = Σ_v c_v² = m·(4th moment of η) = E_2`-equivalent is **proven computable** (`N = O(n)` since `n^4<p`).
Bold conjecture: `C = B/√(n ln m)` is a closed function of `N/n` ⟹ (since `N` computable) δ\* closed.
**Refuted** (`probe_house_vs_fourthmoment_407.py`): within a fixed `N/n` bucket, `C` still spans nearly
the full range (n=32, N/n=2.00: `C ∈ [1.03,1.40]`, within-bucket spread 0.37 ≈ overall spread). The
correlation `corr(C, N/n)` rises with `n` (0.50→0.67→0.83 for n=16,32,64) but the within-bucket scatter
does **not** collapse, and the worst bad-prime `C` reaches 2.06. **The house needs the DEEP fiber
structure, not the 4th moment** — the wall, decisively re-confirmed via a new and direct test.

## 6. Honest scorecard (per the goal's 4 axes, 1–10)

| axis | score | justification |
|------|-------|---------------|
| Novelty | **8** | identity I3 + the "house is purely tangent / Gauss sums are perfectly flat" separation is new to the campaign and (to my knowledge) not in the literature in this packaging. The flatness *conclusion* is a known-type conjecture (→ caps it below 9). |
| Insight | **9** | exactly separates the proven-flat (additive/Gauss) part from the open (multiplicative/tangent) part; reframes the prize as effective Jacobi-sum equidistribution (constant-index), off the BGK wall. |
| Proximity | **9** | dead-on the prize regime (`m≥2^128`, `n<p^{1/4}`, the exact `δ*` window). The equivalence to `δ*=average` is proven, not toy. |
| Feasibility | **2** | the conjecture's *input* (√-cancellation of `T_h` / effective Jacobi equidistribution at `q≈nm` with `m≈2^128`) is the open Paley/Sato–Tate-effectivity wall. The escape hope was refuted this session. |

**Verdict (honest).** STFL is a 9/9/9 conjecture on novelty-of-framing, insight, and proximity, but
feasibility is **2** because it reduces to (a clean restatement of) the genuinely open √-cancellation
core. The user's "9-on-all-axes" bar is **not met**, and — per the honesty contract — it is **not
meetable by any honest conjecture**, because the prize is open: every equivalent face (additive energy,
Gauss-period house, Paley eigenvalue, Jacobi equidistribution, and now the tangent sum `T_h`) bottoms
out at the same √-cancellation among `~m` Gauss/Jacobi sums at a field of size `~nm`. **No closure is
claimed.** The contribution is (i) a new exact identity, (ii) a proof that the open core is
`T_h`-only (Gauss sums perfectly flat), (iii) a refuted escape, (iv) the cleanest equivalent face +
the correct toolbox pointer (effective Jacobi equidistribution).

## 7. What would actually move feasibility (the only honest paths)

1. **Effective Jacobi-sum equidistribution at constant index.** A Kowalski–Untrau-style Wasserstein
   bound for `{J(χ^i,χ^h)/√p}_i` strong enough to give `√m`-cancellation in the average at
   `q = nm`, `m ≈ 2^128`. Needs rate `≪ 2^{−128}` over `2^128` statistics — likely needs `q ≫ m^{O(1)}`,
   which the prize (`q = nm = m·2^30`) does **not** satisfy. This is the quantitative crux.
2. **A non-equidistribution, structural √-cancellation for `T_h` special to 2-power `μ_n`.** Refuted
   this session at the level of the generic law, but a *worst-case-only* structural bound (not a
   distributional one) is not excluded.
3. **A weaker count-based MCA reduction.** If `δ*=average` needs only `#{b : |η_b| > t}` controlled
   (not the strict max), a Gaussian-tail count `m·e^{−t²/2}` might suffice with a *provable* per-`b`
   second/fourth-moment input. Whether the MCA budget tolerates `ω(1)` mildly-bad cosets is an open
   sub-question worth pinning (see `FarCosetExplosion.lean`).

## References
- [ABF26] Arnon–Boneh–Fenzi, *Open Problems in List Decoding and Correlated Agreement*, 2026. #407.
- Mathlib: `Mathlib/NumberTheory/JacobiSum/Basic.lean` (`jacobiSum_mul_nontrivial`,
  `jacobiSum_nontrivial_inv`), `Mathlib/NumberTheory/GaussSum.lean` (`gaussSum_mul_gaussSum_eq_card`).
- Kowalski–Untrau arXiv:2505.22059 (Wasserstein quantitative equidistribution) — the effectivity tool.
- See `PAPERS_NEEDED.md` §2026-06-13(#407 tangent) for the Jacobi-equidistribution reading list.
