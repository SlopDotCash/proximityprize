## Direct novel-math attack on the open bound `B(μ_n) ≤ C√(n·log(q/n))` — 0/6 survive (correctly), but the open core is now pinned EXACTLY, with a concrete attackable next rung

Ran a 13-agent attack whose job was to *prove* the analytic core directly (2-adic tower descent,
Gauss-sum phase cancellation, Stepanov for the deep moment, large-sieve/FFT duality, effective
2-power sum-product, fresh-idea), each ruthlessly verified. **0 survivors** — no proof, as expected
for a 25-year-open problem. But the obstruction map is now sharp, and there's one genuinely new
structural fact + a concrete forward lemma.

### The open core, pinned exactly
The moment arrow is **exact and machine-checkable** (added to `PROXIMITY_PRIZE_CONJECTURE.lean` as
`max_le_moment`): `B = max_b|η_b| ≤ (∑_b|η_b|^{2r})^{1/2r} = (q·E_r)^{1/2r}` for every `r`. Run at the
optimal depth `r ≍ log q` with the **char-0** moment values `E_r ≍ c^r·r!·n^r`, this arrow *literally
yields the prize bound* `B ≲ √(n·log q)`. So:

> **The single open input is DEEP-MOMENT VALIDITY:** `E_r(μ_n)` at (a constant^r times) its char-0
> value for `r ≍ log q`. The proven anchor is **`r = 2` only** (`subgroup_gaussSum_fourthMoment` +
> `RootsOfUnityAdditiveEnergyExact`, `E = 3n²−3n`). The needed depth exceeds the reliable depth
> `r_max ≈ 2 log_n p` by `≈ a/2` (half the tower height). Equivalently: square-root cancellation
> among the `(p−1)/n` Gauss-sum phases `χ̄(b)τ(χ)`, `χ ∈ μ_n^⊥`, at the worst frequency — the
> BGK/MRSS/Weil open core.

### Genuinely new structural fact (why average methods are blind)
**Technique 1 (tower descent)** found, machine-verified at n=8,16: at the worst-case frequency `b*`,
the two coset sums `S_{a−1}(b*)` and `S_{a−1}(b*·w)` are **maximally phase-aligned (cos = 1.0000)** —
a single major-arc clustering split into two co-aligned halves. So the naive `√2`-descent degrades to
factor 2 (trivial `B ≤ n`); the `√log` factor lives in the deep-moment / L∞ tail the descent cannot
see. This is the precise reason second-moment / average / Parseval methods are structurally blind.

### Concrete attackable next rung (a real increment, not the prize)
> Prove the **`r = 3` centered sextuple-energy bound**: `E_3(μ_n) − n⁶/q ≤ C·6·n³` for `p ≳ n³`
> (FFT-probe-confirmed; char-0 value dominated by the `3! = 6` permutation solutions), where
> `E_3 = #{(x₁,x₂,x₃,y₁,y₂,y₃)∈μ_n⁶ : Σx = Σy}`.

Within reach via the **2-adic-tower + NTT-prime cyclotomic rigidity** (`disc Φ_{2^a}` a pure
2-power) on the *multivariate* symmetric-product variety (`StepanovWeilSubstrate.lean` /
`MomentCollisionWeilConditional.lean` the natural home — NOT the univariate engine, which provably
stalls at the in-tree `stepanov_does_not_bound_e1_fiber` codimension-2 obstruction). This would be
the **first unconditional sub-`√p` saving for a 2-power subgroup beyond `r=2`** — a publishable
increment, still short of `n < p^{1/4}` (the prize).

### Honesty findings
- `CharSumMomentDeepWall.lean`'s four "engine" theorems are **content-free**: `M, qEr, T` are free
  reals, the symbol `E_r` is *never a defined object*, proofs are pigeonhole + `rpow` algebra. The
  number theory is abstracted out (it is the wall *statement*, not progress).
- The `n^{3/4}` "intrinsic ceiling" from the moment method is **not intrinsic** — a truncation
  artifact of an *unproven, numerically-fitted* (n=16, k≤4) threshold law. At the strict threshold,
  the honest conditional saving is weaker (`n^{0.917}` at `c=5`, not `n^{3/4}`).

**Net:** no closure (correct). The open core is now exactly: *deep-moment validity at `r ≍ log q`*,
with the moment arrow proven, the `r=2` anchor proven, and the `r=3` rung the concrete next step. The
conjecture (`PROXIMITY_PRIZE_CONJECTURE.lean`) is updated to this sharper input form. The 2-adic-tower
+ rigidity program on the multivariate symmetric-product variety is the one lever no published method
has used. Nothing fabricated.
